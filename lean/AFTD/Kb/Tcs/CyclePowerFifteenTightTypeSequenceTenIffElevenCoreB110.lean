import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b110

Topic: combinatorics   Node: 80ace7ca3e4f

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core: under the layer-free tight-cover constraints for k = 15 and 108 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b110_aux (x : ℤ → Fin 16 → Bool)
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
    (g6 : (x (-2) 7).toNat = 0)
    (g7 : (x (-2) 10).toNat = 0)
    (g8 : (x (-2) 11).toNat = 0)
    (g9 : (x (-1) 3).toNat = 0)
    (g10 : (x (-1) 4).toNat = 0)
    (g11 : (x (-1) 5).toNat = 0)
    (g12 : (x (-1) 6).toNat = 0)
    (g13 : (x (-1) 9).toNat = 0)
    (g14 : (x (-1) 10).toNat = 0)
    (g15 : (x (-1) 11).toNat = 0)
    (g16 : (x (-1) 13).toNat = 0)
    (g17 : (x 0 2).toNat = 1)
    (g18 : (x 0 3).toNat = 1)
    (g19 : (x 0 4).toNat = 1)
    (g20 : (x 0 5).toNat = 1)
    (g21 : (x 0 6).toNat = 0)
    (g22 : (x 0 10).toNat = 0)
    (g23 : (x 0 11).toNat = 1)
    (g24 : (x 0 13).toNat = 1)
    (g25 : (x 1 2).toNat = 0)
    (g26 : (x 1 4).toNat = 0)
    (g27 : (x 1 5).toNat = 0)
    (g28 : (x 1 6).toNat = 0)
    (g29 : (x 1 10).toNat = 0)
    (g30 : (x 1 12).toNat = 0)
    (g31 : (x 2 4).toNat = 0)
    (g32 : (x 2 5).toNat = 0)
    (g33 : (x 2 9).toNat = 0)
    (g34 : (x 2 11).toNat = 0)
    (g35 : (x 3 4).toNat = 0)
    (g36 : (x 3 8).toNat = 0)
    (g37 : (x 3 10).toNat = 0)
    (g38 : (x 4 9).toNat = 0)
    (g39 : (x 5 8).toNat = 0)
    (g40 : (x 5 8 && x 5 11).toNat = 0)
    (g41 : (x 4 9 && x 4 12).toNat = 0)
    (g42 : (x 3 10 && x 3 13).toNat = 0)
    (g43 : (x 2 11 && x 2 14).toNat = 0)
    (g44 : (x (-3) 2 && x (-3) 6).toNat = 0)
    (g45 : (x (-4) 3 && x (-4) 7).toNat = 0)
    (g46 : (x (-1) 3 && x (-1) 7).toNat = 0)
    (g47 : (x 1 2 && x 1 6).toNat = 0)
    (g48 : (x (-1) 4 && x (-1) 8).toNat = 0)
    (g49 : (x (-2) 5 && x (-2) 9).toNat = 0)
    (g50 : (x (-3) 6 && x (-3) 10).toNat = 0)
    (g51 : (x (-4) 7 && x (-4) 11).toNat = 0)
    (g52 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g53 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g54 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g55 : (x 2 8 && x 2 12).toNat = 0)
    (g56 : (x 1 9 && x 1 13).toNat = 0)
    (g57 : (x (-2) 1 && x (-2) 6).toNat = 0)
    (g58 : (x (-3) 2 && x (-3) 7).toNat = 0)
    (g59 : (x (-1) 2 && x (-1) 7).toNat = 0)
    (g60 : (x (-2) 3 && x (-2) 8).toNat = 0)
    (g61 : (x 1 4 && x 1 9).toNat = 0)
    (g62 : (x 0 5 && x 0 10).toNat = 0)
    (g63 : (x (-1) 6 && x (-1) 11).toNat = 0)
    (g64 : (x (-2) 7 && x (-2) 12).toNat = 0)
    (g65 : (x 2 7 && x 2 12).toNat = 0)
    (g66 : (x 1 8 && x 1 13).toNat = 0)
    (g67 : (x 3 8 && x 3 13).toNat = 0)
    (g68 : (x 2 9 && x 2 14).toNat = 0)
    (g69 : (x (-1) 3 && x (-1) 9).toNat = 0)
    (g70 : (x (-2) 4 && x (-2) 10).toNat = 0)
    (g71 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g72 : (x 1 2 && x 1 8).toNat = 0)
    (g73 : (x (-1) 4 && x (-1) 10).toNat = 0)
    (g74 : (x (-2) 5 && x (-2) 11).toNat = 0)
    (g75 : (x (-3) 6 && x (-3) 12).toNat = 0)
    (g76 : (x (-4) 7 && x (-4) 13).toNat = 0)
    (g77 : (x 5 2 && x 5 8).toNat = 0)
    (g78 : (x 4 3 && x 4 9).toNat = 0)
    (g79 : (x 3 4 && x 3 10).toNat = 0)
    (g80 : (x 2 5 && x 2 11).toNat = 0)
    (g81 : (x 1 6 && x 1 12).toNat = 0)
    (g82 : (x 2 6 && x 2 12).toNat = 0)
    (g83 : (x 1 7 && x 1 13).toNat = 0)
    (g84 : (x (-1) 1 && x (-1) 8).toNat = 0)
    (g85 : (x (-2) 2 && x (-2) 9).toNat = 0)
    (g86 : (x (-3) 3 && x (-3) 10).toNat = 0)
    (g87 : (x (-1) 2 && x (-1) 9).toNat = 0)
    (g88 : (x (-2) 3 && x (-2) 10).toNat = 0)
    (g89 : (x (-3) 4 && x (-3) 11).toNat = 0)
    (g90 : (x 3 4 && x 3 11).toNat = 0)
    (g91 : (x 2 5 && x 2 12).toNat = 0)
    (g92 : (x 1 6 && x 1 13).toNat = 0)
    (g93 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g94 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g95 : (x 0 1 && x 0 10).toNat = 0)
    (g96 : (x (-1) 2 && x (-1) 11).toNat = 0)
    (g97 : (x (-2) 3 && x (-2) 12).toNat = 0)
    (g98 : (x 3 3 && x 3 12).toNat = 0)
    (g99 : (x 2 4 && x 2 13).toNat = 0)
    (g100 : (x 1 5 && x 1 14).toNat = 0)
    (g101 : (x 3 4 && x 3 13).toNat = 0)
    (g102 : (x 2 5 && x 2 14).toNat = 0)
    (g103 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g104 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g105 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g106 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g107 : (x 2 4 && x 2 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d18360 : (x 0 1 && x 0 6).toNat = 0 := by
    have r18361 := hand2 (x 0 1) (x 0 6)
    have b18362 := hb (x 0 6)
    have b18363 := hb (x 0 1 && x 0 6)
    clear * - r18361 b18362 b18363 g21
    omega
  have d18364 : (x 0 2 && x 0 6).toNat = 0 := by
    have r18365 := hand2 (x 0 2) (x 0 6)
    have b18366 := hb (x 0 6)
    have b18367 := hb (x 0 2 && x 0 6)
    clear * - r18365 b18366 b18367 g21
    omega
  cases h18368 : x 0 7
  · have f18369 : (x 0 7).toNat = 0 := by rw [h18368]; rfl
    have d18370 : (x 0 7 && x 0 14).toNat = 0 := by
      have r18371 := hand1 (x 0 7) (x 0 14)
      have b18372 := hb (x 0 7)
      have b18373 := hb (x 0 7 && x 0 14)
      clear * - r18371 b18372 b18373 f18369
      omega
    have d18374 : (x 0 7 && x 0 13).toNat = 0 := by
      have r18375 := hand1 (x 0 7) (x 0 13)
      have b18376 := hb (x 0 7)
      have b18377 := hb (x 0 7 && x 0 13)
      clear * - r18375 b18376 b18377 f18369
      omega
    have d18378 : (x 0 3 && x 0 7).toNat = 0 := by
      have r18379 := hand2 (x 0 3) (x 0 7)
      have b18380 := hb (x 0 7)
      have b18381 := hb (x 0 3 && x 0 7)
      clear * - r18379 b18380 b18381 f18369
      omega
    cases h18382 : x 0 8
    · have f18383 : (x 0 8).toNat = 0 := by rw [h18382]; rfl
      have d18384 : (x 0 1 && x 0 8).toNat = 0 := by
        have r18385 := hand2 (x 0 1) (x 0 8)
        have b18386 := hb (x 0 8)
        have b18387 := hb (x 0 1 && x 0 8)
        clear * - r18385 b18386 b18387 f18383
        omega
      have d18388 : (x 0 8 && x 0 14).toNat = 0 := by
        have r18389 := hand1 (x 0 8) (x 0 14)
        have b18390 := hb (x 0 8)
        have b18391 := hb (x 0 8 && x 0 14)
        clear * - r18389 b18390 b18391 f18383
        omega
      have d18392 : (x 0 2 && x 0 8).toNat = 0 := by
        have r18393 := hand2 (x 0 2) (x 0 8)
        have b18394 := hb (x 0 8)
        have b18395 := hb (x 0 2 && x 0 8)
        clear * - r18393 b18394 b18395 f18383
        omega
      have d18396 : (x 0 4 && x 0 8).toNat = 0 := by
        have r18397 := hand2 (x 0 4) (x 0 8)
        have b18398 := hb (x 0 8)
        have b18399 := hb (x 0 4 && x 0 8)
        clear * - r18397 b18398 b18399 f18383
        omega
      cases h18400 : x 0 9
      · have f18401 : (x 0 9).toNat = 0 := by rw [h18400]; rfl
        have d18402 : (x 0 3 && x 0 9).toNat = 0 := by
          have r18403 := hand2 (x 0 3) (x 0 9)
          have b18404 := hb (x 0 9)
          have b18405 := hb (x 0 3 && x 0 9)
          clear * - r18403 b18404 b18405 f18401
          omega
        have d18406 : (x 0 9 && x 0 14).toNat = 0 := by
          have r18407 := hand1 (x 0 9) (x 0 14)
          have b18408 := hb (x 0 9)
          have b18409 := hb (x 0 9 && x 0 14)
          clear * - r18407 b18408 b18409 f18401
          omega
        cases h18410 : x 1 1
        · have f18411 : (x 1 1).toNat = 0 := by rw [h18410]; rfl
          have d18412 : (x 1 9).toNat = 0 := by
            have r18413 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
            have b18414 := hb (x 1 1)
            have b18415 := hb (x 1 9)
            clear * - r18413 b18414 b18415 f18411
            omega
          have d18416 : (x 2 14).toNat = 1 := by
            have r18417 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b18418 := hb (x 1 1)
            have b18419 := hb (x 2 14)
            clear * - r18417 b18418 b18419 f18411
            omega
          cases h18420 : x 1 3
          · have f18421 : (x 1 3).toNat = 0 := by rw [h18420]; rfl
            have d18422 : (x 1 3 && x 1 7).toNat = 0 := by
              have r18423 := hand1 (x 1 3) (x 1 7)
              have b18424 := hb (x 1 3)
              have b18425 := hb (x 1 3 && x 1 7)
              clear * - r18423 b18424 b18425 f18421
              omega
            cases h18426 : x 1 7
            · have f18427 : (x 1 7).toNat = 0 := by rw [h18426]; rfl
              cases h18428 : x (-1) 8
              · have f18429 : (x (-1) 8).toNat = 0 := by rw [h18428]; rfl
                have d18430 : (x (-1) 8 && x (-1) 14).toNat = 0 := by
                  have r18431 := hand1 (x (-1) 8) (x (-1) 14)
                  have b18432 := hb (x (-1) 8)
                  have b18433 := hb (x (-1) 8 && x (-1) 14)
                  clear * - r18431 b18432 b18433 f18429
                  omega
                cases h18434 : x 1 8
                · have f18435 : (x 1 8).toNat = 0 := by rw [h18434]; rfl
                  cases h18436 : x (-1) 12
                  · have f18437 : (x (-1) 12).toNat = 0 := by rw [h18436]; rfl
                    cases h18438 : x (-1) 14
                    · have f18439 : (x (-1) 14).toNat = 0 := by rw [h18438]; rfl
                      cases h18440 : x 2 1
                      · have f18441 : (x 2 1).toNat = 0 := by rw [h18440]; rfl
                        have d18442 : (x 2 1 && x 2 14).toNat = 0 := by
                          have r18443 := hand1 (x 2 1) (x 2 14)
                          have b18444 := hb (x 2 1)
                          have b18445 := hb (x 2 1 && x 2 14)
                          clear * - r18443 b18444 b18445 f18441
                          omega
                        have d18446 : (x 3 13).toNat = 1 := by
                          have r18447 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b18448 := hb (x 1 2)
                          have b18449 := hb (x 3 13)
                          have b18450 := hb (x 2 1 && x 2 14)
                          clear * - r18447 b18448 b18449 b18450 d18442 g25
                          omega
                        have d18451 : (x 3 1).toNat = 1 := by
                          have r18452 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
                          have b18453 := hb (x 3 1)
                          have b18454 := hb (x 3 13)
                          clear * - r18452 b18453 b18454 d18446
                          omega
                        have d18455 : (x 4 12).toNat = 0 := by
                          have r18456 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e18457 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                          have e18458 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                          have b18459 := hb (x 1 3)
                          have b18460 := hb (x 2 2)
                          have b18461 := hb (x 3 13)
                          have b18462 := hb (x 4 12)
                          clear * - r18456 e18457 e18458 b18459 b18460 b18461 b18462 d18446 f18421
                          omega
                        have d18463 : (x 4 1 && x 4 12).toNat = 0 := by
                          have r18464 := hand2 (x 4 1) (x 4 12)
                          have b18465 := hb (x 4 12)
                          have b18466 := hb (x 4 1 && x 4 12)
                          clear * - r18464 b18465 b18466 d18455
                          omega
                        have d18467 : (x 4 3 && x 4 12).toNat = 0 := by
                          have r18468 := hand2 (x 4 3) (x 4 12)
                          have b18469 := hb (x 4 12)
                          have b18470 := hb (x 4 3 && x 4 12)
                          clear * - r18468 b18469 b18470 d18455
                          omega
                        have d18471 : (x 4 4).toNat = 0 := by
                          have r18472 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
                          have b18473 := hb (x 4 4)
                          have b18474 := hb (x 4 12)
                          clear * - r18472 b18473 b18474 d18455
                          omega
                        have d18475 : (x 2 2).toNat = 0 := by
                          have r18476 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e18477 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                          have e18478 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                          have b18479 := hb (x 1 3)
                          have b18480 := hb (x 2 2)
                          have b18481 := hb (x 3 13)
                          have b18482 := hb (x 4 12)
                          clear * - r18476 e18477 e18478 b18479 b18480 b18481 b18482 d18455 d18446 f18421
                          omega
                        have d18483 : (x 2 2 && x 2 6).toNat = 0 := by
                          have r18484 := hand1 (x 2 2) (x 2 6)
                          have b18485 := hb (x 2 2)
                          have b18486 := hb (x 2 2 && x 2 6)
                          clear * - r18484 b18485 b18486 d18475
                          omega
                        have r18487 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r18488 : (x 4 1).toNat + (x 3 2).toNat + (x 2 3).toNat + (x 1 4).toNat + (x 0 5).toNat + (x (-1) 6).toNat + (x (-2) 7).toNat + (x (-3) 8).toNat + (x (-4) 9).toNat + (x (-5) 10).toNat + (x (-6) 11).toNat + (x (-7) 12).toNat + (x (-8) 13).toNat + (x (-9) 14).toNat = 3 := by have q := hcount 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r18489 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r18490 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e18491 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
                        have e18492 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
                        have e18493 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
                        have e18494 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
                        have e18495 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
                        have e18496 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
                        have r18497 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e18498 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                        have e18499 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                        have e18500 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                        have e18501 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                        have e18502 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                        have e18503 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                        have r18504 : 1 ≤ (x 13 3).toNat + (x 12 1 && x 12 4).toNat + (x 11 2 && x 11 5).toNat + (x 10 3 && x 10 6).toNat + (x 9 4 && x 9 7).toNat + (x 8 5 && x 8 8).toNat + (x 7 6 && x 7 9).toNat + (x 6 7 && x 6 10).toNat + (x 5 8 && x 5 11).toNat + (x 4 9 && x 4 12).toNat + (x 3 10 && x 3 13).toNat + (x 2 11 && x 2 14).toNat + (x 1 12).toNat := by have q := hcov3 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r18505 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e18506 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
                        have e18507 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
                        have r18508 : 1 ≤ (x (-4) 9).toNat + (x (-5) 1 && x (-5) 10).toNat + (x (-6) 2 && x (-6) 11).toNat + (x (-7) 3 && x (-7) 12).toNat + (x (-8) 4 && x (-8) 13).toNat + (x (-9) 5 && x (-9) 14).toNat + (x (-10) 6).toNat := by have q := hcov9 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r18509 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r18510 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r18511 : 1 ≤ (x (-8) 13).toNat + (x (-9) 1 && x (-9) 14).toNat + (x (-10) 2).toNat := by have q := hcov13 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r18512 : (x (-10) 2).toNat ≤ (x (-10) 14).toNat := himp _ _ (hp2 (-10))
                        have r18513 := hand2 (x 12 1) (x 12 4)
                        have r18514 := hand2 (x 11 2) (x 11 5)
                        have r18515 := hand2 (x 10 3) (x 10 6)
                        have r18516 := hand2 (x 9 4) (x 9 7)
                        have r18517 := hand2 (x 8 5) (x 8 8)
                        have r18518 := hand2 (x 7 6) (x 7 9)
                        have r18519 := hand2 (x 6 7) (x 6 10)
                        have r18520 := hand1 (x (-4) 8) (x (-4) 12)
                        have r18521 := hand1 (x (-5) 9) (x (-5) 13)
                        have r18522 := hand2 (x (-5) 1) (x (-5) 10)
                        have r18523 := hand2 (x (-6) 2) (x (-6) 11)
                        have r18524 := hand2 (x (-7) 3) (x (-7) 12)
                        have r18525 := hand1 (x (-8) 4) (x (-8) 13)
                        have r18526 := hand1 (x (-9) 5) (x (-9) 14)
                        have r18527 := hand2 (x 6 1) (x 6 10)
                        have r18528 := hand2 (x 5 2) (x 5 11)
                        have r18529 := hand1 (x 3 2) (x 3 13)
                        have r18530 := hand1 (x 2 3) (x 2 14)
                        have r18531 := hand2 (x (-9) 1) (x (-9) 14)
                        linarith only [r18487, r18488, r18489, r18490, e18491, e18492, e18493, e18494, e18495, e18496, r18497, e18498, e18499, e18500, e18501, e18502, e18503, r18504, r18505, e18506, e18507, r18508, r18509, r18510, r18511, r18512, r18513, r18514, r18515, r18516, r18517, r18518, r18519, r18520, r18521, r18522, r18523, r18524, r18525, r18526, r18527, r18528, r18529, r18530, r18531, g2, g5, g6, g11, g12, g19, g20, f18421, g26, g28, f18427, g30, d18475, d18416, d18451, d18446, d18471, d18455, g40, g41, g42, g43, d18483, d18422, d18396, g52, g53, g54, d18467, g101, g102, d18463]
                      · have f18618 : (x 2 1).toNat = 1 := by rw [h18440]; rfl
                        have d18619 : (x 3 14).toNat = 0 := by
                          have r18620 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b18621 := hb (x 2 1)
                          have b18622 := hb (x 3 14)
                          clear * - r18620 b18621 b18622 f18618
                          omega
                        have d18623 : (x 3 1 && x 3 14).toNat = 0 := by
                          have r18624 := hand2 (x 3 1) (x 3 14)
                          have b18625 := hb (x 3 14)
                          have b18626 := hb (x 3 1 && x 3 14)
                          clear * - r18624 b18625 b18626 d18619
                          omega
                        have d18627 : (x 3 3 && x 3 14).toNat = 0 := by
                          have r18628 := hand2 (x 3 3) (x 3 14)
                          have b18629 := hb (x 3 14)
                          have b18630 := hb (x 3 3 && x 3 14)
                          clear * - r18628 b18629 b18630 d18619
                          omega
                        have d18631 : (x 3 6).toNat = 0 := by
                          have r18632 : (x 3 6).toNat ≤ (x 3 14).toNat := himp _ _ (hp6 3)
                          have b18633 := hb (x 3 6)
                          have b18634 := hb (x 3 14)
                          clear * - r18632 b18633 b18634 d18619
                          omega
                        have d18635 : (x 3 6 && x 3 11).toNat = 0 := by
                          have r18636 := hand1 (x 3 6) (x 3 11)
                          have b18637 := hb (x 3 6)
                          have b18638 := hb (x 3 6 && x 3 11)
                          clear * - r18636 b18637 b18638 d18631
                          omega
                        have d18639 : (x 3 2).toNat = 0 := by
                          have r18640 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
                          have b18641 := hb (x 3 2)
                          have b18642 := hb (x 3 14)
                          clear * - r18640 b18641 b18642 d18619
                          omega
                        have d18643 : (x 3 2 && x 3 7).toNat = 0 := by
                          have r18644 := hand1 (x 3 2) (x 3 7)
                          have b18645 := hb (x 3 2)
                          have b18646 := hb (x 3 2 && x 3 7)
                          clear * - r18644 b18645 b18646 d18639
                          omega
                        cases h18647 : x (-1) 7
                        · have f18648 : (x (-1) 7).toNat = 0 := by rw [h18647]; rfl
                          cases h18649 : x 2 2
                          · have f18650 : (x 2 2).toNat = 0 := by rw [h18649]; rfl
                            have d18651 : (x 4 13).toNat = 1 := by
                              have r18652 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have b18653 := hb (x 2 2)
                              have b18654 := hb (x 4 13)
                              have b18655 := hb (x 3 1 && x 3 14)
                              clear * - r18652 b18653 b18654 b18655 d18623 f18650
                              omega
                            have d18656 : (x 4 1).toNat = 1 := by
                              have r18657 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
                              have b18658 := hb (x 4 1)
                              have b18659 := hb (x 4 13)
                              clear * - r18657 b18658 b18659 d18651
                              omega
                            have d18660 : (x 5 12).toNat = 0 := by
                              have r18661 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e18662 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                              have e18663 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                              have b18664 := hb (x 2 3)
                              have b18665 := hb (x 3 2)
                              have b18666 := hb (x 4 13)
                              have b18667 := hb (x 5 12)
                              clear * - r18661 e18662 e18663 b18664 b18665 b18666 b18667 d18651 d18639
                              omega
                            have d18668 : (x 5 1 && x 5 12).toNat = 0 := by
                              have r18669 := hand2 (x 5 1) (x 5 12)
                              have b18670 := hb (x 5 12)
                              have b18671 := hb (x 5 1 && x 5 12)
                              clear * - r18669 b18670 b18671 d18660
                              omega
                            have d18672 : (x 5 4).toNat = 0 := by
                              have r18673 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
                              have b18674 := hb (x 5 4)
                              have b18675 := hb (x 5 12)
                              clear * - r18673 b18674 b18675 d18660
                              omega
                            have d18676 : (x 5 4 && x 5 13).toNat = 0 := by
                              have r18677 := hand1 (x 5 4) (x 5 13)
                              have b18678 := hb (x 5 4)
                              have b18679 := hb (x 5 4 && x 5 13)
                              clear * - r18677 b18678 b18679 d18672
                              omega
                            have d18680 : (x 2 3).toNat = 0 := by
                              have r18681 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e18682 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                              have e18683 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                              have b18684 := hb (x 2 3)
                              have b18685 := hb (x 3 2)
                              have b18686 := hb (x 4 13)
                              have b18687 := hb (x 5 12)
                              clear * - r18681 e18682 e18683 b18684 b18685 b18686 b18687 d18660 d18651 d18639
                              omega
                            have d18688 : (x 2 3 && x 2 8).toNat = 0 := by
                              have r18689 := hand1 (x 2 3) (x 2 8)
                              have b18690 := hb (x 2 3)
                              have b18691 := hb (x 2 3 && x 2 8)
                              clear * - r18689 b18690 b18691 d18680
                              omega
                            have r18692 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r18693 : (x 4 1).toNat + (x 3 2).toNat + (x 2 3).toNat + (x 1 4).toNat + (x 0 5).toNat + (x (-1) 6).toNat + (x (-2) 7).toNat + (x (-3) 8).toNat + (x (-4) 9).toNat + (x (-5) 10).toNat + (x (-6) 11).toNat + (x (-7) 12).toNat + (x (-8) 13).toNat + (x (-9) 14).toNat = 3 := by have q := hcount 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r18694 : (x (-5) 8).toNat + (x (-6) 1 && x (-6) 9).toNat + (x (-7) 2 && x (-7) 10).toNat + (x (-8) 3 && x (-8) 11).toNat + (x (-9) 4 && x (-9) 12).toNat + (x (-10) 5 && x (-10) 13).toNat + (x (-11) 6 && x (-11) 14).toNat + (x (-12) 7).toNat = 1 := by have q := hd8 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e18695 : (x (-6) 1 && x (-6) 9).toNat = (x (-6) 9).toNat := handr _ _ (fun h => hp9 (-6) (h))
                            have e18696 : (x (-7) 2 && x (-7) 10).toNat = (x (-7) 10).toNat := handr _ _ (fun h => hp10 (-7) (h))
                            have e18697 : (x (-8) 3 && x (-8) 11).toNat = (x (-8) 11).toNat := handr _ _ (fun h => hp11 (-8) (h))
                            have e18698 : (x (-9) 4 && x (-9) 12).toNat = (x (-9) 4).toNat := handl _ _ (fun h => hp4 (-9) (h))
                            have e18699 : (x (-10) 5 && x (-10) 13).toNat = (x (-10) 5).toNat := handl _ _ (fun h => hp5 (-10) (h))
                            have e18700 : (x (-11) 6 && x (-11) 14).toNat = (x (-11) 6).toNat := handl _ _ (fun h => hp6 (-11) (h))
                            have r18701 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e18702 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                            have e18703 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                            have e18704 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                            have e18705 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                            have e18706 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                            have e18707 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                            have r18708 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e18709 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                            have e18710 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                            have e18711 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                            have e18712 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                            have e18713 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                            have e18714 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                            have r18715 : (x (-10) 12).toNat + (x (-11) 1 && x (-11) 13).toNat + (x (-12) 2 && x (-12) 14).toNat + (x (-13) 3).toNat = 1 := by have q := hd12 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e18716 : (x (-11) 1 && x (-11) 13).toNat = (x (-11) 13).toNat := handr _ _ (fun h => hp13 (-11) (h))
                            have e18717 : (x (-12) 2 && x (-12) 14).toNat = (x (-12) 2).toNat := handl _ _ (fun h => hp2 (-12) (h))
                            have r18718 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e18719 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
                            have e18720 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
                            have r18721 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e18722 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                            have e18723 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                            have r18724 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e18725 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                            have e18726 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                            have r18727 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e18728 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                            have e18729 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                            have r18730 : 1 ≤ (x 3 4).toNat + (x 2 1 && x 2 5).toNat + (x 1 2 && x 1 6).toNat + (x 0 3 && x 0 7).toNat + (x (-1) 4 && x (-1) 8).toNat + (x (-2) 5 && x (-2) 9).toNat + (x (-3) 6 && x (-3) 10).toNat + (x (-4) 7 && x (-4) 11).toNat + (x (-5) 8 && x (-5) 12).toNat + (x (-6) 9 && x (-6) 13).toNat + (x (-7) 10 && x (-7) 14).toNat + (x (-8) 11).toNat := by have q := hcov4 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e18731 : (x 2 1 && x 2 5).toNat = (x 2 5).toNat := handr _ _ (fun h => hp13 2 (hp5 2 (h)))
                            have e18732 : (x (-7) 10 && x (-7) 14).toNat = (x (-7) 10).toNat := handl _ _ (fun h => hp2 (-7) (hp10 (-7) (h)))
                            have r18733 : 1 ≤ (x 5 5).toNat + (x 4 1 && x 4 6).toNat + (x 3 2 && x 3 7).toNat + (x 2 3 && x 2 8).toNat + (x 1 4 && x 1 9).toNat + (x 0 5 && x 0 10).toNat + (x (-1) 6 && x (-1) 11).toNat + (x (-2) 7 && x (-2) 12).toNat + (x (-3) 8 && x (-3) 13).toNat + (x (-4) 9 && x (-4) 14).toNat + (x (-5) 10).toNat := by have q := hcov5 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r18734 : 1 ≤ (x 3 6).toNat + (x 2 1 && x 2 7).toNat + (x 1 2 && x 1 8).toNat + (x 0 3 && x 0 9).toNat + (x (-1) 4 && x (-1) 10).toNat + (x (-2) 5 && x (-2) 11).toNat + (x (-3) 6 && x (-3) 12).toNat + (x (-4) 7 && x (-4) 13).toNat + (x (-5) 8 && x (-5) 14).toNat + (x (-6) 9).toNat := by have q := hcov6 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r18735 : 1 ≤ (x 9 9).toNat + (x 8 1 && x 8 10).toNat + (x 7 2 && x 7 11).toNat + (x 6 3 && x 6 12).toNat + (x 5 4 && x 5 13).toNat + (x 4 5 && x 4 14).toNat + (x 3 6).toNat := by have q := hcov9 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r18736 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r18737 : 1 ≤ (x (-5) 10).toNat + (x (-6) 1 && x (-6) 11).toNat + (x (-7) 2 && x (-7) 12).toNat + (x (-8) 3 && x (-8) 13).toNat + (x (-9) 4 && x (-9) 14).toNat + (x (-10) 5).toNat := by have q := hcov10 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r18738 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r18739 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := by have q := hcov11 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r18740 : 1 ≤ (x (-10) 13).toNat + (x (-11) 1 && x (-11) 14).toNat + (x (-12) 2).toNat := by have q := hcov13 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r18741 : 1 ≤ (x (-8) 13).toNat + (x (-9) 1 && x (-9) 14).toNat + (x (-10) 2).toNat := by have q := hcov13 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r18742 : (x (-11) 5).toNat ≤ (x (-11) 13).toNat := himp _ _ (hp5 (-11))
                            have r18743 : (x (-10) 4).toNat ≤ (x (-10) 12).toNat := himp _ _ (hp4 (-10))
                            have r18744 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
                            have r18745 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
                            have r18746 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
                            have r18747 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
                            have r18748 := hand1 (x (-5) 8) (x (-5) 12)
                            have r18749 := hand2 (x (-5) 8) (x (-5) 12)
                            have r18750 := hand1 (x (-6) 9) (x (-6) 13)
                            have r18751 := hand2 (x (-6) 9) (x (-6) 13)
                            have r18752 := hand2 (x 4 1) (x 4 6)
                            have r18753 := hand1 (x (-3) 8) (x (-3) 13)
                            have r18754 := hand1 (x (-4) 9) (x (-4) 14)
                            have r18755 := hand2 (x 2 1) (x 2 7)
                            have r18756 := hand1 (x (-5) 8) (x (-5) 14)
                            have r18757 := hand2 (x 8 1) (x 8 10)
                            have r18758 := hand2 (x 7 2) (x 7 11)
                            have r18759 := hand2 (x 6 3) (x 6 12)
                            have r18760 := hand1 (x 4 5) (x 4 14)
                            have r18761 := hand2 (x (-7) 1) (x (-7) 11)
                            have r18762 := hand2 (x (-8) 2) (x (-8) 12)
                            have r18763 := hand2 (x (-9) 3) (x (-9) 13)
                            have r18764 := hand1 (x (-10) 4) (x (-10) 14)
                            have r18765 := hand2 (x (-6) 1) (x (-6) 11)
                            have r18766 := hand1 (x (-7) 2) (x (-7) 12)
                            have r18767 := hand1 (x (-8) 3) (x (-8) 13)
                            have r18768 := hand1 (x (-9) 4) (x (-9) 14)
                            have r18769 := hand1 (x (-4) 4) (x (-4) 14)
                            have r18770 := hand1 (x 4 2) (x 4 13)
                            have r18771 := hand2 (x (-11) 1) (x (-11) 14)
                            have r18772 := hand2 (x (-9) 1) (x (-9) 14)
                            linarith only [r18692, r18693, r18694, e18695, e18696, e18697, e18698, e18699, e18700, r18701, e18702, e18703, e18704, e18705, e18706, e18707, r18708, e18709, e18710, e18711, e18712, e18713, e18714, r18715, e18716, e18717, r18718, e18719, e18720, r18721, e18722, e18723, r18724, e18725, e18726, r18727, e18728, e18729, r18730, e18731, e18732, r18733, r18734, r18735, r18736, r18737, r18738, r18739, r18740, r18741, r18742, r18743, r18744, r18745, r18746, r18747, r18748, r18749, r18750, r18751, r18752, r18753, r18754, r18755, r18756, r18757, r18758, r18759, r18760, r18761, r18762, r18763, r18764, r18765, r18766, r18767, r18768, r18769, r18770, r18771, r18772, g0, g1, g4, g6, g10, g12, g18, g20, g22, g25, g26, f18618, d18680, g31, g32, d18639, g35, d18631, d18656, d18672, g47, d18378, g48, g49, g50, g51, d18643, d18688, g61, g62, g63, g64, g72, d18402, g73, g74, g75, g76, d18676, g104, g105, g106, d18668, d18627]
                          · have f18898 : (x 2 2).toNat = 1 := by rw [h18649]; rfl
                            have d18899 : (x 4 12).toNat = 0 := by
                              have r18900 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e18901 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                              have e18902 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                              have b18903 := hb (x 1 3)
                              have b18904 := hb (x 2 2)
                              have b18905 := hb (x 3 13)
                              have b18906 := hb (x 4 12)
                              clear * - r18900 e18901 e18902 b18903 b18904 b18905 b18906 f18898 f18421
                              omega
                            have d18907 : (x 4 2 && x 4 12).toNat = 0 := by
                              have r18908 := hand2 (x 4 2) (x 4 12)
                              have b18909 := hb (x 4 12)
                              have b18910 := hb (x 4 2 && x 4 12)
                              clear * - r18908 b18909 b18910 d18899
                              omega
                            have d18911 : (x 4 4).toNat = 0 := by
                              have r18912 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
                              have b18913 := hb (x 4 4)
                              have b18914 := hb (x 4 12)
                              clear * - r18912 b18913 b18914 d18899
                              omega
                            have d18915 : (x 3 13).toNat = 0 := by
                              have r18916 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e18917 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                              have e18918 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                              have b18919 := hb (x 1 3)
                              have b18920 := hb (x 2 2)
                              have b18921 := hb (x 3 13)
                              have b18922 := hb (x 4 12)
                              clear * - r18916 e18917 e18918 b18919 b18920 b18921 b18922 d18899 f18898 f18421
                              omega
                            have d18923 : (x 3 3 && x 3 13).toNat = 0 := by
                              have r18924 := hand2 (x 3 3) (x 3 13)
                              have b18925 := hb (x 3 13)
                              have b18926 := hb (x 3 3 && x 3 13)
                              clear * - r18924 b18925 b18926 d18915
                              omega
                            have d18927 : (x 3 5).toNat = 0 := by
                              have r18928 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
                              have b18929 := hb (x 3 5)
                              have b18930 := hb (x 3 13)
                              clear * - r18928 b18929 b18930 d18915
                              omega
                            have r18931 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r18932 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r18933 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e18934 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                            have e18935 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                            have e18936 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                            have e18937 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                            have e18938 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                            have e18939 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                            have r18940 : 1 ≤ (x 3 4).toNat + (x 2 1 && x 2 5).toNat + (x 1 2 && x 1 6).toNat + (x 0 3 && x 0 7).toNat + (x (-1) 4 && x (-1) 8).toNat + (x (-2) 5 && x (-2) 9).toNat + (x (-3) 6 && x (-3) 10).toNat + (x (-4) 7 && x (-4) 11).toNat + (x (-5) 8 && x (-5) 12).toNat + (x (-6) 9 && x (-6) 13).toNat + (x (-7) 10 && x (-7) 14).toNat + (x (-8) 11).toNat := by have q := hcov4 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e18941 : (x 2 1 && x 2 5).toNat = (x 2 5).toNat := handr _ _ (fun h => hp13 2 (hp5 2 (h)))
                            have e18942 : (x (-7) 10 && x (-7) 14).toNat = (x (-7) 10).toNat := handl _ _ (fun h => hp2 (-7) (hp10 (-7) (h)))
                            have r18943 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e18944 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
                            have e18945 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
                            have r18946 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r18947 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r18948 : (x (-11) 2).toNat ≤ (x (-11) 14).toNat := himp _ _ (hp2 (-11))
                            have r18949 := hand1 (x (-5) 8) (x (-5) 12)
                            have r18950 := hand1 (x (-6) 9) (x (-6) 13)
                            have r18951 := hand2 (x 2 2) (x 2 6)
                            have r18952 := hand1 (x (-4) 8) (x (-4) 12)
                            have r18953 := hand1 (x (-5) 9) (x (-5) 13)
                            have r18954 := hand2 (x 5 1) (x 5 11)
                            have r18955 := hand2 (x (-10) 1) (x (-10) 14)
                            linarith only [r18931, r18932, r18933, e18934, e18935, e18936, e18937, e18938, e18939, r18940, e18941, e18942, r18943, e18944, e18945, r18946, r18947, r18948, r18949, r18950, r18951, r18952, r18953, r18954, r18955, g0, g1, g2, g4, g5, g10, g11, g18, g19, g25, f18421, g27, f18427, f18618, f18898, g32, g35, d18927, d18911, g47, d18378, g48, g49, g50, g51, d18422, d18396, g52, g53, g54, d18907, d18923, g107]
                        · have f19017 : (x (-1) 7).toNat = 1 := by rw [h18647]; rfl
                          have d19018 : (x 6 8).toNat = 0 := by
                            have r19019 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e19020 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                            have e19021 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                            have e19022 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                            have e19023 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                            have e19024 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                            have e19025 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                            have b19026 := hb (x (-1) 7)
                            have b19027 := hb (x 0 6)
                            have b19028 := hb (x 1 5)
                            have b19029 := hb (x 2 4)
                            have b19030 := hb (x 3 11)
                            have b19031 := hb (x 4 10)
                            have b19032 := hb (x 5 9)
                            have b19033 := hb (x 6 8)
                            clear * - r19019 e19020 e19021 e19022 e19023 e19024 e19025 b19026 b19027 b19028 b19029 b19030 b19031 b19032 b19033 g31 g27 g21 f19017
                            omega
                          have d19034 : (x 6 1 && x 6 8).toNat = 0 := by
                            have r19035 := hand2 (x 6 1) (x 6 8)
                            have b19036 := hb (x 6 8)
                            have b19037 := hb (x 6 1 && x 6 8)
                            clear * - r19035 b19036 b19037 d19018
                            omega
                          have d19038 : (x 6 2 && x 6 8).toNat = 0 := by
                            have r19039 := hand2 (x 6 2) (x 6 8)
                            have b19040 := hb (x 6 8)
                            have b19041 := hb (x 6 2 && x 6 8)
                            clear * - r19039 b19040 b19041 d19018
                            omega
                          have d19042 : (x 6 3 && x 6 8).toNat = 0 := by
                            have r19043 := hand2 (x 6 3) (x 6 8)
                            have b19044 := hb (x 6 8)
                            have b19045 := hb (x 6 3 && x 6 8)
                            clear * - r19043 b19044 b19045 d19018
                            omega
                          have d19046 : (x 6 4 && x 6 8).toNat = 0 := by
                            have r19047 := hand2 (x 6 4) (x 6 8)
                            have b19048 := hb (x 6 8)
                            have b19049 := hb (x 6 4 && x 6 8)
                            clear * - r19047 b19048 b19049 d19018
                            omega
                          have d19050 : (x 5 9).toNat = 0 := by
                            have r19051 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e19052 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                            have e19053 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                            have e19054 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                            have e19055 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                            have e19056 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                            have e19057 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                            have b19058 := hb (x (-1) 7)
                            have b19059 := hb (x 0 6)
                            have b19060 := hb (x 1 5)
                            have b19061 := hb (x 2 4)
                            have b19062 := hb (x 3 11)
                            have b19063 := hb (x 4 10)
                            have b19064 := hb (x 5 9)
                            have b19065 := hb (x 6 8)
                            clear * - r19051 e19052 e19053 e19054 e19055 e19056 e19057 b19058 b19059 b19060 b19061 b19062 b19063 b19064 b19065 d19018 g31 g27 g21 f19017
                            omega
                          have d19066 : (x 5 2 && x 5 9).toNat = 0 := by
                            have r19067 := hand2 (x 5 2) (x 5 9)
                            have b19068 := hb (x 5 9)
                            have b19069 := hb (x 5 2 && x 5 9)
                            clear * - r19067 b19068 b19069 d19050
                            omega
                          have d19070 : (x 5 3 && x 5 9).toNat = 0 := by
                            have r19071 := hand2 (x 5 3) (x 5 9)
                            have b19072 := hb (x 5 9)
                            have b19073 := hb (x 5 3 && x 5 9)
                            clear * - r19071 b19072 b19073 d19050
                            omega
                          have d19074 : (x 5 4 && x 5 9).toNat = 0 := by
                            have r19075 := hand2 (x 5 4) (x 5 9)
                            have b19076 := hb (x 5 9)
                            have b19077 := hb (x 5 4 && x 5 9)
                            clear * - r19075 b19076 b19077 d19050
                            omega
                          have d19078 : (x 5 5 && x 5 9).toNat = 0 := by
                            have r19079 := hand2 (x 5 5) (x 5 9)
                            have b19080 := hb (x 5 9)
                            have b19081 := hb (x 5 5 && x 5 9)
                            clear * - r19079 b19080 b19081 d19050
                            omega
                          have d19082 : (x 4 10).toNat = 0 := by
                            have r19083 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e19084 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                            have e19085 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                            have e19086 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                            have e19087 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                            have e19088 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                            have e19089 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                            have b19090 := hb (x (-1) 7)
                            have b19091 := hb (x 0 6)
                            have b19092 := hb (x 1 5)
                            have b19093 := hb (x 2 4)
                            have b19094 := hb (x 3 11)
                            have b19095 := hb (x 4 10)
                            have b19096 := hb (x 5 9)
                            have b19097 := hb (x 6 8)
                            clear * - r19083 e19084 e19085 e19086 e19087 e19088 e19089 b19090 b19091 b19092 b19093 b19094 b19095 b19096 b19097 d19018 d19050 g31 g27 g21 f19017
                            omega
                          have d19098 : (x 4 3 && x 4 10).toNat = 0 := by
                            have r19099 := hand2 (x 4 3) (x 4 10)
                            have b19100 := hb (x 4 10)
                            have b19101 := hb (x 4 3 && x 4 10)
                            clear * - r19099 b19100 b19101 d19082
                            omega
                          have d19102 : (x 4 4 && x 4 10).toNat = 0 := by
                            have r19103 := hand2 (x 4 4) (x 4 10)
                            have b19104 := hb (x 4 10)
                            have b19105 := hb (x 4 4 && x 4 10)
                            clear * - r19103 b19104 b19105 d19082
                            omega
                          have d19106 : (x 4 5 && x 4 10).toNat = 0 := by
                            have r19107 := hand2 (x 4 5) (x 4 10)
                            have b19108 := hb (x 4 10)
                            have b19109 := hb (x 4 5 && x 4 10)
                            clear * - r19107 b19108 b19109 d19082
                            omega
                          have d19110 : (x 4 6 && x 4 10).toNat = 0 := by
                            have r19111 := hand2 (x 4 6) (x 4 10)
                            have b19112 := hb (x 4 10)
                            have b19113 := hb (x 4 6 && x 4 10)
                            clear * - r19111 b19112 b19113 d19082
                            omega
                          have d19114 : (x 3 11).toNat = 0 := by
                            have r19115 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e19116 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                            have e19117 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                            have e19118 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                            have e19119 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                            have e19120 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                            have e19121 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                            have b19122 := hb (x (-1) 7)
                            have b19123 := hb (x 0 6)
                            have b19124 := hb (x 1 5)
                            have b19125 := hb (x 2 4)
                            have b19126 := hb (x 3 11)
                            have b19127 := hb (x 4 10)
                            have b19128 := hb (x 5 9)
                            have b19129 := hb (x 6 8)
                            clear * - r19115 e19116 e19117 e19118 e19119 e19120 e19121 b19122 b19123 b19124 b19125 b19126 b19127 b19128 b19129 d19018 d19050 d19082 g31 g27 g21 f19017
                            omega
                          have d19130 : (x 3 5 && x 3 11).toNat = 0 := by
                            have r19131 := hand2 (x 3 5) (x 3 11)
                            have b19132 := hb (x 3 11)
                            have b19133 := hb (x 3 5 && x 3 11)
                            clear * - r19131 b19132 b19133 d19114
                            omega
                          have d19134 : (x 3 7 && x 3 11).toNat = 0 := by
                            have r19135 := hand2 (x 3 7) (x 3 11)
                            have b19136 := hb (x 3 11)
                            have b19137 := hb (x 3 7 && x 3 11)
                            clear * - r19135 b19136 b19137 d19114
                            omega
                          have d19138 : (x 7 7).toNat = 1 := by
                            have r19139 : 1 ≤ (x 7 7).toNat + (x 6 1 && x 6 8).toNat + (x 5 2 && x 5 9).toNat + (x 4 3 && x 4 10).toNat + (x 3 4 && x 3 11).toNat + (x 2 5 && x 2 12).toNat + (x 1 6 && x 1 13).toNat + (x 0 7 && x 0 14).toNat + (x (-1) 8).toNat := by have q := hcov7 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have b19140 := hb (x (-1) 8)
                            have b19141 := hb (x 7 7)
                            have b19142 := hb (x 6 1 && x 6 8)
                            have b19143 := hb (x 5 2 && x 5 9)
                            have b19144 := hb (x 4 3 && x 4 10)
                            have b19145 := hb (x 3 4 && x 3 11)
                            have b19146 := hb (x 2 5 && x 2 12)
                            have b19147 := hb (x 1 6 && x 1 13)
                            have b19148 := hb (x 0 7 && x 0 14)
                            clear * - r19139 b19140 b19141 b19142 b19143 b19144 b19145 b19146 b19147 b19148 d19034 d19066 d19098 g90 g91 g92 d18370 f18429
                            omega
                          have d19149 : (x 14 8).toNat = 0 := by
                            have r19150 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e19151 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                            have e19152 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                            have e19153 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                            have e19154 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                            have e19155 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                            have e19156 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                            have b19157 := hb (x 7 7)
                            have b19158 := hb (x 8 6)
                            have b19159 := hb (x 9 5)
                            have b19160 := hb (x 10 4)
                            have b19161 := hb (x 11 11)
                            have b19162 := hb (x 12 10)
                            have b19163 := hb (x 13 9)
                            have b19164 := hb (x 14 8)
                            clear * - r19150 e19151 e19152 e19153 e19154 e19155 e19156 b19157 b19158 b19159 b19160 b19161 b19162 b19163 b19164 d19138
                            omega
                          have d19165 : (x 13 9).toNat = 0 := by
                            have r19166 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e19167 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                            have e19168 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                            have e19169 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                            have e19170 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                            have e19171 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                            have e19172 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                            have b19173 := hb (x 7 7)
                            have b19174 := hb (x 8 6)
                            have b19175 := hb (x 9 5)
                            have b19176 := hb (x 10 4)
                            have b19177 := hb (x 11 11)
                            have b19178 := hb (x 12 10)
                            have b19179 := hb (x 13 9)
                            have b19180 := hb (x 14 8)
                            clear * - r19166 e19167 e19168 e19169 e19170 e19171 e19172 b19173 b19174 b19175 b19176 b19177 b19178 b19179 b19180 d19149 d19138
                            omega
                          have d19181 : (x 12 10).toNat = 0 := by
                            have r19182 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e19183 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                            have e19184 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                            have e19185 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                            have e19186 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                            have e19187 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                            have e19188 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                            have b19189 := hb (x 7 7)
                            have b19190 := hb (x 8 6)
                            have b19191 := hb (x 9 5)
                            have b19192 := hb (x 10 4)
                            have b19193 := hb (x 11 11)
                            have b19194 := hb (x 12 10)
                            have b19195 := hb (x 13 9)
                            have b19196 := hb (x 14 8)
                            clear * - r19182 e19183 e19184 e19185 e19186 e19187 e19188 b19189 b19190 b19191 b19192 b19193 b19194 b19195 b19196 d19149 d19165 d19138
                            omega
                          have d19197 : (x 12 1 && x 12 10).toNat = 0 := by
                            have r19198 := hand2 (x 12 1) (x 12 10)
                            have b19199 := hb (x 12 10)
                            have b19200 := hb (x 12 1 && x 12 10)
                            clear * - r19198 b19199 b19200 d19181
                            omega
                          have d19201 : (x 11 11).toNat = 0 := by
                            have r19202 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e19203 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                            have e19204 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                            have e19205 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                            have e19206 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                            have e19207 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                            have e19208 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                            have b19209 := hb (x 7 7)
                            have b19210 := hb (x 8 6)
                            have b19211 := hb (x 9 5)
                            have b19212 := hb (x 10 4)
                            have b19213 := hb (x 11 11)
                            have b19214 := hb (x 12 10)
                            have b19215 := hb (x 13 9)
                            have b19216 := hb (x 14 8)
                            clear * - r19202 e19203 e19204 e19205 e19206 e19207 e19208 b19209 b19210 b19211 b19212 b19213 b19214 b19215 b19216 d19149 d19165 d19181 d19138
                            omega
                          have d19217 : (x 11 2 && x 11 11).toNat = 0 := by
                            have r19218 := hand2 (x 11 2) (x 11 11)
                            have b19219 := hb (x 11 11)
                            have b19220 := hb (x 11 2 && x 11 11)
                            clear * - r19218 b19219 b19220 d19201
                            omega
                          have d19221 : (x 10 4).toNat = 0 := by
                            have r19222 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e19223 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                            have e19224 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                            have e19225 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                            have e19226 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                            have e19227 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                            have e19228 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                            have b19229 := hb (x 7 7)
                            have b19230 := hb (x 8 6)
                            have b19231 := hb (x 9 5)
                            have b19232 := hb (x 10 4)
                            have b19233 := hb (x 11 11)
                            have b19234 := hb (x 12 10)
                            have b19235 := hb (x 13 9)
                            have b19236 := hb (x 14 8)
                            clear * - r19222 e19223 e19224 e19225 e19226 e19227 e19228 b19229 b19230 b19231 b19232 b19233 b19234 b19235 b19236 d19149 d19165 d19181 d19201 d19138
                            omega
                          have d19237 : (x 9 5).toNat = 0 := by
                            have r19238 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e19239 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                            have e19240 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                            have e19241 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                            have e19242 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                            have e19243 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                            have e19244 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                            have b19245 := hb (x 7 7)
                            have b19246 := hb (x 8 6)
                            have b19247 := hb (x 9 5)
                            have b19248 := hb (x 10 4)
                            have b19249 := hb (x 11 11)
                            have b19250 := hb (x 12 10)
                            have b19251 := hb (x 13 9)
                            have b19252 := hb (x 14 8)
                            clear * - r19238 e19239 e19240 e19241 e19242 e19243 e19244 b19245 b19246 b19247 b19248 b19249 b19250 b19251 b19252 d19149 d19165 d19181 d19201 d19221 d19138
                            omega
                          have d19253 : (x 8 6).toNat = 0 := by
                            have r19254 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e19255 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                            have e19256 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                            have e19257 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                            have e19258 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                            have e19259 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                            have e19260 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                            have b19261 := hb (x 7 7)
                            have b19262 := hb (x 8 6)
                            have b19263 := hb (x 9 5)
                            have b19264 := hb (x 10 4)
                            have b19265 := hb (x 11 11)
                            have b19266 := hb (x 12 10)
                            have b19267 := hb (x 13 9)
                            have b19268 := hb (x 14 8)
                            clear * - r19254 e19255 e19256 e19257 e19258 e19259 e19260 b19261 b19262 b19263 b19264 b19265 b19266 b19267 b19268 d19149 d19165 d19181 d19201 d19221 d19237 d19138
                            omega
                          have d19269 : (x 8 1 && x 8 6).toNat = 0 := by
                            have r19270 := hand2 (x 8 1) (x 8 6)
                            have b19271 := hb (x 8 6)
                            have b19272 := hb (x 8 1 && x 8 6)
                            clear * - r19270 b19271 b19272 d19253
                            omega
                          have d19273 : (x 8 2 && x 8 6).toNat = 0 := by
                            have r19274 := hand2 (x 8 2) (x 8 6)
                            have b19275 := hb (x 8 6)
                            have b19276 := hb (x 8 2 && x 8 6)
                            clear * - r19274 b19275 b19276 d19253
                            omega
                          have d19277 : (x 7 1 && x 7 7).toNat = 1 := by
                            have r19278 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have b19279 := hb (x (-1) 9)
                            have b19280 := hb (x 8 6)
                            have b19281 := hb (x 7 1 && x 7 7)
                            have b19282 := hb (x 6 2 && x 6 8)
                            have b19283 := hb (x 5 3 && x 5 9)
                            have b19284 := hb (x 4 4 && x 4 10)
                            have b19285 := hb (x 3 5 && x 3 11)
                            have b19286 := hb (x 2 6 && x 2 12)
                            have b19287 := hb (x 1 7 && x 1 13)
                            have b19288 := hb (x 0 8 && x 0 14)
                            clear * - r19278 b19279 b19280 b19281 b19282 b19283 b19284 b19285 b19286 b19287 b19288 d19253 d19038 d19070 d19102 d19130 g82 g83 d18388 g13
                            omega
                          have d19289 : (x 7 1).toNat = 1 := by
                            have r19290 := hand1 (x 7 1) (x 7 7)
                            have b19291 := hb (x 7 1)
                            have b19292 := hb (x 7 1 && x 7 7)
                            clear * - r19290 b19291 b19292 d19277
                            omega
                          have d19293 : (x 8 14).toNat = 0 := by
                            have r19294 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have b19295 := hb (x 7 1)
                            have b19296 := hb (x 8 14)
                            clear * - r19294 b19295 b19296 d19289
                            omega
                          have d19297 : (x 8 5 && x 8 14).toNat = 0 := by
                            have r19298 := hand2 (x 8 5) (x 8 14)
                            have b19299 := hb (x 8 14)
                            have b19300 := hb (x 8 5 && x 8 14)
                            clear * - r19298 b19299 b19300 d19293
                            omega
                          have d19301 : (x 8 2).toNat = 0 := by
                            have r19302 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
                            have b19303 := hb (x 8 2)
                            have b19304 := hb (x 8 14)
                            clear * - r19302 b19303 b19304 d19293
                            omega
                          have d19305 : (x 7 2 && x 7 7).toNat = 1 := by
                            have r19306 : 1 ≤ (x 9 5).toNat + (x 8 1 && x 8 6).toNat + (x 7 2 && x 7 7).toNat + (x 6 3 && x 6 8).toNat + (x 5 4 && x 5 9).toNat + (x 4 5 && x 4 10).toNat + (x 3 6 && x 3 11).toNat + (x 2 7 && x 2 12).toNat + (x 1 8 && x 1 13).toNat + (x 0 9 && x 0 14).toNat + (x (-1) 10).toNat := by have q := hcov5 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have b19307 := hb (x (-1) 10)
                            have b19308 := hb (x 9 5)
                            have b19309 := hb (x 8 1 && x 8 6)
                            have b19310 := hb (x 7 2 && x 7 7)
                            have b19311 := hb (x 6 3 && x 6 8)
                            have b19312 := hb (x 5 4 && x 5 9)
                            have b19313 := hb (x 4 5 && x 4 10)
                            have b19314 := hb (x 3 6 && x 3 11)
                            have b19315 := hb (x 2 7 && x 2 12)
                            have b19316 := hb (x 1 8 && x 1 13)
                            have b19317 := hb (x 0 9 && x 0 14)
                            clear * - r19306 b19307 b19308 b19309 b19310 b19311 b19312 b19313 b19314 b19315 b19316 b19317 d19237 d19269 d19042 d19074 d19106 d18635 g65 g66 d18406 g14
                            omega
                          have d19318 : (x 7 2).toNat = 1 := by
                            have r19319 := hand1 (x 7 2) (x 7 7)
                            have b19320 := hb (x 7 2)
                            have b19321 := hb (x 7 2 && x 7 7)
                            clear * - r19319 b19320 b19321 d19305
                            omega
                          have d19322 : (x 7 14).toNat = 1 := by
                            have r19323 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
                            have b19324 := hb (x 7 2)
                            have b19325 := hb (x 7 14)
                            clear * - r19323 b19324 b19325 d19318
                            omega
                          have d19326 : (x 6 1).toNat = 0 := by
                            have r19327 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have b19328 := hb (x 6 1)
                            have b19329 := hb (x 7 14)
                            clear * - r19327 b19328 b19329 d19322
                            omega
                          have d19330 : (x 6 13).toNat = 0 := by
                            have r19331 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
                            have b19332 := hb (x 6 1)
                            have b19333 := hb (x 6 13)
                            clear * - r19331 b19332 b19333 d19326
                            omega
                          have d19334 : (x 6 5).toNat = 0 := by
                            have r19335 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
                            have b19336 := hb (x 6 5)
                            have b19337 := hb (x 6 13)
                            clear * - r19335 b19336 b19337 d19330
                            omega
                          have d19338 : (x 6 9).toNat = 0 := by
                            have r19339 : (x 6 9).toNat ≤ (x 6 1).toNat := himp _ _ (hp9 6)
                            have b19340 := hb (x 6 1)
                            have b19341 := hb (x 6 9)
                            clear * - r19339 b19340 b19341 d19326
                            omega
                          have d19342 : (x 9 12).toNat = 0 := by
                            have r19343 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e19344 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                            have e19345 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                            have b19346 := hb (x 6 3)
                            have b19347 := hb (x 7 2)
                            have b19348 := hb (x 8 13)
                            have b19349 := hb (x 9 12)
                            clear * - r19343 e19344 e19345 b19346 b19347 b19348 b19349 d19318
                            omega
                          have d19350 : (x 9 2 && x 9 12).toNat = 0 := by
                            have r19351 := hand2 (x 9 2) (x 9 12)
                            have b19352 := hb (x 9 12)
                            have b19353 := hb (x 9 2 && x 9 12)
                            clear * - r19351 b19352 b19353 d19342
                            omega
                          have d19354 : (x 9 4).toNat = 0 := by
                            have r19355 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
                            have b19356 := hb (x 9 4)
                            have b19357 := hb (x 9 12)
                            clear * - r19355 b19356 b19357 d19342
                            omega
                          have d19358 : (x 9 4 && x 9 13).toNat = 0 := by
                            have r19359 := hand1 (x 9 4) (x 9 13)
                            have b19360 := hb (x 9 4)
                            have b19361 := hb (x 9 4 && x 9 13)
                            clear * - r19359 b19360 b19361 d19354
                            omega
                          have d19362 : (x 8 13).toNat = 0 := by
                            have r19363 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e19364 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                            have e19365 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                            have b19366 := hb (x 6 3)
                            have b19367 := hb (x 7 2)
                            have b19368 := hb (x 8 13)
                            have b19369 := hb (x 9 12)
                            clear * - r19363 e19364 e19365 b19366 b19367 b19368 b19369 d19342 d19318
                            omega
                          have d19370 : (x 8 3 && x 8 13).toNat = 0 := by
                            have r19371 := hand2 (x 8 3) (x 8 13)
                            have b19372 := hb (x 8 13)
                            have b19373 := hb (x 8 3 && x 8 13)
                            clear * - r19371 b19372 b19373 d19362
                            omega
                          have d19374 : (x 8 5).toNat = 0 := by
                            have r19375 : (x 8 5).toNat ≤ (x 8 13).toNat := himp _ _ (hp5 8)
                            have b19376 := hb (x 8 5)
                            have b19377 := hb (x 8 13)
                            clear * - r19375 b19376 b19377 d19362
                            omega
                          have d19378 : (x 7 3 && x 7 7).toNat = 1 := by
                            have r19379 : 1 ≤ (x 10 4).toNat + (x 9 1 && x 9 5).toNat + (x 8 2 && x 8 6).toNat + (x 7 3 && x 7 7).toNat + (x 6 4 && x 6 8).toNat + (x 5 5 && x 5 9).toNat + (x 4 6 && x 4 10).toNat + (x 3 7 && x 3 11).toNat + (x 2 8 && x 2 12).toNat + (x 1 9 && x 1 13).toNat + (x 0 10 && x 0 14).toNat + (x (-1) 11).toNat := by have q := hcov4 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e19380 : (x 9 1 && x 9 5).toNat = (x 9 5).toNat := handr _ _ (fun h => hp13 9 (hp5 9 (h)))
                            have e19381 : (x 0 10 && x 0 14).toNat = (x 0 10).toNat := handl _ _ (fun h => hp2 0 (hp10 0 (h)))
                            have b19382 := hb (x (-1) 11)
                            have b19383 := hb (x 0 10)
                            have b19384 := hb (x 9 5)
                            have b19385 := hb (x 10 4)
                            have b19386 := hb (x 8 2 && x 8 6)
                            have b19387 := hb (x 7 3 && x 7 7)
                            have b19388 := hb (x 6 4 && x 6 8)
                            have b19389 := hb (x 5 5 && x 5 9)
                            have b19390 := hb (x 4 6 && x 4 10)
                            have b19391 := hb (x 3 7 && x 3 11)
                            have b19392 := hb (x 2 8 && x 2 12)
                            have b19393 := hb (x 1 9 && x 1 13)
                            clear * - r19379 e19380 e19381 b19382 b19383 b19384 b19385 b19386 b19387 b19388 b19389 b19390 b19391 b19392 b19393 d19221 d19237 d19273 d19046 d19078 d19110 d19134 g55 g56 g22 g15
                            omega
                          have d19394 : (x 7 3).toNat = 1 := by
                            have r19395 := hand1 (x 7 3) (x 7 7)
                            have b19396 := hb (x 7 3)
                            have b19397 := hb (x 7 3 && x 7 7)
                            clear * - r19395 b19396 b19397 d19378
                            omega
                          have d19398 : (x 10 12).toNat = 0 := by
                            have r19399 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e19400 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                            have e19401 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                            have b19402 := hb (x 7 3)
                            have b19403 := hb (x 8 2)
                            have b19404 := hb (x 9 13)
                            have b19405 := hb (x 10 12)
                            clear * - r19399 e19400 e19401 b19402 b19403 b19404 b19405 d19301 d19394
                            omega
                          have d19406 : (x 10 3 && x 10 12).toNat = 0 := by
                            have r19407 := hand2 (x 10 3) (x 10 12)
                            have b19408 := hb (x 10 12)
                            have b19409 := hb (x 10 3 && x 10 12)
                            clear * - r19407 b19408 b19409 d19398
                            omega
                          have d19410 : (x 7 6).toNat = 1 := by
                            have r19411 : 1 ≤ (x 13 9).toNat + (x 12 1 && x 12 10).toNat + (x 11 2 && x 11 11).toNat + (x 10 3 && x 10 12).toNat + (x 9 4 && x 9 13).toNat + (x 8 5 && x 8 14).toNat + (x 7 6).toNat := by have q := hcov9 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have b19412 := hb (x 7 6)
                            have b19413 := hb (x 13 9)
                            have b19414 := hb (x 12 1 && x 12 10)
                            have b19415 := hb (x 11 2 && x 11 11)
                            have b19416 := hb (x 10 3 && x 10 12)
                            have b19417 := hb (x 9 4 && x 9 13)
                            have b19418 := hb (x 8 5 && x 8 14)
                            clear * - r19411 b19412 b19413 b19414 b19415 b19416 b19417 b19418 d19165 d19197 d19217 d19406 d19358 d19297
                            omega
                          have d19419 : (x 13 8).toNat = 0 := by
                            have r19420 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e19421 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                            have e19422 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                            have e19423 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                            have e19424 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                            have e19425 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                            have e19426 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                            have b19427 := hb (x 6 7)
                            have b19428 := hb (x 7 6)
                            have b19429 := hb (x 8 5)
                            have b19430 := hb (x 9 4)
                            have b19431 := hb (x 10 11)
                            have b19432 := hb (x 11 10)
                            have b19433 := hb (x 12 9)
                            have b19434 := hb (x 13 8)
                            clear * - r19420 e19421 e19422 e19423 e19424 e19425 e19426 b19427 b19428 b19429 b19430 b19431 b19432 b19433 b19434 d19354 d19374 d19410
                            omega
                          have d19435 : (x 12 9).toNat = 0 := by
                            have r19436 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e19437 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                            have e19438 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                            have e19439 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                            have e19440 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                            have e19441 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                            have e19442 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                            have b19443 := hb (x 6 7)
                            have b19444 := hb (x 7 6)
                            have b19445 := hb (x 8 5)
                            have b19446 := hb (x 9 4)
                            have b19447 := hb (x 10 11)
                            have b19448 := hb (x 11 10)
                            have b19449 := hb (x 12 9)
                            have b19450 := hb (x 13 8)
                            clear * - r19436 e19437 e19438 e19439 e19440 e19441 e19442 b19443 b19444 b19445 b19446 b19447 b19448 b19449 b19450 d19419 d19354 d19374 d19410
                            omega
                          have d19451 : (x 11 10).toNat = 0 := by
                            have r19452 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e19453 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                            have e19454 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                            have e19455 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                            have e19456 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                            have e19457 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                            have e19458 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                            have b19459 := hb (x 6 7)
                            have b19460 := hb (x 7 6)
                            have b19461 := hb (x 8 5)
                            have b19462 := hb (x 9 4)
                            have b19463 := hb (x 10 11)
                            have b19464 := hb (x 11 10)
                            have b19465 := hb (x 12 9)
                            have b19466 := hb (x 13 8)
                            clear * - r19452 e19453 e19454 e19455 e19456 e19457 e19458 b19459 b19460 b19461 b19462 b19463 b19464 b19465 b19466 d19419 d19435 d19354 d19374 d19410
                            omega
                          have d19467 : (x 10 11).toNat = 0 := by
                            have r19468 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e19469 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                            have e19470 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                            have e19471 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                            have e19472 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                            have e19473 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                            have e19474 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                            have b19475 := hb (x 6 7)
                            have b19476 := hb (x 7 6)
                            have b19477 := hb (x 8 5)
                            have b19478 := hb (x 9 4)
                            have b19479 := hb (x 10 11)
                            have b19480 := hb (x 11 10)
                            have b19481 := hb (x 12 9)
                            have b19482 := hb (x 13 8)
                            clear * - r19468 e19469 e19470 e19471 e19472 e19473 e19474 b19475 b19476 b19477 b19478 b19479 b19480 b19481 b19482 d19419 d19435 d19451 d19354 d19374 d19410
                            omega
                          have d19483 : (x 10 1 && x 10 11).toNat = 0 := by
                            have r19484 := hand2 (x 10 1) (x 10 11)
                            have b19485 := hb (x 10 11)
                            have b19486 := hb (x 10 1 && x 10 11)
                            clear * - r19484 b19485 b19486 d19467
                            omega
                          have d19487 : (x 7 4 && x 7 14).toNat = 1 := by
                            have r19488 : 1 ≤ (x 11 10).toNat + (x 10 1 && x 10 11).toNat + (x 9 2 && x 9 12).toNat + (x 8 3 && x 8 13).toNat + (x 7 4 && x 7 14).toNat + (x 6 5).toNat := by have q := hcov10 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have b19489 := hb (x 6 5)
                            have b19490 := hb (x 11 10)
                            have b19491 := hb (x 10 1 && x 10 11)
                            have b19492 := hb (x 9 2 && x 9 12)
                            have b19493 := hb (x 8 3 && x 8 13)
                            have b19494 := hb (x 7 4 && x 7 14)
                            clear * - r19488 b19489 b19490 b19491 b19492 b19493 b19494 d19451 d19483 d19350 d19370 d19334
                            omega
                          have d19495 : (x 7 4).toNat = 1 := by
                            have r19496 := hand1 (x 7 4) (x 7 14)
                            have b19497 := hb (x 7 4)
                            have b19498 := hb (x 7 4 && x 7 14)
                            clear * - r19496 b19497 b19498 d19487
                            omega
                          have d19499 : (x 7 12).toNat = 1 := by
                            have r19500 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
                            have b19501 := hb (x 7 4)
                            have b19502 := hb (x 7 12)
                            clear * - r19500 b19501 b19502 d19495
                            omega
                          have d19503 : (x 5 2).toNat = 0 := by
                            have r19504 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e19505 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                            have e19506 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                            have b19507 := hb (x 4 3)
                            have b19508 := hb (x 5 2)
                            have b19509 := hb (x 6 13)
                            have b19510 := hb (x 7 12)
                            clear * - r19504 e19505 e19506 b19507 b19508 b19509 b19510 d19499 d19330
                            omega
                          have d19511 : (x 5 10).toNat = 0 := by
                            have r19512 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
                            have b19513 := hb (x 5 2)
                            have b19514 := hb (x 5 10)
                            clear * - r19512 b19513 b19514 d19503
                            omega
                          have d19515 : (x 5 1 && x 5 10).toNat = 0 := by
                            have r19516 := hand2 (x 5 1) (x 5 10)
                            have b19517 := hb (x 5 10)
                            have b19518 := hb (x 5 1 && x 5 10)
                            clear * - r19516 b19517 b19518 d19511
                            omega
                          have d19519 : (x 4 2 && x 4 11).toNat = 1 := by
                            have r19520 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have b19521 := hb (x 0 6)
                            have b19522 := hb (x 6 9)
                            have b19523 := hb (x 5 1 && x 5 10)
                            have b19524 := hb (x 4 2 && x 4 11)
                            have b19525 := hb (x 3 3 && x 3 12)
                            have b19526 := hb (x 2 4 && x 2 13)
                            have b19527 := hb (x 1 5 && x 1 14)
                            clear * - r19520 b19521 b19522 b19523 b19524 b19525 b19526 b19527 d19338 d19515 g98 g99 g100 g21
                            omega
                          have d19528 : (x 4 11).toNat = 1 := by
                            have r19529 := hand2 (x 4 2) (x 4 11)
                            have b19530 := hb (x 4 11)
                            have b19531 := hb (x 4 2 && x 4 11)
                            clear * - r19529 b19530 b19531 d19519
                            omega
                          have d19532 : (x 4 3).toNat = 1 := by
                            have r19533 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
                            have b19534 := hb (x 4 3)
                            have b19535 := hb (x 4 11)
                            clear * - r19533 b19534 b19535 d19528
                            omega
                          have r19536 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e19537 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                          have e19538 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                          have b19539 := hb (x 4 3)
                          have b19540 := hb (x 5 2)
                          have b19541 := hb (x 6 13)
                          have b19542 := hb (x 7 12)
                          linarith only [r19536, e19537, e19538, b19539, b19540, b19541, b19542, d19499, d19330, d19503, d19532]
                    · have f19543 : (x (-1) 14).toNat = 1 := by rw [h18438]; rfl
                      have d19544 : (x (-2) 1).toNat = 0 := by
                        have r19545 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b19546 := hb (x (-2) 1)
                        have b19547 := hb (x (-1) 14)
                        clear * - r19545 b19546 b19547 f19543
                        omega
                      have d19548 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
                        have r19549 := hand1 (x (-2) 1) (x (-2) 14)
                        have b19550 := hb (x (-2) 1)
                        have b19551 := hb (x (-2) 1 && x (-2) 14)
                        clear * - r19549 b19550 b19551 d19544
                        omega
                      have d19552 : (x (-2) 13).toNat = 0 := by
                        have r19553 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
                        have b19554 := hb (x (-2) 1)
                        have b19555 := hb (x (-2) 13)
                        clear * - r19553 b19554 b19555 d19544
                        omega
                      have d19556 : (x (-2) 9).toNat = 0 := by
                        have r19557 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
                        have b19558 := hb (x (-2) 1)
                        have b19559 := hb (x (-2) 9)
                        clear * - r19557 b19558 b19559 d19544
                        omega
                      have d19560 : (x (-3) 2).toNat = 1 := by
                        have r19561 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b19562 := hb (x (-3) 2)
                        have b19563 := hb (x (-1) 13)
                        have b19564 := hb (x (-2) 1 && x (-2) 14)
                        clear * - r19561 b19562 b19563 b19564 g16 d19548
                        omega
                      have d19565 : (x (-3) 14).toNat = 1 := by
                        have r19566 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
                        have b19567 := hb (x (-3) 2)
                        have b19568 := hb (x (-3) 14)
                        clear * - r19566 b19567 b19568 d19560
                        omega
                      have r19569 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r19570 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r19571 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r19572 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e19573 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
                      have e19574 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
                      have r19575 : 1 ≤ (x 11 5).toNat + (x 10 1 && x 10 6).toNat + (x 9 2 && x 9 7).toNat + (x 8 3 && x 8 8).toNat + (x 7 4 && x 7 9).toNat + (x 6 5 && x 6 10).toNat + (x 5 6 && x 5 11).toNat + (x 4 7 && x 4 12).toNat + (x 3 8 && x 3 13).toNat + (x 2 9 && x 2 14).toNat + (x 1 10).toNat := by have q := hcov5 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r19576 : 1 ≤ (x 7 6).toNat + (x 6 1 && x 6 7).toNat + (x 5 2 && x 5 8).toNat + (x 4 3 && x 4 9).toNat + (x 3 4 && x 3 10).toNat + (x 2 5 && x 2 11).toNat + (x 1 6 && x 1 12).toNat + (x 0 7 && x 0 13).toNat + (x (-1) 8 && x (-1) 14).toNat + (x (-2) 9).toNat := by have q := hcov6 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r19577 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r19578 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r19579 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r19580 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r19581 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
                      have r19582 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
                      have r19583 := hand2 (x 10 1) (x 10 6)
                      have r19584 := hand2 (x 9 2) (x 9 7)
                      have r19585 := hand2 (x 8 3) (x 8 8)
                      have r19586 := hand2 (x 7 4) (x 7 9)
                      have r19587 := hand1 (x 6 5) (x 6 10)
                      have r19588 := hand1 (x 5 6) (x 5 11)
                      have r19589 := hand1 (x 4 7) (x 4 12)
                      have r19590 := hand2 (x 6 1) (x 6 7)
                      have r19591 := hand2 (x 5 1) (x 5 11)
                      have r19592 := hand2 (x 4 2) (x 4 12)
                      have r19593 := hand2 (x 3 3) (x 3 13)
                      have r19594 := hand1 (x 10 1) (x 10 12)
                      have r19595 := hand1 (x 9 2) (x 9 13)
                      have r19596 := hand1 (x 8 3) (x 8 14)
                      have r19597 := hand1 (x 12 1) (x 12 12)
                      have r19598 := hand1 (x 11 2) (x 11 13)
                      have r19599 := hand1 (x 10 3) (x 10 14)
                      have r19600 := hand1 (x 12 1) (x 12 14)
                      linarith only [r19569, r19570, r19571, r19572, e19573, e19574, r19575, r19576, r19577, r19578, r19579, r19580, r19581, r19582, r19583, r19584, r19585, r19586, r19587, r19588, r19589, r19590, r19591, r19592, r19593, r19594, r19595, r19596, r19597, r19598, r19599, r19600, d19565, d19556, d19552, f18437, f19543, g23, g24, g27, g29, g30, g33, g34, d18416, g36, g37, g38, g39, g67, g68, g77, g78, g79, g80, g81, d18374, d18430, g107]
                  · have f19679 : (x (-1) 12).toNat = 1 := by rw [h18436]; rfl
                    have d19680 : (x (-2) 13).toNat = 0 := by
                      have r19681 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e19682 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                      have e19683 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                      have b19684 := hb (x (-4) 3)
                      have b19685 := hb (x (-3) 2)
                      have b19686 := hb (x (-2) 13)
                      have b19687 := hb (x (-1) 12)
                      clear * - r19681 e19682 e19683 b19684 b19685 b19686 b19687 f19679
                      omega
                    have d19688 : (x (-3) 2).toNat = 0 := by
                      have r19689 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e19690 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                      have e19691 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                      have b19692 := hb (x (-4) 3)
                      have b19693 := hb (x (-3) 2)
                      have b19694 := hb (x (-2) 13)
                      have b19695 := hb (x (-1) 12)
                      clear * - r19689 e19690 e19691 b19692 b19693 b19694 b19695 f19679 d19680
                      omega
                    have d19696 : (x (-3) 2 && x (-3) 13).toNat = 0 := by
                      have r19697 := hand1 (x (-3) 2) (x (-3) 13)
                      have b19698 := hb (x (-3) 2)
                      have b19699 := hb (x (-3) 2 && x (-3) 13)
                      clear * - r19697 b19698 b19699 d19688
                      omega
                    have d19700 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
                      have r19701 := hand1 (x (-3) 2) (x (-3) 12)
                      have b19702 := hb (x (-3) 2)
                      have b19703 := hb (x (-3) 2 && x (-3) 12)
                      clear * - r19701 b19702 b19703 d19688
                      omega
                    have d19704 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
                      have r19705 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b19706 := hb (x (-3) 2)
                      have b19707 := hb (x (-1) 13)
                      have b19708 := hb (x (-2) 1 && x (-2) 14)
                      clear * - r19705 b19706 b19707 b19708 g16 d19688
                      omega
                    have d19709 : (x (-2) 14).toNat = 1 := by
                      have r19710 := hand2 (x (-2) 1) (x (-2) 14)
                      have b19711 := hb (x (-2) 14)
                      have b19712 := hb (x (-2) 1 && x (-2) 14)
                      clear * - r19710 b19711 b19712 d19704
                      omega
                    have d19713 : (x (-3) 1).toNat = 0 := by
                      have r19714 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b19715 := hb (x (-3) 1)
                      have b19716 := hb (x (-2) 14)
                      clear * - r19714 b19715 b19716 d19709
                      omega
                    have d19717 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
                      have r19718 := hand1 (x (-3) 1) (x (-3) 14)
                      have b19719 := hb (x (-3) 1)
                      have b19720 := hb (x (-3) 1 && x (-3) 14)
                      clear * - r19718 b19719 b19720 d19713
                      omega
                    have d19721 : (x (-4) 2).toNat = 1 := by
                      have r19722 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b19723 := hb (x (-4) 2)
                      have b19724 := hb (x (-2) 13)
                      have b19725 := hb (x (-3) 1 && x (-3) 14)
                      clear * - r19722 b19723 b19724 b19725 d19680 d19717
                      omega
                    have d19726 : (x (-4) 14).toNat = 1 := by
                      have r19727 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
                      have b19728 := hb (x (-4) 2)
                      have b19729 := hb (x (-4) 14)
                      clear * - r19727 b19728 b19729 d19721
                      omega
                    have d19730 : (x (-5) 1).toNat = 0 := by
                      have r19731 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b19732 := hb (x (-5) 1)
                      have b19733 := hb (x (-4) 14)
                      clear * - r19731 b19732 b19733 d19726
                      omega
                    have d19734 : (x (-5) 13).toNat = 0 := by
                      have r19735 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
                      have b19736 := hb (x (-5) 1)
                      have b19737 := hb (x (-5) 13)
                      clear * - r19735 b19736 b19737 d19730
                      omega
                    have d19738 : (x (-3) 13).toNat = 0 := by
                      have r19739 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
                      have b19740 := hb (x (-3) 1)
                      have b19741 := hb (x (-3) 13)
                      clear * - r19739 b19740 b19741 d19713
                      omega
                    have d19742 : (x (-4) 3).toNat = 0 := by
                      have r19743 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e19744 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                      have e19745 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                      have b19746 := hb (x (-4) 3)
                      have b19747 := hb (x (-3) 2)
                      have b19748 := hb (x (-2) 13)
                      have b19749 := hb (x (-1) 12)
                      clear * - r19743 e19744 e19745 b19746 b19747 b19748 b19749 f19679 d19680 d19688
                      omega
                    have d19750 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
                      have r19751 := hand1 (x (-4) 3) (x (-4) 14)
                      have b19752 := hb (x (-4) 3)
                      have b19753 := hb (x (-4) 3 && x (-4) 14)
                      clear * - r19751 b19752 b19753 d19742
                      omega
                    have d19754 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
                      have r19755 := hand1 (x (-4) 3) (x (-4) 13)
                      have b19756 := hb (x (-4) 3)
                      have b19757 := hb (x (-4) 3 && x (-4) 13)
                      clear * - r19755 b19756 b19757 d19742
                      omega
                    have d19758 : (x (-2) 12).toNat = 0 := by
                      have r19759 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e19760 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                      have e19761 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                      have b19762 := hb (x (-5) 3)
                      have b19763 := hb (x (-4) 2)
                      have b19764 := hb (x (-3) 13)
                      have b19765 := hb (x (-2) 12)
                      clear * - r19759 e19760 e19761 b19762 b19763 b19764 b19765 d19738 d19721
                      omega
                    have d19766 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
                      have r19767 := hand2 (x (-2) 1) (x (-2) 12)
                      have b19768 := hb (x (-2) 12)
                      have b19769 := hb (x (-2) 1 && x (-2) 12)
                      clear * - r19767 b19768 b19769 d19758
                      omega
                    have d19770 : (x (-5) 4).toNat = 1 := by
                      have r19771 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b19772 := hb (x (-5) 4)
                      have b19773 := hb (x (-1) 11)
                      have b19774 := hb (x (-2) 1 && x (-2) 12)
                      have b19775 := hb (x (-3) 2 && x (-3) 13)
                      have b19776 := hb (x (-4) 3 && x (-4) 14)
                      clear * - r19771 b19772 b19773 b19774 b19775 b19776 g15 d19766 d19696 d19750
                      omega
                    have d19777 : (x (-5) 12).toNat = 1 := by
                      have r19778 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
                      have b19779 := hb (x (-5) 4)
                      have b19780 := hb (x (-5) 12)
                      clear * - r19778 b19779 b19780 d19770
                      omega
                    have d19781 : (x (-6) 13).toNat = 0 := by
                      have r19782 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e19783 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                      have e19784 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                      have b19785 := hb (x (-8) 3)
                      have b19786 := hb (x (-7) 2)
                      have b19787 := hb (x (-6) 13)
                      have b19788 := hb (x (-5) 12)
                      clear * - r19782 e19783 e19784 b19785 b19786 b19787 b19788 d19777
                      omega
                    have d19789 : (x (-6) 5).toNat = 0 := by
                      have r19790 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
                      have b19791 := hb (x (-6) 5)
                      have b19792 := hb (x (-6) 13)
                      clear * - r19790 b19791 b19792 d19781
                      omega
                    have d19793 : (x (-7) 2).toNat = 0 := by
                      have r19794 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e19795 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                      have e19796 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                      have b19797 := hb (x (-8) 3)
                      have b19798 := hb (x (-7) 2)
                      have b19799 := hb (x (-6) 13)
                      have b19800 := hb (x (-5) 12)
                      clear * - r19794 e19795 e19796 b19797 b19798 b19799 b19800 d19777 d19781
                      omega
                    have d19801 : (x (-6) 1 && x (-6) 14).toNat = 1 := by
                      have r19802 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b19803 := hb (x (-7) 2)
                      have b19804 := hb (x (-5) 13)
                      have b19805 := hb (x (-6) 1 && x (-6) 14)
                      clear * - r19802 b19803 b19804 b19805 d19734 d19793
                      omega
                    have d19806 : (x (-6) 1).toNat = 1 := by
                      have r19807 := hand1 (x (-6) 1) (x (-6) 14)
                      have b19808 := hb (x (-6) 1)
                      have b19809 := hb (x (-6) 1 && x (-6) 14)
                      clear * - r19807 b19808 b19809 d19801
                      omega
                    have d19810 : (x (-5) 14).toNat = 0 := by
                      have r19811 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b19812 := hb (x (-6) 1)
                      have b19813 := hb (x (-5) 14)
                      clear * - r19811 b19812 b19813 d19806
                      omega
                    have d19814 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
                      have r19815 := hand2 (x (-5) 4) (x (-5) 14)
                      have b19816 := hb (x (-5) 14)
                      have b19817 := hb (x (-5) 4 && x (-5) 14)
                      clear * - r19815 b19816 b19817 d19810
                      omega
                    have r19818 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b19819 := hb (x (-6) 5)
                    have b19820 := hb (x (-1) 10)
                    have b19821 := hb (x (-2) 1 && x (-2) 11)
                    have b19822 := hb (x (-3) 2 && x (-3) 12)
                    have b19823 := hb (x (-4) 3 && x (-4) 13)
                    have b19824 := hb (x (-5) 4 && x (-5) 14)
                    linarith only [r19818, b19819, b19820, b19821, b19822, b19823, b19824, g14, g103, d19700, d19754, d19814, d19789]
                · have f19825 : (x 1 8).toNat = 1 := by rw [h18434]; rfl
                  have d19826 : (x (-3) 4).toNat = 0 := by
                    have r19827 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19828 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                    have e19829 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                    have e19830 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                    have e19831 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                    have e19832 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                    have e19833 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                    have b19834 := hb (x (-6) 7)
                    have b19835 := hb (x (-5) 6)
                    have b19836 := hb (x (-4) 5)
                    have b19837 := hb (x (-3) 4)
                    have b19838 := hb (x (-2) 11)
                    have b19839 := hb (x (-1) 10)
                    have b19840 := hb (x 0 9)
                    have b19841 := hb (x 1 8)
                    clear * - r19827 e19828 e19829 e19830 e19831 e19832 e19833 b19834 b19835 b19836 b19837 b19838 b19839 b19840 b19841 f19825 f18401 g14 g8
                    omega
                  have d19842 : (x (-3) 4 && x (-3) 13).toNat = 0 := by
                    have r19843 := hand1 (x (-3) 4) (x (-3) 13)
                    have b19844 := hb (x (-3) 4)
                    have b19845 := hb (x (-3) 4 && x (-3) 13)
                    clear * - r19843 b19844 b19845 d19826
                    omega
                  have d19846 : (x (-4) 5).toNat = 0 := by
                    have r19847 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19848 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                    have e19849 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                    have e19850 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                    have e19851 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                    have e19852 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                    have e19853 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                    have b19854 := hb (x (-6) 7)
                    have b19855 := hb (x (-5) 6)
                    have b19856 := hb (x (-4) 5)
                    have b19857 := hb (x (-3) 4)
                    have b19858 := hb (x (-2) 11)
                    have b19859 := hb (x (-1) 10)
                    have b19860 := hb (x 0 9)
                    have b19861 := hb (x 1 8)
                    clear * - r19847 e19848 e19849 e19850 e19851 e19852 e19853 b19854 b19855 b19856 b19857 b19858 b19859 b19860 b19861 f19825 f18401 g14 g8 d19826
                    omega
                  have d19862 : (x (-4) 5 && x (-4) 14).toNat = 0 := by
                    have r19863 := hand1 (x (-4) 5) (x (-4) 14)
                    have b19864 := hb (x (-4) 5)
                    have b19865 := hb (x (-4) 5 && x (-4) 14)
                    clear * - r19863 b19864 b19865 d19846
                    omega
                  have d19866 : (x (-5) 6).toNat = 1 := by
                    have r19867 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b19868 := hb (x (-5) 6)
                    have b19869 := hb (x 1 9)
                    have b19870 := hb (x 0 1 && x 0 10)
                    have b19871 := hb (x (-1) 2 && x (-1) 11)
                    have b19872 := hb (x (-2) 3 && x (-2) 12)
                    have b19873 := hb (x (-3) 4 && x (-3) 13)
                    have b19874 := hb (x (-4) 5 && x (-4) 14)
                    clear * - r19867 b19868 b19869 b19870 b19871 b19872 b19873 b19874 d18412 g95 g96 g97 d19842 d19862
                    omega
                  have r19875 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e19876 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                  have e19877 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                  have e19878 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                  have e19879 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                  have e19880 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                  have e19881 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                  have b19882 := hb (x (-6) 7)
                  have b19883 := hb (x (-5) 6)
                  have b19884 := hb (x (-4) 5)
                  have b19885 := hb (x (-3) 4)
                  have b19886 := hb (x (-2) 11)
                  have b19887 := hb (x (-1) 10)
                  have b19888 := hb (x 0 9)
                  have b19889 := hb (x 1 8)
                  linarith only [r19875, e19876, e19877, e19878, e19879, e19880, e19881, b19882, b19883, b19884, b19885, b19886, b19887, b19888, b19889, f19825, f18401, g14, g8, d19826, d19846, d19866]
              · have f19890 : (x (-1) 8).toNat = 1 := by rw [h18428]; rfl
                have d19891 : (x (-2) 9).toNat = 0 := by
                  have r19892 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e19893 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                  have e19894 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                  have e19895 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                  have e19896 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                  have e19897 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                  have e19898 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                  have b19899 := hb (x (-8) 7)
                  have b19900 := hb (x (-7) 6)
                  have b19901 := hb (x (-6) 5)
                  have b19902 := hb (x (-5) 4)
                  have b19903 := hb (x (-4) 11)
                  have b19904 := hb (x (-3) 10)
                  have b19905 := hb (x (-2) 9)
                  have b19906 := hb (x (-1) 8)
                  clear * - r19892 e19893 e19894 e19895 e19896 e19897 e19898 b19899 b19900 b19901 b19902 b19903 b19904 b19905 b19906 f19890
                  omega
                have d19907 : (x (-3) 10).toNat = 0 := by
                  have r19908 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e19909 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                  have e19910 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                  have e19911 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                  have e19912 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                  have e19913 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                  have e19914 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                  have b19915 := hb (x (-8) 7)
                  have b19916 := hb (x (-7) 6)
                  have b19917 := hb (x (-6) 5)
                  have b19918 := hb (x (-5) 4)
                  have b19919 := hb (x (-4) 11)
                  have b19920 := hb (x (-3) 10)
                  have b19921 := hb (x (-2) 9)
                  have b19922 := hb (x (-1) 8)
                  clear * - r19908 e19909 e19910 e19911 e19912 e19913 e19914 b19915 b19916 b19917 b19918 b19919 b19920 b19921 b19922 f19890 d19891
                  omega
                have d19923 : (x (-4) 11).toNat = 0 := by
                  have r19924 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e19925 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                  have e19926 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                  have e19927 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                  have e19928 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                  have e19929 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                  have e19930 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                  have b19931 := hb (x (-8) 7)
                  have b19932 := hb (x (-7) 6)
                  have b19933 := hb (x (-6) 5)
                  have b19934 := hb (x (-5) 4)
                  have b19935 := hb (x (-4) 11)
                  have b19936 := hb (x (-3) 10)
                  have b19937 := hb (x (-2) 9)
                  have b19938 := hb (x (-1) 8)
                  clear * - r19924 e19925 e19926 e19927 e19928 e19929 e19930 b19931 b19932 b19933 b19934 b19935 b19936 b19937 b19938 f19890 d19891 d19907
                  omega
                have d19939 : (x (-4) 4 && x (-4) 11).toNat = 0 := by
                  have r19940 := hand2 (x (-4) 4) (x (-4) 11)
                  have b19941 := hb (x (-4) 11)
                  have b19942 := hb (x (-4) 4 && x (-4) 11)
                  clear * - r19940 b19941 b19942 d19923
                  omega
                have d19943 : (x (-5) 4).toNat = 0 := by
                  have r19944 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e19945 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                  have e19946 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                  have e19947 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                  have e19948 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                  have e19949 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                  have e19950 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                  have b19951 := hb (x (-8) 7)
                  have b19952 := hb (x (-7) 6)
                  have b19953 := hb (x (-6) 5)
                  have b19954 := hb (x (-5) 4)
                  have b19955 := hb (x (-4) 11)
                  have b19956 := hb (x (-3) 10)
                  have b19957 := hb (x (-2) 9)
                  have b19958 := hb (x (-1) 8)
                  clear * - r19944 e19945 e19946 e19947 e19948 e19949 e19950 b19951 b19952 b19953 b19954 b19955 b19956 b19957 b19958 f19890 d19891 d19907 d19923
                  omega
                have d19959 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
                  have r19960 := hand1 (x (-5) 4) (x (-5) 13)
                  have b19961 := hb (x (-5) 4)
                  have b19962 := hb (x (-5) 4 && x (-5) 13)
                  clear * - r19960 b19961 b19962 d19943
                  omega
                have d19963 : (x (-5) 4 && x (-5) 9).toNat = 0 := by
                  have r19964 := hand1 (x (-5) 4) (x (-5) 9)
                  have b19965 := hb (x (-5) 4)
                  have b19966 := hb (x (-5) 4 && x (-5) 9)
                  clear * - r19964 b19965 b19966 d19943
                  omega
                have d19967 : (x (-5) 4 && x (-5) 8).toNat = 0 := by
                  have r19968 := hand1 (x (-5) 4) (x (-5) 8)
                  have b19969 := hb (x (-5) 4)
                  have b19970 := hb (x (-5) 4 && x (-5) 8)
                  clear * - r19968 b19969 b19970 d19943
                  omega
                have d19971 : (x (-6) 5).toNat = 0 := by
                  have r19972 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e19973 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                  have e19974 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                  have e19975 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                  have e19976 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                  have e19977 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                  have e19978 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                  have b19979 := hb (x (-8) 7)
                  have b19980 := hb (x (-7) 6)
                  have b19981 := hb (x (-6) 5)
                  have b19982 := hb (x (-5) 4)
                  have b19983 := hb (x (-4) 11)
                  have b19984 := hb (x (-3) 10)
                  have b19985 := hb (x (-2) 9)
                  have b19986 := hb (x (-1) 8)
                  clear * - r19972 e19973 e19974 e19975 e19976 e19977 e19978 b19979 b19980 b19981 b19982 b19983 b19984 b19985 b19986 f19890 d19891 d19907 d19923 d19943
                  omega
                have d19987 : (x (-6) 5 && x (-6) 14).toNat = 0 := by
                  have r19988 := hand1 (x (-6) 5) (x (-6) 14)
                  have b19989 := hb (x (-6) 5)
                  have b19990 := hb (x (-6) 5 && x (-6) 14)
                  clear * - r19988 b19989 b19990 d19971
                  omega
                have d19991 : (x (-6) 5 && x (-6) 10).toNat = 0 := by
                  have r19992 := hand1 (x (-6) 5) (x (-6) 10)
                  have b19993 := hb (x (-6) 5)
                  have b19994 := hb (x (-6) 5 && x (-6) 10)
                  clear * - r19992 b19993 b19994 d19971
                  omega
                have d19995 : (x (-6) 5 && x (-6) 9).toNat = 0 := by
                  have r19996 := hand1 (x (-6) 5) (x (-6) 9)
                  have b19997 := hb (x (-6) 5)
                  have b19998 := hb (x (-6) 5 && x (-6) 9)
                  clear * - r19996 b19997 b19998 d19971
                  omega
                have d19999 : (x (-7) 6).toNat = 0 := by
                  have r20000 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e20001 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                  have e20002 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                  have e20003 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                  have e20004 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                  have e20005 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                  have e20006 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                  have b20007 := hb (x (-8) 7)
                  have b20008 := hb (x (-7) 6)
                  have b20009 := hb (x (-6) 5)
                  have b20010 := hb (x (-5) 4)
                  have b20011 := hb (x (-4) 11)
                  have b20012 := hb (x (-3) 10)
                  have b20013 := hb (x (-2) 9)
                  have b20014 := hb (x (-1) 8)
                  clear * - r20000 e20001 e20002 e20003 e20004 e20005 e20006 b20007 b20008 b20009 b20010 b20011 b20012 b20013 b20014 f19890 d19891 d19907 d19923 d19943 d19971
                  omega
                have d20015 : (x (-7) 6 && x (-7) 11).toNat = 0 := by
                  have r20016 := hand1 (x (-7) 6) (x (-7) 11)
                  have b20017 := hb (x (-7) 6)
                  have b20018 := hb (x (-7) 6 && x (-7) 11)
                  clear * - r20016 b20017 b20018 d19999
                  omega
                have d20019 : (x (-7) 6 && x (-7) 10).toNat = 0 := by
                  have r20020 := hand1 (x (-7) 6) (x (-7) 10)
                  have b20021 := hb (x (-7) 6)
                  have b20022 := hb (x (-7) 6 && x (-7) 10)
                  clear * - r20020 b20021 b20022 d19999
                  omega
                have d20023 : (x (-4) 3 && x (-4) 12).toNat = 1 := by
                  have r20024 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b20025 := hb (x (-7) 6)
                  have b20026 := hb (x (-1) 9)
                  have b20027 := hb (x (-2) 1 && x (-2) 10)
                  have b20028 := hb (x (-3) 2 && x (-3) 11)
                  have b20029 := hb (x (-4) 3 && x (-4) 12)
                  have b20030 := hb (x (-5) 4 && x (-5) 13)
                  have b20031 := hb (x (-6) 5 && x (-6) 14)
                  clear * - r20024 b20025 b20026 b20027 b20028 b20029 b20030 b20031 g13 g93 g94 d19959 d19987 d19999
                  omega
                have d20032 : (x (-4) 12).toNat = 1 := by
                  have r20033 := hand2 (x (-4) 3) (x (-4) 12)
                  have b20034 := hb (x (-4) 12)
                  have b20035 := hb (x (-4) 3 && x (-4) 12)
                  clear * - r20033 b20034 b20035 d20023
                  omega
                have d20036 : (x (-5) 13).toNat = 0 := by
                  have r20037 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e20038 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                  have e20039 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                  have b20040 := hb (x (-7) 3)
                  have b20041 := hb (x (-6) 2)
                  have b20042 := hb (x (-5) 13)
                  have b20043 := hb (x (-4) 12)
                  clear * - r20037 e20038 e20039 b20040 b20041 b20042 b20043 d20032
                  omega
                have d20044 : (x (-5) 5).toNat = 0 := by
                  have r20045 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
                  have b20046 := hb (x (-5) 5)
                  have b20047 := hb (x (-5) 13)
                  clear * - r20045 b20046 b20047 d20036
                  omega
                have d20048 : (x (-5) 5 && x (-5) 12).toNat = 0 := by
                  have r20049 := hand1 (x (-5) 5) (x (-5) 12)
                  have b20050 := hb (x (-5) 5)
                  have b20051 := hb (x (-5) 5 && x (-5) 12)
                  clear * - r20049 b20050 b20051 d20044
                  omega
                have d20052 : (x (-4) 4 && x (-4) 14).toNat = 1 := by
                  have r20053 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b20054 := hb (x (-5) 5)
                  have b20055 := hb (x 0 10)
                  have b20056 := hb (x (-1) 1 && x (-1) 11)
                  have b20057 := hb (x (-2) 2 && x (-2) 12)
                  have b20058 := hb (x (-3) 3 && x (-3) 13)
                  have b20059 := hb (x (-4) 4 && x (-4) 14)
                  clear * - r20053 b20054 b20055 b20056 b20057 b20058 b20059 g22 g104 g105 g106 d20044
                  omega
                have d20060 : (x (-4) 14).toNat = 1 := by
                  have r20061 := hand2 (x (-4) 4) (x (-4) 14)
                  have b20062 := hb (x (-4) 14)
                  have b20063 := hb (x (-4) 4 && x (-4) 14)
                  clear * - r20061 b20062 b20063 d20052
                  omega
                have d20064 : (x (-5) 1).toNat = 0 := by
                  have r20065 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b20066 := hb (x (-5) 1)
                  have b20067 := hb (x (-4) 14)
                  clear * - r20065 b20066 b20067 d20060
                  omega
                have d20068 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
                  have r20069 := hand1 (x (-5) 1) (x (-5) 12)
                  have b20070 := hb (x (-5) 1)
                  have b20071 := hb (x (-5) 1 && x (-5) 12)
                  clear * - r20069 b20070 b20071 d20064
                  omega
                have d20072 : (x (-5) 9).toNat = 0 := by
                  have r20073 : (x (-5) 9).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp9 (-5))
                  have b20074 := hb (x (-5) 1)
                  have b20075 := hb (x (-5) 9)
                  clear * - r20073 b20074 b20075 d20064
                  omega
                have d20076 : (x (-4) 4).toNat = 1 := by
                  have r20077 := hand1 (x (-4) 4) (x (-4) 14)
                  have b20078 := hb (x (-4) 4)
                  have b20079 := hb (x (-4) 4 && x (-4) 14)
                  clear * - r20077 b20078 b20079 d20052
                  omega
                have d20080 : (x (-6) 6).toNat = 0 := by
                  have r20081 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e20082 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                  have e20083 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                  have e20084 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                  have e20085 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                  have e20086 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                  have e20087 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                  have b20088 := hb (x (-7) 7)
                  have b20089 := hb (x (-6) 6)
                  have b20090 := hb (x (-5) 5)
                  have b20091 := hb (x (-4) 4)
                  have b20092 := hb (x (-3) 11)
                  have b20093 := hb (x (-2) 10)
                  have b20094 := hb (x (-1) 9)
                  have b20095 := hb (x 0 8)
                  clear * - r20081 e20082 e20083 e20084 e20085 e20086 e20087 b20088 b20089 b20090 b20091 b20092 b20093 b20094 b20095 f18383 g13 g7 g3 d20076 d20044
                  omega
                have d20096 : (x (-6) 6 && x (-6) 13).toNat = 0 := by
                  have r20097 := hand1 (x (-6) 6) (x (-6) 13)
                  have b20098 := hb (x (-6) 6)
                  have b20099 := hb (x (-6) 6 && x (-6) 13)
                  clear * - r20097 b20098 b20099 d20080
                  omega
                have d20100 : (x (-7) 7).toNat = 0 := by
                  have r20101 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e20102 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                  have e20103 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                  have e20104 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                  have e20105 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                  have e20106 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                  have e20107 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                  have b20108 := hb (x (-7) 7)
                  have b20109 := hb (x (-6) 6)
                  have b20110 := hb (x (-5) 5)
                  have b20111 := hb (x (-4) 4)
                  have b20112 := hb (x (-3) 11)
                  have b20113 := hb (x (-2) 10)
                  have b20114 := hb (x (-1) 9)
                  have b20115 := hb (x 0 8)
                  clear * - r20101 e20102 e20103 e20104 e20105 e20106 e20107 b20108 b20109 b20110 b20111 b20112 b20113 b20114 b20115 f18383 g13 g7 g3 d20076 d20044 d20080
                  omega
                have d20116 : (x (-7) 7 && x (-7) 14).toNat = 0 := by
                  have r20117 := hand1 (x (-7) 7) (x (-7) 14)
                  have b20118 := hb (x (-7) 7)
                  have b20119 := hb (x (-7) 7 && x (-7) 14)
                  clear * - r20117 b20118 b20119 d20100
                  omega
                have d20120 : (x (-6) 2).toNat = 0 := by
                  have r20121 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e20122 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                  have e20123 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                  have b20124 := hb (x (-7) 3)
                  have b20125 := hb (x (-6) 2)
                  have b20126 := hb (x (-5) 13)
                  have b20127 := hb (x (-4) 12)
                  clear * - r20121 e20122 e20123 b20124 b20125 b20126 b20127 d20032 d20036
                  omega
                have d20128 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
                  have r20129 := hand1 (x (-6) 2) (x (-6) 13)
                  have b20130 := hb (x (-6) 2)
                  have b20131 := hb (x (-6) 2 && x (-6) 13)
                  clear * - r20129 b20130 b20131 d20120
                  omega
                have d20132 : (x (-6) 10).toNat = 0 := by
                  have r20133 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
                  have b20134 := hb (x (-6) 2)
                  have b20135 := hb (x (-6) 10)
                  clear * - r20133 b20134 b20135 d20120
                  omega
                have d20136 : (x (-7) 3).toNat = 0 := by
                  have r20137 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e20138 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                  have e20139 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                  have b20140 := hb (x (-7) 3)
                  have b20141 := hb (x (-6) 2)
                  have b20142 := hb (x (-5) 13)
                  have b20143 := hb (x (-4) 12)
                  clear * - r20137 e20138 e20139 b20140 b20141 b20142 b20143 d20032 d20036 d20120
                  omega
                have d20144 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
                  have r20145 := hand1 (x (-7) 3) (x (-7) 14)
                  have b20146 := hb (x (-7) 3)
                  have b20147 := hb (x (-7) 3 && x (-7) 14)
                  clear * - r20145 b20146 b20147 d20136
                  omega
                have d20148 : (x (-8) 4).toNat = 1 := by
                  have r20149 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b20150 := hb (x (-8) 4)
                  have b20151 := hb (x (-4) 11)
                  have b20152 := hb (x (-5) 1 && x (-5) 12)
                  have b20153 := hb (x (-6) 2 && x (-6) 13)
                  have b20154 := hb (x (-7) 3 && x (-7) 14)
                  clear * - r20149 b20150 b20151 b20152 b20153 b20154 d19923 d20068 d20128 d20144
                  omega
                have d20155 : (x (-8) 12).toNat = 1 := by
                  have r20156 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
                  have b20157 := hb (x (-8) 4)
                  have b20158 := hb (x (-8) 12)
                  clear * - r20156 b20157 b20158 d20148
                  omega
                have d20159 : (x (-9) 13).toNat = 0 := by
                  have r20160 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e20161 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
                  have e20162 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
                  have b20163 := hb (x (-11) 3)
                  have b20164 := hb (x (-10) 2)
                  have b20165 := hb (x (-9) 13)
                  have b20166 := hb (x (-8) 12)
                  clear * - r20160 e20161 e20162 b20163 b20164 b20165 b20166 d20155
                  omega
                have d20167 : (x (-9) 8 && x (-9) 13).toNat = 0 := by
                  have r20168 := hand2 (x (-9) 8) (x (-9) 13)
                  have b20169 := hb (x (-9) 13)
                  have b20170 := hb (x (-9) 8 && x (-9) 13)
                  clear * - r20168 b20169 b20170 d20159
                  omega
                have d20171 : (x (-9) 5).toNat = 0 := by
                  have r20172 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
                  have b20173 := hb (x (-9) 5)
                  have b20174 := hb (x (-9) 13)
                  clear * - r20172 b20173 b20174 d20159
                  omega
                have d20175 : (x (-10) 2).toNat = 0 := by
                  have r20176 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e20177 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
                  have e20178 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
                  have b20179 := hb (x (-11) 3)
                  have b20180 := hb (x (-10) 2)
                  have b20181 := hb (x (-9) 13)
                  have b20182 := hb (x (-8) 12)
                  clear * - r20176 e20177 e20178 b20179 b20180 b20181 b20182 d20155 d20159
                  omega
                have d20183 : (x (-10) 10).toNat = 0 := by
                  have r20184 : (x (-10) 10).toNat ≤ (x (-10) 2).toNat := himp _ _ (hp10 (-10))
                  have b20185 := hb (x (-10) 2)
                  have b20186 := hb (x (-10) 10)
                  clear * - r20184 b20185 b20186 d20175
                  omega
                have d20187 : (x (-10) 1 && x (-10) 10).toNat = 0 := by
                  have r20188 := hand2 (x (-10) 1) (x (-10) 10)
                  have b20189 := hb (x (-10) 10)
                  have b20190 := hb (x (-10) 1 && x (-10) 10)
                  clear * - r20188 b20189 b20190 d20183
                  omega
                have d20191 : (x (-11) 3).toNat = 0 := by
                  have r20192 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e20193 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
                  have e20194 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
                  have b20195 := hb (x (-11) 3)
                  have b20196 := hb (x (-10) 2)
                  have b20197 := hb (x (-9) 13)
                  have b20198 := hb (x (-8) 12)
                  clear * - r20192 e20193 e20194 b20195 b20196 b20197 b20198 d20155 d20159 d20175
                  omega
                have d20199 : (x (-11) 11).toNat = 0 := by
                  have r20200 : (x (-11) 11).toNat ≤ (x (-11) 3).toNat := himp _ _ (hp11 (-11))
                  have b20201 := hb (x (-11) 3)
                  have b20202 := hb (x (-11) 11)
                  clear * - r20200 b20201 b20202 d20191
                  omega
                have d20203 : (x (-11) 2 && x (-11) 11).toNat = 0 := by
                  have r20204 := hand2 (x (-11) 2) (x (-11) 11)
                  have b20205 := hb (x (-11) 11)
                  have b20206 := hb (x (-11) 2 && x (-11) 11)
                  clear * - r20204 b20205 b20206 d20199
                  omega
                have d20207 : (x (-7) 11).toNat = 0 := by
                  have r20208 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
                  have b20209 := hb (x (-7) 3)
                  have b20210 := hb (x (-7) 11)
                  clear * - r20208 b20209 b20210 d20136
                  omega
                have d20211 : (x (-8) 7).toNat = 0 := by
                  have r20212 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e20213 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                  have e20214 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                  have e20215 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                  have e20216 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                  have e20217 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                  have e20218 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                  have b20219 := hb (x (-8) 7)
                  have b20220 := hb (x (-7) 6)
                  have b20221 := hb (x (-6) 5)
                  have b20222 := hb (x (-5) 4)
                  have b20223 := hb (x (-4) 11)
                  have b20224 := hb (x (-3) 10)
                  have b20225 := hb (x (-2) 9)
                  have b20226 := hb (x (-1) 8)
                  clear * - r20212 e20213 e20214 e20215 e20216 e20217 e20218 b20219 b20220 b20221 b20222 b20223 b20224 b20225 b20226 f19890 d19891 d19907 d19923 d19943 d19971 d19999
                  omega
                have d20227 : (x (-8) 7 && x (-8) 12).toNat = 0 := by
                  have r20228 := hand1 (x (-8) 7) (x (-8) 12)
                  have b20229 := hb (x (-8) 7)
                  have b20230 := hb (x (-8) 7 && x (-8) 12)
                  clear * - r20228 b20229 b20230 d20211
                  omega
                have d20231 : (x (-8) 7 && x (-8) 11).toNat = 0 := by
                  have r20232 := hand1 (x (-8) 7) (x (-8) 11)
                  have b20233 := hb (x (-8) 7)
                  have b20234 := hb (x (-8) 7 && x (-8) 11)
                  clear * - r20232 b20233 b20234 d20211
                  omega
                have d20235 : (x (-4) 8).toNat = 0 := by
                  have r20236 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e20237 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
                  have e20238 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
                  have e20239 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
                  have e20240 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
                  have e20241 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
                  have e20242 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
                  have b20243 := hb (x (-11) 7)
                  have b20244 := hb (x (-10) 6)
                  have b20245 := hb (x (-9) 5)
                  have b20246 := hb (x (-8) 4)
                  have b20247 := hb (x (-7) 11)
                  have b20248 := hb (x (-6) 10)
                  have b20249 := hb (x (-5) 9)
                  have b20250 := hb (x (-4) 8)
                  clear * - r20236 e20237 e20238 e20239 e20240 e20241 e20242 b20243 b20244 b20245 b20246 b20247 b20248 b20249 b20250 d20072 d20132 d20207 d20148 d20171
                  omega
                have d20251 : (x (-4) 3 && x (-4) 8).toNat = 0 := by
                  have r20252 := hand2 (x (-4) 3) (x (-4) 8)
                  have b20253 := hb (x (-4) 8)
                  have b20254 := hb (x (-4) 3 && x (-4) 8)
                  clear * - r20252 b20253 b20254 d20235
                  omega
                have d20255 : (x (-8) 8).toNat = 1 := by
                  have r20256 : 1 ≤ (x 0 7).toNat + (x (-1) 1 && x (-1) 8).toNat + (x (-2) 2 && x (-2) 9).toNat + (x (-3) 3 && x (-3) 10).toNat + (x (-4) 4 && x (-4) 11).toNat + (x (-5) 5 && x (-5) 12).toNat + (x (-6) 6 && x (-6) 13).toNat + (x (-7) 7 && x (-7) 14).toNat + (x (-8) 8).toNat := by have q := hcov7 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b20257 := hb (x (-8) 8)
                  have b20258 := hb (x 0 7)
                  have b20259 := hb (x (-1) 1 && x (-1) 8)
                  have b20260 := hb (x (-2) 2 && x (-2) 9)
                  have b20261 := hb (x (-3) 3 && x (-3) 10)
                  have b20262 := hb (x (-4) 4 && x (-4) 11)
                  have b20263 := hb (x (-5) 5 && x (-5) 12)
                  have b20264 := hb (x (-6) 6 && x (-6) 13)
                  have b20265 := hb (x (-7) 7 && x (-7) 14)
                  clear * - r20256 b20257 b20258 b20259 b20260 b20261 b20262 b20263 b20264 b20265 f18369 g84 g85 g86 d19939 d20048 d20096 d20116
                  omega
                have d20266 : (x (-9) 9).toNat = 0 := by
                  have r20267 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e20268 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
                  have e20269 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
                  have e20270 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
                  have e20271 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
                  have e20272 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
                  have e20273 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
                  have b20274 := hb (x (-15) 7)
                  have b20275 := hb (x (-14) 6)
                  have b20276 := hb (x (-13) 5)
                  have b20277 := hb (x (-12) 4)
                  have b20278 := hb (x (-11) 11)
                  have b20279 := hb (x (-10) 10)
                  have b20280 := hb (x (-9) 9)
                  have b20281 := hb (x (-8) 8)
                  clear * - r20267 e20268 e20269 e20270 e20271 e20272 e20273 b20274 b20275 b20276 b20277 b20278 b20279 b20280 b20281 d20255 d20183 d20199
                  omega
                have r20282 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20283 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
                have e20284 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
                have e20285 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
                have e20286 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
                have e20287 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
                have e20288 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
                have r20289 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20290 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
                have e20291 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
                have r20292 : 1 ≤ (x (-1) 4).toNat + (x (-2) 1 && x (-2) 5).toNat + (x (-3) 2 && x (-3) 6).toNat + (x (-4) 3 && x (-4) 7).toNat + (x (-5) 4 && x (-5) 8).toNat + (x (-6) 5 && x (-6) 9).toNat + (x (-7) 6 && x (-7) 10).toNat + (x (-8) 7 && x (-8) 11).toNat + (x (-9) 8 && x (-9) 12).toNat + (x (-10) 9 && x (-10) 13).toNat + (x (-11) 10 && x (-11) 14).toNat + (x (-12) 11).toNat := by have q := hcov4 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20293 : (x (-2) 1 && x (-2) 5).toNat = (x (-2) 5).toNat := handr _ _ (fun h => hp13 (-2) (hp5 (-2) (h)))
                have e20294 : (x (-11) 10 && x (-11) 14).toNat = (x (-11) 10).toNat := handl _ _ (fun h => hp2 (-11) (hp10 (-11) (h)))
                have r20295 : 1 ≤ (x (-1) 5).toNat + (x (-2) 1 && x (-2) 6).toNat + (x (-3) 2 && x (-3) 7).toNat + (x (-4) 3 && x (-4) 8).toNat + (x (-5) 4 && x (-5) 9).toNat + (x (-6) 5 && x (-6) 10).toNat + (x (-7) 6 && x (-7) 11).toNat + (x (-8) 7 && x (-8) 12).toNat + (x (-9) 8 && x (-9) 13).toNat + (x (-10) 9 && x (-10) 14).toNat + (x (-11) 10).toNat := by have q := hcov5 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r20296 : 1 ≤ (x (-9) 9).toNat + (x (-10) 1 && x (-10) 10).toNat + (x (-11) 2 && x (-11) 11).toNat + (x (-12) 3 && x (-12) 12).toNat + (x (-13) 4 && x (-13) 13).toNat + (x (-14) 5 && x (-14) 14).toNat + (x (-15) 6).toNat := by have q := hcov9 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r20297 : (x (-11) 10).toNat ≤ (x (-11) 2).toNat := himp _ _ (hp10 (-11))
                have r20298 := hand2 (x (-9) 8) (x (-9) 12)
                have r20299 := hand2 (x (-10) 9) (x (-10) 13)
                have r20300 := hand1 (x (-10) 9) (x (-10) 14)
                have r20301 := hand1 (x (-12) 3) (x (-12) 12)
                have r20302 := hand1 (x (-13) 4) (x (-13) 13)
                have r20303 := hand1 (x (-14) 5) (x (-14) 14)
                linarith only [r20282, e20283, e20284, e20285, e20286, e20287, e20288, r20289, e20290, e20291, r20292, e20293, e20294, r20295, r20296, r20297, r20298, r20299, r20300, r20301, r20302, r20303, d20266, g4, g10, g11, g44, g45, d19967, d19995, d20019, d20231, g57, g58, d20251, d19963, d19991, d20015, d20227, d20167, d20187, d20203]
            · have f20342 : (x 1 7).toNat = 1 := by rw [h18426]; rfl
              have d20343 : (x 8 8).toNat = 0 := by
                have r20344 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20345 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e20346 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e20347 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e20348 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e20349 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e20350 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b20351 := hb (x 1 7)
                have b20352 := hb (x 2 6)
                have b20353 := hb (x 3 5)
                have b20354 := hb (x 4 4)
                have b20355 := hb (x 5 11)
                have b20356 := hb (x 6 10)
                have b20357 := hb (x 7 9)
                have b20358 := hb (x 8 8)
                clear * - r20344 e20345 e20346 e20347 e20348 e20349 e20350 b20351 b20352 b20353 b20354 b20355 b20356 b20357 b20358 f20342
                omega
              have d20359 : (x 8 1 && x 8 8).toNat = 0 := by
                have r20360 := hand2 (x 8 1) (x 8 8)
                have b20361 := hb (x 8 8)
                have b20362 := hb (x 8 1 && x 8 8)
                clear * - r20360 b20361 b20362 d20343
                omega
              have d20363 : (x 8 3 && x 8 8).toNat = 0 := by
                have r20364 := hand2 (x 8 3) (x 8 8)
                have b20365 := hb (x 8 8)
                have b20366 := hb (x 8 3 && x 8 8)
                clear * - r20364 b20365 b20366 d20343
                omega
              have d20367 : (x 7 9).toNat = 0 := by
                have r20368 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20369 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e20370 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e20371 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e20372 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e20373 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e20374 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b20375 := hb (x 1 7)
                have b20376 := hb (x 2 6)
                have b20377 := hb (x 3 5)
                have b20378 := hb (x 4 4)
                have b20379 := hb (x 5 11)
                have b20380 := hb (x 6 10)
                have b20381 := hb (x 7 9)
                have b20382 := hb (x 8 8)
                clear * - r20368 e20369 e20370 e20371 e20372 e20373 e20374 b20375 b20376 b20377 b20378 b20379 b20380 b20381 b20382 d20343 f20342
                omega
              have d20383 : (x 7 2 && x 7 9).toNat = 0 := by
                have r20384 := hand2 (x 7 2) (x 7 9)
                have b20385 := hb (x 7 9)
                have b20386 := hb (x 7 2 && x 7 9)
                clear * - r20384 b20385 b20386 d20367
                omega
              have d20387 : (x 7 4 && x 7 9).toNat = 0 := by
                have r20388 := hand2 (x 7 4) (x 7 9)
                have b20389 := hb (x 7 9)
                have b20390 := hb (x 7 4 && x 7 9)
                clear * - r20388 b20389 b20390 d20367
                omega
              have d20391 : (x 6 10).toNat = 0 := by
                have r20392 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20393 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e20394 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e20395 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e20396 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e20397 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e20398 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b20399 := hb (x 1 7)
                have b20400 := hb (x 2 6)
                have b20401 := hb (x 3 5)
                have b20402 := hb (x 4 4)
                have b20403 := hb (x 5 11)
                have b20404 := hb (x 6 10)
                have b20405 := hb (x 7 9)
                have b20406 := hb (x 8 8)
                clear * - r20392 e20393 e20394 e20395 e20396 e20397 e20398 b20399 b20400 b20401 b20402 b20403 b20404 b20405 b20406 d20343 d20367 f20342
                omega
              have d20407 : (x 6 1 && x 6 10).toNat = 0 := by
                have r20408 := hand2 (x 6 1) (x 6 10)
                have b20409 := hb (x 6 10)
                have b20410 := hb (x 6 1 && x 6 10)
                clear * - r20408 b20409 b20410 d20391
                omega
              have d20411 : (x 6 3 && x 6 10).toNat = 0 := by
                have r20412 := hand2 (x 6 3) (x 6 10)
                have b20413 := hb (x 6 10)
                have b20414 := hb (x 6 3 && x 6 10)
                clear * - r20412 b20413 b20414 d20391
                omega
              have d20415 : (x 6 5 && x 6 10).toNat = 0 := by
                have r20416 := hand2 (x 6 5) (x 6 10)
                have b20417 := hb (x 6 10)
                have b20418 := hb (x 6 5 && x 6 10)
                clear * - r20416 b20417 b20418 d20391
                omega
              have d20419 : (x 5 11).toNat = 0 := by
                have r20420 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20421 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e20422 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e20423 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e20424 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e20425 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e20426 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b20427 := hb (x 1 7)
                have b20428 := hb (x 2 6)
                have b20429 := hb (x 3 5)
                have b20430 := hb (x 4 4)
                have b20431 := hb (x 5 11)
                have b20432 := hb (x 6 10)
                have b20433 := hb (x 7 9)
                have b20434 := hb (x 8 8)
                clear * - r20420 e20421 e20422 e20423 e20424 e20425 e20426 b20427 b20428 b20429 b20430 b20431 b20432 b20433 b20434 d20343 d20367 d20391 f20342
                omega
              have d20435 : (x 5 1 && x 5 11).toNat = 0 := by
                have r20436 := hand2 (x 5 1) (x 5 11)
                have b20437 := hb (x 5 11)
                have b20438 := hb (x 5 1 && x 5 11)
                clear * - r20436 b20437 b20438 d20419
                omega
              have d20439 : (x 5 2 && x 5 11).toNat = 0 := by
                have r20440 := hand2 (x 5 2) (x 5 11)
                have b20441 := hb (x 5 11)
                have b20442 := hb (x 5 2 && x 5 11)
                clear * - r20440 b20441 b20442 d20419
                omega
              have d20443 : (x 4 3 && x 4 12).toNat = 1 := by
                have r20444 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20445 := hb (x 1 6)
                have b20446 := hb (x 7 9)
                have b20447 := hb (x 6 1 && x 6 10)
                have b20448 := hb (x 5 2 && x 5 11)
                have b20449 := hb (x 4 3 && x 4 12)
                have b20450 := hb (x 3 4 && x 3 13)
                have b20451 := hb (x 2 5 && x 2 14)
                clear * - r20444 b20445 b20446 b20447 b20448 b20449 b20450 b20451 d20367 d20407 d20439 g101 g102 g28
                omega
              have d20452 : (x 4 12).toNat = 1 := by
                have r20453 := hand2 (x 4 3) (x 4 12)
                have b20454 := hb (x 4 12)
                have b20455 := hb (x 4 3 && x 4 12)
                clear * - r20453 b20454 b20455 d20443
                omega
              have d20456 : (x 3 13).toNat = 0 := by
                have r20457 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20458 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e20459 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b20460 := hb (x 1 3)
                have b20461 := hb (x 2 2)
                have b20462 := hb (x 3 13)
                have b20463 := hb (x 4 12)
                clear * - r20457 e20458 e20459 b20460 b20461 b20462 b20463 d20452 f18421
                omega
              have d20464 : (x 3 3 && x 3 13).toNat = 0 := by
                have r20465 := hand2 (x 3 3) (x 3 13)
                have b20466 := hb (x 3 13)
                have b20467 := hb (x 3 3 && x 3 13)
                clear * - r20465 b20466 b20467 d20456
                omega
              have d20468 : (x 4 2 && x 4 12).toNat = 1 := by
                have r20469 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20470 := hb (x 1 5)
                have b20471 := hb (x 6 10)
                have b20472 := hb (x 5 1 && x 5 11)
                have b20473 := hb (x 4 2 && x 4 12)
                have b20474 := hb (x 3 3 && x 3 13)
                have b20475 := hb (x 2 4 && x 2 14)
                clear * - r20469 b20470 b20471 b20472 b20473 b20474 b20475 d20391 d20435 d20464 g107 g27
                omega
              have d20476 : (x 4 2).toNat = 1 := by
                have r20477 := hand1 (x 4 2) (x 4 12)
                have b20478 := hb (x 4 2)
                have b20479 := hb (x 4 2 && x 4 12)
                clear * - r20477 b20478 b20479 d20468
                omega
              have d20480 : (x 4 14).toNat = 1 := by
                have r20481 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
                have b20482 := hb (x 4 2)
                have b20483 := hb (x 4 14)
                clear * - r20481 b20482 b20483 d20476
                omega
              have d20484 : (x 3 1).toNat = 0 := by
                have r20485 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20486 := hb (x 3 1)
                have b20487 := hb (x 4 14)
                clear * - r20485 b20486 b20487 d20480
                omega
              have d20488 : (x 3 1 && x 3 14).toNat = 0 := by
                have r20489 := hand1 (x 3 1) (x 3 14)
                have b20490 := hb (x 3 1)
                have b20491 := hb (x 3 1 && x 3 14)
                clear * - r20489 b20490 b20491 d20484
                omega
              have d20492 : (x 6 12).toNat = 0 := by
                have r20493 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20494 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                have e20495 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                have b20496 := hb (x 3 3)
                have b20497 := hb (x 4 2)
                have b20498 := hb (x 5 13)
                have b20499 := hb (x 6 12)
                clear * - r20493 e20494 e20495 b20496 b20497 b20498 b20499 d20476
                omega
              have d20500 : (x 5 13).toNat = 0 := by
                have r20501 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20502 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                have e20503 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                have b20504 := hb (x 3 3)
                have b20505 := hb (x 4 2)
                have b20506 := hb (x 5 13)
                have b20507 := hb (x 6 12)
                clear * - r20501 e20502 e20503 b20504 b20505 b20506 b20507 d20492 d20476
                omega
              have d20508 : (x 3 6 && x 3 13).toNat = 0 := by
                have r20509 := hand2 (x 3 6) (x 3 13)
                have b20510 := hb (x 3 13)
                have b20511 := hb (x 3 6 && x 3 13)
                clear * - r20509 b20510 b20511 d20456
                omega
              have d20512 : (x 3 5).toNat = 0 := by
                have r20513 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
                have b20514 := hb (x 3 5)
                have b20515 := hb (x 3 13)
                clear * - r20513 b20514 b20515 d20456
                omega
              have d20516 : (x 3 5 && x 3 14).toNat = 0 := by
                have r20517 := hand1 (x 3 5) (x 3 14)
                have b20518 := hb (x 3 5)
                have b20519 := hb (x 3 5 && x 3 14)
                clear * - r20517 b20518 b20519 d20512
                omega
              have d20520 : (x 2 1 && x 2 14).toNat = 1 := by
                have r20521 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20522 := hb (x 1 2)
                have b20523 := hb (x 3 13)
                have b20524 := hb (x 2 1 && x 2 14)
                clear * - r20521 b20522 b20523 b20524 d20456 g25
                omega
              have d20525 : (x 2 1).toNat = 1 := by
                have r20526 := hand1 (x 2 1) (x 2 14)
                have b20527 := hb (x 2 1)
                have b20528 := hb (x 2 1 && x 2 14)
                clear * - r20526 b20527 b20528 d20520
                omega
              have d20529 : (x 3 14).toNat = 0 := by
                have r20530 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20531 := hb (x 2 1)
                have b20532 := hb (x 3 14)
                clear * - r20530 b20531 b20532 d20525
                omega
              have d20533 : (x 3 6).toNat = 0 := by
                have r20534 : (x 3 6).toNat ≤ (x 3 14).toNat := himp _ _ (hp6 3)
                have b20535 := hb (x 3 6)
                have b20536 := hb (x 3 14)
                clear * - r20534 b20535 b20536 d20529
                omega
              have d20537 : (x 3 2).toNat = 0 := by
                have r20538 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
                have b20539 := hb (x 3 2)
                have b20540 := hb (x 3 14)
                clear * - r20538 b20539 b20540 d20529
                omega
              have d20541 : (x 4 1 && x 4 14).toNat = 1 := by
                have r20542 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20543 := hb (x 3 2)
                have b20544 := hb (x 5 13)
                have b20545 := hb (x 4 1 && x 4 14)
                clear * - r20542 b20543 b20544 b20545 d20500 d20537
                omega
              have d20546 : (x 4 1).toNat = 1 := by
                have r20547 := hand1 (x 4 1) (x 4 14)
                have b20548 := hb (x 4 1)
                have b20549 := hb (x 4 1 && x 4 14)
                clear * - r20547 b20548 b20549 d20541
                omega
              have d20550 : (x 5 14).toNat = 0 := by
                have r20551 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20552 := hb (x 4 1)
                have b20553 := hb (x 5 14)
                clear * - r20551 b20552 b20553 d20546
                omega
              have d20554 : (x 5 3 && x 5 14).toNat = 0 := by
                have r20555 := hand2 (x 5 3) (x 5 14)
                have b20556 := hb (x 5 14)
                have b20557 := hb (x 5 3 && x 5 14)
                clear * - r20555 b20556 b20557 d20550
                omega
              have d20558 : (x 5 6).toNat = 0 := by
                have r20559 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
                have b20560 := hb (x 5 6)
                have b20561 := hb (x 5 14)
                clear * - r20559 b20560 b20561 d20550
                omega
              have d20562 : (x 5 6 && x 5 11).toNat = 0 := by
                have r20563 := hand1 (x 5 6) (x 5 11)
                have b20564 := hb (x 5 6)
                have b20565 := hb (x 5 6 && x 5 11)
                clear * - r20563 b20564 b20565 d20558
                omega
              have d20566 : (x 5 2).toNat = 0 := by
                have r20567 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
                have b20568 := hb (x 5 2)
                have b20569 := hb (x 5 14)
                clear * - r20567 b20568 b20569 d20550
                omega
              have d20570 : (x 2 2).toNat = 0 := by
                have r20571 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20572 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e20573 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b20574 := hb (x 1 3)
                have b20575 := hb (x 2 2)
                have b20576 := hb (x 3 13)
                have b20577 := hb (x 4 12)
                clear * - r20571 e20572 e20573 b20574 b20575 b20576 b20577 d20452 d20456 f18421
                omega
              have d20578 : (x 4 13).toNat = 1 := by
                have r20579 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20580 := hb (x 2 2)
                have b20581 := hb (x 4 13)
                have b20582 := hb (x 3 1 && x 3 14)
                clear * - r20579 b20580 b20581 b20582 d20488 d20570
                omega
              have d20583 : (x 5 12).toNat = 0 := by
                have r20584 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20585 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                have e20586 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                have b20587 := hb (x 2 3)
                have b20588 := hb (x 3 2)
                have b20589 := hb (x 4 13)
                have b20590 := hb (x 5 12)
                clear * - r20584 e20585 e20586 b20587 b20588 b20589 b20590 d20578 d20537
                omega
              have d20591 : (x 5 3 && x 5 12).toNat = 0 := by
                have r20592 := hand2 (x 5 3) (x 5 12)
                have b20593 := hb (x 5 12)
                have b20594 := hb (x 5 3 && x 5 12)
                clear * - r20592 b20593 b20594 d20583
                omega
              have d20595 : (x 5 4).toNat = 0 := by
                have r20596 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
                have b20597 := hb (x 5 4)
                have b20598 := hb (x 5 12)
                clear * - r20596 b20597 b20598 d20583
                omega
              have d20599 : (x 5 4 && x 5 11).toNat = 0 := by
                have r20600 := hand1 (x 5 4) (x 5 11)
                have b20601 := hb (x 5 4)
                have b20602 := hb (x 5 4 && x 5 11)
                clear * - r20600 b20601 b20602 d20595
                omega
              have d20603 : (x 4 3).toNat = 1 := by
                have r20604 := hand1 (x 4 3) (x 4 12)
                have b20605 := hb (x 4 3)
                have b20606 := hb (x 4 3 && x 4 12)
                clear * - r20604 b20605 b20606 d20443
                omega
              have d20607 : (x 7 12).toNat = 0 := by
                have r20608 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20609 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                have e20610 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                have b20611 := hb (x 4 3)
                have b20612 := hb (x 5 2)
                have b20613 := hb (x 6 13)
                have b20614 := hb (x 7 12)
                clear * - r20608 e20609 e20610 b20611 b20612 b20613 b20614 d20566 d20603
                omega
              have d20615 : (x 7 1 && x 7 12).toNat = 0 := by
                have r20616 := hand2 (x 7 1) (x 7 12)
                have b20617 := hb (x 7 12)
                have b20618 := hb (x 7 1 && x 7 12)
                clear * - r20616 b20617 b20618 d20607
                omega
              have d20619 : (x 7 4).toNat = 0 := by
                have r20620 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
                have b20621 := hb (x 7 4)
                have b20622 := hb (x 7 12)
                clear * - r20620 b20621 b20622 d20607
                omega
              have d20623 : (x 6 13).toNat = 0 := by
                have r20624 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20625 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                have e20626 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                have b20627 := hb (x 4 3)
                have b20628 := hb (x 5 2)
                have b20629 := hb (x 6 13)
                have b20630 := hb (x 7 12)
                clear * - r20624 e20625 e20626 b20627 b20628 b20629 b20630 d20607 d20566 d20603
                omega
              have d20631 : (x 6 2 && x 6 13).toNat = 0 := by
                have r20632 := hand2 (x 6 2) (x 6 13)
                have b20633 := hb (x 6 13)
                have b20634 := hb (x 6 2 && x 6 13)
                clear * - r20632 b20633 b20634 d20623
                omega
              have d20635 : (x 6 5).toNat = 0 := by
                have r20636 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
                have b20637 := hb (x 6 5)
                have b20638 := hb (x 6 13)
                clear * - r20636 b20637 b20638 d20623
                omega
              have d20639 : (x 4 4).toNat = 0 := by
                have r20640 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20641 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e20642 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e20643 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e20644 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e20645 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e20646 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b20647 := hb (x 1 7)
                have b20648 := hb (x 2 6)
                have b20649 := hb (x 3 5)
                have b20650 := hb (x 4 4)
                have b20651 := hb (x 5 11)
                have b20652 := hb (x 6 10)
                have b20653 := hb (x 7 9)
                have b20654 := hb (x 8 8)
                clear * - r20640 e20641 e20642 e20643 e20644 e20645 e20646 b20647 b20648 b20649 b20650 b20651 b20652 b20653 b20654 d20343 d20367 d20391 d20419 d20512 f20342
                omega
              have d20655 : (x 4 4 && x 4 13).toNat = 0 := by
                have r20656 := hand1 (x 4 4) (x 4 13)
                have b20657 := hb (x 4 4)
                have b20658 := hb (x 4 4 && x 4 13)
                clear * - r20656 b20657 b20658 d20639
                omega
              have d20659 : (x 8 11).toNat = 1 := by
                have r20660 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20661 := hb (x 4 4)
                have b20662 := hb (x 8 11)
                have b20663 := hb (x 7 1 && x 7 12)
                have b20664 := hb (x 6 2 && x 6 13)
                have b20665 := hb (x 5 3 && x 5 14)
                clear * - r20660 b20661 b20662 b20663 b20664 b20665 d20615 d20631 d20554 d20639
                omega
              have d20666 : (x 8 3).toNat = 1 := by
                have r20667 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
                have b20668 := hb (x 8 3)
                have b20669 := hb (x 8 11)
                clear * - r20667 b20668 b20669 d20659
                omega
              have d20670 : (x 11 12).toNat = 0 := by
                have r20671 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20672 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                have e20673 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                have b20674 := hb (x 8 3)
                have b20675 := hb (x 9 2)
                have b20676 := hb (x 10 13)
                have b20677 := hb (x 11 12)
                clear * - r20671 e20672 e20673 b20674 b20675 b20676 b20677 d20666
                omega
              have d20678 : (x 10 13).toNat = 0 := by
                have r20679 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20680 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                have e20681 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                have b20682 := hb (x 8 3)
                have b20683 := hb (x 9 2)
                have b20684 := hb (x 10 13)
                have b20685 := hb (x 11 12)
                clear * - r20679 e20680 e20681 b20682 b20683 b20684 b20685 d20670 d20666
                omega
              have d20686 : (x 9 2).toNat = 0 := by
                have r20687 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20688 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                have e20689 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                have b20690 := hb (x 8 3)
                have b20691 := hb (x 9 2)
                have b20692 := hb (x 10 13)
                have b20693 := hb (x 11 12)
                clear * - r20687 e20688 e20689 b20690 b20691 b20692 b20693 d20670 d20678 d20666
                omega
              have d20694 : (x 9 2 && x 9 7).toNat = 0 := by
                have r20695 := hand1 (x 9 2) (x 9 7)
                have b20696 := hb (x 9 2)
                have b20697 := hb (x 9 2 && x 9 7)
                clear * - r20695 b20696 b20697 d20686
                omega
              have d20698 : (x 9 10).toNat = 0 := by
                have r20699 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
                have b20700 := hb (x 9 2)
                have b20701 := hb (x 9 10)
                clear * - r20699 b20700 b20701 d20686
                omega
              have d20702 : (x 11 8).toNat = 0 := by
                have r20703 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20704 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
                have e20705 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
                have e20706 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
                have e20707 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
                have e20708 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
                have e20709 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
                have b20710 := hb (x 4 7)
                have b20711 := hb (x 5 6)
                have b20712 := hb (x 6 5)
                have b20713 := hb (x 7 4)
                have b20714 := hb (x 8 11)
                have b20715 := hb (x 9 10)
                have b20716 := hb (x 10 9)
                have b20717 := hb (x 11 8)
                clear * - r20703 e20704 e20705 e20706 e20707 e20708 e20709 b20710 b20711 b20712 b20713 b20714 b20715 b20716 b20717 d20698 d20659 d20619 d20635 d20558
                omega
              have d20718 : (x 10 9).toNat = 0 := by
                have r20719 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20720 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
                have e20721 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
                have e20722 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
                have e20723 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
                have e20724 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
                have e20725 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
                have b20726 := hb (x 4 7)
                have b20727 := hb (x 5 6)
                have b20728 := hb (x 6 5)
                have b20729 := hb (x 7 4)
                have b20730 := hb (x 8 11)
                have b20731 := hb (x 9 10)
                have b20732 := hb (x 10 9)
                have b20733 := hb (x 11 8)
                clear * - r20719 e20720 e20721 e20722 e20723 e20724 e20725 b20726 b20727 b20728 b20729 b20730 b20731 b20732 b20733 d20702 d20698 d20659 d20619 d20635 d20558
                omega
              have d20734 : (x 4 7).toNat = 0 := by
                have r20735 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20736 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
                have e20737 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
                have e20738 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
                have e20739 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
                have e20740 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
                have e20741 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
                have b20742 := hb (x 4 7)
                have b20743 := hb (x 5 6)
                have b20744 := hb (x 6 5)
                have b20745 := hb (x 7 4)
                have b20746 := hb (x 8 11)
                have b20747 := hb (x 9 10)
                have b20748 := hb (x 10 9)
                have b20749 := hb (x 11 8)
                clear * - r20735 e20736 e20737 e20738 e20739 e20740 e20741 b20742 b20743 b20744 b20745 b20746 b20747 b20748 b20749 d20702 d20718 d20698 d20659 d20619 d20635 d20558
                omega
              have d20750 : (x 4 7 && x 4 12).toNat = 0 := by
                have r20751 := hand1 (x 4 7) (x 4 12)
                have b20752 := hb (x 4 7)
                have b20753 := hb (x 4 7 && x 4 12)
                clear * - r20751 b20752 b20753 d20734
                omega
              have d20754 : (x 2 6).toNat = 0 := by
                have r20755 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20756 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e20757 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e20758 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e20759 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e20760 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e20761 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b20762 := hb (x 1 7)
                have b20763 := hb (x 2 6)
                have b20764 := hb (x 3 5)
                have b20765 := hb (x 4 4)
                have b20766 := hb (x 5 11)
                have b20767 := hb (x 6 10)
                have b20768 := hb (x 7 9)
                have b20769 := hb (x 8 8)
                clear * - r20755 e20756 e20757 e20758 e20759 e20760 e20761 b20762 b20763 b20764 b20765 b20766 b20767 b20768 b20769 d20343 d20367 d20391 d20419 d20639 d20512 f20342
                omega
              have r20770 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r20771 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e20772 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
              have e20773 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
              have e20774 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
              have e20775 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
              have e20776 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
              have e20777 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
              have r20778 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e20779 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
              have e20780 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
              have e20781 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
              have e20782 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
              have e20783 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
              have e20784 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
              have r20785 : 1 ≤ (x 11 5).toNat + (x 10 1 && x 10 6).toNat + (x 9 2 && x 9 7).toNat + (x 8 3 && x 8 8).toNat + (x 7 4 && x 7 9).toNat + (x 6 5 && x 6 10).toNat + (x 5 6 && x 5 11).toNat + (x 4 7 && x 4 12).toNat + (x 3 8 && x 3 13).toNat + (x 2 9 && x 2 14).toNat + (x 1 10).toNat := by have q := hcov5 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r20786 : 1 ≤ (x 9 7).toNat + (x 8 1 && x 8 8).toNat + (x 7 2 && x 7 9).toNat + (x 6 3 && x 6 10).toNat + (x 5 4 && x 5 11).toNat + (x 4 5 && x 4 12).toNat + (x 3 6 && x 3 13).toNat + (x 2 7 && x 2 14).toNat + (x 1 8).toNat := by have q := hcov7 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r20787 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r20788 : 1 ≤ (x 8 9).toNat + (x 7 1 && x 7 10).toNat + (x 6 2 && x 6 11).toNat + (x 5 3 && x 5 12).toNat + (x 4 4 && x 4 13).toNat + (x 3 5 && x 3 14).toNat + (x 2 6).toNat := by have q := hcov9 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r20789 := hand2 (x 10 1) (x 10 6)
              have r20790 := hand1 (x 4 5) (x 4 12)
              have r20791 := hand1 (x 2 7) (x 2 14)
              have r20792 := hand1 (x (-3) 4) (x (-3) 13)
              have r20793 := hand1 (x (-4) 5) (x (-4) 14)
              have r20794 := hand2 (x 7 1) (x 7 10)
              have r20795 := hand2 (x 6 2) (x 6 11)
              linarith only [r20770, r20771, e20772, e20773, e20774, e20775, e20776, e20777, r20778, e20779, e20780, e20781, e20782, e20783, e20784, r20785, r20786, r20787, r20788, r20789, r20790, r20791, r20792, r20793, r20794, r20795, g8, g14, f18401, d18412, g29, d20754, d18416, d20533, d20456, d20452, d20595, d20419, d20391, d20367, d20343, d20694, d20363, d20387, d20415, d20562, d20750, g67, g68, d20359, d20383, d20411, d20599, d20508, g95, g96, g97, d20591, d20655, d20516]
          · have f20855 : (x 1 3).toNat = 1 := by rw [h18420]; rfl
            have d20856 : (x 4 12).toNat = 0 := by
              have r20857 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e20858 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e20859 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b20860 := hb (x 1 3)
              have b20861 := hb (x 2 2)
              have b20862 := hb (x 3 13)
              have b20863 := hb (x 4 12)
              clear * - r20857 e20858 e20859 b20860 b20861 b20862 b20863 f20855
              omega
            have d20864 : (x 4 1 && x 4 12).toNat = 0 := by
              have r20865 := hand2 (x 4 1) (x 4 12)
              have b20866 := hb (x 4 12)
              have b20867 := hb (x 4 1 && x 4 12)
              clear * - r20865 b20866 b20867 d20856
              omega
            have d20868 : (x 4 4).toNat = 0 := by
              have r20869 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
              have b20870 := hb (x 4 4)
              have b20871 := hb (x 4 12)
              clear * - r20869 b20870 b20871 d20856
              omega
            have d20872 : (x 3 13).toNat = 0 := by
              have r20873 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e20874 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e20875 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b20876 := hb (x 1 3)
              have b20877 := hb (x 2 2)
              have b20878 := hb (x 3 13)
              have b20879 := hb (x 4 12)
              clear * - r20873 e20874 e20875 b20876 b20877 b20878 b20879 d20856 f20855
              omega
            have d20880 : (x 3 2 && x 3 13).toNat = 0 := by
              have r20881 := hand2 (x 3 2) (x 3 13)
              have b20882 := hb (x 3 13)
              have b20883 := hb (x 3 2 && x 3 13)
              clear * - r20881 b20882 b20883 d20872
              omega
            have d20884 : (x 2 1 && x 2 14).toNat = 1 := by
              have r20885 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b20886 := hb (x 1 2)
              have b20887 := hb (x 3 13)
              have b20888 := hb (x 2 1 && x 2 14)
              clear * - r20885 b20886 b20887 b20888 d20872 g25
              omega
            have d20889 : (x 2 1).toNat = 1 := by
              have r20890 := hand1 (x 2 1) (x 2 14)
              have b20891 := hb (x 2 1)
              have b20892 := hb (x 2 1 && x 2 14)
              clear * - r20890 b20891 b20892 d20884
              omega
            have d20893 : (x 3 14).toNat = 0 := by
              have r20894 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b20895 := hb (x 2 1)
              have b20896 := hb (x 3 14)
              clear * - r20894 b20895 b20896 d20889
              omega
            have d20897 : (x 3 1 && x 3 14).toNat = 0 := by
              have r20898 := hand2 (x 3 1) (x 3 14)
              have b20899 := hb (x 3 14)
              have b20900 := hb (x 3 1 && x 3 14)
              clear * - r20898 b20899 b20900 d20893
              omega
            have d20901 : (x 3 2).toNat = 0 := by
              have r20902 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
              have b20903 := hb (x 3 2)
              have b20904 := hb (x 3 14)
              clear * - r20902 b20903 b20904 d20893
              omega
            have d20905 : (x 2 2).toNat = 0 := by
              have r20906 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e20907 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e20908 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b20909 := hb (x 1 3)
              have b20910 := hb (x 2 2)
              have b20911 := hb (x 3 13)
              have b20912 := hb (x 4 12)
              clear * - r20906 e20907 e20908 b20909 b20910 b20911 b20912 d20856 d20872 f20855
              omega
            have d20913 : (x 4 13).toNat = 1 := by
              have r20914 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b20915 := hb (x 2 2)
              have b20916 := hb (x 4 13)
              have b20917 := hb (x 3 1 && x 3 14)
              clear * - r20914 b20915 b20916 b20917 d20897 d20905
              omega
            have d20918 : (x 4 1).toNat = 1 := by
              have r20919 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
              have b20920 := hb (x 4 1)
              have b20921 := hb (x 4 13)
              clear * - r20919 b20920 b20921 d20913
              omega
            have d20922 : (x 5 14).toNat = 0 := by
              have r20923 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b20924 := hb (x 4 1)
              have b20925 := hb (x 5 14)
              clear * - r20923 b20924 b20925 d20918
              omega
            have d20926 : (x 5 3 && x 5 14).toNat = 0 := by
              have r20927 := hand2 (x 5 3) (x 5 14)
              have b20928 := hb (x 5 14)
              have b20929 := hb (x 5 3 && x 5 14)
              clear * - r20927 b20928 b20929 d20922
              omega
            have d20930 : (x 5 2).toNat = 0 := by
              have r20931 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
              have b20932 := hb (x 5 2)
              have b20933 := hb (x 5 14)
              clear * - r20931 b20932 b20933 d20922
              omega
            have d20934 : (x 5 12).toNat = 0 := by
              have r20935 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e20936 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
              have e20937 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
              have b20938 := hb (x 2 3)
              have b20939 := hb (x 3 2)
              have b20940 := hb (x 4 13)
              have b20941 := hb (x 5 12)
              clear * - r20935 e20936 e20937 b20938 b20939 b20940 b20941 d20913 d20901
              omega
            have d20942 : (x 5 4).toNat = 0 := by
              have r20943 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
              have b20944 := hb (x 5 4)
              have b20945 := hb (x 5 12)
              clear * - r20943 b20944 b20945 d20934
              omega
            have d20946 : (x 2 3).toNat = 0 := by
              have r20947 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e20948 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
              have e20949 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
              have b20950 := hb (x 2 3)
              have b20951 := hb (x 3 2)
              have b20952 := hb (x 4 13)
              have b20953 := hb (x 5 12)
              clear * - r20947 e20948 e20949 b20950 b20951 b20952 b20953 d20934 d20913 d20901
              omega
            have d20954 : (x 2 3 && x 2 14).toNat = 0 := by
              have r20955 := hand1 (x 2 3) (x 2 14)
              have b20956 := hb (x 2 3)
              have b20957 := hb (x 2 3 && x 2 14)
              clear * - r20955 b20956 b20957 d20946
              omega
            have d20958 : (x 5 11).toNat = 1 := by
              have r20959 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b20960 := hb (x 1 4)
              have b20961 := hb (x 5 11)
              have b20962 := hb (x 4 1 && x 4 12)
              have b20963 := hb (x 3 2 && x 3 13)
              have b20964 := hb (x 2 3 && x 2 14)
              clear * - r20959 b20960 b20961 b20962 b20963 b20964 d20864 d20880 d20954 g26
              omega
            have d20965 : (x 5 3).toNat = 1 := by
              have r20966 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
              have b20967 := hb (x 5 3)
              have b20968 := hb (x 5 11)
              clear * - r20966 b20967 b20968 d20958
              omega
            have d20969 : (x 8 12).toNat = 0 := by
              have r20970 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e20971 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
              have e20972 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
              have b20973 := hb (x 5 3)
              have b20974 := hb (x 6 2)
              have b20975 := hb (x 7 13)
              have b20976 := hb (x 8 12)
              clear * - r20970 e20971 e20972 b20973 b20974 b20975 b20976 d20965
              omega
            have d20977 : (x 8 1 && x 8 12).toNat = 0 := by
              have r20978 := hand2 (x 8 1) (x 8 12)
              have b20979 := hb (x 8 12)
              have b20980 := hb (x 8 1 && x 8 12)
              clear * - r20978 b20979 b20980 d20969
              omega
            have d20981 : (x 8 4).toNat = 0 := by
              have r20982 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
              have b20983 := hb (x 8 4)
              have b20984 := hb (x 8 12)
              clear * - r20982 b20983 b20984 d20969
              omega
            have d20985 : (x 7 13).toNat = 0 := by
              have r20986 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e20987 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
              have e20988 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
              have b20989 := hb (x 5 3)
              have b20990 := hb (x 6 2)
              have b20991 := hb (x 7 13)
              have b20992 := hb (x 8 12)
              clear * - r20986 e20987 e20988 b20989 b20990 b20991 b20992 d20969 d20965
              omega
            have d20993 : (x 7 2 && x 7 13).toNat = 0 := by
              have r20994 := hand2 (x 7 2) (x 7 13)
              have b20995 := hb (x 7 13)
              have b20996 := hb (x 7 2 && x 7 13)
              clear * - r20994 b20995 b20996 d20985
              omega
            have d20997 : (x 6 1 && x 6 14).toNat = 1 := by
              have r20998 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b20999 := hb (x 5 2)
              have b21000 := hb (x 7 13)
              have b21001 := hb (x 6 1 && x 6 14)
              clear * - r20998 b20999 b21000 b21001 d20985 d20930
              omega
            have d21002 : (x 6 1).toNat = 1 := by
              have r21003 := hand1 (x 6 1) (x 6 14)
              have b21004 := hb (x 6 1)
              have b21005 := hb (x 6 1 && x 6 14)
              clear * - r21003 b21004 b21005 d20997
              omega
            have d21006 : (x 7 14).toNat = 0 := by
              have r21007 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21008 := hb (x 6 1)
              have b21009 := hb (x 7 14)
              clear * - r21007 b21008 b21009 d21002
              omega
            have d21010 : (x 7 1 && x 7 14).toNat = 0 := by
              have r21011 := hand2 (x 7 1) (x 7 14)
              have b21012 := hb (x 7 14)
              have b21013 := hb (x 7 1 && x 7 14)
              clear * - r21011 b21012 b21013 d21006
              omega
            have d21014 : (x 7 2).toNat = 0 := by
              have r21015 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
              have b21016 := hb (x 7 2)
              have b21017 := hb (x 7 14)
              clear * - r21015 b21016 b21017 d21006
              omega
            have d21018 : (x 6 2).toNat = 0 := by
              have r21019 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21020 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
              have e21021 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
              have b21022 := hb (x 5 3)
              have b21023 := hb (x 6 2)
              have b21024 := hb (x 7 13)
              have b21025 := hb (x 8 12)
              clear * - r21019 e21020 e21021 b21022 b21023 b21024 b21025 d20969 d20985 d20965
              omega
            have d21026 : (x 6 2 && x 6 13).toNat = 0 := by
              have r21027 := hand1 (x 6 2) (x 6 13)
              have b21028 := hb (x 6 2)
              have b21029 := hb (x 6 2 && x 6 13)
              clear * - r21027 b21028 b21029 d21018
              omega
            have d21030 : (x 8 13).toNat = 1 := by
              have r21031 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21032 := hb (x 6 2)
              have b21033 := hb (x 8 13)
              have b21034 := hb (x 7 1 && x 7 14)
              clear * - r21031 b21032 b21033 b21034 d21010 d21018
              omega
            have d21035 : (x 8 1).toNat = 1 := by
              have r21036 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
              have b21037 := hb (x 8 1)
              have b21038 := hb (x 8 13)
              clear * - r21036 b21037 b21038 d21030
              omega
            have d21039 : (x 9 14).toNat = 0 := by
              have r21040 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21041 := hb (x 8 1)
              have b21042 := hb (x 9 14)
              clear * - r21040 b21041 b21042 d21035
              omega
            have d21043 : (x 9 3 && x 9 14).toNat = 0 := by
              have r21044 := hand2 (x 9 3) (x 9 14)
              have b21045 := hb (x 9 14)
              have b21046 := hb (x 9 3 && x 9 14)
              clear * - r21044 b21045 b21046 d21039
              omega
            have d21047 : (x 9 2).toNat = 0 := by
              have r21048 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
              have b21049 := hb (x 9 2)
              have b21050 := hb (x 9 14)
              clear * - r21048 b21049 b21050 d21039
              omega
            have d21051 : (x 9 12).toNat = 0 := by
              have r21052 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21053 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
              have e21054 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
              have b21055 := hb (x 6 3)
              have b21056 := hb (x 7 2)
              have b21057 := hb (x 8 13)
              have b21058 := hb (x 9 12)
              clear * - r21052 e21053 e21054 b21055 b21056 b21057 b21058 d21030 d21014
              omega
            have d21059 : (x 9 4).toNat = 0 := by
              have r21060 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
              have b21061 := hb (x 9 4)
              have b21062 := hb (x 9 12)
              clear * - r21060 b21061 b21062 d21051
              omega
            have d21063 : (x 6 3).toNat = 0 := by
              have r21064 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21065 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
              have e21066 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
              have b21067 := hb (x 6 3)
              have b21068 := hb (x 7 2)
              have b21069 := hb (x 8 13)
              have b21070 := hb (x 9 12)
              clear * - r21064 e21065 e21066 b21067 b21068 b21069 b21070 d21051 d21030 d21014
              omega
            have d21071 : (x 6 3 && x 6 14).toNat = 0 := by
              have r21072 := hand1 (x 6 3) (x 6 14)
              have b21073 := hb (x 6 3)
              have b21074 := hb (x 6 3 && x 6 14)
              clear * - r21072 b21073 b21074 d21063
              omega
            have d21075 : (x 9 11).toNat = 1 := by
              have r21076 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21077 := hb (x 5 4)
              have b21078 := hb (x 9 11)
              have b21079 := hb (x 8 1 && x 8 12)
              have b21080 := hb (x 7 2 && x 7 13)
              have b21081 := hb (x 6 3 && x 6 14)
              clear * - r21076 b21077 b21078 b21079 b21080 b21081 d20977 d20993 d21071 d20942
              omega
            have d21082 : (x 9 3).toNat = 1 := by
              have r21083 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
              have b21084 := hb (x 9 3)
              have b21085 := hb (x 9 11)
              clear * - r21083 b21084 b21085 d21075
              omega
            have d21086 : (x 12 12).toNat = 0 := by
              have r21087 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21088 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
              have e21089 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
              have b21090 := hb (x 9 3)
              have b21091 := hb (x 10 2)
              have b21092 := hb (x 11 13)
              have b21093 := hb (x 12 12)
              clear * - r21087 e21088 e21089 b21090 b21091 b21092 b21093 d21082
              omega
            have d21094 : (x 12 1 && x 12 12).toNat = 0 := by
              have r21095 := hand2 (x 12 1) (x 12 12)
              have b21096 := hb (x 12 12)
              have b21097 := hb (x 12 1 && x 12 12)
              clear * - r21095 b21096 b21097 d21086
              omega
            have d21098 : (x 12 4).toNat = 0 := by
              have r21099 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
              have b21100 := hb (x 12 4)
              have b21101 := hb (x 12 12)
              clear * - r21099 b21100 b21101 d21086
              omega
            have d21102 : (x 11 13).toNat = 0 := by
              have r21103 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21104 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
              have e21105 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
              have b21106 := hb (x 9 3)
              have b21107 := hb (x 10 2)
              have b21108 := hb (x 11 13)
              have b21109 := hb (x 12 12)
              clear * - r21103 e21104 e21105 b21106 b21107 b21108 b21109 d21086 d21082
              omega
            have d21110 : (x 11 2 && x 11 13).toNat = 0 := by
              have r21111 := hand2 (x 11 2) (x 11 13)
              have b21112 := hb (x 11 13)
              have b21113 := hb (x 11 2 && x 11 13)
              clear * - r21111 b21112 b21113 d21102
              omega
            have d21114 : (x 10 1 && x 10 14).toNat = 1 := by
              have r21115 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21116 := hb (x 9 2)
              have b21117 := hb (x 11 13)
              have b21118 := hb (x 10 1 && x 10 14)
              clear * - r21115 b21116 b21117 b21118 d21102 d21047
              omega
            have d21119 : (x 10 14).toNat = 1 := by
              have r21120 := hand2 (x 10 1) (x 10 14)
              have b21121 := hb (x 10 14)
              have b21122 := hb (x 10 1 && x 10 14)
              clear * - r21120 b21121 b21122 d21114
              omega
            have d21123 : (x 9 1).toNat = 0 := by
              have r21124 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21125 := hb (x 9 1)
              have b21126 := hb (x 10 14)
              clear * - r21124 b21125 b21126 d21119
              omega
            have d21127 : (x 9 13).toNat = 0 := by
              have r21128 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
              have b21129 := hb (x 9 1)
              have b21130 := hb (x 9 13)
              clear * - r21128 b21129 b21130 d21123
              omega
            have d21131 : (x 8 1 && x 8 14).toNat = 1 := by
              have r21132 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21133 := hb (x 7 2)
              have b21134 := hb (x 9 13)
              have b21135 := hb (x 8 1 && x 8 14)
              clear * - r21132 b21133 b21134 b21135 d21127 d21014
              omega
            have d21136 : (x 8 14).toNat = 1 := by
              have r21137 := hand2 (x 8 1) (x 8 14)
              have b21138 := hb (x 8 14)
              have b21139 := hb (x 8 1 && x 8 14)
              clear * - r21137 b21138 b21139 d21131
              omega
            have d21140 : (x 7 1).toNat = 0 := by
              have r21141 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21142 := hb (x 7 1)
              have b21143 := hb (x 8 14)
              clear * - r21141 b21142 b21143 d21136
              omega
            have d21144 : (x 7 1 && x 7 12).toNat = 0 := by
              have r21145 := hand1 (x 7 1) (x 7 12)
              have b21146 := hb (x 7 1)
              have b21147 := hb (x 7 1 && x 7 12)
              clear * - r21145 b21146 b21147 d21140
              omega
            have d21148 : (x 8 11).toNat = 1 := by
              have r21149 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21150 := hb (x 4 4)
              have b21151 := hb (x 8 11)
              have b21152 := hb (x 7 1 && x 7 12)
              have b21153 := hb (x 6 2 && x 6 13)
              have b21154 := hb (x 5 3 && x 5 14)
              clear * - r21149 b21150 b21151 b21152 b21153 b21154 d21144 d21026 d20926 d20868
              omega
            have d21155 : (x 8 3).toNat = 1 := by
              have r21156 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
              have b21157 := hb (x 8 3)
              have b21158 := hb (x 8 11)
              clear * - r21156 b21157 b21158 d21148
              omega
            have d21159 : (x 11 12).toNat = 0 := by
              have r21160 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21161 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
              have e21162 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
              have b21163 := hb (x 8 3)
              have b21164 := hb (x 9 2)
              have b21165 := hb (x 10 13)
              have b21166 := hb (x 11 12)
              clear * - r21160 e21161 e21162 b21163 b21164 b21165 b21166 d21047 d21155
              omega
            have d21167 : (x 11 1 && x 11 12).toNat = 0 := by
              have r21168 := hand2 (x 11 1) (x 11 12)
              have b21169 := hb (x 11 12)
              have b21170 := hb (x 11 1 && x 11 12)
              clear * - r21168 b21169 b21170 d21159
              omega
            have d21171 : (x 10 13).toNat = 0 := by
              have r21172 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21173 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
              have e21174 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
              have b21175 := hb (x 8 3)
              have b21176 := hb (x 9 2)
              have b21177 := hb (x 10 13)
              have b21178 := hb (x 11 12)
              clear * - r21172 e21173 e21174 b21175 b21176 b21177 b21178 d21159 d21047 d21155
              omega
            have d21179 : (x 10 2 && x 10 13).toNat = 0 := by
              have r21180 := hand2 (x 10 2) (x 10 13)
              have b21181 := hb (x 10 13)
              have b21182 := hb (x 10 2 && x 10 13)
              clear * - r21180 b21181 b21182 d21171
              omega
            have d21183 : (x 12 11).toNat = 1 := by
              have r21184 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21185 := hb (x 8 4)
              have b21186 := hb (x 12 11)
              have b21187 := hb (x 11 1 && x 11 12)
              have b21188 := hb (x 10 2 && x 10 13)
              have b21189 := hb (x 9 3 && x 9 14)
              clear * - r21184 b21185 b21186 b21187 b21188 b21189 d21167 d21179 d21043 d20981
              omega
            have d21190 : (x 12 3).toNat = 1 := by
              have r21191 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
              have b21192 := hb (x 12 3)
              have b21193 := hb (x 12 11)
              clear * - r21191 b21192 b21193 d21183
              omega
            have d21194 : (x 15 12).toNat = 0 := by
              have r21195 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21196 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
              have e21197 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
              have b21198 := hb (x 12 3)
              have b21199 := hb (x 13 2)
              have b21200 := hb (x 14 13)
              have b21201 := hb (x 15 12)
              clear * - r21195 e21196 e21197 b21198 b21199 b21200 b21201 d21190
              omega
            have d21202 : (x 15 1 && x 15 12).toNat = 0 := by
              have r21203 := hand2 (x 15 1) (x 15 12)
              have b21204 := hb (x 15 12)
              have b21205 := hb (x 15 1 && x 15 12)
              clear * - r21203 b21204 b21205 d21194
              omega
            have d21206 : (x 14 13).toNat = 0 := by
              have r21207 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21208 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
              have e21209 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
              have b21210 := hb (x 12 3)
              have b21211 := hb (x 13 2)
              have b21212 := hb (x 14 13)
              have b21213 := hb (x 15 12)
              clear * - r21207 e21208 e21209 b21210 b21211 b21212 b21213 d21194 d21190
              omega
            have d21214 : (x 14 2 && x 14 13).toNat = 0 := by
              have r21215 := hand2 (x 14 2) (x 14 13)
              have b21216 := hb (x 14 13)
              have b21217 := hb (x 14 2 && x 14 13)
              clear * - r21215 b21216 b21217 d21206
              omega
            have d21218 : (x 13 2).toNat = 0 := by
              have r21219 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21220 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
              have e21221 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
              have b21222 := hb (x 12 3)
              have b21223 := hb (x 13 2)
              have b21224 := hb (x 14 13)
              have b21225 := hb (x 15 12)
              clear * - r21219 e21220 e21221 b21222 b21223 b21224 b21225 d21194 d21206 d21190
              omega
            have d21226 : (x 10 1).toNat = 1 := by
              have r21227 := hand1 (x 10 1) (x 10 14)
              have b21228 := hb (x 10 1)
              have b21229 := hb (x 10 1 && x 10 14)
              clear * - r21227 b21228 b21229 d21114
              omega
            have d21230 : (x 11 14).toNat = 0 := by
              have r21231 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21232 := hb (x 10 1)
              have b21233 := hb (x 11 14)
              clear * - r21231 b21232 b21233 d21226
              omega
            have d21234 : (x 11 1 && x 11 14).toNat = 0 := by
              have r21235 := hand2 (x 11 1) (x 11 14)
              have b21236 := hb (x 11 14)
              have b21237 := hb (x 11 1 && x 11 14)
              clear * - r21235 b21236 b21237 d21230
              omega
            have d21238 : (x 11 2).toNat = 0 := by
              have r21239 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
              have b21240 := hb (x 11 2)
              have b21241 := hb (x 11 14)
              clear * - r21239 b21240 b21241 d21230
              omega
            have d21242 : (x 10 2).toNat = 0 := by
              have r21243 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21244 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
              have e21245 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
              have b21246 := hb (x 9 3)
              have b21247 := hb (x 10 2)
              have b21248 := hb (x 11 13)
              have b21249 := hb (x 12 12)
              clear * - r21243 e21244 e21245 b21246 b21247 b21248 b21249 d21086 d21102 d21082
              omega
            have d21250 : (x 12 13).toNat = 1 := by
              have r21251 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21252 := hb (x 10 2)
              have b21253 := hb (x 12 13)
              have b21254 := hb (x 11 1 && x 11 14)
              clear * - r21251 b21252 b21253 b21254 d21234 d21242
              omega
            have d21255 : (x 12 1).toNat = 1 := by
              have r21256 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
              have b21257 := hb (x 12 1)
              have b21258 := hb (x 12 13)
              clear * - r21256 b21257 b21258 d21250
              omega
            have d21259 : (x 13 14).toNat = 0 := by
              have r21260 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21261 := hb (x 12 1)
              have b21262 := hb (x 13 14)
              clear * - r21260 b21261 b21262 d21255
              omega
            have d21263 : (x 13 1 && x 13 14).toNat = 0 := by
              have r21264 := hand2 (x 13 1) (x 13 14)
              have b21265 := hb (x 13 14)
              have b21266 := hb (x 13 1 && x 13 14)
              clear * - r21264 b21265 b21266 d21259
              omega
            have d21267 : (x 12 2).toNat = 1 := by
              have r21268 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21269 := hb (x 12 2)
              have b21270 := hb (x 14 13)
              have b21271 := hb (x 13 1 && x 13 14)
              clear * - r21268 b21269 b21270 b21271 d21206 d21263
              omega
            have d21272 : (x 14 12).toNat = 0 := by
              have r21273 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21274 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
              have e21275 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
              have b21276 := hb (x 11 3)
              have b21277 := hb (x 12 2)
              have b21278 := hb (x 13 13)
              have b21279 := hb (x 14 12)
              clear * - r21273 e21274 e21275 b21276 b21277 b21278 b21279 d21267
              omega
            have d21280 : (x 14 4).toNat = 0 := by
              have r21281 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
              have b21282 := hb (x 14 4)
              have b21283 := hb (x 14 12)
              clear * - r21281 b21282 b21283 d21272
              omega
            have d21284 : (x 14 4 && x 14 14).toNat = 0 := by
              have r21285 := hand1 (x 14 4) (x 14 14)
              have b21286 := hb (x 14 4)
              have b21287 := hb (x 14 4 && x 14 14)
              clear * - r21285 b21286 b21287 d21280
              omega
            have d21288 : (x 13 13).toNat = 0 := by
              have r21289 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21290 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
              have e21291 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
              have b21292 := hb (x 11 3)
              have b21293 := hb (x 12 2)
              have b21294 := hb (x 13 13)
              have b21295 := hb (x 14 12)
              clear * - r21289 e21290 e21291 b21292 b21293 b21294 b21295 d21272 d21267
              omega
            have d21296 : (x 13 5).toNat = 0 := by
              have r21297 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
              have b21298 := hb (x 13 5)
              have b21299 := hb (x 13 13)
              clear * - r21297 b21298 b21299 d21288
              omega
            have d21300 : (x 13 3 && x 13 14).toNat = 0 := by
              have r21301 := hand2 (x 13 3) (x 13 14)
              have b21302 := hb (x 13 14)
              have b21303 := hb (x 13 3 && x 13 14)
              clear * - r21301 b21302 b21303 d21259
              omega
            have d21304 : (x 16 11).toNat = 1 := by
              have r21305 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21306 := hb (x 12 4)
              have b21307 := hb (x 16 11)
              have b21308 := hb (x 15 1 && x 15 12)
              have b21309 := hb (x 14 2 && x 14 13)
              have b21310 := hb (x 13 3 && x 13 14)
              clear * - r21305 b21306 b21307 b21308 b21309 b21310 d21202 d21214 d21300 d21098
              omega
            have d21311 : (x 16 3).toNat = 1 := by
              have r21312 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
              have b21313 := hb (x 16 3)
              have b21314 := hb (x 16 11)
              clear * - r21312 b21313 b21314 d21304
              omega
            have d21315 : (x 19 12).toNat = 0 := by
              have r21316 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21317 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
              have e21318 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
              have b21319 := hb (x 16 3)
              have b21320 := hb (x 17 2)
              have b21321 := hb (x 18 13)
              have b21322 := hb (x 19 12)
              clear * - r21316 e21317 e21318 b21319 b21320 b21321 b21322 d21311
              omega
            have d21323 : (x 18 13).toNat = 0 := by
              have r21324 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21325 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
              have e21326 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
              have b21327 := hb (x 16 3)
              have b21328 := hb (x 17 2)
              have b21329 := hb (x 18 13)
              have b21330 := hb (x 19 12)
              clear * - r21324 e21325 e21326 b21327 b21328 b21329 b21330 d21315 d21311
              omega
            have d21331 : (x 17 2).toNat = 0 := by
              have r21332 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21333 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
              have e21334 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
              have b21335 := hb (x 16 3)
              have b21336 := hb (x 17 2)
              have b21337 := hb (x 18 13)
              have b21338 := hb (x 19 12)
              clear * - r21332 e21333 e21334 b21335 b21336 b21337 b21338 d21315 d21323 d21311
              omega
            have d21339 : (x 13 12).toNat = 0 := by
              have r21340 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21341 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
              have e21342 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
              have b21343 := hb (x 10 3)
              have b21344 := hb (x 11 2)
              have b21345 := hb (x 12 13)
              have b21346 := hb (x 13 12)
              clear * - r21340 e21341 e21342 b21343 b21344 b21345 b21346 d21250 d21238
              omega
            have d21347 : (x 13 4).toNat = 0 := by
              have r21348 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
              have b21349 := hb (x 13 4)
              have b21350 := hb (x 13 12)
              clear * - r21348 b21349 b21350 d21339
              omega
            have d21351 : (x 10 3).toNat = 0 := by
              have r21352 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21353 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
              have e21354 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
              have b21355 := hb (x 10 3)
              have b21356 := hb (x 11 2)
              have b21357 := hb (x 12 13)
              have b21358 := hb (x 13 12)
              clear * - r21352 e21353 e21354 b21355 b21356 b21357 b21358 d21339 d21250 d21238
              omega
            have d21359 : (x 10 3 && x 10 14).toNat = 0 := by
              have r21360 := hand1 (x 10 3) (x 10 14)
              have b21361 := hb (x 10 3)
              have b21362 := hb (x 10 3 && x 10 14)
              clear * - r21360 b21361 b21362 d21351
              omega
            have d21363 : (x 13 11).toNat = 1 := by
              have r21364 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21365 := hb (x 9 4)
              have b21366 := hb (x 13 11)
              have b21367 := hb (x 12 1 && x 12 12)
              have b21368 := hb (x 11 2 && x 11 13)
              have b21369 := hb (x 10 3 && x 10 14)
              clear * - r21364 b21365 b21366 b21367 b21368 b21369 d21094 d21110 d21359 d21059
              omega
            have d21370 : (x 13 3).toNat = 1 := by
              have r21371 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
              have b21372 := hb (x 13 3)
              have b21373 := hb (x 13 11)
              clear * - r21371 b21372 b21373 d21363
              omega
            have d21374 : (x 16 12).toNat = 0 := by
              have r21375 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21376 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
              have e21377 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
              have b21378 := hb (x 13 3)
              have b21379 := hb (x 14 2)
              have b21380 := hb (x 15 13)
              have b21381 := hb (x 16 12)
              clear * - r21375 e21376 e21377 b21378 b21379 b21380 b21381 d21370
              omega
            have d21382 : (x 16 1 && x 16 12).toNat = 0 := by
              have r21383 := hand2 (x 16 1) (x 16 12)
              have b21384 := hb (x 16 12)
              have b21385 := hb (x 16 1 && x 16 12)
              clear * - r21383 b21384 b21385 d21374
              omega
            have d21386 : (x 16 2 && x 16 12).toNat = 0 := by
              have r21387 := hand2 (x 16 2) (x 16 12)
              have b21388 := hb (x 16 12)
              have b21389 := hb (x 16 2 && x 16 12)
              clear * - r21387 b21388 b21389 d21374
              omega
            have d21390 : (x 15 13).toNat = 0 := by
              have r21391 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21392 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
              have e21393 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
              have b21394 := hb (x 13 3)
              have b21395 := hb (x 14 2)
              have b21396 := hb (x 15 13)
              have b21397 := hb (x 16 12)
              clear * - r21391 e21392 e21393 b21394 b21395 b21396 b21397 d21374 d21370
              omega
            have d21398 : (x 15 2 && x 15 13).toNat = 0 := by
              have r21399 := hand2 (x 15 2) (x 15 13)
              have b21400 := hb (x 15 13)
              have b21401 := hb (x 15 2 && x 15 13)
              clear * - r21399 b21400 b21401 d21390
              omega
            have d21402 : (x 15 3 && x 15 13).toNat = 0 := by
              have r21403 := hand2 (x 15 3) (x 15 13)
              have b21404 := hb (x 15 13)
              have b21405 := hb (x 15 3 && x 15 13)
              clear * - r21403 b21404 b21405 d21390
              omega
            have d21406 : (x 14 1 && x 14 14).toNat = 1 := by
              have r21407 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21408 := hb (x 13 2)
              have b21409 := hb (x 15 13)
              have b21410 := hb (x 14 1 && x 14 14)
              clear * - r21407 b21408 b21409 b21410 d21390 d21218
              omega
            have d21411 : (x 14 1).toNat = 1 := by
              have r21412 := hand1 (x 14 1) (x 14 14)
              have b21413 := hb (x 14 1)
              have b21414 := hb (x 14 1 && x 14 14)
              clear * - r21412 b21413 b21414 d21406
              omega
            have d21415 : (x 15 14).toNat = 0 := by
              have r21416 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21417 := hb (x 14 1)
              have b21418 := hb (x 15 14)
              clear * - r21416 b21417 b21418 d21411
              omega
            have d21419 : (x 15 1 && x 15 14).toNat = 0 := by
              have r21420 := hand2 (x 15 1) (x 15 14)
              have b21421 := hb (x 15 14)
              have b21422 := hb (x 15 1 && x 15 14)
              clear * - r21420 b21421 b21422 d21415
              omega
            have d21423 : (x 15 2).toNat = 0 := by
              have r21424 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
              have b21425 := hb (x 15 2)
              have b21426 := hb (x 15 14)
              clear * - r21424 b21425 b21426 d21415
              omega
            have d21427 : (x 14 2).toNat = 0 := by
              have r21428 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21429 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
              have e21430 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
              have b21431 := hb (x 13 3)
              have b21432 := hb (x 14 2)
              have b21433 := hb (x 15 13)
              have b21434 := hb (x 16 12)
              clear * - r21428 e21429 e21430 b21431 b21432 b21433 b21434 d21374 d21390 d21370
              omega
            have d21435 : (x 16 13).toNat = 1 := by
              have r21436 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21437 := hb (x 14 2)
              have b21438 := hb (x 16 13)
              have b21439 := hb (x 15 1 && x 15 14)
              clear * - r21436 b21437 b21438 b21439 d21419 d21427
              omega
            have d21440 : (x 17 12).toNat = 0 := by
              have r21441 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21442 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
              have e21443 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
              have b21444 := hb (x 14 3)
              have b21445 := hb (x 15 2)
              have b21446 := hb (x 16 13)
              have b21447 := hb (x 17 12)
              clear * - r21441 e21442 e21443 b21444 b21445 b21446 b21447 d21435 d21423
              omega
            have d21448 : (x 14 3).toNat = 0 := by
              have r21449 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21450 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
              have e21451 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
              have b21452 := hb (x 14 3)
              have b21453 := hb (x 15 2)
              have b21454 := hb (x 16 13)
              have b21455 := hb (x 17 12)
              clear * - r21449 e21450 e21451 b21452 b21453 b21454 b21455 d21440 d21435 d21423
              omega
            have d21456 : (x 14 3 && x 14 14).toNat = 0 := by
              have r21457 := hand1 (x 14 3) (x 14 14)
              have b21458 := hb (x 14 3)
              have b21459 := hb (x 14 3 && x 14 14)
              clear * - r21457 b21458 b21459 d21448
              omega
            have d21460 : (x 17 11).toNat = 1 := by
              have r21461 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21462 := hb (x 13 4)
              have b21463 := hb (x 17 11)
              have b21464 := hb (x 16 1 && x 16 12)
              have b21465 := hb (x 15 2 && x 15 13)
              have b21466 := hb (x 14 3 && x 14 14)
              clear * - r21461 b21462 b21463 b21464 b21465 b21466 d21382 d21398 d21456 d21347
              omega
            have d21467 : (x 17 3).toNat = 1 := by
              have r21468 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
              have b21469 := hb (x 17 3)
              have b21470 := hb (x 17 11)
              clear * - r21468 b21469 b21470 d21460
              omega
            have d21471 : (x 20 12).toNat = 0 := by
              have r21472 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21473 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
              have e21474 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
              have b21475 := hb (x 17 3)
              have b21476 := hb (x 18 2)
              have b21477 := hb (x 19 13)
              have b21478 := hb (x 20 12)
              clear * - r21472 e21473 e21474 b21475 b21476 b21477 b21478 d21467
              omega
            have d21479 : (x 19 13).toNat = 0 := by
              have r21480 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21481 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
              have e21482 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
              have b21483 := hb (x 17 3)
              have b21484 := hb (x 18 2)
              have b21485 := hb (x 19 13)
              have b21486 := hb (x 20 12)
              clear * - r21480 e21481 e21482 b21483 b21484 b21485 b21486 d21471 d21467
              omega
            have d21487 : (x 18 1 && x 18 14).toNat = 1 := by
              have r21488 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21489 := hb (x 17 2)
              have b21490 := hb (x 19 13)
              have b21491 := hb (x 18 1 && x 18 14)
              clear * - r21488 b21489 b21490 b21491 d21479 d21331
              omega
            have d21492 : (x 18 14).toNat = 1 := by
              have r21493 := hand2 (x 18 1) (x 18 14)
              have b21494 := hb (x 18 14)
              have b21495 := hb (x 18 1 && x 18 14)
              clear * - r21493 b21494 b21495 d21487
              omega
            have d21496 : (x 17 1).toNat = 0 := by
              have r21497 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21498 := hb (x 17 1)
              have b21499 := hb (x 18 14)
              clear * - r21497 b21498 b21499 d21492
              omega
            have d21500 : (x 17 1 && x 17 11).toNat = 0 := by
              have r21501 := hand1 (x 17 1) (x 17 11)
              have b21502 := hb (x 17 1)
              have b21503 := hb (x 17 1 && x 17 11)
              clear * - r21501 b21502 b21503 d21496
              omega
            have d21504 : (x 18 2).toNat = 0 := by
              have r21505 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21506 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
              have e21507 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
              have b21508 := hb (x 17 3)
              have b21509 := hb (x 18 2)
              have b21510 := hb (x 19 13)
              have b21511 := hb (x 20 12)
              clear * - r21505 e21506 e21507 b21508 b21509 b21510 b21511 d21471 d21479 d21467
              omega
            have d21512 : (x 18 10).toNat = 0 := by
              have r21513 : (x 18 10).toNat ≤ (x 18 2).toNat := himp _ _ (hp10 18)
              have b21514 := hb (x 18 2)
              have b21515 := hb (x 18 10)
              clear * - r21513 b21514 b21515 d21504
              omega
            have r21516 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := by have q := hcov10 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b21517 := hb (x 13 5)
            have b21518 := hb (x 18 10)
            have b21519 := hb (x 17 1 && x 17 11)
            have b21520 := hb (x 16 2 && x 16 12)
            have b21521 := hb (x 15 3 && x 15 13)
            have b21522 := hb (x 14 4 && x 14 14)
            linarith only [r21516, b21517, b21518, b21519, b21520, b21521, b21522, d21512, d21500, d21386, d21402, d21284, d21296]
        · have f21523 : (x 1 1).toNat = 1 := by rw [h18410]; rfl
          have d21524 : (x 2 14).toNat = 0 := by
            have r21525 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b21526 := hb (x 1 1)
            have b21527 := hb (x 2 14)
            clear * - r21525 b21526 b21527 f21523
            omega
          have d21528 : (x 2 1 && x 2 14).toNat = 0 := by
            have r21529 := hand2 (x 2 1) (x 2 14)
            have b21530 := hb (x 2 14)
            have b21531 := hb (x 2 1 && x 2 14)
            clear * - r21529 b21530 b21531 d21524
            omega
          have d21532 : (x 2 6).toNat = 0 := by
            have r21533 : (x 2 6).toNat ≤ (x 2 14).toNat := himp _ _ (hp6 2)
            have b21534 := hb (x 2 6)
            have b21535 := hb (x 2 14)
            clear * - r21533 b21534 b21535 d21524
            omega
          have d21536 : (x 2 2 && x 2 6).toNat = 0 := by
            have r21537 := hand2 (x 2 2) (x 2 6)
            have b21538 := hb (x 2 6)
            have b21539 := hb (x 2 2 && x 2 6)
            clear * - r21537 b21538 b21539 d21532
            omega
          have d21540 : (x 2 2).toNat = 0 := by
            have r21541 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
            have b21542 := hb (x 2 2)
            have b21543 := hb (x 2 14)
            clear * - r21541 b21542 b21543 d21524
            omega
          have d21544 : (x 3 13).toNat = 1 := by
            have r21545 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b21546 := hb (x 1 2)
            have b21547 := hb (x 3 13)
            have b21548 := hb (x 2 1 && x 2 14)
            clear * - r21545 b21546 b21547 b21548 d21528 g25
            omega
          have d21549 : (x 3 1).toNat = 1 := by
            have r21550 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
            have b21551 := hb (x 3 1)
            have b21552 := hb (x 3 13)
            clear * - r21550 b21551 b21552 d21544
            omega
          have d21553 : (x 4 12).toNat = 0 := by
            have r21554 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e21555 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e21556 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b21557 := hb (x 1 3)
            have b21558 := hb (x 2 2)
            have b21559 := hb (x 3 13)
            have b21560 := hb (x 4 12)
            clear * - r21554 e21555 e21556 b21557 b21558 b21559 b21560 d21544 d21540
            omega
          have d21561 : (x 4 3 && x 4 12).toNat = 0 := by
            have r21562 := hand2 (x 4 3) (x 4 12)
            have b21563 := hb (x 4 12)
            have b21564 := hb (x 4 3 && x 4 12)
            clear * - r21562 b21563 b21564 d21553
            omega
          have d21565 : (x 4 4).toNat = 0 := by
            have r21566 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
            have b21567 := hb (x 4 4)
            have b21568 := hb (x 4 12)
            clear * - r21566 b21567 b21568 d21553
            omega
          have d21569 : (x 1 3).toNat = 0 := by
            have r21570 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e21571 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e21572 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b21573 := hb (x 1 3)
            have b21574 := hb (x 2 2)
            have b21575 := hb (x 3 13)
            have b21576 := hb (x 4 12)
            clear * - r21570 e21571 e21572 b21573 b21574 b21575 b21576 d21553 d21544 d21540
            omega
          have d21577 : (x 1 3 && x 1 7).toNat = 0 := by
            have r21578 := hand1 (x 1 3) (x 1 7)
            have b21579 := hb (x 1 3)
            have b21580 := hb (x 1 3 && x 1 7)
            clear * - r21578 b21579 b21580 d21569
            omega
          have r21581 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r21582 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r21583 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21584 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e21585 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e21586 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e21587 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e21588 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e21589 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have r21590 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21591 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
          have e21592 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
          have r21593 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21594 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
          have e21595 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
          have r21596 : 1 ≤ (x 2 6).toNat + (x 1 1 && x 1 7).toNat + (x 0 2 && x 0 8).toNat + (x (-1) 3 && x (-1) 9).toNat + (x (-2) 4 && x (-2) 10).toNat + (x (-3) 5 && x (-3) 11).toNat + (x (-4) 6 && x (-4) 12).toNat + (x (-5) 7 && x (-5) 13).toNat + (x (-6) 8 && x (-6) 14).toNat + (x (-7) 9).toNat := by have q := hcov6 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r21597 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r21598 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r21599 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r21600 : (x (-11) 5).toNat ≤ (x (-11) 13).toNat := himp _ _ (hp5 (-11))
          have r21601 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
          have r21602 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
          have r21603 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
          have r21604 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
          have r21605 := hand1 (x (-4) 8) (x (-4) 12)
          have r21606 := hand1 (x (-5) 9) (x (-5) 13)
          have r21607 := hand2 (x 1 1) (x 1 7)
          have r21608 := hand1 (x (-4) 6) (x (-4) 12)
          have r21609 := hand1 (x (-5) 7) (x (-5) 13)
          have r21610 := hand1 (x (-6) 8) (x (-6) 14)
          have r21611 := hand2 (x 6 1) (x 6 10)
          have r21612 := hand2 (x 5 2) (x 5 11)
          have r21613 := hand2 (x (-7) 1) (x (-7) 11)
          have r21614 := hand2 (x (-8) 2) (x (-8) 12)
          have r21615 := hand2 (x (-9) 3) (x (-9) 13)
          have r21616 := hand2 (x (-10) 4) (x (-10) 14)
          have r21617 := hand1 (x (-4) 4) (x (-4) 14)
          linarith only [r21581, r21582, r21583, e21584, e21585, e21586, e21587, e21588, e21589, r21590, e21591, e21592, r21593, e21594, e21595, r21596, r21597, r21598, r21599, r21600, r21601, r21602, r21603, r21604, r21605, r21606, r21607, r21608, r21609, r21610, r21611, r21612, r21613, r21614, r21615, r21616, r21617, g2, g5, g9, g11, g17, g19, g22, f21523, d21569, g28, d21540, d21532, d21549, d21565, d21536, d21577, d18396, g52, g53, g54, d18392, g69, g70, g71, d21561, g101, g102, g104, g105, g106]
      · have f21692 : (x 0 9).toNat = 1 := by rw [h18400]; rfl
        have d21693 : (x 1 8).toNat = 0 := by
          have r21694 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21695 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e21696 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e21697 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e21698 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e21699 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e21700 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b21701 := hb (x (-6) 7)
          have b21702 := hb (x (-5) 6)
          have b21703 := hb (x (-4) 5)
          have b21704 := hb (x (-3) 4)
          have b21705 := hb (x (-2) 11)
          have b21706 := hb (x (-1) 10)
          have b21707 := hb (x 0 9)
          have b21708 := hb (x 1 8)
          clear * - r21694 e21695 e21696 e21697 e21698 e21699 e21700 b21701 b21702 b21703 b21704 b21705 b21706 b21707 b21708 f21692 g14 g8
          omega
        have d21709 : (x (-3) 4).toNat = 0 := by
          have r21710 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21711 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e21712 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e21713 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e21714 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e21715 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e21716 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b21717 := hb (x (-6) 7)
          have b21718 := hb (x (-5) 6)
          have b21719 := hb (x (-4) 5)
          have b21720 := hb (x (-3) 4)
          have b21721 := hb (x (-2) 11)
          have b21722 := hb (x (-1) 10)
          have b21723 := hb (x 0 9)
          have b21724 := hb (x 1 8)
          clear * - r21710 e21711 e21712 e21713 e21714 e21715 e21716 b21717 b21718 b21719 b21720 b21721 b21722 b21723 b21724 d21693 f21692 g14 g8
          omega
        have d21725 : (x (-3) 4 && x (-3) 13).toNat = 0 := by
          have r21726 := hand1 (x (-3) 4) (x (-3) 13)
          have b21727 := hb (x (-3) 4)
          have b21728 := hb (x (-3) 4 && x (-3) 13)
          clear * - r21726 b21727 b21728 d21709
          omega
        have d21729 : (x (-3) 4 && x (-3) 9).toNat = 0 := by
          have r21730 := hand1 (x (-3) 4) (x (-3) 9)
          have b21731 := hb (x (-3) 4)
          have b21732 := hb (x (-3) 4 && x (-3) 9)
          clear * - r21730 b21731 b21732 d21709
          omega
        have d21733 : (x (-4) 5).toNat = 0 := by
          have r21734 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21735 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e21736 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e21737 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e21738 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e21739 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e21740 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b21741 := hb (x (-6) 7)
          have b21742 := hb (x (-5) 6)
          have b21743 := hb (x (-4) 5)
          have b21744 := hb (x (-3) 4)
          have b21745 := hb (x (-2) 11)
          have b21746 := hb (x (-1) 10)
          have b21747 := hb (x 0 9)
          have b21748 := hb (x 1 8)
          clear * - r21734 e21735 e21736 e21737 e21738 e21739 e21740 b21741 b21742 b21743 b21744 b21745 b21746 b21747 b21748 d21693 f21692 g14 g8 d21709
          omega
        have d21749 : (x (-4) 5 && x (-4) 14).toNat = 0 := by
          have r21750 := hand1 (x (-4) 5) (x (-4) 14)
          have b21751 := hb (x (-4) 5)
          have b21752 := hb (x (-4) 5 && x (-4) 14)
          clear * - r21750 b21751 b21752 d21733
          omega
        have d21753 : (x (-4) 5 && x (-4) 12).toNat = 0 := by
          have r21754 := hand1 (x (-4) 5) (x (-4) 12)
          have b21755 := hb (x (-4) 5)
          have b21756 := hb (x (-4) 5 && x (-4) 12)
          clear * - r21754 b21755 b21756 d21733
          omega
        have d21757 : (x (-4) 5 && x (-4) 10).toNat = 0 := by
          have r21758 := hand1 (x (-4) 5) (x (-4) 10)
          have b21759 := hb (x (-4) 5)
          have b21760 := hb (x (-4) 5 && x (-4) 10)
          clear * - r21758 b21759 b21760 d21733
          omega
        have d21761 : (x (-5) 6).toNat = 0 := by
          have r21762 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21763 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e21764 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e21765 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e21766 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e21767 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e21768 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b21769 := hb (x (-6) 7)
          have b21770 := hb (x (-5) 6)
          have b21771 := hb (x (-4) 5)
          have b21772 := hb (x (-3) 4)
          have b21773 := hb (x (-2) 11)
          have b21774 := hb (x (-1) 10)
          have b21775 := hb (x 0 9)
          have b21776 := hb (x 1 8)
          clear * - r21762 e21763 e21764 e21765 e21766 e21767 e21768 b21769 b21770 b21771 b21772 b21773 b21774 b21775 b21776 d21693 f21692 g14 g8 d21709 d21733
          omega
        have d21777 : (x (-5) 6 && x (-5) 13).toNat = 0 := by
          have r21778 := hand1 (x (-5) 6) (x (-5) 13)
          have b21779 := hb (x (-5) 6)
          have b21780 := hb (x (-5) 6 && x (-5) 13)
          clear * - r21778 b21779 b21780 d21761
          omega
        have d21781 : (x (-5) 6 && x (-5) 11).toNat = 0 := by
          have r21782 := hand1 (x (-5) 6) (x (-5) 11)
          have b21783 := hb (x (-5) 6)
          have b21784 := hb (x (-5) 6 && x (-5) 11)
          clear * - r21782 b21783 b21784 d21761
          omega
        have d21785 : (x 1 9).toNat = 1 := by
          have r21786 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21787 := hb (x (-5) 6)
          have b21788 := hb (x 1 9)
          have b21789 := hb (x 0 1 && x 0 10)
          have b21790 := hb (x (-1) 2 && x (-1) 11)
          have b21791 := hb (x (-2) 3 && x (-2) 12)
          have b21792 := hb (x (-3) 4 && x (-3) 13)
          have b21793 := hb (x (-4) 5 && x (-4) 14)
          clear * - r21786 b21787 b21788 b21789 b21790 b21791 b21792 b21793 g95 g96 g97 d21725 d21749 d21761
          omega
        have d21794 : (x 1 1).toNat = 1 := by
          have r21795 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
          have b21796 := hb (x 1 1)
          have b21797 := hb (x 1 9)
          clear * - r21795 b21796 b21797 d21785
          omega
        have d21798 : (x 2 14).toNat = 0 := by
          have r21799 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21800 := hb (x 1 1)
          have b21801 := hb (x 2 14)
          clear * - r21799 b21800 b21801 d21794
          omega
        have d21802 : (x 2 1 && x 2 14).toNat = 0 := by
          have r21803 := hand2 (x 2 1) (x 2 14)
          have b21804 := hb (x 2 14)
          have b21805 := hb (x 2 1 && x 2 14)
          clear * - r21803 b21804 b21805 d21798
          omega
        have d21806 : (x 3 13).toNat = 1 := by
          have r21807 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21808 := hb (x 1 2)
          have b21809 := hb (x 3 13)
          have b21810 := hb (x 2 1 && x 2 14)
          clear * - r21807 b21808 b21809 b21810 d21802 g25
          omega
        have d21811 : (x 4 12).toNat = 0 := by
          have r21812 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21813 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e21814 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b21815 := hb (x 1 3)
          have b21816 := hb (x 2 2)
          have b21817 := hb (x 3 13)
          have b21818 := hb (x 4 12)
          clear * - r21812 e21813 e21814 b21815 b21816 b21817 b21818 d21806
          omega
        have d21819 : (x 4 3 && x 4 12).toNat = 0 := by
          have r21820 := hand2 (x 4 3) (x 4 12)
          have b21821 := hb (x 4 12)
          have b21822 := hb (x 4 3 && x 4 12)
          clear * - r21820 b21821 b21822 d21811
          omega
        have d21823 : (x 4 4).toNat = 0 := by
          have r21824 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
          have b21825 := hb (x 4 4)
          have b21826 := hb (x 4 12)
          clear * - r21824 b21825 b21826 d21811
          omega
        have d21827 : (x 2 6).toNat = 0 := by
          have r21828 : (x 2 6).toNat ≤ (x 2 14).toNat := himp _ _ (hp6 2)
          have b21829 := hb (x 2 6)
          have b21830 := hb (x 2 14)
          clear * - r21828 b21829 b21830 d21798
          omega
        have d21831 : (x 2 8).toNat = 0 := by
          have r21832 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21833 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
          have e21834 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
          have e21835 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
          have e21836 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
          have e21837 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
          have e21838 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
          have b21839 := hb (x (-5) 7)
          have b21840 := hb (x (-4) 6)
          have b21841 := hb (x (-3) 5)
          have b21842 := hb (x (-2) 4)
          have b21843 := hb (x (-1) 11)
          have b21844 := hb (x 0 10)
          have b21845 := hb (x 1 9)
          have b21846 := hb (x 2 8)
          clear * - r21832 e21833 e21834 e21835 e21836 e21837 e21838 b21839 b21840 b21841 b21842 b21843 b21844 b21845 b21846 d21785 g22 g15
          omega
        have d21847 : (x (-2) 4).toNat = 0 := by
          have r21848 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21849 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
          have e21850 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
          have e21851 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
          have e21852 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
          have e21853 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
          have e21854 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
          have b21855 := hb (x (-5) 7)
          have b21856 := hb (x (-4) 6)
          have b21857 := hb (x (-3) 5)
          have b21858 := hb (x (-2) 4)
          have b21859 := hb (x (-1) 11)
          have b21860 := hb (x 0 10)
          have b21861 := hb (x 1 9)
          have b21862 := hb (x 2 8)
          clear * - r21848 e21849 e21850 e21851 e21852 e21853 e21854 b21855 b21856 b21857 b21858 b21859 b21860 b21861 b21862 d21831 d21785 g22 g15
          omega
        have d21863 : (x (-2) 4 && x (-2) 8).toNat = 0 := by
          have r21864 := hand1 (x (-2) 4) (x (-2) 8)
          have b21865 := hb (x (-2) 4)
          have b21866 := hb (x (-2) 4 && x (-2) 8)
          clear * - r21864 b21865 b21866 d21847
          omega
        have d21867 : (x (-3) 5).toNat = 0 := by
          have r21868 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21869 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
          have e21870 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
          have e21871 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
          have e21872 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
          have e21873 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
          have e21874 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
          have b21875 := hb (x (-5) 7)
          have b21876 := hb (x (-4) 6)
          have b21877 := hb (x (-3) 5)
          have b21878 := hb (x (-2) 4)
          have b21879 := hb (x (-1) 11)
          have b21880 := hb (x 0 10)
          have b21881 := hb (x 1 9)
          have b21882 := hb (x 2 8)
          clear * - r21868 e21869 e21870 e21871 e21872 e21873 e21874 b21875 b21876 b21877 b21878 b21879 b21880 b21881 b21882 d21831 d21785 g22 g15 d21847
          omega
        have d21883 : (x (-3) 5 && x (-3) 9).toNat = 0 := by
          have r21884 := hand1 (x (-3) 5) (x (-3) 9)
          have b21885 := hb (x (-3) 5)
          have b21886 := hb (x (-3) 5 && x (-3) 9)
          clear * - r21884 b21885 b21886 d21867
          omega
        have d21887 : (x (-4) 6).toNat = 0 := by
          have r21888 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21889 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
          have e21890 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
          have e21891 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
          have e21892 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
          have e21893 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
          have e21894 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
          have b21895 := hb (x (-5) 7)
          have b21896 := hb (x (-4) 6)
          have b21897 := hb (x (-3) 5)
          have b21898 := hb (x (-2) 4)
          have b21899 := hb (x (-1) 11)
          have b21900 := hb (x 0 10)
          have b21901 := hb (x 1 9)
          have b21902 := hb (x 2 8)
          clear * - r21888 e21889 e21890 e21891 e21892 e21893 e21894 b21895 b21896 b21897 b21898 b21899 b21900 b21901 b21902 d21831 d21785 g22 g15 d21847 d21867
          omega
        have d21903 : (x (-4) 6 && x (-4) 10).toNat = 0 := by
          have r21904 := hand1 (x (-4) 6) (x (-4) 10)
          have b21905 := hb (x (-4) 6)
          have b21906 := hb (x (-4) 6 && x (-4) 10)
          clear * - r21904 b21905 b21906 d21887
          omega
        have d21907 : (x (-5) 7).toNat = 0 := by
          have r21908 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21909 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
          have e21910 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
          have e21911 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
          have e21912 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
          have e21913 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
          have e21914 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
          have b21915 := hb (x (-5) 7)
          have b21916 := hb (x (-4) 6)
          have b21917 := hb (x (-3) 5)
          have b21918 := hb (x (-2) 4)
          have b21919 := hb (x (-1) 11)
          have b21920 := hb (x 0 10)
          have b21921 := hb (x 1 9)
          have b21922 := hb (x 2 8)
          clear * - r21908 e21909 e21910 e21911 e21912 e21913 e21914 b21915 b21916 b21917 b21918 b21919 b21920 b21921 b21922 d21831 d21785 g22 g15 d21847 d21867 d21887
          omega
        have d21923 : (x (-5) 7 && x (-5) 11).toNat = 0 := by
          have r21924 := hand1 (x (-5) 7) (x (-5) 11)
          have b21925 := hb (x (-5) 7)
          have b21926 := hb (x (-5) 7 && x (-5) 11)
          clear * - r21924 b21925 b21926 d21907
          omega
        have d21927 : (x (-6) 7).toNat = 0 := by
          have r21928 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21929 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e21930 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e21931 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e21932 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e21933 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e21934 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b21935 := hb (x (-6) 7)
          have b21936 := hb (x (-5) 6)
          have b21937 := hb (x (-4) 5)
          have b21938 := hb (x (-3) 4)
          have b21939 := hb (x (-2) 11)
          have b21940 := hb (x (-1) 10)
          have b21941 := hb (x 0 9)
          have b21942 := hb (x 1 8)
          clear * - r21928 e21929 e21930 e21931 e21932 e21933 e21934 b21935 b21936 b21937 b21938 b21939 b21940 b21941 b21942 d21693 f21692 g14 g8 d21709 d21733 d21761
          omega
        have d21943 : (x (-6) 7 && x (-6) 14).toNat = 0 := by
          have r21944 := hand1 (x (-6) 7) (x (-6) 14)
          have b21945 := hb (x (-6) 7)
          have b21946 := hb (x (-6) 7 && x (-6) 14)
          clear * - r21944 b21945 b21946 d21927
          omega
        have d21947 : (x (-6) 7 && x (-6) 12).toNat = 0 := by
          have r21948 := hand1 (x (-6) 7) (x (-6) 12)
          have b21949 := hb (x (-6) 7)
          have b21950 := hb (x (-6) 7 && x (-6) 12)
          clear * - r21948 b21949 b21950 d21927
          omega
        have r21951 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21952 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
        have e21953 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
        have e21954 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
        have e21955 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
        have e21956 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
        have e21957 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
        have r21958 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21959 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
        have e21960 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
        have e21961 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
        have e21962 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
        have e21963 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
        have e21964 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
        have r21965 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21966 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e21967 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e21968 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e21969 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e21970 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e21971 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have r21972 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21973 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
        have e21974 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
        have r21975 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21976 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e21977 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have r21978 : 1 ≤ (x 2 4).toNat + (x 1 1 && x 1 5).toNat + (x 0 2 && x 0 6).toNat + (x (-1) 3 && x (-1) 7).toNat + (x (-2) 4 && x (-2) 8).toNat + (x (-3) 5 && x (-3) 9).toNat + (x (-4) 6 && x (-4) 10).toNat + (x (-5) 7 && x (-5) 11).toNat + (x (-6) 8 && x (-6) 12).toNat + (x (-7) 9 && x (-7) 13).toNat + (x (-8) 10 && x (-8) 14).toNat + (x (-9) 11).toNat := by have q := hcov4 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21979 : (x 1 1 && x 1 5).toNat = (x 1 5).toNat := handr _ _ (fun h => hp13 1 (hp5 1 (h)))
        have e21980 : (x (-8) 10 && x (-8) 14).toNat = (x (-8) 10).toNat := handl _ _ (fun h => hp2 (-8) (hp10 (-8) (h)))
        have r21981 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := by have q := hcov5 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r21982 : 1 ≤ (x 1 7).toNat + (x 0 1 && x 0 8).toNat + (x (-1) 2 && x (-1) 9).toNat + (x (-2) 3 && x (-2) 10).toNat + (x (-3) 4 && x (-3) 11).toNat + (x (-4) 5 && x (-4) 12).toNat + (x (-5) 6 && x (-5) 13).toNat + (x (-6) 7 && x (-6) 14).toNat + (x (-7) 8).toNat := by have q := hcov7 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r21983 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r21984 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r21985 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r21986 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
        have r21987 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
        have r21988 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
        have r21989 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
        have r21990 := hand1 (x (-6) 8) (x (-6) 12)
        have r21991 := hand1 (x (-7) 9) (x (-7) 13)
        have r21992 := hand2 (x (-7) 8) (x (-7) 13)
        have r21993 := hand1 (x (-8) 9) (x (-8) 14)
        have r21994 := hand2 (x 6 1) (x 6 10)
        have r21995 := hand2 (x 5 2) (x 5 11)
        have r21996 := hand2 (x (-7) 1) (x (-7) 11)
        have r21997 := hand1 (x (-8) 2) (x (-8) 12)
        have r21998 := hand1 (x (-9) 3) (x (-9) 13)
        have r21999 := hand1 (x (-10) 4) (x (-10) 14)
        have r22000 := hand1 (x (-4) 4) (x (-4) 14)
        linarith only [r21951, e21952, e21953, e21954, e21955, e21956, e21957, r21958, e21959, e21960, e21961, e21962, e21963, e21964, r21965, e21966, e21967, e21968, e21969, e21970, e21971, r21972, e21973, e21974, r21975, e21976, e21977, r21978, e21979, e21980, r21981, r21982, r21983, r21984, r21985, r21986, r21987, r21988, r21989, r21990, r21991, r21992, r21993, r21994, r21995, r21996, r21997, r21998, r21999, r22000, g22, g27, g28, g31, d21827, d21823, d18364, g46, d21863, d21883, d21903, d21923, d18360, g59, g60, d21729, d21757, d21781, d21947, d18384, g87, g88, g89, d21753, d21777, d21943, d21819, g101, g102, g104, g105, g106]
    · have f22078 : (x 0 8).toNat = 1 := by rw [h18382]; rfl
      have d22079 : (x (-4) 4).toNat = 0 := by
        have r22080 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22081 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
        have e22082 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
        have e22083 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
        have e22084 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
        have e22085 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
        have e22086 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
        have b22087 := hb (x (-7) 7)
        have b22088 := hb (x (-6) 6)
        have b22089 := hb (x (-5) 5)
        have b22090 := hb (x (-4) 4)
        have b22091 := hb (x (-3) 11)
        have b22092 := hb (x (-2) 10)
        have b22093 := hb (x (-1) 9)
        have b22094 := hb (x 0 8)
        clear * - r22080 e22081 e22082 e22083 e22084 e22085 e22086 b22087 b22088 b22089 b22090 b22091 b22092 b22093 b22094 f22078 g13 g7 g3
        omega
      have d22095 : (x (-4) 4 && x (-4) 14).toNat = 0 := by
        have r22096 := hand1 (x (-4) 4) (x (-4) 14)
        have b22097 := hb (x (-4) 4)
        have b22098 := hb (x (-4) 4 && x (-4) 14)
        clear * - r22096 b22097 b22098 d22079
        omega
      have d22099 : (x (-5) 5).toNat = 1 := by
        have r22100 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b22101 := hb (x (-5) 5)
        have b22102 := hb (x 0 10)
        have b22103 := hb (x (-1) 1 && x (-1) 11)
        have b22104 := hb (x (-2) 2 && x (-2) 12)
        have b22105 := hb (x (-3) 3 && x (-3) 13)
        have b22106 := hb (x (-4) 4 && x (-4) 14)
        clear * - r22100 b22101 b22102 b22103 b22104 b22105 b22106 g22 g104 g105 g106 d22095
        omega
      have r22107 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22108 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
      have e22109 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
      have e22110 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
      have e22111 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
      have e22112 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
      have e22113 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
      have b22114 := hb (x (-7) 7)
      have b22115 := hb (x (-6) 6)
      have b22116 := hb (x (-5) 5)
      have b22117 := hb (x (-4) 4)
      have b22118 := hb (x (-3) 11)
      have b22119 := hb (x (-2) 10)
      have b22120 := hb (x (-1) 9)
      have b22121 := hb (x 0 8)
      linarith only [r22107, e22108, e22109, e22110, e22111, e22112, e22113, b22114, b22115, b22116, b22117, b22118, b22119, b22120, b22121, f22078, g13, g7, g3, d22079, d22099]
  · have f22122 : (x 0 7).toNat = 1 := by rw [h18368]; rfl
    have d22123 : (x 7 8).toNat = 0 := by
      have r22124 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22125 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e22126 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e22127 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e22128 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e22129 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e22130 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b22131 := hb (x 0 7)
      have b22132 := hb (x 1 6)
      have b22133 := hb (x 2 5)
      have b22134 := hb (x 3 4)
      have b22135 := hb (x 4 11)
      have b22136 := hb (x 5 10)
      have b22137 := hb (x 6 9)
      have b22138 := hb (x 7 8)
      clear * - r22124 e22125 e22126 e22127 e22128 e22129 e22130 b22131 b22132 b22133 b22134 b22135 b22136 b22137 b22138 g35 g32 g28 f22122
      omega
    have d22139 : (x 6 9).toNat = 0 := by
      have r22140 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22141 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e22142 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e22143 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e22144 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e22145 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e22146 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b22147 := hb (x 0 7)
      have b22148 := hb (x 1 6)
      have b22149 := hb (x 2 5)
      have b22150 := hb (x 3 4)
      have b22151 := hb (x 4 11)
      have b22152 := hb (x 5 10)
      have b22153 := hb (x 6 9)
      have b22154 := hb (x 7 8)
      clear * - r22140 e22141 e22142 e22143 e22144 e22145 e22146 b22147 b22148 b22149 b22150 b22151 b22152 b22153 b22154 d22123 g35 g32 g28 f22122
      omega
    have d22155 : (x 5 10).toNat = 0 := by
      have r22156 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22157 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e22158 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e22159 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e22160 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e22161 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e22162 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b22163 := hb (x 0 7)
      have b22164 := hb (x 1 6)
      have b22165 := hb (x 2 5)
      have b22166 := hb (x 3 4)
      have b22167 := hb (x 4 11)
      have b22168 := hb (x 5 10)
      have b22169 := hb (x 6 9)
      have b22170 := hb (x 7 8)
      clear * - r22156 e22157 e22158 e22159 e22160 e22161 e22162 b22163 b22164 b22165 b22166 b22167 b22168 b22169 b22170 d22123 d22139 g35 g32 g28 f22122
      omega
    have d22171 : (x 5 1 && x 5 10).toNat = 0 := by
      have r22172 := hand2 (x 5 1) (x 5 10)
      have b22173 := hb (x 5 10)
      have b22174 := hb (x 5 1 && x 5 10)
      clear * - r22172 b22173 b22174 d22155
      omega
    have d22175 : (x 4 2 && x 4 11).toNat = 1 := by
      have r22176 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b22177 := hb (x 0 6)
      have b22178 := hb (x 6 9)
      have b22179 := hb (x 5 1 && x 5 10)
      have b22180 := hb (x 4 2 && x 4 11)
      have b22181 := hb (x 3 3 && x 3 12)
      have b22182 := hb (x 2 4 && x 2 13)
      have b22183 := hb (x 1 5 && x 1 14)
      clear * - r22176 b22177 b22178 b22179 b22180 b22181 b22182 b22183 d22139 d22171 g98 g99 g100 g21
      omega
    have d22184 : (x 4 11).toNat = 1 := by
      have r22185 := hand2 (x 4 2) (x 4 11)
      have b22186 := hb (x 4 11)
      have b22187 := hb (x 4 2 && x 4 11)
      clear * - r22185 b22186 b22187 d22175
      omega
    have r22188 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e22189 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e22190 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e22191 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e22192 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e22193 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e22194 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b22195 := hb (x 0 7)
    have b22196 := hb (x 1 6)
    have b22197 := hb (x 2 5)
    have b22198 := hb (x 3 4)
    have b22199 := hb (x 4 11)
    have b22200 := hb (x 5 10)
    have b22201 := hb (x 6 9)
    have b22202 := hb (x 7 8)
    linarith only [r22188, e22189, e22190, e22191, e22192, e22193, e22194, b22195, b22196, b22197, b22198, b22199, b22200, b22201, b22202, d22123, d22139, d22155, d22184, g35, g32, g28, f22122]

theorem cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b110 (x : ℤ → Fin 16 → Bool)
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
    (g6 : (x (-2) 7).toNat = 0)
    (g7 : (x (-2) 10).toNat = 0)
    (g8 : (x (-2) 11).toNat = 0)
    (g9 : (x (-1) 3).toNat = 0)
    (g10 : (x (-1) 4).toNat = 0)
    (g11 : (x (-1) 5).toNat = 0)
    (g12 : (x (-1) 6).toNat = 0)
    (g13 : (x (-1) 9).toNat = 0)
    (g14 : (x (-1) 10).toNat = 0)
    (g15 : (x (-1) 11).toNat = 0)
    (g16 : (x (-1) 13).toNat = 0)
    (g17 : (x 0 2).toNat = 1)
    (g18 : (x 0 3).toNat = 1)
    (g19 : (x 0 4).toNat = 1)
    (g20 : (x 0 5).toNat = 1)
    (g21 : (x 0 6).toNat = 0)
    (g22 : (x 0 10).toNat = 0)
    (g23 : (x 0 11).toNat = 1)
    (g24 : (x 0 13).toNat = 1)
    (g25 : (x 1 2).toNat = 0)
    (g26 : (x 1 4).toNat = 0)
    (g27 : (x 1 5).toNat = 0)
    (g28 : (x 1 6).toNat = 0)
    (g29 : (x 1 10).toNat = 0)
    (g30 : (x 1 12).toNat = 0)
    (g31 : (x 2 4).toNat = 0)
    (g32 : (x 2 5).toNat = 0)
    (g33 : (x 2 9).toNat = 0)
    (g34 : (x 2 11).toNat = 0)
    (g35 : (x 3 4).toNat = 0)
    (g36 : (x 3 8).toNat = 0)
    (g37 : (x 3 10).toNat = 0)
    (g38 : (x 4 9).toNat = 0)
    (g39 : (x 5 8).toNat = 0)
    (g40 : (x 5 8 && x 5 11).toNat = 0)
    (g41 : (x 4 9 && x 4 12).toNat = 0)
    (g42 : (x 3 10 && x 3 13).toNat = 0)
    (g43 : (x 2 11 && x 2 14).toNat = 0)
    (g44 : (x (-3) 2 && x (-3) 6).toNat = 0)
    (g45 : (x (-4) 3 && x (-4) 7).toNat = 0)
    (g46 : (x (-1) 3 && x (-1) 7).toNat = 0)
    (g47 : (x 1 2 && x 1 6).toNat = 0)
    (g48 : (x (-1) 4 && x (-1) 8).toNat = 0)
    (g49 : (x (-2) 5 && x (-2) 9).toNat = 0)
    (g50 : (x (-3) 6 && x (-3) 10).toNat = 0)
    (g51 : (x (-4) 7 && x (-4) 11).toNat = 0)
    (g52 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g53 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g54 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g55 : (x 2 8 && x 2 12).toNat = 0)
    (g56 : (x 1 9 && x 1 13).toNat = 0)
    (g57 : (x (-2) 1 && x (-2) 6).toNat = 0)
    (g58 : (x (-3) 2 && x (-3) 7).toNat = 0)
    (g59 : (x (-1) 2 && x (-1) 7).toNat = 0)
    (g60 : (x (-2) 3 && x (-2) 8).toNat = 0)
    (g61 : (x 1 4 && x 1 9).toNat = 0)
    (g62 : (x 0 5 && x 0 10).toNat = 0)
    (g63 : (x (-1) 6 && x (-1) 11).toNat = 0)
    (g64 : (x (-2) 7 && x (-2) 12).toNat = 0)
    (g65 : (x 2 7 && x 2 12).toNat = 0)
    (g66 : (x 1 8 && x 1 13).toNat = 0)
    (g67 : (x 3 8 && x 3 13).toNat = 0)
    (g68 : (x 2 9 && x 2 14).toNat = 0)
    (g69 : (x (-1) 3 && x (-1) 9).toNat = 0)
    (g70 : (x (-2) 4 && x (-2) 10).toNat = 0)
    (g71 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g72 : (x 1 2 && x 1 8).toNat = 0)
    (g73 : (x (-1) 4 && x (-1) 10).toNat = 0)
    (g74 : (x (-2) 5 && x (-2) 11).toNat = 0)
    (g75 : (x (-3) 6 && x (-3) 12).toNat = 0)
    (g76 : (x (-4) 7 && x (-4) 13).toNat = 0)
    (g77 : (x 5 2 && x 5 8).toNat = 0)
    (g78 : (x 4 3 && x 4 9).toNat = 0)
    (g79 : (x 3 4 && x 3 10).toNat = 0)
    (g80 : (x 2 5 && x 2 11).toNat = 0)
    (g81 : (x 1 6 && x 1 12).toNat = 0)
    (g82 : (x 2 6 && x 2 12).toNat = 0)
    (g83 : (x 1 7 && x 1 13).toNat = 0)
    (g84 : (x (-1) 1 && x (-1) 8).toNat = 0)
    (g85 : (x (-2) 2 && x (-2) 9).toNat = 0)
    (g86 : (x (-3) 3 && x (-3) 10).toNat = 0)
    (g87 : (x (-1) 2 && x (-1) 9).toNat = 0)
    (g88 : (x (-2) 3 && x (-2) 10).toNat = 0)
    (g89 : (x (-3) 4 && x (-3) 11).toNat = 0)
    (g90 : (x 3 4 && x 3 11).toNat = 0)
    (g91 : (x 2 5 && x 2 12).toNat = 0)
    (g92 : (x 1 6 && x 1 13).toNat = 0)
    (g93 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g94 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g95 : (x 0 1 && x 0 10).toNat = 0)
    (g96 : (x (-1) 2 && x (-1) 11).toNat = 0)
    (g97 : (x (-2) 3 && x (-2) 12).toNat = 0)
    (g98 : (x 3 3 && x 3 12).toNat = 0)
    (g99 : (x 2 4 && x 2 13).toNat = 0)
    (g100 : (x 1 5 && x 1 14).toNat = 0)
    (g101 : (x 3 4 && x 3 13).toNat = 0)
    (g102 : (x 2 5 && x 2 14).toNat = 0)
    (g103 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g104 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g105 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g106 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g107 : (x 2 4 && x 2 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b110_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83 g84 g85 g86 g87 g88 g89 g90 g91 g92 g93 g94 g95 g96 g97 g98 g99 g100 g101 g102 g103 g104 g105 g106 g107
