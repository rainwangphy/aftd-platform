import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt1110110

Topic: combinatorics   Node: 419a03a197a3

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_alternates_core: under the layer-free tight-cover constraints for k = 15 and 119 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt1110110_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 7).toNat = 0)
    (g1 : (x (-3) 11).toNat = 0)
    (g2 : (x (-2) 6).toNat = 0)
    (g3 : (x (-2) 10).toNat = 0)
    (g4 : (x (-2) 11).toNat = 0)
    (g5 : (x (-1) 3).toNat = 0)
    (g6 : (x (-1) 5).toNat = 0)
    (g7 : (x (-1) 9).toNat = 0)
    (g8 : (x (-1) 10).toNat = 0)
    (g9 : (x (-1) 11).toNat = 0)
    (g10 : (x (-1) 13).toNat = 0)
    (g11 : (x 0 2).toNat = 1)
    (g12 : (x 0 4).toNat = 1)
    (g13 : (x 0 5).toNat = 0)
    (g14 : (x 0 7).toNat = 0)
    (g15 : (x 0 12).toNat = 1)
    (g16 : (x 0 13).toNat = 1)
    (g17 : (x 1 1).toNat = 1)
    (g18 : (x 1 3).toNat = 0)
    (g19 : (x 1 4).toNat = 0)
    (g20 : (x 1 5).toNat = 0)
    (g21 : (x 1 6).toNat = 0)
    (g22 : (x 1 10).toNat = 0)
    (g23 : (x 1 11).toNat = 0)
    (g24 : (x 1 12).toNat = 0)
    (g25 : (x 1 14).toNat = 0)
    (g26 : (x 2 2).toNat = 0)
    (g27 : (x 2 4).toNat = 0)
    (g28 : (x 2 5).toNat = 0)
    (g29 : (x 2 6).toNat = 0)
    (g30 : (x 2 10).toNat = 0)
    (g31 : (x 2 13).toNat = 0)
    (g32 : (x 2 14).toNat = 0)
    (g33 : (x 3 1).toNat = 1)
    (g34 : (x 3 4).toNat = 0)
    (g35 : (x 3 9).toNat = 0)
    (g36 : (x 3 12).toNat = 0)
    (g37 : (x 3 13).toNat = 1)
    (g38 : (x 4 2).toNat = 0)
    (g39 : (x 4 4).toNat = 0)
    (g40 : (x 4 6).toNat = 0)
    (g41 : (x 4 8).toNat = 0)
    (g42 : (x 4 10).toNat = 0)
    (g43 : (x 4 12).toNat = 0)
    (g44 : (x 4 3 && x 4 6).toNat = 0)
    (g45 : (x 3 4 && x 3 7).toNat = 0)
    (g46 : (x 2 5 && x 2 8).toNat = 0)
    (g47 : (x 1 6 && x 1 9).toNat = 0)
    (g48 : (x 0 7 && x 0 10).toNat = 0)
    (g49 : (x (-1) 8 && x (-1) 11).toNat = 0)
    (g50 : (x 2 2 && x 2 6).toNat = 0)
    (g51 : (x 1 3 && x 1 7).toNat = 0)
    (g52 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g53 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g54 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g55 : (x 3 4 && x 3 8).toNat = 0)
    (g56 : (x 2 5 && x 2 9).toNat = 0)
    (g57 : (x 1 6 && x 1 10).toNat = 0)
    (g58 : (x 0 7 && x 0 11).toNat = 0)
    (g59 : (x (-1) 1 && x (-1) 6).toNat = 0)
    (g60 : (x (-2) 2 && x (-2) 7).toNat = 0)
    (g61 : (x (-3) 3 && x (-3) 8).toNat = 0)
    (g62 : (x 1 1 && x 1 6).toNat = 0)
    (g63 : (x 0 2 && x 0 7).toNat = 0)
    (g64 : (x (-1) 3 && x (-1) 8).toNat = 0)
    (g65 : (x 4 3 && x 4 8).toNat = 0)
    (g66 : (x 3 4 && x 3 9).toNat = 0)
    (g67 : (x 2 5 && x 2 10).toNat = 0)
    (g68 : (x 1 6 && x 1 11).toNat = 0)
    (g69 : (x 0 7 && x 0 12).toNat = 0)
    (g70 : (x (-1) 8 && x (-1) 13).toNat = 0)
    (g71 : (x 0 1 && x 0 7).toNat = 0)
    (g72 : (x (-1) 2 && x (-1) 8).toNat = 0)
    (g73 : (x (-2) 3 && x (-2) 9).toNat = 0)
    (g74 : (x (-1) 3 && x (-1) 9).toNat = 0)
    (g75 : (x (-2) 4 && x (-2) 10).toNat = 0)
    (g76 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g77 : (x 3 4 && x 3 10).toNat = 0)
    (g78 : (x 2 5 && x 2 11).toNat = 0)
    (g79 : (x 1 6 && x 1 12).toNat = 0)
    (g80 : (x 0 7 && x 0 13).toNat = 0)
    (g81 : (x 4 6 && x 4 12).toNat = 0)
    (g82 : (x 2 8 && x 2 14).toNat = 0)
    (g83 : (x (-1) 1 && x (-1) 8).toNat = 0)
    (g84 : (x (-2) 2 && x (-2) 9).toNat = 0)
    (g85 : (x (-3) 3 && x (-3) 10).toNat = 0)
    (g86 : (x 4 3 && x 4 10).toNat = 0)
    (g87 : (x 3 4 && x 3 11).toNat = 0)
    (g88 : (x 2 5 && x 2 12).toNat = 0)
    (g89 : (x 1 6 && x 1 13).toNat = 0)
    (g90 : (x 0 7 && x 0 14).toNat = 0)
    (g91 : (x 4 6 && x 4 13).toNat = 0)
    (g92 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g93 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g94 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g95 : (x (-2) 2 && x (-2) 11).toNat = 0)
    (g96 : (x (-3) 3 && x (-3) 12).toNat = 0)
    (g97 : (x 4 1 && x 4 10).toNat = 0)
    (g98 : (x 2 3 && x 2 12).toNat = 0)
    (g99 : (x 1 4 && x 1 13).toNat = 0)
    (g100 : (x 4 2 && x 4 11).toNat = 0)
    (g101 : (x 3 3 && x 3 12).toNat = 0)
    (g102 : (x 2 4 && x 2 13).toNat = 0)
    (g103 : (x 1 5 && x 1 14).toNat = 0)
    (g104 : (x 4 3 && x 4 12).toNat = 0)
    (g105 : (x 3 4 && x 3 13).toNat = 0)
    (g106 : (x 2 5 && x 2 14).toNat = 0)
    (g107 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g108 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g109 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g110 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g111 : (x 3 2 && x 3 12).toNat = 0)
    (g112 : (x 2 3 && x 2 13).toNat = 0)
    (g113 : (x 1 4 && x 1 14).toNat = 0)
    (g114 : (x 3 4 && x 3 14).toNat = 0)
    (g115 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g116 : (x (-2) 2 && x (-2) 13).toNat = 0)
    (g117 : (x (-3) 3 && x (-3) 14).toNat = 0)
    (g118 : (x 4 1 && x 4 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d34477 : (x 0 5 && x 0 14).toNat = 0 := by
    have r34478 := hand1 (x 0 5) (x 0 14)
    have b34479 := hb (x 0 5)
    have b34480 := hb (x 0 5 && x 0 14)
    clear * - r34478 b34479 b34480 g13
    omega
  cases h34481 : x 0 6
  · have f34482 : (x 0 6).toNat = 0 := by rw [h34481]; rfl
    cases h34483 : x 0 8
    · have f34484 : (x 0 8).toNat = 0 := by rw [h34483]; rfl
      have d34485 : (x 0 2 && x 0 8).toNat = 0 := by
        have r34486 := hand2 (x 0 2) (x 0 8)
        have b34487 := hb (x 0 8)
        have b34488 := hb (x 0 2 && x 0 8)
        clear * - r34486 b34487 b34488 f34484
        omega
      have d34489 : (x 0 4 && x 0 8).toNat = 0 := by
        have r34490 := hand2 (x 0 4) (x 0 8)
        have b34491 := hb (x 0 8)
        have b34492 := hb (x 0 4 && x 0 8)
        clear * - r34490 b34491 b34492 f34484
        omega
      have r34493 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r34494 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r34495 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r34496 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e34497 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e34498 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e34499 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e34500 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e34501 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e34502 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have r34503 : (x (-11) 12).toNat + (x (-12) 1 && x (-12) 13).toNat + (x (-13) 2 && x (-13) 14).toNat + (x (-14) 3).toNat = 1 := by have q := hd12 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e34504 : (x (-12) 1 && x (-12) 13).toNat = (x (-12) 13).toNat := handr _ _ (fun h => hp13 (-12) (h))
      have e34505 : (x (-13) 2 && x (-13) 14).toNat = (x (-13) 2).toNat := handl _ _ (fun h => hp2 (-13) (h))
      have r34506 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e34507 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e34508 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have r34509 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e34510 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e34511 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have r34512 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r34513 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e34514 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
      have e34515 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
      have r34516 : 1 ≤ (x 2 6).toNat + (x 1 1 && x 1 7).toNat + (x 0 2 && x 0 8).toNat + (x (-1) 3 && x (-1) 9).toNat + (x (-2) 4 && x (-2) 10).toNat + (x (-3) 5 && x (-3) 11).toNat + (x (-4) 6 && x (-4) 12).toNat + (x (-5) 7 && x (-5) 13).toNat + (x (-6) 8 && x (-6) 14).toNat + (x (-7) 9).toNat := by have q := hcov6 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r34517 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r34518 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r34519 : 1 ≤ (x (-7) 11).toNat + (x (-8) 1 && x (-8) 12).toNat + (x (-9) 2 && x (-9) 13).toNat + (x (-10) 3 && x (-10) 14).toNat + (x (-11) 4).toNat := by have q := hcov11 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r34520 : 1 ≤ (x (-11) 13).toNat + (x (-12) 1 && x (-12) 14).toNat + (x (-13) 2).toNat := by have q := hcov13 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r34521 : (x (-11) 4).toNat ≤ (x (-11) 12).toNat := himp _ _ (hp4 (-11))
      have r34522 : (x (-11) 5).toNat ≤ (x (-11) 13).toNat := himp _ _ (hp5 (-11))
      have r34523 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
      have r34524 := hand1 (x (-4) 8) (x (-4) 12)
      have r34525 := hand1 (x (-5) 9) (x (-5) 13)
      have r34526 := hand2 (x 1 1) (x 1 7)
      have r34527 := hand1 (x (-4) 6) (x (-4) 12)
      have r34528 := hand1 (x (-5) 7) (x (-5) 13)
      have r34529 := hand1 (x (-6) 8) (x (-6) 14)
      have r34530 := hand2 (x 6 1) (x 6 10)
      have r34531 := hand2 (x 5 2) (x 5 11)
      have r34532 := hand1 (x (-7) 1) (x (-7) 11)
      have r34533 := hand2 (x (-8) 2) (x (-8) 12)
      have r34534 := hand2 (x (-9) 3) (x (-9) 13)
      have r34535 := hand2 (x (-10) 4) (x (-10) 14)
      have r34536 := hand2 (x (-8) 1) (x (-8) 12)
      have r34537 := hand2 (x (-9) 2) (x (-9) 13)
      have r34538 := hand2 (x (-10) 3) (x (-10) 14)
      have r34539 := hand2 (x (-12) 1) (x (-12) 14)
      have b34593 := hb (x 7 1)
      linarith only [r34493, r34494, r34495, r34496, e34497, e34498, e34499, e34500, e34501, e34502, r34503, e34504, e34505, r34506, e34507, e34508, r34509, e34510, e34511, r34512, r34513, e34514, e34515, r34516, r34517, r34518, r34519, r34520, r34521, r34522, r34523, r34524, r34525, r34526, r34527, r34528, r34529, r34530, r34531, r34532, r34533, r34534, r34535, r34536, r34537, r34538, r34539, b34593, g0, g1, g2, g3, g5, g6, g7, g11, g12, f34484, g17, g18, g21, g26, g29, g33, g39, g50, g51, d34489, g52, g53, g54, d34485, g74, g75, g76, g104, g105, g106]
    · have f34627 : (x 0 8).toNat = 1 := by rw [h34483]; rfl
      have d34628 : (x (-4) 4).toNat = 0 := by
        have r34629 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34630 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
        have e34631 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
        have e34632 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
        have e34633 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
        have e34634 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
        have e34635 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
        have b34636 := hb (x (-7) 7)
        have b34637 := hb (x (-6) 6)
        have b34638 := hb (x (-5) 5)
        have b34639 := hb (x (-4) 4)
        have b34640 := hb (x (-3) 11)
        have b34641 := hb (x (-2) 10)
        have b34642 := hb (x (-1) 9)
        have b34643 := hb (x 0 8)
        clear * - r34629 e34630 e34631 e34632 e34633 e34634 e34635 b34636 b34637 b34638 b34639 b34640 b34641 b34642 b34643 f34627 g7 g3 g1
        omega
      have d34644 : (x (-4) 4 && x (-4) 14).toNat = 0 := by
        have r34645 := hand1 (x (-4) 4) (x (-4) 14)
        have b34646 := hb (x (-4) 4)
        have b34647 := hb (x (-4) 4 && x (-4) 14)
        clear * - r34645 b34646 b34647 d34628
        omega
      have d34648 : (x (-4) 4 && x (-4) 13).toNat = 0 := by
        have r34649 := hand1 (x (-4) 4) (x (-4) 13)
        have b34650 := hb (x (-4) 4)
        have b34651 := hb (x (-4) 4 && x (-4) 13)
        clear * - r34649 b34650 b34651 d34628
        omega
      have d34652 : (x (-4) 4 && x (-4) 11).toNat = 0 := by
        have r34653 := hand1 (x (-4) 4) (x (-4) 11)
        have b34654 := hb (x (-4) 4)
        have b34655 := hb (x (-4) 4 && x (-4) 11)
        clear * - r34653 b34654 b34655 d34628
        omega
      have d34656 : (x (-4) 4 && x (-4) 9).toNat = 0 := by
        have r34657 := hand1 (x (-4) 4) (x (-4) 9)
        have b34658 := hb (x (-4) 4)
        have b34659 := hb (x (-4) 4 && x (-4) 9)
        clear * - r34657 b34658 b34659 d34628
        omega
      have d34660 : (x (-5) 5).toNat = 0 := by
        have r34661 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34662 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
        have e34663 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
        have e34664 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
        have e34665 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
        have e34666 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
        have e34667 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
        have b34668 := hb (x (-7) 7)
        have b34669 := hb (x (-6) 6)
        have b34670 := hb (x (-5) 5)
        have b34671 := hb (x (-4) 4)
        have b34672 := hb (x (-3) 11)
        have b34673 := hb (x (-2) 10)
        have b34674 := hb (x (-1) 9)
        have b34675 := hb (x 0 8)
        clear * - r34661 e34662 e34663 e34664 e34665 e34666 e34667 b34668 b34669 b34670 b34671 b34672 b34673 b34674 b34675 f34627 g7 g3 g1 d34628
        omega
      have d34676 : (x (-5) 5 && x (-5) 14).toNat = 0 := by
        have r34677 := hand1 (x (-5) 5) (x (-5) 14)
        have b34678 := hb (x (-5) 5)
        have b34679 := hb (x (-5) 5 && x (-5) 14)
        clear * - r34677 b34678 b34679 d34660
        omega
      have d34680 : (x (-5) 5 && x (-5) 12).toNat = 0 := by
        have r34681 := hand1 (x (-5) 5) (x (-5) 12)
        have b34682 := hb (x (-5) 5)
        have b34683 := hb (x (-5) 5 && x (-5) 12)
        clear * - r34681 b34682 b34683 d34660
        omega
      have d34684 : (x (-5) 5 && x (-5) 10).toNat = 0 := by
        have r34685 := hand1 (x (-5) 5) (x (-5) 10)
        have b34686 := hb (x (-5) 5)
        have b34687 := hb (x (-5) 5 && x (-5) 10)
        clear * - r34685 b34686 b34687 d34660
        omega
      have d34688 : (x 0 10).toNat = 1 := by
        have r34689 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b34690 := hb (x (-5) 5)
        have b34691 := hb (x 0 10)
        have b34692 := hb (x (-1) 1 && x (-1) 11)
        have b34693 := hb (x (-2) 2 && x (-2) 12)
        have b34694 := hb (x (-3) 3 && x (-3) 13)
        have b34695 := hb (x (-4) 4 && x (-4) 14)
        clear * - r34689 b34690 b34691 b34692 b34693 b34694 b34695 g108 g109 g110 d34644 d34660
        omega
      have d34696 : (x 2 8).toNat = 0 := by
        have r34697 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34698 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e34699 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e34700 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e34701 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e34702 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e34703 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b34704 := hb (x (-5) 7)
        have b34705 := hb (x (-4) 6)
        have b34706 := hb (x (-3) 5)
        have b34707 := hb (x (-2) 4)
        have b34708 := hb (x (-1) 11)
        have b34709 := hb (x 0 10)
        have b34710 := hb (x 1 9)
        have b34711 := hb (x 2 8)
        clear * - r34697 e34698 e34699 e34700 e34701 e34702 e34703 b34704 b34705 b34706 b34707 b34708 b34709 b34710 b34711 d34688 g9
        omega
      have d34712 : (x 1 9).toNat = 0 := by
        have r34713 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34714 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e34715 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e34716 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e34717 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e34718 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e34719 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b34720 := hb (x (-5) 7)
        have b34721 := hb (x (-4) 6)
        have b34722 := hb (x (-3) 5)
        have b34723 := hb (x (-2) 4)
        have b34724 := hb (x (-1) 11)
        have b34725 := hb (x 0 10)
        have b34726 := hb (x 1 9)
        have b34727 := hb (x 2 8)
        clear * - r34713 e34714 e34715 e34716 e34717 e34718 e34719 b34720 b34721 b34722 b34723 b34724 b34725 b34726 b34727 d34696 d34688 g9
        omega
      have d34728 : (x (-2) 4).toNat = 0 := by
        have r34729 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34730 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e34731 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e34732 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e34733 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e34734 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e34735 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b34736 := hb (x (-5) 7)
        have b34737 := hb (x (-4) 6)
        have b34738 := hb (x (-3) 5)
        have b34739 := hb (x (-2) 4)
        have b34740 := hb (x (-1) 11)
        have b34741 := hb (x 0 10)
        have b34742 := hb (x 1 9)
        have b34743 := hb (x 2 8)
        clear * - r34729 e34730 e34731 e34732 e34733 e34734 e34735 b34736 b34737 b34738 b34739 b34740 b34741 b34742 b34743 d34696 d34712 d34688 g9
        omega
      have d34744 : (x (-2) 4 && x (-2) 9).toNat = 0 := by
        have r34745 := hand1 (x (-2) 4) (x (-2) 9)
        have b34746 := hb (x (-2) 4)
        have b34747 := hb (x (-2) 4 && x (-2) 9)
        clear * - r34745 b34746 b34747 d34728
        omega
      have d34748 : (x (-3) 5).toNat = 0 := by
        have r34749 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34750 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e34751 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e34752 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e34753 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e34754 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e34755 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b34756 := hb (x (-5) 7)
        have b34757 := hb (x (-4) 6)
        have b34758 := hb (x (-3) 5)
        have b34759 := hb (x (-2) 4)
        have b34760 := hb (x (-1) 11)
        have b34761 := hb (x 0 10)
        have b34762 := hb (x 1 9)
        have b34763 := hb (x 2 8)
        clear * - r34749 e34750 e34751 e34752 e34753 e34754 e34755 b34756 b34757 b34758 b34759 b34760 b34761 b34762 b34763 d34696 d34712 d34688 g9 d34728
        omega
      have d34764 : (x (-3) 5 && x (-3) 10).toNat = 0 := by
        have r34765 := hand1 (x (-3) 5) (x (-3) 10)
        have b34766 := hb (x (-3) 5)
        have b34767 := hb (x (-3) 5 && x (-3) 10)
        clear * - r34765 b34766 b34767 d34748
        omega
      have d34768 : (x (-4) 6).toNat = 0 := by
        have r34769 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34770 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e34771 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e34772 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e34773 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e34774 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e34775 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b34776 := hb (x (-5) 7)
        have b34777 := hb (x (-4) 6)
        have b34778 := hb (x (-3) 5)
        have b34779 := hb (x (-2) 4)
        have b34780 := hb (x (-1) 11)
        have b34781 := hb (x 0 10)
        have b34782 := hb (x 1 9)
        have b34783 := hb (x 2 8)
        clear * - r34769 e34770 e34771 e34772 e34773 e34774 e34775 b34776 b34777 b34778 b34779 b34780 b34781 b34782 b34783 d34696 d34712 d34688 g9 d34728 d34748
        omega
      have d34784 : (x (-4) 6 && x (-4) 11).toNat = 0 := by
        have r34785 := hand1 (x (-4) 6) (x (-4) 11)
        have b34786 := hb (x (-4) 6)
        have b34787 := hb (x (-4) 6 && x (-4) 11)
        clear * - r34785 b34786 b34787 d34768
        omega
      have d34788 : (x (-5) 7).toNat = 0 := by
        have r34789 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34790 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e34791 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e34792 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e34793 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e34794 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e34795 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b34796 := hb (x (-5) 7)
        have b34797 := hb (x (-4) 6)
        have b34798 := hb (x (-3) 5)
        have b34799 := hb (x (-2) 4)
        have b34800 := hb (x (-1) 11)
        have b34801 := hb (x 0 10)
        have b34802 := hb (x 1 9)
        have b34803 := hb (x 2 8)
        clear * - r34789 e34790 e34791 e34792 e34793 e34794 e34795 b34796 b34797 b34798 b34799 b34800 b34801 b34802 b34803 d34696 d34712 d34688 g9 d34728 d34748 d34768
        omega
      have d34804 : (x (-5) 7 && x (-5) 12).toNat = 0 := by
        have r34805 := hand1 (x (-5) 7) (x (-5) 12)
        have b34806 := hb (x (-5) 7)
        have b34807 := hb (x (-5) 7 && x (-5) 12)
        clear * - r34805 b34806 b34807 d34788
        omega
      have d34808 : (x (-6) 6).toNat = 0 := by
        have r34809 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34810 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
        have e34811 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
        have e34812 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
        have e34813 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
        have e34814 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
        have e34815 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
        have b34816 := hb (x (-7) 7)
        have b34817 := hb (x (-6) 6)
        have b34818 := hb (x (-5) 5)
        have b34819 := hb (x (-4) 4)
        have b34820 := hb (x (-3) 11)
        have b34821 := hb (x (-2) 10)
        have b34822 := hb (x (-1) 9)
        have b34823 := hb (x 0 8)
        clear * - r34809 e34810 e34811 e34812 e34813 e34814 e34815 b34816 b34817 b34818 b34819 b34820 b34821 b34822 b34823 f34627 g7 g3 g1 d34628 d34660
        omega
      have d34824 : (x (-6) 6 && x (-6) 13).toNat = 0 := by
        have r34825 := hand1 (x (-6) 6) (x (-6) 13)
        have b34826 := hb (x (-6) 6)
        have b34827 := hb (x (-6) 6 && x (-6) 13)
        clear * - r34825 b34826 b34827 d34808
        omega
      have d34828 : (x (-6) 6 && x (-6) 11).toNat = 0 := by
        have r34829 := hand1 (x (-6) 6) (x (-6) 11)
        have b34830 := hb (x (-6) 6)
        have b34831 := hb (x (-6) 6 && x (-6) 11)
        clear * - r34829 b34830 b34831 d34808
        omega
      have d34832 : (x 0 9).toNat = 1 := by
        have r34833 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b34834 := hb (x (-6) 6)
        have b34835 := hb (x 0 9)
        have b34836 := hb (x (-1) 1 && x (-1) 10)
        have b34837 := hb (x (-2) 2 && x (-2) 11)
        have b34838 := hb (x (-3) 3 && x (-3) 12)
        have b34839 := hb (x (-4) 4 && x (-4) 13)
        have b34840 := hb (x (-5) 5 && x (-5) 14)
        clear * - r34833 b34834 b34835 b34836 b34837 b34838 b34839 b34840 g94 g95 g96 d34648 d34676 d34808
        omega
      have d34841 : (x 1 8).toNat = 0 := by
        have r34842 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34843 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
        have e34844 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
        have e34845 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
        have e34846 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
        have e34847 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
        have e34848 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
        have b34849 := hb (x (-6) 7)
        have b34850 := hb (x (-5) 6)
        have b34851 := hb (x (-4) 5)
        have b34852 := hb (x (-3) 4)
        have b34853 := hb (x (-2) 11)
        have b34854 := hb (x (-1) 10)
        have b34855 := hb (x 0 9)
        have b34856 := hb (x 1 8)
        clear * - r34842 e34843 e34844 e34845 e34846 e34847 e34848 b34849 b34850 b34851 b34852 b34853 b34854 b34855 b34856 d34832 g8 g4
        omega
      have d34857 : (x (-3) 4).toNat = 0 := by
        have r34858 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34859 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
        have e34860 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
        have e34861 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
        have e34862 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
        have e34863 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
        have e34864 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
        have b34865 := hb (x (-6) 7)
        have b34866 := hb (x (-5) 6)
        have b34867 := hb (x (-4) 5)
        have b34868 := hb (x (-3) 4)
        have b34869 := hb (x (-2) 11)
        have b34870 := hb (x (-1) 10)
        have b34871 := hb (x 0 9)
        have b34872 := hb (x 1 8)
        clear * - r34858 e34859 e34860 e34861 e34862 e34863 e34864 b34865 b34866 b34867 b34868 b34869 b34870 b34871 b34872 d34841 d34832 g8 g4
        omega
      have d34873 : (x (-3) 4 && x (-3) 10).toNat = 0 := by
        have r34874 := hand1 (x (-3) 4) (x (-3) 10)
        have b34875 := hb (x (-3) 4)
        have b34876 := hb (x (-3) 4 && x (-3) 10)
        clear * - r34874 b34875 b34876 d34857
        omega
      have d34877 : (x (-4) 5).toNat = 0 := by
        have r34878 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34879 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
        have e34880 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
        have e34881 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
        have e34882 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
        have e34883 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
        have e34884 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
        have b34885 := hb (x (-6) 7)
        have b34886 := hb (x (-5) 6)
        have b34887 := hb (x (-4) 5)
        have b34888 := hb (x (-3) 4)
        have b34889 := hb (x (-2) 11)
        have b34890 := hb (x (-1) 10)
        have b34891 := hb (x 0 9)
        have b34892 := hb (x 1 8)
        clear * - r34878 e34879 e34880 e34881 e34882 e34883 e34884 b34885 b34886 b34887 b34888 b34889 b34890 b34891 b34892 d34841 d34832 g8 g4 d34857
        omega
      have d34893 : (x (-4) 5 && x (-4) 11).toNat = 0 := by
        have r34894 := hand1 (x (-4) 5) (x (-4) 11)
        have b34895 := hb (x (-4) 5)
        have b34896 := hb (x (-4) 5 && x (-4) 11)
        clear * - r34894 b34895 b34896 d34877
        omega
      have d34897 : (x (-5) 6).toNat = 0 := by
        have r34898 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34899 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
        have e34900 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
        have e34901 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
        have e34902 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
        have e34903 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
        have e34904 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
        have b34905 := hb (x (-6) 7)
        have b34906 := hb (x (-5) 6)
        have b34907 := hb (x (-4) 5)
        have b34908 := hb (x (-3) 4)
        have b34909 := hb (x (-2) 11)
        have b34910 := hb (x (-1) 10)
        have b34911 := hb (x 0 9)
        have b34912 := hb (x 1 8)
        clear * - r34898 e34899 e34900 e34901 e34902 e34903 e34904 b34905 b34906 b34907 b34908 b34909 b34910 b34911 b34912 d34841 d34832 g8 g4 d34857 d34877
        omega
      have d34913 : (x (-5) 6 && x (-5) 12).toNat = 0 := by
        have r34914 := hand1 (x (-5) 6) (x (-5) 12)
        have b34915 := hb (x (-5) 6)
        have b34916 := hb (x (-5) 6 && x (-5) 12)
        clear * - r34914 b34915 b34916 d34897
        omega
      have d34917 : (x (-6) 7).toNat = 0 := by
        have r34918 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34919 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
        have e34920 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
        have e34921 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
        have e34922 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
        have e34923 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
        have e34924 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
        have b34925 := hb (x (-6) 7)
        have b34926 := hb (x (-5) 6)
        have b34927 := hb (x (-4) 5)
        have b34928 := hb (x (-3) 4)
        have b34929 := hb (x (-2) 11)
        have b34930 := hb (x (-1) 10)
        have b34931 := hb (x 0 9)
        have b34932 := hb (x 1 8)
        clear * - r34918 e34919 e34920 e34921 e34922 e34923 e34924 b34925 b34926 b34927 b34928 b34929 b34930 b34931 b34932 d34841 d34832 g8 g4 d34857 d34877 d34897
        omega
      have d34933 : (x (-6) 7 && x (-6) 13).toNat = 0 := by
        have r34934 := hand1 (x (-6) 7) (x (-6) 13)
        have b34935 := hb (x (-6) 7)
        have b34936 := hb (x (-6) 7 && x (-6) 13)
        clear * - r34934 b34935 b34936 d34917
        omega
      have d34937 : (x (-7) 7).toNat = 0 := by
        have r34938 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34939 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
        have e34940 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
        have e34941 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
        have e34942 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
        have e34943 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
        have e34944 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
        have b34945 := hb (x (-7) 7)
        have b34946 := hb (x (-6) 6)
        have b34947 := hb (x (-5) 5)
        have b34948 := hb (x (-4) 4)
        have b34949 := hb (x (-3) 11)
        have b34950 := hb (x (-2) 10)
        have b34951 := hb (x (-1) 9)
        have b34952 := hb (x 0 8)
        clear * - r34938 e34939 e34940 e34941 e34942 e34943 e34944 b34945 b34946 b34947 b34948 b34949 b34950 b34951 b34952 f34627 g7 g3 g1 d34628 d34660 d34808
        omega
      have d34953 : (x (-7) 7 && x (-7) 14).toNat = 0 := by
        have r34954 := hand1 (x (-7) 7) (x (-7) 14)
        have b34955 := hb (x (-7) 7)
        have b34956 := hb (x (-7) 7 && x (-7) 14)
        clear * - r34954 b34955 b34956 d34937
        omega
      have d34957 : (x (-7) 7 && x (-7) 12).toNat = 0 := by
        have r34958 := hand1 (x (-7) 7) (x (-7) 12)
        have b34959 := hb (x (-7) 7)
        have b34960 := hb (x (-7) 7 && x (-7) 12)
        clear * - r34958 b34959 b34960 d34937
        omega
      have d34961 : (x (-8) 8).toNat = 1 := by
        have r34962 : 1 ≤ (x 0 7).toNat + (x (-1) 1 && x (-1) 8).toNat + (x (-2) 2 && x (-2) 9).toNat + (x (-3) 3 && x (-3) 10).toNat + (x (-4) 4 && x (-4) 11).toNat + (x (-5) 5 && x (-5) 12).toNat + (x (-6) 6 && x (-6) 13).toNat + (x (-7) 7 && x (-7) 14).toNat + (x (-8) 8).toNat := by have q := hcov7 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b34963 := hb (x (-8) 8)
        have b34964 := hb (x 0 7)
        have b34965 := hb (x (-1) 1 && x (-1) 8)
        have b34966 := hb (x (-2) 2 && x (-2) 9)
        have b34967 := hb (x (-3) 3 && x (-3) 10)
        have b34968 := hb (x (-4) 4 && x (-4) 11)
        have b34969 := hb (x (-5) 5 && x (-5) 12)
        have b34970 := hb (x (-6) 6 && x (-6) 13)
        have b34971 := hb (x (-7) 7 && x (-7) 14)
        clear * - r34962 b34963 b34964 b34965 b34966 b34967 b34968 b34969 b34970 b34971 g14 g83 g84 g85 d34652 d34680 d34824 d34953
        omega
      have d34972 : (x (-9) 9).toNat = 0 := by
        have r34973 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34974 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
        have e34975 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
        have e34976 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
        have e34977 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
        have e34978 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
        have e34979 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
        have b34980 := hb (x (-15) 7)
        have b34981 := hb (x (-14) 6)
        have b34982 := hb (x (-13) 5)
        have b34983 := hb (x (-12) 4)
        have b34984 := hb (x (-11) 11)
        have b34985 := hb (x (-10) 10)
        have b34986 := hb (x (-9) 9)
        have b34987 := hb (x (-8) 8)
        clear * - r34973 e34974 e34975 e34976 e34977 e34978 e34979 b34980 b34981 b34982 b34983 b34984 b34985 b34986 b34987 d34961
        omega
      have d34988 : (x (-9) 9 && x (-9) 14).toNat = 0 := by
        have r34989 := hand1 (x (-9) 9) (x (-9) 14)
        have b34990 := hb (x (-9) 9)
        have b34991 := hb (x (-9) 9 && x (-9) 14)
        clear * - r34989 b34990 b34991 d34972
        omega
      have d34992 : (x (-10) 10).toNat = 0 := by
        have r34993 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34994 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
        have e34995 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
        have e34996 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
        have e34997 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
        have e34998 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
        have e34999 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
        have b35000 := hb (x (-15) 7)
        have b35001 := hb (x (-14) 6)
        have b35002 := hb (x (-13) 5)
        have b35003 := hb (x (-12) 4)
        have b35004 := hb (x (-11) 11)
        have b35005 := hb (x (-10) 10)
        have b35006 := hb (x (-9) 9)
        have b35007 := hb (x (-8) 8)
        clear * - r34993 e34994 e34995 e34996 e34997 e34998 e34999 b35000 b35001 b35002 b35003 b35004 b35005 b35006 b35007 d34961 d34972
        omega
      have d35008 : (x (-8) 8 && x (-8) 13).toNat = 1 := by
        have r35009 : 1 ≤ (x 0 5).toNat + (x (-1) 1 && x (-1) 6).toNat + (x (-2) 2 && x (-2) 7).toNat + (x (-3) 3 && x (-3) 8).toNat + (x (-4) 4 && x (-4) 9).toNat + (x (-5) 5 && x (-5) 10).toNat + (x (-6) 6 && x (-6) 11).toNat + (x (-7) 7 && x (-7) 12).toNat + (x (-8) 8 && x (-8) 13).toNat + (x (-9) 9 && x (-9) 14).toNat + (x (-10) 10).toNat := by have q := hcov5 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35010 := hb (x (-10) 10)
        have b35011 := hb (x 0 5)
        have b35012 := hb (x (-1) 1 && x (-1) 6)
        have b35013 := hb (x (-2) 2 && x (-2) 7)
        have b35014 := hb (x (-3) 3 && x (-3) 8)
        have b35015 := hb (x (-4) 4 && x (-4) 9)
        have b35016 := hb (x (-5) 5 && x (-5) 10)
        have b35017 := hb (x (-6) 6 && x (-6) 11)
        have b35018 := hb (x (-7) 7 && x (-7) 12)
        have b35019 := hb (x (-8) 8 && x (-8) 13)
        have b35020 := hb (x (-9) 9 && x (-9) 14)
        clear * - r35009 b35010 b35011 b35012 b35013 b35014 b35015 b35016 b35017 b35018 b35019 b35020 g13 g59 g60 g61 d34656 d34684 d34828 d34957 d34988 d34992
        omega
      have d35021 : (x (-8) 13).toNat = 1 := by
        have r35022 := hand2 (x (-8) 8) (x (-8) 13)
        have b35023 := hb (x (-8) 13)
        have b35024 := hb (x (-8) 8 && x (-8) 13)
        clear * - r35022 b35023 b35024 d35008
        omega
      have d35025 : (x (-8) 1).toNat = 1 := by
        have r35026 : (x (-8) 13).toNat ≤ (x (-8) 1).toNat := himp _ _ (hp13 (-8))
        have b35027 := hb (x (-8) 1)
        have b35028 := hb (x (-8) 13)
        clear * - r35026 b35027 b35028 d35021
        omega
      have d35029 : (x (-7) 14).toNat = 0 := by
        have r35030 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35031 := hb (x (-8) 1)
        have b35032 := hb (x (-7) 14)
        clear * - r35030 b35031 b35032 d35025
        omega
      have d35033 : (x (-7) 8 && x (-7) 14).toNat = 0 := by
        have r35034 := hand2 (x (-7) 8) (x (-7) 14)
        have b35035 := hb (x (-7) 14)
        have b35036 := hb (x (-7) 8 && x (-7) 14)
        clear * - r35034 b35035 b35036 d35029
        omega
      have d35037 : (x (-8) 9).toNat = 1 := by
        have r35038 : 1 ≤ (x 1 6).toNat + (x 0 1 && x 0 7).toNat + (x (-1) 2 && x (-1) 8).toNat + (x (-2) 3 && x (-2) 9).toNat + (x (-3) 4 && x (-3) 10).toNat + (x (-4) 5 && x (-4) 11).toNat + (x (-5) 6 && x (-5) 12).toNat + (x (-6) 7 && x (-6) 13).toNat + (x (-7) 8 && x (-7) 14).toNat + (x (-8) 9).toNat := by have q := hcov6 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35039 := hb (x (-8) 9)
        have b35040 := hb (x 1 6)
        have b35041 := hb (x 0 1 && x 0 7)
        have b35042 := hb (x (-1) 2 && x (-1) 8)
        have b35043 := hb (x (-2) 3 && x (-2) 9)
        have b35044 := hb (x (-3) 4 && x (-3) 10)
        have b35045 := hb (x (-4) 5 && x (-4) 11)
        have b35046 := hb (x (-5) 6 && x (-5) 12)
        have b35047 := hb (x (-6) 7 && x (-6) 13)
        have b35048 := hb (x (-7) 8 && x (-7) 14)
        clear * - r35038 b35039 b35040 b35041 b35042 b35043 b35044 b35045 b35046 b35047 b35048 g21 g71 g72 g73 d34873 d34893 d34913 d34933 d35033
        omega
      have d35049 : (x (-7) 8).toNat = 0 := by
        have r35050 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35051 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
        have e35052 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
        have e35053 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
        have e35054 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
        have e35055 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
        have e35056 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
        have b35057 := hb (x (-14) 7)
        have b35058 := hb (x (-13) 6)
        have b35059 := hb (x (-12) 5)
        have b35060 := hb (x (-11) 4)
        have b35061 := hb (x (-10) 11)
        have b35062 := hb (x (-9) 10)
        have b35063 := hb (x (-8) 9)
        have b35064 := hb (x (-7) 8)
        clear * - r35050 e35051 e35052 e35053 e35054 e35055 e35056 b35057 b35058 b35059 b35060 b35061 b35062 b35063 b35064 d35037
        omega
      have d35065 : (x (-9) 10).toNat = 0 := by
        have r35066 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35067 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
        have e35068 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
        have e35069 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
        have e35070 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
        have e35071 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
        have e35072 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
        have b35073 := hb (x (-14) 7)
        have b35074 := hb (x (-13) 6)
        have b35075 := hb (x (-12) 5)
        have b35076 := hb (x (-11) 4)
        have b35077 := hb (x (-10) 11)
        have b35078 := hb (x (-9) 10)
        have b35079 := hb (x (-8) 9)
        have b35080 := hb (x (-7) 8)
        clear * - r35066 e35067 e35068 e35069 e35070 e35071 e35072 b35073 b35074 b35075 b35076 b35077 b35078 b35079 b35080 d35049 d35037
        omega
      have d35081 : (x (-10) 11).toNat = 0 := by
        have r35082 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35083 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
        have e35084 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
        have e35085 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
        have e35086 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
        have e35087 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
        have e35088 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
        have b35089 := hb (x (-14) 7)
        have b35090 := hb (x (-13) 6)
        have b35091 := hb (x (-12) 5)
        have b35092 := hb (x (-11) 4)
        have b35093 := hb (x (-10) 11)
        have b35094 := hb (x (-9) 10)
        have b35095 := hb (x (-8) 9)
        have b35096 := hb (x (-7) 8)
        clear * - r35082 e35083 e35084 e35085 e35086 e35087 e35088 b35089 b35090 b35091 b35092 b35093 b35094 b35095 b35096 d35049 d35037 d35065
        omega
      have d35097 : (x (-11) 4).toNat = 0 := by
        have r35098 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35099 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
        have e35100 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
        have e35101 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
        have e35102 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
        have e35103 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
        have e35104 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
        have b35105 := hb (x (-14) 7)
        have b35106 := hb (x (-13) 6)
        have b35107 := hb (x (-12) 5)
        have b35108 := hb (x (-11) 4)
        have b35109 := hb (x (-10) 11)
        have b35110 := hb (x (-9) 10)
        have b35111 := hb (x (-8) 9)
        have b35112 := hb (x (-7) 8)
        clear * - r35098 e35099 e35100 e35101 e35102 e35103 e35104 b35105 b35106 b35107 b35108 b35109 b35110 b35111 b35112 d35049 d35037 d35065 d35081
        omega
      have d35113 : (x (-11) 4 && x (-11) 14).toNat = 0 := by
        have r35114 := hand1 (x (-11) 4) (x (-11) 14)
        have b35115 := hb (x (-11) 4)
        have b35116 := hb (x (-11) 4 && x (-11) 14)
        clear * - r35114 b35115 b35116 d35097
        omega
      have d35117 : (x (-12) 5).toNat = 0 := by
        have r35118 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35119 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
        have e35120 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
        have e35121 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
        have e35122 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
        have e35123 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
        have e35124 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
        have b35125 := hb (x (-14) 7)
        have b35126 := hb (x (-13) 6)
        have b35127 := hb (x (-12) 5)
        have b35128 := hb (x (-11) 4)
        have b35129 := hb (x (-10) 11)
        have b35130 := hb (x (-9) 10)
        have b35131 := hb (x (-8) 9)
        have b35132 := hb (x (-7) 8)
        clear * - r35118 e35119 e35120 e35121 e35122 e35123 e35124 b35125 b35126 b35127 b35128 b35129 b35130 b35131 b35132 d35049 d35037 d35065 d35081 d35097
        omega
      have d35133 : (x (-7) 9 && x (-7) 14).toNat = 0 := by
        have r35134 := hand2 (x (-7) 9) (x (-7) 14)
        have b35135 := hb (x (-7) 14)
        have b35136 := hb (x (-7) 9 && x (-7) 14)
        clear * - r35134 b35135 b35136 d35029
        omega
      have d35137 : (x (-7) 6).toNat = 0 := by
        have r35138 : (x (-7) 6).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp6 (-7))
        have b35139 := hb (x (-7) 6)
        have b35140 := hb (x (-7) 14)
        clear * - r35138 b35139 b35140 d35029
        omega
      have d35141 : (x (-7) 2).toNat = 0 := by
        have r35142 : (x (-7) 2).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp2 (-7))
        have b35143 := hb (x (-7) 2)
        have b35144 := hb (x (-7) 14)
        clear * - r35142 b35143 b35144 d35029
        omega
      have d35145 : (x (-7) 10).toNat = 0 := by
        have r35146 : (x (-7) 10).toNat ≤ (x (-7) 2).toNat := himp _ _ (hp10 (-7))
        have b35147 := hb (x (-7) 2)
        have b35148 := hb (x (-7) 10)
        clear * - r35146 b35147 b35148 d35141
        omega
      have d35149 : (x (-7) 12).toNat = 0 := by
        have r35150 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35151 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
        have e35152 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
        have b35153 := hb (x (-10) 3)
        have b35154 := hb (x (-9) 2)
        have b35155 := hb (x (-8) 13)
        have b35156 := hb (x (-7) 12)
        clear * - r35150 e35151 e35152 b35153 b35154 b35155 b35156 d35021
        omega
      have d35157 : (x (-9) 2).toNat = 0 := by
        have r35158 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35159 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
        have e35160 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
        have b35161 := hb (x (-10) 3)
        have b35162 := hb (x (-9) 2)
        have b35163 := hb (x (-8) 13)
        have b35164 := hb (x (-7) 12)
        clear * - r35158 e35159 e35160 b35161 b35162 b35163 b35164 d35149 d35021
        omega
      have d35165 : (x (-9) 2 && x (-9) 12).toNat = 0 := by
        have r35166 := hand1 (x (-9) 2) (x (-9) 12)
        have b35167 := hb (x (-9) 2)
        have b35168 := hb (x (-9) 2 && x (-9) 12)
        clear * - r35166 b35167 b35168 d35157
        omega
      have d35169 : (x (-10) 3).toNat = 0 := by
        have r35170 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35171 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
        have e35172 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
        have b35173 := hb (x (-10) 3)
        have b35174 := hb (x (-9) 2)
        have b35175 := hb (x (-8) 13)
        have b35176 := hb (x (-7) 12)
        clear * - r35170 e35171 e35172 b35173 b35174 b35175 b35176 d35149 d35021 d35157
        omega
      have d35177 : (x (-10) 3 && x (-10) 13).toNat = 0 := by
        have r35178 := hand1 (x (-10) 3) (x (-10) 13)
        have b35179 := hb (x (-10) 3)
        have b35180 := hb (x (-10) 3 && x (-10) 13)
        clear * - r35178 b35179 b35180 d35169
        omega
      have d35181 : (x (-8) 1 && x (-8) 11).toNat = 1 := by
        have r35182 : 1 ≤ (x (-7) 10).toNat + (x (-8) 1 && x (-8) 11).toNat + (x (-9) 2 && x (-9) 12).toNat + (x (-10) 3 && x (-10) 13).toNat + (x (-11) 4 && x (-11) 14).toNat + (x (-12) 5).toNat := by have q := hcov10 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35183 := hb (x (-12) 5)
        have b35184 := hb (x (-7) 10)
        have b35185 := hb (x (-8) 1 && x (-8) 11)
        have b35186 := hb (x (-9) 2 && x (-9) 12)
        have b35187 := hb (x (-10) 3 && x (-10) 13)
        have b35188 := hb (x (-11) 4 && x (-11) 14)
        clear * - r35182 b35183 b35184 b35185 b35186 b35187 b35188 d35145 d35165 d35177 d35113 d35117
        omega
      have d35189 : (x (-8) 11).toNat = 1 := by
        have r35190 := hand2 (x (-8) 1) (x (-8) 11)
        have b35191 := hb (x (-8) 11)
        have b35192 := hb (x (-8) 1 && x (-8) 11)
        clear * - r35190 b35191 b35192 d35181
        omega
      have d35193 : (x (-8) 3).toNat = 1 := by
        have r35194 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
        have b35195 := hb (x (-8) 3)
        have b35196 := hb (x (-8) 11)
        clear * - r35194 b35195 b35196 d35189
        omega
      have d35197 : (x (-5) 12).toNat = 0 := by
        have r35198 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35199 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
        have e35200 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
        have b35201 := hb (x (-8) 3)
        have b35202 := hb (x (-7) 2)
        have b35203 := hb (x (-6) 13)
        have b35204 := hb (x (-5) 12)
        clear * - r35198 e35199 e35200 b35201 b35202 b35203 b35204 d35141 d35193
        omega
      have d35205 : (x (-5) 4).toNat = 0 := by
        have r35206 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
        have b35207 := hb (x (-5) 4)
        have b35208 := hb (x (-5) 12)
        clear * - r35206 b35207 b35208 d35197
        omega
      have d35209 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
        have r35210 := hand1 (x (-5) 4) (x (-5) 13)
        have b35211 := hb (x (-5) 4)
        have b35212 := hb (x (-5) 4 && x (-5) 13)
        clear * - r35210 b35211 b35212 d35205
        omega
      have d35213 : (x (-6) 13).toNat = 0 := by
        have r35214 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35215 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
        have e35216 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
        have b35217 := hb (x (-8) 3)
        have b35218 := hb (x (-7) 2)
        have b35219 := hb (x (-6) 13)
        have b35220 := hb (x (-5) 12)
        clear * - r35214 e35215 e35216 b35217 b35218 b35219 b35220 d35197 d35141 d35193
        omega
      have d35221 : (x (-6) 8 && x (-6) 13).toNat = 0 := by
        have r35222 := hand2 (x (-6) 8) (x (-6) 13)
        have b35223 := hb (x (-6) 13)
        have b35224 := hb (x (-6) 8 && x (-6) 13)
        clear * - r35222 b35223 b35224 d35213
        omega
      have d35225 : (x (-8) 10).toNat = 1 := by
        have r35226 : 1 ≤ (x 2 5).toNat + (x 1 1 && x 1 6).toNat + (x 0 2 && x 0 7).toNat + (x (-1) 3 && x (-1) 8).toNat + (x (-2) 4 && x (-2) 9).toNat + (x (-3) 5 && x (-3) 10).toNat + (x (-4) 6 && x (-4) 11).toNat + (x (-5) 7 && x (-5) 12).toNat + (x (-6) 8 && x (-6) 13).toNat + (x (-7) 9 && x (-7) 14).toNat + (x (-8) 10).toNat := by have q := hcov5 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35227 := hb (x (-8) 10)
        have b35228 := hb (x 2 5)
        have b35229 := hb (x 1 1 && x 1 6)
        have b35230 := hb (x 0 2 && x 0 7)
        have b35231 := hb (x (-1) 3 && x (-1) 8)
        have b35232 := hb (x (-2) 4 && x (-2) 9)
        have b35233 := hb (x (-3) 5 && x (-3) 10)
        have b35234 := hb (x (-4) 6 && x (-4) 11)
        have b35235 := hb (x (-5) 7 && x (-5) 12)
        have b35236 := hb (x (-6) 8 && x (-6) 13)
        have b35237 := hb (x (-7) 9 && x (-7) 14)
        clear * - r35226 b35227 b35228 b35229 b35230 b35231 b35232 b35233 b35234 b35235 b35236 b35237 g28 g62 g63 g64 d34744 d34764 d34784 d34804 d35221 d35133
        omega
      have d35238 : (x (-8) 2).toNat = 1 := by
        have r35239 : (x (-8) 10).toNat ≤ (x (-8) 2).toNat := himp _ _ (hp10 (-8))
        have b35240 := hb (x (-8) 2)
        have b35241 := hb (x (-8) 10)
        clear * - r35239 b35240 b35241 d35225
        omega
      have d35242 : (x (-6) 12).toNat = 0 := by
        have r35243 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35244 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
        have e35245 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
        have b35246 := hb (x (-9) 3)
        have b35247 := hb (x (-8) 2)
        have b35248 := hb (x (-7) 13)
        have b35249 := hb (x (-6) 12)
        clear * - r35243 e35244 e35245 b35246 b35247 b35248 b35249 d35238
        omega
      have d35250 : (x (-6) 4).toNat = 0 := by
        have r35251 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
        have b35252 := hb (x (-6) 4)
        have b35253 := hb (x (-6) 12)
        clear * - r35251 b35252 b35253 d35242
        omega
      have d35254 : (x (-6) 4 && x (-6) 14).toNat = 0 := by
        have r35255 := hand1 (x (-6) 4) (x (-6) 14)
        have b35256 := hb (x (-6) 4)
        have b35257 := hb (x (-6) 4 && x (-6) 14)
        clear * - r35255 b35256 b35257 d35250
        omega
      have d35258 : (x (-7) 13).toNat = 0 := by
        have r35259 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35260 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
        have e35261 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
        have b35262 := hb (x (-9) 3)
        have b35263 := hb (x (-8) 2)
        have b35264 := hb (x (-7) 13)
        have b35265 := hb (x (-6) 12)
        clear * - r35259 e35260 e35261 b35262 b35263 b35264 b35265 d35242 d35238
        omega
      have d35266 : (x (-7) 5).toNat = 0 := by
        have r35267 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
        have b35268 := hb (x (-7) 5)
        have b35269 := hb (x (-7) 13)
        clear * - r35267 b35268 b35269 d35258
        omega
      have d35270 : (x (-6) 5).toNat = 0 := by
        have r35271 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
        have b35272 := hb (x (-6) 5)
        have b35273 := hb (x (-6) 13)
        clear * - r35271 b35272 b35273 d35213
        omega
      have d35274 : (x (-6) 5 && x (-6) 14).toNat = 0 := by
        have r35275 := hand1 (x (-6) 5) (x (-6) 14)
        have b35276 := hb (x (-6) 5)
        have b35277 := hb (x (-6) 5 && x (-6) 14)
        clear * - r35275 b35276 b35277 d35270
        omega
      have d35278 : (x (-4) 3 && x (-4) 12).toNat = 1 := by
        have r35279 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35280 := hb (x (-7) 6)
        have b35281 := hb (x (-1) 9)
        have b35282 := hb (x (-2) 1 && x (-2) 10)
        have b35283 := hb (x (-3) 2 && x (-3) 11)
        have b35284 := hb (x (-4) 3 && x (-4) 12)
        have b35285 := hb (x (-5) 4 && x (-5) 13)
        have b35286 := hb (x (-6) 5 && x (-6) 14)
        clear * - r35279 b35280 b35281 b35282 b35283 b35284 b35285 b35286 g7 g92 g93 d35209 d35274 d35137
        omega
      have d35287 : (x (-4) 12).toNat = 1 := by
        have r35288 := hand2 (x (-4) 3) (x (-4) 12)
        have b35289 := hb (x (-4) 12)
        have b35290 := hb (x (-4) 3 && x (-4) 12)
        clear * - r35288 b35289 b35290 d35278
        omega
      have d35291 : (x (-5) 13).toNat = 0 := by
        have r35292 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35293 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e35294 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have b35295 := hb (x (-7) 3)
        have b35296 := hb (x (-6) 2)
        have b35297 := hb (x (-5) 13)
        have b35298 := hb (x (-4) 12)
        clear * - r35292 e35293 e35294 b35295 b35296 b35297 b35298 d35287
        omega
      have d35299 : (x (-5) 3 && x (-5) 13).toNat = 0 := by
        have r35300 := hand2 (x (-5) 3) (x (-5) 13)
        have b35301 := hb (x (-5) 13)
        have b35302 := hb (x (-5) 3 && x (-5) 13)
        clear * - r35300 b35301 b35302 d35291
        omega
      have d35303 : (x (-4) 2 && x (-4) 12).toNat = 1 := by
        have r35304 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35305 := hb (x (-7) 5)
        have b35306 := hb (x (-2) 10)
        have b35307 := hb (x (-3) 1 && x (-3) 11)
        have b35308 := hb (x (-4) 2 && x (-4) 12)
        have b35309 := hb (x (-5) 3 && x (-5) 13)
        have b35310 := hb (x (-6) 4 && x (-6) 14)
        clear * - r35304 b35305 b35306 b35307 b35308 b35309 b35310 g3 g107 d35299 d35254 d35266
        omega
      have d35311 : (x (-4) 2).toNat = 1 := by
        have r35312 := hand1 (x (-4) 2) (x (-4) 12)
        have b35313 := hb (x (-4) 2)
        have b35314 := hb (x (-4) 2 && x (-4) 12)
        clear * - r35312 b35313 b35314 d35303
        omega
      have d35315 : (x (-4) 14).toNat = 1 := by
        have r35316 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
        have b35317 := hb (x (-4) 2)
        have b35318 := hb (x (-4) 14)
        clear * - r35316 b35317 b35318 d35311
        omega
      have d35319 : (x (-2) 12).toNat = 0 := by
        have r35320 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35321 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e35322 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have b35323 := hb (x (-5) 3)
        have b35324 := hb (x (-4) 2)
        have b35325 := hb (x (-3) 13)
        have b35326 := hb (x (-2) 12)
        clear * - r35320 e35321 e35322 b35323 b35324 b35325 b35326 d35311
        omega
      have d35327 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
        have r35328 := hand2 (x (-2) 1) (x (-2) 12)
        have b35329 := hb (x (-2) 12)
        have b35330 := hb (x (-2) 1 && x (-2) 12)
        clear * - r35328 b35329 b35330 d35319
        omega
      have d35331 : (x (-2) 9 && x (-2) 12).toNat = 0 := by
        have r35332 := hand2 (x (-2) 9) (x (-2) 12)
        have b35333 := hb (x (-2) 12)
        have b35334 := hb (x (-2) 9 && x (-2) 12)
        clear * - r35332 b35333 b35334 d35319
        omega
      have d35335 : (x (-3) 13).toNat = 0 := by
        have r35336 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35337 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e35338 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have b35339 := hb (x (-5) 3)
        have b35340 := hb (x (-4) 2)
        have b35341 := hb (x (-3) 13)
        have b35342 := hb (x (-2) 12)
        clear * - r35336 e35337 e35338 b35339 b35340 b35341 b35342 d35319 d35311
        omega
      have d35343 : (x (-3) 2 && x (-3) 13).toNat = 0 := by
        have r35344 := hand2 (x (-3) 2) (x (-3) 13)
        have b35345 := hb (x (-3) 13)
        have b35346 := hb (x (-3) 2 && x (-3) 13)
        clear * - r35344 b35345 b35346 d35335
        omega
      have d35347 : (x (-4) 3 && x (-4) 14).toNat = 1 := by
        have r35348 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35349 := hb (x (-5) 4)
        have b35350 := hb (x (-1) 11)
        have b35351 := hb (x (-2) 1 && x (-2) 12)
        have b35352 := hb (x (-3) 2 && x (-3) 13)
        have b35353 := hb (x (-4) 3 && x (-4) 14)
        clear * - r35348 b35349 b35350 b35351 b35352 b35353 g9 d35327 d35343 d35205
        omega
      have d35354 : (x (-4) 3).toNat = 1 := by
        have r35355 := hand1 (x (-4) 3) (x (-4) 14)
        have b35356 := hb (x (-4) 3)
        have b35357 := hb (x (-4) 3 && x (-4) 14)
        clear * - r35355 b35356 b35357 d35347
        omega
      have d35358 : (x (-1) 12).toNat = 0 := by
        have r35359 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35360 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e35361 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b35362 := hb (x (-4) 3)
        have b35363 := hb (x (-3) 2)
        have b35364 := hb (x (-2) 13)
        have b35365 := hb (x (-1) 12)
        clear * - r35359 e35360 e35361 b35362 b35363 b35364 b35365 d35354
        omega
      have d35366 : (x (-2) 13).toNat = 0 := by
        have r35367 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35368 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e35369 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b35370 := hb (x (-4) 3)
        have b35371 := hb (x (-3) 2)
        have b35372 := hb (x (-2) 13)
        have b35373 := hb (x (-1) 12)
        clear * - r35367 e35368 e35369 b35370 b35371 b35372 b35373 d35358 d35354
        omega
      have d35374 : (x (-3) 2).toNat = 0 := by
        have r35375 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35376 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e35377 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b35378 := hb (x (-4) 3)
        have b35379 := hb (x (-3) 2)
        have b35380 := hb (x (-2) 13)
        have b35381 := hb (x (-1) 12)
        clear * - r35375 e35376 e35377 b35378 b35379 b35380 b35381 d35358 d35366 d35354
        omega
      have d35382 : (x (-3) 10).toNat = 0 := by
        have r35383 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
        have b35384 := hb (x (-3) 2)
        have b35385 := hb (x (-3) 10)
        clear * - r35383 b35384 b35385 d35374
        omega
      have d35386 : (x (-3) 10 && x (-3) 13).toNat = 0 := by
        have r35387 := hand1 (x (-3) 10) (x (-3) 13)
        have b35388 := hb (x (-3) 10)
        have b35389 := hb (x (-3) 10 && x (-3) 13)
        clear * - r35387 b35388 b35389 d35382
        omega
      have d35390 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
        have r35391 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35392 := hb (x (-3) 2)
        have b35393 := hb (x (-1) 13)
        have b35394 := hb (x (-2) 1 && x (-2) 14)
        clear * - r35391 b35392 b35393 b35394 g10 d35374
        omega
      have d35395 : (x (-2) 14).toNat = 1 := by
        have r35396 := hand2 (x (-2) 1) (x (-2) 14)
        have b35397 := hb (x (-2) 14)
        have b35398 := hb (x (-2) 1 && x (-2) 14)
        clear * - r35396 b35397 b35398 d35390
        omega
      have d35399 : (x (-3) 1).toNat = 0 := by
        have r35400 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35401 := hb (x (-3) 1)
        have b35402 := hb (x (-2) 14)
        clear * - r35400 b35401 b35402 d35395
        omega
      have d35403 : (x (-3) 1 && x (-3) 12).toNat = 0 := by
        have r35404 := hand1 (x (-3) 1) (x (-3) 12)
        have b35405 := hb (x (-3) 1)
        have b35406 := hb (x (-3) 1 && x (-3) 12)
        clear * - r35404 b35405 b35406 d35399
        omega
      have d35407 : (x (-5) 3).toNat = 0 := by
        have r35408 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35409 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e35410 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have b35411 := hb (x (-5) 3)
        have b35412 := hb (x (-4) 2)
        have b35413 := hb (x (-3) 13)
        have b35414 := hb (x (-2) 12)
        clear * - r35408 e35409 e35410 b35411 b35412 b35413 b35414 d35319 d35335 d35311
        omega
      have d35415 : (x (-5) 3 && x (-5) 14).toNat = 0 := by
        have r35416 := hand1 (x (-5) 3) (x (-5) 14)
        have b35417 := hb (x (-5) 3)
        have b35418 := hb (x (-5) 3 && x (-5) 14)
        clear * - r35416 b35417 b35418 d35407
        omega
      have d35419 : (x (-4) 2 && x (-4) 13).toNat = 1 := by
        have r35420 : 1 ≤ (x (-2) 11).toNat + (x (-3) 1 && x (-3) 12).toNat + (x (-4) 2 && x (-4) 13).toNat + (x (-5) 3 && x (-5) 14).toNat + (x (-6) 4).toNat := by have q := hcov11 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35421 := hb (x (-6) 4)
        have b35422 := hb (x (-2) 11)
        have b35423 := hb (x (-3) 1 && x (-3) 12)
        have b35424 := hb (x (-4) 2 && x (-4) 13)
        have b35425 := hb (x (-5) 3 && x (-5) 14)
        clear * - r35420 b35421 b35422 b35423 b35424 b35425 g4 d35403 d35415 d35250
        omega
      have d35426 : (x (-4) 13).toNat = 1 := by
        have r35427 := hand2 (x (-4) 2) (x (-4) 13)
        have b35428 := hb (x (-4) 13)
        have b35429 := hb (x (-4) 2 && x (-4) 13)
        clear * - r35427 b35428 b35429 d35419
        omega
      have d35430 : (x (-3) 12).toNat = 0 := by
        have r35431 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35432 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
        have e35433 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
        have b35434 := hb (x (-6) 3)
        have b35435 := hb (x (-5) 2)
        have b35436 := hb (x (-4) 13)
        have b35437 := hb (x (-3) 12)
        clear * - r35431 e35432 e35433 b35434 b35435 b35436 b35437 d35426
        omega
      have d35438 : (x (-6) 1 && x (-6) 14).toNat = 1 := by
        have r35439 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35440 := hb (x (-7) 2)
        have b35441 := hb (x (-5) 13)
        have b35442 := hb (x (-6) 1 && x (-6) 14)
        clear * - r35439 b35440 b35441 b35442 d35291 d35141
        omega
      have d35443 : (x (-6) 14).toNat = 1 := by
        have r35444 := hand2 (x (-6) 1) (x (-6) 14)
        have b35445 := hb (x (-6) 14)
        have b35446 := hb (x (-6) 1 && x (-6) 14)
        clear * - r35444 b35445 b35446 d35438
        omega
      have d35447 : (x (-6) 1).toNat = 1 := by
        have r35448 := hand1 (x (-6) 1) (x (-6) 14)
        have b35449 := hb (x (-6) 1)
        have b35450 := hb (x (-6) 1 && x (-6) 14)
        clear * - r35448 b35449 b35450 d35438
        omega
      have d35451 : (x (-5) 14).toNat = 0 := by
        have r35452 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35453 := hb (x (-6) 1)
        have b35454 := hb (x (-5) 14)
        clear * - r35452 b35453 b35454 d35447
        omega
      have d35455 : (x 7 1).toNat = 0 := by
        have r35456 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35457 := hb (x (-6) 14)
        have b35458 := hb (x (-5) 13)
        have b35459 := hb (x (-4) 12)
        have b35460 := hb (x (-3) 11)
        have b35461 := hb (x (-2) 10)
        have b35462 := hb (x (-1) 9)
        have b35463 := hb (x 0 8)
        have b35464 := hb (x 1 7)
        have b35465 := hb (x 2 6)
        have b35466 := hb (x 3 5)
        have b35467 := hb (x 4 4)
        have b35468 := hb (x 5 3)
        have b35469 := hb (x 6 2)
        have b35470 := hb (x 7 1)
        clear * - r35456 b35457 b35458 b35459 b35460 b35461 b35462 b35463 b35464 b35465 b35466 b35467 b35468 b35469 b35470 g39 g29 f34627 g7 g3 g1 d35287 d35291 d35443
        omega
      have d35471 : (x 7 1 && x 7 14).toNat = 0 := by
        have r35472 := hand1 (x 7 1) (x 7 14)
        have b35473 := hb (x 7 1)
        have b35474 := hb (x 7 1 && x 7 14)
        clear * - r35472 b35473 b35474 d35455
        omega
      have d35475 : (x 7 13).toNat = 0 := by
        have r35476 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
        have b35477 := hb (x 7 1)
        have b35478 := hb (x 7 13)
        clear * - r35476 b35477 b35478 d35455
        omega
      have d35479 : (x 7 5).toNat = 0 := by
        have r35480 : (x 7 5).toNat ≤ (x 7 13).toNat := himp _ _ (hp5 7)
        have b35481 := hb (x 7 5)
        have b35482 := hb (x 7 13)
        clear * - r35480 b35481 b35482 d35475
        omega
      have d35483 : (x 7 9).toNat = 0 := by
        have r35484 : (x 7 9).toNat ≤ (x 7 1).toNat := himp _ _ (hp9 7)
        have b35485 := hb (x 7 1)
        have b35486 := hb (x 7 9)
        clear * - r35484 b35485 b35486 d35455
        omega
      have d35487 : (x 7 3 && x 7 9).toNat = 0 := by
        have r35488 := hand2 (x 7 3) (x 7 9)
        have b35489 := hb (x 7 9)
        have b35490 := hb (x 7 3 && x 7 9)
        clear * - r35488 b35489 b35490 d35483
        omega
      have d35491 : (x 6 2).toNat = 0 := by
        have r35492 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35493 := hb (x (-6) 14)
        have b35494 := hb (x (-5) 13)
        have b35495 := hb (x (-4) 12)
        have b35496 := hb (x (-3) 11)
        have b35497 := hb (x (-2) 10)
        have b35498 := hb (x (-1) 9)
        have b35499 := hb (x 0 8)
        have b35500 := hb (x 1 7)
        have b35501 := hb (x 2 6)
        have b35502 := hb (x 3 5)
        have b35503 := hb (x 4 4)
        have b35504 := hb (x 5 3)
        have b35505 := hb (x 6 2)
        have b35506 := hb (x 7 1)
        clear * - r35492 b35493 b35494 b35495 b35496 b35497 b35498 b35499 b35500 b35501 b35502 b35503 b35504 b35505 b35506 d35455 g39 g29 f34627 g7 g3 g1 d35287 d35291 d35443
        omega
      have d35507 : (x 6 10).toNat = 0 := by
        have r35508 : (x 6 10).toNat ≤ (x 6 2).toNat := himp _ _ (hp10 6)
        have b35509 := hb (x 6 2)
        have b35510 := hb (x 6 10)
        clear * - r35508 b35509 b35510 d35491
        omega
      have d35511 : (x 6 1 && x 6 10).toNat = 0 := by
        have r35512 := hand2 (x 6 1) (x 6 10)
        have b35513 := hb (x 6 10)
        have b35514 := hb (x 6 1 && x 6 10)
        clear * - r35512 b35513 b35514 d35507
        omega
      have d35515 : (x 5 2 && x 5 11).toNat = 1 := by
        have r35516 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35517 := hb (x 1 6)
        have b35518 := hb (x 7 9)
        have b35519 := hb (x 6 1 && x 6 10)
        have b35520 := hb (x 5 2 && x 5 11)
        have b35521 := hb (x 4 3 && x 4 12)
        have b35522 := hb (x 3 4 && x 3 13)
        have b35523 := hb (x 2 5 && x 2 14)
        clear * - r35516 b35517 b35518 b35519 b35520 b35521 b35522 b35523 d35483 d35511 g104 g105 g106 g21
        omega
      have d35524 : (x 5 11).toNat = 1 := by
        have r35525 := hand2 (x 5 2) (x 5 11)
        have b35526 := hb (x 5 11)
        have b35527 := hb (x 5 2 && x 5 11)
        clear * - r35525 b35526 b35527 d35515
        omega
      have d35528 : (x 5 2).toNat = 1 := by
        have r35529 := hand1 (x 5 2) (x 5 11)
        have b35530 := hb (x 5 2)
        have b35531 := hb (x 5 2 && x 5 11)
        clear * - r35529 b35530 b35531 d35515
        omega
      have d35532 : (x 5 14).toNat = 1 := by
        have r35533 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
        have b35534 := hb (x 5 2)
        have b35535 := hb (x 5 14)
        clear * - r35533 b35534 b35535 d35528
        omega
      have d35536 : (x 4 1).toNat = 0 := by
        have r35537 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35538 := hb (x 4 1)
        have b35539 := hb (x 5 14)
        clear * - r35537 b35538 b35539 d35532
        omega
      have d35540 : (x 4 1 && x 4 11).toNat = 0 := by
        have r35541 := hand1 (x 4 1) (x 4 11)
        have b35542 := hb (x 4 1)
        have b35543 := hb (x 4 1 && x 4 11)
        clear * - r35541 b35542 b35543 d35536
        omega
      have d35544 : (x 5 10).toNat = 1 := by
        have r35545 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35546 := hb (x 0 5)
        have b35547 := hb (x 5 10)
        have b35548 := hb (x 4 1 && x 4 11)
        have b35549 := hb (x 3 2 && x 3 12)
        have b35550 := hb (x 2 3 && x 2 13)
        have b35551 := hb (x 1 4 && x 1 14)
        clear * - r35545 b35546 b35547 b35548 b35549 b35550 b35551 d35540 g111 g112 g113 g13
        omega
      have d35552 : (x 7 8).toNat = 0 := by
        have r35553 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35554 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e35555 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e35556 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e35557 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e35558 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e35559 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b35560 := hb (x 0 7)
        have b35561 := hb (x 1 6)
        have b35562 := hb (x 2 5)
        have b35563 := hb (x 3 4)
        have b35564 := hb (x 4 11)
        have b35565 := hb (x 5 10)
        have b35566 := hb (x 6 9)
        have b35567 := hb (x 7 8)
        clear * - r35553 e35554 e35555 e35556 e35557 e35558 e35559 b35560 b35561 b35562 b35563 b35564 b35565 b35566 b35567 d35544 g34 g28 g21 g14
        omega
      have d35568 : (x 6 9).toNat = 0 := by
        have r35569 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35570 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e35571 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e35572 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e35573 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e35574 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e35575 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b35576 := hb (x 0 7)
        have b35577 := hb (x 1 6)
        have b35578 := hb (x 2 5)
        have b35579 := hb (x 3 4)
        have b35580 := hb (x 4 11)
        have b35581 := hb (x 5 10)
        have b35582 := hb (x 6 9)
        have b35583 := hb (x 7 8)
        clear * - r35569 e35570 e35571 e35572 e35573 e35574 e35575 b35576 b35577 b35578 b35579 b35580 b35581 b35582 b35583 d35552 d35544 g34 g28 g21 g14
        omega
      have d35584 : (x 5 1 && x 5 10).toNat = 1 := by
        have r35585 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35586 := hb (x 0 6)
        have b35587 := hb (x 6 9)
        have b35588 := hb (x 5 1 && x 5 10)
        have b35589 := hb (x 4 2 && x 4 11)
        have b35590 := hb (x 3 3 && x 3 12)
        have b35591 := hb (x 2 4 && x 2 13)
        have b35592 := hb (x 1 5 && x 1 14)
        clear * - r35585 b35586 b35587 b35588 b35589 b35590 b35591 b35592 d35568 g100 g101 g102 g103 f34482
        omega
      have d35593 : (x 5 1).toNat = 1 := by
        have r35594 := hand1 (x 5 1) (x 5 10)
        have b35595 := hb (x 5 1)
        have b35596 := hb (x 5 1 && x 5 10)
        clear * - r35594 b35595 b35596 d35584
        omega
      have d35597 : (x 6 14).toNat = 0 := by
        have r35598 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35599 := hb (x 5 1)
        have b35600 := hb (x 6 14)
        clear * - r35598 b35599 b35600 d35593
        omega
      have d35601 : (x 6 6).toNat = 0 := by
        have r35602 : (x 6 6).toNat ≤ (x 6 14).toNat := himp _ _ (hp6 6)
        have b35603 := hb (x 6 6)
        have b35604 := hb (x 6 14)
        clear * - r35602 b35603 b35604 d35597
        omega
      have d35605 : (x 6 1 && x 6 6).toNat = 0 := by
        have r35606 := hand2 (x 6 1) (x 6 6)
        have b35607 := hb (x 6 6)
        have b35608 := hb (x 6 1 && x 6 6)
        clear * - r35606 b35607 b35608 d35601
        omega
      have d35609 : (x 4 11).toNat = 0 := by
        have r35610 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35611 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e35612 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e35613 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e35614 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e35615 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e35616 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b35617 := hb (x 0 7)
        have b35618 := hb (x 1 6)
        have b35619 := hb (x 2 5)
        have b35620 := hb (x 3 4)
        have b35621 := hb (x 4 11)
        have b35622 := hb (x 5 10)
        have b35623 := hb (x 6 9)
        have b35624 := hb (x 7 8)
        clear * - r35610 e35611 e35612 e35613 e35614 e35615 e35616 b35617 b35618 b35619 b35620 b35621 b35622 b35623 b35624 d35552 d35568 d35544 g34 g28 g21 g14
        omega
      have d35625 : (x 4 13).toNat = 0 := by
        have r35626 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
        have b35627 := hb (x 4 1)
        have b35628 := hb (x 4 13)
        clear * - r35626 b35627 b35628 d35536
        omega
      have d35629 : (x 4 3 && x 4 13).toNat = 0 := by
        have r35630 := hand2 (x 4 3) (x 4 13)
        have b35631 := hb (x 4 13)
        have b35632 := hb (x 4 3 && x 4 13)
        clear * - r35630 b35631 b35632 d35625
        omega
      have d35633 : (x 4 5).toNat = 0 := by
        have r35634 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
        have b35635 := hb (x 4 5)
        have b35636 := hb (x 4 13)
        clear * - r35634 b35635 b35636 d35625
        omega
      have d35637 : (x 3 1 && x 3 14).toNat = 1 := by
        have r35638 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35639 := hb (x 2 2)
        have b35640 := hb (x 4 13)
        have b35641 := hb (x 3 1 && x 3 14)
        clear * - r35638 b35639 b35640 b35641 d35625 g26
        omega
      have d35642 : (x 3 14).toNat = 1 := by
        have r35643 := hand2 (x 3 1) (x 3 14)
        have b35644 := hb (x 3 14)
        have b35645 := hb (x 3 1 && x 3 14)
        clear * - r35643 b35644 b35645 d35637
        omega
      have d35646 : (x 7 12).toNat = 0 := by
        have r35647 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35648 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
        have e35649 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
        have b35650 := hb (x 4 3)
        have b35651 := hb (x 5 2)
        have b35652 := hb (x 6 13)
        have b35653 := hb (x 7 12)
        clear * - r35647 e35648 e35649 b35650 b35651 b35652 b35653 d35528
        omega
      have d35654 : (x 7 2 && x 7 12).toNat = 0 := by
        have r35655 := hand2 (x 7 2) (x 7 12)
        have b35656 := hb (x 7 12)
        have b35657 := hb (x 7 2 && x 7 12)
        clear * - r35655 b35656 b35657 d35646
        omega
      have d35658 : (x 6 13).toNat = 0 := by
        have r35659 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35660 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
        have e35661 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
        have b35662 := hb (x 4 3)
        have b35663 := hb (x 5 2)
        have b35664 := hb (x 6 13)
        have b35665 := hb (x 7 12)
        clear * - r35659 e35660 e35661 b35662 b35663 b35664 b35665 d35646 d35528
        omega
      have d35666 : (x 6 3 && x 6 13).toNat = 0 := by
        have r35667 := hand2 (x 6 3) (x 6 13)
        have b35668 := hb (x 6 13)
        have b35669 := hb (x 6 3 && x 6 13)
        clear * - r35667 b35668 b35669 d35658
        omega
      have d35670 : (x 6 4 && x 6 10).toNat = 0 := by
        have r35671 := hand2 (x 6 4) (x 6 10)
        have b35672 := hb (x 6 10)
        have b35673 := hb (x 6 4 && x 6 10)
        clear * - r35671 b35672 b35673 d35507
        omega
      have d35674 : (x 8 8).toNat = 0 := by
        have r35675 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35676 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e35677 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e35678 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e35679 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e35680 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e35681 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b35682 := hb (x 1 7)
        have b35683 := hb (x 2 6)
        have b35684 := hb (x 3 5)
        have b35685 := hb (x 4 4)
        have b35686 := hb (x 5 11)
        have b35687 := hb (x 6 10)
        have b35688 := hb (x 7 9)
        have b35689 := hb (x 8 8)
        clear * - r35675 e35676 e35677 e35678 e35679 e35680 e35681 b35682 b35683 b35684 b35685 b35686 b35687 b35688 b35689 d35483 d35507 d35524 g39 g29
        omega
      have d35690 : (x 8 2 && x 8 8).toNat = 0 := by
        have r35691 := hand2 (x 8 2) (x 8 8)
        have b35692 := hb (x 8 8)
        have b35693 := hb (x 8 2 && x 8 8)
        clear * - r35691 b35692 b35693 d35674
        omega
      have d35694 : (x 8 13).toNat = 1 := by
        have r35695 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35696 := hb (x 6 2)
        have b35697 := hb (x 8 13)
        have b35698 := hb (x 7 1 && x 7 14)
        clear * - r35695 b35696 b35697 b35698 d35471 d35491
        omega
      have d35699 : (x 8 1).toNat = 1 := by
        have r35700 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
        have b35701 := hb (x 8 1)
        have b35702 := hb (x 8 13)
        clear * - r35700 b35701 b35702 d35694
        omega
      have d35703 : (x 9 14).toNat = 0 := by
        have r35704 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35705 := hb (x 8 1)
        have b35706 := hb (x 9 14)
        clear * - r35704 b35705 b35706 d35699
        omega
      have d35707 : (x 9 1 && x 9 14).toNat = 0 := by
        have r35708 := hand2 (x 9 1) (x 9 14)
        have b35709 := hb (x 9 14)
        have b35710 := hb (x 9 1 && x 9 14)
        clear * - r35708 b35709 b35710 d35703
        omega
      have d35711 : (x 9 3 && x 9 14).toNat = 0 := by
        have r35712 := hand2 (x 9 3) (x 9 14)
        have b35713 := hb (x 9 14)
        have b35714 := hb (x 9 3 && x 9 14)
        clear * - r35712 b35713 b35714 d35703
        omega
      have d35715 : (x 9 7 && x 9 14).toNat = 0 := by
        have r35716 := hand2 (x 9 7) (x 9 14)
        have b35717 := hb (x 9 14)
        have b35718 := hb (x 9 7 && x 9 14)
        clear * - r35716 b35717 b35718 d35703
        omega
      have d35719 : (x 9 6).toNat = 0 := by
        have r35720 : (x 9 6).toNat ≤ (x 9 14).toNat := himp _ _ (hp6 9)
        have b35721 := hb (x 9 6)
        have b35722 := hb (x 9 14)
        clear * - r35720 b35721 b35722 d35703
        omega
      have d35723 : (x 9 2).toNat = 0 := by
        have r35724 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
        have b35725 := hb (x 9 2)
        have b35726 := hb (x 9 14)
        clear * - r35724 b35725 b35726 d35703
        omega
      have d35727 : (x 9 10).toNat = 0 := by
        have r35728 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
        have b35729 := hb (x 9 2)
        have b35730 := hb (x 9 10)
        clear * - r35728 b35729 b35730 d35723
        omega
      have d35731 : (x 7 2).toNat = 0 := by
        have r35732 : (x 8 1).toNat + (x 7 2).toNat + (x 6 3).toNat + (x 5 4).toNat + (x 4 5).toNat + (x 3 6).toNat + (x 2 7).toNat + (x 1 8).toNat + (x 0 9).toNat + (x (-1) 10).toNat + (x (-2) 11).toNat + (x (-3) 12).toNat + (x (-4) 13).toNat + (x (-5) 14).toNat = 3 := by have q := hcount 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35733 := hb (x (-5) 14)
        have b35734 := hb (x (-4) 13)
        have b35735 := hb (x (-3) 12)
        have b35736 := hb (x (-2) 11)
        have b35737 := hb (x (-1) 10)
        have b35738 := hb (x 0 9)
        have b35739 := hb (x 1 8)
        have b35740 := hb (x 2 7)
        have b35741 := hb (x 3 6)
        have b35742 := hb (x 4 5)
        have b35743 := hb (x 5 4)
        have b35744 := hb (x 6 3)
        have b35745 := hb (x 7 2)
        have b35746 := hb (x 8 1)
        clear * - r35732 b35733 b35734 b35735 b35736 b35737 b35738 b35739 b35740 b35741 b35742 b35743 b35744 b35745 b35746 d35699 d35633 d34841 d34832 g8 g4 d35430 d35426 d35451
        omega
      have d35747 : (x 7 10).toNat = 0 := by
        have r35748 : (x 7 10).toNat ≤ (x 7 2).toNat := himp _ _ (hp10 7)
        have b35749 := hb (x 7 2)
        have b35750 := hb (x 7 10)
        clear * - r35748 b35749 b35750 d35731
        omega
      have d35751 : (x 7 3 && x 7 10).toNat = 0 := by
        have r35752 := hand2 (x 7 3) (x 7 10)
        have b35753 := hb (x 7 10)
        have b35754 := hb (x 7 3 && x 7 10)
        clear * - r35752 b35753 b35754 d35747
        omega
      have d35755 : (x 6 3).toNat = 0 := by
        have r35756 : (x 8 1).toNat + (x 7 2).toNat + (x 6 3).toNat + (x 5 4).toNat + (x 4 5).toNat + (x 3 6).toNat + (x 2 7).toNat + (x 1 8).toNat + (x 0 9).toNat + (x (-1) 10).toNat + (x (-2) 11).toNat + (x (-3) 12).toNat + (x (-4) 13).toNat + (x (-5) 14).toNat = 3 := by have q := hcount 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35757 := hb (x (-5) 14)
        have b35758 := hb (x (-4) 13)
        have b35759 := hb (x (-3) 12)
        have b35760 := hb (x (-2) 11)
        have b35761 := hb (x (-1) 10)
        have b35762 := hb (x 0 9)
        have b35763 := hb (x 1 8)
        have b35764 := hb (x 2 7)
        have b35765 := hb (x 3 6)
        have b35766 := hb (x 4 5)
        have b35767 := hb (x 5 4)
        have b35768 := hb (x 6 3)
        have b35769 := hb (x 7 2)
        have b35770 := hb (x 8 1)
        clear * - r35756 b35757 b35758 b35759 b35760 b35761 b35762 b35763 b35764 b35765 b35766 b35767 b35768 b35769 b35770 d35699 d35731 d35633 d34841 d34832 g8 g4 d35430 d35426 d35451
        omega
      have d35771 : (x 6 11).toNat = 0 := by
        have r35772 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
        have b35773 := hb (x 6 3)
        have b35774 := hb (x 6 11)
        clear * - r35772 b35773 b35774 d35755
        omega
      have d35775 : (x 6 1 && x 6 11).toNat = 0 := by
        have r35776 := hand2 (x 6 1) (x 6 11)
        have b35777 := hb (x 6 11)
        have b35778 := hb (x 6 1 && x 6 11)
        clear * - r35776 b35777 b35778 d35771
        omega
      have d35779 : (x 5 2 && x 5 12).toNat = 1 := by
        have r35780 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35781 := hb (x 2 5)
        have b35782 := hb (x 7 10)
        have b35783 := hb (x 6 1 && x 6 11)
        have b35784 := hb (x 5 2 && x 5 12)
        have b35785 := hb (x 4 3 && x 4 13)
        have b35786 := hb (x 3 4 && x 3 14)
        clear * - r35780 b35781 b35782 b35783 b35784 b35785 b35786 d35747 d35775 d35629 g114 g28
        omega
      have d35787 : (x 5 12).toNat = 1 := by
        have r35788 := hand2 (x 5 2) (x 5 12)
        have b35789 := hb (x 5 12)
        have b35790 := hb (x 5 2 && x 5 12)
        clear * - r35788 b35789 b35790 d35779
        omega
      have d35791 : (x 3 2).toNat = 0 := by
        have r35792 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35793 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e35794 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b35795 := hb (x 2 3)
        have b35796 := hb (x 3 2)
        have b35797 := hb (x 4 13)
        have b35798 := hb (x 5 12)
        clear * - r35792 e35793 e35794 b35795 b35796 b35797 b35798 d35787 d35625
        omega
      have d35799 : (x 5 13).toNat = 1 := by
        have r35800 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35801 := hb (x 3 2)
        have b35802 := hb (x 5 13)
        have b35803 := hb (x 4 1 && x 4 14)
        clear * - r35800 b35801 b35802 b35803 g118 d35791
        omega
      have d35804 : (x 6 12).toNat = 0 := by
        have r35805 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35806 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
        have e35807 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
        have b35808 := hb (x 3 3)
        have b35809 := hb (x 4 2)
        have b35810 := hb (x 5 13)
        have b35811 := hb (x 6 12)
        clear * - r35805 e35806 e35807 b35808 b35809 b35810 b35811 d35799 g38
        omega
      have d35812 : (x 6 4).toNat = 0 := by
        have r35813 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
        have b35814 := hb (x 6 4)
        have b35815 := hb (x 6 12)
        clear * - r35813 b35814 b35815 d35804
        omega
      have d35816 : (x 6 4 && x 6 11).toNat = 0 := by
        have r35817 := hand1 (x 6 4) (x 6 11)
        have b35818 := hb (x 6 4)
        have b35819 := hb (x 6 4 && x 6 11)
        clear * - r35817 b35818 b35819 d35812
        omega
      have d35820 : (x 6 1 && x 6 4).toNat = 0 := by
        have r35821 := hand2 (x 6 1) (x 6 4)
        have b35822 := hb (x 6 4)
        have b35823 := hb (x 6 1 && x 6 4)
        clear * - r35821 b35822 b35823 d35812
        omega
      have d35824 : (x 5 4).toNat = 0 := by
        have r35825 : (x 8 1).toNat + (x 7 2).toNat + (x 6 3).toNat + (x 5 4).toNat + (x 4 5).toNat + (x 3 6).toNat + (x 2 7).toNat + (x 1 8).toNat + (x 0 9).toNat + (x (-1) 10).toNat + (x (-2) 11).toNat + (x (-3) 12).toNat + (x (-4) 13).toNat + (x (-5) 14).toNat = 3 := by have q := hcount 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35826 := hb (x (-5) 14)
        have b35827 := hb (x (-4) 13)
        have b35828 := hb (x (-3) 12)
        have b35829 := hb (x (-2) 11)
        have b35830 := hb (x (-1) 10)
        have b35831 := hb (x 0 9)
        have b35832 := hb (x 1 8)
        have b35833 := hb (x 2 7)
        have b35834 := hb (x 3 6)
        have b35835 := hb (x 4 5)
        have b35836 := hb (x 5 4)
        have b35837 := hb (x 6 3)
        have b35838 := hb (x 7 2)
        have b35839 := hb (x 8 1)
        clear * - r35825 b35826 b35827 b35828 b35829 b35830 b35831 b35832 b35833 b35834 b35835 b35836 b35837 b35838 b35839 d35699 d35731 d35755 d35633 d34841 d34832 g8 g4 d35430 d35426 d35451
        omega
      have d35840 : (x 5 4 && x 5 14).toNat = 0 := by
        have r35841 := hand1 (x 5 4) (x 5 14)
        have b35842 := hb (x 5 4)
        have b35843 := hb (x 5 4 && x 5 14)
        clear * - r35841 b35842 b35843 d35824
        omega
      have d35844 : (x 8 1 && x 8 11).toNat = 1 := by
        have r35845 : 1 ≤ (x 9 10).toNat + (x 8 1 && x 8 11).toNat + (x 7 2 && x 7 12).toNat + (x 6 3 && x 6 13).toNat + (x 5 4 && x 5 14).toNat + (x 4 5).toNat := by have q := hcov10 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35846 := hb (x 4 5)
        have b35847 := hb (x 9 10)
        have b35848 := hb (x 8 1 && x 8 11)
        have b35849 := hb (x 7 2 && x 7 12)
        have b35850 := hb (x 6 3 && x 6 13)
        have b35851 := hb (x 5 4 && x 5 14)
        clear * - r35845 b35846 b35847 b35848 b35849 b35850 b35851 d35727 d35654 d35666 d35840 d35633
        omega
      have d35852 : (x 8 11).toNat = 1 := by
        have r35853 := hand2 (x 8 1) (x 8 11)
        have b35854 := hb (x 8 11)
        have b35855 := hb (x 8 1 && x 8 11)
        clear * - r35853 b35854 b35855 d35844
        omega
      have d35856 : (x 8 3).toNat = 1 := by
        have r35857 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
        have b35858 := hb (x 8 3)
        have b35859 := hb (x 8 11)
        clear * - r35857 b35858 b35859 d35852
        omega
      have d35860 : (x 11 12).toNat = 0 := by
        have r35861 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35862 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e35863 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b35864 := hb (x 8 3)
        have b35865 := hb (x 9 2)
        have b35866 := hb (x 10 13)
        have b35867 := hb (x 11 12)
        clear * - r35861 e35862 e35863 b35864 b35865 b35866 b35867 d35723 d35856
        omega
      have d35868 : (x 11 1 && x 11 12).toNat = 0 := by
        have r35869 := hand2 (x 11 1) (x 11 12)
        have b35870 := hb (x 11 12)
        have b35871 := hb (x 11 1 && x 11 12)
        clear * - r35869 b35870 b35871 d35860
        omega
      have d35872 : (x 11 5 && x 11 12).toNat = 0 := by
        have r35873 := hand2 (x 11 5) (x 11 12)
        have b35874 := hb (x 11 12)
        have b35875 := hb (x 11 5 && x 11 12)
        clear * - r35873 b35874 b35875 d35860
        omega
      have d35876 : (x 11 4).toNat = 0 := by
        have r35877 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
        have b35878 := hb (x 11 4)
        have b35879 := hb (x 11 12)
        clear * - r35877 b35878 b35879 d35860
        omega
      have d35880 : (x 10 13).toNat = 0 := by
        have r35881 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35882 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e35883 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b35884 := hb (x 8 3)
        have b35885 := hb (x 9 2)
        have b35886 := hb (x 10 13)
        have b35887 := hb (x 11 12)
        clear * - r35881 e35882 e35883 b35884 b35885 b35886 b35887 d35860 d35723 d35856
        omega
      have d35888 : (x 10 2 && x 10 13).toNat = 0 := by
        have r35889 := hand2 (x 10 2) (x 10 13)
        have b35890 := hb (x 10 13)
        have b35891 := hb (x 10 2 && x 10 13)
        clear * - r35889 b35890 b35891 d35880
        omega
      have d35892 : (x 10 6 && x 10 13).toNat = 0 := by
        have r35893 := hand2 (x 10 6) (x 10 13)
        have b35894 := hb (x 10 13)
        have b35895 := hb (x 10 6 && x 10 13)
        clear * - r35893 b35894 b35895 d35880
        omega
      have d35896 : (x 10 5).toNat = 0 := by
        have r35897 : (x 10 5).toNat ≤ (x 10 13).toNat := himp _ _ (hp5 10)
        have b35898 := hb (x 10 5)
        have b35899 := hb (x 10 13)
        clear * - r35897 b35898 b35899 d35880
        omega
      have d35900 : (x 8 2).toNat = 1 := by
        have r35901 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35902 := hb (x 8 2)
        have b35903 := hb (x 10 13)
        have b35904 := hb (x 9 1 && x 9 14)
        clear * - r35901 b35902 b35903 b35904 d35880 d35707
        omega
      have d35905 : (x 10 12).toNat = 0 := by
        have r35906 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35907 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
        have e35908 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
        have b35909 := hb (x 7 3)
        have b35910 := hb (x 8 2)
        have b35911 := hb (x 9 13)
        have b35912 := hb (x 10 12)
        clear * - r35906 e35907 e35908 b35909 b35910 b35911 b35912 d35900
        omega
      have d35913 : (x 10 2 && x 10 12).toNat = 0 := by
        have r35914 := hand2 (x 10 2) (x 10 12)
        have b35915 := hb (x 10 12)
        have b35916 := hb (x 10 2 && x 10 12)
        clear * - r35914 b35915 b35916 d35905
        omega
      have d35917 : (x 9 13).toNat = 0 := by
        have r35918 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35919 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
        have e35920 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
        have b35921 := hb (x 7 3)
        have b35922 := hb (x 8 2)
        have b35923 := hb (x 9 13)
        have b35924 := hb (x 10 12)
        clear * - r35918 e35919 e35920 b35921 b35922 b35923 b35924 d35905 d35900
        omega
      have d35925 : (x 9 3 && x 9 13).toNat = 0 := by
        have r35926 := hand2 (x 9 3) (x 9 13)
        have b35927 := hb (x 9 13)
        have b35928 := hb (x 9 3 && x 9 13)
        clear * - r35926 b35927 b35928 d35917
        omega
      have d35929 : (x 7 3).toNat = 0 := by
        have r35930 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35931 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
        have e35932 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
        have b35933 := hb (x 7 3)
        have b35934 := hb (x 8 2)
        have b35935 := hb (x 9 13)
        have b35936 := hb (x 10 12)
        clear * - r35930 e35931 e35932 b35933 b35934 b35935 b35936 d35905 d35917 d35900
        omega
      have d35937 : (x 9 1).toNat = 0 := by
        have r35938 : (x 9 1).toNat + (x 8 2).toNat + (x 7 3).toNat + (x 6 4).toNat + (x 5 5).toNat + (x 4 6).toNat + (x 3 7).toNat + (x 2 8).toNat + (x 1 9).toNat + (x 0 10).toNat + (x (-1) 11).toNat + (x (-2) 12).toNat + (x (-3) 13).toNat + (x (-4) 14).toNat = 3 := by have q := hcount 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35939 := hb (x (-4) 14)
        have b35940 := hb (x (-3) 13)
        have b35941 := hb (x (-2) 12)
        have b35942 := hb (x (-1) 11)
        have b35943 := hb (x 0 10)
        have b35944 := hb (x 1 9)
        have b35945 := hb (x 2 8)
        have b35946 := hb (x 3 7)
        have b35947 := hb (x 4 6)
        have b35948 := hb (x 5 5)
        have b35949 := hb (x 6 4)
        have b35950 := hb (x 7 3)
        have b35951 := hb (x 8 2)
        have b35952 := hb (x 9 1)
        clear * - r35938 b35939 b35940 b35941 b35942 b35943 b35944 b35945 b35946 b35947 b35948 b35949 b35950 b35951 b35952 d35900 d35929 d35812 g40 d34696 d34712 d34688 g9 d35319 d35335 d35315
        omega
      have d35953 : (x 9 1 && x 9 8).toNat = 0 := by
        have r35954 := hand1 (x 9 1) (x 9 8)
        have b35955 := hb (x 9 1)
        have b35956 := hb (x 9 1 && x 9 8)
        clear * - r35954 b35955 b35956 d35937
        omega
      have d35957 : (x 9 1 && x 9 7).toNat = 0 := by
        have r35958 := hand1 (x 9 1) (x 9 7)
        have b35959 := hb (x 9 1)
        have b35960 := hb (x 9 1 && x 9 7)
        clear * - r35958 b35959 b35960 d35937
        omega
      have d35961 : (x 5 5).toNat = 0 := by
        have r35962 : (x 9 1).toNat + (x 8 2).toNat + (x 7 3).toNat + (x 6 4).toNat + (x 5 5).toNat + (x 4 6).toNat + (x 3 7).toNat + (x 2 8).toNat + (x 1 9).toNat + (x 0 10).toNat + (x (-1) 11).toNat + (x (-2) 12).toNat + (x (-3) 13).toNat + (x (-4) 14).toNat = 3 := by have q := hcount 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35963 := hb (x (-4) 14)
        have b35964 := hb (x (-3) 13)
        have b35965 := hb (x (-2) 12)
        have b35966 := hb (x (-1) 11)
        have b35967 := hb (x 0 10)
        have b35968 := hb (x 1 9)
        have b35969 := hb (x 2 8)
        have b35970 := hb (x 3 7)
        have b35971 := hb (x 4 6)
        have b35972 := hb (x 5 5)
        have b35973 := hb (x 6 4)
        have b35974 := hb (x 7 3)
        have b35975 := hb (x 8 2)
        have b35976 := hb (x 9 1)
        clear * - r35962 b35963 b35964 b35965 b35966 b35967 b35968 b35969 b35970 b35971 b35972 b35973 b35974 b35975 b35976 d35937 d35900 d35929 d35812 g40 d34696 d34712 d34688 g9 d35319 d35335 d35315
        omega
      have d35977 : (x 5 5 && x 5 12).toNat = 0 := by
        have r35978 := hand1 (x 5 5) (x 5 12)
        have b35979 := hb (x 5 5)
        have b35980 := hb (x 5 5 && x 5 12)
        clear * - r35978 b35979 b35980 d35961
        omega
      have d35981 : (x 5 5 && x 5 11).toNat = 0 := by
        have r35982 := hand1 (x 5 5) (x 5 11)
        have b35983 := hb (x 5 5)
        have b35984 := hb (x 5 5 && x 5 11)
        clear * - r35982 b35983 b35984 d35961
        omega
      have d35985 : (x 5 2 && x 5 5).toNat = 0 := by
        have r35986 := hand2 (x 5 2) (x 5 5)
        have b35987 := hb (x 5 5)
        have b35988 := hb (x 5 2 && x 5 5)
        clear * - r35986 b35987 b35988 d35961
        omega
      have d35989 : (x (-4) 11 && x (-4) 14).toNat = 1 := by
        have r35990 : 1 ≤ (x 7 3).toNat + (x 6 1 && x 6 4).toNat + (x 5 2 && x 5 5).toNat + (x 4 3 && x 4 6).toNat + (x 3 4 && x 3 7).toNat + (x 2 5 && x 2 8).toNat + (x 1 6 && x 1 9).toNat + (x 0 7 && x 0 10).toNat + (x (-1) 8 && x (-1) 11).toNat + (x (-2) 9 && x (-2) 12).toNat + (x (-3) 10 && x (-3) 13).toNat + (x (-4) 11 && x (-4) 14).toNat + (x (-5) 12).toNat := by have q := hcov3 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35991 := hb (x (-5) 12)
        have b35992 := hb (x 7 3)
        have b35993 := hb (x 6 1 && x 6 4)
        have b35994 := hb (x 5 2 && x 5 5)
        have b35995 := hb (x 4 3 && x 4 6)
        have b35996 := hb (x 3 4 && x 3 7)
        have b35997 := hb (x 2 5 && x 2 8)
        have b35998 := hb (x 1 6 && x 1 9)
        have b35999 := hb (x 0 7 && x 0 10)
        have b36000 := hb (x (-1) 8 && x (-1) 11)
        have b36001 := hb (x (-2) 9 && x (-2) 12)
        have b36002 := hb (x (-3) 10 && x (-3) 13)
        have b36003 := hb (x (-4) 11 && x (-4) 14)
        clear * - r35990 b35991 b35992 b35993 b35994 b35995 b35996 b35997 b35998 b35999 b36000 b36001 b36002 b36003 d35929 d35820 d35985 g44 g45 g46 g47 g48 g49 d35331 d35386 d35197
        omega
      have d36004 : (x (-4) 11).toNat = 1 := by
        have r36005 := hand1 (x (-4) 11) (x (-4) 14)
        have b36006 := hb (x (-4) 11)
        have b36007 := hb (x (-4) 11 && x (-4) 14)
        clear * - r36005 b36006 b36007 d35989
        omega
      have d36008 : (x (-1) 8).toNat = 0 := by
        have r36009 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36010 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e36011 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e36012 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e36013 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e36014 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e36015 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have b36016 := hb (x (-8) 7)
        have b36017 := hb (x (-7) 6)
        have b36018 := hb (x (-6) 5)
        have b36019 := hb (x (-5) 4)
        have b36020 := hb (x (-4) 11)
        have b36021 := hb (x (-3) 10)
        have b36022 := hb (x (-2) 9)
        have b36023 := hb (x (-1) 8)
        clear * - r36009 e36010 e36011 e36012 e36013 e36014 e36015 b36016 b36017 b36018 b36019 b36020 b36021 b36022 b36023 d35382 d36004 d35205 d35270 d35137
        omega
      have d36024 : (x (-2) 9).toNat = 0 := by
        have r36025 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36026 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e36027 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e36028 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e36029 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e36030 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e36031 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have b36032 := hb (x (-8) 7)
        have b36033 := hb (x (-7) 6)
        have b36034 := hb (x (-6) 5)
        have b36035 := hb (x (-5) 4)
        have b36036 := hb (x (-4) 11)
        have b36037 := hb (x (-3) 10)
        have b36038 := hb (x (-2) 9)
        have b36039 := hb (x (-1) 8)
        clear * - r36025 e36026 e36027 e36028 e36029 e36030 e36031 b36032 b36033 b36034 b36035 b36036 b36037 b36038 b36039 d36008 d35382 d36004 d35205 d35270 d35137
        omega
      have d36040 : (x (-2) 9 && x (-2) 14).toNat = 0 := by
        have r36041 := hand1 (x (-2) 9) (x (-2) 14)
        have b36042 := hb (x (-2) 9)
        have b36043 := hb (x (-2) 9 && x (-2) 14)
        clear * - r36041 b36042 b36043 d36024
        omega
      have d36044 : (x 5 2 && x 5 7).toNat = 1 := by
        have r36045 : 1 ≤ (x 7 5).toNat + (x 6 1 && x 6 6).toNat + (x 5 2 && x 5 7).toNat + (x 4 3 && x 4 8).toNat + (x 3 4 && x 3 9).toNat + (x 2 5 && x 2 10).toNat + (x 1 6 && x 1 11).toNat + (x 0 7 && x 0 12).toNat + (x (-1) 8 && x (-1) 13).toNat + (x (-2) 9 && x (-2) 14).toNat + (x (-3) 10).toNat := by have q := hcov5 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b36046 := hb (x (-3) 10)
        have b36047 := hb (x 7 5)
        have b36048 := hb (x 6 1 && x 6 6)
        have b36049 := hb (x 5 2 && x 5 7)
        have b36050 := hb (x 4 3 && x 4 8)
        have b36051 := hb (x 3 4 && x 3 9)
        have b36052 := hb (x 2 5 && x 2 10)
        have b36053 := hb (x 1 6 && x 1 11)
        have b36054 := hb (x 0 7 && x 0 12)
        have b36055 := hb (x (-1) 8 && x (-1) 13)
        have b36056 := hb (x (-2) 9 && x (-2) 14)
        clear * - r36045 b36046 b36047 b36048 b36049 b36050 b36051 b36052 b36053 b36054 b36055 b36056 d35479 d35605 g65 g66 g67 g68 g69 g70 d36040 d35382
        omega
      have d36057 : (x 5 7).toNat = 1 := by
        have r36058 := hand2 (x 5 2) (x 5 7)
        have b36059 := hb (x 5 7)
        have b36060 := hb (x 5 2 && x 5 7)
        clear * - r36058 b36059 b36060 d36044
        omega
      have d36061 : (x 12 8).toNat = 0 := by
        have r36062 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36063 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
        have e36064 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
        have e36065 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
        have e36066 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
        have e36067 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
        have e36068 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
        have b36069 := hb (x 5 7)
        have b36070 := hb (x 6 6)
        have b36071 := hb (x 7 5)
        have b36072 := hb (x 8 4)
        have b36073 := hb (x 9 11)
        have b36074 := hb (x 10 10)
        have b36075 := hb (x 11 9)
        have b36076 := hb (x 12 8)
        clear * - r36062 e36063 e36064 e36065 e36066 e36067 e36068 b36069 b36070 b36071 b36072 b36073 b36074 b36075 b36076 d35479 d35601 d36057
        omega
      have d36077 : (x 11 9).toNat = 0 := by
        have r36078 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36079 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
        have e36080 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
        have e36081 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
        have e36082 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
        have e36083 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
        have e36084 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
        have b36085 := hb (x 5 7)
        have b36086 := hb (x 6 6)
        have b36087 := hb (x 7 5)
        have b36088 := hb (x 8 4)
        have b36089 := hb (x 9 11)
        have b36090 := hb (x 10 10)
        have b36091 := hb (x 11 9)
        have b36092 := hb (x 12 8)
        clear * - r36078 e36079 e36080 e36081 e36082 e36083 e36084 b36085 b36086 b36087 b36088 b36089 b36090 b36091 b36092 d36061 d35479 d35601 d36057
        omega
      have d36093 : (x 10 10).toNat = 0 := by
        have r36094 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36095 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
        have e36096 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
        have e36097 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
        have e36098 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
        have e36099 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
        have e36100 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
        have b36101 := hb (x 5 7)
        have b36102 := hb (x 6 6)
        have b36103 := hb (x 7 5)
        have b36104 := hb (x 8 4)
        have b36105 := hb (x 9 11)
        have b36106 := hb (x 10 10)
        have b36107 := hb (x 11 9)
        have b36108 := hb (x 12 8)
        clear * - r36094 e36095 e36096 e36097 e36098 e36099 e36100 b36101 b36102 b36103 b36104 b36105 b36106 b36107 b36108 d36061 d36077 d35479 d35601 d36057
        omega
      have d36109 : (x 9 11).toNat = 0 := by
        have r36110 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36111 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
        have e36112 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
        have e36113 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
        have e36114 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
        have e36115 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
        have e36116 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
        have b36117 := hb (x 5 7)
        have b36118 := hb (x 6 6)
        have b36119 := hb (x 7 5)
        have b36120 := hb (x 8 4)
        have b36121 := hb (x 9 11)
        have b36122 := hb (x 10 10)
        have b36123 := hb (x 11 9)
        have b36124 := hb (x 12 8)
        clear * - r36110 e36111 e36112 e36113 e36114 e36115 e36116 b36117 b36118 b36119 b36120 b36121 b36122 b36123 b36124 d36061 d36077 d36093 d35479 d35601 d36057
        omega
      have d36125 : (x 8 4).toNat = 0 := by
        have r36126 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36127 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
        have e36128 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
        have e36129 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
        have e36130 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
        have e36131 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
        have e36132 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
        have b36133 := hb (x 5 7)
        have b36134 := hb (x 6 6)
        have b36135 := hb (x 7 5)
        have b36136 := hb (x 8 4)
        have b36137 := hb (x 9 11)
        have b36138 := hb (x 10 10)
        have b36139 := hb (x 11 9)
        have b36140 := hb (x 12 8)
        clear * - r36126 e36127 e36128 e36129 e36130 e36131 e36132 b36133 b36134 b36135 b36136 b36137 b36138 b36139 b36140 d36061 d36077 d36093 d36109 d35479 d35601 d36057
        omega
      have d36141 : (x 8 4 && x 8 14).toNat = 0 := by
        have r36142 := hand1 (x 8 4) (x 8 14)
        have b36143 := hb (x 8 4)
        have b36144 := hb (x 8 4 && x 8 14)
        clear * - r36142 b36143 b36144 d36125
        omega
      have d36145 : (x 12 11).toNat = 1 := by
        have r36146 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b36147 := hb (x 8 4)
        have b36148 := hb (x 12 11)
        have b36149 := hb (x 11 1 && x 11 12)
        have b36150 := hb (x 10 2 && x 10 13)
        have b36151 := hb (x 9 3 && x 9 14)
        clear * - r36146 b36147 b36148 b36149 b36150 b36151 d35868 d35888 d35711 d36125
        omega
      have d36152 : (x 12 3).toNat = 1 := by
        have r36153 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
        have b36154 := hb (x 12 3)
        have b36155 := hb (x 12 11)
        clear * - r36153 b36154 b36155 d36145
        omega
      have d36156 : (x 15 12).toNat = 0 := by
        have r36157 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36158 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e36159 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b36160 := hb (x 12 3)
        have b36161 := hb (x 13 2)
        have b36162 := hb (x 14 13)
        have b36163 := hb (x 15 12)
        clear * - r36157 e36158 e36159 b36160 b36161 b36162 b36163 d36152
        omega
      have d36164 : (x 15 1 && x 15 12).toNat = 0 := by
        have r36165 := hand2 (x 15 1) (x 15 12)
        have b36166 := hb (x 15 12)
        have b36167 := hb (x 15 1 && x 15 12)
        clear * - r36165 b36166 b36167 d36156
        omega
      have d36168 : (x 14 13).toNat = 0 := by
        have r36169 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36170 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e36171 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b36172 := hb (x 12 3)
        have b36173 := hb (x 13 2)
        have b36174 := hb (x 14 13)
        have b36175 := hb (x 15 12)
        clear * - r36169 e36170 e36171 b36172 b36173 b36174 b36175 d36156 d36152
        omega
      have d36176 : (x 14 2 && x 14 13).toNat = 0 := by
        have r36177 := hand2 (x 14 2) (x 14 13)
        have b36178 := hb (x 14 13)
        have b36179 := hb (x 14 2 && x 14 13)
        clear * - r36177 b36178 b36179 d36168
        omega
      have d36180 : (x 13 2).toNat = 0 := by
        have r36181 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36182 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e36183 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b36184 := hb (x 12 3)
        have b36185 := hb (x 13 2)
        have b36186 := hb (x 14 13)
        have b36187 := hb (x 15 12)
        clear * - r36181 e36182 e36183 b36184 b36185 b36186 b36187 d36156 d36168 d36152
        omega
      have d36188 : (x 13 10).toNat = 0 := by
        have r36189 : (x 13 10).toNat ≤ (x 13 2).toNat := himp _ _ (hp10 13)
        have b36190 := hb (x 13 2)
        have b36191 := hb (x 13 10)
        clear * - r36189 b36190 b36191 d36180
        omega
      have d36192 : (x 13 3 && x 13 10).toNat = 0 := by
        have r36193 := hand2 (x 13 3) (x 13 10)
        have b36194 := hb (x 13 10)
        have b36195 := hb (x 13 3 && x 13 10)
        clear * - r36193 b36194 b36195 d36188
        omega
      have d36196 : (x 15 8).toNat = 0 := by
        have r36197 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36198 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
        have e36199 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
        have e36200 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
        have e36201 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
        have e36202 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
        have e36203 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
        have b36204 := hb (x 8 7)
        have b36205 := hb (x 9 6)
        have b36206 := hb (x 10 5)
        have b36207 := hb (x 11 4)
        have b36208 := hb (x 12 11)
        have b36209 := hb (x 13 10)
        have b36210 := hb (x 14 9)
        have b36211 := hb (x 15 8)
        clear * - r36197 e36198 e36199 e36200 e36201 e36202 e36203 b36204 b36205 b36206 b36207 b36208 b36209 b36210 b36211 d36188 d36145 d35876 d35896 d35719
        omega
      have d36212 : (x 15 1 && x 15 8).toNat = 0 := by
        have r36213 := hand2 (x 15 1) (x 15 8)
        have b36214 := hb (x 15 8)
        have b36215 := hb (x 15 1 && x 15 8)
        clear * - r36213 b36214 b36215 d36196
        omega
      have d36216 : (x 14 9).toNat = 0 := by
        have r36217 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36218 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
        have e36219 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
        have e36220 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
        have e36221 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
        have e36222 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
        have e36223 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
        have b36224 := hb (x 8 7)
        have b36225 := hb (x 9 6)
        have b36226 := hb (x 10 5)
        have b36227 := hb (x 11 4)
        have b36228 := hb (x 12 11)
        have b36229 := hb (x 13 10)
        have b36230 := hb (x 14 9)
        have b36231 := hb (x 15 8)
        clear * - r36217 e36218 e36219 e36220 e36221 e36222 e36223 b36224 b36225 b36226 b36227 b36228 b36229 b36230 b36231 d36196 d36188 d36145 d35876 d35896 d35719
        omega
      have d36232 : (x 14 2 && x 14 9).toNat = 0 := by
        have r36233 := hand2 (x 14 2) (x 14 9)
        have b36234 := hb (x 14 9)
        have b36235 := hb (x 14 2 && x 14 9)
        clear * - r36233 b36234 b36235 d36216
        omega
      have d36236 : (x 8 7).toNat = 0 := by
        have r36237 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36238 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
        have e36239 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
        have e36240 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
        have e36241 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
        have e36242 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
        have e36243 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
        have b36244 := hb (x 8 7)
        have b36245 := hb (x 9 6)
        have b36246 := hb (x 10 5)
        have b36247 := hb (x 11 4)
        have b36248 := hb (x 12 11)
        have b36249 := hb (x 13 10)
        have b36250 := hb (x 14 9)
        have b36251 := hb (x 15 8)
        clear * - r36237 e36238 e36239 e36240 e36241 e36242 e36243 b36244 b36245 b36246 b36247 b36248 b36249 b36250 b36251 d36196 d36216 d36188 d36145 d35876 d35896 d35719
        omega
      have d36252 : (x 14 1).toNat = 1 := by
        have r36253 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b36254 := hb (x 1 14)
        have b36255 := hb (x 2 13)
        have b36256 := hb (x 3 12)
        have b36257 := hb (x 4 11)
        have b36258 := hb (x 5 10)
        have b36259 := hb (x 6 9)
        have b36260 := hb (x 7 8)
        have b36261 := hb (x 8 7)
        have b36262 := hb (x 9 6)
        have b36263 := hb (x 10 5)
        have b36264 := hb (x 11 4)
        have b36265 := hb (x 12 3)
        have b36266 := hb (x 13 2)
        have b36267 := hb (x 14 1)
        clear * - r36253 b36254 b36255 b36256 b36257 b36258 b36259 b36260 b36261 b36262 b36263 b36264 b36265 b36266 b36267 d36180 d36152 d35876 d35896 d35719 d36236 d35552 d35568 d35544 d35609 g36 g31 g25
        omega
      have d36268 : (x 15 14).toNat = 0 := by
        have r36269 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b36270 := hb (x 14 1)
        have b36271 := hb (x 15 14)
        clear * - r36269 b36270 b36271 d36252
        omega
      have d36272 : (x 15 6).toNat = 0 := by
        have r36273 : (x 15 6).toNat ≤ (x 15 14).toNat := himp _ _ (hp6 15)
        have b36274 := hb (x 15 6)
        have b36275 := hb (x 15 14)
        clear * - r36273 b36274 b36275 d36268
        omega
      have d36276 : (x 15 2).toNat = 0 := by
        have r36277 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
        have b36278 := hb (x 15 2)
        have b36279 := hb (x 15 14)
        clear * - r36277 b36278 b36279 d36268
        omega
      have d36280 : (x 11 1).toNat = 0 := by
        have r36281 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b36282 := hb (x (-2) 14)
        have b36283 := hb (x (-1) 13)
        have b36284 := hb (x 0 12)
        have b36285 := hb (x 1 11)
        have b36286 := hb (x 2 10)
        have b36287 := hb (x 3 9)
        have b36288 := hb (x 4 8)
        have b36289 := hb (x 5 7)
        have b36290 := hb (x 6 6)
        have b36291 := hb (x 7 5)
        have b36292 := hb (x 8 4)
        have b36293 := hb (x 9 3)
        have b36294 := hb (x 10 2)
        have b36295 := hb (x 11 1)
        clear * - r36281 b36282 b36283 b36284 b36285 b36286 b36287 b36288 b36289 b36290 b36291 b36292 b36293 b36294 b36295 d36125 d35479 d35601 d36057 g41 g35 g30 g23 g15 g10 d35395
        omega
      have d36296 : (x 11 1 && x 11 14).toNat = 0 := by
        have r36297 := hand1 (x 11 1) (x 11 14)
        have b36298 := hb (x 11 1)
        have b36299 := hb (x 11 1 && x 11 14)
        clear * - r36297 b36298 b36299 d36280
        omega
      have d36300 : (x 11 1 && x 11 11).toNat = 0 := by
        have r36301 := hand1 (x 11 1) (x 11 11)
        have b36302 := hb (x 11 1)
        have b36303 := hb (x 11 1 && x 11 11)
        clear * - r36301 b36302 b36303 d36280
        omega
      have d36304 : (x 12 10).toNat = 1 := by
        have r36305 : 1 ≤ (x 12 10).toNat + (x 11 1 && x 11 11).toNat + (x 10 2 && x 10 12).toNat + (x 9 3 && x 9 13).toNat + (x 8 4 && x 8 14).toNat + (x 7 5).toNat := by have q := hcov10 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b36306 := hb (x 7 5)
        have b36307 := hb (x 12 10)
        have b36308 := hb (x 11 1 && x 11 11)
        have b36309 := hb (x 10 2 && x 10 12)
        have b36310 := hb (x 9 3 && x 9 13)
        have b36311 := hb (x 8 4 && x 8 14)
        clear * - r36305 b36306 b36307 b36308 b36309 b36310 b36311 d36300 d35913 d35925 d36141 d35479
        omega
      have d36312 : (x 12 2).toNat = 1 := by
        have r36313 : (x 12 10).toNat ≤ (x 12 2).toNat := himp _ _ (hp10 12)
        have b36314 := hb (x 12 2)
        have b36315 := hb (x 12 10)
        clear * - r36313 b36314 b36315 d36304
        omega
      have d36316 : (x 14 12).toNat = 0 := by
        have r36317 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36318 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
        have e36319 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
        have b36320 := hb (x 11 3)
        have b36321 := hb (x 12 2)
        have b36322 := hb (x 13 13)
        have b36323 := hb (x 14 12)
        clear * - r36317 e36318 e36319 b36320 b36321 b36322 b36323 d36312
        omega
      have d36324 : (x 14 2 && x 14 12).toNat = 0 := by
        have r36325 := hand2 (x 14 2) (x 14 12)
        have b36326 := hb (x 14 12)
        have b36327 := hb (x 14 2 && x 14 12)
        clear * - r36325 b36326 b36327 d36316
        omega
      have d36328 : (x 13 13).toNat = 0 := by
        have r36329 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36330 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
        have e36331 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
        have b36332 := hb (x 11 3)
        have b36333 := hb (x 12 2)
        have b36334 := hb (x 13 13)
        have b36335 := hb (x 14 12)
        clear * - r36329 e36330 e36331 b36332 b36333 b36334 b36335 d36316 d36312
        omega
      have d36336 : (x 13 3 && x 13 13).toNat = 0 := by
        have r36337 := hand2 (x 13 3) (x 13 13)
        have b36338 := hb (x 13 13)
        have b36339 := hb (x 13 3 && x 13 13)
        clear * - r36337 b36338 b36339 d36328
        omega
      have d36340 : (x 11 13).toNat = 0 := by
        have r36341 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
        have b36342 := hb (x 11 1)
        have b36343 := hb (x 11 13)
        clear * - r36341 b36342 b36343 d36280
        omega
      have d36344 : (x 11 5).toNat = 0 := by
        have r36345 : (x 11 5).toNat ≤ (x 11 13).toNat := himp _ _ (hp5 11)
        have b36346 := hb (x 11 5)
        have b36347 := hb (x 11 13)
        clear * - r36345 b36346 b36347 d36340
        omega
      have d36348 : (x 10 1 && x 10 14).toNat = 1 := by
        have r36349 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b36350 := hb (x 9 2)
        have b36351 := hb (x 11 13)
        have b36352 := hb (x 10 1 && x 10 14)
        clear * - r36349 b36350 b36351 b36352 d36340 d35723
        omega
      have d36353 : (x 10 1).toNat = 1 := by
        have r36354 := hand1 (x 10 1) (x 10 14)
        have b36355 := hb (x 10 1)
        have b36356 := hb (x 10 1 && x 10 14)
        clear * - r36354 b36355 b36356 d36348
        omega
      have d36357 : (x 11 14).toNat = 0 := by
        have r36358 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b36359 := hb (x 10 1)
        have b36360 := hb (x 11 14)
        clear * - r36358 b36359 b36360 d36353
        omega
      have d36361 : (x 11 6).toNat = 0 := by
        have r36362 : (x 11 6).toNat ≤ (x 11 14).toNat := himp _ _ (hp6 11)
        have b36363 := hb (x 11 6)
        have b36364 := hb (x 11 14)
        clear * - r36362 b36363 b36364 d36357
        omega
      have d36365 : (x 11 2).toNat = 0 := by
        have r36366 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
        have b36367 := hb (x 11 2)
        have b36368 := hb (x 11 14)
        clear * - r36366 b36367 b36368 d36357
        omega
      have d36369 : (x 12 1 && x 12 14).toNat = 1 := by
        have r36370 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b36371 := hb (x 11 2)
        have b36372 := hb (x 13 13)
        have b36373 := hb (x 12 1 && x 12 14)
        clear * - r36370 b36371 b36372 b36373 d36328 d36365
        omega
      have d36374 : (x 12 1).toNat = 1 := by
        have r36375 := hand1 (x 12 1) (x 12 14)
        have b36376 := hb (x 12 1)
        have b36377 := hb (x 12 1 && x 12 14)
        clear * - r36375 b36376 b36377 d36369
        omega
      have d36378 : (x 13 14).toNat = 0 := by
        have r36379 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b36380 := hb (x 12 1)
        have b36381 := hb (x 13 14)
        clear * - r36379 b36380 b36381 d36374
        omega
      have d36382 : (x 13 3 && x 13 14).toNat = 0 := by
        have r36383 := hand2 (x 13 3) (x 13 14)
        have b36384 := hb (x 13 14)
        have b36385 := hb (x 13 3 && x 13 14)
        clear * - r36383 b36384 b36385 d36378
        omega
      have d36386 : (x 10 2).toNat = 0 := by
        have r36387 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b36388 := hb (x (-2) 14)
        have b36389 := hb (x (-1) 13)
        have b36390 := hb (x 0 12)
        have b36391 := hb (x 1 11)
        have b36392 := hb (x 2 10)
        have b36393 := hb (x 3 9)
        have b36394 := hb (x 4 8)
        have b36395 := hb (x 5 7)
        have b36396 := hb (x 6 6)
        have b36397 := hb (x 7 5)
        have b36398 := hb (x 8 4)
        have b36399 := hb (x 9 3)
        have b36400 := hb (x 10 2)
        have b36401 := hb (x 11 1)
        clear * - r36387 b36388 b36389 b36390 b36391 b36392 b36393 b36394 b36395 b36396 b36397 b36398 b36399 b36400 b36401 d36280 d36125 d35479 d35601 d36057 g41 g35 g30 g23 g15 g10 d35395
        omega
      have d36402 : (x 12 13).toNat = 1 := by
        have r36403 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b36404 := hb (x 10 2)
        have b36405 := hb (x 12 13)
        have b36406 := hb (x 11 1 && x 11 14)
        clear * - r36403 b36404 b36405 b36406 d36296 d36386
        omega
      have d36407 : (x 13 12).toNat = 0 := by
        have r36408 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36409 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
        have e36410 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
        have b36411 := hb (x 10 3)
        have b36412 := hb (x 11 2)
        have b36413 := hb (x 12 13)
        have b36414 := hb (x 13 12)
        clear * - r36408 e36409 e36410 b36411 b36412 b36413 b36414 d36402 d36365
        omega
      have d36415 : (x 13 4).toNat = 0 := by
        have r36416 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
        have b36417 := hb (x 13 4)
        have b36418 := hb (x 13 12)
        clear * - r36416 b36417 b36418 d36407
        omega
      have d36419 : (x 3 7).toNat = 0 := by
        have r36420 : (x 9 1).toNat + (x 8 2).toNat + (x 7 3).toNat + (x 6 4).toNat + (x 5 5).toNat + (x 4 6).toNat + (x 3 7).toNat + (x 2 8).toNat + (x 1 9).toNat + (x 0 10).toNat + (x (-1) 11).toNat + (x (-2) 12).toNat + (x (-3) 13).toNat + (x (-4) 14).toNat = 3 := by have q := hcount 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b36421 := hb (x (-4) 14)
        have b36422 := hb (x (-3) 13)
        have b36423 := hb (x (-2) 12)
        have b36424 := hb (x (-1) 11)
        have b36425 := hb (x 0 10)
        have b36426 := hb (x 1 9)
        have b36427 := hb (x 2 8)
        have b36428 := hb (x 3 7)
        have b36429 := hb (x 4 6)
        have b36430 := hb (x 5 5)
        have b36431 := hb (x 6 4)
        have b36432 := hb (x 7 3)
        have b36433 := hb (x 8 2)
        have b36434 := hb (x 9 1)
        clear * - r36420 b36421 b36422 b36423 b36424 b36425 b36426 b36427 b36428 b36429 b36430 b36431 b36432 b36433 b36434 d35937 d35900 d35929 d35812 d35961 g40 d34696 d34712 d34688 g9 d35319 d35335 d35315
        omega
      have d36435 : (x 3 7 && x 3 14).toNat = 0 := by
        have r36436 := hand1 (x 3 7) (x 3 14)
        have b36437 := hb (x 3 7)
        have b36438 := hb (x 3 7 && x 3 14)
        clear * - r36436 b36437 b36438 d36419
        omega
      have d36439 : (x 3 7 && x 3 13).toNat = 0 := by
        have r36440 := hand1 (x 3 7) (x 3 13)
        have b36441 := hb (x 3 7)
        have b36442 := hb (x 3 7 && x 3 13)
        clear * - r36440 b36441 b36442 d36419
        omega
      have d36443 : (x 10 6).toNat = 1 := by
        have r36444 : 1 ≤ (x 10 6).toNat + (x 9 1 && x 9 7).toNat + (x 8 2 && x 8 8).toNat + (x 7 3 && x 7 9).toNat + (x 6 4 && x 6 10).toNat + (x 5 5 && x 5 11).toNat + (x 4 6 && x 4 12).toNat + (x 3 7 && x 3 13).toNat + (x 2 8 && x 2 14).toNat + (x 1 9).toNat := by have q := hcov6 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b36445 := hb (x 1 9)
        have b36446 := hb (x 10 6)
        have b36447 := hb (x 9 1 && x 9 7)
        have b36448 := hb (x 8 2 && x 8 8)
        have b36449 := hb (x 7 3 && x 7 9)
        have b36450 := hb (x 6 4 && x 6 10)
        have b36451 := hb (x 5 5 && x 5 11)
        have b36452 := hb (x 4 6 && x 4 12)
        have b36453 := hb (x 3 7 && x 3 13)
        have b36454 := hb (x 2 8 && x 2 14)
        clear * - r36444 b36445 b36446 b36447 b36448 b36449 b36450 b36451 b36452 b36453 b36454 d35957 d35690 d35487 d35670 d35981 g81 d36439 g82 d34712
        omega
      have d36455 : (x 16 8).toNat = 0 := by
        have r36456 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36457 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
        have e36458 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
        have e36459 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
        have e36460 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
        have e36461 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
        have e36462 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
        have b36463 := hb (x 9 7)
        have b36464 := hb (x 10 6)
        have b36465 := hb (x 11 5)
        have b36466 := hb (x 12 4)
        have b36467 := hb (x 13 11)
        have b36468 := hb (x 14 10)
        have b36469 := hb (x 15 9)
        have b36470 := hb (x 16 8)
        clear * - r36456 e36457 e36458 e36459 e36460 e36461 e36462 b36463 b36464 b36465 b36466 b36467 b36468 b36469 b36470 d36344 d36443
        omega
      have d36471 : (x 15 9).toNat = 0 := by
        have r36472 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36473 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
        have e36474 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
        have e36475 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
        have e36476 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
        have e36477 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
        have e36478 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
        have b36479 := hb (x 9 7)
        have b36480 := hb (x 10 6)
        have b36481 := hb (x 11 5)
        have b36482 := hb (x 12 4)
        have b36483 := hb (x 13 11)
        have b36484 := hb (x 14 10)
        have b36485 := hb (x 15 9)
        have b36486 := hb (x 16 8)
        clear * - r36472 e36473 e36474 e36475 e36476 e36477 e36478 b36479 b36480 b36481 b36482 b36483 b36484 b36485 b36486 d36455 d36344 d36443
        omega
      have d36487 : (x 14 10).toNat = 0 := by
        have r36488 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36489 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
        have e36490 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
        have e36491 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
        have e36492 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
        have e36493 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
        have e36494 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
        have b36495 := hb (x 9 7)
        have b36496 := hb (x 10 6)
        have b36497 := hb (x 11 5)
        have b36498 := hb (x 12 4)
        have b36499 := hb (x 13 11)
        have b36500 := hb (x 14 10)
        have b36501 := hb (x 15 9)
        have b36502 := hb (x 16 8)
        clear * - r36488 e36489 e36490 e36491 e36492 e36493 e36494 b36495 b36496 b36497 b36498 b36499 b36500 b36501 b36502 d36455 d36471 d36344 d36443
        omega
      have d36503 : (x 13 11).toNat = 0 := by
        have r36504 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36505 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
        have e36506 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
        have e36507 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
        have e36508 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
        have e36509 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
        have e36510 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
        have b36511 := hb (x 9 7)
        have b36512 := hb (x 10 6)
        have b36513 := hb (x 11 5)
        have b36514 := hb (x 12 4)
        have b36515 := hb (x 13 11)
        have b36516 := hb (x 14 10)
        have b36517 := hb (x 15 9)
        have b36518 := hb (x 16 8)
        clear * - r36504 e36505 e36506 e36507 e36508 e36509 e36510 b36511 b36512 b36513 b36514 b36515 b36516 b36517 b36518 d36455 d36471 d36487 d36344 d36443
        omega
      have d36519 : (x 12 4).toNat = 0 := by
        have r36520 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36521 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
        have e36522 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
        have e36523 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
        have e36524 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
        have e36525 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
        have e36526 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
        have b36527 := hb (x 9 7)
        have b36528 := hb (x 10 6)
        have b36529 := hb (x 11 5)
        have b36530 := hb (x 12 4)
        have b36531 := hb (x 13 11)
        have b36532 := hb (x 14 10)
        have b36533 := hb (x 15 9)
        have b36534 := hb (x 16 8)
        clear * - r36520 e36521 e36522 e36523 e36524 e36525 e36526 b36527 b36528 b36529 b36530 b36531 b36532 b36533 b36534 d36455 d36471 d36487 d36503 d36344 d36443
        omega
      have d36535 : (x 12 4 && x 12 14).toNat = 0 := by
        have r36536 := hand1 (x 12 4) (x 12 14)
        have b36537 := hb (x 12 4)
        have b36538 := hb (x 12 4 && x 12 14)
        clear * - r36536 b36537 b36538 d36519
        omega
      have d36539 : (x 12 4 && x 12 11).toNat = 0 := by
        have r36540 := hand1 (x 12 4) (x 12 11)
        have b36541 := hb (x 12 4)
        have b36542 := hb (x 12 4 && x 12 11)
        clear * - r36540 b36541 b36542 d36519
        omega
      have d36543 : (x 16 7).toNat = 1 := by
        have r36544 : 1 ≤ (x 16 7).toNat + (x 15 1 && x 15 8).toNat + (x 14 2 && x 14 9).toNat + (x 13 3 && x 13 10).toNat + (x 12 4 && x 12 11).toNat + (x 11 5 && x 11 12).toNat + (x 10 6 && x 10 13).toNat + (x 9 7 && x 9 14).toNat + (x 8 8).toNat := by have q := hcov7 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b36545 := hb (x 8 8)
        have b36546 := hb (x 16 7)
        have b36547 := hb (x 15 1 && x 15 8)
        have b36548 := hb (x 14 2 && x 14 9)
        have b36549 := hb (x 13 3 && x 13 10)
        have b36550 := hb (x 12 4 && x 12 11)
        have b36551 := hb (x 11 5 && x 11 12)
        have b36552 := hb (x 10 6 && x 10 13)
        have b36553 := hb (x 9 7 && x 9 14)
        clear * - r36544 b36545 b36546 b36547 b36548 b36549 b36550 b36551 b36552 b36553 d36212 d36232 d36192 d36539 d35872 d35892 d35715 d35674
        omega
      have d36554 : (x 23 8).toNat = 0 := by
        have r36555 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36556 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
        have e36557 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
        have e36558 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
        have e36559 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
        have e36560 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
        have e36561 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
        have b36562 := hb (x 16 7)
        have b36563 := hb (x 17 6)
        have b36564 := hb (x 18 5)
        have b36565 := hb (x 19 4)
        have b36566 := hb (x 20 11)
        have b36567 := hb (x 21 10)
        have b36568 := hb (x 22 9)
        have b36569 := hb (x 23 8)
        clear * - r36555 e36556 e36557 e36558 e36559 e36560 e36561 b36562 b36563 b36564 b36565 b36566 b36567 b36568 b36569 d36543
        omega
      have d36570 : (x 22 9).toNat = 0 := by
        have r36571 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36572 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
        have e36573 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
        have e36574 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
        have e36575 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
        have e36576 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
        have e36577 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
        have b36578 := hb (x 16 7)
        have b36579 := hb (x 17 6)
        have b36580 := hb (x 18 5)
        have b36581 := hb (x 19 4)
        have b36582 := hb (x 20 11)
        have b36583 := hb (x 21 10)
        have b36584 := hb (x 22 9)
        have b36585 := hb (x 23 8)
        clear * - r36571 e36572 e36573 e36574 e36575 e36576 e36577 b36578 b36579 b36580 b36581 b36582 b36583 b36584 b36585 d36554 d36543
        omega
      have d36586 : (x 21 10).toNat = 0 := by
        have r36587 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36588 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
        have e36589 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
        have e36590 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
        have e36591 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
        have e36592 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
        have e36593 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
        have b36594 := hb (x 16 7)
        have b36595 := hb (x 17 6)
        have b36596 := hb (x 18 5)
        have b36597 := hb (x 19 4)
        have b36598 := hb (x 20 11)
        have b36599 := hb (x 21 10)
        have b36600 := hb (x 22 9)
        have b36601 := hb (x 23 8)
        clear * - r36587 e36588 e36589 e36590 e36591 e36592 e36593 b36594 b36595 b36596 b36597 b36598 b36599 b36600 b36601 d36554 d36570 d36543
        omega
      have d36602 : (x 21 1 && x 21 10).toNat = 0 := by
        have r36603 := hand2 (x 21 1) (x 21 10)
        have b36604 := hb (x 21 10)
        have b36605 := hb (x 21 1 && x 21 10)
        clear * - r36603 b36604 b36605 d36586
        omega
      have d36606 : (x 20 11).toNat = 0 := by
        have r36607 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36608 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
        have e36609 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
        have e36610 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
        have e36611 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
        have e36612 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
        have e36613 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
        have b36614 := hb (x 16 7)
        have b36615 := hb (x 17 6)
        have b36616 := hb (x 18 5)
        have b36617 := hb (x 19 4)
        have b36618 := hb (x 20 11)
        have b36619 := hb (x 21 10)
        have b36620 := hb (x 22 9)
        have b36621 := hb (x 23 8)
        clear * - r36607 e36608 e36609 e36610 e36611 e36612 e36613 b36614 b36615 b36616 b36617 b36618 b36619 b36620 b36621 d36554 d36570 d36586 d36543
        omega
      have d36622 : (x 20 2 && x 20 11).toNat = 0 := by
        have r36623 := hand2 (x 20 2) (x 20 11)
        have b36624 := hb (x 20 11)
        have b36625 := hb (x 20 2 && x 20 11)
        clear * - r36623 b36624 b36625 d36606
        omega
      have d36626 : (x 16 11).toNat = 1 := by
        have r36627 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b36628 := hb (x 12 4)
        have b36629 := hb (x 16 11)
        have b36630 := hb (x 15 1 && x 15 12)
        have b36631 := hb (x 14 2 && x 14 13)
        have b36632 := hb (x 13 3 && x 13 14)
        clear * - r36627 b36628 b36629 b36630 b36631 b36632 d36164 d36176 d36382 d36519
        omega
      have d36633 : (x 16 3).toNat = 1 := by
        have r36634 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
        have b36635 := hb (x 16 3)
        have b36636 := hb (x 16 11)
        clear * - r36634 b36635 b36636 d36626
        omega
      have d36637 : (x 19 12).toNat = 0 := by
        have r36638 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36639 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
        have e36640 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
        have b36641 := hb (x 16 3)
        have b36642 := hb (x 17 2)
        have b36643 := hb (x 18 13)
        have b36644 := hb (x 19 12)
        clear * - r36638 e36639 e36640 b36641 b36642 b36643 b36644 d36633
        omega
      have d36645 : (x 19 3 && x 19 12).toNat = 0 := by
        have r36646 := hand2 (x 19 3) (x 19 12)
        have b36647 := hb (x 19 12)
        have b36648 := hb (x 19 3 && x 19 12)
        clear * - r36646 b36647 b36648 d36637
        omega
      have d36649 : (x 18 13).toNat = 0 := by
        have r36650 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36651 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
        have e36652 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
        have b36653 := hb (x 16 3)
        have b36654 := hb (x 17 2)
        have b36655 := hb (x 18 13)
        have b36656 := hb (x 19 12)
        clear * - r36650 e36651 e36652 b36653 b36654 b36655 b36656 d36637 d36633
        omega
      have d36657 : (x 18 4 && x 18 13).toNat = 0 := by
        have r36658 := hand2 (x 18 4) (x 18 13)
        have b36659 := hb (x 18 13)
        have b36660 := hb (x 18 4 && x 18 13)
        clear * - r36658 b36659 b36660 d36649
        omega
      have d36661 : (x 9 7).toNat = 0 := by
        have r36662 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36663 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
        have e36664 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
        have e36665 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
        have e36666 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
        have e36667 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
        have e36668 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
        have b36669 := hb (x 9 7)
        have b36670 := hb (x 10 6)
        have b36671 := hb (x 11 5)
        have b36672 := hb (x 12 4)
        have b36673 := hb (x 13 11)
        have b36674 := hb (x 14 10)
        have b36675 := hb (x 15 9)
        have b36676 := hb (x 16 8)
        clear * - r36662 e36663 e36664 e36665 e36666 e36667 e36668 b36669 b36670 b36671 b36672 b36673 b36674 b36675 b36676 d36455 d36471 d36487 d36503 d36519 d36344 d36443
        omega
      have d36677 : (x 15 1).toNat = 0 := by
        have r36678 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b36679 := hb (x 2 14)
        have b36680 := hb (x 3 13)
        have b36681 := hb (x 4 12)
        have b36682 := hb (x 5 11)
        have b36683 := hb (x 6 10)
        have b36684 := hb (x 7 9)
        have b36685 := hb (x 8 8)
        have b36686 := hb (x 9 7)
        have b36687 := hb (x 10 6)
        have b36688 := hb (x 11 5)
        have b36689 := hb (x 12 4)
        have b36690 := hb (x 13 3)
        have b36691 := hb (x 14 2)
        have b36692 := hb (x 15 1)
        clear * - r36678 b36679 b36680 b36681 b36682 b36683 b36684 b36685 b36686 b36687 b36688 b36689 b36690 b36691 b36692 d36519 d36344 d36443 d36661 d35674 d35483 d35507 d35524 g43 g37 g32
        omega
      have d36693 : (x 15 1 && x 15 11).toNat = 0 := by
        have r36694 := hand1 (x 15 1) (x 15 11)
        have b36695 := hb (x 15 1)
        have b36696 := hb (x 15 1 && x 15 11)
        clear * - r36694 b36695 b36696 d36677
        omega
      have d36697 : (x 16 10).toNat = 1 := by
        have r36698 : 1 ≤ (x 16 10).toNat + (x 15 1 && x 15 11).toNat + (x 14 2 && x 14 12).toNat + (x 13 3 && x 13 13).toNat + (x 12 4 && x 12 14).toNat + (x 11 5).toNat := by have q := hcov10 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b36699 := hb (x 11 5)
        have b36700 := hb (x 16 10)
        have b36701 := hb (x 15 1 && x 15 11)
        have b36702 := hb (x 14 2 && x 14 12)
        have b36703 := hb (x 13 3 && x 13 13)
        have b36704 := hb (x 12 4 && x 12 14)
        clear * - r36698 b36699 b36700 b36701 b36702 b36703 b36704 d36693 d36324 d36336 d36535 d36344
        omega
      have d36705 : (x 16 2).toNat = 1 := by
        have r36706 : (x 16 10).toNat ≤ (x 16 2).toNat := himp _ _ (hp10 16)
        have b36707 := hb (x 16 2)
        have b36708 := hb (x 16 10)
        clear * - r36706 b36707 b36708 d36697
        omega
      have d36709 : (x 18 12).toNat = 0 := by
        have r36710 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36711 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
        have e36712 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
        have b36713 := hb (x 15 3)
        have b36714 := hb (x 16 2)
        have b36715 := hb (x 17 13)
        have b36716 := hb (x 18 12)
        clear * - r36710 e36711 e36712 b36713 b36714 b36715 b36716 d36705
        omega
      have d36717 : (x 18 3 && x 18 12).toNat = 0 := by
        have r36718 := hand2 (x 18 3) (x 18 12)
        have b36719 := hb (x 18 12)
        have b36720 := hb (x 18 3 && x 18 12)
        clear * - r36718 b36719 b36720 d36709
        omega
      have d36721 : (x 18 4).toNat = 0 := by
        have r36722 : (x 18 4).toNat ≤ (x 18 12).toNat := himp _ _ (hp4 18)
        have b36723 := hb (x 18 4)
        have b36724 := hb (x 18 12)
        clear * - r36722 b36723 b36724 d36709
        omega
      have d36725 : (x 17 13).toNat = 0 := by
        have r36726 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36727 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
        have e36728 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
        have b36729 := hb (x 15 3)
        have b36730 := hb (x 16 2)
        have b36731 := hb (x 17 13)
        have b36732 := hb (x 18 12)
        clear * - r36726 e36727 e36728 b36729 b36730 b36731 b36732 d36709 d36705
        omega
      have d36733 : (x 17 4 && x 17 13).toNat = 0 := by
        have r36734 := hand2 (x 17 4) (x 17 13)
        have b36735 := hb (x 17 13)
        have b36736 := hb (x 17 4 && x 17 13)
        clear * - r36734 b36735 b36736 d36725
        omega
      have d36737 : (x 17 5).toNat = 0 := by
        have r36738 : (x 17 5).toNat ≤ (x 17 13).toNat := himp _ _ (hp5 17)
        have b36739 := hb (x 17 5)
        have b36740 := hb (x 17 13)
        clear * - r36738 b36739 b36740 d36725
        omega
      have d36741 : (x 17 5 && x 17 14).toNat = 0 := by
        have r36742 := hand1 (x 17 5) (x 17 14)
        have b36743 := hb (x 17 5)
        have b36744 := hb (x 17 5 && x 17 14)
        clear * - r36742 b36743 b36744 d36737
        omega
      have d36745 : (x 16 6).toNat = 1 := by
        have r36746 : 1 ≤ (x 22 9).toNat + (x 21 1 && x 21 10).toNat + (x 20 2 && x 20 11).toNat + (x 19 3 && x 19 12).toNat + (x 18 4 && x 18 13).toNat + (x 17 5 && x 17 14).toNat + (x 16 6).toNat := by have q := hcov9 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b36747 := hb (x 16 6)
        have b36748 := hb (x 22 9)
        have b36749 := hb (x 21 1 && x 21 10)
        have b36750 := hb (x 20 2 && x 20 11)
        have b36751 := hb (x 19 3 && x 19 12)
        have b36752 := hb (x 18 4 && x 18 13)
        have b36753 := hb (x 17 5 && x 17 14)
        clear * - r36746 b36747 b36748 b36749 b36750 b36751 b36752 b36753 d36570 d36602 d36622 d36645 d36657 d36741
        omega
      have d36754 : (x 22 8).toNat = 0 := by
        have r36755 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36756 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
        have e36757 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
        have e36758 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
        have e36759 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
        have e36760 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
        have e36761 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
        have b36762 := hb (x 15 7)
        have b36763 := hb (x 16 6)
        have b36764 := hb (x 17 5)
        have b36765 := hb (x 18 4)
        have b36766 := hb (x 19 11)
        have b36767 := hb (x 20 10)
        have b36768 := hb (x 21 9)
        have b36769 := hb (x 22 8)
        clear * - r36755 e36756 e36757 e36758 e36759 e36760 e36761 b36762 b36763 b36764 b36765 b36766 b36767 b36768 b36769 d36721 d36737 d36745
        omega
      have d36770 : (x 21 9).toNat = 0 := by
        have r36771 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36772 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
        have e36773 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
        have e36774 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
        have e36775 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
        have e36776 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
        have e36777 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
        have b36778 := hb (x 15 7)
        have b36779 := hb (x 16 6)
        have b36780 := hb (x 17 5)
        have b36781 := hb (x 18 4)
        have b36782 := hb (x 19 11)
        have b36783 := hb (x 20 10)
        have b36784 := hb (x 21 9)
        have b36785 := hb (x 22 8)
        clear * - r36771 e36772 e36773 e36774 e36775 e36776 e36777 b36778 b36779 b36780 b36781 b36782 b36783 b36784 b36785 d36754 d36721 d36737 d36745
        omega
      have d36786 : (x 20 10).toNat = 0 := by
        have r36787 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36788 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
        have e36789 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
        have e36790 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
        have e36791 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
        have e36792 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
        have e36793 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
        have b36794 := hb (x 15 7)
        have b36795 := hb (x 16 6)
        have b36796 := hb (x 17 5)
        have b36797 := hb (x 18 4)
        have b36798 := hb (x 19 11)
        have b36799 := hb (x 20 10)
        have b36800 := hb (x 21 9)
        have b36801 := hb (x 22 8)
        clear * - r36787 e36788 e36789 e36790 e36791 e36792 e36793 b36794 b36795 b36796 b36797 b36798 b36799 b36800 b36801 d36754 d36770 d36721 d36737 d36745
        omega
      have d36802 : (x 20 1 && x 20 10).toNat = 0 := by
        have r36803 := hand2 (x 20 1) (x 20 10)
        have b36804 := hb (x 20 10)
        have b36805 := hb (x 20 1 && x 20 10)
        clear * - r36803 b36804 b36805 d36786
        omega
      have d36806 : (x 19 11).toNat = 0 := by
        have r36807 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36808 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
        have e36809 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
        have e36810 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
        have e36811 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
        have e36812 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
        have e36813 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
        have b36814 := hb (x 15 7)
        have b36815 := hb (x 16 6)
        have b36816 := hb (x 17 5)
        have b36817 := hb (x 18 4)
        have b36818 := hb (x 19 11)
        have b36819 := hb (x 20 10)
        have b36820 := hb (x 21 9)
        have b36821 := hb (x 22 8)
        clear * - r36807 e36808 e36809 e36810 e36811 e36812 e36813 b36814 b36815 b36816 b36817 b36818 b36819 b36820 b36821 d36754 d36770 d36786 d36721 d36737 d36745
        omega
      have d36822 : (x 19 2 && x 19 11).toNat = 0 := by
        have r36823 := hand2 (x 19 2) (x 19 11)
        have b36824 := hb (x 19 11)
        have b36825 := hb (x 19 2 && x 19 11)
        clear * - r36823 b36824 b36825 d36806
        omega
      have d36826 : (x 16 5 && x 16 14).toNat = 1 := by
        have r36827 : 1 ≤ (x 21 9).toNat + (x 20 1 && x 20 10).toNat + (x 19 2 && x 19 11).toNat + (x 18 3 && x 18 12).toNat + (x 17 4 && x 17 13).toNat + (x 16 5 && x 16 14).toNat + (x 15 6).toNat := by have q := hcov9 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b36828 := hb (x 15 6)
        have b36829 := hb (x 21 9)
        have b36830 := hb (x 20 1 && x 20 10)
        have b36831 := hb (x 19 2 && x 19 11)
        have b36832 := hb (x 18 3 && x 18 12)
        have b36833 := hb (x 17 4 && x 17 13)
        have b36834 := hb (x 16 5 && x 16 14)
        clear * - r36827 b36828 b36829 b36830 b36831 b36832 b36833 b36834 d36770 d36802 d36822 d36717 d36733 d36272
        omega
      have d36835 : (x 16 5).toNat = 1 := by
        have r36836 := hand1 (x 16 5) (x 16 14)
        have b36837 := hb (x 16 5)
        have b36838 := hb (x 16 5 && x 16 14)
        clear * - r36836 b36837 b36838 d36826
        omega
      have d36839 : (x 16 13).toNat = 1 := by
        have r36840 : (x 16 5).toNat ≤ (x 16 13).toNat := himp _ _ (hp5 16)
        have b36841 := hb (x 16 5)
        have b36842 := hb (x 16 13)
        clear * - r36840 b36841 b36842 d36835
        omega
      have d36843 : (x 16 1).toNat = 1 := by
        have r36844 : (x 16 13).toNat ≤ (x 16 1).toNat := himp _ _ (hp13 16)
        have b36845 := hb (x 16 1)
        have b36846 := hb (x 16 13)
        clear * - r36844 b36845 b36846 d36839
        omega
      have d36847 : (x 14 3).toNat = 0 := by
        have r36848 : (x 16 1).toNat + (x 15 2).toNat + (x 14 3).toNat + (x 13 4).toNat + (x 12 5).toNat + (x 11 6).toNat + (x 10 7).toNat + (x 9 8).toNat + (x 8 9).toNat + (x 7 10).toNat + (x 6 11).toNat + (x 5 12).toNat + (x 4 13).toNat + (x 3 14).toNat = 3 := by have q := hcount 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b36849 := hb (x 3 14)
        have b36850 := hb (x 4 13)
        have b36851 := hb (x 5 12)
        have b36852 := hb (x 6 11)
        have b36853 := hb (x 7 10)
        have b36854 := hb (x 8 9)
        have b36855 := hb (x 9 8)
        have b36856 := hb (x 10 7)
        have b36857 := hb (x 11 6)
        have b36858 := hb (x 12 5)
        have b36859 := hb (x 13 4)
        have b36860 := hb (x 14 3)
        have b36861 := hb (x 15 2)
        have b36862 := hb (x 16 1)
        clear * - r36848 b36849 b36850 b36851 b36852 b36853 b36854 b36855 b36856 b36857 b36858 b36859 b36860 b36861 b36862 d36843 d36276 d36415 d36361 d35747 d35771 d35787 d35625 d35642
        omega
      have d36863 : (x 12 5).toNat = 0 := by
        have r36864 : (x 16 1).toNat + (x 15 2).toNat + (x 14 3).toNat + (x 13 4).toNat + (x 12 5).toNat + (x 11 6).toNat + (x 10 7).toNat + (x 9 8).toNat + (x 8 9).toNat + (x 7 10).toNat + (x 6 11).toNat + (x 5 12).toNat + (x 4 13).toNat + (x 3 14).toNat = 3 := by have q := hcount 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b36865 := hb (x 3 14)
        have b36866 := hb (x 4 13)
        have b36867 := hb (x 5 12)
        have b36868 := hb (x 6 11)
        have b36869 := hb (x 7 10)
        have b36870 := hb (x 8 9)
        have b36871 := hb (x 9 8)
        have b36872 := hb (x 10 7)
        have b36873 := hb (x 11 6)
        have b36874 := hb (x 12 5)
        have b36875 := hb (x 13 4)
        have b36876 := hb (x 14 3)
        have b36877 := hb (x 15 2)
        have b36878 := hb (x 16 1)
        clear * - r36864 b36865 b36866 b36867 b36868 b36869 b36870 b36871 b36872 b36873 b36874 b36875 b36876 b36877 b36878 d36843 d36276 d36847 d36415 d36361 d35747 d35771 d35787 d35625 d35642
        omega
      have d36879 : (x 10 7).toNat = 0 := by
        have r36880 : (x 16 1).toNat + (x 15 2).toNat + (x 14 3).toNat + (x 13 4).toNat + (x 12 5).toNat + (x 11 6).toNat + (x 10 7).toNat + (x 9 8).toNat + (x 8 9).toNat + (x 7 10).toNat + (x 6 11).toNat + (x 5 12).toNat + (x 4 13).toNat + (x 3 14).toNat = 3 := by have q := hcount 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b36881 := hb (x 3 14)
        have b36882 := hb (x 4 13)
        have b36883 := hb (x 5 12)
        have b36884 := hb (x 6 11)
        have b36885 := hb (x 7 10)
        have b36886 := hb (x 8 9)
        have b36887 := hb (x 9 8)
        have b36888 := hb (x 10 7)
        have b36889 := hb (x 11 6)
        have b36890 := hb (x 12 5)
        have b36891 := hb (x 13 4)
        have b36892 := hb (x 14 3)
        have b36893 := hb (x 15 2)
        have b36894 := hb (x 16 1)
        clear * - r36880 b36881 b36882 b36883 b36884 b36885 b36886 b36887 b36888 b36889 b36890 b36891 b36892 b36893 b36894 d36843 d36276 d36847 d36415 d36863 d36361 d35747 d35771 d35787 d35625 d35642
        omega
      have d36895 : (x 8 2 && x 8 9).toNat = 1 := by
        have r36896 : 1 ≤ (x 10 7).toNat + (x 9 1 && x 9 8).toNat + (x 8 2 && x 8 9).toNat + (x 7 3 && x 7 10).toNat + (x 6 4 && x 6 11).toNat + (x 5 5 && x 5 12).toNat + (x 4 6 && x 4 13).toNat + (x 3 7 && x 3 14).toNat + (x 2 8).toNat := by have q := hcov7 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b36897 := hb (x 2 8)
        have b36898 := hb (x 10 7)
        have b36899 := hb (x 9 1 && x 9 8)
        have b36900 := hb (x 8 2 && x 8 9)
        have b36901 := hb (x 7 3 && x 7 10)
        have b36902 := hb (x 6 4 && x 6 11)
        have b36903 := hb (x 5 5 && x 5 12)
        have b36904 := hb (x 4 6 && x 4 13)
        have b36905 := hb (x 3 7 && x 3 14)
        clear * - r36896 b36897 b36898 b36899 b36900 b36901 b36902 b36903 b36904 b36905 d36879 d35953 d35751 d35816 d35977 g91 d36435 d34696
        omega
      have d36906 : (x 8 9).toNat = 1 := by
        have r36907 := hand2 (x 8 2) (x 8 9)
        have b36908 := hb (x 8 9)
        have b36909 := hb (x 8 2 && x 8 9)
        clear * - r36907 b36908 b36909 d36895
        omega
      have r36910 : (x 16 1).toNat + (x 15 2).toNat + (x 14 3).toNat + (x 13 4).toNat + (x 12 5).toNat + (x 11 6).toNat + (x 10 7).toNat + (x 9 8).toNat + (x 8 9).toNat + (x 7 10).toNat + (x 6 11).toNat + (x 5 12).toNat + (x 4 13).toNat + (x 3 14).toNat = 3 := by have q := hcount 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b36911 := hb (x 3 14)
      have b36912 := hb (x 4 13)
      have b36913 := hb (x 5 12)
      have b36914 := hb (x 6 11)
      have b36915 := hb (x 7 10)
      have b36916 := hb (x 8 9)
      have b36917 := hb (x 9 8)
      have b36918 := hb (x 10 7)
      have b36919 := hb (x 11 6)
      have b36920 := hb (x 12 5)
      have b36921 := hb (x 13 4)
      have b36922 := hb (x 14 3)
      have b36923 := hb (x 15 2)
      have b36924 := hb (x 16 1)
      linarith only [r36910, b36911, b36912, b36913, b36914, b36915, b36916, b36917, b36918, b36919, b36920, b36921, b36922, b36923, b36924, d36843, d36276, d36847, d36415, d36863, d36361, d36879, d36906, d35747, d35771, d35787, d35625, d35642]
  · have f36925 : (x 0 6).toNat = 1 := by rw [h34481]; rfl
    have d36926 : (x 6 8).toNat = 0 := by
      have r36927 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e36928 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e36929 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e36930 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e36931 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e36932 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e36933 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b36934 := hb (x (-1) 7)
      have b36935 := hb (x 0 6)
      have b36936 := hb (x 1 5)
      have b36937 := hb (x 2 4)
      have b36938 := hb (x 3 11)
      have b36939 := hb (x 4 10)
      have b36940 := hb (x 5 9)
      have b36941 := hb (x 6 8)
      clear * - r36927 e36928 e36929 e36930 e36931 e36932 e36933 b36934 b36935 b36936 b36937 b36938 b36939 b36940 b36941 g42 g27 g20 f36925
      omega
    have d36942 : (x 6 1 && x 6 8).toNat = 0 := by
      have r36943 := hand2 (x 6 1) (x 6 8)
      have b36944 := hb (x 6 8)
      have b36945 := hb (x 6 1 && x 6 8)
      clear * - r36943 b36944 b36945 d36926
      omega
    have d36946 : (x 5 9).toNat = 0 := by
      have r36947 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e36948 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e36949 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e36950 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e36951 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e36952 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e36953 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b36954 := hb (x (-1) 7)
      have b36955 := hb (x 0 6)
      have b36956 := hb (x 1 5)
      have b36957 := hb (x 2 4)
      have b36958 := hb (x 3 11)
      have b36959 := hb (x 4 10)
      have b36960 := hb (x 5 9)
      have b36961 := hb (x 6 8)
      clear * - r36947 e36948 e36949 e36950 e36951 e36952 e36953 b36954 b36955 b36956 b36957 b36958 b36959 b36960 b36961 d36926 g42 g27 g20 f36925
      omega
    have d36962 : (x 5 2 && x 5 9).toNat = 0 := by
      have r36963 := hand2 (x 5 2) (x 5 9)
      have b36964 := hb (x 5 9)
      have b36965 := hb (x 5 2 && x 5 9)
      clear * - r36963 b36964 b36965 d36946
      omega
    have d36966 : (x 3 11).toNat = 0 := by
      have r36967 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e36968 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e36969 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e36970 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e36971 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e36972 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e36973 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b36974 := hb (x (-1) 7)
      have b36975 := hb (x 0 6)
      have b36976 := hb (x 1 5)
      have b36977 := hb (x 2 4)
      have b36978 := hb (x 3 11)
      have b36979 := hb (x 4 10)
      have b36980 := hb (x 5 9)
      have b36981 := hb (x 6 8)
      clear * - r36967 e36968 e36969 e36970 e36971 e36972 e36973 b36974 b36975 b36976 b36977 b36978 b36979 b36980 b36981 d36926 d36946 g42 g27 g20 f36925
      omega
    have d36982 : (x 3 2 && x 3 11).toNat = 0 := by
      have r36983 := hand2 (x 3 2) (x 3 11)
      have b36984 := hb (x 3 11)
      have b36985 := hb (x 3 2 && x 3 11)
      clear * - r36983 b36984 b36985 d36966
      omega
    have d36986 : (x (-1) 6).toNat = 1 := by
      have r36987 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b36988 := hb (x (-1) 6)
      have b36989 := hb (x 5 9)
      have b36990 := hb (x 4 1 && x 4 10)
      have b36991 := hb (x 3 2 && x 3 11)
      have b36992 := hb (x 2 3 && x 2 12)
      have b36993 := hb (x 1 4 && x 1 13)
      have b36994 := hb (x 0 5 && x 0 14)
      clear * - r36987 b36988 b36989 b36990 b36991 b36992 b36993 b36994 d36946 g97 d36982 g98 g99 d34477
      omega
    have d36995 : (x (-1) 14).toNat = 1 := by
      have r36996 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
      have b36997 := hb (x (-1) 6)
      have b36998 := hb (x (-1) 14)
      clear * - r36996 b36997 b36998 d36986
      omega
    have d36999 : (x (-2) 1).toNat = 0 := by
      have r37000 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b37001 := hb (x (-2) 1)
      have b37002 := hb (x (-1) 14)
      clear * - r37000 b37001 b37002 d36995
      omega
    have d37003 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
      have r37004 := hand1 (x (-2) 1) (x (-2) 14)
      have b37005 := hb (x (-2) 1)
      have b37006 := hb (x (-2) 1 && x (-2) 14)
      clear * - r37004 b37005 b37006 d36999
      omega
    have d37007 : (x (-3) 2).toNat = 1 := by
      have r37008 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b37009 := hb (x (-3) 2)
      have b37010 := hb (x (-1) 13)
      have b37011 := hb (x (-2) 1 && x (-2) 14)
      clear * - r37008 b37009 b37010 b37011 g10 d37003
      omega
    have d37012 : (x (-3) 14).toNat = 1 := by
      have r37013 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
      have b37014 := hb (x (-3) 2)
      have b37015 := hb (x (-3) 14)
      clear * - r37013 b37014 b37015 d37007
      omega
    have d37016 : (x (-4) 1).toNat = 0 := by
      have r37017 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b37018 := hb (x (-4) 1)
      have b37019 := hb (x (-3) 14)
      clear * - r37017 b37018 b37019 d37012
      omega
    have d37020 : (x (-4) 13).toNat = 0 := by
      have r37021 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
      have b37022 := hb (x (-4) 1)
      have b37023 := hb (x (-4) 13)
      clear * - r37021 b37022 b37023 d37016
      omega
    have d37024 : (x (-1) 12).toNat = 0 := by
      have r37025 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e37026 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e37027 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b37028 := hb (x (-4) 3)
      have b37029 := hb (x (-3) 2)
      have b37030 := hb (x (-2) 13)
      have b37031 := hb (x (-1) 12)
      clear * - r37025 e37026 e37027 b37028 b37029 b37030 b37031 d37007
      omega
    have d37032 : (x (-1) 8 && x (-1) 12).toNat = 0 := by
      have r37033 := hand2 (x (-1) 8) (x (-1) 12)
      have b37034 := hb (x (-1) 12)
      have b37035 := hb (x (-1) 8 && x (-1) 12)
      clear * - r37033 b37034 b37035 d37024
      omega
    have d37036 : (x (-2) 13).toNat = 0 := by
      have r37037 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e37038 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e37039 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b37040 := hb (x (-4) 3)
      have b37041 := hb (x (-3) 2)
      have b37042 := hb (x (-2) 13)
      have b37043 := hb (x (-1) 12)
      clear * - r37037 e37038 e37039 b37040 b37041 b37042 b37043 d37024 d37007
      omega
    have d37044 : (x (-2) 9 && x (-2) 13).toNat = 0 := by
      have r37045 := hand2 (x (-2) 9) (x (-2) 13)
      have b37046 := hb (x (-2) 13)
      have b37047 := hb (x (-2) 9 && x (-2) 13)
      clear * - r37045 b37046 b37047 d37036
      omega
    have d37048 : (x (-4) 3).toNat = 0 := by
      have r37049 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e37050 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e37051 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b37052 := hb (x (-4) 3)
      have b37053 := hb (x (-3) 2)
      have b37054 := hb (x (-2) 13)
      have b37055 := hb (x (-1) 12)
      clear * - r37049 e37050 e37051 b37052 b37053 b37054 b37055 d37024 d37036 d37007
      omega
    have d37056 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
      have r37057 := hand1 (x (-4) 3) (x (-4) 12)
      have b37058 := hb (x (-4) 3)
      have b37059 := hb (x (-4) 3 && x (-4) 12)
      clear * - r37057 b37058 b37059 d37048
      omega
    have d37060 : (x (-4) 11).toNat = 0 := by
      have r37061 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
      have b37062 := hb (x (-4) 3)
      have b37063 := hb (x (-4) 11)
      clear * - r37061 b37062 b37063 d37048
      omega
    have d37064 : (x (-2) 9).toNat = 0 := by
      have r37065 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
      have b37066 := hb (x (-2) 1)
      have b37067 := hb (x (-2) 9)
      clear * - r37065 b37066 b37067 d36999
      omega
    have d37068 : (x 5 8).toNat = 0 := by
      have r37069 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e37070 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
      have e37071 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
      have e37072 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
      have e37073 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
      have e37074 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
      have e37075 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
      have b37076 := hb (x (-2) 7)
      have b37077 := hb (x (-1) 6)
      have b37078 := hb (x 0 5)
      have b37079 := hb (x 1 4)
      have b37080 := hb (x 2 11)
      have b37081 := hb (x 3 10)
      have b37082 := hb (x 4 9)
      have b37083 := hb (x 5 8)
      clear * - r37069 e37070 e37071 e37072 e37073 e37074 e37075 b37076 b37077 b37078 b37079 b37080 b37081 b37082 b37083 g19 g13 d36986
      omega
    have d37084 : (x 5 2 && x 5 8).toNat = 0 := by
      have r37085 := hand2 (x 5 2) (x 5 8)
      have b37086 := hb (x 5 8)
      have b37087 := hb (x 5 2 && x 5 8)
      clear * - r37085 b37086 b37087 d37068
      omega
    have d37088 : (x 4 9).toNat = 0 := by
      have r37089 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e37090 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
      have e37091 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
      have e37092 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
      have e37093 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
      have e37094 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
      have e37095 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
      have b37096 := hb (x (-2) 7)
      have b37097 := hb (x (-1) 6)
      have b37098 := hb (x 0 5)
      have b37099 := hb (x 1 4)
      have b37100 := hb (x 2 11)
      have b37101 := hb (x 3 10)
      have b37102 := hb (x 4 9)
      have b37103 := hb (x 5 8)
      clear * - r37089 e37090 e37091 e37092 e37093 e37094 e37095 b37096 b37097 b37098 b37099 b37100 b37101 b37102 b37103 d37068 g19 g13 d36986
      omega
    have d37104 : (x 4 3 && x 4 9).toNat = 0 := by
      have r37105 := hand2 (x 4 3) (x 4 9)
      have b37106 := hb (x 4 9)
      have b37107 := hb (x 4 3 && x 4 9)
      clear * - r37105 b37106 b37107 d37088
      omega
    have d37108 : (x 3 10).toNat = 0 := by
      have r37109 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e37110 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
      have e37111 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
      have e37112 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
      have e37113 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
      have e37114 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
      have e37115 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
      have b37116 := hb (x (-2) 7)
      have b37117 := hb (x (-1) 6)
      have b37118 := hb (x 0 5)
      have b37119 := hb (x 1 4)
      have b37120 := hb (x 2 11)
      have b37121 := hb (x 3 10)
      have b37122 := hb (x 4 9)
      have b37123 := hb (x 5 8)
      clear * - r37109 e37110 e37111 e37112 e37113 e37114 e37115 b37116 b37117 b37118 b37119 b37120 b37121 b37122 b37123 d37068 d37088 g19 g13 d36986
      omega
    have d37124 : (x 2 11).toNat = 0 := by
      have r37125 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e37126 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
      have e37127 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
      have e37128 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
      have e37129 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
      have e37130 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
      have e37131 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
      have b37132 := hb (x (-2) 7)
      have b37133 := hb (x (-1) 6)
      have b37134 := hb (x 0 5)
      have b37135 := hb (x 1 4)
      have b37136 := hb (x 2 11)
      have b37137 := hb (x 3 10)
      have b37138 := hb (x 4 9)
      have b37139 := hb (x 5 8)
      clear * - r37125 e37126 e37127 e37128 e37129 e37130 e37131 b37132 b37133 b37134 b37135 b37136 b37137 b37138 b37139 d37068 d37088 d37108 g19 g13 d36986
      omega
    have r37140 : (x 6 1).toNat + (x 5 2).toNat + (x 4 3).toNat + (x 3 4).toNat + (x 2 5).toNat + (x 1 6).toNat + (x 0 7).toNat + (x (-1) 8).toNat + (x (-2) 9).toNat + (x (-3) 10).toNat + (x (-4) 11).toNat + (x (-5) 12).toNat + (x (-6) 13).toNat + (x (-7) 14).toNat = 3 := by have q := hcount 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r37141 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r37142 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r37143 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37144 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
    have e37145 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
    have e37146 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
    have e37147 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
    have e37148 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
    have e37149 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
    have r37150 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37151 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e37152 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e37153 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e37154 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e37155 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e37156 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have r37157 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37158 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
    have e37159 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
    have r37160 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37161 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e37162 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have r37163 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37164 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e37165 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have r37166 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r37167 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r37168 : 1 ≤ (x 7 4).toNat + (x 6 1 && x 6 5).toNat + (x 5 2 && x 5 6).toNat + (x 4 3 && x 4 7).toNat + (x 3 4 && x 3 8).toNat + (x 2 5 && x 2 9).toNat + (x 1 6 && x 1 10).toNat + (x 0 7 && x 0 11).toNat + (x (-1) 8 && x (-1) 12).toNat + (x (-2) 9 && x (-2) 13).toNat + (x (-3) 10 && x (-3) 14).toNat + (x (-4) 11).toNat := by have q := hcov4 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37169 : (x 6 1 && x 6 5).toNat = (x 6 5).toNat := handr _ _ (fun h => hp13 6 (hp5 6 (h)))
    have e37170 : (x (-3) 10 && x (-3) 14).toNat = (x (-3) 10).toNat := handl _ _ (fun h => hp2 (-3) (hp10 (-3) (h)))
    have r37171 : 1 ≤ (x 7 6).toNat + (x 6 1 && x 6 7).toNat + (x 5 2 && x 5 8).toNat + (x 4 3 && x 4 9).toNat + (x 3 4 && x 3 10).toNat + (x 2 5 && x 2 11).toNat + (x 1 6 && x 1 12).toNat + (x 0 7 && x 0 13).toNat + (x (-1) 8 && x (-1) 14).toNat + (x (-2) 9).toNat := by have q := hcov6 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r37172 : 1 ≤ (x 7 7).toNat + (x 6 1 && x 6 8).toNat + (x 5 2 && x 5 9).toNat + (x 4 3 && x 4 10).toNat + (x 3 4 && x 3 11).toNat + (x 2 5 && x 2 12).toNat + (x 1 6 && x 1 13).toNat + (x 0 7 && x 0 14).toNat + (x (-1) 8).toNat := by have q := hcov7 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r37173 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r37174 : 1 ≤ (x 13 9).toNat + (x 12 1 && x 12 10).toNat + (x 11 2 && x 11 11).toNat + (x 10 3 && x 10 12).toNat + (x 9 4 && x 9 13).toNat + (x 8 5 && x 8 14).toNat + (x 7 6).toNat := by have q := hcov9 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r37175 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r37176 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r37177 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r37178 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r37179 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
    have r37180 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
    have r37181 : (x 7 6).toNat ≤ (x 7 14).toNat := himp _ _ (hp6 7)
    have r37182 := hand2 (x 5 2) (x 5 6)
    have r37183 := hand2 (x 4 3) (x 4 7)
    have r37184 := hand2 (x 6 1) (x 6 7)
    have r37185 := hand1 (x (-1) 8) (x (-1) 14)
    have r37186 := hand1 (x (-5) 4) (x (-5) 13)
    have r37187 := hand1 (x (-6) 5) (x (-6) 14)
    have r37188 := hand1 (x 12 1) (x 12 10)
    have r37189 := hand1 (x 11 2) (x 11 11)
    have r37190 := hand1 (x 10 3) (x 10 12)
    have r37191 := hand1 (x 9 4) (x 9 13)
    have r37192 := hand1 (x 8 5) (x 8 14)
    have r37193 := hand1 (x 10 1) (x 10 12)
    have r37194 := hand1 (x 9 2) (x 9 13)
    have r37195 := hand1 (x 8 3) (x 8 14)
    have r37196 := hand1 (x (-6) 1) (x (-6) 14)
    have r37197 := hand2 (x (-5) 1) (x (-5) 14)
    have b37203 := hb (x (-7) 14)
    linarith only [r37140, r37141, r37142, r37143, e37144, e37145, e37146, e37147, e37148, e37149, r37150, e37151, e37152, e37153, e37154, e37155, e37156, r37157, e37158, e37159, r37160, e37161, e37162, r37163, e37164, e37165, r37166, r37167, r37168, e37169, e37170, r37171, r37172, r37173, r37174, r37175, r37176, r37177, r37178, r37179, r37180, r37181, r37182, r37183, r37184, r37185, r37186, r37187, r37188, r37189, r37190, r37191, r37192, r37193, r37194, r37195, r37196, r37197, b37203, d37060, d37020, d37012, d37064, d37036, g7, d37024, d36995, g14, g16, g21, g22, g24, g28, d37124, g34, d37108, d37088, d37068, g55, g56, g57, g58, d37032, d37044, d37084, d37104, g77, g78, g79, g80, d36942, d36962, g86, g87, g88, g89, g90, g92, g93, d37056, g115, g116, g117]

theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt1110110 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 7).toNat = 0)
    (g1 : (x (-3) 11).toNat = 0)
    (g2 : (x (-2) 6).toNat = 0)
    (g3 : (x (-2) 10).toNat = 0)
    (g4 : (x (-2) 11).toNat = 0)
    (g5 : (x (-1) 3).toNat = 0)
    (g6 : (x (-1) 5).toNat = 0)
    (g7 : (x (-1) 9).toNat = 0)
    (g8 : (x (-1) 10).toNat = 0)
    (g9 : (x (-1) 11).toNat = 0)
    (g10 : (x (-1) 13).toNat = 0)
    (g11 : (x 0 2).toNat = 1)
    (g12 : (x 0 4).toNat = 1)
    (g13 : (x 0 5).toNat = 0)
    (g14 : (x 0 7).toNat = 0)
    (g15 : (x 0 12).toNat = 1)
    (g16 : (x 0 13).toNat = 1)
    (g17 : (x 1 1).toNat = 1)
    (g18 : (x 1 3).toNat = 0)
    (g19 : (x 1 4).toNat = 0)
    (g20 : (x 1 5).toNat = 0)
    (g21 : (x 1 6).toNat = 0)
    (g22 : (x 1 10).toNat = 0)
    (g23 : (x 1 11).toNat = 0)
    (g24 : (x 1 12).toNat = 0)
    (g25 : (x 1 14).toNat = 0)
    (g26 : (x 2 2).toNat = 0)
    (g27 : (x 2 4).toNat = 0)
    (g28 : (x 2 5).toNat = 0)
    (g29 : (x 2 6).toNat = 0)
    (g30 : (x 2 10).toNat = 0)
    (g31 : (x 2 13).toNat = 0)
    (g32 : (x 2 14).toNat = 0)
    (g33 : (x 3 1).toNat = 1)
    (g34 : (x 3 4).toNat = 0)
    (g35 : (x 3 9).toNat = 0)
    (g36 : (x 3 12).toNat = 0)
    (g37 : (x 3 13).toNat = 1)
    (g38 : (x 4 2).toNat = 0)
    (g39 : (x 4 4).toNat = 0)
    (g40 : (x 4 6).toNat = 0)
    (g41 : (x 4 8).toNat = 0)
    (g42 : (x 4 10).toNat = 0)
    (g43 : (x 4 12).toNat = 0)
    (g44 : (x 4 3 && x 4 6).toNat = 0)
    (g45 : (x 3 4 && x 3 7).toNat = 0)
    (g46 : (x 2 5 && x 2 8).toNat = 0)
    (g47 : (x 1 6 && x 1 9).toNat = 0)
    (g48 : (x 0 7 && x 0 10).toNat = 0)
    (g49 : (x (-1) 8 && x (-1) 11).toNat = 0)
    (g50 : (x 2 2 && x 2 6).toNat = 0)
    (g51 : (x 1 3 && x 1 7).toNat = 0)
    (g52 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g53 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g54 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g55 : (x 3 4 && x 3 8).toNat = 0)
    (g56 : (x 2 5 && x 2 9).toNat = 0)
    (g57 : (x 1 6 && x 1 10).toNat = 0)
    (g58 : (x 0 7 && x 0 11).toNat = 0)
    (g59 : (x (-1) 1 && x (-1) 6).toNat = 0)
    (g60 : (x (-2) 2 && x (-2) 7).toNat = 0)
    (g61 : (x (-3) 3 && x (-3) 8).toNat = 0)
    (g62 : (x 1 1 && x 1 6).toNat = 0)
    (g63 : (x 0 2 && x 0 7).toNat = 0)
    (g64 : (x (-1) 3 && x (-1) 8).toNat = 0)
    (g65 : (x 4 3 && x 4 8).toNat = 0)
    (g66 : (x 3 4 && x 3 9).toNat = 0)
    (g67 : (x 2 5 && x 2 10).toNat = 0)
    (g68 : (x 1 6 && x 1 11).toNat = 0)
    (g69 : (x 0 7 && x 0 12).toNat = 0)
    (g70 : (x (-1) 8 && x (-1) 13).toNat = 0)
    (g71 : (x 0 1 && x 0 7).toNat = 0)
    (g72 : (x (-1) 2 && x (-1) 8).toNat = 0)
    (g73 : (x (-2) 3 && x (-2) 9).toNat = 0)
    (g74 : (x (-1) 3 && x (-1) 9).toNat = 0)
    (g75 : (x (-2) 4 && x (-2) 10).toNat = 0)
    (g76 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g77 : (x 3 4 && x 3 10).toNat = 0)
    (g78 : (x 2 5 && x 2 11).toNat = 0)
    (g79 : (x 1 6 && x 1 12).toNat = 0)
    (g80 : (x 0 7 && x 0 13).toNat = 0)
    (g81 : (x 4 6 && x 4 12).toNat = 0)
    (g82 : (x 2 8 && x 2 14).toNat = 0)
    (g83 : (x (-1) 1 && x (-1) 8).toNat = 0)
    (g84 : (x (-2) 2 && x (-2) 9).toNat = 0)
    (g85 : (x (-3) 3 && x (-3) 10).toNat = 0)
    (g86 : (x 4 3 && x 4 10).toNat = 0)
    (g87 : (x 3 4 && x 3 11).toNat = 0)
    (g88 : (x 2 5 && x 2 12).toNat = 0)
    (g89 : (x 1 6 && x 1 13).toNat = 0)
    (g90 : (x 0 7 && x 0 14).toNat = 0)
    (g91 : (x 4 6 && x 4 13).toNat = 0)
    (g92 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g93 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g94 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g95 : (x (-2) 2 && x (-2) 11).toNat = 0)
    (g96 : (x (-3) 3 && x (-3) 12).toNat = 0)
    (g97 : (x 4 1 && x 4 10).toNat = 0)
    (g98 : (x 2 3 && x 2 12).toNat = 0)
    (g99 : (x 1 4 && x 1 13).toNat = 0)
    (g100 : (x 4 2 && x 4 11).toNat = 0)
    (g101 : (x 3 3 && x 3 12).toNat = 0)
    (g102 : (x 2 4 && x 2 13).toNat = 0)
    (g103 : (x 1 5 && x 1 14).toNat = 0)
    (g104 : (x 4 3 && x 4 12).toNat = 0)
    (g105 : (x 3 4 && x 3 13).toNat = 0)
    (g106 : (x 2 5 && x 2 14).toNat = 0)
    (g107 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g108 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g109 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g110 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g111 : (x 3 2 && x 3 12).toNat = 0)
    (g112 : (x 2 3 && x 2 13).toNat = 0)
    (g113 : (x 1 4 && x 1 14).toNat = 0)
    (g114 : (x 3 4 && x 3 14).toNat = 0)
    (g115 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g116 : (x (-2) 2 && x (-2) 13).toNat = 0)
    (g117 : (x (-3) 3 && x (-3) 14).toNat = 0)
    (g118 : (x 4 1 && x 4 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt1110110_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83 g84 g85 g86 g87 g88 g89 g90 g91 g92 g93 g94 g95 g96 g97 g98 g99 g100 g101 g102 g103 g104 g105 g106 g107 g108 g109 g110 g111 g112 g113 g114 g115 g116 g117 g118
