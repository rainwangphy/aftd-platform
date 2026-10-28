import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_a111110

Topic: combinatorics   Node: 0863bc36f4c6

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_six_iff_seven_core: under the layer-free tight-cover constraints for k = 15 and 103 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_a111110_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-12) 4).toNat = 0)
    (g1 : (x (-4) 7).toNat = 0)
    (g2 : (x (-3) 6).toNat = 0)
    (g3 : (x (-3) 7).toNat = 0)
    (g4 : (x (-3) 11).toNat = 0)
    (g5 : (x (-2) 5).toNat = 0)
    (g6 : (x (-2) 6).toNat = 0)
    (g7 : (x (-2) 10).toNat = 0)
    (g8 : (x (-1) 1).toNat = 0)
    (g9 : (x (-1) 4).toNat = 0)
    (g10 : (x (-1) 5).toNat = 0)
    (g11 : (x (-1) 9).toNat = 0)
    (g12 : (x (-1) 10).toNat = 0)
    (g13 : (x (-1) 11).toNat = 0)
    (g14 : (x (-1) 13).toNat = 0)
    (g15 : (x 0 3).toNat = 1)
    (g16 : (x 0 4).toNat = 1)
    (g17 : (x 0 7).toNat = 0)
    (g18 : (x 0 8).toNat = 1)
    (g19 : (x 0 11).toNat = 1)
    (g20 : (x 0 12).toNat = 1)
    (g21 : (x 0 13).toNat = 1)
    (g22 : (x 1 1).toNat = 0)
    (g23 : (x 1 2).toNat = 0)
    (g24 : (x 1 4).toNat = 0)
    (g25 : (x 1 5).toNat = 0)
    (g26 : (x 1 6).toNat = 0)
    (g27 : (x 1 8).toNat = 0)
    (g28 : (x 1 9).toNat = 0)
    (g29 : (x 1 10).toNat = 0)
    (g30 : (x 1 11).toNat = 0)
    (g31 : (x 1 12).toNat = 0)
    (g32 : (x 1 13).toNat = 0)
    (g33 : (x 2 5).toNat = 0)
    (g34 : (x 2 9).toNat = 0)
    (g35 : (x 2 10).toNat = 0)
    (g36 : (x 2 11).toNat = 0)
    (g37 : (x 3 4).toNat = 0)
    (g38 : (x 3 8).toNat = 0)
    (g39 : (x 3 9).toNat = 0)
    (g40 : (x 3 10).toNat = 0)
    (g41 : (x 4 8).toNat = 0)
    (g42 : (x 4 9).toNat = 0)
    (g43 : (x 5 8).toNat = 0)
    (g44 : (x (-2) 1 && x (-2) 2).toNat = 0)
    (g45 : (x (-3) 2 && x (-3) 3).toNat = 0)
    (g46 : (x (-4) 3 && x (-4) 4).toNat = 0)
    (g47 : (x (-5) 4 && x (-5) 5).toNat = 0)
    (g48 : (x (-6) 5 && x (-6) 6).toNat = 0)
    (g49 : (x (-7) 6 && x (-7) 7).toNat = 0)
    (g50 : (x (-9) 8 && x (-9) 9).toNat = 0)
    (g51 : (x (-10) 9 && x (-10) 10).toNat = 0)
    (g52 : (x (-11) 10 && x (-11) 11).toNat = 0)
    (g53 : (x 6 8 && x 6 10).toNat = 0)
    (g54 : (x 5 9 && x 5 11).toNat = 0)
    (g55 : (x 4 10 && x 4 12).toNat = 0)
    (g56 : (x 3 11 && x 3 13).toNat = 0)
    (g57 : (x 2 12 && x 2 14).toNat = 0)
    (g58 : (x 5 8 && x 5 11).toNat = 0)
    (g59 : (x 4 9 && x 4 12).toNat = 0)
    (g60 : (x 3 10 && x 3 13).toNat = 0)
    (g61 : (x 2 11 && x 2 14).toNat = 0)
    (g62 : (x 1 2 && x 1 6).toNat = 0)
    (g63 : (x 0 3 && x 0 7).toNat = 0)
    (g64 : (x (-1) 4 && x (-1) 8).toNat = 0)
    (g65 : (x (-2) 5 && x (-2) 9).toNat = 0)
    (g66 : (x (-3) 6 && x (-3) 10).toNat = 0)
    (g67 : (x (-4) 7 && x (-4) 11).toNat = 0)
    (g68 : (x 3 4 && x 3 8).toNat = 0)
    (g69 : (x 2 5 && x 2 9).toNat = 0)
    (g70 : (x 1 6 && x 1 10).toNat = 0)
    (g71 : (x 0 7 && x 0 11).toNat = 0)
    (g72 : (x (-2) 1 && x (-2) 6).toNat = 0)
    (g73 : (x (-3) 2 && x (-3) 7).toNat = 0)
    (g74 : (x 4 3 && x 4 8).toNat = 0)
    (g75 : (x 3 4 && x 3 9).toNat = 0)
    (g76 : (x 2 5 && x 2 10).toNat = 0)
    (g77 : (x 1 6 && x 1 11).toNat = 0)
    (g78 : (x 0 7 && x 0 12).toNat = 0)
    (g79 : (x (-1) 8 && x (-1) 13).toNat = 0)
    (g80 : (x 3 8 && x 3 13).toNat = 0)
    (g81 : (x 2 9 && x 2 14).toNat = 0)
    (g82 : (x 5 2 && x 5 8).toNat = 0)
    (g83 : (x 4 3 && x 4 9).toNat = 0)
    (g84 : (x 3 4 && x 3 10).toNat = 0)
    (g85 : (x 2 5 && x 2 11).toNat = 0)
    (g86 : (x 1 6 && x 1 12).toNat = 0)
    (g87 : (x 0 7 && x 0 13).toNat = 0)
    (g88 : (x 2 8 && x 2 14).toNat = 0)
    (g89 : (x 6 1 && x 6 8).toNat = 0)
    (g90 : (x 5 2 && x 5 9).toNat = 0)
    (g91 : (x 4 3 && x 4 10).toNat = 0)
    (g92 : (x 3 4 && x 3 11).toNat = 0)
    (g93 : (x 2 5 && x 2 12).toNat = 0)
    (g94 : (x 1 6 && x 1 13).toNat = 0)
    (g95 : (x 0 7 && x 0 14).toNat = 0)
    (g96 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g97 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g98 : (x 3 4 && x 3 13).toNat = 0)
    (g99 : (x 2 5 && x 2 14).toNat = 0)
    (g100 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g101 : (x 2 4 && x 2 14).toNat = 0)
    (g102 : (x 3 4 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d46712 : (x 2 14).toNat = 1 := by
    have r46713 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b46714 := hb (x 1 1)
    have b46715 := hb (x 2 14)
    clear * - r46713 b46714 b46715 g22
    omega
  cases h46716 : x 1 3
  · have f46717 : (x 1 3).toNat = 0 := by rw [h46716]; rfl
    cases h46718 : x 1 7
    · have f46719 : (x 1 7).toNat = 0 := by rw [h46718]; rfl
      cases h46720 : x (-1) 8
      · have f46721 : (x (-1) 8).toNat = 0 := by rw [h46720]; rfl
        have d46722 : (x (-1) 8 && x (-1) 14).toNat = 0 := by
          have r46723 := hand1 (x (-1) 8) (x (-1) 14)
          have b46724 := hb (x (-1) 8)
          have b46725 := hb (x (-1) 8 && x (-1) 14)
          clear * - r46723 b46724 b46725 f46721
          omega
        have d46726 : (x (-1) 8 && x (-1) 12).toNat = 0 := by
          have r46727 := hand1 (x (-1) 8) (x (-1) 12)
          have b46728 := hb (x (-1) 8)
          have b46729 := hb (x (-1) 8 && x (-1) 12)
          clear * - r46727 b46728 b46729 f46721
          omega
        have d46730 : (x 7 7).toNat = 1 := by
          have r46731 : 1 ≤ (x 7 7).toNat + (x 6 1 && x 6 8).toNat + (x 5 2 && x 5 9).toNat + (x 4 3 && x 4 10).toNat + (x 3 4 && x 3 11).toNat + (x 2 5 && x 2 12).toNat + (x 1 6 && x 1 13).toNat + (x 0 7 && x 0 14).toNat + (x (-1) 8).toNat := by have q := hcov7 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b46732 := hb (x (-1) 8)
          have b46733 := hb (x 7 7)
          have b46734 := hb (x 6 1 && x 6 8)
          have b46735 := hb (x 5 2 && x 5 9)
          have b46736 := hb (x 4 3 && x 4 10)
          have b46737 := hb (x 3 4 && x 3 11)
          have b46738 := hb (x 2 5 && x 2 12)
          have b46739 := hb (x 1 6 && x 1 13)
          have b46740 := hb (x 0 7 && x 0 14)
          clear * - r46731 b46732 b46733 b46734 b46735 b46736 b46737 b46738 b46739 b46740 g89 g90 g91 g92 g93 g94 g95 f46721
          omega
        have d46741 : (x 14 8).toNat = 0 := by
          have r46742 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e46743 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
          have e46744 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
          have e46745 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
          have e46746 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
          have e46747 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
          have e46748 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
          have b46749 := hb (x 7 7)
          have b46750 := hb (x 8 6)
          have b46751 := hb (x 9 5)
          have b46752 := hb (x 10 4)
          have b46753 := hb (x 11 11)
          have b46754 := hb (x 12 10)
          have b46755 := hb (x 13 9)
          have b46756 := hb (x 14 8)
          clear * - r46742 e46743 e46744 e46745 e46746 e46747 e46748 b46749 b46750 b46751 b46752 b46753 b46754 b46755 b46756 d46730
          omega
        have d46757 : (x 13 9).toNat = 0 := by
          have r46758 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e46759 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
          have e46760 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
          have e46761 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
          have e46762 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
          have e46763 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
          have e46764 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
          have b46765 := hb (x 7 7)
          have b46766 := hb (x 8 6)
          have b46767 := hb (x 9 5)
          have b46768 := hb (x 10 4)
          have b46769 := hb (x 11 11)
          have b46770 := hb (x 12 10)
          have b46771 := hb (x 13 9)
          have b46772 := hb (x 14 8)
          clear * - r46758 e46759 e46760 e46761 e46762 e46763 e46764 b46765 b46766 b46767 b46768 b46769 b46770 b46771 b46772 d46741 d46730
          omega
        have d46773 : (x 12 10).toNat = 0 := by
          have r46774 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e46775 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
          have e46776 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
          have e46777 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
          have e46778 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
          have e46779 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
          have e46780 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
          have b46781 := hb (x 7 7)
          have b46782 := hb (x 8 6)
          have b46783 := hb (x 9 5)
          have b46784 := hb (x 10 4)
          have b46785 := hb (x 11 11)
          have b46786 := hb (x 12 10)
          have b46787 := hb (x 13 9)
          have b46788 := hb (x 14 8)
          clear * - r46774 e46775 e46776 e46777 e46778 e46779 e46780 b46781 b46782 b46783 b46784 b46785 b46786 b46787 b46788 d46741 d46757 d46730
          omega
        have d46789 : (x 12 1 && x 12 10).toNat = 0 := by
          have r46790 := hand2 (x 12 1) (x 12 10)
          have b46791 := hb (x 12 10)
          have b46792 := hb (x 12 1 && x 12 10)
          clear * - r46790 b46791 b46792 d46773
          omega
        have d46793 : (x 11 11).toNat = 0 := by
          have r46794 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e46795 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
          have e46796 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
          have e46797 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
          have e46798 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
          have e46799 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
          have e46800 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
          have b46801 := hb (x 7 7)
          have b46802 := hb (x 8 6)
          have b46803 := hb (x 9 5)
          have b46804 := hb (x 10 4)
          have b46805 := hb (x 11 11)
          have b46806 := hb (x 12 10)
          have b46807 := hb (x 13 9)
          have b46808 := hb (x 14 8)
          clear * - r46794 e46795 e46796 e46797 e46798 e46799 e46800 b46801 b46802 b46803 b46804 b46805 b46806 b46807 b46808 d46741 d46757 d46773 d46730
          omega
        have d46809 : (x 11 1 && x 11 11).toNat = 0 := by
          have r46810 := hand2 (x 11 1) (x 11 11)
          have b46811 := hb (x 11 11)
          have b46812 := hb (x 11 1 && x 11 11)
          clear * - r46810 b46811 b46812 d46793
          omega
        have d46813 : (x 11 2 && x 11 11).toNat = 0 := by
          have r46814 := hand2 (x 11 2) (x 11 11)
          have b46815 := hb (x 11 11)
          have b46816 := hb (x 11 2 && x 11 11)
          clear * - r46814 b46815 b46816 d46793
          omega
        have d46817 : (x 10 4).toNat = 0 := by
          have r46818 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e46819 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
          have e46820 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
          have e46821 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
          have e46822 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
          have e46823 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
          have e46824 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
          have b46825 := hb (x 7 7)
          have b46826 := hb (x 8 6)
          have b46827 := hb (x 9 5)
          have b46828 := hb (x 10 4)
          have b46829 := hb (x 11 11)
          have b46830 := hb (x 12 10)
          have b46831 := hb (x 13 9)
          have b46832 := hb (x 14 8)
          clear * - r46818 e46819 e46820 e46821 e46822 e46823 e46824 b46825 b46826 b46827 b46828 b46829 b46830 b46831 b46832 d46741 d46757 d46773 d46793 d46730
          omega
        have d46833 : (x 10 4 && x 10 6).toNat = 0 := by
          have r46834 := hand1 (x 10 4) (x 10 6)
          have b46835 := hb (x 10 4)
          have b46836 := hb (x 10 4 && x 10 6)
          clear * - r46834 b46835 b46836 d46817
          omega
        have d46837 : (x 9 5).toNat = 0 := by
          have r46838 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e46839 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
          have e46840 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
          have e46841 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
          have e46842 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
          have e46843 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
          have e46844 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
          have b46845 := hb (x 7 7)
          have b46846 := hb (x 8 6)
          have b46847 := hb (x 9 5)
          have b46848 := hb (x 10 4)
          have b46849 := hb (x 11 11)
          have b46850 := hb (x 12 10)
          have b46851 := hb (x 13 9)
          have b46852 := hb (x 14 8)
          clear * - r46838 e46839 e46840 e46841 e46842 e46843 e46844 b46845 b46846 b46847 b46848 b46849 b46850 b46851 b46852 d46741 d46757 d46773 d46793 d46817 d46730
          omega
        have d46853 : (x 9 5 && x 9 7).toNat = 0 := by
          have r46854 := hand1 (x 9 5) (x 9 7)
          have b46855 := hb (x 9 5)
          have b46856 := hb (x 9 5 && x 9 7)
          clear * - r46854 b46855 b46856 d46837
          omega
        have d46857 : (x 8 6).toNat = 0 := by
          have r46858 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e46859 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
          have e46860 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
          have e46861 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
          have e46862 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
          have e46863 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
          have e46864 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
          have b46865 := hb (x 7 7)
          have b46866 := hb (x 8 6)
          have b46867 := hb (x 9 5)
          have b46868 := hb (x 10 4)
          have b46869 := hb (x 11 11)
          have b46870 := hb (x 12 10)
          have b46871 := hb (x 13 9)
          have b46872 := hb (x 14 8)
          clear * - r46858 e46859 e46860 e46861 e46862 e46863 e46864 b46865 b46866 b46867 b46868 b46869 b46870 b46871 b46872 d46741 d46757 d46773 d46793 d46817 d46837 d46730
          omega
        have d46873 : (x 8 6 && x 8 8).toNat = 0 := by
          have r46874 := hand1 (x 8 6) (x 8 8)
          have b46875 := hb (x 8 6)
          have b46876 := hb (x 8 6 && x 8 8)
          clear * - r46874 b46875 b46876 d46857
          omega
        cases h46877 : x (-1) 12
        · have f46878 : (x (-1) 12).toNat = 0 := by rw [h46877]; rfl
          cases h46879 : x (-1) 14
          · have f46880 : (x (-1) 14).toNat = 0 := by rw [h46879]; rfl
            cases h46881 : x 2 1
            · have f46882 : (x 2 1).toNat = 0 := by rw [h46881]; rfl
              have d46883 : (x 2 1 && x 2 14).toNat = 0 := by
                have r46884 := hand1 (x 2 1) (x 2 14)
                have b46885 := hb (x 2 1)
                have b46886 := hb (x 2 1 && x 2 14)
                clear * - r46884 b46885 b46886 f46882
                omega
              have d46887 : (x 3 13).toNat = 1 := by
                have r46888 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b46889 := hb (x 1 2)
                have b46890 := hb (x 3 13)
                have b46891 := hb (x 2 1 && x 2 14)
                clear * - r46888 b46889 b46890 b46891 d46883 g23
                omega
              have d46892 : (x 4 12).toNat = 0 := by
                have r46893 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e46894 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e46895 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b46896 := hb (x 1 3)
                have b46897 := hb (x 2 2)
                have b46898 := hb (x 3 13)
                have b46899 := hb (x 4 12)
                clear * - r46893 e46894 e46895 b46896 b46897 b46898 b46899 d46887 f46717
                omega
              have d46900 : (x 4 3 && x 4 12).toNat = 0 := by
                have r46901 := hand2 (x 4 3) (x 4 12)
                have b46902 := hb (x 4 12)
                have b46903 := hb (x 4 3 && x 4 12)
                clear * - r46901 b46902 b46903 d46892
                omega
              have d46904 : (x 4 7 && x 4 12).toNat = 0 := by
                have r46905 := hand2 (x 4 7) (x 4 12)
                have b46906 := hb (x 4 12)
                have b46907 := hb (x 4 7 && x 4 12)
                clear * - r46905 b46906 b46907 d46892
                omega
              have d46908 : (x 4 4).toNat = 0 := by
                have r46909 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
                have b46910 := hb (x 4 4)
                have b46911 := hb (x 4 12)
                clear * - r46909 b46910 b46911 d46892
                omega
              have r46912 : (x 6 1).toNat + (x 5 2).toNat + (x 4 3).toNat + (x 3 4).toNat + (x 2 5).toNat + (x 1 6).toNat + (x 0 7).toNat + (x (-1) 8).toNat + (x (-2) 9).toNat + (x (-3) 10).toNat + (x (-4) 11).toNat + (x (-5) 12).toNat + (x (-6) 13).toNat + (x (-7) 14).toNat = 3 := by have q := hcount 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r46913 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r46914 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r46915 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46916 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e46917 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e46918 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e46919 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e46920 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e46921 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have r46922 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46923 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
              have e46924 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
              have e46925 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
              have e46926 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
              have e46927 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
              have e46928 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
              have r46929 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46930 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
              have e46931 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
              have r46932 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46933 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
              have e46934 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
              have r46935 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r46936 : 1 ≤ (x 14 2).toNat + (x 13 1 && x 13 3).toNat + (x 12 2 && x 12 4).toNat + (x 11 3 && x 11 5).toNat + (x 10 4 && x 10 6).toNat + (x 9 5 && x 9 7).toNat + (x 8 6 && x 8 8).toNat + (x 7 7 && x 7 9).toNat + (x 6 8 && x 6 10).toNat + (x 5 9 && x 5 11).toNat + (x 4 10 && x 4 12).toNat + (x 3 11 && x 3 13).toNat + (x 2 12 && x 2 14).toNat + (x 1 13).toNat := by have q := hcov2 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r46937 : 1 ≤ (x 13 3).toNat + (x 12 1 && x 12 4).toNat + (x 11 2 && x 11 5).toNat + (x 10 3 && x 10 6).toNat + (x 9 4 && x 9 7).toNat + (x 8 5 && x 8 8).toNat + (x 7 6 && x 7 9).toNat + (x 6 7 && x 6 10).toNat + (x 5 8 && x 5 11).toNat + (x 4 9 && x 4 12).toNat + (x 3 10 && x 3 13).toNat + (x 2 11 && x 2 14).toNat + (x 1 12).toNat := by have q := hcov3 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r46938 : 1 ≤ (x 11 5).toNat + (x 10 1 && x 10 6).toNat + (x 9 2 && x 9 7).toNat + (x 8 3 && x 8 8).toNat + (x 7 4 && x 7 9).toNat + (x 6 5 && x 6 10).toNat + (x 5 6 && x 5 11).toNat + (x 4 7 && x 4 12).toNat + (x 3 8 && x 3 13).toNat + (x 2 9 && x 2 14).toNat + (x 1 10).toNat := by have q := hcov5 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r46939 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r46940 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r46941 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r46942 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r46943 : (x 7 6).toNat ≤ (x 7 14).toNat := himp _ _ (hp6 7)
              have r46944 : (x 7 9).toNat ≤ (x 7 1).toNat := himp _ _ (hp9 7)
              have r46945 := hand2 (x 13 1) (x 13 3)
              have r46946 := hand2 (x 12 2) (x 12 4)
              have r46947 := hand2 (x 11 3) (x 11 5)
              have r46948 := hand2 (x 7 7) (x 7 9)
              have r46949 := hand2 (x 12 1) (x 12 4)
              have r46950 := hand2 (x 11 2) (x 11 5)
              have r46951 := hand2 (x 10 3) (x 10 6)
              have r46952 := hand2 (x 9 4) (x 9 7)
              have r46953 := hand2 (x 8 5) (x 8 8)
              have r46954 := hand1 (x 7 6) (x 7 9)
              have r46955 := hand2 (x 6 7) (x 6 10)
              have r46956 := hand2 (x 10 1) (x 10 6)
              have r46957 := hand2 (x 9 2) (x 9 7)
              have r46958 := hand2 (x 8 3) (x 8 8)
              have r46959 := hand1 (x 7 4) (x 7 9)
              have r46960 := hand1 (x 6 5) (x 6 10)
              have r46961 := hand1 (x 5 6) (x 5 11)
              have r46962 := hand2 (x (-4) 3) (x (-4) 12)
              have r46963 := hand1 (x (-5) 4) (x (-5) 13)
              have r46964 := hand1 (x (-6) 5) (x (-6) 14)
              have r46965 := hand2 (x 6 1) (x 6 10)
              have r46966 := hand2 (x 5 2) (x 5 11)
              have r46967 := hand2 (x 7 1) (x 7 12)
              have r46968 := hand1 (x 6 2) (x 6 13)
              have r46969 := hand1 (x 5 3) (x 5 14)
              have r46970 := hand2 (x (-6) 1) (x (-6) 14)
              have b46975 := hb (x (-7) 14)
              linarith only [r46912, r46913, r46914, r46915, e46916, e46917, e46918, e46919, e46920, e46921, r46922, e46923, e46924, e46925, e46926, e46927, e46928, r46929, e46930, e46931, r46932, e46933, e46934, r46935, r46936, r46937, r46938, r46939, r46940, r46941, r46942, r46943, r46944, r46945, r46946, r46947, r46948, r46949, r46950, r46951, r46952, r46953, r46954, r46955, r46956, r46957, r46958, r46959, r46960, r46961, r46962, r46963, r46964, r46965, r46966, r46967, r46968, r46969, r46970, b46975, g4, g7, f46721, g11, g17, g18, g26, f46719, g29, g31, g32, g33, d46712, g37, d46887, d46908, d46892, d46833, d46853, d46873, g53, g54, g55, g56, g57, g58, g59, g60, g61, d46904, g80, g81, g96, g97, d46900, g98, g99]
            · have f47080 : (x 2 1).toNat = 1 := by rw [h46881]; rfl
              have d47081 : (x 3 14).toNat = 0 := by
                have r47082 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b47083 := hb (x 2 1)
                have b47084 := hb (x 3 14)
                clear * - r47082 b47083 b47084 f47080
                omega
              have d47085 : (x 3 1 && x 3 14).toNat = 0 := by
                have r47086 := hand2 (x 3 1) (x 3 14)
                have b47087 := hb (x 3 14)
                have b47088 := hb (x 3 1 && x 3 14)
                clear * - r47086 b47087 b47088 d47081
                omega
              have d47089 : (x 3 5 && x 3 14).toNat = 0 := by
                have r47090 := hand2 (x 3 5) (x 3 14)
                have b47091 := hb (x 3 14)
                have b47092 := hb (x 3 5 && x 3 14)
                clear * - r47090 b47091 b47092 d47081
                omega
              have d47093 : (x 3 6).toNat = 0 := by
                have r47094 : (x 3 6).toNat ≤ (x 3 14).toNat := himp _ _ (hp6 3)
                have b47095 := hb (x 3 6)
                have b47096 := hb (x 3 14)
                clear * - r47094 b47095 b47096 d47081
                omega
              have d47097 : (x 3 2).toNat = 0 := by
                have r47098 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
                have b47099 := hb (x 3 2)
                have b47100 := hb (x 3 14)
                clear * - r47098 b47099 b47100 d47081
                omega
              cases h47101 : x 2 2
              · have f47102 : (x 2 2).toNat = 0 := by rw [h47101]; rfl
                have d47103 : (x 4 13).toNat = 1 := by
                  have r47104 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b47105 := hb (x 2 2)
                  have b47106 := hb (x 4 13)
                  have b47107 := hb (x 3 1 && x 3 14)
                  clear * - r47104 b47105 b47106 b47107 d47085 f47102
                  omega
                have d47108 : (x 4 1).toNat = 1 := by
                  have r47109 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
                  have b47110 := hb (x 4 1)
                  have b47111 := hb (x 4 13)
                  clear * - r47109 b47110 b47111 d47103
                  omega
                have d47112 : (x 5 14).toNat = 0 := by
                  have r47113 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b47114 := hb (x 4 1)
                  have b47115 := hb (x 5 14)
                  clear * - r47113 b47114 b47115 d47108
                  omega
                have d47116 : (x 5 1 && x 5 14).toNat = 0 := by
                  have r47117 := hand2 (x 5 1) (x 5 14)
                  have b47118 := hb (x 5 14)
                  have b47119 := hb (x 5 1 && x 5 14)
                  clear * - r47117 b47118 b47119 d47112
                  omega
                have d47120 : (x 5 3 && x 5 14).toNat = 0 := by
                  have r47121 := hand2 (x 5 3) (x 5 14)
                  have b47122 := hb (x 5 14)
                  have b47123 := hb (x 5 3 && x 5 14)
                  clear * - r47121 b47122 b47123 d47112
                  omega
                have d47124 : (x 5 6).toNat = 0 := by
                  have r47125 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
                  have b47126 := hb (x 5 6)
                  have b47127 := hb (x 5 14)
                  clear * - r47125 b47126 b47127 d47112
                  omega
                have d47128 : (x 5 2 && x 5 6).toNat = 0 := by
                  have r47129 := hand2 (x 5 2) (x 5 6)
                  have b47130 := hb (x 5 6)
                  have b47131 := hb (x 5 2 && x 5 6)
                  clear * - r47129 b47130 b47131 d47124
                  omega
                have d47132 : (x 5 2).toNat = 0 := by
                  have r47133 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
                  have b47134 := hb (x 5 2)
                  have b47135 := hb (x 5 14)
                  clear * - r47133 b47134 b47135 d47112
                  omega
                have d47136 : (x 5 2 && x 5 12).toNat = 0 := by
                  have r47137 := hand1 (x 5 2) (x 5 12)
                  have b47138 := hb (x 5 2)
                  have b47139 := hb (x 5 2 && x 5 12)
                  clear * - r47137 b47138 b47139 d47132
                  omega
                have d47140 : (x 5 2 && x 5 11).toNat = 0 := by
                  have r47141 := hand1 (x 5 2) (x 5 11)
                  have b47142 := hb (x 5 2)
                  have b47143 := hb (x 5 2 && x 5 11)
                  clear * - r47141 b47142 b47143 d47132
                  omega
                have d47144 : (x 5 2 && x 5 7).toNat = 0 := by
                  have r47145 := hand1 (x 5 2) (x 5 7)
                  have b47146 := hb (x 5 2)
                  have b47147 := hb (x 5 2 && x 5 7)
                  clear * - r47145 b47146 b47147 d47132
                  omega
                have d47148 : (x 5 12).toNat = 0 := by
                  have r47149 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e47150 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                  have e47151 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                  have b47152 := hb (x 2 3)
                  have b47153 := hb (x 3 2)
                  have b47154 := hb (x 4 13)
                  have b47155 := hb (x 5 12)
                  clear * - r47149 e47150 e47151 b47152 b47153 b47154 b47155 d47103 d47097
                  omega
                have d47156 : (x 5 3 && x 5 12).toNat = 0 := by
                  have r47157 := hand2 (x 5 3) (x 5 12)
                  have b47158 := hb (x 5 12)
                  have b47159 := hb (x 5 3 && x 5 12)
                  clear * - r47157 b47158 b47159 d47148
                  omega
                have d47160 : (x 5 4).toNat = 0 := by
                  have r47161 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
                  have b47162 := hb (x 5 4)
                  have b47163 := hb (x 5 12)
                  clear * - r47161 b47162 b47163 d47148
                  omega
                have d47164 : (x 5 4 && x 5 13).toNat = 0 := by
                  have r47165 := hand1 (x 5 4) (x 5 13)
                  have b47166 := hb (x 5 4)
                  have b47167 := hb (x 5 4 && x 5 13)
                  clear * - r47165 b47166 b47167 d47160
                  omega
                cases h47168 : x 2 6
                · have f47169 : (x 2 6).toNat = 0 := by rw [h47168]; rfl
                  cases h47170 : x 2 7
                  · have f47171 : (x 2 7).toNat = 0 := by rw [h47170]; rfl
                    have r47172 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r47173 : (x 6 1).toNat + (x 5 2).toNat + (x 4 3).toNat + (x 3 4).toNat + (x 2 5).toNat + (x 1 6).toNat + (x 0 7).toNat + (x (-1) 8).toNat + (x (-2) 9).toNat + (x (-3) 10).toNat + (x (-4) 11).toNat + (x (-5) 12).toNat + (x (-6) 13).toNat + (x (-7) 14).toNat = 3 := by have q := hcount 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r47174 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r47175 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r47176 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r47177 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r47178 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e47179 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                    have e47180 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                    have e47181 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                    have e47182 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                    have e47183 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                    have e47184 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                    have r47185 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e47186 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                    have e47187 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                    have e47188 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                    have e47189 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                    have e47190 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                    have e47191 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                    have r47192 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e47193 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                    have e47194 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                    have r47195 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e47196 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                    have e47197 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                    have r47198 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e47199 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                    have e47200 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                    have r47201 : 1 ≤ (x 14 2).toNat + (x 13 1 && x 13 3).toNat + (x 12 2 && x 12 4).toNat + (x 11 3 && x 11 5).toNat + (x 10 4 && x 10 6).toNat + (x 9 5 && x 9 7).toNat + (x 8 6 && x 8 8).toNat + (x 7 7 && x 7 9).toNat + (x 6 8 && x 6 10).toNat + (x 5 9 && x 5 11).toNat + (x 4 10 && x 4 12).toNat + (x 3 11 && x 3 13).toNat + (x 2 12 && x 2 14).toNat + (x 1 13).toNat := by have q := hcov2 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r47202 : 1 ≤ (x 3 4).toNat + (x 2 1 && x 2 5).toNat + (x 1 2 && x 1 6).toNat + (x 0 3 && x 0 7).toNat + (x (-1) 4 && x (-1) 8).toNat + (x (-2) 5 && x (-2) 9).toNat + (x (-3) 6 && x (-3) 10).toNat + (x (-4) 7 && x (-4) 11).toNat + (x (-5) 8 && x (-5) 12).toNat + (x (-6) 9 && x (-6) 13).toNat + (x (-7) 10 && x (-7) 14).toNat + (x (-8) 11).toNat := by have q := hcov4 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e47203 : (x 2 1 && x 2 5).toNat = (x 2 5).toNat := handr _ _ (fun h => hp13 2 (hp5 2 (h)))
                    have e47204 : (x (-7) 10 && x (-7) 14).toNat = (x (-7) 10).toNat := handl _ _ (fun h => hp2 (-7) (hp10 (-7) (h)))
                    have r47205 : 1 ≤ (x 7 4).toNat + (x 6 1 && x 6 5).toNat + (x 5 2 && x 5 6).toNat + (x 4 3 && x 4 7).toNat + (x 3 4 && x 3 8).toNat + (x 2 5 && x 2 9).toNat + (x 1 6 && x 1 10).toNat + (x 0 7 && x 0 11).toNat + (x (-1) 8 && x (-1) 12).toNat + (x (-2) 9 && x (-2) 13).toNat + (x (-3) 10 && x (-3) 14).toNat + (x (-4) 11).toNat := by have q := hcov4 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e47206 : (x 6 1 && x 6 5).toNat = (x 6 5).toNat := handr _ _ (fun h => hp13 6 (hp5 6 (h)))
                    have e47207 : (x (-3) 10 && x (-3) 14).toNat = (x (-3) 10).toNat := handl _ _ (fun h => hp2 (-3) (hp10 (-3) (h)))
                    have r47208 : 1 ≤ (x 7 5).toNat + (x 6 1 && x 6 6).toNat + (x 5 2 && x 5 7).toNat + (x 4 3 && x 4 8).toNat + (x 3 4 && x 3 9).toNat + (x 2 5 && x 2 10).toNat + (x 1 6 && x 1 11).toNat + (x 0 7 && x 0 12).toNat + (x (-1) 8 && x (-1) 13).toNat + (x (-2) 9 && x (-2) 14).toNat + (x (-3) 10).toNat := by have q := hcov5 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r47209 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r47210 : 1 ≤ (x 12 10).toNat + (x 11 1 && x 11 11).toNat + (x 10 2 && x 10 12).toNat + (x 9 3 && x 9 13).toNat + (x 8 4 && x 8 14).toNat + (x 7 5).toNat := by have q := hcov10 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r47211 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := by have q := hcov11 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r47212 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r47213 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r47214 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r47215 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r47216 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
                    have r47217 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
                    have r47218 : (x 7 5).toNat ≤ (x 7 13).toNat := himp _ _ (hp5 7)
                    have r47219 : (x 7 9).toNat ≤ (x 7 1).toNat := himp _ _ (hp9 7)
                    have r47220 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
                    have r47221 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
                    have r47222 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
                    have r47223 := hand2 (x 13 1) (x 13 3)
                    have r47224 := hand2 (x 12 2) (x 12 4)
                    have r47225 := hand2 (x 11 3) (x 11 5)
                    have r47226 := hand2 (x 7 7) (x 7 9)
                    have r47227 := hand1 (x (-5) 8) (x (-5) 12)
                    have r47228 := hand1 (x (-6) 9) (x (-6) 13)
                    have r47229 := hand2 (x 4 3) (x 4 7)
                    have r47230 := hand2 (x (-2) 9) (x (-2) 13)
                    have r47231 := hand2 (x 6 1) (x 6 6)
                    have r47232 := hand1 (x (-2) 9) (x (-2) 14)
                    have r47233 := hand2 (x (-4) 3) (x (-4) 12)
                    have r47234 := hand1 (x (-5) 4) (x (-5) 13)
                    have r47235 := hand1 (x (-6) 5) (x (-6) 14)
                    have r47236 := hand1 (x 10 2) (x 10 12)
                    have r47237 := hand1 (x 9 3) (x 9 13)
                    have r47238 := hand1 (x 8 4) (x 8 14)
                    have r47239 := hand2 (x (-9) 1) (x (-9) 12)
                    have r47240 := hand2 (x (-10) 2) (x (-10) 13)
                    have r47241 := hand2 (x (-11) 3) (x (-11) 14)
                    have r47242 := hand2 (x 7 1) (x 7 12)
                    have r47243 := hand1 (x 6 2) (x 6 13)
                    have r47244 := hand2 (x (-6) 1) (x (-6) 14)
                    have r47245 := hand2 (x (-2) 1) (x (-2) 14)
                    have r47246 := hand1 (x 10 1) (x 10 14)
                    have b47257 := hb (x (-7) 14)
                    have b47318 := hb (x 6 1)
                    linarith only [r47172, r47173, r47174, r47175, r47176, r47177, r47178, e47179, e47180, e47181, e47182, e47183, e47184, r47185, e47186, e47187, e47188, e47189, e47190, e47191, r47192, e47193, e47194, r47195, e47196, e47197, r47198, e47199, e47200, r47201, r47202, e47203, e47204, r47205, e47206, e47207, r47208, r47209, r47210, r47211, r47212, r47213, r47214, r47215, r47216, r47217, r47218, r47219, r47220, r47221, r47222, r47223, r47224, r47225, r47226, r47227, r47228, r47229, r47230, r47231, r47232, r47233, r47234, r47235, r47236, r47237, r47238, r47239, r47240, r47241, r47242, r47243, r47244, r47245, r47246, b47257, b47318, g0, g1, g2, g4, g5, g7, g9, f46721, g11, f46878, g14, g15, g17, g18, g19, g20, g23, f46717, g26, f46719, g29, g30, g32, f47080, f47102, g33, f47169, g34, g35, d46712, g37, g38, g39, g41, d47132, d47124, d46773, d46833, d46853, d46873, g53, g54, g55, g56, g57, g62, g63, g64, g65, g66, g67, d47128, g68, g69, g70, g71, d46726, d47144, g74, g75, g76, g77, g78, g79, g96, g97, d46809, d47120]
                  · have f47403 : (x 2 7).toNat = 1 := by rw [h47170]; rfl
                    have d47404 : (x 9 8).toNat = 0 := by
                      have r47405 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e47406 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                      have e47407 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                      have e47408 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                      have e47409 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                      have e47410 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                      have e47411 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                      have b47412 := hb (x 2 7)
                      have b47413 := hb (x 3 6)
                      have b47414 := hb (x 4 5)
                      have b47415 := hb (x 5 4)
                      have b47416 := hb (x 6 11)
                      have b47417 := hb (x 7 10)
                      have b47418 := hb (x 8 9)
                      have b47419 := hb (x 9 8)
                      clear * - r47405 e47406 e47407 e47408 e47409 e47410 e47411 b47412 b47413 b47414 b47415 b47416 b47417 b47418 b47419 d47160 d47093 f47403
                      omega
                    have d47420 : (x 8 9).toNat = 0 := by
                      have r47421 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e47422 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                      have e47423 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                      have e47424 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                      have e47425 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                      have e47426 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                      have e47427 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                      have b47428 := hb (x 2 7)
                      have b47429 := hb (x 3 6)
                      have b47430 := hb (x 4 5)
                      have b47431 := hb (x 5 4)
                      have b47432 := hb (x 6 11)
                      have b47433 := hb (x 7 10)
                      have b47434 := hb (x 8 9)
                      have b47435 := hb (x 9 8)
                      clear * - r47421 e47422 e47423 e47424 e47425 e47426 e47427 b47428 b47429 b47430 b47431 b47432 b47433 b47434 b47435 d47404 d47160 d47093 f47403
                      omega
                    have d47436 : (x 7 10).toNat = 0 := by
                      have r47437 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e47438 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                      have e47439 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                      have e47440 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                      have e47441 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                      have e47442 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                      have e47443 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                      have b47444 := hb (x 2 7)
                      have b47445 := hb (x 3 6)
                      have b47446 := hb (x 4 5)
                      have b47447 := hb (x 5 4)
                      have b47448 := hb (x 6 11)
                      have b47449 := hb (x 7 10)
                      have b47450 := hb (x 8 9)
                      have b47451 := hb (x 9 8)
                      clear * - r47437 e47438 e47439 e47440 e47441 e47442 e47443 b47444 b47445 b47446 b47447 b47448 b47449 b47450 b47451 d47404 d47420 d47160 d47093 f47403
                      omega
                    have d47452 : (x 7 1 && x 7 10).toNat = 0 := by
                      have r47453 := hand2 (x 7 1) (x 7 10)
                      have b47454 := hb (x 7 10)
                      have b47455 := hb (x 7 1 && x 7 10)
                      clear * - r47453 b47454 b47455 d47436
                      omega
                    have d47456 : (x 6 11).toNat = 0 := by
                      have r47457 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e47458 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                      have e47459 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                      have e47460 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                      have e47461 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                      have e47462 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                      have e47463 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                      have b47464 := hb (x 2 7)
                      have b47465 := hb (x 3 6)
                      have b47466 := hb (x 4 5)
                      have b47467 := hb (x 5 4)
                      have b47468 := hb (x 6 11)
                      have b47469 := hb (x 7 10)
                      have b47470 := hb (x 8 9)
                      have b47471 := hb (x 9 8)
                      clear * - r47457 e47458 e47459 e47460 e47461 e47462 e47463 b47464 b47465 b47466 b47467 b47468 b47469 b47470 b47471 d47404 d47420 d47436 d47160 d47093 f47403
                      omega
                    have d47472 : (x 6 1 && x 6 11).toNat = 0 := by
                      have r47473 := hand2 (x 6 1) (x 6 11)
                      have b47474 := hb (x 6 11)
                      have b47475 := hb (x 6 1 && x 6 11)
                      clear * - r47473 b47474 b47475 d47456
                      omega
                    have d47476 : (x 4 3 && x 4 13).toNat = 1 := by
                      have r47477 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b47478 := hb (x 2 5)
                      have b47479 := hb (x 7 10)
                      have b47480 := hb (x 6 1 && x 6 11)
                      have b47481 := hb (x 5 2 && x 5 12)
                      have b47482 := hb (x 4 3 && x 4 13)
                      have b47483 := hb (x 3 4 && x 3 14)
                      clear * - r47477 b47478 b47479 b47480 b47481 b47482 b47483 d47436 d47472 d47136 g102 g33
                      omega
                    have d47484 : (x 4 3).toNat = 1 := by
                      have r47485 := hand1 (x 4 3) (x 4 13)
                      have b47486 := hb (x 4 3)
                      have b47487 := hb (x 4 3 && x 4 13)
                      clear * - r47485 b47486 b47487 d47476
                      omega
                    have d47488 : (x 7 12).toNat = 0 := by
                      have r47489 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e47490 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                      have e47491 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                      have b47492 := hb (x 4 3)
                      have b47493 := hb (x 5 2)
                      have b47494 := hb (x 6 13)
                      have b47495 := hb (x 7 12)
                      clear * - r47489 e47490 e47491 b47492 b47493 b47494 b47495 d47132 d47484
                      omega
                    have d47496 : (x 6 13).toNat = 0 := by
                      have r47497 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e47498 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                      have e47499 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                      have b47500 := hb (x 4 3)
                      have b47501 := hb (x 5 2)
                      have b47502 := hb (x 6 13)
                      have b47503 := hb (x 7 12)
                      clear * - r47497 e47498 e47499 b47500 b47501 b47502 b47503 d47488 d47132 d47484
                      omega
                    have d47504 : (x 4 2).toNat = 1 := by
                      have r47505 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b47506 := hb (x 4 2)
                      have b47507 := hb (x 6 13)
                      have b47508 := hb (x 5 1 && x 5 14)
                      clear * - r47505 b47506 b47507 b47508 d47496 d47116
                      omega
                    have d47509 : (x 4 14).toNat = 1 := by
                      have r47510 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
                      have b47511 := hb (x 4 2)
                      have b47512 := hb (x 4 14)
                      clear * - r47510 b47511 b47512 d47504
                      omega
                    have d47513 : (x 3 1).toNat = 0 := by
                      have r47514 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b47515 := hb (x 3 1)
                      have b47516 := hb (x 4 14)
                      clear * - r47514 b47515 b47516 d47509
                      omega
                    have d47517 : (x 3 13).toNat = 0 := by
                      have r47518 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
                      have b47519 := hb (x 3 1)
                      have b47520 := hb (x 3 13)
                      clear * - r47518 b47519 b47520 d47513
                      omega
                    have d47521 : (x 3 7 && x 3 13).toNat = 0 := by
                      have r47522 := hand2 (x 3 7) (x 3 13)
                      have b47523 := hb (x 3 13)
                      have b47524 := hb (x 3 7 && x 3 13)
                      clear * - r47522 b47523 b47524 d47517
                      omega
                    have d47525 : (x 3 5).toNat = 0 := by
                      have r47526 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
                      have b47527 := hb (x 3 5)
                      have b47528 := hb (x 3 13)
                      clear * - r47526 b47527 b47528 d47517
                      omega
                    have d47529 : (x 4 12).toNat = 1 := by
                      have r47530 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e47531 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                      have e47532 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                      have b47533 := hb (x 1 3)
                      have b47534 := hb (x 2 2)
                      have b47535 := hb (x 3 13)
                      have b47536 := hb (x 4 12)
                      clear * - r47530 e47531 e47532 b47533 b47534 b47535 b47536 d47517 f47102 f46717
                      omega
                    have d47537 : (x 6 12).toNat = 0 := by
                      have r47538 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e47539 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                      have e47540 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                      have b47541 := hb (x 3 3)
                      have b47542 := hb (x 4 2)
                      have b47543 := hb (x 5 13)
                      have b47544 := hb (x 6 12)
                      clear * - r47538 e47539 e47540 b47541 b47542 b47543 b47544 d47504
                      omega
                    have d47545 : (x 6 3 && x 6 12).toNat = 0 := by
                      have r47546 := hand2 (x 6 3) (x 6 12)
                      have b47547 := hb (x 6 12)
                      have b47548 := hb (x 6 3 && x 6 12)
                      clear * - r47546 b47547 b47548 d47537
                      omega
                    have d47549 : (x 6 4).toNat = 0 := by
                      have r47550 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
                      have b47551 := hb (x 6 4)
                      have b47552 := hb (x 6 12)
                      clear * - r47550 b47551 b47552 d47537
                      omega
                    have d47553 : (x 6 4 && x 6 10).toNat = 0 := by
                      have r47554 := hand1 (x 6 4) (x 6 10)
                      have b47555 := hb (x 6 4)
                      have b47556 := hb (x 6 4 && x 6 10)
                      clear * - r47554 b47555 b47556 d47549
                      omega
                    have d47557 : (x 5 13).toNat = 0 := by
                      have r47558 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e47559 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                      have e47560 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                      have b47561 := hb (x 3 3)
                      have b47562 := hb (x 4 2)
                      have b47563 := hb (x 5 13)
                      have b47564 := hb (x 6 12)
                      clear * - r47558 e47559 e47560 b47561 b47562 b47563 b47564 d47537 d47504
                      omega
                    have d47565 : (x 5 5).toNat = 0 := by
                      have r47566 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
                      have b47567 := hb (x 5 5)
                      have b47568 := hb (x 5 13)
                      clear * - r47566 b47567 b47568 d47557
                      omega
                    have d47569 : (x 5 5 && x 5 11).toNat = 0 := by
                      have r47570 := hand1 (x 5 5) (x 5 11)
                      have b47571 := hb (x 5 5)
                      have b47572 := hb (x 5 5 && x 5 11)
                      clear * - r47570 b47571 b47572 d47565
                      omega
                    have d47573 : (x 6 2 && x 6 11).toNat = 0 := by
                      have r47574 := hand2 (x 6 2) (x 6 11)
                      have b47575 := hb (x 6 11)
                      have b47576 := hb (x 6 2 && x 6 11)
                      clear * - r47574 b47575 b47576 d47456
                      omega
                    have d47577 : (x 4 4 && x 4 13).toNat = 1 := by
                      have r47578 : 1 ≤ (x 8 9).toNat + (x 7 1 && x 7 10).toNat + (x 6 2 && x 6 11).toNat + (x 5 3 && x 5 12).toNat + (x 4 4 && x 4 13).toNat + (x 3 5 && x 3 14).toNat + (x 2 6).toNat := by have q := hcov9 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b47579 := hb (x 2 6)
                      have b47580 := hb (x 8 9)
                      have b47581 := hb (x 7 1 && x 7 10)
                      have b47582 := hb (x 6 2 && x 6 11)
                      have b47583 := hb (x 5 3 && x 5 12)
                      have b47584 := hb (x 4 4 && x 4 13)
                      have b47585 := hb (x 3 5 && x 3 14)
                      clear * - r47578 b47579 b47580 b47581 b47582 b47583 b47584 b47585 d47420 d47452 d47573 d47156 d47089 f47169
                      omega
                    have d47586 : (x 4 4).toNat = 1 := by
                      have r47587 := hand1 (x 4 4) (x 4 13)
                      have b47588 := hb (x 4 4)
                      have b47589 := hb (x 4 4 && x 4 13)
                      clear * - r47587 b47588 b47589 d47577
                      omega
                    have d47590 : (x 4 5).toNat = 0 := by
                      have r47591 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e47592 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                      have e47593 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                      have e47594 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                      have e47595 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                      have e47596 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                      have e47597 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                      have b47598 := hb (x 2 7)
                      have b47599 := hb (x 3 6)
                      have b47600 := hb (x 4 5)
                      have b47601 := hb (x 5 4)
                      have b47602 := hb (x 6 11)
                      have b47603 := hb (x 7 10)
                      have b47604 := hb (x 8 9)
                      have b47605 := hb (x 9 8)
                      clear * - r47591 e47592 e47593 e47594 e47595 e47596 e47597 b47598 b47599 b47600 b47601 b47602 b47603 b47604 b47605 d47404 d47420 d47436 d47456 d47160 d47093 f47403
                      omega
                    have d47606 : (x 4 5 && x 4 14).toNat = 0 := by
                      have r47607 := hand1 (x 4 5) (x 4 14)
                      have b47608 := hb (x 4 5)
                      have b47609 := hb (x 4 5 && x 4 14)
                      clear * - r47607 b47608 b47609 d47590
                      omega
                    have d47610 : (x 8 8).toNat = 0 := by
                      have r47611 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e47612 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                      have e47613 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                      have e47614 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                      have e47615 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                      have e47616 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                      have e47617 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                      have b47618 := hb (x 1 7)
                      have b47619 := hb (x 2 6)
                      have b47620 := hb (x 3 5)
                      have b47621 := hb (x 4 4)
                      have b47622 := hb (x 5 11)
                      have b47623 := hb (x 6 10)
                      have b47624 := hb (x 7 9)
                      have b47625 := hb (x 8 8)
                      clear * - r47611 e47612 e47613 e47614 e47615 e47616 e47617 b47618 b47619 b47620 b47621 b47622 b47623 b47624 b47625 d47586 d47525 f47169 f46719
                      omega
                    have d47626 : (x 8 2 && x 8 8).toNat = 0 := by
                      have r47627 := hand2 (x 8 2) (x 8 8)
                      have b47628 := hb (x 8 8)
                      have b47629 := hb (x 8 2 && x 8 8)
                      clear * - r47627 b47628 b47629 d47610
                      omega
                    have d47630 : (x 7 9).toNat = 0 := by
                      have r47631 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e47632 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                      have e47633 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                      have e47634 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                      have e47635 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                      have e47636 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                      have e47637 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                      have b47638 := hb (x 1 7)
                      have b47639 := hb (x 2 6)
                      have b47640 := hb (x 3 5)
                      have b47641 := hb (x 4 4)
                      have b47642 := hb (x 5 11)
                      have b47643 := hb (x 6 10)
                      have b47644 := hb (x 7 9)
                      have b47645 := hb (x 8 8)
                      clear * - r47631 e47632 e47633 e47634 e47635 e47636 e47637 b47638 b47639 b47640 b47641 b47642 b47643 b47644 b47645 d47610 d47586 d47525 f47169 f46719
                      omega
                    have d47646 : (x 7 3 && x 7 9).toNat = 0 := by
                      have r47647 := hand2 (x 7 3) (x 7 9)
                      have b47648 := hb (x 7 9)
                      have b47649 := hb (x 7 3 && x 7 9)
                      clear * - r47647 b47648 b47649 d47630
                      omega
                    have d47650 : (x 7 7 && x 7 9).toNat = 0 := by
                      have r47651 := hand2 (x 7 7) (x 7 9)
                      have b47652 := hb (x 7 9)
                      have b47653 := hb (x 7 7 && x 7 9)
                      clear * - r47651 b47652 b47653 d47630
                      omega
                    have d47654 : (x 6 10).toNat = 0 := by
                      have r47655 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e47656 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                      have e47657 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                      have e47658 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                      have e47659 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                      have e47660 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                      have e47661 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                      have b47662 := hb (x 1 7)
                      have b47663 := hb (x 2 6)
                      have b47664 := hb (x 3 5)
                      have b47665 := hb (x 4 4)
                      have b47666 := hb (x 5 11)
                      have b47667 := hb (x 6 10)
                      have b47668 := hb (x 7 9)
                      have b47669 := hb (x 8 8)
                      clear * - r47655 e47656 e47657 e47658 e47659 e47660 e47661 b47662 b47663 b47664 b47665 b47666 b47667 b47668 b47669 d47610 d47630 d47586 d47525 f47169 f46719
                      omega
                    have d47670 : (x 5 11).toNat = 0 := by
                      have r47671 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e47672 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                      have e47673 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                      have e47674 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                      have e47675 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                      have e47676 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                      have e47677 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                      have b47678 := hb (x 1 7)
                      have b47679 := hb (x 2 6)
                      have b47680 := hb (x 3 5)
                      have b47681 := hb (x 4 4)
                      have b47682 := hb (x 5 11)
                      have b47683 := hb (x 6 10)
                      have b47684 := hb (x 7 9)
                      have b47685 := hb (x 8 8)
                      clear * - r47671 e47672 e47673 e47674 e47675 e47676 e47677 b47678 b47679 b47680 b47681 b47682 b47683 b47684 b47685 d47610 d47630 d47654 d47586 d47525 f47169 f46719
                      omega
                    have r47686 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r47687 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e47688 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                    have e47689 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                    have e47690 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                    have e47691 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                    have e47692 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                    have e47693 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                    have r47694 : 1 ≤ (x 14 2).toNat + (x 13 1 && x 13 3).toNat + (x 12 2 && x 12 4).toNat + (x 11 3 && x 11 5).toNat + (x 10 4 && x 10 6).toNat + (x 9 5 && x 9 7).toNat + (x 8 6 && x 8 8).toNat + (x 7 7 && x 7 9).toNat + (x 6 8 && x 6 10).toNat + (x 5 9 && x 5 11).toNat + (x 4 10 && x 4 12).toNat + (x 3 11 && x 3 13).toNat + (x 2 12 && x 2 14).toNat + (x 1 13).toNat := by have q := hcov2 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r47695 : 1 ≤ (x 10 6).toNat + (x 9 1 && x 9 7).toNat + (x 8 2 && x 8 8).toNat + (x 7 3 && x 7 9).toNat + (x 6 4 && x 6 10).toNat + (x 5 5 && x 5 11).toNat + (x 4 6 && x 4 12).toNat + (x 3 7 && x 3 13).toNat + (x 2 8 && x 2 14).toNat + (x 1 9).toNat := by have q := hcov6 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r47696 : 1 ≤ (x 9 9).toNat + (x 8 1 && x 8 10).toNat + (x 7 2 && x 7 11).toNat + (x 6 3 && x 6 12).toNat + (x 5 4 && x 5 13).toNat + (x 4 5 && x 4 14).toNat + (x 3 6).toNat := by have q := hcov9 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r47697 := hand2 (x 13 1) (x 13 3)
                    have r47698 := hand2 (x 12 2) (x 12 4)
                    have r47699 := hand2 (x 11 3) (x 11 5)
                    have r47700 := hand2 (x 9 1) (x 9 7)
                    have r47701 := hand1 (x 4 6) (x 4 12)
                    have r47702 := hand2 (x 8 1) (x 8 10)
                    have r47703 := hand2 (x 7 2) (x 7 11)
                    linarith only [r47686, r47687, e47688, e47689, e47690, e47691, e47692, e47693, r47694, r47695, r47696, r47697, r47698, r47699, r47700, r47701, r47702, r47703, g28, g32, d46712, d47093, d47517, d47529, d47565, d47670, d47549, d47654, d47630, d47610, d46833, d46853, d46873, d47650, g53, g54, g55, g56, g57, d47626, d47646, d47553, d47569, d47521, g88, d47545, d47164, d47606]
                · have f47754 : (x 2 6).toNat = 1 := by rw [h47168]; rfl
                  have d47755 : (x 8 8).toNat = 0 := by
                    have r47756 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e47757 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                    have e47758 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                    have e47759 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                    have e47760 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                    have e47761 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                    have e47762 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                    have b47763 := hb (x 1 7)
                    have b47764 := hb (x 2 6)
                    have b47765 := hb (x 3 5)
                    have b47766 := hb (x 4 4)
                    have b47767 := hb (x 5 11)
                    have b47768 := hb (x 6 10)
                    have b47769 := hb (x 7 9)
                    have b47770 := hb (x 8 8)
                    clear * - r47756 e47757 e47758 e47759 e47760 e47761 e47762 b47763 b47764 b47765 b47766 b47767 b47768 b47769 b47770 f47754 f46719
                    omega
                  have d47771 : (x 8 2 && x 8 8).toNat = 0 := by
                    have r47772 := hand2 (x 8 2) (x 8 8)
                    have b47773 := hb (x 8 8)
                    have b47774 := hb (x 8 2 && x 8 8)
                    clear * - r47772 b47773 b47774 d47755
                    omega
                  have d47775 : (x 7 9).toNat = 0 := by
                    have r47776 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e47777 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                    have e47778 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                    have e47779 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                    have e47780 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                    have e47781 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                    have e47782 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                    have b47783 := hb (x 1 7)
                    have b47784 := hb (x 2 6)
                    have b47785 := hb (x 3 5)
                    have b47786 := hb (x 4 4)
                    have b47787 := hb (x 5 11)
                    have b47788 := hb (x 6 10)
                    have b47789 := hb (x 7 9)
                    have b47790 := hb (x 8 8)
                    clear * - r47776 e47777 e47778 e47779 e47780 e47781 e47782 b47783 b47784 b47785 b47786 b47787 b47788 b47789 b47790 d47755 f47754 f46719
                    omega
                  have d47791 : (x 7 3 && x 7 9).toNat = 0 := by
                    have r47792 := hand2 (x 7 3) (x 7 9)
                    have b47793 := hb (x 7 9)
                    have b47794 := hb (x 7 3 && x 7 9)
                    clear * - r47792 b47793 b47794 d47775
                    omega
                  have d47795 : (x 7 7 && x 7 9).toNat = 0 := by
                    have r47796 := hand2 (x 7 7) (x 7 9)
                    have b47797 := hb (x 7 9)
                    have b47798 := hb (x 7 7 && x 7 9)
                    clear * - r47796 b47797 b47798 d47775
                    omega
                  have d47799 : (x 6 10).toNat = 0 := by
                    have r47800 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e47801 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                    have e47802 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                    have e47803 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                    have e47804 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                    have e47805 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                    have e47806 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                    have b47807 := hb (x 1 7)
                    have b47808 := hb (x 2 6)
                    have b47809 := hb (x 3 5)
                    have b47810 := hb (x 4 4)
                    have b47811 := hb (x 5 11)
                    have b47812 := hb (x 6 10)
                    have b47813 := hb (x 7 9)
                    have b47814 := hb (x 8 8)
                    clear * - r47800 e47801 e47802 e47803 e47804 e47805 e47806 b47807 b47808 b47809 b47810 b47811 b47812 b47813 b47814 d47755 d47775 f47754 f46719
                    omega
                  have d47815 : (x 6 1 && x 6 10).toNat = 0 := by
                    have r47816 := hand2 (x 6 1) (x 6 10)
                    have b47817 := hb (x 6 10)
                    have b47818 := hb (x 6 1 && x 6 10)
                    clear * - r47816 b47817 b47818 d47799
                    omega
                  have d47819 : (x 4 3 && x 4 12).toNat = 1 := by
                    have r47820 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b47821 := hb (x 1 6)
                    have b47822 := hb (x 7 9)
                    have b47823 := hb (x 6 1 && x 6 10)
                    have b47824 := hb (x 5 2 && x 5 11)
                    have b47825 := hb (x 4 3 && x 4 12)
                    have b47826 := hb (x 3 4 && x 3 13)
                    have b47827 := hb (x 2 5 && x 2 14)
                    clear * - r47820 b47821 b47822 b47823 b47824 b47825 b47826 b47827 d47775 d47815 d47140 g98 g99 g26
                    omega
                  have d47828 : (x 4 12).toNat = 1 := by
                    have r47829 := hand2 (x 4 3) (x 4 12)
                    have b47830 := hb (x 4 12)
                    have b47831 := hb (x 4 3 && x 4 12)
                    clear * - r47829 b47830 b47831 d47819
                    omega
                  have d47832 : (x 3 13).toNat = 0 := by
                    have r47833 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e47834 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                    have e47835 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                    have b47836 := hb (x 1 3)
                    have b47837 := hb (x 2 2)
                    have b47838 := hb (x 3 13)
                    have b47839 := hb (x 4 12)
                    clear * - r47833 e47834 e47835 b47836 b47837 b47838 b47839 d47828 f47102 f46717
                    omega
                  have d47840 : (x 3 7 && x 3 13).toNat = 0 := by
                    have r47841 := hand2 (x 3 7) (x 3 13)
                    have b47842 := hb (x 3 13)
                    have b47843 := hb (x 3 7 && x 3 13)
                    clear * - r47841 b47842 b47843 d47832
                    omega
                  have d47844 : (x 3 5).toNat = 0 := by
                    have r47845 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
                    have b47846 := hb (x 3 5)
                    have b47847 := hb (x 3 13)
                    clear * - r47845 b47846 b47847 d47832
                    omega
                  have d47848 : (x 4 3).toNat = 1 := by
                    have r47849 := hand1 (x 4 3) (x 4 12)
                    have b47850 := hb (x 4 3)
                    have b47851 := hb (x 4 3 && x 4 12)
                    clear * - r47849 b47850 b47851 d47819
                    omega
                  have d47852 : (x 7 12).toNat = 0 := by
                    have r47853 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e47854 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                    have e47855 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                    have b47856 := hb (x 4 3)
                    have b47857 := hb (x 5 2)
                    have b47858 := hb (x 6 13)
                    have b47859 := hb (x 7 12)
                    clear * - r47853 e47854 e47855 b47856 b47857 b47858 b47859 d47132 d47848
                    omega
                  have d47860 : (x 6 13).toNat = 0 := by
                    have r47861 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e47862 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                    have e47863 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                    have b47864 := hb (x 4 3)
                    have b47865 := hb (x 5 2)
                    have b47866 := hb (x 6 13)
                    have b47867 := hb (x 7 12)
                    clear * - r47861 e47862 e47863 b47864 b47865 b47866 b47867 d47852 d47132 d47848
                    omega
                  have d47868 : (x 4 2).toNat = 1 := by
                    have r47869 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b47870 := hb (x 4 2)
                    have b47871 := hb (x 6 13)
                    have b47872 := hb (x 5 1 && x 5 14)
                    clear * - r47869 b47870 b47871 b47872 d47860 d47116
                    omega
                  have d47873 : (x 6 12).toNat = 0 := by
                    have r47874 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e47875 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                    have e47876 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                    have b47877 := hb (x 3 3)
                    have b47878 := hb (x 4 2)
                    have b47879 := hb (x 5 13)
                    have b47880 := hb (x 6 12)
                    clear * - r47874 e47875 e47876 b47877 b47878 b47879 b47880 d47868
                    omega
                  have d47881 : (x 6 2 && x 6 12).toNat = 0 := by
                    have r47882 := hand2 (x 6 2) (x 6 12)
                    have b47883 := hb (x 6 12)
                    have b47884 := hb (x 6 2 && x 6 12)
                    clear * - r47882 b47883 b47884 d47873
                    omega
                  have d47885 : (x 6 4).toNat = 0 := by
                    have r47886 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
                    have b47887 := hb (x 6 4)
                    have b47888 := hb (x 6 12)
                    clear * - r47886 b47887 b47888 d47873
                    omega
                  have d47889 : (x 6 4 && x 6 10).toNat = 0 := by
                    have r47890 := hand1 (x 6 4) (x 6 10)
                    have b47891 := hb (x 6 4)
                    have b47892 := hb (x 6 4 && x 6 10)
                    clear * - r47890 b47891 b47892 d47885
                    omega
                  have d47893 : (x 5 13).toNat = 0 := by
                    have r47894 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e47895 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                    have e47896 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                    have b47897 := hb (x 3 3)
                    have b47898 := hb (x 4 2)
                    have b47899 := hb (x 5 13)
                    have b47900 := hb (x 6 12)
                    clear * - r47894 e47895 e47896 b47897 b47898 b47899 b47900 d47873 d47868
                    omega
                  have d47901 : (x 5 3 && x 5 13).toNat = 0 := by
                    have r47902 := hand2 (x 5 3) (x 5 13)
                    have b47903 := hb (x 5 13)
                    have b47904 := hb (x 5 3 && x 5 13)
                    clear * - r47902 b47903 b47904 d47893
                    omega
                  have d47905 : (x 5 5).toNat = 0 := by
                    have r47906 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
                    have b47907 := hb (x 5 5)
                    have b47908 := hb (x 5 13)
                    clear * - r47906 b47907 b47908 d47893
                    omega
                  have d47909 : (x 5 5 && x 5 11).toNat = 0 := by
                    have r47910 := hand1 (x 5 5) (x 5 11)
                    have b47911 := hb (x 5 5)
                    have b47912 := hb (x 5 5 && x 5 11)
                    clear * - r47910 b47911 b47912 d47905
                    omega
                  have d47913 : (x 5 11).toNat = 0 := by
                    have r47914 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e47915 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                    have e47916 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                    have e47917 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                    have e47918 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                    have e47919 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                    have e47920 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                    have b47921 := hb (x 1 7)
                    have b47922 := hb (x 2 6)
                    have b47923 := hb (x 3 5)
                    have b47924 := hb (x 4 4)
                    have b47925 := hb (x 5 11)
                    have b47926 := hb (x 6 10)
                    have b47927 := hb (x 7 9)
                    have b47928 := hb (x 8 8)
                    clear * - r47914 e47915 e47916 e47917 e47918 e47919 e47920 b47921 b47922 b47923 b47924 b47925 b47926 b47927 b47928 d47755 d47775 d47799 d47844 f47754 f46719
                    omega
                  have d47929 : (x 4 4).toNat = 0 := by
                    have r47930 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e47931 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                    have e47932 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                    have e47933 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                    have e47934 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                    have e47935 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                    have e47936 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                    have b47937 := hb (x 1 7)
                    have b47938 := hb (x 2 6)
                    have b47939 := hb (x 3 5)
                    have b47940 := hb (x 4 4)
                    have b47941 := hb (x 5 11)
                    have b47942 := hb (x 6 10)
                    have b47943 := hb (x 7 9)
                    have b47944 := hb (x 8 8)
                    clear * - r47930 e47931 e47932 e47933 e47934 e47935 e47936 b47937 b47938 b47939 b47940 b47941 b47942 b47943 b47944 d47755 d47775 d47799 d47913 d47844 f47754 f46719
                    omega
                  have d47945 : (x 4 4 && x 4 14).toNat = 0 := by
                    have r47946 := hand1 (x 4 4) (x 4 14)
                    have b47947 := hb (x 4 4)
                    have b47948 := hb (x 4 4 && x 4 14)
                    clear * - r47946 b47947 b47948 d47929
                    omega
                  have r47949 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r47950 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e47951 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                  have e47952 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                  have e47953 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                  have e47954 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                  have e47955 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                  have e47956 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                  have r47957 : 1 ≤ (x 14 2).toNat + (x 13 1 && x 13 3).toNat + (x 12 2 && x 12 4).toNat + (x 11 3 && x 11 5).toNat + (x 10 4 && x 10 6).toNat + (x 9 5 && x 9 7).toNat + (x 8 6 && x 8 8).toNat + (x 7 7 && x 7 9).toNat + (x 6 8 && x 6 10).toNat + (x 5 9 && x 5 11).toNat + (x 4 10 && x 4 12).toNat + (x 3 11 && x 3 13).toNat + (x 2 12 && x 2 14).toNat + (x 1 13).toNat := by have q := hcov2 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r47958 : 1 ≤ (x 10 6).toNat + (x 9 1 && x 9 7).toNat + (x 8 2 && x 8 8).toNat + (x 7 3 && x 7 9).toNat + (x 6 4 && x 6 10).toNat + (x 5 5 && x 5 11).toNat + (x 4 6 && x 4 12).toNat + (x 3 7 && x 3 13).toNat + (x 2 8 && x 2 14).toNat + (x 1 9).toNat := by have q := hcov6 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r47959 : 1 ≤ (x 8 10).toNat + (x 7 1 && x 7 11).toNat + (x 6 2 && x 6 12).toNat + (x 5 3 && x 5 13).toNat + (x 4 4 && x 4 14).toNat + (x 3 5).toNat := by have q := hcov10 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r47960 := hand2 (x 13 1) (x 13 3)
                  have r47961 := hand2 (x 12 2) (x 12 4)
                  have r47962 := hand2 (x 11 3) (x 11 5)
                  have r47963 := hand2 (x 9 1) (x 9 7)
                  have r47964 := hand1 (x 4 6) (x 4 12)
                  have r47965 := hand2 (x 7 1) (x 7 11)
                  linarith only [r47949, r47950, e47951, e47952, e47953, e47954, e47955, e47956, r47957, r47958, r47959, r47960, r47961, r47962, r47963, r47964, r47965, g28, g32, d46712, d47844, d47832, d47828, d47905, d47913, d47885, d47799, d47775, d47755, d46833, d46853, d46873, d47795, g53, g54, g55, g56, g57, d47771, d47791, d47889, d47909, d47840, g88, d47881, d47901, d47945]
              · have f48015 : (x 2 2).toNat = 1 := by rw [h47101]; rfl
                have r48016 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r48017 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r48018 : (x (-5) 8).toNat + (x (-6) 1 && x (-6) 9).toNat + (x (-7) 2 && x (-7) 10).toNat + (x (-8) 3 && x (-8) 11).toNat + (x (-9) 4 && x (-9) 12).toNat + (x (-10) 5 && x (-10) 13).toNat + (x (-11) 6 && x (-11) 14).toNat + (x (-12) 7).toNat = 1 := by have q := hd8 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e48019 : (x (-6) 1 && x (-6) 9).toNat = (x (-6) 9).toNat := handr _ _ (fun h => hp9 (-6) (h))
                have e48020 : (x (-7) 2 && x (-7) 10).toNat = (x (-7) 10).toNat := handr _ _ (fun h => hp10 (-7) (h))
                have e48021 : (x (-8) 3 && x (-8) 11).toNat = (x (-8) 11).toNat := handr _ _ (fun h => hp11 (-8) (h))
                have e48022 : (x (-9) 4 && x (-9) 12).toNat = (x (-9) 4).toNat := handl _ _ (fun h => hp4 (-9) (h))
                have e48023 : (x (-10) 5 && x (-10) 13).toNat = (x (-10) 5).toNat := handl _ _ (fun h => hp5 (-10) (h))
                have e48024 : (x (-11) 6 && x (-11) 14).toNat = (x (-11) 6).toNat := handl _ _ (fun h => hp6 (-11) (h))
                have r48025 : 1 ≤ (x 3 4).toNat + (x 2 1 && x 2 5).toNat + (x 1 2 && x 1 6).toNat + (x 0 3 && x 0 7).toNat + (x (-1) 4 && x (-1) 8).toNat + (x (-2) 5 && x (-2) 9).toNat + (x (-3) 6 && x (-3) 10).toNat + (x (-4) 7 && x (-4) 11).toNat + (x (-5) 8 && x (-5) 12).toNat + (x (-6) 9 && x (-6) 13).toNat + (x (-7) 10 && x (-7) 14).toNat + (x (-8) 11).toNat := by have q := hcov4 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e48026 : (x 2 1 && x 2 5).toNat = (x 2 5).toNat := handr _ _ (fun h => hp13 2 (hp5 2 (h)))
                have e48027 : (x (-7) 10 && x (-7) 14).toNat = (x (-7) 10).toNat := handl _ _ (fun h => hp2 (-7) (hp10 (-7) (h)))
                have r48028 : 1 ≤ (x (-5) 9).toNat + (x (-6) 1 && x (-6) 10).toNat + (x (-7) 2 && x (-7) 11).toNat + (x (-8) 3 && x (-8) 12).toNat + (x (-9) 4 && x (-9) 13).toNat + (x (-10) 5 && x (-10) 14).toNat + (x (-11) 6).toNat := by have q := hcov9 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r48029 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r48030 : (x (-11) 2).toNat ≤ (x (-11) 14).toNat := himp _ _ (hp2 (-11))
                have r48031 := hand1 (x (-5) 8) (x (-5) 12)
                have r48032 := hand1 (x (-6) 9) (x (-6) 13)
                have r48033 := hand2 (x (-6) 1) (x (-6) 10)
                have r48034 := hand2 (x (-7) 2) (x (-7) 11)
                have r48035 := hand2 (x (-8) 3) (x (-8) 12)
                have r48036 := hand1 (x (-9) 4) (x (-9) 13)
                have r48037 := hand1 (x (-10) 5) (x (-10) 14)
                have r48038 := hand2 (x (-10) 1) (x (-10) 14)
                linarith only [r48016, r48017, r48018, e48019, e48020, e48021, e48022, e48023, e48024, r48025, e48026, e48027, r48028, r48029, r48030, r48031, r48032, r48033, r48034, r48035, r48036, r48037, r48038, g1, g2, g3, g5, g6, g9, g10, g15, g16, g23, f46717, f47080, f48015, g33, g37, g62, g63, g64, g65, g66, g67]
          · have f48088 : (x (-1) 14).toNat = 1 := by rw [h46879]; rfl
            have d48089 : (x (-2) 1).toNat = 0 := by
              have r48090 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b48091 := hb (x (-2) 1)
              have b48092 := hb (x (-1) 14)
              clear * - r48090 b48091 b48092 f48088
              omega
            have d48093 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
              have r48094 := hand1 (x (-2) 1) (x (-2) 14)
              have b48095 := hb (x (-2) 1)
              have b48096 := hb (x (-2) 1 && x (-2) 14)
              clear * - r48094 b48095 b48096 d48089
              omega
            have d48097 : (x (-2) 13).toNat = 0 := by
              have r48098 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
              have b48099 := hb (x (-2) 1)
              have b48100 := hb (x (-2) 13)
              clear * - r48098 b48099 b48100 d48089
              omega
            have d48101 : (x (-2) 9 && x (-2) 13).toNat = 0 := by
              have r48102 := hand2 (x (-2) 9) (x (-2) 13)
              have b48103 := hb (x (-2) 13)
              have b48104 := hb (x (-2) 9 && x (-2) 13)
              clear * - r48102 b48103 b48104 d48097
              omega
            have d48105 : (x (-2) 9).toNat = 0 := by
              have r48106 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
              have b48107 := hb (x (-2) 1)
              have b48108 := hb (x (-2) 9)
              clear * - r48106 b48107 b48108 d48089
              omega
            have d48109 : (x (-3) 2).toNat = 1 := by
              have r48110 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b48111 := hb (x (-3) 2)
              have b48112 := hb (x (-1) 13)
              have b48113 := hb (x (-2) 1 && x (-2) 14)
              clear * - r48110 b48111 b48112 b48113 g14 d48093
              omega
            have d48114 : (x (-3) 14).toNat = 1 := by
              have r48115 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
              have b48116 := hb (x (-3) 2)
              have b48117 := hb (x (-3) 14)
              clear * - r48115 b48116 b48117 d48109
              omega
            have d48118 : (x (-4) 3).toNat = 0 := by
              have r48119 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e48120 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e48121 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b48122 := hb (x (-4) 3)
              have b48123 := hb (x (-3) 2)
              have b48124 := hb (x (-2) 13)
              have b48125 := hb (x (-1) 12)
              clear * - r48119 e48120 e48121 b48122 b48123 b48124 b48125 f46878 d48097 d48109
              omega
            have d48126 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
              have r48127 := hand1 (x (-4) 3) (x (-4) 12)
              have b48128 := hb (x (-4) 3)
              have b48129 := hb (x (-4) 3 && x (-4) 12)
              clear * - r48127 b48128 b48129 d48118
              omega
            have d48130 : (x (-4) 11).toNat = 0 := by
              have r48131 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
              have b48132 := hb (x (-4) 3)
              have b48133 := hb (x (-4) 11)
              clear * - r48131 b48132 b48133 d48118
              omega
            have r48134 : (x 6 1).toNat + (x 5 2).toNat + (x 4 3).toNat + (x 3 4).toNat + (x 2 5).toNat + (x 1 6).toNat + (x 0 7).toNat + (x (-1) 8).toNat + (x (-2) 9).toNat + (x (-3) 10).toNat + (x (-4) 11).toNat + (x (-5) 12).toNat + (x (-6) 13).toNat + (x (-7) 14).toNat = 3 := by have q := hcount 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r48135 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r48136 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r48137 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e48138 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e48139 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e48140 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e48141 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e48142 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e48143 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have r48144 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e48145 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
            have e48146 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
            have r48147 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e48148 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
            have e48149 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
            have r48150 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r48151 : 1 ≤ (x 7 4).toNat + (x 6 1 && x 6 5).toNat + (x 5 2 && x 5 6).toNat + (x 4 3 && x 4 7).toNat + (x 3 4 && x 3 8).toNat + (x 2 5 && x 2 9).toNat + (x 1 6 && x 1 10).toNat + (x 0 7 && x 0 11).toNat + (x (-1) 8 && x (-1) 12).toNat + (x (-2) 9 && x (-2) 13).toNat + (x (-3) 10 && x (-3) 14).toNat + (x (-4) 11).toNat := by have q := hcov4 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e48152 : (x 6 1 && x 6 5).toNat = (x 6 5).toNat := handr _ _ (fun h => hp13 6 (hp5 6 (h)))
            have e48153 : (x (-3) 10 && x (-3) 14).toNat = (x (-3) 10).toNat := handl _ _ (fun h => hp2 (-3) (hp10 (-3) (h)))
            have r48154 : 1 ≤ (x 7 6).toNat + (x 6 1 && x 6 7).toNat + (x 5 2 && x 5 8).toNat + (x 4 3 && x 4 9).toNat + (x 3 4 && x 3 10).toNat + (x 2 5 && x 2 11).toNat + (x 1 6 && x 1 12).toNat + (x 0 7 && x 0 13).toNat + (x (-1) 8 && x (-1) 14).toNat + (x (-2) 9).toNat := by have q := hcov6 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r48155 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r48156 : 1 ≤ (x 13 9).toNat + (x 12 1 && x 12 10).toNat + (x 11 2 && x 11 11).toNat + (x 10 3 && x 10 12).toNat + (x 9 4 && x 9 13).toNat + (x 8 5 && x 8 14).toNat + (x 7 6).toNat := by have q := hcov9 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r48157 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r48158 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
            have r48159 : (x 7 6).toNat ≤ (x 7 14).toNat := himp _ _ (hp6 7)
            have r48160 := hand2 (x 5 2) (x 5 6)
            have r48161 := hand2 (x 4 3) (x 4 7)
            have r48162 := hand2 (x 6 1) (x 6 7)
            have r48163 := hand1 (x (-5) 4) (x (-5) 13)
            have r48164 := hand1 (x (-6) 5) (x (-6) 14)
            have r48165 := hand1 (x 10 3) (x 10 12)
            have r48166 := hand1 (x 9 4) (x 9 13)
            have r48167 := hand1 (x 8 5) (x 8 14)
            have r48168 := hand1 (x 10 1) (x 10 12)
            have r48169 := hand1 (x 9 2) (x 9 13)
            have r48170 := hand1 (x 8 3) (x 8 14)
            have b48175 := hb (x (-7) 14)
            linarith only [r48134, r48135, r48136, r48137, e48138, e48139, e48140, e48141, e48142, e48143, r48144, e48145, e48146, r48147, e48148, e48149, r48150, r48151, e48152, e48153, r48154, r48155, r48156, r48157, r48158, r48159, r48160, r48161, r48162, r48163, r48164, r48165, r48166, r48167, r48168, r48169, r48170, b48175, d48130, d48114, d48105, d48097, f46721, g11, f46878, f48088, g17, g19, g21, g26, g29, g31, g33, g34, g36, g37, g38, g40, g42, g43, d46793, d46757, g68, g69, g70, g71, d46726, d48101, g82, g83, g84, g85, g86, g87, d46722, g96, g97, d48126, d46789, d46813]
        · have f48254 : (x (-1) 12).toNat = 1 := by rw [h46877]; rfl
          have d48255 : (x (-2) 13).toNat = 0 := by
            have r48256 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e48257 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e48258 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b48259 := hb (x (-4) 3)
            have b48260 := hb (x (-3) 2)
            have b48261 := hb (x (-2) 13)
            have b48262 := hb (x (-1) 12)
            clear * - r48256 e48257 e48258 b48259 b48260 b48261 b48262 f48254
            omega
          have d48263 : (x (-3) 2).toNat = 0 := by
            have r48264 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e48265 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e48266 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b48267 := hb (x (-4) 3)
            have b48268 := hb (x (-3) 2)
            have b48269 := hb (x (-2) 13)
            have b48270 := hb (x (-1) 12)
            clear * - r48264 e48265 e48266 b48267 b48268 b48269 b48270 f48254 d48255
            omega
          have d48271 : (x (-3) 2 && x (-3) 13).toNat = 0 := by
            have r48272 := hand1 (x (-3) 2) (x (-3) 13)
            have b48273 := hb (x (-3) 2)
            have b48274 := hb (x (-3) 2 && x (-3) 13)
            clear * - r48272 b48273 b48274 d48263
            omega
          have d48275 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
            have r48276 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b48277 := hb (x (-3) 2)
            have b48278 := hb (x (-1) 13)
            have b48279 := hb (x (-2) 1 && x (-2) 14)
            clear * - r48276 b48277 b48278 b48279 g14 d48263
            omega
          have d48280 : (x (-2) 14).toNat = 1 := by
            have r48281 := hand2 (x (-2) 1) (x (-2) 14)
            have b48282 := hb (x (-2) 14)
            have b48283 := hb (x (-2) 1 && x (-2) 14)
            clear * - r48281 b48282 b48283 d48275
            omega
          have d48284 : (x (-3) 1).toNat = 0 := by
            have r48285 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b48286 := hb (x (-3) 1)
            have b48287 := hb (x (-2) 14)
            clear * - r48285 b48286 b48287 d48280
            omega
          have d48288 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
            have r48289 := hand1 (x (-3) 1) (x (-3) 14)
            have b48290 := hb (x (-3) 1)
            have b48291 := hb (x (-3) 1 && x (-3) 14)
            clear * - r48289 b48290 b48291 d48284
            omega
          have d48292 : (x (-4) 2).toNat = 1 := by
            have r48293 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b48294 := hb (x (-4) 2)
            have b48295 := hb (x (-2) 13)
            have b48296 := hb (x (-3) 1 && x (-3) 14)
            clear * - r48293 b48294 b48295 b48296 d48255 d48288
            omega
          have d48297 : (x (-4) 14).toNat = 1 := by
            have r48298 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
            have b48299 := hb (x (-4) 2)
            have b48300 := hb (x (-4) 14)
            clear * - r48298 b48299 b48300 d48292
            omega
          have d48301 : (x (-5) 1).toNat = 0 := by
            have r48302 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b48303 := hb (x (-5) 1)
            have b48304 := hb (x (-4) 14)
            clear * - r48302 b48303 b48304 d48297
            omega
          have d48305 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
            have r48306 := hand1 (x (-5) 1) (x (-5) 12)
            have b48307 := hb (x (-5) 1)
            have b48308 := hb (x (-5) 1 && x (-5) 12)
            clear * - r48306 b48307 b48308 d48301
            omega
          have d48309 : (x (-5) 13).toNat = 0 := by
            have r48310 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
            have b48311 := hb (x (-5) 1)
            have b48312 := hb (x (-5) 13)
            clear * - r48310 b48311 b48312 d48301
            omega
          have d48313 : (x (-3) 13).toNat = 0 := by
            have r48314 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
            have b48315 := hb (x (-3) 1)
            have b48316 := hb (x (-3) 13)
            clear * - r48314 b48315 b48316 d48284
            omega
          have d48317 : (x (-4) 3).toNat = 0 := by
            have r48318 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e48319 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e48320 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b48321 := hb (x (-4) 3)
            have b48322 := hb (x (-3) 2)
            have b48323 := hb (x (-2) 13)
            have b48324 := hb (x (-1) 12)
            clear * - r48318 e48319 e48320 b48321 b48322 b48323 b48324 f48254 d48255 d48263
            omega
          have d48325 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
            have r48326 := hand1 (x (-4) 3) (x (-4) 14)
            have b48327 := hb (x (-4) 3)
            have b48328 := hb (x (-4) 3 && x (-4) 14)
            clear * - r48326 b48327 b48328 d48317
            omega
          have d48329 : (x (-4) 11).toNat = 0 := by
            have r48330 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
            have b48331 := hb (x (-4) 3)
            have b48332 := hb (x (-4) 11)
            clear * - r48330 b48331 b48332 d48317
            omega
          have d48333 : (x (-2) 12).toNat = 0 := by
            have r48334 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e48335 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
            have e48336 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
            have b48337 := hb (x (-5) 3)
            have b48338 := hb (x (-4) 2)
            have b48339 := hb (x (-3) 13)
            have b48340 := hb (x (-2) 12)
            clear * - r48334 e48335 e48336 b48337 b48338 b48339 b48340 d48313 d48292
            omega
          have d48341 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
            have r48342 := hand2 (x (-2) 1) (x (-2) 12)
            have b48343 := hb (x (-2) 12)
            have b48344 := hb (x (-2) 1 && x (-2) 12)
            clear * - r48342 b48343 b48344 d48333
            omega
          have d48345 : (x (-5) 3).toNat = 0 := by
            have r48346 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e48347 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
            have e48348 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
            have b48349 := hb (x (-5) 3)
            have b48350 := hb (x (-4) 2)
            have b48351 := hb (x (-3) 13)
            have b48352 := hb (x (-2) 12)
            clear * - r48346 e48347 e48348 b48349 b48350 b48351 b48352 d48333 d48313 d48292
            omega
          have d48353 : (x (-5) 11).toNat = 0 := by
            have r48354 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
            have b48355 := hb (x (-5) 3)
            have b48356 := hb (x (-5) 11)
            clear * - r48354 b48355 b48356 d48345
            omega
          have d48357 : (x (-5) 4).toNat = 1 := by
            have r48358 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b48359 := hb (x (-5) 4)
            have b48360 := hb (x (-1) 11)
            have b48361 := hb (x (-2) 1 && x (-2) 12)
            have b48362 := hb (x (-3) 2 && x (-3) 13)
            have b48363 := hb (x (-4) 3 && x (-4) 14)
            clear * - r48358 b48359 b48360 b48361 b48362 b48363 g13 d48341 d48271 d48325
            omega
          have d48364 : (x (-5) 12).toNat = 1 := by
            have r48365 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
            have b48366 := hb (x (-5) 4)
            have b48367 := hb (x (-5) 12)
            clear * - r48365 b48366 b48367 d48357
            omega
          have d48368 : (x (-6) 13).toNat = 0 := by
            have r48369 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e48370 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
            have e48371 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
            have b48372 := hb (x (-8) 3)
            have b48373 := hb (x (-7) 2)
            have b48374 := hb (x (-6) 13)
            have b48375 := hb (x (-5) 12)
            clear * - r48369 e48370 e48371 b48372 b48373 b48374 b48375 d48364
            omega
          have d48376 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
            have r48377 := hand2 (x (-6) 2) (x (-6) 13)
            have b48378 := hb (x (-6) 13)
            have b48379 := hb (x (-6) 2 && x (-6) 13)
            clear * - r48377 b48378 b48379 d48368
            omega
          have d48380 : (x (-7) 2).toNat = 0 := by
            have r48381 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e48382 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
            have e48383 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
            have b48384 := hb (x (-8) 3)
            have b48385 := hb (x (-7) 2)
            have b48386 := hb (x (-6) 13)
            have b48387 := hb (x (-5) 12)
            clear * - r48381 e48382 e48383 b48384 b48385 b48386 b48387 d48364 d48368
            omega
          have d48388 : (x (-7) 2 && x (-7) 13).toNat = 0 := by
            have r48389 := hand1 (x (-7) 2) (x (-7) 13)
            have b48390 := hb (x (-7) 2)
            have b48391 := hb (x (-7) 2 && x (-7) 13)
            clear * - r48389 b48390 b48391 d48380
            omega
          have d48392 : (x (-6) 1 && x (-6) 14).toNat = 1 := by
            have r48393 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b48394 := hb (x (-7) 2)
            have b48395 := hb (x (-5) 13)
            have b48396 := hb (x (-6) 1 && x (-6) 14)
            clear * - r48393 b48394 b48395 b48396 d48309 d48380
            omega
          have d48397 : (x (-6) 14).toNat = 1 := by
            have r48398 := hand2 (x (-6) 1) (x (-6) 14)
            have b48399 := hb (x (-6) 14)
            have b48400 := hb (x (-6) 1 && x (-6) 14)
            clear * - r48398 b48399 b48400 d48392
            omega
          have d48401 : (x (-7) 1).toNat = 0 := by
            have r48402 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b48403 := hb (x (-7) 1)
            have b48404 := hb (x (-6) 14)
            clear * - r48402 b48403 b48404 d48397
            omega
          have d48405 : (x (-7) 1 && x (-7) 14).toNat = 0 := by
            have r48406 := hand1 (x (-7) 1) (x (-7) 14)
            have b48407 := hb (x (-7) 1)
            have b48408 := hb (x (-7) 1 && x (-7) 14)
            clear * - r48406 b48407 b48408 d48401
            omega
          have d48409 : (x (-8) 2).toNat = 1 := by
            have r48410 : 1 ≤ (x (-6) 13).toNat + (x (-7) 1 && x (-7) 14).toNat + (x (-8) 2).toNat := by have q := hcov13 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b48411 := hb (x (-8) 2)
            have b48412 := hb (x (-6) 13)
            have b48413 := hb (x (-7) 1 && x (-7) 14)
            clear * - r48410 b48411 b48412 b48413 d48368 d48405
            omega
          have d48414 : (x (-8) 14).toNat = 1 := by
            have r48415 : (x (-8) 2).toNat ≤ (x (-8) 14).toNat := himp _ _ (hp2 (-8))
            have b48416 := hb (x (-8) 2)
            have b48417 := hb (x (-8) 14)
            clear * - r48415 b48416 b48417 d48409
            omega
          have d48418 : (x (-9) 1).toNat = 0 := by
            have r48419 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b48420 := hb (x (-9) 1)
            have b48421 := hb (x (-8) 14)
            clear * - r48419 b48420 b48421 d48414
            omega
          have d48422 : (x (-9) 1 && x (-9) 12).toNat = 0 := by
            have r48423 := hand1 (x (-9) 1) (x (-9) 12)
            have b48424 := hb (x (-9) 1)
            have b48425 := hb (x (-9) 1 && x (-9) 12)
            clear * - r48423 b48424 b48425 d48418
            omega
          have d48426 : (x (-9) 13).toNat = 0 := by
            have r48427 : (x (-9) 13).toNat ≤ (x (-9) 1).toNat := himp _ _ (hp13 (-9))
            have b48428 := hb (x (-9) 1)
            have b48429 := hb (x (-9) 13)
            clear * - r48427 b48428 b48429 d48418
            omega
          have d48430 : (x (-6) 12).toNat = 0 := by
            have r48431 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e48432 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
            have e48433 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
            have b48434 := hb (x (-9) 3)
            have b48435 := hb (x (-8) 2)
            have b48436 := hb (x (-7) 13)
            have b48437 := hb (x (-6) 12)
            clear * - r48431 e48432 e48433 b48434 b48435 b48436 b48437 d48409
            omega
          have d48438 : (x (-6) 1 && x (-6) 12).toNat = 0 := by
            have r48439 := hand2 (x (-6) 1) (x (-6) 12)
            have b48440 := hb (x (-6) 12)
            have b48441 := hb (x (-6) 1 && x (-6) 12)
            clear * - r48439 b48440 b48441 d48430
            omega
          have d48442 : (x (-7) 13).toNat = 0 := by
            have r48443 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e48444 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
            have e48445 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
            have b48446 := hb (x (-9) 3)
            have b48447 := hb (x (-8) 2)
            have b48448 := hb (x (-7) 13)
            have b48449 := hb (x (-6) 12)
            clear * - r48443 e48444 e48445 b48446 b48447 b48448 b48449 d48430 d48409
            omega
          have d48450 : (x (-8) 3).toNat = 0 := by
            have r48451 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e48452 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
            have e48453 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
            have b48454 := hb (x (-8) 3)
            have b48455 := hb (x (-7) 2)
            have b48456 := hb (x (-6) 13)
            have b48457 := hb (x (-5) 12)
            clear * - r48451 e48452 e48453 b48454 b48455 b48456 b48457 d48364 d48368 d48380
            omega
          have d48458 : (x (-8) 3 && x (-8) 14).toNat = 0 := by
            have r48459 := hand1 (x (-8) 3) (x (-8) 14)
            have b48460 := hb (x (-8) 3)
            have b48461 := hb (x (-8) 3 && x (-8) 14)
            clear * - r48459 b48460 b48461 d48450
            omega
          have d48462 : (x (-8) 11).toNat = 0 := by
            have r48463 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
            have b48464 := hb (x (-8) 3)
            have b48465 := hb (x (-8) 11)
            clear * - r48463 b48464 b48465 d48450
            omega
          have d48466 : (x (-9) 4).toNat = 1 := by
            have r48467 : 1 ≤ (x (-5) 11).toNat + (x (-6) 1 && x (-6) 12).toNat + (x (-7) 2 && x (-7) 13).toNat + (x (-8) 3 && x (-8) 14).toNat + (x (-9) 4).toNat := by have q := hcov11 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b48468 := hb (x (-9) 4)
            have b48469 := hb (x (-5) 11)
            have b48470 := hb (x (-6) 1 && x (-6) 12)
            have b48471 := hb (x (-7) 2 && x (-7) 13)
            have b48472 := hb (x (-8) 3 && x (-8) 14)
            clear * - r48467 b48468 b48469 b48470 b48471 b48472 d48353 d48438 d48388 d48458
            omega
          have d48473 : (x (-9) 12).toNat = 1 := by
            have r48474 : (x (-9) 4).toNat ≤ (x (-9) 12).toNat := himp _ _ (hp4 (-9))
            have b48475 := hb (x (-9) 4)
            have b48476 := hb (x (-9) 12)
            clear * - r48474 b48475 b48476 d48466
            omega
          have d48477 : (x (-10) 13).toNat = 0 := by
            have r48478 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e48479 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
            have e48480 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
            have b48481 := hb (x (-12) 3)
            have b48482 := hb (x (-11) 2)
            have b48483 := hb (x (-10) 13)
            have b48484 := hb (x (-9) 12)
            clear * - r48478 e48479 e48480 b48481 b48482 b48483 b48484 d48473
            omega
          have d48485 : (x (-10) 2 && x (-10) 13).toNat = 0 := by
            have r48486 := hand2 (x (-10) 2) (x (-10) 13)
            have b48487 := hb (x (-10) 13)
            have b48488 := hb (x (-10) 2 && x (-10) 13)
            clear * - r48486 b48487 b48488 d48477
            omega
          have d48489 : (x (-11) 2).toNat = 0 := by
            have r48490 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e48491 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
            have e48492 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
            have b48493 := hb (x (-12) 3)
            have b48494 := hb (x (-11) 2)
            have b48495 := hb (x (-10) 13)
            have b48496 := hb (x (-9) 12)
            clear * - r48490 e48491 e48492 b48493 b48494 b48495 b48496 d48473 d48477
            omega
          have d48497 : (x (-10) 1 && x (-10) 14).toNat = 1 := by
            have r48498 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b48499 := hb (x (-11) 2)
            have b48500 := hb (x (-9) 13)
            have b48501 := hb (x (-10) 1 && x (-10) 14)
            clear * - r48498 b48499 b48500 b48501 d48426 d48489
            omega
          have d48502 : (x (-10) 1).toNat = 1 := by
            have r48503 := hand1 (x (-10) 1) (x (-10) 14)
            have b48504 := hb (x (-10) 1)
            have b48505 := hb (x (-10) 1 && x (-10) 14)
            clear * - r48503 b48504 b48505 d48497
            omega
          have d48506 : (x (-9) 14).toNat = 0 := by
            have r48507 : (x (-9) 14).toNat + (x (-10) 1).toNat = 1 := by have q := hd14 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b48508 := hb (x (-10) 1)
            have b48509 := hb (x (-9) 14)
            clear * - r48507 b48508 b48509 d48502
            omega
          have d48510 : (x (-9) 2).toNat = 0 := by
            have r48511 : (x (-9) 2).toNat ≤ (x (-9) 14).toNat := himp _ _ (hp2 (-9))
            have b48512 := hb (x (-9) 2)
            have b48513 := hb (x (-9) 14)
            clear * - r48511 b48512 b48513 d48506
            omega
          have d48514 : (x (-8) 1 && x (-8) 14).toNat = 1 := by
            have r48515 : 1 ≤ (x (-7) 13).toNat + (x (-8) 1 && x (-8) 14).toNat + (x (-9) 2).toNat := by have q := hcov13 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b48516 := hb (x (-9) 2)
            have b48517 := hb (x (-7) 13)
            have b48518 := hb (x (-8) 1 && x (-8) 14)
            clear * - r48515 b48516 b48517 b48518 d48442 d48510
            omega
          have d48519 : (x (-8) 1).toNat = 1 := by
            have r48520 := hand1 (x (-8) 1) (x (-8) 14)
            have b48521 := hb (x (-8) 1)
            have b48522 := hb (x (-8) 1 && x (-8) 14)
            clear * - r48520 b48521 b48522 d48514
            omega
          have d48523 : (x (-7) 14).toNat = 0 := by
            have r48524 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b48525 := hb (x (-8) 1)
            have b48526 := hb (x (-7) 14)
            clear * - r48524 b48525 b48526 d48519
            omega
          have d48527 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
            have r48528 := hand2 (x (-7) 3) (x (-7) 14)
            have b48529 := hb (x (-7) 14)
            have b48530 := hb (x (-7) 3 && x (-7) 14)
            clear * - r48528 b48529 b48530 d48523
            omega
          have d48531 : (x (-8) 4).toNat = 1 := by
            have r48532 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b48533 := hb (x (-8) 4)
            have b48534 := hb (x (-4) 11)
            have b48535 := hb (x (-5) 1 && x (-5) 12)
            have b48536 := hb (x (-6) 2 && x (-6) 13)
            have b48537 := hb (x (-7) 3 && x (-7) 14)
            clear * - r48532 b48533 b48534 b48535 b48536 b48537 d48329 d48305 d48376 d48527
            omega
          have d48538 : (x (-8) 12).toNat = 1 := by
            have r48539 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
            have b48540 := hb (x (-8) 4)
            have b48541 := hb (x (-8) 12)
            clear * - r48539 b48540 b48541 d48531
            omega
          have d48542 : (x (-10) 2).toNat = 0 := by
            have r48543 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e48544 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
            have e48545 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
            have b48546 := hb (x (-11) 3)
            have b48547 := hb (x (-10) 2)
            have b48548 := hb (x (-9) 13)
            have b48549 := hb (x (-8) 12)
            clear * - r48543 e48544 e48545 b48546 b48547 b48548 b48549 d48538 d48426
            omega
          have d48550 : (x (-11) 3).toNat = 0 := by
            have r48551 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e48552 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
            have e48553 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
            have b48554 := hb (x (-11) 3)
            have b48555 := hb (x (-10) 2)
            have b48556 := hb (x (-9) 13)
            have b48557 := hb (x (-8) 12)
            clear * - r48551 e48552 e48553 b48554 b48555 b48556 b48557 d48538 d48426 d48542
            omega
          have d48558 : (x (-11) 3 && x (-11) 14).toNat = 0 := by
            have r48559 := hand1 (x (-11) 3) (x (-11) 14)
            have b48560 := hb (x (-11) 3)
            have b48561 := hb (x (-11) 3 && x (-11) 14)
            clear * - r48559 b48560 b48561 d48550
            omega
          have r48562 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := by have q := hcov11 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b48563 := hb (x (-12) 4)
          have b48564 := hb (x (-8) 11)
          have b48565 := hb (x (-9) 1 && x (-9) 12)
          have b48566 := hb (x (-10) 2 && x (-10) 13)
          have b48567 := hb (x (-11) 3 && x (-11) 14)
          linarith only [r48562, b48563, b48564, b48565, b48566, b48567, d48462, d48422, d48485, d48558, g0]
      · have f48568 : (x (-1) 8).toNat = 1 := by rw [h46720]; rfl
        have d48569 : (x (-2) 9).toNat = 0 := by
          have r48570 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e48571 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
          have e48572 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
          have e48573 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
          have e48574 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
          have e48575 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
          have e48576 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
          have b48577 := hb (x (-8) 7)
          have b48578 := hb (x (-7) 6)
          have b48579 := hb (x (-6) 5)
          have b48580 := hb (x (-5) 4)
          have b48581 := hb (x (-4) 11)
          have b48582 := hb (x (-3) 10)
          have b48583 := hb (x (-2) 9)
          have b48584 := hb (x (-1) 8)
          clear * - r48570 e48571 e48572 e48573 e48574 e48575 e48576 b48577 b48578 b48579 b48580 b48581 b48582 b48583 b48584 f48568
          omega
        have d48585 : (x (-3) 10).toNat = 0 := by
          have r48586 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e48587 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
          have e48588 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
          have e48589 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
          have e48590 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
          have e48591 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
          have e48592 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
          have b48593 := hb (x (-8) 7)
          have b48594 := hb (x (-7) 6)
          have b48595 := hb (x (-6) 5)
          have b48596 := hb (x (-5) 4)
          have b48597 := hb (x (-4) 11)
          have b48598 := hb (x (-3) 10)
          have b48599 := hb (x (-2) 9)
          have b48600 := hb (x (-1) 8)
          clear * - r48586 e48587 e48588 e48589 e48590 e48591 e48592 b48593 b48594 b48595 b48596 b48597 b48598 b48599 b48600 f48568 d48569
          omega
        have d48601 : (x (-4) 11).toNat = 0 := by
          have r48602 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e48603 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
          have e48604 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
          have e48605 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
          have e48606 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
          have e48607 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
          have e48608 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
          have b48609 := hb (x (-8) 7)
          have b48610 := hb (x (-7) 6)
          have b48611 := hb (x (-6) 5)
          have b48612 := hb (x (-5) 4)
          have b48613 := hb (x (-4) 11)
          have b48614 := hb (x (-3) 10)
          have b48615 := hb (x (-2) 9)
          have b48616 := hb (x (-1) 8)
          clear * - r48602 e48603 e48604 e48605 e48606 e48607 e48608 b48609 b48610 b48611 b48612 b48613 b48614 b48615 b48616 f48568 d48569 d48585
          omega
        have d48617 : (x (-5) 4).toNat = 0 := by
          have r48618 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e48619 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
          have e48620 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
          have e48621 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
          have e48622 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
          have e48623 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
          have e48624 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
          have b48625 := hb (x (-8) 7)
          have b48626 := hb (x (-7) 6)
          have b48627 := hb (x (-6) 5)
          have b48628 := hb (x (-5) 4)
          have b48629 := hb (x (-4) 11)
          have b48630 := hb (x (-3) 10)
          have b48631 := hb (x (-2) 9)
          have b48632 := hb (x (-1) 8)
          clear * - r48618 e48619 e48620 e48621 e48622 e48623 e48624 b48625 b48626 b48627 b48628 b48629 b48630 b48631 b48632 f48568 d48569 d48585 d48601
          omega
        have d48633 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
          have r48634 := hand1 (x (-5) 4) (x (-5) 14)
          have b48635 := hb (x (-5) 4)
          have b48636 := hb (x (-5) 4 && x (-5) 14)
          clear * - r48634 b48635 b48636 d48617
          omega
        have d48637 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
          have r48638 := hand1 (x (-5) 4) (x (-5) 13)
          have b48639 := hb (x (-5) 4)
          have b48640 := hb (x (-5) 4 && x (-5) 13)
          clear * - r48638 b48639 b48640 d48617
          omega
        have d48641 : (x (-5) 4 && x (-5) 9).toNat = 0 := by
          have r48642 := hand1 (x (-5) 4) (x (-5) 9)
          have b48643 := hb (x (-5) 4)
          have b48644 := hb (x (-5) 4 && x (-5) 9)
          clear * - r48642 b48643 b48644 d48617
          omega
        have d48645 : (x (-6) 5).toNat = 0 := by
          have r48646 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e48647 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
          have e48648 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
          have e48649 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
          have e48650 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
          have e48651 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
          have e48652 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
          have b48653 := hb (x (-8) 7)
          have b48654 := hb (x (-7) 6)
          have b48655 := hb (x (-6) 5)
          have b48656 := hb (x (-5) 4)
          have b48657 := hb (x (-4) 11)
          have b48658 := hb (x (-3) 10)
          have b48659 := hb (x (-2) 9)
          have b48660 := hb (x (-1) 8)
          clear * - r48646 e48647 e48648 e48649 e48650 e48651 e48652 b48653 b48654 b48655 b48656 b48657 b48658 b48659 b48660 f48568 d48569 d48585 d48601 d48617
          omega
        have d48661 : (x (-6) 5 && x (-6) 14).toNat = 0 := by
          have r48662 := hand1 (x (-6) 5) (x (-6) 14)
          have b48663 := hb (x (-6) 5)
          have b48664 := hb (x (-6) 5 && x (-6) 14)
          clear * - r48662 b48663 b48664 d48645
          omega
        have d48665 : (x (-6) 5 && x (-6) 10).toNat = 0 := by
          have r48666 := hand1 (x (-6) 5) (x (-6) 10)
          have b48667 := hb (x (-6) 5)
          have b48668 := hb (x (-6) 5 && x (-6) 10)
          clear * - r48666 b48667 b48668 d48645
          omega
        have d48669 : (x (-7) 6).toNat = 0 := by
          have r48670 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e48671 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
          have e48672 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
          have e48673 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
          have e48674 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
          have e48675 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
          have e48676 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
          have b48677 := hb (x (-8) 7)
          have b48678 := hb (x (-7) 6)
          have b48679 := hb (x (-6) 5)
          have b48680 := hb (x (-5) 4)
          have b48681 := hb (x (-4) 11)
          have b48682 := hb (x (-3) 10)
          have b48683 := hb (x (-2) 9)
          have b48684 := hb (x (-1) 8)
          clear * - r48670 e48671 e48672 e48673 e48674 e48675 e48676 b48677 b48678 b48679 b48680 b48681 b48682 b48683 b48684 f48568 d48569 d48585 d48601 d48617 d48645
          omega
        have d48685 : (x (-7) 6 && x (-7) 11).toNat = 0 := by
          have r48686 := hand1 (x (-7) 6) (x (-7) 11)
          have b48687 := hb (x (-7) 6)
          have b48688 := hb (x (-7) 6 && x (-7) 11)
          clear * - r48686 b48687 b48688 d48669
          omega
        have d48689 : (x (-4) 3 && x (-4) 12).toNat = 1 := by
          have r48690 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b48691 := hb (x (-7) 6)
          have b48692 := hb (x (-1) 9)
          have b48693 := hb (x (-2) 1 && x (-2) 10)
          have b48694 := hb (x (-3) 2 && x (-3) 11)
          have b48695 := hb (x (-4) 3 && x (-4) 12)
          have b48696 := hb (x (-5) 4 && x (-5) 13)
          have b48697 := hb (x (-6) 5 && x (-6) 14)
          clear * - r48690 b48691 b48692 b48693 b48694 b48695 b48696 b48697 g11 g96 g97 d48637 d48661 d48669
          omega
        have d48698 : (x (-4) 12).toNat = 1 := by
          have r48699 := hand2 (x (-4) 3) (x (-4) 12)
          have b48700 := hb (x (-4) 12)
          have b48701 := hb (x (-4) 3 && x (-4) 12)
          clear * - r48699 b48700 b48701 d48689
          omega
        have d48702 : (x (-5) 13).toNat = 0 := by
          have r48703 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e48704 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
          have e48705 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
          have b48706 := hb (x (-7) 3)
          have b48707 := hb (x (-6) 2)
          have b48708 := hb (x (-5) 13)
          have b48709 := hb (x (-4) 12)
          clear * - r48703 e48704 e48705 b48706 b48707 b48708 b48709 d48698
          omega
        have d48710 : (x (-6) 2).toNat = 0 := by
          have r48711 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e48712 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
          have e48713 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
          have b48714 := hb (x (-7) 3)
          have b48715 := hb (x (-6) 2)
          have b48716 := hb (x (-5) 13)
          have b48717 := hb (x (-4) 12)
          clear * - r48711 e48712 e48713 b48714 b48715 b48716 b48717 d48698 d48702
          omega
        have d48718 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
          have r48719 := hand1 (x (-6) 2) (x (-6) 13)
          have b48720 := hb (x (-6) 2)
          have b48721 := hb (x (-6) 2 && x (-6) 13)
          clear * - r48719 b48720 b48721 d48710
          omega
        have d48722 : (x (-6) 10).toNat = 0 := by
          have r48723 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
          have b48724 := hb (x (-6) 2)
          have b48725 := hb (x (-6) 10)
          clear * - r48723 b48724 b48725 d48710
          omega
        have d48726 : (x (-7) 3).toNat = 0 := by
          have r48727 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e48728 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
          have e48729 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
          have b48730 := hb (x (-7) 3)
          have b48731 := hb (x (-6) 2)
          have b48732 := hb (x (-5) 13)
          have b48733 := hb (x (-4) 12)
          clear * - r48727 e48728 e48729 b48730 b48731 b48732 b48733 d48698 d48702 d48710
          omega
        have d48734 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
          have r48735 := hand1 (x (-7) 3) (x (-7) 14)
          have b48736 := hb (x (-7) 3)
          have b48737 := hb (x (-7) 3 && x (-7) 14)
          clear * - r48735 b48736 b48737 d48726
          omega
        have d48738 : (x (-7) 11).toNat = 0 := by
          have r48739 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
          have b48740 := hb (x (-7) 3)
          have b48741 := hb (x (-7) 11)
          clear * - r48739 b48740 b48741 d48726
          omega
        have d48742 : (x (-4) 3).toNat = 1 := by
          have r48743 := hand1 (x (-4) 3) (x (-4) 12)
          have b48744 := hb (x (-4) 3)
          have b48745 := hb (x (-4) 3 && x (-4) 12)
          clear * - r48743 b48744 b48745 d48689
          omega
        have d48746 : (x (-1) 12).toNat = 0 := by
          have r48747 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e48748 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e48749 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b48750 := hb (x (-4) 3)
          have b48751 := hb (x (-3) 2)
          have b48752 := hb (x (-2) 13)
          have b48753 := hb (x (-1) 12)
          clear * - r48747 e48748 e48749 b48750 b48751 b48752 b48753 d48742
          omega
        have d48754 : (x (-2) 13).toNat = 0 := by
          have r48755 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e48756 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e48757 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b48758 := hb (x (-4) 3)
          have b48759 := hb (x (-3) 2)
          have b48760 := hb (x (-2) 13)
          have b48761 := hb (x (-1) 12)
          clear * - r48755 e48756 e48757 b48758 b48759 b48760 b48761 d48746 d48742
          omega
        have d48762 : (x (-3) 2).toNat = 0 := by
          have r48763 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e48764 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e48765 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b48766 := hb (x (-4) 3)
          have b48767 := hb (x (-3) 2)
          have b48768 := hb (x (-2) 13)
          have b48769 := hb (x (-1) 12)
          clear * - r48763 e48764 e48765 b48766 b48767 b48768 b48769 d48746 d48754 d48742
          omega
        have d48770 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
          have r48771 := hand1 (x (-3) 2) (x (-3) 12)
          have b48772 := hb (x (-3) 2)
          have b48773 := hb (x (-3) 2 && x (-3) 12)
          clear * - r48771 b48772 b48773 d48762
          omega
        have d48774 : (x (-4) 3 && x (-4) 13).toNat = 1 := by
          have r48775 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b48776 := hb (x (-6) 5)
          have b48777 := hb (x (-1) 10)
          have b48778 := hb (x (-2) 1 && x (-2) 11)
          have b48779 := hb (x (-3) 2 && x (-3) 12)
          have b48780 := hb (x (-4) 3 && x (-4) 13)
          have b48781 := hb (x (-5) 4 && x (-5) 14)
          clear * - r48775 b48776 b48777 b48778 b48779 b48780 b48781 g12 g100 d48770 d48633 d48645
          omega
        have d48782 : (x (-4) 13).toNat = 1 := by
          have r48783 := hand2 (x (-4) 3) (x (-4) 13)
          have b48784 := hb (x (-4) 13)
          have b48785 := hb (x (-4) 3 && x (-4) 13)
          clear * - r48783 b48784 b48785 d48774
          omega
        have d48786 : (x (-4) 1).toNat = 1 := by
          have r48787 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
          have b48788 := hb (x (-4) 1)
          have b48789 := hb (x (-4) 13)
          clear * - r48787 b48788 b48789 d48782
          omega
        have d48790 : (x (-3) 14).toNat = 0 := by
          have r48791 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b48792 := hb (x (-4) 1)
          have b48793 := hb (x (-3) 14)
          clear * - r48791 b48792 b48793 d48786
          omega
        have d48794 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
          have r48795 := hand2 (x (-3) 1) (x (-3) 14)
          have b48796 := hb (x (-3) 14)
          have b48797 := hb (x (-3) 1 && x (-3) 14)
          clear * - r48795 b48796 b48797 d48790
          omega
        have d48798 : (x (-4) 2).toNat = 1 := by
          have r48799 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b48800 := hb (x (-4) 2)
          have b48801 := hb (x (-2) 13)
          have b48802 := hb (x (-3) 1 && x (-3) 14)
          clear * - r48799 b48800 b48801 b48802 d48754 d48794
          omega
        have d48803 : (x (-4) 14).toNat = 1 := by
          have r48804 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
          have b48805 := hb (x (-4) 2)
          have b48806 := hb (x (-4) 14)
          clear * - r48804 b48805 b48806 d48798
          omega
        have d48807 : (x (-5) 1).toNat = 0 := by
          have r48808 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b48809 := hb (x (-5) 1)
          have b48810 := hb (x (-4) 14)
          clear * - r48808 b48809 b48810 d48803
          omega
        have d48811 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
          have r48812 := hand1 (x (-5) 1) (x (-5) 12)
          have b48813 := hb (x (-5) 1)
          have b48814 := hb (x (-5) 1 && x (-5) 12)
          clear * - r48812 b48813 b48814 d48807
          omega
        have d48815 : (x (-8) 4).toNat = 1 := by
          have r48816 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b48817 := hb (x (-8) 4)
          have b48818 := hb (x (-4) 11)
          have b48819 := hb (x (-5) 1 && x (-5) 12)
          have b48820 := hb (x (-6) 2 && x (-6) 13)
          have b48821 := hb (x (-7) 3 && x (-7) 14)
          clear * - r48816 b48817 b48818 b48819 b48820 b48821 d48601 d48811 d48718 d48734
          omega
        have d48822 : (x (-8) 12).toNat = 1 := by
          have r48823 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
          have b48824 := hb (x (-8) 4)
          have b48825 := hb (x (-8) 12)
          clear * - r48823 b48824 b48825 d48815
          omega
        have d48826 : (x (-9) 13).toNat = 0 := by
          have r48827 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e48828 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
          have e48829 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
          have b48830 := hb (x (-11) 3)
          have b48831 := hb (x (-10) 2)
          have b48832 := hb (x (-9) 13)
          have b48833 := hb (x (-8) 12)
          clear * - r48827 e48828 e48829 b48830 b48831 b48832 b48833 d48822
          omega
        have d48834 : (x (-9) 8 && x (-9) 13).toNat = 0 := by
          have r48835 := hand2 (x (-9) 8) (x (-9) 13)
          have b48836 := hb (x (-9) 13)
          have b48837 := hb (x (-9) 8 && x (-9) 13)
          clear * - r48835 b48836 b48837 d48826
          omega
        have d48838 : (x (-9) 5).toNat = 0 := by
          have r48839 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
          have b48840 := hb (x (-9) 5)
          have b48841 := hb (x (-9) 13)
          clear * - r48839 b48840 b48841 d48826
          omega
        have d48842 : (x (-5) 9).toNat = 0 := by
          have r48843 : (x (-5) 9).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp9 (-5))
          have b48844 := hb (x (-5) 1)
          have b48845 := hb (x (-5) 9)
          clear * - r48843 b48844 b48845 d48807
          omega
        have d48846 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
          have r48847 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b48848 := hb (x (-3) 2)
          have b48849 := hb (x (-1) 13)
          have b48850 := hb (x (-2) 1 && x (-2) 14)
          clear * - r48847 b48848 b48849 b48850 g14 d48762
          omega
        have d48851 : (x (-2) 1).toNat = 1 := by
          have r48852 := hand1 (x (-2) 1) (x (-2) 14)
          have b48853 := hb (x (-2) 1)
          have b48854 := hb (x (-2) 1 && x (-2) 14)
          clear * - r48852 b48853 b48854 d48846
          omega
        have d48855 : (x (-8) 7).toNat = 0 := by
          have r48856 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e48857 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
          have e48858 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
          have e48859 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
          have e48860 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
          have e48861 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
          have e48862 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
          have b48863 := hb (x (-8) 7)
          have b48864 := hb (x (-7) 6)
          have b48865 := hb (x (-6) 5)
          have b48866 := hb (x (-5) 4)
          have b48867 := hb (x (-4) 11)
          have b48868 := hb (x (-3) 10)
          have b48869 := hb (x (-2) 9)
          have b48870 := hb (x (-1) 8)
          clear * - r48856 e48857 e48858 e48859 e48860 e48861 e48862 b48863 b48864 b48865 b48866 b48867 b48868 b48869 b48870 f48568 d48569 d48585 d48601 d48617 d48645 d48669
          omega
        have d48871 : (x (-8) 7 && x (-8) 12).toNat = 0 := by
          have r48872 := hand1 (x (-8) 7) (x (-8) 12)
          have b48873 := hb (x (-8) 7)
          have b48874 := hb (x (-8) 7 && x (-8) 12)
          clear * - r48872 b48873 b48874 d48855
          omega
        have d48875 : (x (-8) 7 && x (-8) 8).toNat = 0 := by
          have r48876 := hand1 (x (-8) 7) (x (-8) 8)
          have b48877 := hb (x (-8) 7)
          have b48878 := hb (x (-8) 7 && x (-8) 8)
          clear * - r48876 b48877 b48878 d48855
          omega
        have d48879 : (x (-4) 8).toNat = 0 := by
          have r48880 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e48881 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
          have e48882 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
          have e48883 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
          have e48884 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
          have e48885 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
          have e48886 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
          have b48887 := hb (x (-11) 7)
          have b48888 := hb (x (-10) 6)
          have b48889 := hb (x (-9) 5)
          have b48890 := hb (x (-8) 4)
          have b48891 := hb (x (-7) 11)
          have b48892 := hb (x (-6) 10)
          have b48893 := hb (x (-5) 9)
          have b48894 := hb (x (-4) 8)
          clear * - r48880 e48881 e48882 e48883 e48884 e48885 e48886 b48887 b48888 b48889 b48890 b48891 b48892 b48893 b48894 d48842 d48722 d48738 d48815 d48838
          omega
        have d48895 : (x (-4) 3 && x (-4) 8).toNat = 0 := by
          have r48896 := hand2 (x (-4) 3) (x (-4) 8)
          have b48897 := hb (x (-4) 8)
          have b48898 := hb (x (-4) 3 && x (-4) 8)
          clear * - r48896 b48897 b48898 d48879
          omega
        have r48899 : (x (-2) 1).toNat + (x (-3) 2).toNat + (x (-4) 3).toNat + (x (-5) 4).toNat + (x (-6) 5).toNat + (x (-7) 6).toNat + (x (-8) 7).toNat + (x (-9) 8).toNat + (x (-10) 9).toNat + (x (-11) 10).toNat + (x (-12) 11).toNat + (x (-13) 12).toNat + (x (-14) 13).toNat + (x (-15) 14).toNat = 3 := by have q := hcount (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r48900 : 1 ≤ (x (-1) 1).toNat + (x (-2) 1 && x (-2) 2).toNat + (x (-3) 2 && x (-3) 3).toNat + (x (-4) 3 && x (-4) 4).toNat + (x (-5) 4 && x (-5) 5).toNat + (x (-6) 5 && x (-6) 6).toNat + (x (-7) 6 && x (-7) 7).toNat + (x (-8) 7 && x (-8) 8).toNat + (x (-9) 8 && x (-9) 9).toNat + (x (-10) 9 && x (-10) 10).toNat + (x (-11) 10 && x (-11) 11).toNat + (x (-12) 11 && x (-12) 12).toNat + (x (-13) 12 && x (-13) 13).toNat + (x (-14) 13 && x (-14) 14).toNat + (x (-15) 14).toNat := by have q := hcov1 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r48901 : 1 ≤ (x (-1) 5).toNat + (x (-2) 1 && x (-2) 6).toNat + (x (-3) 2 && x (-3) 7).toNat + (x (-4) 3 && x (-4) 8).toNat + (x (-5) 4 && x (-5) 9).toNat + (x (-6) 5 && x (-6) 10).toNat + (x (-7) 6 && x (-7) 11).toNat + (x (-8) 7 && x (-8) 12).toNat + (x (-9) 8 && x (-9) 13).toNat + (x (-10) 9 && x (-10) 14).toNat + (x (-11) 10).toNat := by have q := hcov5 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r48902 := hand1 (x (-12) 11) (x (-12) 12)
        have r48903 := hand1 (x (-13) 12) (x (-13) 13)
        have r48904 := hand1 (x (-14) 13) (x (-14) 14)
        have r48905 := hand1 (x (-10) 9) (x (-10) 14)
        linarith only [r48899, r48900, r48901, r48902, r48903, r48904, r48905, d48855, d48669, d48645, d48617, d48742, d48762, d48851, g8, g10, g44, g45, g46, g47, g48, g49, d48875, g50, g51, g52, g72, g73, d48895, d48641, d48665, d48685, d48871, d48834]
    · have f48944 : (x 1 7).toNat = 1 := by rw [h46718]; rfl
      have d48945 : (x 8 8).toNat = 0 := by
        have r48946 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e48947 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e48948 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e48949 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e48950 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e48951 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e48952 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b48953 := hb (x 1 7)
        have b48954 := hb (x 2 6)
        have b48955 := hb (x 3 5)
        have b48956 := hb (x 4 4)
        have b48957 := hb (x 5 11)
        have b48958 := hb (x 6 10)
        have b48959 := hb (x 7 9)
        have b48960 := hb (x 8 8)
        clear * - r48946 e48947 e48948 e48949 e48950 e48951 e48952 b48953 b48954 b48955 b48956 b48957 b48958 b48959 b48960 f48944
        omega
      have d48961 : (x 8 1 && x 8 8).toNat = 0 := by
        have r48962 := hand2 (x 8 1) (x 8 8)
        have b48963 := hb (x 8 8)
        have b48964 := hb (x 8 1 && x 8 8)
        clear * - r48962 b48963 b48964 d48945
        omega
      have d48965 : (x 8 3 && x 8 8).toNat = 0 := by
        have r48966 := hand2 (x 8 3) (x 8 8)
        have b48967 := hb (x 8 8)
        have b48968 := hb (x 8 3 && x 8 8)
        clear * - r48966 b48967 b48968 d48945
        omega
      have d48969 : (x 7 9).toNat = 0 := by
        have r48970 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e48971 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e48972 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e48973 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e48974 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e48975 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e48976 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b48977 := hb (x 1 7)
        have b48978 := hb (x 2 6)
        have b48979 := hb (x 3 5)
        have b48980 := hb (x 4 4)
        have b48981 := hb (x 5 11)
        have b48982 := hb (x 6 10)
        have b48983 := hb (x 7 9)
        have b48984 := hb (x 8 8)
        clear * - r48970 e48971 e48972 e48973 e48974 e48975 e48976 b48977 b48978 b48979 b48980 b48981 b48982 b48983 b48984 d48945 f48944
        omega
      have d48985 : (x 7 2 && x 7 9).toNat = 0 := by
        have r48986 := hand2 (x 7 2) (x 7 9)
        have b48987 := hb (x 7 9)
        have b48988 := hb (x 7 2 && x 7 9)
        clear * - r48986 b48987 b48988 d48969
        omega
      have d48989 : (x 7 4 && x 7 9).toNat = 0 := by
        have r48990 := hand2 (x 7 4) (x 7 9)
        have b48991 := hb (x 7 9)
        have b48992 := hb (x 7 4 && x 7 9)
        clear * - r48990 b48991 b48992 d48969
        omega
      have d48993 : (x 6 10).toNat = 0 := by
        have r48994 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e48995 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e48996 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e48997 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e48998 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e48999 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e49000 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b49001 := hb (x 1 7)
        have b49002 := hb (x 2 6)
        have b49003 := hb (x 3 5)
        have b49004 := hb (x 4 4)
        have b49005 := hb (x 5 11)
        have b49006 := hb (x 6 10)
        have b49007 := hb (x 7 9)
        have b49008 := hb (x 8 8)
        clear * - r48994 e48995 e48996 e48997 e48998 e48999 e49000 b49001 b49002 b49003 b49004 b49005 b49006 b49007 b49008 d48945 d48969 f48944
        omega
      have d49009 : (x 6 1 && x 6 10).toNat = 0 := by
        have r49010 := hand2 (x 6 1) (x 6 10)
        have b49011 := hb (x 6 10)
        have b49012 := hb (x 6 1 && x 6 10)
        clear * - r49010 b49011 b49012 d48993
        omega
      have d49013 : (x 6 3 && x 6 10).toNat = 0 := by
        have r49014 := hand2 (x 6 3) (x 6 10)
        have b49015 := hb (x 6 10)
        have b49016 := hb (x 6 3 && x 6 10)
        clear * - r49014 b49015 b49016 d48993
        omega
      have d49017 : (x 6 5 && x 6 10).toNat = 0 := by
        have r49018 := hand2 (x 6 5) (x 6 10)
        have b49019 := hb (x 6 10)
        have b49020 := hb (x 6 5 && x 6 10)
        clear * - r49018 b49019 b49020 d48993
        omega
      have d49021 : (x 5 11).toNat = 0 := by
        have r49022 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e49023 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e49024 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e49025 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e49026 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e49027 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e49028 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b49029 := hb (x 1 7)
        have b49030 := hb (x 2 6)
        have b49031 := hb (x 3 5)
        have b49032 := hb (x 4 4)
        have b49033 := hb (x 5 11)
        have b49034 := hb (x 6 10)
        have b49035 := hb (x 7 9)
        have b49036 := hb (x 8 8)
        clear * - r49022 e49023 e49024 e49025 e49026 e49027 e49028 b49029 b49030 b49031 b49032 b49033 b49034 b49035 b49036 d48945 d48969 d48993 f48944
        omega
      have d49037 : (x 5 1 && x 5 11).toNat = 0 := by
        have r49038 := hand2 (x 5 1) (x 5 11)
        have b49039 := hb (x 5 11)
        have b49040 := hb (x 5 1 && x 5 11)
        clear * - r49038 b49039 b49040 d49021
        omega
      have d49041 : (x 5 2 && x 5 11).toNat = 0 := by
        have r49042 := hand2 (x 5 2) (x 5 11)
        have b49043 := hb (x 5 11)
        have b49044 := hb (x 5 2 && x 5 11)
        clear * - r49042 b49043 b49044 d49021
        omega
      have d49045 : (x 4 3 && x 4 12).toNat = 1 := by
        have r49046 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b49047 := hb (x 1 6)
        have b49048 := hb (x 7 9)
        have b49049 := hb (x 6 1 && x 6 10)
        have b49050 := hb (x 5 2 && x 5 11)
        have b49051 := hb (x 4 3 && x 4 12)
        have b49052 := hb (x 3 4 && x 3 13)
        have b49053 := hb (x 2 5 && x 2 14)
        clear * - r49046 b49047 b49048 b49049 b49050 b49051 b49052 b49053 d48969 d49009 d49041 g98 g99 g26
        omega
      have d49054 : (x 4 12).toNat = 1 := by
        have r49055 := hand2 (x 4 3) (x 4 12)
        have b49056 := hb (x 4 12)
        have b49057 := hb (x 4 3 && x 4 12)
        clear * - r49055 b49056 b49057 d49045
        omega
      have d49058 : (x 3 13).toNat = 0 := by
        have r49059 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e49060 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e49061 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b49062 := hb (x 1 3)
        have b49063 := hb (x 2 2)
        have b49064 := hb (x 3 13)
        have b49065 := hb (x 4 12)
        clear * - r49059 e49060 e49061 b49062 b49063 b49064 b49065 d49054 f46717
        omega
      have d49066 : (x 3 3 && x 3 13).toNat = 0 := by
        have r49067 := hand2 (x 3 3) (x 3 13)
        have b49068 := hb (x 3 13)
        have b49069 := hb (x 3 3 && x 3 13)
        clear * - r49067 b49068 b49069 d49058
        omega
      have d49070 : (x 4 2 && x 4 12).toNat = 1 := by
        have r49071 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b49072 := hb (x 1 5)
        have b49073 := hb (x 6 10)
        have b49074 := hb (x 5 1 && x 5 11)
        have b49075 := hb (x 4 2 && x 4 12)
        have b49076 := hb (x 3 3 && x 3 13)
        have b49077 := hb (x 2 4 && x 2 14)
        clear * - r49071 b49072 b49073 b49074 b49075 b49076 b49077 d48993 d49037 d49066 g101 g25
        omega
      have d49078 : (x 4 2).toNat = 1 := by
        have r49079 := hand1 (x 4 2) (x 4 12)
        have b49080 := hb (x 4 2)
        have b49081 := hb (x 4 2 && x 4 12)
        clear * - r49079 b49080 b49081 d49070
        omega
      have d49082 : (x 4 14).toNat = 1 := by
        have r49083 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
        have b49084 := hb (x 4 2)
        have b49085 := hb (x 4 14)
        clear * - r49083 b49084 b49085 d49078
        omega
      have d49086 : (x 3 1).toNat = 0 := by
        have r49087 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b49088 := hb (x 3 1)
        have b49089 := hb (x 4 14)
        clear * - r49087 b49088 b49089 d49082
        omega
      have d49090 : (x 3 1 && x 3 14).toNat = 0 := by
        have r49091 := hand1 (x 3 1) (x 3 14)
        have b49092 := hb (x 3 1)
        have b49093 := hb (x 3 1 && x 3 14)
        clear * - r49091 b49092 b49093 d49086
        omega
      have d49094 : (x 6 12).toNat = 0 := by
        have r49095 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e49096 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
        have e49097 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
        have b49098 := hb (x 3 3)
        have b49099 := hb (x 4 2)
        have b49100 := hb (x 5 13)
        have b49101 := hb (x 6 12)
        clear * - r49095 e49096 e49097 b49098 b49099 b49100 b49101 d49078
        omega
      have d49102 : (x 5 13).toNat = 0 := by
        have r49103 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e49104 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
        have e49105 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
        have b49106 := hb (x 3 3)
        have b49107 := hb (x 4 2)
        have b49108 := hb (x 5 13)
        have b49109 := hb (x 6 12)
        clear * - r49103 e49104 e49105 b49106 b49107 b49108 b49109 d49094 d49078
        omega
      have d49110 : (x 3 6 && x 3 13).toNat = 0 := by
        have r49111 := hand2 (x 3 6) (x 3 13)
        have b49112 := hb (x 3 13)
        have b49113 := hb (x 3 6 && x 3 13)
        clear * - r49111 b49112 b49113 d49058
        omega
      have d49114 : (x 3 5).toNat = 0 := by
        have r49115 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
        have b49116 := hb (x 3 5)
        have b49117 := hb (x 3 13)
        clear * - r49115 b49116 b49117 d49058
        omega
      have d49118 : (x 3 5 && x 3 14).toNat = 0 := by
        have r49119 := hand1 (x 3 5) (x 3 14)
        have b49120 := hb (x 3 5)
        have b49121 := hb (x 3 5 && x 3 14)
        clear * - r49119 b49120 b49121 d49114
        omega
      have d49122 : (x 2 1 && x 2 14).toNat = 1 := by
        have r49123 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b49124 := hb (x 1 2)
        have b49125 := hb (x 3 13)
        have b49126 := hb (x 2 1 && x 2 14)
        clear * - r49123 b49124 b49125 b49126 d49058 g23
        omega
      have d49127 : (x 2 1).toNat = 1 := by
        have r49128 := hand1 (x 2 1) (x 2 14)
        have b49129 := hb (x 2 1)
        have b49130 := hb (x 2 1 && x 2 14)
        clear * - r49128 b49129 b49130 d49122
        omega
      have d49131 : (x 3 14).toNat = 0 := by
        have r49132 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b49133 := hb (x 2 1)
        have b49134 := hb (x 3 14)
        clear * - r49132 b49133 b49134 d49127
        omega
      have d49135 : (x 3 6).toNat = 0 := by
        have r49136 : (x 3 6).toNat ≤ (x 3 14).toNat := himp _ _ (hp6 3)
        have b49137 := hb (x 3 6)
        have b49138 := hb (x 3 14)
        clear * - r49136 b49137 b49138 d49131
        omega
      have d49139 : (x 3 2).toNat = 0 := by
        have r49140 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
        have b49141 := hb (x 3 2)
        have b49142 := hb (x 3 14)
        clear * - r49140 b49141 b49142 d49131
        omega
      have d49143 : (x 4 1 && x 4 14).toNat = 1 := by
        have r49144 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b49145 := hb (x 3 2)
        have b49146 := hb (x 5 13)
        have b49147 := hb (x 4 1 && x 4 14)
        clear * - r49144 b49145 b49146 b49147 d49102 d49139
        omega
      have d49148 : (x 4 1).toNat = 1 := by
        have r49149 := hand1 (x 4 1) (x 4 14)
        have b49150 := hb (x 4 1)
        have b49151 := hb (x 4 1 && x 4 14)
        clear * - r49149 b49150 b49151 d49143
        omega
      have d49152 : (x 5 14).toNat = 0 := by
        have r49153 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b49154 := hb (x 4 1)
        have b49155 := hb (x 5 14)
        clear * - r49153 b49154 b49155 d49148
        omega
      have d49156 : (x 5 3 && x 5 14).toNat = 0 := by
        have r49157 := hand2 (x 5 3) (x 5 14)
        have b49158 := hb (x 5 14)
        have b49159 := hb (x 5 3 && x 5 14)
        clear * - r49157 b49158 b49159 d49152
        omega
      have d49160 : (x 5 6).toNat = 0 := by
        have r49161 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
        have b49162 := hb (x 5 6)
        have b49163 := hb (x 5 14)
        clear * - r49161 b49162 b49163 d49152
        omega
      have d49164 : (x 5 6 && x 5 11).toNat = 0 := by
        have r49165 := hand1 (x 5 6) (x 5 11)
        have b49166 := hb (x 5 6)
        have b49167 := hb (x 5 6 && x 5 11)
        clear * - r49165 b49166 b49167 d49160
        omega
      have d49168 : (x 5 2).toNat = 0 := by
        have r49169 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
        have b49170 := hb (x 5 2)
        have b49171 := hb (x 5 14)
        clear * - r49169 b49170 b49171 d49152
        omega
      have d49172 : (x 2 2).toNat = 0 := by
        have r49173 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e49174 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e49175 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b49176 := hb (x 1 3)
        have b49177 := hb (x 2 2)
        have b49178 := hb (x 3 13)
        have b49179 := hb (x 4 12)
        clear * - r49173 e49174 e49175 b49176 b49177 b49178 b49179 d49054 d49058 f46717
        omega
      have d49180 : (x 4 13).toNat = 1 := by
        have r49181 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b49182 := hb (x 2 2)
        have b49183 := hb (x 4 13)
        have b49184 := hb (x 3 1 && x 3 14)
        clear * - r49181 b49182 b49183 b49184 d49090 d49172
        omega
      have d49185 : (x 5 12).toNat = 0 := by
        have r49186 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e49187 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e49188 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b49189 := hb (x 2 3)
        have b49190 := hb (x 3 2)
        have b49191 := hb (x 4 13)
        have b49192 := hb (x 5 12)
        clear * - r49186 e49187 e49188 b49189 b49190 b49191 b49192 d49180 d49139
        omega
      have d49193 : (x 5 3 && x 5 12).toNat = 0 := by
        have r49194 := hand2 (x 5 3) (x 5 12)
        have b49195 := hb (x 5 12)
        have b49196 := hb (x 5 3 && x 5 12)
        clear * - r49194 b49195 b49196 d49185
        omega
      have d49197 : (x 5 4).toNat = 0 := by
        have r49198 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
        have b49199 := hb (x 5 4)
        have b49200 := hb (x 5 12)
        clear * - r49198 b49199 b49200 d49185
        omega
      have d49201 : (x 5 4 && x 5 11).toNat = 0 := by
        have r49202 := hand1 (x 5 4) (x 5 11)
        have b49203 := hb (x 5 4)
        have b49204 := hb (x 5 4 && x 5 11)
        clear * - r49202 b49203 b49204 d49197
        omega
      have d49205 : (x 4 3).toNat = 1 := by
        have r49206 := hand1 (x 4 3) (x 4 12)
        have b49207 := hb (x 4 3)
        have b49208 := hb (x 4 3 && x 4 12)
        clear * - r49206 b49207 b49208 d49045
        omega
      have d49209 : (x 7 12).toNat = 0 := by
        have r49210 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e49211 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
        have e49212 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
        have b49213 := hb (x 4 3)
        have b49214 := hb (x 5 2)
        have b49215 := hb (x 6 13)
        have b49216 := hb (x 7 12)
        clear * - r49210 e49211 e49212 b49213 b49214 b49215 b49216 d49168 d49205
        omega
      have d49217 : (x 7 1 && x 7 12).toNat = 0 := by
        have r49218 := hand2 (x 7 1) (x 7 12)
        have b49219 := hb (x 7 12)
        have b49220 := hb (x 7 1 && x 7 12)
        clear * - r49218 b49219 b49220 d49209
        omega
      have d49221 : (x 7 4).toNat = 0 := by
        have r49222 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
        have b49223 := hb (x 7 4)
        have b49224 := hb (x 7 12)
        clear * - r49222 b49223 b49224 d49209
        omega
      have d49225 : (x 6 13).toNat = 0 := by
        have r49226 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e49227 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
        have e49228 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
        have b49229 := hb (x 4 3)
        have b49230 := hb (x 5 2)
        have b49231 := hb (x 6 13)
        have b49232 := hb (x 7 12)
        clear * - r49226 e49227 e49228 b49229 b49230 b49231 b49232 d49209 d49168 d49205
        omega
      have d49233 : (x 6 2 && x 6 13).toNat = 0 := by
        have r49234 := hand2 (x 6 2) (x 6 13)
        have b49235 := hb (x 6 13)
        have b49236 := hb (x 6 2 && x 6 13)
        clear * - r49234 b49235 b49236 d49225
        omega
      have d49237 : (x 6 5).toNat = 0 := by
        have r49238 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
        have b49239 := hb (x 6 5)
        have b49240 := hb (x 6 13)
        clear * - r49238 b49239 b49240 d49225
        omega
      have d49241 : (x 4 4).toNat = 0 := by
        have r49242 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e49243 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e49244 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e49245 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e49246 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e49247 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e49248 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b49249 := hb (x 1 7)
        have b49250 := hb (x 2 6)
        have b49251 := hb (x 3 5)
        have b49252 := hb (x 4 4)
        have b49253 := hb (x 5 11)
        have b49254 := hb (x 6 10)
        have b49255 := hb (x 7 9)
        have b49256 := hb (x 8 8)
        clear * - r49242 e49243 e49244 e49245 e49246 e49247 e49248 b49249 b49250 b49251 b49252 b49253 b49254 b49255 b49256 d48945 d48969 d48993 d49021 d49114 f48944
        omega
      have d49257 : (x 4 4 && x 4 13).toNat = 0 := by
        have r49258 := hand1 (x 4 4) (x 4 13)
        have b49259 := hb (x 4 4)
        have b49260 := hb (x 4 4 && x 4 13)
        clear * - r49258 b49259 b49260 d49241
        omega
      have d49261 : (x 8 11).toNat = 1 := by
        have r49262 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b49263 := hb (x 4 4)
        have b49264 := hb (x 8 11)
        have b49265 := hb (x 7 1 && x 7 12)
        have b49266 := hb (x 6 2 && x 6 13)
        have b49267 := hb (x 5 3 && x 5 14)
        clear * - r49262 b49263 b49264 b49265 b49266 b49267 d49217 d49233 d49156 d49241
        omega
      have d49268 : (x 8 3).toNat = 1 := by
        have r49269 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
        have b49270 := hb (x 8 3)
        have b49271 := hb (x 8 11)
        clear * - r49269 b49270 b49271 d49261
        omega
      have d49272 : (x 11 12).toNat = 0 := by
        have r49273 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e49274 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e49275 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b49276 := hb (x 8 3)
        have b49277 := hb (x 9 2)
        have b49278 := hb (x 10 13)
        have b49279 := hb (x 11 12)
        clear * - r49273 e49274 e49275 b49276 b49277 b49278 b49279 d49268
        omega
      have d49280 : (x 10 13).toNat = 0 := by
        have r49281 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e49282 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e49283 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b49284 := hb (x 8 3)
        have b49285 := hb (x 9 2)
        have b49286 := hb (x 10 13)
        have b49287 := hb (x 11 12)
        clear * - r49281 e49282 e49283 b49284 b49285 b49286 b49287 d49272 d49268
        omega
      have d49288 : (x 9 2).toNat = 0 := by
        have r49289 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e49290 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e49291 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b49292 := hb (x 8 3)
        have b49293 := hb (x 9 2)
        have b49294 := hb (x 10 13)
        have b49295 := hb (x 11 12)
        clear * - r49289 e49290 e49291 b49292 b49293 b49294 b49295 d49272 d49280 d49268
        omega
      have d49296 : (x 9 2 && x 9 7).toNat = 0 := by
        have r49297 := hand1 (x 9 2) (x 9 7)
        have b49298 := hb (x 9 2)
        have b49299 := hb (x 9 2 && x 9 7)
        clear * - r49297 b49298 b49299 d49288
        omega
      have d49300 : (x 9 10).toNat = 0 := by
        have r49301 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
        have b49302 := hb (x 9 2)
        have b49303 := hb (x 9 10)
        clear * - r49301 b49302 b49303 d49288
        omega
      have d49304 : (x 11 8).toNat = 0 := by
        have r49305 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e49306 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
        have e49307 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
        have e49308 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
        have e49309 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
        have e49310 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
        have e49311 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
        have b49312 := hb (x 4 7)
        have b49313 := hb (x 5 6)
        have b49314 := hb (x 6 5)
        have b49315 := hb (x 7 4)
        have b49316 := hb (x 8 11)
        have b49317 := hb (x 9 10)
        have b49318 := hb (x 10 9)
        have b49319 := hb (x 11 8)
        clear * - r49305 e49306 e49307 e49308 e49309 e49310 e49311 b49312 b49313 b49314 b49315 b49316 b49317 b49318 b49319 d49300 d49261 d49221 d49237 d49160
        omega
      have d49320 : (x 10 9).toNat = 0 := by
        have r49321 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e49322 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
        have e49323 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
        have e49324 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
        have e49325 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
        have e49326 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
        have e49327 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
        have b49328 := hb (x 4 7)
        have b49329 := hb (x 5 6)
        have b49330 := hb (x 6 5)
        have b49331 := hb (x 7 4)
        have b49332 := hb (x 8 11)
        have b49333 := hb (x 9 10)
        have b49334 := hb (x 10 9)
        have b49335 := hb (x 11 8)
        clear * - r49321 e49322 e49323 e49324 e49325 e49326 e49327 b49328 b49329 b49330 b49331 b49332 b49333 b49334 b49335 d49304 d49300 d49261 d49221 d49237 d49160
        omega
      have d49336 : (x 4 7).toNat = 0 := by
        have r49337 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e49338 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
        have e49339 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
        have e49340 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
        have e49341 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
        have e49342 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
        have e49343 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
        have b49344 := hb (x 4 7)
        have b49345 := hb (x 5 6)
        have b49346 := hb (x 6 5)
        have b49347 := hb (x 7 4)
        have b49348 := hb (x 8 11)
        have b49349 := hb (x 9 10)
        have b49350 := hb (x 10 9)
        have b49351 := hb (x 11 8)
        clear * - r49337 e49338 e49339 e49340 e49341 e49342 e49343 b49344 b49345 b49346 b49347 b49348 b49349 b49350 b49351 d49304 d49320 d49300 d49261 d49221 d49237 d49160
        omega
      have d49352 : (x 4 7 && x 4 12).toNat = 0 := by
        have r49353 := hand1 (x 4 7) (x 4 12)
        have b49354 := hb (x 4 7)
        have b49355 := hb (x 4 7 && x 4 12)
        clear * - r49353 b49354 b49355 d49336
        omega
      have d49356 : (x 2 6).toNat = 0 := by
        have r49357 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e49358 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e49359 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e49360 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e49361 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e49362 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e49363 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b49364 := hb (x 1 7)
        have b49365 := hb (x 2 6)
        have b49366 := hb (x 3 5)
        have b49367 := hb (x 4 4)
        have b49368 := hb (x 5 11)
        have b49369 := hb (x 6 10)
        have b49370 := hb (x 7 9)
        have b49371 := hb (x 8 8)
        clear * - r49357 e49358 e49359 e49360 e49361 e49362 e49363 b49364 b49365 b49366 b49367 b49368 b49369 b49370 b49371 d48945 d48969 d48993 d49021 d49241 d49114 f48944
        omega
      have r49372 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r49373 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e49374 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
      have e49375 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
      have e49376 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
      have e49377 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
      have e49378 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
      have e49379 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
      have r49380 : 1 ≤ (x 11 5).toNat + (x 10 1 && x 10 6).toNat + (x 9 2 && x 9 7).toNat + (x 8 3 && x 8 8).toNat + (x 7 4 && x 7 9).toNat + (x 6 5 && x 6 10).toNat + (x 5 6 && x 5 11).toNat + (x 4 7 && x 4 12).toNat + (x 3 8 && x 3 13).toNat + (x 2 9 && x 2 14).toNat + (x 1 10).toNat := by have q := hcov5 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r49381 : 1 ≤ (x 9 7).toNat + (x 8 1 && x 8 8).toNat + (x 7 2 && x 7 9).toNat + (x 6 3 && x 6 10).toNat + (x 5 4 && x 5 11).toNat + (x 4 5 && x 4 12).toNat + (x 3 6 && x 3 13).toNat + (x 2 7 && x 2 14).toNat + (x 1 8).toNat := by have q := hcov7 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r49382 : 1 ≤ (x 8 9).toNat + (x 7 1 && x 7 10).toNat + (x 6 2 && x 6 11).toNat + (x 5 3 && x 5 12).toNat + (x 4 4 && x 4 13).toNat + (x 3 5 && x 3 14).toNat + (x 2 6).toNat := by have q := hcov9 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r49383 := hand2 (x 10 1) (x 10 6)
      have r49384 := hand1 (x 4 5) (x 4 12)
      have r49385 := hand1 (x 2 7) (x 2 14)
      have r49386 := hand2 (x 7 1) (x 7 10)
      have r49387 := hand2 (x 6 2) (x 6 11)
      linarith only [r49372, r49373, e49374, e49375, e49376, e49377, e49378, e49379, r49380, r49381, r49382, r49383, r49384, r49385, r49386, r49387, g27, g29, d49356, d46712, d49135, d49058, d49054, d49197, d49021, d48993, d48969, d48945, d49296, d48965, d48989, d49017, d49164, d49352, g80, g81, d48961, d48985, d49013, d49201, d49110, d49193, d49257, d49118]
  · have f49434 : (x 1 3).toNat = 1 := by rw [h46716]; rfl
    have d49435 : (x 4 12).toNat = 0 := by
      have r49436 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e49437 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e49438 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b49439 := hb (x 1 3)
      have b49440 := hb (x 2 2)
      have b49441 := hb (x 3 13)
      have b49442 := hb (x 4 12)
      clear * - r49436 e49437 e49438 b49439 b49440 b49441 b49442 f49434
      omega
    have d49443 : (x 4 1 && x 4 12).toNat = 0 := by
      have r49444 := hand2 (x 4 1) (x 4 12)
      have b49445 := hb (x 4 12)
      have b49446 := hb (x 4 1 && x 4 12)
      clear * - r49444 b49445 b49446 d49435
      omega
    have d49447 : (x 4 4).toNat = 0 := by
      have r49448 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
      have b49449 := hb (x 4 4)
      have b49450 := hb (x 4 12)
      clear * - r49448 b49449 b49450 d49435
      omega
    have d49451 : (x 3 13).toNat = 0 := by
      have r49452 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e49453 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e49454 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b49455 := hb (x 1 3)
      have b49456 := hb (x 2 2)
      have b49457 := hb (x 3 13)
      have b49458 := hb (x 4 12)
      clear * - r49452 e49453 e49454 b49455 b49456 b49457 b49458 d49435 f49434
      omega
    have d49459 : (x 3 2 && x 3 13).toNat = 0 := by
      have r49460 := hand2 (x 3 2) (x 3 13)
      have b49461 := hb (x 3 13)
      have b49462 := hb (x 3 2 && x 3 13)
      clear * - r49460 b49461 b49462 d49451
      omega
    have d49463 : (x 2 1 && x 2 14).toNat = 1 := by
      have r49464 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b49465 := hb (x 1 2)
      have b49466 := hb (x 3 13)
      have b49467 := hb (x 2 1 && x 2 14)
      clear * - r49464 b49465 b49466 b49467 d49451 g23
      omega
    have d49468 : (x 2 1).toNat = 1 := by
      have r49469 := hand1 (x 2 1) (x 2 14)
      have b49470 := hb (x 2 1)
      have b49471 := hb (x 2 1 && x 2 14)
      clear * - r49469 b49470 b49471 d49463
      omega
    have d49472 : (x 3 14).toNat = 0 := by
      have r49473 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b49474 := hb (x 2 1)
      have b49475 := hb (x 3 14)
      clear * - r49473 b49474 b49475 d49468
      omega
    have d49476 : (x 3 1 && x 3 14).toNat = 0 := by
      have r49477 := hand2 (x 3 1) (x 3 14)
      have b49478 := hb (x 3 14)
      have b49479 := hb (x 3 1 && x 3 14)
      clear * - r49477 b49478 b49479 d49472
      omega
    have d49480 : (x 3 2).toNat = 0 := by
      have r49481 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
      have b49482 := hb (x 3 2)
      have b49483 := hb (x 3 14)
      clear * - r49481 b49482 b49483 d49472
      omega
    have d49484 : (x 2 2).toNat = 0 := by
      have r49485 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e49486 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e49487 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b49488 := hb (x 1 3)
      have b49489 := hb (x 2 2)
      have b49490 := hb (x 3 13)
      have b49491 := hb (x 4 12)
      clear * - r49485 e49486 e49487 b49488 b49489 b49490 b49491 d49435 d49451 f49434
      omega
    have d49492 : (x 4 13).toNat = 1 := by
      have r49493 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b49494 := hb (x 2 2)
      have b49495 := hb (x 4 13)
      have b49496 := hb (x 3 1 && x 3 14)
      clear * - r49493 b49494 b49495 b49496 d49476 d49484
      omega
    have d49497 : (x 4 1).toNat = 1 := by
      have r49498 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
      have b49499 := hb (x 4 1)
      have b49500 := hb (x 4 13)
      clear * - r49498 b49499 b49500 d49492
      omega
    have d49501 : (x 5 14).toNat = 0 := by
      have r49502 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b49503 := hb (x 4 1)
      have b49504 := hb (x 5 14)
      clear * - r49502 b49503 b49504 d49497
      omega
    have d49505 : (x 5 3 && x 5 14).toNat = 0 := by
      have r49506 := hand2 (x 5 3) (x 5 14)
      have b49507 := hb (x 5 14)
      have b49508 := hb (x 5 3 && x 5 14)
      clear * - r49506 b49507 b49508 d49501
      omega
    have d49509 : (x 5 2).toNat = 0 := by
      have r49510 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
      have b49511 := hb (x 5 2)
      have b49512 := hb (x 5 14)
      clear * - r49510 b49511 b49512 d49501
      omega
    have d49513 : (x 5 12).toNat = 0 := by
      have r49514 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e49515 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e49516 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b49517 := hb (x 2 3)
      have b49518 := hb (x 3 2)
      have b49519 := hb (x 4 13)
      have b49520 := hb (x 5 12)
      clear * - r49514 e49515 e49516 b49517 b49518 b49519 b49520 d49492 d49480
      omega
    have d49521 : (x 5 4).toNat = 0 := by
      have r49522 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
      have b49523 := hb (x 5 4)
      have b49524 := hb (x 5 12)
      clear * - r49522 b49523 b49524 d49513
      omega
    have d49525 : (x 2 3).toNat = 0 := by
      have r49526 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e49527 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e49528 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b49529 := hb (x 2 3)
      have b49530 := hb (x 3 2)
      have b49531 := hb (x 4 13)
      have b49532 := hb (x 5 12)
      clear * - r49526 e49527 e49528 b49529 b49530 b49531 b49532 d49513 d49492 d49480
      omega
    have d49533 : (x 2 3 && x 2 14).toNat = 0 := by
      have r49534 := hand1 (x 2 3) (x 2 14)
      have b49535 := hb (x 2 3)
      have b49536 := hb (x 2 3 && x 2 14)
      clear * - r49534 b49535 b49536 d49525
      omega
    have d49537 : (x 5 11).toNat = 1 := by
      have r49538 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b49539 := hb (x 1 4)
      have b49540 := hb (x 5 11)
      have b49541 := hb (x 4 1 && x 4 12)
      have b49542 := hb (x 3 2 && x 3 13)
      have b49543 := hb (x 2 3 && x 2 14)
      clear * - r49538 b49539 b49540 b49541 b49542 b49543 d49443 d49459 d49533 g24
      omega
    have d49544 : (x 5 3).toNat = 1 := by
      have r49545 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
      have b49546 := hb (x 5 3)
      have b49547 := hb (x 5 11)
      clear * - r49545 b49546 b49547 d49537
      omega
    have d49548 : (x 8 12).toNat = 0 := by
      have r49549 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e49550 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e49551 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have b49552 := hb (x 5 3)
      have b49553 := hb (x 6 2)
      have b49554 := hb (x 7 13)
      have b49555 := hb (x 8 12)
      clear * - r49549 e49550 e49551 b49552 b49553 b49554 b49555 d49544
      omega
    have d49556 : (x 8 1 && x 8 12).toNat = 0 := by
      have r49557 := hand2 (x 8 1) (x 8 12)
      have b49558 := hb (x 8 12)
      have b49559 := hb (x 8 1 && x 8 12)
      clear * - r49557 b49558 b49559 d49548
      omega
    have d49560 : (x 8 4).toNat = 0 := by
      have r49561 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
      have b49562 := hb (x 8 4)
      have b49563 := hb (x 8 12)
      clear * - r49561 b49562 b49563 d49548
      omega
    have d49564 : (x 7 13).toNat = 0 := by
      have r49565 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e49566 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e49567 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have b49568 := hb (x 5 3)
      have b49569 := hb (x 6 2)
      have b49570 := hb (x 7 13)
      have b49571 := hb (x 8 12)
      clear * - r49565 e49566 e49567 b49568 b49569 b49570 b49571 d49548 d49544
      omega
    have d49572 : (x 7 2 && x 7 13).toNat = 0 := by
      have r49573 := hand2 (x 7 2) (x 7 13)
      have b49574 := hb (x 7 13)
      have b49575 := hb (x 7 2 && x 7 13)
      clear * - r49573 b49574 b49575 d49564
      omega
    have d49576 : (x 6 1 && x 6 14).toNat = 1 := by
      have r49577 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b49578 := hb (x 5 2)
      have b49579 := hb (x 7 13)
      have b49580 := hb (x 6 1 && x 6 14)
      clear * - r49577 b49578 b49579 b49580 d49564 d49509
      omega
    have d49581 : (x 6 1).toNat = 1 := by
      have r49582 := hand1 (x 6 1) (x 6 14)
      have b49583 := hb (x 6 1)
      have b49584 := hb (x 6 1 && x 6 14)
      clear * - r49582 b49583 b49584 d49576
      omega
    have d49585 : (x 7 14).toNat = 0 := by
      have r49586 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b49587 := hb (x 6 1)
      have b49588 := hb (x 7 14)
      clear * - r49586 b49587 b49588 d49581
      omega
    have d49589 : (x 7 1 && x 7 14).toNat = 0 := by
      have r49590 := hand2 (x 7 1) (x 7 14)
      have b49591 := hb (x 7 14)
      have b49592 := hb (x 7 1 && x 7 14)
      clear * - r49590 b49591 b49592 d49585
      omega
    have d49593 : (x 7 2).toNat = 0 := by
      have r49594 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
      have b49595 := hb (x 7 2)
      have b49596 := hb (x 7 14)
      clear * - r49594 b49595 b49596 d49585
      omega
    have d49597 : (x 6 2).toNat = 0 := by
      have r49598 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e49599 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e49600 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have b49601 := hb (x 5 3)
      have b49602 := hb (x 6 2)
      have b49603 := hb (x 7 13)
      have b49604 := hb (x 8 12)
      clear * - r49598 e49599 e49600 b49601 b49602 b49603 b49604 d49548 d49564 d49544
      omega
    have d49605 : (x 6 2 && x 6 13).toNat = 0 := by
      have r49606 := hand1 (x 6 2) (x 6 13)
      have b49607 := hb (x 6 2)
      have b49608 := hb (x 6 2 && x 6 13)
      clear * - r49606 b49607 b49608 d49597
      omega
    have d49609 : (x 8 13).toNat = 1 := by
      have r49610 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b49611 := hb (x 6 2)
      have b49612 := hb (x 8 13)
      have b49613 := hb (x 7 1 && x 7 14)
      clear * - r49610 b49611 b49612 b49613 d49589 d49597
      omega
    have d49614 : (x 8 1).toNat = 1 := by
      have r49615 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
      have b49616 := hb (x 8 1)
      have b49617 := hb (x 8 13)
      clear * - r49615 b49616 b49617 d49609
      omega
    have d49618 : (x 9 14).toNat = 0 := by
      have r49619 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b49620 := hb (x 8 1)
      have b49621 := hb (x 9 14)
      clear * - r49619 b49620 b49621 d49614
      omega
    have d49622 : (x 9 3 && x 9 14).toNat = 0 := by
      have r49623 := hand2 (x 9 3) (x 9 14)
      have b49624 := hb (x 9 14)
      have b49625 := hb (x 9 3 && x 9 14)
      clear * - r49623 b49624 b49625 d49618
      omega
    have d49626 : (x 9 2).toNat = 0 := by
      have r49627 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
      have b49628 := hb (x 9 2)
      have b49629 := hb (x 9 14)
      clear * - r49627 b49628 b49629 d49618
      omega
    have d49630 : (x 9 12).toNat = 0 := by
      have r49631 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e49632 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
      have e49633 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
      have b49634 := hb (x 6 3)
      have b49635 := hb (x 7 2)
      have b49636 := hb (x 8 13)
      have b49637 := hb (x 9 12)
      clear * - r49631 e49632 e49633 b49634 b49635 b49636 b49637 d49609 d49593
      omega
    have d49638 : (x 9 4).toNat = 0 := by
      have r49639 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
      have b49640 := hb (x 9 4)
      have b49641 := hb (x 9 12)
      clear * - r49639 b49640 b49641 d49630
      omega
    have d49642 : (x 6 3).toNat = 0 := by
      have r49643 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e49644 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
      have e49645 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
      have b49646 := hb (x 6 3)
      have b49647 := hb (x 7 2)
      have b49648 := hb (x 8 13)
      have b49649 := hb (x 9 12)
      clear * - r49643 e49644 e49645 b49646 b49647 b49648 b49649 d49630 d49609 d49593
      omega
    have d49650 : (x 6 3 && x 6 14).toNat = 0 := by
      have r49651 := hand1 (x 6 3) (x 6 14)
      have b49652 := hb (x 6 3)
      have b49653 := hb (x 6 3 && x 6 14)
      clear * - r49651 b49652 b49653 d49642
      omega
    have d49654 : (x 9 11).toNat = 1 := by
      have r49655 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b49656 := hb (x 5 4)
      have b49657 := hb (x 9 11)
      have b49658 := hb (x 8 1 && x 8 12)
      have b49659 := hb (x 7 2 && x 7 13)
      have b49660 := hb (x 6 3 && x 6 14)
      clear * - r49655 b49656 b49657 b49658 b49659 b49660 d49556 d49572 d49650 d49521
      omega
    have d49661 : (x 9 3).toNat = 1 := by
      have r49662 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
      have b49663 := hb (x 9 3)
      have b49664 := hb (x 9 11)
      clear * - r49662 b49663 b49664 d49654
      omega
    have d49665 : (x 12 12).toNat = 0 := by
      have r49666 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e49667 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
      have e49668 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
      have b49669 := hb (x 9 3)
      have b49670 := hb (x 10 2)
      have b49671 := hb (x 11 13)
      have b49672 := hb (x 12 12)
      clear * - r49666 e49667 e49668 b49669 b49670 b49671 b49672 d49661
      omega
    have d49673 : (x 12 1 && x 12 12).toNat = 0 := by
      have r49674 := hand2 (x 12 1) (x 12 12)
      have b49675 := hb (x 12 12)
      have b49676 := hb (x 12 1 && x 12 12)
      clear * - r49674 b49675 b49676 d49665
      omega
    have d49677 : (x 12 4).toNat = 0 := by
      have r49678 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
      have b49679 := hb (x 12 4)
      have b49680 := hb (x 12 12)
      clear * - r49678 b49679 b49680 d49665
      omega
    have d49681 : (x 11 13).toNat = 0 := by
      have r49682 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e49683 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
      have e49684 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
      have b49685 := hb (x 9 3)
      have b49686 := hb (x 10 2)
      have b49687 := hb (x 11 13)
      have b49688 := hb (x 12 12)
      clear * - r49682 e49683 e49684 b49685 b49686 b49687 b49688 d49665 d49661
      omega
    have d49689 : (x 11 2 && x 11 13).toNat = 0 := by
      have r49690 := hand2 (x 11 2) (x 11 13)
      have b49691 := hb (x 11 13)
      have b49692 := hb (x 11 2 && x 11 13)
      clear * - r49690 b49691 b49692 d49681
      omega
    have d49693 : (x 10 1 && x 10 14).toNat = 1 := by
      have r49694 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b49695 := hb (x 9 2)
      have b49696 := hb (x 11 13)
      have b49697 := hb (x 10 1 && x 10 14)
      clear * - r49694 b49695 b49696 b49697 d49681 d49626
      omega
    have d49698 : (x 10 14).toNat = 1 := by
      have r49699 := hand2 (x 10 1) (x 10 14)
      have b49700 := hb (x 10 14)
      have b49701 := hb (x 10 1 && x 10 14)
      clear * - r49699 b49700 b49701 d49693
      omega
    have d49702 : (x 9 1).toNat = 0 := by
      have r49703 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b49704 := hb (x 9 1)
      have b49705 := hb (x 10 14)
      clear * - r49703 b49704 b49705 d49698
      omega
    have d49706 : (x 9 13).toNat = 0 := by
      have r49707 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
      have b49708 := hb (x 9 1)
      have b49709 := hb (x 9 13)
      clear * - r49707 b49708 b49709 d49702
      omega
    have d49710 : (x 8 1 && x 8 14).toNat = 1 := by
      have r49711 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b49712 := hb (x 7 2)
      have b49713 := hb (x 9 13)
      have b49714 := hb (x 8 1 && x 8 14)
      clear * - r49711 b49712 b49713 b49714 d49706 d49593
      omega
    have d49715 : (x 8 14).toNat = 1 := by
      have r49716 := hand2 (x 8 1) (x 8 14)
      have b49717 := hb (x 8 14)
      have b49718 := hb (x 8 1 && x 8 14)
      clear * - r49716 b49717 b49718 d49710
      omega
    have d49719 : (x 7 1).toNat = 0 := by
      have r49720 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b49721 := hb (x 7 1)
      have b49722 := hb (x 8 14)
      clear * - r49720 b49721 b49722 d49715
      omega
    have d49723 : (x 7 1 && x 7 12).toNat = 0 := by
      have r49724 := hand1 (x 7 1) (x 7 12)
      have b49725 := hb (x 7 1)
      have b49726 := hb (x 7 1 && x 7 12)
      clear * - r49724 b49725 b49726 d49719
      omega
    have d49727 : (x 8 11).toNat = 1 := by
      have r49728 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b49729 := hb (x 4 4)
      have b49730 := hb (x 8 11)
      have b49731 := hb (x 7 1 && x 7 12)
      have b49732 := hb (x 6 2 && x 6 13)
      have b49733 := hb (x 5 3 && x 5 14)
      clear * - r49728 b49729 b49730 b49731 b49732 b49733 d49723 d49605 d49505 d49447
      omega
    have d49734 : (x 8 3).toNat = 1 := by
      have r49735 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
      have b49736 := hb (x 8 3)
      have b49737 := hb (x 8 11)
      clear * - r49735 b49736 b49737 d49727
      omega
    have d49738 : (x 11 12).toNat = 0 := by
      have r49739 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e49740 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
      have e49741 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
      have b49742 := hb (x 8 3)
      have b49743 := hb (x 9 2)
      have b49744 := hb (x 10 13)
      have b49745 := hb (x 11 12)
      clear * - r49739 e49740 e49741 b49742 b49743 b49744 b49745 d49626 d49734
      omega
    have d49746 : (x 11 1 && x 11 12).toNat = 0 := by
      have r49747 := hand2 (x 11 1) (x 11 12)
      have b49748 := hb (x 11 12)
      have b49749 := hb (x 11 1 && x 11 12)
      clear * - r49747 b49748 b49749 d49738
      omega
    have d49750 : (x 10 13).toNat = 0 := by
      have r49751 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e49752 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
      have e49753 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
      have b49754 := hb (x 8 3)
      have b49755 := hb (x 9 2)
      have b49756 := hb (x 10 13)
      have b49757 := hb (x 11 12)
      clear * - r49751 e49752 e49753 b49754 b49755 b49756 b49757 d49738 d49626 d49734
      omega
    have d49758 : (x 10 2 && x 10 13).toNat = 0 := by
      have r49759 := hand2 (x 10 2) (x 10 13)
      have b49760 := hb (x 10 13)
      have b49761 := hb (x 10 2 && x 10 13)
      clear * - r49759 b49760 b49761 d49750
      omega
    have d49762 : (x 12 11).toNat = 1 := by
      have r49763 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b49764 := hb (x 8 4)
      have b49765 := hb (x 12 11)
      have b49766 := hb (x 11 1 && x 11 12)
      have b49767 := hb (x 10 2 && x 10 13)
      have b49768 := hb (x 9 3 && x 9 14)
      clear * - r49763 b49764 b49765 b49766 b49767 b49768 d49746 d49758 d49622 d49560
      omega
    have d49769 : (x 12 3).toNat = 1 := by
      have r49770 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
      have b49771 := hb (x 12 3)
      have b49772 := hb (x 12 11)
      clear * - r49770 b49771 b49772 d49762
      omega
    have d49773 : (x 15 12).toNat = 0 := by
      have r49774 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e49775 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
      have e49776 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
      have b49777 := hb (x 12 3)
      have b49778 := hb (x 13 2)
      have b49779 := hb (x 14 13)
      have b49780 := hb (x 15 12)
      clear * - r49774 e49775 e49776 b49777 b49778 b49779 b49780 d49769
      omega
    have d49781 : (x 15 1 && x 15 12).toNat = 0 := by
      have r49782 := hand2 (x 15 1) (x 15 12)
      have b49783 := hb (x 15 12)
      have b49784 := hb (x 15 1 && x 15 12)
      clear * - r49782 b49783 b49784 d49773
      omega
    have d49785 : (x 14 13).toNat = 0 := by
      have r49786 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e49787 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
      have e49788 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
      have b49789 := hb (x 12 3)
      have b49790 := hb (x 13 2)
      have b49791 := hb (x 14 13)
      have b49792 := hb (x 15 12)
      clear * - r49786 e49787 e49788 b49789 b49790 b49791 b49792 d49773 d49769
      omega
    have d49793 : (x 14 2 && x 14 13).toNat = 0 := by
      have r49794 := hand2 (x 14 2) (x 14 13)
      have b49795 := hb (x 14 13)
      have b49796 := hb (x 14 2 && x 14 13)
      clear * - r49794 b49795 b49796 d49785
      omega
    have d49797 : (x 13 2).toNat = 0 := by
      have r49798 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e49799 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
      have e49800 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
      have b49801 := hb (x 12 3)
      have b49802 := hb (x 13 2)
      have b49803 := hb (x 14 13)
      have b49804 := hb (x 15 12)
      clear * - r49798 e49799 e49800 b49801 b49802 b49803 b49804 d49773 d49785 d49769
      omega
    have d49805 : (x 10 1).toNat = 1 := by
      have r49806 := hand1 (x 10 1) (x 10 14)
      have b49807 := hb (x 10 1)
      have b49808 := hb (x 10 1 && x 10 14)
      clear * - r49806 b49807 b49808 d49693
      omega
    have d49809 : (x 11 14).toNat = 0 := by
      have r49810 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b49811 := hb (x 10 1)
      have b49812 := hb (x 11 14)
      clear * - r49810 b49811 b49812 d49805
      omega
    have d49813 : (x 11 1 && x 11 14).toNat = 0 := by
      have r49814 := hand2 (x 11 1) (x 11 14)
      have b49815 := hb (x 11 14)
      have b49816 := hb (x 11 1 && x 11 14)
      clear * - r49814 b49815 b49816 d49809
      omega
    have d49817 : (x 11 2).toNat = 0 := by
      have r49818 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
      have b49819 := hb (x 11 2)
      have b49820 := hb (x 11 14)
      clear * - r49818 b49819 b49820 d49809
      omega
    have d49821 : (x 10 2).toNat = 0 := by
      have r49822 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e49823 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
      have e49824 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
      have b49825 := hb (x 9 3)
      have b49826 := hb (x 10 2)
      have b49827 := hb (x 11 13)
      have b49828 := hb (x 12 12)
      clear * - r49822 e49823 e49824 b49825 b49826 b49827 b49828 d49665 d49681 d49661
      omega
    have d49829 : (x 12 13).toNat = 1 := by
      have r49830 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b49831 := hb (x 10 2)
      have b49832 := hb (x 12 13)
      have b49833 := hb (x 11 1 && x 11 14)
      clear * - r49830 b49831 b49832 b49833 d49813 d49821
      omega
    have d49834 : (x 12 1).toNat = 1 := by
      have r49835 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
      have b49836 := hb (x 12 1)
      have b49837 := hb (x 12 13)
      clear * - r49835 b49836 b49837 d49829
      omega
    have d49838 : (x 13 14).toNat = 0 := by
      have r49839 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b49840 := hb (x 12 1)
      have b49841 := hb (x 13 14)
      clear * - r49839 b49840 b49841 d49834
      omega
    have d49842 : (x 13 1 && x 13 14).toNat = 0 := by
      have r49843 := hand2 (x 13 1) (x 13 14)
      have b49844 := hb (x 13 14)
      have b49845 := hb (x 13 1 && x 13 14)
      clear * - r49843 b49844 b49845 d49838
      omega
    have d49846 : (x 12 2).toNat = 1 := by
      have r49847 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b49848 := hb (x 12 2)
      have b49849 := hb (x 14 13)
      have b49850 := hb (x 13 1 && x 13 14)
      clear * - r49847 b49848 b49849 b49850 d49785 d49842
      omega
    have d49851 : (x 14 12).toNat = 0 := by
      have r49852 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e49853 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
      have e49854 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
      have b49855 := hb (x 11 3)
      have b49856 := hb (x 12 2)
      have b49857 := hb (x 13 13)
      have b49858 := hb (x 14 12)
      clear * - r49852 e49853 e49854 b49855 b49856 b49857 b49858 d49846
      omega
    have d49859 : (x 14 4).toNat = 0 := by
      have r49860 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
      have b49861 := hb (x 14 4)
      have b49862 := hb (x 14 12)
      clear * - r49860 b49861 b49862 d49851
      omega
    have d49863 : (x 14 4 && x 14 14).toNat = 0 := by
      have r49864 := hand1 (x 14 4) (x 14 14)
      have b49865 := hb (x 14 4)
      have b49866 := hb (x 14 4 && x 14 14)
      clear * - r49864 b49865 b49866 d49859
      omega
    have d49867 : (x 13 13).toNat = 0 := by
      have r49868 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e49869 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
      have e49870 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
      have b49871 := hb (x 11 3)
      have b49872 := hb (x 12 2)
      have b49873 := hb (x 13 13)
      have b49874 := hb (x 14 12)
      clear * - r49868 e49869 e49870 b49871 b49872 b49873 b49874 d49851 d49846
      omega
    have d49875 : (x 13 5).toNat = 0 := by
      have r49876 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
      have b49877 := hb (x 13 5)
      have b49878 := hb (x 13 13)
      clear * - r49876 b49877 b49878 d49867
      omega
    have d49879 : (x 13 3 && x 13 14).toNat = 0 := by
      have r49880 := hand2 (x 13 3) (x 13 14)
      have b49881 := hb (x 13 14)
      have b49882 := hb (x 13 3 && x 13 14)
      clear * - r49880 b49881 b49882 d49838
      omega
    have d49883 : (x 16 11).toNat = 1 := by
      have r49884 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b49885 := hb (x 12 4)
      have b49886 := hb (x 16 11)
      have b49887 := hb (x 15 1 && x 15 12)
      have b49888 := hb (x 14 2 && x 14 13)
      have b49889 := hb (x 13 3 && x 13 14)
      clear * - r49884 b49885 b49886 b49887 b49888 b49889 d49781 d49793 d49879 d49677
      omega
    have d49890 : (x 16 3).toNat = 1 := by
      have r49891 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
      have b49892 := hb (x 16 3)
      have b49893 := hb (x 16 11)
      clear * - r49891 b49892 b49893 d49883
      omega
    have d49894 : (x 19 12).toNat = 0 := by
      have r49895 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e49896 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
      have e49897 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
      have b49898 := hb (x 16 3)
      have b49899 := hb (x 17 2)
      have b49900 := hb (x 18 13)
      have b49901 := hb (x 19 12)
      clear * - r49895 e49896 e49897 b49898 b49899 b49900 b49901 d49890
      omega
    have d49902 : (x 18 13).toNat = 0 := by
      have r49903 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e49904 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
      have e49905 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
      have b49906 := hb (x 16 3)
      have b49907 := hb (x 17 2)
      have b49908 := hb (x 18 13)
      have b49909 := hb (x 19 12)
      clear * - r49903 e49904 e49905 b49906 b49907 b49908 b49909 d49894 d49890
      omega
    have d49910 : (x 17 2).toNat = 0 := by
      have r49911 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e49912 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
      have e49913 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
      have b49914 := hb (x 16 3)
      have b49915 := hb (x 17 2)
      have b49916 := hb (x 18 13)
      have b49917 := hb (x 19 12)
      clear * - r49911 e49912 e49913 b49914 b49915 b49916 b49917 d49894 d49902 d49890
      omega
    have d49918 : (x 13 12).toNat = 0 := by
      have r49919 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e49920 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
      have e49921 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
      have b49922 := hb (x 10 3)
      have b49923 := hb (x 11 2)
      have b49924 := hb (x 12 13)
      have b49925 := hb (x 13 12)
      clear * - r49919 e49920 e49921 b49922 b49923 b49924 b49925 d49829 d49817
      omega
    have d49926 : (x 13 4).toNat = 0 := by
      have r49927 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
      have b49928 := hb (x 13 4)
      have b49929 := hb (x 13 12)
      clear * - r49927 b49928 b49929 d49918
      omega
    have d49930 : (x 10 3).toNat = 0 := by
      have r49931 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e49932 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
      have e49933 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
      have b49934 := hb (x 10 3)
      have b49935 := hb (x 11 2)
      have b49936 := hb (x 12 13)
      have b49937 := hb (x 13 12)
      clear * - r49931 e49932 e49933 b49934 b49935 b49936 b49937 d49918 d49829 d49817
      omega
    have d49938 : (x 10 3 && x 10 14).toNat = 0 := by
      have r49939 := hand1 (x 10 3) (x 10 14)
      have b49940 := hb (x 10 3)
      have b49941 := hb (x 10 3 && x 10 14)
      clear * - r49939 b49940 b49941 d49930
      omega
    have d49942 : (x 13 11).toNat = 1 := by
      have r49943 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b49944 := hb (x 9 4)
      have b49945 := hb (x 13 11)
      have b49946 := hb (x 12 1 && x 12 12)
      have b49947 := hb (x 11 2 && x 11 13)
      have b49948 := hb (x 10 3 && x 10 14)
      clear * - r49943 b49944 b49945 b49946 b49947 b49948 d49673 d49689 d49938 d49638
      omega
    have d49949 : (x 13 3).toNat = 1 := by
      have r49950 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
      have b49951 := hb (x 13 3)
      have b49952 := hb (x 13 11)
      clear * - r49950 b49951 b49952 d49942
      omega
    have d49953 : (x 16 12).toNat = 0 := by
      have r49954 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e49955 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
      have e49956 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
      have b49957 := hb (x 13 3)
      have b49958 := hb (x 14 2)
      have b49959 := hb (x 15 13)
      have b49960 := hb (x 16 12)
      clear * - r49954 e49955 e49956 b49957 b49958 b49959 b49960 d49949
      omega
    have d49961 : (x 16 1 && x 16 12).toNat = 0 := by
      have r49962 := hand2 (x 16 1) (x 16 12)
      have b49963 := hb (x 16 12)
      have b49964 := hb (x 16 1 && x 16 12)
      clear * - r49962 b49963 b49964 d49953
      omega
    have d49965 : (x 16 2 && x 16 12).toNat = 0 := by
      have r49966 := hand2 (x 16 2) (x 16 12)
      have b49967 := hb (x 16 12)
      have b49968 := hb (x 16 2 && x 16 12)
      clear * - r49966 b49967 b49968 d49953
      omega
    have d49969 : (x 15 13).toNat = 0 := by
      have r49970 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e49971 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
      have e49972 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
      have b49973 := hb (x 13 3)
      have b49974 := hb (x 14 2)
      have b49975 := hb (x 15 13)
      have b49976 := hb (x 16 12)
      clear * - r49970 e49971 e49972 b49973 b49974 b49975 b49976 d49953 d49949
      omega
    have d49977 : (x 15 2 && x 15 13).toNat = 0 := by
      have r49978 := hand2 (x 15 2) (x 15 13)
      have b49979 := hb (x 15 13)
      have b49980 := hb (x 15 2 && x 15 13)
      clear * - r49978 b49979 b49980 d49969
      omega
    have d49981 : (x 15 3 && x 15 13).toNat = 0 := by
      have r49982 := hand2 (x 15 3) (x 15 13)
      have b49983 := hb (x 15 13)
      have b49984 := hb (x 15 3 && x 15 13)
      clear * - r49982 b49983 b49984 d49969
      omega
    have d49985 : (x 14 1 && x 14 14).toNat = 1 := by
      have r49986 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b49987 := hb (x 13 2)
      have b49988 := hb (x 15 13)
      have b49989 := hb (x 14 1 && x 14 14)
      clear * - r49986 b49987 b49988 b49989 d49969 d49797
      omega
    have d49990 : (x 14 1).toNat = 1 := by
      have r49991 := hand1 (x 14 1) (x 14 14)
      have b49992 := hb (x 14 1)
      have b49993 := hb (x 14 1 && x 14 14)
      clear * - r49991 b49992 b49993 d49985
      omega
    have d49994 : (x 15 14).toNat = 0 := by
      have r49995 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b49996 := hb (x 14 1)
      have b49997 := hb (x 15 14)
      clear * - r49995 b49996 b49997 d49990
      omega
    have d49998 : (x 15 1 && x 15 14).toNat = 0 := by
      have r49999 := hand2 (x 15 1) (x 15 14)
      have b50000 := hb (x 15 14)
      have b50001 := hb (x 15 1 && x 15 14)
      clear * - r49999 b50000 b50001 d49994
      omega
    have d50002 : (x 15 2).toNat = 0 := by
      have r50003 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
      have b50004 := hb (x 15 2)
      have b50005 := hb (x 15 14)
      clear * - r50003 b50004 b50005 d49994
      omega
    have d50006 : (x 14 2).toNat = 0 := by
      have r50007 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e50008 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
      have e50009 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
      have b50010 := hb (x 13 3)
      have b50011 := hb (x 14 2)
      have b50012 := hb (x 15 13)
      have b50013 := hb (x 16 12)
      clear * - r50007 e50008 e50009 b50010 b50011 b50012 b50013 d49953 d49969 d49949
      omega
    have d50014 : (x 16 13).toNat = 1 := by
      have r50015 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b50016 := hb (x 14 2)
      have b50017 := hb (x 16 13)
      have b50018 := hb (x 15 1 && x 15 14)
      clear * - r50015 b50016 b50017 b50018 d49998 d50006
      omega
    have d50019 : (x 17 12).toNat = 0 := by
      have r50020 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e50021 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
      have e50022 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
      have b50023 := hb (x 14 3)
      have b50024 := hb (x 15 2)
      have b50025 := hb (x 16 13)
      have b50026 := hb (x 17 12)
      clear * - r50020 e50021 e50022 b50023 b50024 b50025 b50026 d50014 d50002
      omega
    have d50027 : (x 14 3).toNat = 0 := by
      have r50028 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e50029 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
      have e50030 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
      have b50031 := hb (x 14 3)
      have b50032 := hb (x 15 2)
      have b50033 := hb (x 16 13)
      have b50034 := hb (x 17 12)
      clear * - r50028 e50029 e50030 b50031 b50032 b50033 b50034 d50019 d50014 d50002
      omega
    have d50035 : (x 14 3 && x 14 14).toNat = 0 := by
      have r50036 := hand1 (x 14 3) (x 14 14)
      have b50037 := hb (x 14 3)
      have b50038 := hb (x 14 3 && x 14 14)
      clear * - r50036 b50037 b50038 d50027
      omega
    have d50039 : (x 17 11).toNat = 1 := by
      have r50040 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b50041 := hb (x 13 4)
      have b50042 := hb (x 17 11)
      have b50043 := hb (x 16 1 && x 16 12)
      have b50044 := hb (x 15 2 && x 15 13)
      have b50045 := hb (x 14 3 && x 14 14)
      clear * - r50040 b50041 b50042 b50043 b50044 b50045 d49961 d49977 d50035 d49926
      omega
    have d50046 : (x 17 3).toNat = 1 := by
      have r50047 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
      have b50048 := hb (x 17 3)
      have b50049 := hb (x 17 11)
      clear * - r50047 b50048 b50049 d50039
      omega
    have d50050 : (x 20 12).toNat = 0 := by
      have r50051 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e50052 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
      have e50053 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
      have b50054 := hb (x 17 3)
      have b50055 := hb (x 18 2)
      have b50056 := hb (x 19 13)
      have b50057 := hb (x 20 12)
      clear * - r50051 e50052 e50053 b50054 b50055 b50056 b50057 d50046
      omega
    have d50058 : (x 19 13).toNat = 0 := by
      have r50059 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e50060 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
      have e50061 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
      have b50062 := hb (x 17 3)
      have b50063 := hb (x 18 2)
      have b50064 := hb (x 19 13)
      have b50065 := hb (x 20 12)
      clear * - r50059 e50060 e50061 b50062 b50063 b50064 b50065 d50050 d50046
      omega
    have d50066 : (x 18 1 && x 18 14).toNat = 1 := by
      have r50067 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b50068 := hb (x 17 2)
      have b50069 := hb (x 19 13)
      have b50070 := hb (x 18 1 && x 18 14)
      clear * - r50067 b50068 b50069 b50070 d50058 d49910
      omega
    have d50071 : (x 18 14).toNat = 1 := by
      have r50072 := hand2 (x 18 1) (x 18 14)
      have b50073 := hb (x 18 14)
      have b50074 := hb (x 18 1 && x 18 14)
      clear * - r50072 b50073 b50074 d50066
      omega
    have d50075 : (x 17 1).toNat = 0 := by
      have r50076 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b50077 := hb (x 17 1)
      have b50078 := hb (x 18 14)
      clear * - r50076 b50077 b50078 d50071
      omega
    have d50079 : (x 17 1 && x 17 11).toNat = 0 := by
      have r50080 := hand1 (x 17 1) (x 17 11)
      have b50081 := hb (x 17 1)
      have b50082 := hb (x 17 1 && x 17 11)
      clear * - r50080 b50081 b50082 d50075
      omega
    have d50083 : (x 18 2).toNat = 0 := by
      have r50084 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e50085 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
      have e50086 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
      have b50087 := hb (x 17 3)
      have b50088 := hb (x 18 2)
      have b50089 := hb (x 19 13)
      have b50090 := hb (x 20 12)
      clear * - r50084 e50085 e50086 b50087 b50088 b50089 b50090 d50050 d50058 d50046
      omega
    have d50091 : (x 18 10).toNat = 0 := by
      have r50092 : (x 18 10).toNat ≤ (x 18 2).toNat := himp _ _ (hp10 18)
      have b50093 := hb (x 18 2)
      have b50094 := hb (x 18 10)
      clear * - r50092 b50093 b50094 d50083
      omega
    have r50095 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := by have q := hcov10 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b50096 := hb (x 13 5)
    have b50097 := hb (x 18 10)
    have b50098 := hb (x 17 1 && x 17 11)
    have b50099 := hb (x 16 2 && x 16 12)
    have b50100 := hb (x 15 3 && x 15 13)
    have b50101 := hb (x 14 4 && x 14 14)
    linarith only [r50095, b50096, b50097, b50098, b50099, b50100, b50101, d50091, d50079, d49965, d49981, d49863, d49875]

theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_a111110 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-12) 4).toNat = 0)
    (g1 : (x (-4) 7).toNat = 0)
    (g2 : (x (-3) 6).toNat = 0)
    (g3 : (x (-3) 7).toNat = 0)
    (g4 : (x (-3) 11).toNat = 0)
    (g5 : (x (-2) 5).toNat = 0)
    (g6 : (x (-2) 6).toNat = 0)
    (g7 : (x (-2) 10).toNat = 0)
    (g8 : (x (-1) 1).toNat = 0)
    (g9 : (x (-1) 4).toNat = 0)
    (g10 : (x (-1) 5).toNat = 0)
    (g11 : (x (-1) 9).toNat = 0)
    (g12 : (x (-1) 10).toNat = 0)
    (g13 : (x (-1) 11).toNat = 0)
    (g14 : (x (-1) 13).toNat = 0)
    (g15 : (x 0 3).toNat = 1)
    (g16 : (x 0 4).toNat = 1)
    (g17 : (x 0 7).toNat = 0)
    (g18 : (x 0 8).toNat = 1)
    (g19 : (x 0 11).toNat = 1)
    (g20 : (x 0 12).toNat = 1)
    (g21 : (x 0 13).toNat = 1)
    (g22 : (x 1 1).toNat = 0)
    (g23 : (x 1 2).toNat = 0)
    (g24 : (x 1 4).toNat = 0)
    (g25 : (x 1 5).toNat = 0)
    (g26 : (x 1 6).toNat = 0)
    (g27 : (x 1 8).toNat = 0)
    (g28 : (x 1 9).toNat = 0)
    (g29 : (x 1 10).toNat = 0)
    (g30 : (x 1 11).toNat = 0)
    (g31 : (x 1 12).toNat = 0)
    (g32 : (x 1 13).toNat = 0)
    (g33 : (x 2 5).toNat = 0)
    (g34 : (x 2 9).toNat = 0)
    (g35 : (x 2 10).toNat = 0)
    (g36 : (x 2 11).toNat = 0)
    (g37 : (x 3 4).toNat = 0)
    (g38 : (x 3 8).toNat = 0)
    (g39 : (x 3 9).toNat = 0)
    (g40 : (x 3 10).toNat = 0)
    (g41 : (x 4 8).toNat = 0)
    (g42 : (x 4 9).toNat = 0)
    (g43 : (x 5 8).toNat = 0)
    (g44 : (x (-2) 1 && x (-2) 2).toNat = 0)
    (g45 : (x (-3) 2 && x (-3) 3).toNat = 0)
    (g46 : (x (-4) 3 && x (-4) 4).toNat = 0)
    (g47 : (x (-5) 4 && x (-5) 5).toNat = 0)
    (g48 : (x (-6) 5 && x (-6) 6).toNat = 0)
    (g49 : (x (-7) 6 && x (-7) 7).toNat = 0)
    (g50 : (x (-9) 8 && x (-9) 9).toNat = 0)
    (g51 : (x (-10) 9 && x (-10) 10).toNat = 0)
    (g52 : (x (-11) 10 && x (-11) 11).toNat = 0)
    (g53 : (x 6 8 && x 6 10).toNat = 0)
    (g54 : (x 5 9 && x 5 11).toNat = 0)
    (g55 : (x 4 10 && x 4 12).toNat = 0)
    (g56 : (x 3 11 && x 3 13).toNat = 0)
    (g57 : (x 2 12 && x 2 14).toNat = 0)
    (g58 : (x 5 8 && x 5 11).toNat = 0)
    (g59 : (x 4 9 && x 4 12).toNat = 0)
    (g60 : (x 3 10 && x 3 13).toNat = 0)
    (g61 : (x 2 11 && x 2 14).toNat = 0)
    (g62 : (x 1 2 && x 1 6).toNat = 0)
    (g63 : (x 0 3 && x 0 7).toNat = 0)
    (g64 : (x (-1) 4 && x (-1) 8).toNat = 0)
    (g65 : (x (-2) 5 && x (-2) 9).toNat = 0)
    (g66 : (x (-3) 6 && x (-3) 10).toNat = 0)
    (g67 : (x (-4) 7 && x (-4) 11).toNat = 0)
    (g68 : (x 3 4 && x 3 8).toNat = 0)
    (g69 : (x 2 5 && x 2 9).toNat = 0)
    (g70 : (x 1 6 && x 1 10).toNat = 0)
    (g71 : (x 0 7 && x 0 11).toNat = 0)
    (g72 : (x (-2) 1 && x (-2) 6).toNat = 0)
    (g73 : (x (-3) 2 && x (-3) 7).toNat = 0)
    (g74 : (x 4 3 && x 4 8).toNat = 0)
    (g75 : (x 3 4 && x 3 9).toNat = 0)
    (g76 : (x 2 5 && x 2 10).toNat = 0)
    (g77 : (x 1 6 && x 1 11).toNat = 0)
    (g78 : (x 0 7 && x 0 12).toNat = 0)
    (g79 : (x (-1) 8 && x (-1) 13).toNat = 0)
    (g80 : (x 3 8 && x 3 13).toNat = 0)
    (g81 : (x 2 9 && x 2 14).toNat = 0)
    (g82 : (x 5 2 && x 5 8).toNat = 0)
    (g83 : (x 4 3 && x 4 9).toNat = 0)
    (g84 : (x 3 4 && x 3 10).toNat = 0)
    (g85 : (x 2 5 && x 2 11).toNat = 0)
    (g86 : (x 1 6 && x 1 12).toNat = 0)
    (g87 : (x 0 7 && x 0 13).toNat = 0)
    (g88 : (x 2 8 && x 2 14).toNat = 0)
    (g89 : (x 6 1 && x 6 8).toNat = 0)
    (g90 : (x 5 2 && x 5 9).toNat = 0)
    (g91 : (x 4 3 && x 4 10).toNat = 0)
    (g92 : (x 3 4 && x 3 11).toNat = 0)
    (g93 : (x 2 5 && x 2 12).toNat = 0)
    (g94 : (x 1 6 && x 1 13).toNat = 0)
    (g95 : (x 0 7 && x 0 14).toNat = 0)
    (g96 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g97 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g98 : (x 3 4 && x 3 13).toNat = 0)
    (g99 : (x 2 5 && x 2 14).toNat = 0)
    (g100 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g101 : (x 2 4 && x 2 14).toNat = 0)
    (g102 : (x 3 4 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_a111110_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83 g84 g85 g86 g87 g88 g89 g90 g91 g92 g93 g94 g95 g96 g97 g98 g99 g100 g101 g102
