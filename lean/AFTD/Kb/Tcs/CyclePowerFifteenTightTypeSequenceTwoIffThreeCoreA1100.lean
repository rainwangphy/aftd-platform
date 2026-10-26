import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a1100

Topic: combinatorics   Node: a6fef55bf03d

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP; the same generator on the same window refutes x(0,2) != x(0,3) (a case-split tree of 109 + 3 nodes).

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_two_iff_three_core: under the layer-free tight-cover constraints for k = 15 and 87 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a1100_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-7) 11).toNat = 0)
    (g1 : (x (-6) 6).toNat = 0)
    (g2 : (x (-6) 10).toNat = 0)
    (g3 : (x (-5) 13).toNat = 0)
    (g4 : (x (-2) 3).toNat = 0)
    (g5 : (x (-2) 11).toNat = 0)
    (g6 : (x (-1) 2).toNat = 0)
    (g7 : (x (-1) 3).toNat = 0)
    (g8 : (x (-1) 5).toNat = 0)
    (g9 : (x (-1) 9).toNat = 0)
    (g10 : (x (-1) 10).toNat = 0)
    (g11 : (x (-1) 11).toNat = 0)
    (g12 : (x (-1) 13).toNat = 0)
    (g13 : (x 0 1).toNat = 1)
    (g14 : (x 0 2).toNat = 1)
    (g15 : (x 0 3).toNat = 0)
    (g16 : (x 0 4).toNat = 0)
    (g17 : (x 0 5).toNat = 0)
    (g18 : (x 0 8).toNat = 0)
    (g19 : (x 0 11).toNat = 0)
    (g20 : (x 0 12).toNat = 1)
    (g21 : (x 0 13).toNat = 1)
    (g22 : (x 0 14).toNat = 1)
    (g23 : (x 1 2).toNat = 0)
    (g24 : (x 1 4).toNat = 0)
    (g25 : (x 1 5).toNat = 0)
    (g26 : (x 1 6).toNat = 0)
    (g27 : (x 1 10).toNat = 0)
    (g28 : (x 1 12).toNat = 0)
    (g29 : (x 1 13).toNat = 0)
    (g30 : (x 1 14).toNat = 0)
    (g31 : (x 2 4).toNat = 0)
    (g32 : (x 2 12).toNat = 0)
    (g33 : (x 1 10 && x 1 11).toNat = 0)
    (g34 : (x 0 11 && x 0 12).toNat = 0)
    (g35 : (x (-1) 12 && x (-1) 13).toNat = 0)
    (g36 : (x 0 1 && x 0 3).toNat = 0)
    (g37 : (x (-1) 2 && x (-1) 4).toNat = 0)
    (g38 : (x (-2) 3 && x (-2) 5).toNat = 0)
    (g39 : (x 2 9 && x 2 12).toNat = 0)
    (g40 : (x 1 10 && x 1 13).toNat = 0)
    (g41 : (x 0 11 && x 0 14).toNat = 0)
    (g42 : (x 0 4 && x 0 8).toNat = 0)
    (g43 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g44 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g45 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g46 : (x (-5) 9 && x (-5) 13).toNat = 0)
    (g47 : (x (-6) 5 && x (-6) 10).toNat = 0)
    (g48 : (x (-7) 6 && x (-7) 11).toNat = 0)
    (g49 : (x 1 1 && x 1 6).toNat = 0)
    (g50 : (x (-1) 3 && x (-1) 8).toNat = 0)
    (g51 : (x 1 6 && x 1 11).toNat = 0)
    (g52 : (x (-1) 8 && x (-1) 13).toNat = 0)
    (g53 : (x 1 9 && x 1 14).toNat = 0)
    (g54 : (x 1 7 && x 1 14).toNat = 0)
    (g55 : (x (-6) 1 && x (-6) 10).toNat = 0)
    (g56 : (x (-7) 2 && x (-7) 11).toNat = 0)
    (g57 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g58 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g59 : (x (-5) 4 && x (-5) 13).toNat = 0)
    (g60 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g61 : (x (-2) 2 && x (-2) 11).toNat = 0)
    (g62 : (x (-3) 3 && x (-3) 12).toNat = 0)
    (g63 : (x (-5) 5 && x (-5) 14).toNat = 0)
    (g64 : (x 1 1 && x 1 10).toNat = 0)
    (g65 : (x 0 2 && x 0 11).toNat = 0)
    (g66 : (x (-1) 3 && x (-1) 12).toNat = 0)
    (g67 : (x 1 2 && x 1 11).toNat = 0)
    (g68 : (x 0 3 && x 0 12).toNat = 0)
    (g69 : (x (-1) 4 && x (-1) 13).toNat = 0)
    (g70 : (x 2 4 && x 2 13).toNat = 0)
    (g71 : (x 1 5 && x 1 14).toNat = 0)
    (g72 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g73 : (x 0 1 && x 0 11).toNat = 0)
    (g74 : (x (-1) 2 && x (-1) 12).toNat = 0)
    (g75 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g76 : (x 1 2 && x 1 12).toNat = 0)
    (g77 : (x 0 3 && x 0 13).toNat = 0)
    (g78 : (x 2 2 && x 2 12).toNat = 0)
    (g79 : (x 1 3 && x 1 13).toNat = 0)
    (g80 : (x 0 4 && x 0 14).toNat = 0)
    (g81 : (x 1 4 && x 1 14).toNat = 0)
    (g82 : (x (-6) 2 && x (-6) 13).toNat = 0)
    (g83 : (x (-7) 3 && x (-7) 14).toNat = 0)
    (g84 : (x 2 1 && x 2 12).toNat = 0)
    (g85 : (x 1 2 && x 1 13).toNat = 0)
    (g86 : (x 0 3 && x 0 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  cases h17560 : x 0 6
  · have f17561 : (x 0 6).toNat = 0 := by rw [h17560]; rfl
    cases h17562 : x 0 7
    · have f17563 : (x 0 7).toNat = 0 := by rw [h17562]; rfl
      have d17564 : (x 0 7 && x 0 12).toNat = 0 := by
        have r17565 := hand1 (x 0 7) (x 0 12)
        have b17566 := hb (x 0 7)
        have b17567 := hb (x 0 7 && x 0 12)
        clear * - r17565 b17566 b17567 f17563
        omega
      have d17568 : (x 0 2 && x 0 7).toNat = 0 := by
        have r17569 := hand2 (x 0 2) (x 0 7)
        have b17570 := hb (x 0 7)
        have b17571 := hb (x 0 2 && x 0 7)
        clear * - r17569 b17570 b17571 f17563
        omega
      cases h17572 : x 0 9
      · have f17573 : (x 0 9).toNat = 0 := by rw [h17572]; rfl
        have d17574 : (x (-4) 4 && x (-4) 13).toNat = 1 := by
          have r17575 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b17576 := hb (x (-6) 6)
          have b17577 := hb (x 0 9)
          have b17578 := hb (x (-1) 1 && x (-1) 10)
          have b17579 := hb (x (-2) 2 && x (-2) 11)
          have b17580 := hb (x (-3) 3 && x (-3) 12)
          have b17581 := hb (x (-4) 4 && x (-4) 13)
          have b17582 := hb (x (-5) 5 && x (-5) 14)
          clear * - r17575 b17576 b17577 b17578 b17579 b17580 b17581 b17582 f17573 g60 g61 g62 g63 g1
          omega
        have d17583 : (x (-4) 13).toNat = 1 := by
          have r17584 := hand2 (x (-4) 4) (x (-4) 13)
          have b17585 := hb (x (-4) 13)
          have b17586 := hb (x (-4) 4 && x (-4) 13)
          clear * - r17584 b17585 b17586 d17574
          omega
        have d17587 : (x (-4) 1).toNat = 1 := by
          have r17588 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
          have b17589 := hb (x (-4) 1)
          have b17590 := hb (x (-4) 13)
          clear * - r17588 b17589 b17590 d17583
          omega
        have d17591 : (x (-3) 14).toNat = 0 := by
          have r17592 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b17593 := hb (x (-4) 1)
          have b17594 := hb (x (-3) 14)
          clear * - r17592 b17593 b17594 d17587
          omega
        have d17595 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
          have r17596 := hand2 (x (-3) 1) (x (-3) 14)
          have b17597 := hb (x (-3) 14)
          have b17598 := hb (x (-3) 1 && x (-3) 14)
          clear * - r17596 b17597 b17598 d17591
          omega
        have d17599 : (x (-3) 4 && x (-3) 14).toNat = 0 := by
          have r17600 := hand2 (x (-3) 4) (x (-3) 14)
          have b17601 := hb (x (-3) 14)
          have b17602 := hb (x (-3) 4 && x (-3) 14)
          clear * - r17600 b17601 b17602 d17591
          omega
        have d17603 : (x (-4) 5).toNat = 1 := by
          have r17604 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b17605 := hb (x (-4) 5)
          have b17606 := hb (x 1 10)
          have b17607 := hb (x 0 1 && x 0 11)
          have b17608 := hb (x (-1) 2 && x (-1) 12)
          have b17609 := hb (x (-2) 3 && x (-2) 13)
          have b17610 := hb (x (-3) 4 && x (-3) 14)
          clear * - r17604 b17605 b17606 b17607 b17608 b17609 b17610 g27 g73 g74 g75 d17599
          omega
        have d17611 : (x (-3) 5 && x (-3) 14).toNat = 0 := by
          have r17612 := hand2 (x (-3) 5) (x (-3) 14)
          have b17613 := hb (x (-3) 14)
          have b17614 := hb (x (-3) 5 && x (-3) 14)
          clear * - r17612 b17613 b17614 d17591
          omega
        have d17615 : (x (-3) 6).toNat = 0 := by
          have r17616 : (x (-3) 6).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp6 (-3))
          have b17617 := hb (x (-3) 6)
          have b17618 := hb (x (-3) 14)
          clear * - r17616 b17617 b17618 d17591
          omega
        have d17619 : (x (-3) 4 && x (-3) 6).toNat = 0 := by
          have r17620 := hand2 (x (-3) 4) (x (-3) 6)
          have b17621 := hb (x (-3) 6)
          have b17622 := hb (x (-3) 4 && x (-3) 6)
          clear * - r17620 b17621 b17622 d17615
          omega
        have d17623 : (x (-3) 2).toNat = 0 := by
          have r17624 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
          have b17625 := hb (x (-3) 2)
          have b17626 := hb (x (-3) 14)
          clear * - r17624 b17625 b17626 d17591
          omega
        have d17627 : (x (-3) 2 && x (-3) 13).toNat = 0 := by
          have r17628 := hand1 (x (-3) 2) (x (-3) 13)
          have b17629 := hb (x (-3) 2)
          have b17630 := hb (x (-3) 2 && x (-3) 13)
          clear * - r17628 b17629 b17630 d17623
          omega
        have d17631 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
          have r17632 := hand1 (x (-3) 2) (x (-3) 12)
          have b17633 := hb (x (-3) 2)
          have b17634 := hb (x (-3) 2 && x (-3) 12)
          clear * - r17632 b17633 b17634 d17623
          omega
        have d17635 : (x (-3) 2 && x (-3) 9).toNat = 0 := by
          have r17636 := hand1 (x (-3) 2) (x (-3) 9)
          have b17637 := hb (x (-3) 2)
          have b17638 := hb (x (-3) 2 && x (-3) 9)
          clear * - r17636 b17637 b17638 d17623
          omega
        have d17639 : (x (-3) 2 && x (-3) 7).toNat = 0 := by
          have r17640 := hand1 (x (-3) 2) (x (-3) 7)
          have b17641 := hb (x (-3) 2)
          have b17642 := hb (x (-3) 2 && x (-3) 7)
          clear * - r17640 b17641 b17642 d17623
          omega
        have d17643 : (x (-3) 10).toNat = 0 := by
          have r17644 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
          have b17645 := hb (x (-3) 2)
          have b17646 := hb (x (-3) 10)
          clear * - r17644 b17645 b17646 d17623
          omega
        have d17647 : (x (-3) 1 && x (-3) 10).toNat = 0 := by
          have r17648 := hand2 (x (-3) 1) (x (-3) 10)
          have b17649 := hb (x (-3) 10)
          have b17650 := hb (x (-3) 1 && x (-3) 10)
          clear * - r17648 b17649 b17650 d17643
          omega
        have d17651 : (x (-3) 5 && x (-3) 10).toNat = 0 := by
          have r17652 := hand2 (x (-3) 5) (x (-3) 10)
          have b17653 := hb (x (-3) 10)
          have b17654 := hb (x (-3) 5 && x (-3) 10)
          clear * - r17652 b17653 b17654 d17643
          omega
        have d17655 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
          have r17656 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b17657 := hb (x (-3) 2)
          have b17658 := hb (x (-1) 13)
          have b17659 := hb (x (-2) 1 && x (-2) 14)
          clear * - r17656 b17657 b17658 b17659 g12 d17623
          omega
        have d17660 : (x (-2) 14).toNat = 1 := by
          have r17661 := hand2 (x (-2) 1) (x (-2) 14)
          have b17662 := hb (x (-2) 14)
          have b17663 := hb (x (-2) 1 && x (-2) 14)
          clear * - r17661 b17662 b17663 d17655
          omega
        have d17664 : (x (-3) 1).toNat = 0 := by
          have r17665 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b17666 := hb (x (-3) 1)
          have b17667 := hb (x (-2) 14)
          clear * - r17665 b17666 b17667 d17660
          omega
        have d17668 : (x (-3) 13).toNat = 0 := by
          have r17669 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
          have b17670 := hb (x (-3) 1)
          have b17671 := hb (x (-3) 13)
          clear * - r17669 b17670 b17671 d17664
          omega
        have d17672 : (x (-3) 5).toNat = 0 := by
          have r17673 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
          have b17674 := hb (x (-3) 5)
          have b17675 := hb (x (-3) 13)
          clear * - r17673 b17674 b17675 d17668
          omega
        have d17676 : (x (-3) 9).toNat = 0 := by
          have r17677 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
          have b17678 := hb (x (-3) 1)
          have b17679 := hb (x (-3) 9)
          clear * - r17677 b17678 b17679 d17664
          omega
        have d17680 : (x (-2) 1).toNat = 1 := by
          have r17681 := hand1 (x (-2) 1) (x (-2) 14)
          have b17682 := hb (x (-2) 1)
          have b17683 := hb (x (-2) 1 && x (-2) 14)
          clear * - r17681 b17682 b17683 d17655
          omega
        have d17684 : (x (-1) 14).toNat = 0 := by
          have r17685 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b17686 := hb (x (-2) 1)
          have b17687 := hb (x (-1) 14)
          clear * - r17685 b17686 b17687 d17680
          omega
        have d17688 : (x (-1) 4 && x (-1) 14).toNat = 0 := by
          have r17689 := hand2 (x (-1) 4) (x (-1) 14)
          have b17690 := hb (x (-1) 14)
          have b17691 := hb (x (-1) 4 && x (-1) 14)
          clear * - r17689 b17690 b17691 d17684
          omega
        have d17692 : (x (-1) 6).toNat = 0 := by
          have r17693 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
          have b17694 := hb (x (-1) 6)
          have b17695 := hb (x (-1) 14)
          clear * - r17693 b17694 b17695 d17684
          omega
        have d17696 : (x (-3) 12).toNat = 0 := by
          have r17697 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e17698 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
          have e17699 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
          have b17700 := hb (x (-6) 3)
          have b17701 := hb (x (-5) 2)
          have b17702 := hb (x (-4) 13)
          have b17703 := hb (x (-3) 12)
          clear * - r17697 e17698 e17699 b17700 b17701 b17702 b17703 d17583
          omega
        have d17704 : (x (-3) 4).toNat = 0 := by
          have r17705 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
          have b17706 := hb (x (-3) 4)
          have b17707 := hb (x (-3) 12)
          clear * - r17705 b17706 b17707 d17696
          omega
        have d17708 : (x (-5) 2).toNat = 0 := by
          have r17709 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e17710 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
          have e17711 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
          have b17712 := hb (x (-6) 3)
          have b17713 := hb (x (-5) 2)
          have b17714 := hb (x (-4) 13)
          have b17715 := hb (x (-3) 12)
          clear * - r17709 e17710 e17711 b17712 b17713 b17714 b17715 d17696 d17583
          omega
        have d17716 : (x (-4) 1 && x (-4) 14).toNat = 1 := by
          have r17717 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b17718 := hb (x (-5) 2)
          have b17719 := hb (x (-3) 13)
          have b17720 := hb (x (-4) 1 && x (-4) 14)
          clear * - r17717 b17718 b17719 b17720 d17668 d17708
          omega
        have d17721 : (x (-4) 14).toNat = 1 := by
          have r17722 := hand2 (x (-4) 1) (x (-4) 14)
          have b17723 := hb (x (-4) 14)
          have b17724 := hb (x (-4) 1 && x (-4) 14)
          clear * - r17722 b17723 b17724 d17716
          omega
        have d17725 : (x (-5) 1).toNat = 0 := by
          have r17726 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b17727 := hb (x (-5) 1)
          have b17728 := hb (x (-4) 14)
          clear * - r17726 b17727 b17728 d17721
          omega
        have d17729 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
          have r17730 := hand1 (x (-5) 1) (x (-5) 12)
          have b17731 := hb (x (-5) 1)
          have b17732 := hb (x (-5) 1 && x (-5) 12)
          clear * - r17730 b17731 b17732 d17725
          omega
        have d17733 : (x (-5) 9).toNat = 0 := by
          have r17734 : (x (-5) 9).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp9 (-5))
          have b17735 := hb (x (-5) 1)
          have b17736 := hb (x (-5) 9)
          clear * - r17734 b17735 b17736 d17725
          omega
        have d17737 : (x (-5) 4 && x (-5) 9).toNat = 0 := by
          have r17738 := hand2 (x (-5) 4) (x (-5) 9)
          have b17739 := hb (x (-5) 9)
          have b17740 := hb (x (-5) 4 && x (-5) 9)
          clear * - r17738 b17739 b17740 d17733
          omega
        have d17741 : (x 1 8).toNat = 0 := by
          have r17742 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e17743 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e17744 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e17745 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e17746 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e17747 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e17748 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b17749 := hb (x (-6) 7)
          have b17750 := hb (x (-5) 6)
          have b17751 := hb (x (-4) 5)
          have b17752 := hb (x (-3) 4)
          have b17753 := hb (x (-2) 11)
          have b17754 := hb (x (-1) 10)
          have b17755 := hb (x 0 9)
          have b17756 := hb (x 1 8)
          clear * - r17742 e17743 e17744 e17745 e17746 e17747 e17748 b17749 b17750 b17751 b17752 b17753 b17754 b17755 b17756 f17573 g10 g5 d17704 d17603
          omega
        have d17757 : (x (-5) 6).toNat = 0 := by
          have r17758 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e17759 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e17760 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e17761 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e17762 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e17763 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e17764 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b17765 := hb (x (-6) 7)
          have b17766 := hb (x (-5) 6)
          have b17767 := hb (x (-4) 5)
          have b17768 := hb (x (-3) 4)
          have b17769 := hb (x (-2) 11)
          have b17770 := hb (x (-1) 10)
          have b17771 := hb (x 0 9)
          have b17772 := hb (x 1 8)
          clear * - r17758 e17759 e17760 e17761 e17762 e17763 e17764 b17765 b17766 b17767 b17768 b17769 b17770 b17771 b17772 d17741 f17573 g10 g5 d17704 d17603
          omega
        have d17773 : (x (-5) 6 && x (-5) 8).toNat = 0 := by
          have r17774 := hand1 (x (-5) 6) (x (-5) 8)
          have b17775 := hb (x (-5) 6)
          have b17776 := hb (x (-5) 6 && x (-5) 8)
          clear * - r17774 b17775 b17776 d17757
          omega
        have d17777 : (x (-6) 7).toNat = 0 := by
          have r17778 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e17779 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e17780 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e17781 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e17782 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e17783 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e17784 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b17785 := hb (x (-6) 7)
          have b17786 := hb (x (-5) 6)
          have b17787 := hb (x (-4) 5)
          have b17788 := hb (x (-3) 4)
          have b17789 := hb (x (-2) 11)
          have b17790 := hb (x (-1) 10)
          have b17791 := hb (x 0 9)
          have b17792 := hb (x 1 8)
          clear * - r17778 e17779 e17780 e17781 e17782 e17783 e17784 b17785 b17786 b17787 b17788 b17789 b17790 b17791 b17792 d17741 f17573 g10 g5 d17704 d17603 d17757
          omega
        have d17793 : (x (-6) 7 && x (-6) 9).toNat = 0 := by
          have r17794 := hand1 (x (-6) 7) (x (-6) 9)
          have b17795 := hb (x (-6) 7)
          have b17796 := hb (x (-6) 7 && x (-6) 9)
          clear * - r17794 b17795 b17796 d17777
          omega
        cases h17797 : x 0 10
        · have f17798 : (x 0 10).toNat = 0 := by rw [h17797]; rfl
          cases h17799 : x 1 1
          · have f17800 : (x 1 1).toNat = 0 := by rw [h17799]; rfl
            have d17801 : (x 2 14).toNat = 1 := by
              have r17802 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b17803 := hb (x 1 1)
              have b17804 := hb (x 2 14)
              clear * - r17802 b17803 b17804 f17800
              omega
            cases h17805 : x 1 3
            · have f17806 : (x 1 3).toNat = 0 := by rw [h17805]; rfl
              have d17807 : (x 1 3 && x 1 7).toNat = 0 := by
                have r17808 := hand1 (x 1 3) (x 1 7)
                have b17809 := hb (x 1 3)
                have b17810 := hb (x 1 3 && x 1 7)
                clear * - r17808 b17809 b17810 f17806
                omega
              have d17811 : (x 1 11).toNat = 0 := by
                have r17812 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
                have b17813 := hb (x 1 3)
                have b17814 := hb (x 1 11)
                clear * - r17812 b17813 b17814 f17806
                omega
              cases h17815 : x (-1) 4
              · have f17816 : (x (-1) 4).toNat = 0 := by rw [h17815]; rfl
                have d17817 : (x 3 11).toNat = 1 := by
                  have r17818 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b17819 := hb (x (-1) 4)
                  have b17820 := hb (x 3 11)
                  have b17821 := hb (x 2 1 && x 2 12)
                  have b17822 := hb (x 1 2 && x 1 13)
                  have b17823 := hb (x 0 3 && x 0 14)
                  clear * - r17818 b17819 b17820 b17821 b17822 b17823 g84 g85 g86 f17816
                  omega
                have d17824 : (x 3 3).toNat = 1 := by
                  have r17825 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
                  have b17826 := hb (x 3 3)
                  have b17827 := hb (x 3 11)
                  clear * - r17825 b17826 b17827 d17817
                  omega
                have d17828 : (x 6 12).toNat = 0 := by
                  have r17829 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e17830 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                  have e17831 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                  have b17832 := hb (x 3 3)
                  have b17833 := hb (x 4 2)
                  have b17834 := hb (x 5 13)
                  have b17835 := hb (x 6 12)
                  clear * - r17829 e17830 e17831 b17832 b17833 b17834 b17835 d17824
                  omega
                have d17836 : (x 6 4).toNat = 0 := by
                  have r17837 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
                  have b17838 := hb (x 6 4)
                  have b17839 := hb (x 6 12)
                  clear * - r17837 b17838 b17839 d17828
                  omega
                have d17840 : (x 6 4 && x 6 14).toNat = 0 := by
                  have r17841 := hand1 (x 6 4) (x 6 14)
                  have b17842 := hb (x 6 4)
                  have b17843 := hb (x 6 4 && x 6 14)
                  clear * - r17841 b17842 b17843 d17836
                  omega
                have d17844 : (x 5 13).toNat = 0 := by
                  have r17845 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e17846 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                  have e17847 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                  have b17848 := hb (x 3 3)
                  have b17849 := hb (x 4 2)
                  have b17850 := hb (x 5 13)
                  have b17851 := hb (x 6 12)
                  clear * - r17845 e17846 e17847 b17848 b17849 b17850 b17851 d17828 d17824
                  omega
                have d17852 : (x 5 5).toNat = 0 := by
                  have r17853 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
                  have b17854 := hb (x 5 5)
                  have b17855 := hb (x 5 13)
                  clear * - r17853 b17854 b17855 d17844
                  omega
                have d17856 : (x 4 2).toNat = 0 := by
                  have r17857 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e17858 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                  have e17859 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                  have b17860 := hb (x 3 3)
                  have b17861 := hb (x 4 2)
                  have b17862 := hb (x 5 13)
                  have b17863 := hb (x 6 12)
                  clear * - r17857 e17858 e17859 b17860 b17861 b17862 b17863 d17828 d17844 d17824
                  omega
                have d17864 : (x 4 10).toNat = 0 := by
                  have r17865 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
                  have b17866 := hb (x 4 2)
                  have b17867 := hb (x 4 10)
                  clear * - r17865 b17866 b17867 d17856
                  omega
                have d17868 : (x 4 7 && x 4 10).toNat = 0 := by
                  have r17869 := hand2 (x 4 7) (x 4 10)
                  have b17870 := hb (x 4 10)
                  have b17871 := hb (x 4 7 && x 4 10)
                  clear * - r17869 b17870 b17871 d17864
                  omega
                have d17872 : (x 3 1 && x 3 11).toNat = 1 := by
                  have r17873 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b17874 := hb (x (-1) 5)
                  have b17875 := hb (x 4 10)
                  have b17876 := hb (x 3 1 && x 3 11)
                  have b17877 := hb (x 2 2 && x 2 12)
                  have b17878 := hb (x 1 3 && x 1 13)
                  have b17879 := hb (x 0 4 && x 0 14)
                  clear * - r17873 b17874 b17875 b17876 b17877 b17878 b17879 d17864 g78 g79 g80 g8
                  omega
                have d17880 : (x 3 1).toNat = 1 := by
                  have r17881 := hand1 (x 3 1) (x 3 11)
                  have b17882 := hb (x 3 1)
                  have b17883 := hb (x 3 1 && x 3 11)
                  clear * - r17881 b17882 b17883 d17872
                  omega
                have d17884 : (x 4 14).toNat = 0 := by
                  have r17885 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b17886 := hb (x 3 1)
                  have b17887 := hb (x 4 14)
                  clear * - r17885 b17886 b17887 d17880
                  omega
                have d17888 : (x 4 1 && x 4 14).toNat = 0 := by
                  have r17889 := hand2 (x 4 1) (x 4 14)
                  have b17890 := hb (x 4 14)
                  have b17891 := hb (x 4 1 && x 4 14)
                  clear * - r17889 b17890 b17891 d17884
                  omega
                have d17892 : (x 3 2).toNat = 1 := by
                  have r17893 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b17894 := hb (x 3 2)
                  have b17895 := hb (x 5 13)
                  have b17896 := hb (x 4 1 && x 4 14)
                  clear * - r17893 b17894 b17895 b17896 d17844 d17888
                  omega
                have d17897 : (x 3 14).toNat = 1 := by
                  have r17898 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
                  have b17899 := hb (x 3 2)
                  have b17900 := hb (x 3 14)
                  clear * - r17898 b17899 b17900 d17892
                  omega
                have d17901 : (x 2 1).toNat = 0 := by
                  have r17902 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b17903 := hb (x 2 1)
                  have b17904 := hb (x 3 14)
                  clear * - r17902 b17903 b17904 d17897
                  omega
                have d17905 : (x 2 1 && x 2 14).toNat = 0 := by
                  have r17906 := hand1 (x 2 1) (x 2 14)
                  have b17907 := hb (x 2 1)
                  have b17908 := hb (x 2 1 && x 2 14)
                  clear * - r17906 b17907 b17908 d17901
                  omega
                have d17909 : (x 3 13).toNat = 1 := by
                  have r17910 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b17911 := hb (x 1 2)
                  have b17912 := hb (x 3 13)
                  have b17913 := hb (x 2 1 && x 2 14)
                  clear * - r17910 b17911 b17912 b17913 d17905 g23
                  omega
                have d17914 : (x 4 12).toNat = 0 := by
                  have r17915 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e17916 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                  have e17917 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                  have b17918 := hb (x 1 3)
                  have b17919 := hb (x 2 2)
                  have b17920 := hb (x 3 13)
                  have b17921 := hb (x 4 12)
                  clear * - r17915 e17916 e17917 b17918 b17919 b17920 b17921 d17909 f17806
                  omega
                have d17922 : (x 4 3 && x 4 12).toNat = 0 := by
                  have r17923 := hand2 (x 4 3) (x 4 12)
                  have b17924 := hb (x 4 12)
                  have b17925 := hb (x 4 3 && x 4 12)
                  clear * - r17923 b17924 b17925 d17914
                  omega
                have d17926 : (x 4 4).toNat = 0 := by
                  have r17927 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
                  have b17928 := hb (x 4 4)
                  have b17929 := hb (x 4 12)
                  clear * - r17927 b17928 b17929 d17914
                  omega
                have d17930 : (x 4 4 && x 4 13).toNat = 0 := by
                  have r17931 := hand1 (x 4 4) (x 4 13)
                  have b17932 := hb (x 4 4)
                  have b17933 := hb (x 4 4 && x 4 13)
                  clear * - r17931 b17932 b17933 d17926
                  omega
                have d17934 : (x 4 4 && x 4 11).toNat = 0 := by
                  have r17935 := hand1 (x 4 4) (x 4 11)
                  have b17936 := hb (x 4 4)
                  have b17937 := hb (x 4 4 && x 4 11)
                  clear * - r17935 b17936 b17937 d17926
                  omega
                have d17938 : (x 2 2).toNat = 0 := by
                  have r17939 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e17940 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                  have e17941 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                  have b17942 := hb (x 1 3)
                  have b17943 := hb (x 2 2)
                  have b17944 := hb (x 3 13)
                  have b17945 := hb (x 4 12)
                  clear * - r17939 e17940 e17941 b17942 b17943 b17944 b17945 d17914 d17909 f17806
                  omega
                have d17946 : (x 2 2 && x 2 6).toNat = 0 := by
                  have r17947 := hand1 (x 2 2) (x 2 6)
                  have b17948 := hb (x 2 2)
                  have b17949 := hb (x 2 2 && x 2 6)
                  clear * - r17947 b17948 b17949 d17938
                  omega
                have d17950 : (x 2 10).toNat = 0 := by
                  have r17951 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
                  have b17952 := hb (x 2 2)
                  have b17953 := hb (x 2 10)
                  clear * - r17951 b17952 b17953 d17938
                  omega
                have d17954 : (x 2 1 && x 2 10).toNat = 0 := by
                  have r17955 := hand2 (x 2 1) (x 2 10)
                  have b17956 := hb (x 2 10)
                  have b17957 := hb (x 2 1 && x 2 10)
                  clear * - r17955 b17956 b17957 d17950
                  omega
                have d17958 : (x 2 5 && x 2 10).toNat = 0 := by
                  have r17959 := hand2 (x 2 5) (x 2 10)
                  have b17960 := hb (x 2 10)
                  have b17961 := hb (x 2 5 && x 2 10)
                  clear * - r17959 b17960 b17961 d17950
                  omega
                have d17962 : (x 2 1 && x 2 11).toNat = 0 := by
                  have r17963 := hand1 (x 2 1) (x 2 11)
                  have b17964 := hb (x 2 1)
                  have b17965 := hb (x 2 1 && x 2 11)
                  clear * - r17963 b17964 b17965 d17901
                  omega
                have d17966 : (x 2 13).toNat = 0 := by
                  have r17967 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
                  have b17968 := hb (x 2 1)
                  have b17969 := hb (x 2 13)
                  clear * - r17967 b17968 b17969 d17901
                  omega
                have d17970 : (x 2 6 && x 2 13).toNat = 0 := by
                  have r17971 := hand2 (x 2 6) (x 2 13)
                  have b17972 := hb (x 2 13)
                  have b17973 := hb (x 2 6 && x 2 13)
                  clear * - r17971 b17972 b17973 d17966
                  omega
                have d17974 : (x 2 5).toNat = 0 := by
                  have r17975 : (x 2 5).toNat ≤ (x 2 13).toNat := himp _ _ (hp5 2)
                  have b17976 := hb (x 2 5)
                  have b17977 := hb (x 2 13)
                  clear * - r17975 b17976 b17977 d17966
                  omega
                have d17978 : (x 2 5 && x 2 14).toNat = 0 := by
                  have r17979 := hand1 (x 2 5) (x 2 14)
                  have b17980 := hb (x 2 5)
                  have b17981 := hb (x 2 5 && x 2 14)
                  clear * - r17979 b17980 b17981 d17974
                  omega
                have d17982 : (x 3 12).toNat = 1 := by
                  have r17983 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e17984 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
                  have e17985 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
                  have b17986 := hb (x 0 3)
                  have b17987 := hb (x 1 2)
                  have b17988 := hb (x 2 13)
                  have b17989 := hb (x 3 12)
                  clear * - r17983 e17984 e17985 b17986 b17987 b17988 b17989 d17966 g23 g15
                  omega
                have d17990 : (x 2 9).toNat = 0 := by
                  have r17991 : (x 2 9).toNat ≤ (x 2 1).toNat := himp _ _ (hp9 2)
                  have b17992 := hb (x 2 1)
                  have b17993 := hb (x 2 9)
                  clear * - r17991 b17992 b17993 d17901
                  omega
                have d17994 : (x 5 12).toNat = 0 := by
                  have r17995 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e17996 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                  have e17997 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                  have b17998 := hb (x 2 3)
                  have b17999 := hb (x 3 2)
                  have b18000 := hb (x 4 13)
                  have b18001 := hb (x 5 12)
                  clear * - r17995 e17996 e17997 b17998 b17999 b18000 b18001 d17892
                  omega
                have d18002 : (x 5 3 && x 5 12).toNat = 0 := by
                  have r18003 := hand2 (x 5 3) (x 5 12)
                  have b18004 := hb (x 5 12)
                  have b18005 := hb (x 5 3 && x 5 12)
                  clear * - r18003 b18004 b18005 d17994
                  omega
                have d18006 : (x 5 4).toNat = 0 := by
                  have r18007 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
                  have b18008 := hb (x 5 4)
                  have b18009 := hb (x 5 12)
                  clear * - r18007 b18008 b18009 d17994
                  omega
                have d18010 : (x 4 13).toNat = 0 := by
                  have r18011 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e18012 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                  have e18013 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                  have b18014 := hb (x 2 3)
                  have b18015 := hb (x 3 2)
                  have b18016 := hb (x 4 13)
                  have b18017 := hb (x 5 12)
                  clear * - r18011 e18012 e18013 b18014 b18015 b18016 b18017 d17994 d17892
                  omega
                have d18018 : (x 4 5).toNat = 0 := by
                  have r18019 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
                  have b18020 := hb (x 4 5)
                  have b18021 := hb (x 4 13)
                  clear * - r18019 b18020 b18021 d18010
                  omega
                have d18022 : (x 2 3).toNat = 0 := by
                  have r18023 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e18024 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                  have e18025 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                  have b18026 := hb (x 2 3)
                  have b18027 := hb (x 3 2)
                  have b18028 := hb (x 4 13)
                  have b18029 := hb (x 5 12)
                  clear * - r18023 e18024 e18025 b18026 b18027 b18028 b18029 d17994 d18010 d17892
                  omega
                have d18030 : (x 2 11).toNat = 0 := by
                  have r18031 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
                  have b18032 := hb (x 2 3)
                  have b18033 := hb (x 2 11)
                  clear * - r18031 b18032 b18033 d18022
                  omega
                have d18034 : (x 6 8).toNat = 0 := by
                  have r18035 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e18036 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                  have e18037 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                  have e18038 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                  have e18039 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                  have e18040 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                  have e18041 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                  have b18042 := hb (x (-1) 7)
                  have b18043 := hb (x 0 6)
                  have b18044 := hb (x 1 5)
                  have b18045 := hb (x 2 4)
                  have b18046 := hb (x 3 11)
                  have b18047 := hb (x 4 10)
                  have b18048 := hb (x 5 9)
                  have b18049 := hb (x 6 8)
                  clear * - r18035 e18036 e18037 e18038 e18039 e18040 e18041 b18042 b18043 b18044 b18045 b18046 b18047 b18048 b18049 d17864 d17817 g31 g25 f17561
                  omega
                have d18050 : (x 6 5 && x 6 8).toNat = 0 := by
                  have r18051 := hand2 (x 6 5) (x 6 8)
                  have b18052 := hb (x 6 8)
                  have b18053 := hb (x 6 5 && x 6 8)
                  clear * - r18051 b18052 b18053 d18034
                  omega
                have d18054 : (x 5 9).toNat = 0 := by
                  have r18055 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e18056 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                  have e18057 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                  have e18058 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                  have e18059 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                  have e18060 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                  have e18061 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                  have b18062 := hb (x (-1) 7)
                  have b18063 := hb (x 0 6)
                  have b18064 := hb (x 1 5)
                  have b18065 := hb (x 2 4)
                  have b18066 := hb (x 3 11)
                  have b18067 := hb (x 4 10)
                  have b18068 := hb (x 5 9)
                  have b18069 := hb (x 6 8)
                  clear * - r18055 e18056 e18057 e18058 e18059 e18060 e18061 b18062 b18063 b18064 b18065 b18066 b18067 b18068 b18069 d18034 d17864 d17817 g31 g25 f17561
                  omega
                have d18070 : (x 5 6 && x 5 9).toNat = 0 := by
                  have r18071 := hand2 (x 5 6) (x 5 9)
                  have b18072 := hb (x 5 9)
                  have b18073 := hb (x 5 6 && x 5 9)
                  clear * - r18071 b18072 b18073 d18054
                  omega
                have d18074 : (x (-1) 7).toNat = 0 := by
                  have r18075 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e18076 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                  have e18077 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                  have e18078 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                  have e18079 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                  have e18080 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                  have e18081 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                  have b18082 := hb (x (-1) 7)
                  have b18083 := hb (x 0 6)
                  have b18084 := hb (x 1 5)
                  have b18085 := hb (x 2 4)
                  have b18086 := hb (x 3 11)
                  have b18087 := hb (x 4 10)
                  have b18088 := hb (x 5 9)
                  have b18089 := hb (x 6 8)
                  clear * - r18075 e18076 e18077 e18078 e18079 e18080 e18081 b18082 b18083 b18084 b18085 b18086 b18087 b18088 b18089 d18034 d18054 d17864 d17817 g31 g25 f17561
                  omega
                cases h18090 : x 1 7
                · have f18091 : (x 1 7).toNat = 0 := by rw [h18090]; rfl
                  cases h18092 : x (-1) 8
                  · have f18093 : (x (-1) 8).toNat = 0 := by rw [h18092]; rfl
                    cases h18094 : x (-1) 12
                    · have f18095 : (x (-1) 12).toNat = 0 := by rw [h18094]; rfl
                      have r18096 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r18097 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r18098 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r18099 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r18100 : (x (-5) 8).toNat + (x (-6) 1 && x (-6) 9).toNat + (x (-7) 2 && x (-7) 10).toNat + (x (-8) 3 && x (-8) 11).toNat + (x (-9) 4 && x (-9) 12).toNat + (x (-10) 5 && x (-10) 13).toNat + (x (-11) 6 && x (-11) 14).toNat + (x (-12) 7).toNat = 1 := by have q := hd8 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e18101 : (x (-6) 1 && x (-6) 9).toNat = (x (-6) 9).toNat := handr _ _ (fun h => hp9 (-6) (h))
                      have e18102 : (x (-7) 2 && x (-7) 10).toNat = (x (-7) 10).toNat := handr _ _ (fun h => hp10 (-7) (h))
                      have e18103 : (x (-8) 3 && x (-8) 11).toNat = (x (-8) 11).toNat := handr _ _ (fun h => hp11 (-8) (h))
                      have e18104 : (x (-9) 4 && x (-9) 12).toNat = (x (-9) 4).toNat := handl _ _ (fun h => hp4 (-9) (h))
                      have e18105 : (x (-10) 5 && x (-10) 13).toNat = (x (-10) 5).toNat := handl _ _ (fun h => hp5 (-10) (h))
                      have e18106 : (x (-11) 6 && x (-11) 14).toNat = (x (-11) 6).toNat := handl _ _ (fun h => hp6 (-11) (h))
                      have r18107 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e18108 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                      have e18109 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                      have e18110 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                      have e18111 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                      have e18112 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                      have e18113 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                      have r18114 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e18115 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
                      have e18116 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
                      have e18117 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
                      have e18118 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
                      have e18119 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
                      have e18120 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
                      have r18121 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e18122 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
                      have e18123 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
                      have r18124 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e18125 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
                      have e18126 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
                      have r18127 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e18128 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                      have e18129 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                      have r18130 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e18131 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
                      have e18132 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
                      have r18133 : (x (-11) 14).toNat + (x (-12) 1).toNat = 1 := by have q := hd14 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r18134 : (x (-10) 14).toNat + (x (-11) 1).toNat = 1 := by have q := hd14 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r18135 : 1 ≤ (x 1 2).toNat + (x 0 1 && x 0 3).toNat + (x (-1) 2 && x (-1) 4).toNat + (x (-2) 3 && x (-2) 5).toNat + (x (-3) 4 && x (-3) 6).toNat + (x (-4) 5 && x (-4) 7).toNat + (x (-5) 6 && x (-5) 8).toNat + (x (-6) 7 && x (-6) 9).toNat + (x (-7) 8 && x (-7) 10).toNat + (x (-8) 9 && x (-8) 11).toNat + (x (-9) 10 && x (-9) 12).toNat + (x (-10) 11 && x (-10) 13).toNat + (x (-11) 12 && x (-11) 14).toNat + (x (-12) 13).toNat := by have q := hcov2 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r18136 : 1 ≤ (x 11 3).toNat + (x 10 1 && x 10 4).toNat + (x 9 2 && x 9 5).toNat + (x 8 3 && x 8 6).toNat + (x 7 4 && x 7 7).toNat + (x 6 5 && x 6 8).toNat + (x 5 6 && x 5 9).toNat + (x 4 7 && x 4 10).toNat + (x 3 8 && x 3 11).toNat + (x 2 9 && x 2 12).toNat + (x 1 10 && x 1 13).toNat + (x 0 11 && x 0 14).toNat + (x (-1) 12).toNat := by have q := hcov3 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r18137 : 1 ≤ (x 7 5).toNat + (x 6 1 && x 6 6).toNat + (x 5 2 && x 5 7).toNat + (x 4 3 && x 4 8).toNat + (x 3 4 && x 3 9).toNat + (x 2 5 && x 2 10).toNat + (x 1 6 && x 1 11).toNat + (x 0 7 && x 0 12).toNat + (x (-1) 8 && x (-1) 13).toNat + (x (-2) 9 && x (-2) 14).toNat + (x (-3) 10).toNat := by have q := hcov5 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r18138 : 1 ≤ (x (-5) 9).toNat + (x (-6) 1 && x (-6) 10).toNat + (x (-7) 2 && x (-7) 11).toNat + (x (-8) 3 && x (-8) 12).toNat + (x (-9) 4 && x (-9) 13).toNat + (x (-10) 5 && x (-10) 14).toNat + (x (-11) 6).toNat := by have q := hcov9 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r18139 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r18140 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r18141 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r18142 : 1 ≤ (x (-11) 13).toNat + (x (-12) 1 && x (-12) 14).toNat + (x (-13) 2).toNat := by have q := hcov13 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r18143 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r18144 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r18145 : (x (-13) 2).toNat ≤ (x (-13) 14).toNat := himp _ _ (hp2 (-13))
                      have r18146 : (x (-11) 13).toNat ≤ (x (-11) 1).toNat := himp _ _ (hp13 (-11))
                      have r18147 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
                      have r18148 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
                      have r18149 := hand2 (x (-4) 5) (x (-4) 7)
                      have r18150 := hand1 (x (-7) 8) (x (-7) 10)
                      have r18151 := hand1 (x (-8) 9) (x (-8) 11)
                      have r18152 := hand1 (x (-9) 10) (x (-9) 12)
                      have r18153 := hand1 (x (-10) 11) (x (-10) 13)
                      have r18154 := hand1 (x (-11) 12) (x (-11) 14)
                      have r18155 := hand2 (x 10 1) (x 10 4)
                      have r18156 := hand2 (x 9 2) (x 9 5)
                      have r18157 := hand2 (x 8 3) (x 8 6)
                      have r18158 := hand2 (x 7 4) (x 7 7)
                      have r18159 := hand1 (x 3 8) (x 3 11)
                      have r18160 := hand2 (x 6 1) (x 6 6)
                      have r18161 := hand2 (x 5 2) (x 5 7)
                      have r18162 := hand2 (x 4 3) (x 4 8)
                      have r18163 := hand2 (x 3 4) (x 3 9)
                      have r18164 := hand1 (x (-2) 9) (x (-2) 14)
                      have r18165 := hand2 (x (-8) 3) (x (-8) 12)
                      have r18166 := hand1 (x (-9) 4) (x (-9) 13)
                      have r18167 := hand1 (x (-10) 5) (x (-10) 14)
                      have r18168 := hand1 (x (-4) 3) (x (-4) 12)
                      have r18169 := hand1 (x (-6) 5) (x (-6) 14)
                      have r18170 := hand1 (x (-2) 5) (x (-2) 14)
                      have r18171 := hand1 (x 11 1) (x 11 12)
                      have r18172 := hand1 (x 10 2) (x 10 13)
                      have r18173 := hand1 (x 9 3) (x 9 14)
                      have r18174 := hand1 (x (-12) 1) (x (-12) 14)
                      have r18175 := hand2 (x (-10) 1) (x (-10) 14)
                      have r18176 := hand1 (x 13 1) (x 13 14)
                      linarith only [r18096, r18097, r18098, r18099, r18100, e18101, e18102, e18103, e18104, e18105, e18106, r18107, e18108, e18109, e18110, e18111, e18112, e18113, r18114, e18115, e18116, e18117, e18118, e18119, e18120, r18121, e18122, e18123, r18124, e18125, e18126, r18127, e18128, e18129, r18130, e18131, e18132, r18133, r18134, r18135, r18136, r18137, r18138, r18139, r18140, r18141, r18142, r18143, r18144, r18145, r18146, r18147, r18148, r18149, r18150, r18151, r18152, r18153, r18154, r18155, r18156, r18157, r18158, r18159, r18160, r18161, r18162, r18163, r18164, r18165, r18166, r18167, r18168, r18169, r18170, r18171, r18172, r18173, r18174, r18175, r18176, d17777, d17757, d17733, d17603, d17623, d17704, d17615, d17643, g4, d17660, g6, f17816, f18093, g9, f18095, g12, g13, g15, g19, g20, g22, g23, g27, d17811, g29, d17901, d17990, d17950, g32, d17817, d17864, d18054, d18034, g36, g37, g38, d17619, d17773, d17793, d18050, d18070, d17868, g39, g40, g41, d17958, g51, d17564, g52, g55, g56, g57, g58, g59, d17954, g67, g68, g69]
                    · have f18324 : (x (-1) 12).toNat = 1 := by rw [h18094]; rfl
                      have d18325 : (x (-2) 13).toNat = 0 := by
                        have r18326 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e18327 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                        have e18328 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                        have b18329 := hb (x (-4) 3)
                        have b18330 := hb (x (-3) 2)
                        have b18331 := hb (x (-2) 13)
                        have b18332 := hb (x (-1) 12)
                        clear * - r18326 e18327 e18328 b18329 b18330 b18331 b18332 f18324 d17623
                        omega
                      have d18333 : (x (-4) 2).toNat = 1 := by
                        have r18334 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b18335 := hb (x (-4) 2)
                        have b18336 := hb (x (-2) 13)
                        have b18337 := hb (x (-3) 1 && x (-3) 14)
                        clear * - r18334 b18335 b18336 b18337 d18325 d17595
                        omega
                      have d18338 : (x (-4) 3).toNat = 0 := by
                        have r18339 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e18340 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                        have e18341 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                        have b18342 := hb (x (-4) 3)
                        have b18343 := hb (x (-3) 2)
                        have b18344 := hb (x (-2) 13)
                        have b18345 := hb (x (-1) 12)
                        clear * - r18339 e18340 e18341 b18342 b18343 b18344 b18345 f18324 d18325 d17623
                        omega
                      have d18346 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
                        have r18347 := hand1 (x (-4) 3) (x (-4) 14)
                        have b18348 := hb (x (-4) 3)
                        have b18349 := hb (x (-4) 3 && x (-4) 14)
                        clear * - r18347 b18348 b18349 d18338
                        omega
                      have d18350 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
                        have r18351 := hand1 (x (-4) 3) (x (-4) 13)
                        have b18352 := hb (x (-4) 3)
                        have b18353 := hb (x (-4) 3 && x (-4) 13)
                        clear * - r18351 b18352 b18353 d18338
                        omega
                      have d18354 : (x (-2) 12).toNat = 0 := by
                        have r18355 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e18356 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                        have e18357 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                        have b18358 := hb (x (-5) 3)
                        have b18359 := hb (x (-4) 2)
                        have b18360 := hb (x (-3) 13)
                        have b18361 := hb (x (-2) 12)
                        clear * - r18355 e18356 e18357 b18358 b18359 b18360 b18361 d17668 d18333
                        omega
                      have d18362 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
                        have r18363 := hand2 (x (-2) 1) (x (-2) 12)
                        have b18364 := hb (x (-2) 12)
                        have b18365 := hb (x (-2) 1 && x (-2) 12)
                        clear * - r18363 b18364 b18365 d18354
                        omega
                      have d18366 : (x (-5) 4).toNat = 1 := by
                        have r18367 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b18368 := hb (x (-5) 4)
                        have b18369 := hb (x (-1) 11)
                        have b18370 := hb (x (-2) 1 && x (-2) 12)
                        have b18371 := hb (x (-3) 2 && x (-3) 13)
                        have b18372 := hb (x (-4) 3 && x (-4) 14)
                        clear * - r18367 b18368 b18369 b18370 b18371 b18372 g11 d18362 d17627 d18346
                        omega
                      have d18373 : (x (-5) 12).toNat = 1 := by
                        have r18374 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
                        have b18375 := hb (x (-5) 4)
                        have b18376 := hb (x (-5) 12)
                        clear * - r18374 b18375 b18376 d18366
                        omega
                      have d18377 : (x (-6) 13).toNat = 0 := by
                        have r18378 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e18379 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                        have e18380 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                        have b18381 := hb (x (-8) 3)
                        have b18382 := hb (x (-7) 2)
                        have b18383 := hb (x (-6) 13)
                        have b18384 := hb (x (-5) 12)
                        clear * - r18378 e18379 e18380 b18381 b18382 b18383 b18384 d18373
                        omega
                      have d18385 : (x (-6) 5).toNat = 0 := by
                        have r18386 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
                        have b18387 := hb (x (-6) 5)
                        have b18388 := hb (x (-6) 13)
                        clear * - r18386 b18387 b18388 d18377
                        omega
                      have d18389 : (x (-7) 2).toNat = 0 := by
                        have r18390 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e18391 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                        have e18392 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                        have b18393 := hb (x (-8) 3)
                        have b18394 := hb (x (-7) 2)
                        have b18395 := hb (x (-6) 13)
                        have b18396 := hb (x (-5) 12)
                        clear * - r18390 e18391 e18392 b18393 b18394 b18395 b18396 d18373 d18377
                        omega
                      have d18397 : (x (-6) 1 && x (-6) 14).toNat = 1 := by
                        have r18398 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b18399 := hb (x (-7) 2)
                        have b18400 := hb (x (-5) 13)
                        have b18401 := hb (x (-6) 1 && x (-6) 14)
                        clear * - r18398 b18399 b18400 b18401 g3 d18389
                        omega
                      have d18402 : (x (-6) 1).toNat = 1 := by
                        have r18403 := hand1 (x (-6) 1) (x (-6) 14)
                        have b18404 := hb (x (-6) 1)
                        have b18405 := hb (x (-6) 1 && x (-6) 14)
                        clear * - r18403 b18404 b18405 d18397
                        omega
                      have d18406 : (x (-5) 14).toNat = 0 := by
                        have r18407 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b18408 := hb (x (-6) 1)
                        have b18409 := hb (x (-5) 14)
                        clear * - r18407 b18408 b18409 d18402
                        omega
                      have d18410 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
                        have r18411 := hand2 (x (-5) 4) (x (-5) 14)
                        have b18412 := hb (x (-5) 14)
                        have b18413 := hb (x (-5) 4 && x (-5) 14)
                        clear * - r18411 b18412 b18413 d18406
                        omega
                      have r18414 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b18415 := hb (x (-6) 5)
                      have b18416 := hb (x (-1) 10)
                      have b18417 := hb (x (-2) 1 && x (-2) 11)
                      have b18418 := hb (x (-3) 2 && x (-3) 12)
                      have b18419 := hb (x (-4) 3 && x (-4) 13)
                      have b18420 := hb (x (-5) 4 && x (-5) 14)
                      linarith only [r18414, b18415, b18416, b18417, b18418, b18419, b18420, g10, g72, d17631, d18350, d18410, d18385]
                  · have f18421 : (x (-1) 8).toNat = 1 := by rw [h18092]; rfl
                    have d18422 : (x (-2) 9).toNat = 0 := by
                      have r18423 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e18424 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                      have e18425 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                      have e18426 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                      have e18427 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                      have e18428 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                      have e18429 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                      have b18430 := hb (x (-8) 7)
                      have b18431 := hb (x (-7) 6)
                      have b18432 := hb (x (-6) 5)
                      have b18433 := hb (x (-5) 4)
                      have b18434 := hb (x (-4) 11)
                      have b18435 := hb (x (-3) 10)
                      have b18436 := hb (x (-2) 9)
                      have b18437 := hb (x (-1) 8)
                      clear * - r18423 e18424 e18425 e18426 e18427 e18428 e18429 b18430 b18431 b18432 b18433 b18434 b18435 b18436 b18437 f18421 d17643
                      omega
                    have d18438 : (x (-4) 11).toNat = 0 := by
                      have r18439 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e18440 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                      have e18441 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                      have e18442 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                      have e18443 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                      have e18444 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                      have e18445 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                      have b18446 := hb (x (-8) 7)
                      have b18447 := hb (x (-7) 6)
                      have b18448 := hb (x (-6) 5)
                      have b18449 := hb (x (-5) 4)
                      have b18450 := hb (x (-4) 11)
                      have b18451 := hb (x (-3) 10)
                      have b18452 := hb (x (-2) 9)
                      have b18453 := hb (x (-1) 8)
                      clear * - r18439 e18440 e18441 e18442 e18443 e18444 e18445 b18446 b18447 b18448 b18449 b18450 b18451 b18452 b18453 f18421 d18422 d17643
                      omega
                    have d18454 : (x (-4) 2 && x (-4) 11).toNat = 0 := by
                      have r18455 := hand2 (x (-4) 2) (x (-4) 11)
                      have b18456 := hb (x (-4) 11)
                      have b18457 := hb (x (-4) 2 && x (-4) 11)
                      clear * - r18455 b18456 b18457 d18438
                      omega
                    have d18458 : (x (-8) 4).toNat = 1 := by
                      have r18459 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b18460 := hb (x (-8) 4)
                      have b18461 := hb (x (-4) 11)
                      have b18462 := hb (x (-5) 1 && x (-5) 12)
                      have b18463 := hb (x (-6) 2 && x (-6) 13)
                      have b18464 := hb (x (-7) 3 && x (-7) 14)
                      clear * - r18459 b18460 b18461 b18462 b18463 b18464 d18438 d17729 g82 g83
                      omega
                    have d18465 : (x (-8) 12).toNat = 1 := by
                      have r18466 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
                      have b18467 := hb (x (-8) 4)
                      have b18468 := hb (x (-8) 12)
                      clear * - r18466 b18467 b18468 d18458
                      omega
                    have d18469 : (x (-9) 13).toNat = 0 := by
                      have r18470 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e18471 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
                      have e18472 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
                      have b18473 := hb (x (-11) 3)
                      have b18474 := hb (x (-10) 2)
                      have b18475 := hb (x (-9) 13)
                      have b18476 := hb (x (-8) 12)
                      clear * - r18470 e18471 e18472 b18473 b18474 b18475 b18476 d18465
                      omega
                    have d18477 : (x (-9) 8 && x (-9) 13).toNat = 0 := by
                      have r18478 := hand2 (x (-9) 8) (x (-9) 13)
                      have b18479 := hb (x (-9) 13)
                      have b18480 := hb (x (-9) 8 && x (-9) 13)
                      clear * - r18478 b18479 b18480 d18469
                      omega
                    have d18481 : (x (-9) 5).toNat = 0 := by
                      have r18482 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
                      have b18483 := hb (x (-9) 5)
                      have b18484 := hb (x (-9) 13)
                      clear * - r18482 b18483 b18484 d18469
                      omega
                    have d18485 : (x (-5) 4).toNat = 0 := by
                      have r18486 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e18487 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                      have e18488 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                      have e18489 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                      have e18490 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                      have e18491 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                      have e18492 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                      have b18493 := hb (x (-8) 7)
                      have b18494 := hb (x (-7) 6)
                      have b18495 := hb (x (-6) 5)
                      have b18496 := hb (x (-5) 4)
                      have b18497 := hb (x (-4) 11)
                      have b18498 := hb (x (-3) 10)
                      have b18499 := hb (x (-2) 9)
                      have b18500 := hb (x (-1) 8)
                      clear * - r18486 e18487 e18488 e18489 e18490 e18491 e18492 b18493 b18494 b18495 b18496 b18497 b18498 b18499 b18500 f18421 d18422 d17643 d18438
                      omega
                    have d18501 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
                      have r18502 := hand1 (x (-5) 4) (x (-5) 14)
                      have b18503 := hb (x (-5) 4)
                      have b18504 := hb (x (-5) 4 && x (-5) 14)
                      clear * - r18502 b18503 b18504 d18485
                      omega
                    have d18505 : (x (-5) 4 && x (-5) 11).toNat = 0 := by
                      have r18506 := hand1 (x (-5) 4) (x (-5) 11)
                      have b18507 := hb (x (-5) 4)
                      have b18508 := hb (x (-5) 4 && x (-5) 11)
                      clear * - r18506 b18507 b18508 d18485
                      omega
                    have d18509 : (x (-6) 5).toNat = 0 := by
                      have r18510 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e18511 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                      have e18512 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                      have e18513 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                      have e18514 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                      have e18515 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                      have e18516 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                      have b18517 := hb (x (-8) 7)
                      have b18518 := hb (x (-7) 6)
                      have b18519 := hb (x (-6) 5)
                      have b18520 := hb (x (-5) 4)
                      have b18521 := hb (x (-4) 11)
                      have b18522 := hb (x (-3) 10)
                      have b18523 := hb (x (-2) 9)
                      have b18524 := hb (x (-1) 8)
                      clear * - r18510 e18511 e18512 e18513 e18514 e18515 e18516 b18517 b18518 b18519 b18520 b18521 b18522 b18523 b18524 f18421 d18422 d17643 d18438 d18485
                      omega
                    have d18525 : (x (-6) 5 && x (-6) 12).toNat = 0 := by
                      have r18526 := hand1 (x (-6) 5) (x (-6) 12)
                      have b18527 := hb (x (-6) 5)
                      have b18528 := hb (x (-6) 5 && x (-6) 12)
                      clear * - r18526 b18527 b18528 d18509
                      omega
                    have d18529 : (x (-4) 3 && x (-4) 13).toNat = 1 := by
                      have r18530 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b18531 := hb (x (-6) 5)
                      have b18532 := hb (x (-1) 10)
                      have b18533 := hb (x (-2) 1 && x (-2) 11)
                      have b18534 := hb (x (-3) 2 && x (-3) 12)
                      have b18535 := hb (x (-4) 3 && x (-4) 13)
                      have b18536 := hb (x (-5) 4 && x (-5) 14)
                      clear * - r18530 b18531 b18532 b18533 b18534 b18535 b18536 g10 g72 d17631 d18501 d18509
                      omega
                    have d18537 : (x (-4) 3).toNat = 1 := by
                      have r18538 := hand1 (x (-4) 3) (x (-4) 13)
                      have b18539 := hb (x (-4) 3)
                      have b18540 := hb (x (-4) 3 && x (-4) 13)
                      clear * - r18538 b18539 b18540 d18529
                      omega
                    have d18541 : (x (-1) 12).toNat = 0 := by
                      have r18542 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e18543 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                      have e18544 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                      have b18545 := hb (x (-4) 3)
                      have b18546 := hb (x (-3) 2)
                      have b18547 := hb (x (-2) 13)
                      have b18548 := hb (x (-1) 12)
                      clear * - r18542 e18543 e18544 b18545 b18546 b18547 b18548 d17623 d18537
                      omega
                    have d18549 : (x (-2) 13).toNat = 0 := by
                      have r18550 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e18551 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                      have e18552 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                      have b18553 := hb (x (-4) 3)
                      have b18554 := hb (x (-3) 2)
                      have b18555 := hb (x (-2) 13)
                      have b18556 := hb (x (-1) 12)
                      clear * - r18550 e18551 e18552 b18553 b18554 b18555 b18556 d18541 d17623 d18537
                      omega
                    have d18557 : (x (-2) 5).toNat = 0 := by
                      have r18558 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
                      have b18559 := hb (x (-2) 5)
                      have b18560 := hb (x (-2) 13)
                      clear * - r18558 b18559 b18560 d18549
                      omega
                    have d18561 : (x (-2) 5 && x (-2) 14).toNat = 0 := by
                      have r18562 := hand1 (x (-2) 5) (x (-2) 14)
                      have b18563 := hb (x (-2) 5)
                      have b18564 := hb (x (-2) 5 && x (-2) 14)
                      clear * - r18562 b18563 b18564 d18557
                      omega
                    have d18565 : (x 3 9).toNat = 1 := by
                      have r18566 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b18567 := hb (x (-3) 6)
                      have b18568 := hb (x 3 9)
                      have b18569 := hb (x 2 1 && x 2 10)
                      have b18570 := hb (x 1 2 && x 1 11)
                      have b18571 := hb (x 0 3 && x 0 12)
                      have b18572 := hb (x (-1) 4 && x (-1) 13)
                      have b18573 := hb (x (-2) 5 && x (-2) 14)
                      clear * - r18566 b18567 b18568 b18569 b18570 b18571 b18572 b18573 d17954 g67 g68 g69 d18561 d17615
                      omega
                    have d18574 : (x 4 8).toNat = 0 := by
                      have r18575 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e18576 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
                      have e18577 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
                      have e18578 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
                      have e18579 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
                      have e18580 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
                      have e18581 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
                      have b18582 := hb (x (-3) 7)
                      have b18583 := hb (x (-2) 6)
                      have b18584 := hb (x (-1) 5)
                      have b18585 := hb (x 0 4)
                      have b18586 := hb (x 1 11)
                      have b18587 := hb (x 2 10)
                      have b18588 := hb (x 3 9)
                      have b18589 := hb (x 4 8)
                      clear * - r18575 e18576 e18577 e18578 e18579 e18580 e18581 b18582 b18583 b18584 b18585 b18586 b18587 b18588 b18589 d18565 d17950 d17811 g16 g8
                      omega
                    have d18590 : (x (-2) 6).toNat = 0 := by
                      have r18591 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e18592 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
                      have e18593 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
                      have e18594 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
                      have e18595 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
                      have e18596 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
                      have e18597 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
                      have b18598 := hb (x (-3) 7)
                      have b18599 := hb (x (-2) 6)
                      have b18600 := hb (x (-1) 5)
                      have b18601 := hb (x 0 4)
                      have b18602 := hb (x 1 11)
                      have b18603 := hb (x 2 10)
                      have b18604 := hb (x 3 9)
                      have b18605 := hb (x 4 8)
                      clear * - r18591 e18592 e18593 e18594 e18595 e18596 e18597 b18598 b18599 b18600 b18601 b18602 b18603 b18604 b18605 d18574 d18565 d17950 d17811 g16 g8
                      omega
                    have d18606 : (x (-2) 1 && x (-2) 6).toNat = 0 := by
                      have r18607 := hand2 (x (-2) 1) (x (-2) 6)
                      have b18608 := hb (x (-2) 6)
                      have b18609 := hb (x (-2) 1 && x (-2) 6)
                      clear * - r18607 b18608 b18609 d18590
                      omega
                    have d18610 : (x (-4) 2).toNat = 1 := by
                      have r18611 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b18612 := hb (x (-4) 2)
                      have b18613 := hb (x (-2) 13)
                      have b18614 := hb (x (-3) 1 && x (-3) 14)
                      clear * - r18611 b18612 b18613 b18614 d18549 d17595
                      omega
                    have d18615 : (x (-2) 12).toNat = 0 := by
                      have r18616 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e18617 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                      have e18618 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                      have b18619 := hb (x (-5) 3)
                      have b18620 := hb (x (-4) 2)
                      have b18621 := hb (x (-3) 13)
                      have b18622 := hb (x (-2) 12)
                      clear * - r18616 e18617 e18618 b18619 b18620 b18621 b18622 d17668 d18610
                      omega
                    have d18623 : (x (-5) 3).toNat = 0 := by
                      have r18624 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e18625 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                      have e18626 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                      have b18627 := hb (x (-5) 3)
                      have b18628 := hb (x (-4) 2)
                      have b18629 := hb (x (-3) 13)
                      have b18630 := hb (x (-2) 12)
                      clear * - r18624 e18625 e18626 b18627 b18628 b18629 b18630 d18615 d17668 d18610
                      omega
                    have d18631 : (x (-5) 3 && x (-5) 12).toNat = 0 := by
                      have r18632 := hand1 (x (-5) 3) (x (-5) 12)
                      have b18633 := hb (x (-5) 3)
                      have b18634 := hb (x (-5) 3 && x (-5) 12)
                      clear * - r18632 b18633 b18634 d18623
                      omega
                    have d18635 : (x (-5) 11).toNat = 0 := by
                      have r18636 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
                      have b18637 := hb (x (-5) 3)
                      have b18638 := hb (x (-5) 11)
                      clear * - r18636 b18637 b18638 d18623
                      omega
                    have d18639 : (x (-7) 6).toNat = 0 := by
                      have r18640 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e18641 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                      have e18642 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                      have e18643 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                      have e18644 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                      have e18645 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                      have e18646 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                      have b18647 := hb (x (-8) 7)
                      have b18648 := hb (x (-7) 6)
                      have b18649 := hb (x (-6) 5)
                      have b18650 := hb (x (-5) 4)
                      have b18651 := hb (x (-4) 11)
                      have b18652 := hb (x (-3) 10)
                      have b18653 := hb (x (-2) 9)
                      have b18654 := hb (x (-1) 8)
                      clear * - r18640 e18641 e18642 e18643 e18644 e18645 e18646 b18647 b18648 b18649 b18650 b18651 b18652 b18653 b18654 f18421 d18422 d17643 d18438 d18485 d18509
                      omega
                    have d18655 : (x (-7) 6 && x (-7) 13).toNat = 0 := by
                      have r18656 := hand1 (x (-7) 6) (x (-7) 13)
                      have b18657 := hb (x (-7) 6)
                      have b18658 := hb (x (-7) 6 && x (-7) 13)
                      clear * - r18656 b18657 b18658 d18639
                      omega
                    have d18659 : (x (-8) 7).toNat = 0 := by
                      have r18660 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e18661 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                      have e18662 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                      have e18663 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                      have e18664 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                      have e18665 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                      have e18666 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                      have b18667 := hb (x (-8) 7)
                      have b18668 := hb (x (-7) 6)
                      have b18669 := hb (x (-6) 5)
                      have b18670 := hb (x (-5) 4)
                      have b18671 := hb (x (-4) 11)
                      have b18672 := hb (x (-3) 10)
                      have b18673 := hb (x (-2) 9)
                      have b18674 := hb (x (-1) 8)
                      clear * - r18660 e18661 e18662 e18663 e18664 e18665 e18666 b18667 b18668 b18669 b18670 b18671 b18672 b18673 b18674 f18421 d18422 d17643 d18438 d18485 d18509 d18639
                      omega
                    have d18675 : (x (-8) 7 && x (-8) 14).toNat = 0 := by
                      have r18676 := hand1 (x (-8) 7) (x (-8) 14)
                      have b18677 := hb (x (-8) 7)
                      have b18678 := hb (x (-8) 7 && x (-8) 14)
                      clear * - r18676 b18677 b18678 d18659
                      omega
                    have d18679 : (x (-8) 7 && x (-8) 12).toNat = 0 := by
                      have r18680 := hand1 (x (-8) 7) (x (-8) 12)
                      have b18681 := hb (x (-8) 7)
                      have b18682 := hb (x (-8) 7 && x (-8) 12)
                      clear * - r18680 b18681 b18682 d18659
                      omega
                    have d18683 : (x (-4) 8).toNat = 0 := by
                      have r18684 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e18685 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
                      have e18686 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
                      have e18687 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
                      have e18688 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
                      have e18689 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
                      have e18690 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
                      have b18691 := hb (x (-11) 7)
                      have b18692 := hb (x (-10) 6)
                      have b18693 := hb (x (-9) 5)
                      have b18694 := hb (x (-8) 4)
                      have b18695 := hb (x (-7) 11)
                      have b18696 := hb (x (-6) 10)
                      have b18697 := hb (x (-5) 9)
                      have b18698 := hb (x (-4) 8)
                      clear * - r18684 e18685 e18686 e18687 e18688 e18689 e18690 b18691 b18692 b18693 b18694 b18695 b18696 b18697 b18698 d17733 g2 g0 d18458 d18481
                      omega
                    have d18699 : (x (-4) 3 && x (-4) 8).toNat = 0 := by
                      have r18700 := hand2 (x (-4) 3) (x (-4) 8)
                      have b18701 := hb (x (-4) 8)
                      have b18702 := hb (x (-4) 3 && x (-4) 8)
                      clear * - r18700 b18701 b18702 d18683
                      omega
                    have r18703 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18704 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
                    have e18705 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
                    have e18706 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
                    have e18707 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
                    have e18708 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
                    have e18709 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
                    have r18710 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18711 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                    have e18712 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                    have e18713 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                    have e18714 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                    have e18715 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                    have e18716 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                    have r18717 : 1 ≤ (x (-1) 5).toNat + (x (-2) 1 && x (-2) 6).toNat + (x (-3) 2 && x (-3) 7).toNat + (x (-4) 3 && x (-4) 8).toNat + (x (-5) 4 && x (-5) 9).toNat + (x (-6) 5 && x (-6) 10).toNat + (x (-7) 6 && x (-7) 11).toNat + (x (-8) 7 && x (-8) 12).toNat + (x (-9) 8 && x (-9) 13).toNat + (x (-10) 9 && x (-10) 14).toNat + (x (-11) 10).toNat := by have q := hcov5 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r18718 : 1 ≤ (x (-1) 7).toNat + (x (-2) 1 && x (-2) 8).toNat + (x (-3) 2 && x (-3) 9).toNat + (x (-4) 3 && x (-4) 10).toNat + (x (-5) 4 && x (-5) 11).toNat + (x (-6) 5 && x (-6) 12).toNat + (x (-7) 6 && x (-7) 13).toNat + (x (-8) 7 && x (-8) 14).toNat + (x (-9) 8).toNat := by have q := hcov7 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r18719 : 1 ≤ (x (-2) 9).toNat + (x (-3) 1 && x (-3) 10).toNat + (x (-4) 2 && x (-4) 11).toNat + (x (-5) 3 && x (-5) 12).toNat + (x (-6) 4 && x (-6) 13).toNat + (x (-7) 5 && x (-7) 14).toNat + (x (-8) 6).toNat := by have q := hcov9 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r18720 := hand1 (x (-10) 9) (x (-10) 14)
                    have r18721 := hand2 (x (-2) 1) (x (-2) 8)
                    have r18722 := hand2 (x (-4) 3) (x (-4) 10)
                    have r18723 := hand1 (x (-6) 4) (x (-6) 13)
                    have r18724 := hand1 (x (-7) 5) (x (-7) 14)
                    linarith only [r18703, e18704, e18705, e18706, e18707, e18708, e18709, r18710, e18711, e18712, e18713, e18714, e18715, e18716, r18717, r18718, r18719, r18720, r18721, r18722, r18723, r18724, d18635, d17676, d18422, g8, d18074, d18606, d17639, d18699, d17737, g47, g48, d18679, d18477, d17635, d18505, d18525, d18655, d18675, d17647, d18454, d18631]
                · have f18765 : (x 1 7).toNat = 1 := by rw [h18090]; rfl
                  have d18766 : (x 8 8).toNat = 0 := by
                    have r18767 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18768 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                    have e18769 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                    have e18770 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                    have e18771 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                    have e18772 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                    have e18773 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                    have b18774 := hb (x 1 7)
                    have b18775 := hb (x 2 6)
                    have b18776 := hb (x 3 5)
                    have b18777 := hb (x 4 4)
                    have b18778 := hb (x 5 11)
                    have b18779 := hb (x 6 10)
                    have b18780 := hb (x 7 9)
                    have b18781 := hb (x 8 8)
                    clear * - r18767 e18768 e18769 e18770 e18771 e18772 e18773 b18774 b18775 b18776 b18777 b18778 b18779 b18780 b18781 d17926 f18765
                    omega
                  have d18782 : (x 8 8 && x 8 14).toNat = 0 := by
                    have r18783 := hand1 (x 8 8) (x 8 14)
                    have b18784 := hb (x 8 8)
                    have b18785 := hb (x 8 8 && x 8 14)
                    clear * - r18783 b18784 b18785 d18766
                    omega
                  have d18786 : (x 7 9).toNat = 0 := by
                    have r18787 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18788 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                    have e18789 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                    have e18790 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                    have e18791 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                    have e18792 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                    have e18793 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                    have b18794 := hb (x 1 7)
                    have b18795 := hb (x 2 6)
                    have b18796 := hb (x 3 5)
                    have b18797 := hb (x 4 4)
                    have b18798 := hb (x 5 11)
                    have b18799 := hb (x 6 10)
                    have b18800 := hb (x 7 9)
                    have b18801 := hb (x 8 8)
                    clear * - r18787 e18788 e18789 e18790 e18791 e18792 e18793 b18794 b18795 b18796 b18797 b18798 b18799 b18800 b18801 d18766 d17926 f18765
                    omega
                  have d18802 : (x 6 10).toNat = 0 := by
                    have r18803 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18804 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                    have e18805 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                    have e18806 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                    have e18807 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                    have e18808 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                    have e18809 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                    have b18810 := hb (x 1 7)
                    have b18811 := hb (x 2 6)
                    have b18812 := hb (x 3 5)
                    have b18813 := hb (x 4 4)
                    have b18814 := hb (x 5 11)
                    have b18815 := hb (x 6 10)
                    have b18816 := hb (x 7 9)
                    have b18817 := hb (x 8 8)
                    clear * - r18803 e18804 e18805 e18806 e18807 e18808 e18809 b18810 b18811 b18812 b18813 b18814 b18815 b18816 b18817 d18766 d18786 d17926 f18765
                    omega
                  have d18818 : (x 6 1 && x 6 10).toNat = 0 := by
                    have r18819 := hand2 (x 6 1) (x 6 10)
                    have b18820 := hb (x 6 10)
                    have b18821 := hb (x 6 1 && x 6 10)
                    clear * - r18819 b18820 b18821 d18802
                    omega
                  have d18822 : (x 5 11).toNat = 0 := by
                    have r18823 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18824 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                    have e18825 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                    have e18826 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                    have e18827 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                    have e18828 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                    have e18829 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                    have b18830 := hb (x 1 7)
                    have b18831 := hb (x 2 6)
                    have b18832 := hb (x 3 5)
                    have b18833 := hb (x 4 4)
                    have b18834 := hb (x 5 11)
                    have b18835 := hb (x 6 10)
                    have b18836 := hb (x 7 9)
                    have b18837 := hb (x 8 8)
                    clear * - r18823 e18824 e18825 e18826 e18827 e18828 e18829 b18830 b18831 b18832 b18833 b18834 b18835 b18836 b18837 d18766 d18786 d18802 d17926 f18765
                    omega
                  have d18838 : (x 5 2 && x 5 11).toNat = 0 := by
                    have r18839 := hand2 (x 5 2) (x 5 11)
                    have b18840 := hb (x 5 11)
                    have b18841 := hb (x 5 2 && x 5 11)
                    clear * - r18839 b18840 b18841 d18822
                    omega
                  have d18842 : (x 3 4 && x 3 13).toNat = 1 := by
                    have r18843 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b18844 := hb (x 1 6)
                    have b18845 := hb (x 7 9)
                    have b18846 := hb (x 6 1 && x 6 10)
                    have b18847 := hb (x 5 2 && x 5 11)
                    have b18848 := hb (x 4 3 && x 4 12)
                    have b18849 := hb (x 3 4 && x 3 13)
                    have b18850 := hb (x 2 5 && x 2 14)
                    clear * - r18843 b18844 b18845 b18846 b18847 b18848 b18849 b18850 d18786 d18818 d18838 d17922 d17978 g26
                    omega
                  have d18851 : (x 3 4).toNat = 1 := by
                    have r18852 := hand1 (x 3 4) (x 3 13)
                    have b18853 := hb (x 3 4)
                    have b18854 := hb (x 3 4 && x 3 13)
                    clear * - r18852 b18853 b18854 d18842
                    omega
                  have d18855 : (x 3 5).toNat = 0 := by
                    have r18856 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18857 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                    have e18858 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                    have e18859 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                    have e18860 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                    have e18861 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                    have e18862 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                    have b18863 := hb (x 1 7)
                    have b18864 := hb (x 2 6)
                    have b18865 := hb (x 3 5)
                    have b18866 := hb (x 4 4)
                    have b18867 := hb (x 5 11)
                    have b18868 := hb (x 6 10)
                    have b18869 := hb (x 7 9)
                    have b18870 := hb (x 8 8)
                    clear * - r18856 e18857 e18858 e18859 e18860 e18861 e18862 b18863 b18864 b18865 b18866 b18867 b18868 b18869 b18870 d18766 d18786 d18802 d18822 d17926 f18765
                    omega
                  have d18871 : (x 3 5 && x 3 14).toNat = 0 := by
                    have r18872 := hand1 (x 3 5) (x 3 14)
                    have b18873 := hb (x 3 5)
                    have b18874 := hb (x 3 5 && x 3 14)
                    clear * - r18872 b18873 b18874 d18855
                    omega
                  have d18875 : (x 3 5 && x 3 12).toNat = 0 := by
                    have r18876 := hand1 (x 3 5) (x 3 12)
                    have b18877 := hb (x 3 5)
                    have b18878 := hb (x 3 5 && x 3 12)
                    clear * - r18876 b18877 b18878 d18855
                    omega
                  have d18879 : (x 2 6).toNat = 0 := by
                    have r18880 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18881 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                    have e18882 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                    have e18883 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                    have e18884 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                    have e18885 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                    have e18886 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                    have b18887 := hb (x 1 7)
                    have b18888 := hb (x 2 6)
                    have b18889 := hb (x 3 5)
                    have b18890 := hb (x 4 4)
                    have b18891 := hb (x 5 11)
                    have b18892 := hb (x 6 10)
                    have b18893 := hb (x 7 9)
                    have b18894 := hb (x 8 8)
                    clear * - r18880 e18881 e18882 e18883 e18884 e18885 e18886 b18887 b18888 b18889 b18890 b18891 b18892 b18893 b18894 d18766 d18786 d18802 d18822 d17926 d18855 f18765
                    omega
                  have d18895 : (x 7 8).toNat = 0 := by
                    have r18896 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18897 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
                    have e18898 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
                    have e18899 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
                    have e18900 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
                    have e18901 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
                    have e18902 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
                    have b18903 := hb (x 0 7)
                    have b18904 := hb (x 1 6)
                    have b18905 := hb (x 2 5)
                    have b18906 := hb (x 3 4)
                    have b18907 := hb (x 4 11)
                    have b18908 := hb (x 5 10)
                    have b18909 := hb (x 6 9)
                    have b18910 := hb (x 7 8)
                    clear * - r18896 e18897 e18898 e18899 e18900 e18901 e18902 b18903 b18904 b18905 b18906 b18907 b18908 b18909 b18910 d18851 d17974 g26 f17563
                    omega
                  have d18911 : (x 7 1 && x 7 8).toNat = 0 := by
                    have r18912 := hand2 (x 7 1) (x 7 8)
                    have b18913 := hb (x 7 8)
                    have b18914 := hb (x 7 1 && x 7 8)
                    clear * - r18912 b18913 b18914 d18895
                    omega
                  have d18915 : (x 6 9).toNat = 0 := by
                    have r18916 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18917 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
                    have e18918 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
                    have e18919 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
                    have e18920 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
                    have e18921 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
                    have e18922 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
                    have b18923 := hb (x 0 7)
                    have b18924 := hb (x 1 6)
                    have b18925 := hb (x 2 5)
                    have b18926 := hb (x 3 4)
                    have b18927 := hb (x 4 11)
                    have b18928 := hb (x 5 10)
                    have b18929 := hb (x 6 9)
                    have b18930 := hb (x 7 8)
                    clear * - r18916 e18917 e18918 e18919 e18920 e18921 e18922 b18923 b18924 b18925 b18926 b18927 b18928 b18929 b18930 d18895 d18851 d17974 g26 f17563
                    omega
                  have d18931 : (x 6 2 && x 6 9).toNat = 0 := by
                    have r18932 := hand2 (x 6 2) (x 6 9)
                    have b18933 := hb (x 6 9)
                    have b18934 := hb (x 6 2 && x 6 9)
                    clear * - r18932 b18933 b18934 d18915
                    omega
                  have d18935 : (x 5 10).toNat = 0 := by
                    have r18936 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18937 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
                    have e18938 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
                    have e18939 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
                    have e18940 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
                    have e18941 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
                    have e18942 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
                    have b18943 := hb (x 0 7)
                    have b18944 := hb (x 1 6)
                    have b18945 := hb (x 2 5)
                    have b18946 := hb (x 3 4)
                    have b18947 := hb (x 4 11)
                    have b18948 := hb (x 5 10)
                    have b18949 := hb (x 6 9)
                    have b18950 := hb (x 7 8)
                    clear * - r18936 e18937 e18938 e18939 e18940 e18941 e18942 b18943 b18944 b18945 b18946 b18947 b18948 b18949 b18950 d18895 d18915 d18851 d17974 g26 f17563
                    omega
                  have d18951 : (x 5 3 && x 5 10).toNat = 0 := by
                    have r18952 := hand2 (x 5 3) (x 5 10)
                    have b18953 := hb (x 5 10)
                    have b18954 := hb (x 5 3 && x 5 10)
                    clear * - r18952 b18953 b18954 d18935
                    omega
                  have d18955 : (x 4 11).toNat = 0 := by
                    have r18956 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18957 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
                    have e18958 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
                    have e18959 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
                    have e18960 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
                    have e18961 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
                    have e18962 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
                    have b18963 := hb (x 0 7)
                    have b18964 := hb (x 1 6)
                    have b18965 := hb (x 2 5)
                    have b18966 := hb (x 3 4)
                    have b18967 := hb (x 4 11)
                    have b18968 := hb (x 5 10)
                    have b18969 := hb (x 6 9)
                    have b18970 := hb (x 7 8)
                    clear * - r18956 e18957 e18958 e18959 e18960 e18961 e18962 b18963 b18964 b18965 b18966 b18967 b18968 b18969 b18970 d18895 d18915 d18935 d18851 d17974 g26 f17563
                    omega
                  have d18971 : (x 8 7).toNat = 1 := by
                    have r18972 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := by have q := hcov7 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b18973 := hb (x 0 8)
                    have b18974 := hb (x 8 7)
                    have b18975 := hb (x 7 1 && x 7 8)
                    have b18976 := hb (x 6 2 && x 6 9)
                    have b18977 := hb (x 5 3 && x 5 10)
                    have b18978 := hb (x 4 4 && x 4 11)
                    have b18979 := hb (x 3 5 && x 3 12)
                    have b18980 := hb (x 2 6 && x 2 13)
                    have b18981 := hb (x 1 7 && x 1 14)
                    clear * - r18972 b18973 b18974 b18975 b18976 b18977 b18978 b18979 b18980 b18981 d18911 d18931 d18951 d17934 d18875 d17970 g54 g18
                    omega
                  have d18982 : (x 15 8).toNat = 0 := by
                    have r18983 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18984 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                    have e18985 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                    have e18986 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                    have e18987 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                    have e18988 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                    have e18989 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                    have b18990 := hb (x 8 7)
                    have b18991 := hb (x 9 6)
                    have b18992 := hb (x 10 5)
                    have b18993 := hb (x 11 4)
                    have b18994 := hb (x 12 11)
                    have b18995 := hb (x 13 10)
                    have b18996 := hb (x 14 9)
                    have b18997 := hb (x 15 8)
                    clear * - r18983 e18984 e18985 e18986 e18987 e18988 e18989 b18990 b18991 b18992 b18993 b18994 b18995 b18996 b18997 d18971
                    omega
                  have d18998 : (x 14 9).toNat = 0 := by
                    have r18999 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19000 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                    have e19001 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                    have e19002 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                    have e19003 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                    have e19004 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                    have e19005 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                    have b19006 := hb (x 8 7)
                    have b19007 := hb (x 9 6)
                    have b19008 := hb (x 10 5)
                    have b19009 := hb (x 11 4)
                    have b19010 := hb (x 12 11)
                    have b19011 := hb (x 13 10)
                    have b19012 := hb (x 14 9)
                    have b19013 := hb (x 15 8)
                    clear * - r18999 e19000 e19001 e19002 e19003 e19004 e19005 b19006 b19007 b19008 b19009 b19010 b19011 b19012 b19013 d18982 d18971
                    omega
                  have d19014 : (x 13 10).toNat = 0 := by
                    have r19015 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19016 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                    have e19017 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                    have e19018 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                    have e19019 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                    have e19020 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                    have e19021 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                    have b19022 := hb (x 8 7)
                    have b19023 := hb (x 9 6)
                    have b19024 := hb (x 10 5)
                    have b19025 := hb (x 11 4)
                    have b19026 := hb (x 12 11)
                    have b19027 := hb (x 13 10)
                    have b19028 := hb (x 14 9)
                    have b19029 := hb (x 15 8)
                    clear * - r19015 e19016 e19017 e19018 e19019 e19020 e19021 b19022 b19023 b19024 b19025 b19026 b19027 b19028 b19029 d18982 d18998 d18971
                    omega
                  have d19030 : (x 13 1 && x 13 10).toNat = 0 := by
                    have r19031 := hand2 (x 13 1) (x 13 10)
                    have b19032 := hb (x 13 10)
                    have b19033 := hb (x 13 1 && x 13 10)
                    clear * - r19031 b19032 b19033 d19014
                    omega
                  have d19034 : (x 12 11).toNat = 0 := by
                    have r19035 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19036 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                    have e19037 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                    have e19038 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                    have e19039 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                    have e19040 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                    have e19041 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                    have b19042 := hb (x 8 7)
                    have b19043 := hb (x 9 6)
                    have b19044 := hb (x 10 5)
                    have b19045 := hb (x 11 4)
                    have b19046 := hb (x 12 11)
                    have b19047 := hb (x 13 10)
                    have b19048 := hb (x 14 9)
                    have b19049 := hb (x 15 8)
                    clear * - r19035 e19036 e19037 e19038 e19039 e19040 e19041 b19042 b19043 b19044 b19045 b19046 b19047 b19048 b19049 d18982 d18998 d19014 d18971
                    omega
                  have d19050 : (x 12 1 && x 12 11).toNat = 0 := by
                    have r19051 := hand2 (x 12 1) (x 12 11)
                    have b19052 := hb (x 12 11)
                    have b19053 := hb (x 12 1 && x 12 11)
                    clear * - r19051 b19052 b19053 d19034
                    omega
                  have d19054 : (x 12 2 && x 12 11).toNat = 0 := by
                    have r19055 := hand2 (x 12 2) (x 12 11)
                    have b19056 := hb (x 12 11)
                    have b19057 := hb (x 12 2 && x 12 11)
                    clear * - r19055 b19056 b19057 d19034
                    omega
                  have d19058 : (x 11 4).toNat = 0 := by
                    have r19059 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19060 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                    have e19061 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                    have e19062 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                    have e19063 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                    have e19064 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                    have e19065 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                    have b19066 := hb (x 8 7)
                    have b19067 := hb (x 9 6)
                    have b19068 := hb (x 10 5)
                    have b19069 := hb (x 11 4)
                    have b19070 := hb (x 12 11)
                    have b19071 := hb (x 13 10)
                    have b19072 := hb (x 14 9)
                    have b19073 := hb (x 15 8)
                    clear * - r19059 e19060 e19061 e19062 e19063 e19064 e19065 b19066 b19067 b19068 b19069 b19070 b19071 b19072 b19073 d18982 d18998 d19014 d19034 d18971
                    omega
                  have d19074 : (x 11 4 && x 11 14).toNat = 0 := by
                    have r19075 := hand1 (x 11 4) (x 11 14)
                    have b19076 := hb (x 11 4)
                    have b19077 := hb (x 11 4 && x 11 14)
                    clear * - r19075 b19076 b19077 d19058
                    omega
                  have d19078 : (x 10 5).toNat = 0 := by
                    have r19079 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19080 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                    have e19081 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                    have e19082 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                    have e19083 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                    have e19084 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                    have e19085 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                    have b19086 := hb (x 8 7)
                    have b19087 := hb (x 9 6)
                    have b19088 := hb (x 10 5)
                    have b19089 := hb (x 11 4)
                    have b19090 := hb (x 12 11)
                    have b19091 := hb (x 13 10)
                    have b19092 := hb (x 14 9)
                    have b19093 := hb (x 15 8)
                    clear * - r19079 e19080 e19081 e19082 e19083 e19084 e19085 b19086 b19087 b19088 b19089 b19090 b19091 b19092 b19093 d18982 d18998 d19014 d19034 d19058 d18971
                    omega
                  have d19094 : (x 9 6).toNat = 0 := by
                    have r19095 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19096 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                    have e19097 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                    have e19098 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                    have e19099 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                    have e19100 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                    have e19101 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                    have b19102 := hb (x 8 7)
                    have b19103 := hb (x 9 6)
                    have b19104 := hb (x 10 5)
                    have b19105 := hb (x 11 4)
                    have b19106 := hb (x 12 11)
                    have b19107 := hb (x 13 10)
                    have b19108 := hb (x 14 9)
                    have b19109 := hb (x 15 8)
                    clear * - r19095 e19096 e19097 e19098 e19099 e19100 e19101 b19102 b19103 b19104 b19105 b19106 b19107 b19108 b19109 d18982 d18998 d19014 d19034 d19058 d19078 d18971
                    omega
                  have d19110 : (x (-4) 8 && x (-4) 12).toNat = 1 := by
                    have r19111 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19112 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
                    have e19113 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
                    have b19114 := hb (x (-7) 11)
                    have b19115 := hb (x (-6) 10)
                    have b19116 := hb (x 3 5)
                    have b19117 := hb (x 4 4)
                    have b19118 := hb (x 2 2 && x 2 6)
                    have b19119 := hb (x 1 3 && x 1 7)
                    have b19120 := hb (x 0 4 && x 0 8)
                    have b19121 := hb (x (-1) 5 && x (-1) 9)
                    have b19122 := hb (x (-2) 6 && x (-2) 10)
                    have b19123 := hb (x (-3) 7 && x (-3) 11)
                    have b19124 := hb (x (-4) 8 && x (-4) 12)
                    have b19125 := hb (x (-5) 9 && x (-5) 13)
                    clear * - r19111 e19112 e19113 b19114 b19115 b19116 b19117 b19118 b19119 b19120 b19121 b19122 b19123 b19124 b19125 d17926 d18855 d17946 d17807 g42 g43 g44 g45 g46 g2 g0
                    omega
                  have d19126 : (x (-4) 8).toNat = 1 := by
                    have r19127 := hand1 (x (-4) 8) (x (-4) 12)
                    have b19128 := hb (x (-4) 8)
                    have b19129 := hb (x (-4) 8 && x (-4) 12)
                    clear * - r19127 b19128 b19129 d19110
                    omega
                  have d19130 : (x (-8) 4).toNat = 0 := by
                    have r19131 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19132 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
                    have e19133 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
                    have e19134 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
                    have e19135 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
                    have e19136 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
                    have e19137 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
                    have b19138 := hb (x (-11) 7)
                    have b19139 := hb (x (-10) 6)
                    have b19140 := hb (x (-9) 5)
                    have b19141 := hb (x (-8) 4)
                    have b19142 := hb (x (-7) 11)
                    have b19143 := hb (x (-6) 10)
                    have b19144 := hb (x (-5) 9)
                    have b19145 := hb (x (-4) 8)
                    clear * - r19131 e19132 e19133 e19134 e19135 e19136 e19137 b19138 b19139 b19140 b19141 b19142 b19143 b19144 b19145 d19126 d17733 g2 g0
                    omega
                  have d19146 : (x (-4) 11).toNat = 1 := by
                    have r19147 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b19148 := hb (x (-8) 4)
                    have b19149 := hb (x (-4) 11)
                    have b19150 := hb (x (-5) 1 && x (-5) 12)
                    have b19151 := hb (x (-6) 2 && x (-6) 13)
                    have b19152 := hb (x (-7) 3 && x (-7) 14)
                    clear * - r19147 b19148 b19149 b19150 b19151 b19152 d17729 g82 g83 d19130
                    omega
                  have d19153 : (x (-4) 3).toNat = 1 := by
                    have r19154 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
                    have b19155 := hb (x (-4) 3)
                    have b19156 := hb (x (-4) 11)
                    clear * - r19154 b19155 b19156 d19146
                    omega
                  have d19157 : (x (-1) 12).toNat = 0 := by
                    have r19158 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19159 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                    have e19160 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                    have b19161 := hb (x (-4) 3)
                    have b19162 := hb (x (-3) 2)
                    have b19163 := hb (x (-2) 13)
                    have b19164 := hb (x (-1) 12)
                    clear * - r19158 e19159 e19160 b19161 b19162 b19163 b19164 d17623 d19153
                    omega
                  have d19165 : (x (-2) 13).toNat = 0 := by
                    have r19166 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19167 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                    have e19168 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                    have b19169 := hb (x (-4) 3)
                    have b19170 := hb (x (-3) 2)
                    have b19171 := hb (x (-2) 13)
                    have b19172 := hb (x (-1) 12)
                    clear * - r19166 e19167 e19168 b19169 b19170 b19171 b19172 d19157 d17623 d19153
                    omega
                  have d19173 : (x (-2) 5).toNat = 0 := by
                    have r19174 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
                    have b19175 := hb (x (-2) 5)
                    have b19176 := hb (x (-2) 13)
                    clear * - r19174 b19175 b19176 d19165
                    omega
                  have d19177 : (x (-2) 5 && x (-2) 14).toNat = 0 := by
                    have r19178 := hand1 (x (-2) 5) (x (-2) 14)
                    have b19179 := hb (x (-2) 5)
                    have b19180 := hb (x (-2) 5 && x (-2) 14)
                    clear * - r19178 b19179 b19180 d19173
                    omega
                  have d19181 : (x 3 9).toNat = 1 := by
                    have r19182 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b19183 := hb (x (-3) 6)
                    have b19184 := hb (x 3 9)
                    have b19185 := hb (x 2 1 && x 2 10)
                    have b19186 := hb (x 1 2 && x 1 11)
                    have b19187 := hb (x 0 3 && x 0 12)
                    have b19188 := hb (x (-1) 4 && x (-1) 13)
                    have b19189 := hb (x (-2) 5 && x (-2) 14)
                    clear * - r19182 b19183 b19184 b19185 b19186 b19187 b19188 b19189 d17954 g67 g68 g69 d19177 d17615
                    omega
                  have d19190 : (x 4 8).toNat = 0 := by
                    have r19191 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19192 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
                    have e19193 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
                    have e19194 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
                    have e19195 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
                    have e19196 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
                    have e19197 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
                    have b19198 := hb (x (-3) 7)
                    have b19199 := hb (x (-2) 6)
                    have b19200 := hb (x (-1) 5)
                    have b19201 := hb (x 0 4)
                    have b19202 := hb (x 1 11)
                    have b19203 := hb (x 2 10)
                    have b19204 := hb (x 3 9)
                    have b19205 := hb (x 4 8)
                    clear * - r19191 e19192 e19193 e19194 e19195 e19196 e19197 b19198 b19199 b19200 b19201 b19202 b19203 b19204 b19205 d19181 d17950 d17811 g16 g8
                    omega
                  have d19206 : (x 3 10).toNat = 1 := by
                    have r19207 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b19208 := hb (x (-2) 5)
                    have b19209 := hb (x 3 10)
                    have b19210 := hb (x 2 1 && x 2 11)
                    have b19211 := hb (x 1 2 && x 1 12)
                    have b19212 := hb (x 0 3 && x 0 13)
                    have b19213 := hb (x (-1) 4 && x (-1) 14)
                    clear * - r19207 b19208 b19209 b19210 b19211 b19212 b19213 d17962 g76 g77 d17688 d19173
                    omega
                  have d19214 : (x 5 8).toNat = 0 := by
                    have r19215 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19216 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                    have e19217 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                    have e19218 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                    have e19219 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                    have e19220 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                    have e19221 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                    have b19222 := hb (x (-2) 7)
                    have b19223 := hb (x (-1) 6)
                    have b19224 := hb (x 0 5)
                    have b19225 := hb (x 1 4)
                    have b19226 := hb (x 2 11)
                    have b19227 := hb (x 3 10)
                    have b19228 := hb (x 4 9)
                    have b19229 := hb (x 5 8)
                    clear * - r19215 e19216 e19217 e19218 e19219 e19220 e19221 b19222 b19223 b19224 b19225 b19226 b19227 b19228 b19229 d19206 d18030 g24 g17 d17692
                    omega
                  have d19230 : (x 4 9).toNat = 0 := by
                    have r19231 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19232 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                    have e19233 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                    have e19234 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                    have e19235 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                    have e19236 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                    have e19237 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                    have b19238 := hb (x (-2) 7)
                    have b19239 := hb (x (-1) 6)
                    have b19240 := hb (x 0 5)
                    have b19241 := hb (x 1 4)
                    have b19242 := hb (x 2 11)
                    have b19243 := hb (x 3 10)
                    have b19244 := hb (x 4 9)
                    have b19245 := hb (x 5 8)
                    clear * - r19231 e19232 e19233 e19234 e19235 e19236 e19237 b19238 b19239 b19240 b19241 b19242 b19243 b19244 b19245 d19214 d19206 d18030 g24 g17 d17692
                    omega
                  have d19246 : (x 11 1).toNat = 0 := by
                    have r19247 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b19248 := hb (x (-2) 14)
                    have b19249 := hb (x (-1) 13)
                    have b19250 := hb (x 0 12)
                    have b19251 := hb (x 1 11)
                    have b19252 := hb (x 2 10)
                    have b19253 := hb (x 3 9)
                    have b19254 := hb (x 4 8)
                    have b19255 := hb (x 5 7)
                    have b19256 := hb (x 6 6)
                    have b19257 := hb (x 7 5)
                    have b19258 := hb (x 8 4)
                    have b19259 := hb (x 9 3)
                    have b19260 := hb (x 10 2)
                    have b19261 := hb (x 11 1)
                    clear * - r19247 b19248 b19249 b19250 b19251 b19252 b19253 b19254 b19255 b19256 b19257 b19258 b19259 b19260 b19261 d19190 d19181 d17950 d17811 g20 g12 d17660
                    omega
                  have d19262 : (x 11 1 && x 11 14).toNat = 0 := by
                    have r19263 := hand1 (x 11 1) (x 11 14)
                    have b19264 := hb (x 11 1)
                    have b19265 := hb (x 11 1 && x 11 14)
                    clear * - r19263 b19264 b19265 d19246
                    omega
                  have d19266 : (x 11 1 && x 11 12).toNat = 0 := by
                    have r19267 := hand1 (x 11 1) (x 11 12)
                    have b19268 := hb (x 11 1)
                    have b19269 := hb (x 11 1 && x 11 12)
                    clear * - r19267 b19268 b19269 d19246
                    omega
                  have d19270 : (x 11 13).toNat = 0 := by
                    have r19271 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
                    have b19272 := hb (x 11 1)
                    have b19273 := hb (x 11 13)
                    clear * - r19271 b19272 b19273 d19246
                    omega
                  have d19274 : (x 11 3 && x 11 13).toNat = 0 := by
                    have r19275 := hand2 (x 11 3) (x 11 13)
                    have b19276 := hb (x 11 13)
                    have b19277 := hb (x 11 3 && x 11 13)
                    clear * - r19275 b19276 b19277 d19270
                    omega
                  have d19278 : (x 11 5).toNat = 0 := by
                    have r19279 : (x 11 5).toNat ≤ (x 11 13).toNat := himp _ _ (hp5 11)
                    have b19280 := hb (x 11 5)
                    have b19281 := hb (x 11 13)
                    clear * - r19279 b19280 b19281 d19270
                    omega
                  have d19282 : (x 11 5 && x 11 11).toNat = 0 := by
                    have r19283 := hand1 (x 11 5) (x 11 11)
                    have b19284 := hb (x 11 5)
                    have b19285 := hb (x 11 5 && x 11 11)
                    clear * - r19283 b19284 b19285 d19278
                    omega
                  have d19286 : (x 11 9).toNat = 0 := by
                    have r19287 : (x 11 9).toNat ≤ (x 11 1).toNat := himp _ _ (hp9 11)
                    have b19288 := hb (x 11 1)
                    have b19289 := hb (x 11 9)
                    clear * - r19287 b19288 b19289 d19246
                    omega
                  have d19290 : (x 10 2).toNat = 0 := by
                    have r19291 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b19292 := hb (x (-2) 14)
                    have b19293 := hb (x (-1) 13)
                    have b19294 := hb (x 0 12)
                    have b19295 := hb (x 1 11)
                    have b19296 := hb (x 2 10)
                    have b19297 := hb (x 3 9)
                    have b19298 := hb (x 4 8)
                    have b19299 := hb (x 5 7)
                    have b19300 := hb (x 6 6)
                    have b19301 := hb (x 7 5)
                    have b19302 := hb (x 8 4)
                    have b19303 := hb (x 9 3)
                    have b19304 := hb (x 10 2)
                    have b19305 := hb (x 11 1)
                    clear * - r19291 b19292 b19293 b19294 b19295 b19296 b19297 b19298 b19299 b19300 b19301 b19302 b19303 b19304 b19305 d19246 d19190 d19181 d17950 d17811 g20 g12 d17660
                    omega
                  have d19306 : (x 10 2 && x 10 13).toNat = 0 := by
                    have r19307 := hand1 (x 10 2) (x 10 13)
                    have b19308 := hb (x 10 2)
                    have b19309 := hb (x 10 2 && x 10 13)
                    clear * - r19307 b19308 b19309 d19290
                    omega
                  have d19310 : (x 10 10).toNat = 0 := by
                    have r19311 : (x 10 10).toNat ≤ (x 10 2).toNat := himp _ _ (hp10 10)
                    have b19312 := hb (x 10 2)
                    have b19313 := hb (x 10 10)
                    clear * - r19311 b19312 b19313 d19290
                    omega
                  have d19314 : (x 12 13).toNat = 1 := by
                    have r19315 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b19316 := hb (x 10 2)
                    have b19317 := hb (x 12 13)
                    have b19318 := hb (x 11 1 && x 11 14)
                    clear * - r19315 b19316 b19317 b19318 d19262 d19290
                    omega
                  have d19319 : (x 12 1).toNat = 1 := by
                    have r19320 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
                    have b19321 := hb (x 12 1)
                    have b19322 := hb (x 12 13)
                    clear * - r19320 b19321 b19322 d19314
                    omega
                  have d19323 : (x 13 14).toNat = 0 := by
                    have r19324 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b19325 := hb (x 12 1)
                    have b19326 := hb (x 13 14)
                    clear * - r19324 b19325 b19326 d19319
                    omega
                  have d19327 : (x 13 2).toNat = 0 := by
                    have r19328 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
                    have b19329 := hb (x 13 2)
                    have b19330 := hb (x 13 14)
                    clear * - r19328 b19329 b19330 d19323
                    omega
                  have d19331 : (x 13 2 && x 13 12).toNat = 0 := by
                    have r19332 := hand1 (x 13 2) (x 13 12)
                    have b19333 := hb (x 13 2)
                    have b19334 := hb (x 13 2 && x 13 12)
                    clear * - r19332 b19333 b19334 d19327
                    omega
                  have d19335 : (x 11 2).toNat = 0 := by
                    have r19336 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b19337 := hb (x (-1) 14)
                    have b19338 := hb (x 0 13)
                    have b19339 := hb (x 1 12)
                    have b19340 := hb (x 2 11)
                    have b19341 := hb (x 3 10)
                    have b19342 := hb (x 4 9)
                    have b19343 := hb (x 5 8)
                    have b19344 := hb (x 6 7)
                    have b19345 := hb (x 7 6)
                    have b19346 := hb (x 8 5)
                    have b19347 := hb (x 9 4)
                    have b19348 := hb (x 10 3)
                    have b19349 := hb (x 11 2)
                    have b19350 := hb (x 12 1)
                    clear * - r19336 b19337 b19338 b19339 b19340 b19341 b19342 b19343 b19344 b19345 b19346 b19347 b19348 b19349 b19350 d19319 d19214 d19230 d19206 d18030 g28 g21 d17684
                    omega
                  have d19351 : (x 11 2 && x 11 12).toNat = 0 := by
                    have r19352 := hand1 (x 11 2) (x 11 12)
                    have b19353 := hb (x 11 2)
                    have b19354 := hb (x 11 2 && x 11 12)
                    clear * - r19352 b19353 b19354 d19335
                    omega
                  have d19355 : (x 10 3).toNat = 0 := by
                    have r19356 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b19357 := hb (x (-1) 14)
                    have b19358 := hb (x 0 13)
                    have b19359 := hb (x 1 12)
                    have b19360 := hb (x 2 11)
                    have b19361 := hb (x 3 10)
                    have b19362 := hb (x 4 9)
                    have b19363 := hb (x 5 8)
                    have b19364 := hb (x 6 7)
                    have b19365 := hb (x 7 6)
                    have b19366 := hb (x 8 5)
                    have b19367 := hb (x 9 4)
                    have b19368 := hb (x 10 3)
                    have b19369 := hb (x 11 2)
                    have b19370 := hb (x 12 1)
                    clear * - r19356 b19357 b19358 b19359 b19360 b19361 b19362 b19363 b19364 b19365 b19366 b19367 b19368 b19369 b19370 d19319 d19335 d19214 d19230 d19206 d18030 g28 g21 d17684
                    omega
                  have d19371 : (x 10 3 && x 10 13).toNat = 0 := by
                    have r19372 := hand1 (x 10 3) (x 10 13)
                    have b19373 := hb (x 10 3)
                    have b19374 := hb (x 10 3 && x 10 13)
                    clear * - r19372 b19373 b19374 d19355
                    omega
                  have d19375 : (x 9 4).toNat = 0 := by
                    have r19376 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b19377 := hb (x (-1) 14)
                    have b19378 := hb (x 0 13)
                    have b19379 := hb (x 1 12)
                    have b19380 := hb (x 2 11)
                    have b19381 := hb (x 3 10)
                    have b19382 := hb (x 4 9)
                    have b19383 := hb (x 5 8)
                    have b19384 := hb (x 6 7)
                    have b19385 := hb (x 7 6)
                    have b19386 := hb (x 8 5)
                    have b19387 := hb (x 9 4)
                    have b19388 := hb (x 10 3)
                    have b19389 := hb (x 11 2)
                    have b19390 := hb (x 12 1)
                    clear * - r19376 b19377 b19378 b19379 b19380 b19381 b19382 b19383 b19384 b19385 b19386 b19387 b19388 b19389 b19390 d19319 d19335 d19355 d19214 d19230 d19206 d18030 g28 g21 d17684
                    omega
                  have d19391 : (x 9 4 && x 9 14).toNat = 0 := by
                    have r19392 := hand1 (x 9 4) (x 9 14)
                    have b19393 := hb (x 9 4)
                    have b19394 := hb (x 9 4 && x 9 14)
                    clear * - r19392 b19393 b19394 d19375
                    omega
                  have d19395 : (x 8 5).toNat = 1 := by
                    have r19396 : 1 ≤ (x 13 10).toNat + (x 12 1 && x 12 11).toNat + (x 11 2 && x 11 12).toNat + (x 10 3 && x 10 13).toNat + (x 9 4 && x 9 14).toNat + (x 8 5).toNat := by have q := hcov10 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b19397 := hb (x 8 5)
                    have b19398 := hb (x 13 10)
                    have b19399 := hb (x 12 1 && x 12 11)
                    have b19400 := hb (x 11 2 && x 11 12)
                    have b19401 := hb (x 10 3 && x 10 13)
                    have b19402 := hb (x 9 4 && x 9 14)
                    clear * - r19396 b19397 b19398 b19399 b19400 b19401 b19402 d19014 d19050 d19351 d19371 d19391
                    omega
                  have d19403 : (x 8 13).toNat = 1 := by
                    have r19404 : (x 8 5).toNat ≤ (x 8 13).toNat := himp _ _ (hp5 8)
                    have b19405 := hb (x 8 5)
                    have b19406 := hb (x 8 13)
                    clear * - r19404 b19405 b19406 d19395
                    omega
                  have d19407 : (x 8 1).toNat = 1 := by
                    have r19408 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
                    have b19409 := hb (x 8 1)
                    have b19410 := hb (x 8 13)
                    clear * - r19408 b19409 b19410 d19403
                    omega
                  have d19411 : (x 9 14).toNat = 0 := by
                    have r19412 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b19413 := hb (x 8 1)
                    have b19414 := hb (x 9 14)
                    clear * - r19412 b19413 b19414 d19407
                    omega
                  have d19415 : (x 9 3 && x 9 14).toNat = 0 := by
                    have r19416 := hand2 (x 9 3) (x 9 14)
                    have b19417 := hb (x 9 14)
                    have b19418 := hb (x 9 3 && x 9 14)
                    clear * - r19416 b19417 b19418 d19411
                    omega
                  have d19419 : (x 8 4).toNat = 1 := by
                    have r19420 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b19421 := hb (x 8 4)
                    have b19422 := hb (x 12 11)
                    have b19423 := hb (x 11 1 && x 11 12)
                    have b19424 := hb (x 10 2 && x 10 13)
                    have b19425 := hb (x 9 3 && x 9 14)
                    clear * - r19420 b19421 b19422 b19423 b19424 b19425 d19034 d19266 d19306 d19415
                    omega
                  have d19426 : (x 8 12).toNat = 1 := by
                    have r19427 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
                    have b19428 := hb (x 8 4)
                    have b19429 := hb (x 8 12)
                    clear * - r19427 b19428 b19429 d19419
                    omega
                  have d19430 : (x 7 13).toNat = 0 := by
                    have r19431 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19432 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                    have e19433 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                    have b19434 := hb (x 5 3)
                    have b19435 := hb (x 6 2)
                    have b19436 := hb (x 7 13)
                    have b19437 := hb (x 8 12)
                    clear * - r19431 e19432 e19433 b19434 b19435 b19436 b19437 d19426
                    omega
                  have d19438 : (x 7 3 && x 7 13).toNat = 0 := by
                    have r19439 := hand2 (x 7 3) (x 7 13)
                    have b19440 := hb (x 7 13)
                    have b19441 := hb (x 7 3 && x 7 13)
                    clear * - r19439 b19440 b19441 d19430
                    omega
                  have d19442 : (x 7 5).toNat = 0 := by
                    have r19443 : (x 7 5).toNat ≤ (x 7 13).toNat := himp _ _ (hp5 7)
                    have b19444 := hb (x 7 5)
                    have b19445 := hb (x 7 13)
                    clear * - r19443 b19444 b19445 d19430
                    omega
                  have d19446 : (x 6 2).toNat = 0 := by
                    have r19447 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19448 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                    have e19449 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                    have b19450 := hb (x 5 3)
                    have b19451 := hb (x 6 2)
                    have b19452 := hb (x 7 13)
                    have b19453 := hb (x 8 12)
                    clear * - r19447 e19448 e19449 b19450 b19451 b19452 b19453 d19426 d19430
                    omega
                  have d19454 : (x 6 2 && x 6 13).toNat = 0 := by
                    have r19455 := hand1 (x 6 2) (x 6 13)
                    have b19456 := hb (x 6 2)
                    have b19457 := hb (x 6 2 && x 6 13)
                    clear * - r19455 b19456 b19457 d19446
                    omega
                  have d19458 : (x 6 2 && x 6 11).toNat = 0 := by
                    have r19459 := hand1 (x 6 2) (x 6 11)
                    have b19460 := hb (x 6 2)
                    have b19461 := hb (x 6 2 && x 6 11)
                    clear * - r19459 b19460 b19461 d19446
                    omega
                  have d19462 : (x 5 3).toNat = 0 := by
                    have r19463 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19464 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                    have e19465 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                    have b19466 := hb (x 5 3)
                    have b19467 := hb (x 6 2)
                    have b19468 := hb (x 7 13)
                    have b19469 := hb (x 8 12)
                    clear * - r19463 e19464 e19465 b19466 b19467 b19468 b19469 d19426 d19430 d19446
                    omega
                  have d19470 : (x 5 3 && x 5 14).toNat = 0 := by
                    have r19471 := hand1 (x 5 3) (x 5 14)
                    have b19472 := hb (x 5 3)
                    have b19473 := hb (x 5 3 && x 5 14)
                    clear * - r19471 b19472 b19473 d19462
                    omega
                  have d19474 : (x 12 8).toNat = 0 := by
                    have r19475 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19476 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
                    have e19477 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
                    have e19478 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
                    have e19479 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
                    have e19480 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
                    have e19481 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
                    have b19482 := hb (x 5 7)
                    have b19483 := hb (x 6 6)
                    have b19484 := hb (x 7 5)
                    have b19485 := hb (x 8 4)
                    have b19486 := hb (x 9 11)
                    have b19487 := hb (x 10 10)
                    have b19488 := hb (x 11 9)
                    have b19489 := hb (x 12 8)
                    clear * - r19475 e19476 e19477 e19478 e19479 e19480 e19481 b19482 b19483 b19484 b19485 b19486 b19487 b19488 b19489 d19286 d19310 d19419 d19442
                    omega
                  have d19490 : (x 9 11).toNat = 0 := by
                    have r19491 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19492 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
                    have e19493 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
                    have e19494 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
                    have e19495 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
                    have e19496 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
                    have e19497 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
                    have b19498 := hb (x 5 7)
                    have b19499 := hb (x 6 6)
                    have b19500 := hb (x 7 5)
                    have b19501 := hb (x 8 4)
                    have b19502 := hb (x 9 11)
                    have b19503 := hb (x 10 10)
                    have b19504 := hb (x 11 9)
                    have b19505 := hb (x 12 8)
                    clear * - r19491 e19492 e19493 e19494 e19495 e19496 e19497 b19498 b19499 b19500 b19501 b19502 b19503 b19504 b19505 d19474 d19286 d19310 d19419 d19442
                    omega
                  have d19506 : (x 9 1 && x 9 11).toNat = 0 := by
                    have r19507 := hand2 (x 9 1) (x 9 11)
                    have b19508 := hb (x 9 11)
                    have b19509 := hb (x 9 1 && x 9 11)
                    clear * - r19507 b19508 b19509 d19490
                    omega
                  have d19510 : (x 8 2 && x 8 12).toNat = 1 := by
                    have r19511 : 1 ≤ (x 10 10).toNat + (x 9 1 && x 9 11).toNat + (x 8 2 && x 8 12).toNat + (x 7 3 && x 7 13).toNat + (x 6 4 && x 6 14).toNat + (x 5 5).toNat := by have q := hcov10 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b19512 := hb (x 5 5)
                    have b19513 := hb (x 10 10)
                    have b19514 := hb (x 9 1 && x 9 11)
                    have b19515 := hb (x 8 2 && x 8 12)
                    have b19516 := hb (x 7 3 && x 7 13)
                    have b19517 := hb (x 6 4 && x 6 14)
                    clear * - r19511 b19512 b19513 b19514 b19515 b19516 b19517 d19310 d19506 d19438 d17840 d17852
                    omega
                  have d19518 : (x 8 2).toNat = 1 := by
                    have r19519 := hand1 (x 8 2) (x 8 12)
                    have b19520 := hb (x 8 2)
                    have b19521 := hb (x 8 2 && x 8 12)
                    clear * - r19519 b19520 b19521 d19510
                    omega
                  have d19522 : (x 8 14).toNat = 1 := by
                    have r19523 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
                    have b19524 := hb (x 8 2)
                    have b19525 := hb (x 8 14)
                    clear * - r19523 b19524 b19525 d19518
                    omega
                  have d19526 : (x 7 1).toNat = 0 := by
                    have r19527 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b19528 := hb (x 7 1)
                    have b19529 := hb (x 8 14)
                    clear * - r19527 b19528 b19529 d19522
                    omega
                  have d19530 : (x 7 1 && x 7 12).toNat = 0 := by
                    have r19531 := hand1 (x 7 1) (x 7 12)
                    have b19532 := hb (x 7 1)
                    have b19533 := hb (x 7 1 && x 7 12)
                    clear * - r19531 b19532 b19533 d19526
                    omega
                  have d19534 : (x 8 11).toNat = 1 := by
                    have r19535 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b19536 := hb (x 4 4)
                    have b19537 := hb (x 8 11)
                    have b19538 := hb (x 7 1 && x 7 12)
                    have b19539 := hb (x 6 2 && x 6 13)
                    have b19540 := hb (x 5 3 && x 5 14)
                    clear * - r19535 b19536 b19537 b19538 b19539 b19540 d19530 d19454 d19470 d17926
                    omega
                  have d19541 : (x 8 3).toNat = 1 := by
                    have r19542 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
                    have b19543 := hb (x 8 3)
                    have b19544 := hb (x 8 11)
                    clear * - r19542 b19543 b19544 d19534
                    omega
                  have d19545 : (x 11 12).toNat = 0 := by
                    have r19546 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19547 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                    have e19548 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                    have b19549 := hb (x 8 3)
                    have b19550 := hb (x 9 2)
                    have b19551 := hb (x 10 13)
                    have b19552 := hb (x 11 12)
                    clear * - r19546 e19547 e19548 b19549 b19550 b19551 b19552 d19541
                    omega
                  have d19553 : (x 11 3 && x 11 12).toNat = 0 := by
                    have r19554 := hand2 (x 11 3) (x 11 12)
                    have b19555 := hb (x 11 12)
                    have b19556 := hb (x 11 3 && x 11 12)
                    clear * - r19554 b19555 b19556 d19545
                    omega
                  have d19557 : (x 10 13).toNat = 0 := by
                    have r19558 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19559 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                    have e19560 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                    have b19561 := hb (x 8 3)
                    have b19562 := hb (x 9 2)
                    have b19563 := hb (x 10 13)
                    have b19564 := hb (x 11 12)
                    clear * - r19558 e19559 e19560 b19561 b19562 b19563 b19564 d19545 d19541
                    omega
                  have d19565 : (x 10 4 && x 10 13).toNat = 0 := by
                    have r19566 := hand2 (x 10 4) (x 10 13)
                    have b19567 := hb (x 10 13)
                    have b19568 := hb (x 10 4 && x 10 13)
                    clear * - r19566 b19567 b19568 d19557
                    omega
                  have d19569 : (x 9 2).toNat = 0 := by
                    have r19570 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19571 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                    have e19572 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                    have b19573 := hb (x 8 3)
                    have b19574 := hb (x 9 2)
                    have b19575 := hb (x 10 13)
                    have b19576 := hb (x 11 12)
                    clear * - r19570 e19571 e19572 b19573 b19574 b19575 b19576 d19545 d19557 d19541
                    omega
                  have d19577 : (x 10 1 && x 10 14).toNat = 1 := by
                    have r19578 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b19579 := hb (x 9 2)
                    have b19580 := hb (x 11 13)
                    have b19581 := hb (x 10 1 && x 10 14)
                    clear * - r19578 b19579 b19580 b19581 d19270 d19569
                    omega
                  have d19582 : (x 10 14).toNat = 1 := by
                    have r19583 := hand2 (x 10 1) (x 10 14)
                    have b19584 := hb (x 10 14)
                    have b19585 := hb (x 10 1 && x 10 14)
                    clear * - r19583 b19584 b19585 d19577
                    omega
                  have d19586 : (x 9 1).toNat = 0 := by
                    have r19587 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b19588 := hb (x 9 1)
                    have b19589 := hb (x 10 14)
                    clear * - r19587 b19588 b19589 d19582
                    omega
                  have d19590 : (x 9 13).toNat = 0 := by
                    have r19591 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
                    have b19592 := hb (x 9 1)
                    have b19593 := hb (x 9 13)
                    clear * - r19591 b19592 b19593 d19586
                    omega
                  have d19594 : (x 9 7 && x 9 13).toNat = 0 := by
                    have r19595 := hand2 (x 9 7) (x 9 13)
                    have b19596 := hb (x 9 13)
                    have b19597 := hb (x 9 7 && x 9 13)
                    clear * - r19595 b19596 b19597 d19590
                    omega
                  have d19598 : (x 9 5).toNat = 0 := by
                    have r19599 : (x 9 5).toNat ≤ (x 9 13).toNat := himp _ _ (hp5 9)
                    have b19600 := hb (x 9 5)
                    have b19601 := hb (x 9 13)
                    clear * - r19599 b19600 b19601 d19590
                    omega
                  have d19602 : (x 9 5 && x 9 14).toNat = 0 := by
                    have r19603 := hand1 (x 9 5) (x 9 14)
                    have b19604 := hb (x 9 5)
                    have b19605 := hb (x 9 5 && x 9 14)
                    clear * - r19603 b19604 b19605 d19598
                    omega
                  have d19606 : (x 8 6).toNat = 1 := by
                    have r19607 : 1 ≤ (x 14 9).toNat + (x 13 1 && x 13 10).toNat + (x 12 2 && x 12 11).toNat + (x 11 3 && x 11 12).toNat + (x 10 4 && x 10 13).toNat + (x 9 5 && x 9 14).toNat + (x 8 6).toNat := by have q := hcov9 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b19608 := hb (x 8 6)
                    have b19609 := hb (x 14 9)
                    have b19610 := hb (x 13 1 && x 13 10)
                    have b19611 := hb (x 12 2 && x 12 11)
                    have b19612 := hb (x 11 3 && x 11 12)
                    have b19613 := hb (x 10 4 && x 10 13)
                    have b19614 := hb (x 9 5 && x 9 14)
                    clear * - r19607 b19608 b19609 b19610 b19611 b19612 b19613 b19614 d18998 d19030 d19054 d19553 d19565 d19602
                    omega
                  have d19615 : (x 14 8).toNat = 0 := by
                    have r19616 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19617 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                    have e19618 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                    have e19619 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                    have e19620 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                    have e19621 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                    have e19622 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                    have b19623 := hb (x 7 7)
                    have b19624 := hb (x 8 6)
                    have b19625 := hb (x 9 5)
                    have b19626 := hb (x 10 4)
                    have b19627 := hb (x 11 11)
                    have b19628 := hb (x 12 10)
                    have b19629 := hb (x 13 9)
                    have b19630 := hb (x 14 8)
                    clear * - r19616 e19617 e19618 e19619 e19620 e19621 e19622 b19623 b19624 b19625 b19626 b19627 b19628 b19629 b19630 d19598 d19606
                    omega
                  have d19631 : (x 14 2 && x 14 8).toNat = 0 := by
                    have r19632 := hand2 (x 14 2) (x 14 8)
                    have b19633 := hb (x 14 8)
                    have b19634 := hb (x 14 2 && x 14 8)
                    clear * - r19632 b19633 b19634 d19615
                    omega
                  have d19635 : (x 13 9).toNat = 0 := by
                    have r19636 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19637 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                    have e19638 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                    have e19639 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                    have e19640 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                    have e19641 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                    have e19642 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                    have b19643 := hb (x 7 7)
                    have b19644 := hb (x 8 6)
                    have b19645 := hb (x 9 5)
                    have b19646 := hb (x 10 4)
                    have b19647 := hb (x 11 11)
                    have b19648 := hb (x 12 10)
                    have b19649 := hb (x 13 9)
                    have b19650 := hb (x 14 8)
                    clear * - r19636 e19637 e19638 e19639 e19640 e19641 e19642 b19643 b19644 b19645 b19646 b19647 b19648 b19649 b19650 d19615 d19598 d19606
                    omega
                  have d19651 : (x 13 3 && x 13 9).toNat = 0 := by
                    have r19652 := hand2 (x 13 3) (x 13 9)
                    have b19653 := hb (x 13 9)
                    have b19654 := hb (x 13 3 && x 13 9)
                    clear * - r19652 b19653 b19654 d19635
                    omega
                  have d19655 : (x 12 10).toNat = 0 := by
                    have r19656 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19657 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                    have e19658 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                    have e19659 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                    have e19660 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                    have e19661 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                    have e19662 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                    have b19663 := hb (x 7 7)
                    have b19664 := hb (x 8 6)
                    have b19665 := hb (x 9 5)
                    have b19666 := hb (x 10 4)
                    have b19667 := hb (x 11 11)
                    have b19668 := hb (x 12 10)
                    have b19669 := hb (x 13 9)
                    have b19670 := hb (x 14 8)
                    clear * - r19656 e19657 e19658 e19659 e19660 e19661 e19662 b19663 b19664 b19665 b19666 b19667 b19668 b19669 b19670 d19615 d19635 d19598 d19606
                    omega
                  have d19671 : (x 12 4 && x 12 10).toNat = 0 := by
                    have r19672 := hand2 (x 12 4) (x 12 10)
                    have b19673 := hb (x 12 10)
                    have b19674 := hb (x 12 4 && x 12 10)
                    clear * - r19672 b19673 b19674 d19655
                    omega
                  have d19675 : (x 11 11).toNat = 0 := by
                    have r19676 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19677 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                    have e19678 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                    have e19679 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                    have e19680 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                    have e19681 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                    have e19682 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                    have b19683 := hb (x 7 7)
                    have b19684 := hb (x 8 6)
                    have b19685 := hb (x 9 5)
                    have b19686 := hb (x 10 4)
                    have b19687 := hb (x 11 11)
                    have b19688 := hb (x 12 10)
                    have b19689 := hb (x 13 9)
                    have b19690 := hb (x 14 8)
                    clear * - r19676 e19677 e19678 e19679 e19680 e19681 e19682 b19683 b19684 b19685 b19686 b19687 b19688 b19689 b19690 d19615 d19635 d19655 d19598 d19606
                    omega
                  have d19691 : (x 10 4).toNat = 0 := by
                    have r19692 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19693 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                    have e19694 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                    have e19695 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                    have e19696 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                    have e19697 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                    have e19698 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                    have b19699 := hb (x 7 7)
                    have b19700 := hb (x 8 6)
                    have b19701 := hb (x 9 5)
                    have b19702 := hb (x 10 4)
                    have b19703 := hb (x 11 11)
                    have b19704 := hb (x 12 10)
                    have b19705 := hb (x 13 9)
                    have b19706 := hb (x 14 8)
                    clear * - r19692 e19693 e19694 e19695 e19696 e19697 e19698 b19699 b19700 b19701 b19702 b19703 b19704 b19705 b19706 d19615 d19635 d19655 d19675 d19598 d19606
                    omega
                  have d19707 : (x 10 4 && x 10 14).toNat = 0 := by
                    have r19708 := hand1 (x 10 4) (x 10 14)
                    have b19709 := hb (x 10 4)
                    have b19710 := hb (x 10 4 && x 10 14)
                    clear * - r19708 b19709 b19710 d19691
                    omega
                  have d19711 : (x 7 7).toNat = 0 := by
                    have r19712 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19713 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                    have e19714 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                    have e19715 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                    have e19716 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                    have e19717 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                    have e19718 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                    have b19719 := hb (x 7 7)
                    have b19720 := hb (x 8 6)
                    have b19721 := hb (x 9 5)
                    have b19722 := hb (x 10 4)
                    have b19723 := hb (x 11 11)
                    have b19724 := hb (x 12 10)
                    have b19725 := hb (x 13 9)
                    have b19726 := hb (x 14 8)
                    clear * - r19712 e19713 e19714 e19715 e19716 e19717 e19718 b19719 b19720 b19721 b19722 b19723 b19724 b19725 b19726 d19615 d19635 d19655 d19675 d19691 d19598 d19606
                    omega
                  have d19727 : (x 13 1).toNat = 0 := by
                    have r19728 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b19729 := hb (x 0 14)
                    have b19730 := hb (x 1 13)
                    have b19731 := hb (x 2 12)
                    have b19732 := hb (x 3 11)
                    have b19733 := hb (x 4 10)
                    have b19734 := hb (x 5 9)
                    have b19735 := hb (x 6 8)
                    have b19736 := hb (x 7 7)
                    have b19737 := hb (x 8 6)
                    have b19738 := hb (x 9 5)
                    have b19739 := hb (x 10 4)
                    have b19740 := hb (x 11 3)
                    have b19741 := hb (x 12 2)
                    have b19742 := hb (x 13 1)
                    clear * - r19728 b19729 b19730 b19731 b19732 b19733 b19734 b19735 b19736 b19737 b19738 b19739 b19740 b19741 b19742 d19691 d19598 d19606 d19711 d18034 d18054 d17864 d17817 g32 g29 g22
                    omega
                  have d19743 : (x 13 1 && x 13 11).toNat = 0 := by
                    have r19744 := hand1 (x 13 1) (x 13 11)
                    have b19745 := hb (x 13 1)
                    have b19746 := hb (x 13 1 && x 13 11)
                    clear * - r19744 b19745 b19746 d19727
                    omega
                  have d19747 : (x 12 2).toNat = 0 := by
                    have r19748 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b19749 := hb (x 0 14)
                    have b19750 := hb (x 1 13)
                    have b19751 := hb (x 2 12)
                    have b19752 := hb (x 3 11)
                    have b19753 := hb (x 4 10)
                    have b19754 := hb (x 5 9)
                    have b19755 := hb (x 6 8)
                    have b19756 := hb (x 7 7)
                    have b19757 := hb (x 8 6)
                    have b19758 := hb (x 9 5)
                    have b19759 := hb (x 10 4)
                    have b19760 := hb (x 11 3)
                    have b19761 := hb (x 12 2)
                    have b19762 := hb (x 13 1)
                    clear * - r19748 b19749 b19750 b19751 b19752 b19753 b19754 b19755 b19756 b19757 b19758 b19759 b19760 b19761 b19762 d19727 d19691 d19598 d19606 d19711 d18034 d18054 d17864 d17817 g32 g29 g22
                    omega
                  have d19763 : (x 12 2 && x 12 12).toNat = 0 := by
                    have r19764 := hand1 (x 12 2) (x 12 12)
                    have b19765 := hb (x 12 2)
                    have b19766 := hb (x 12 2 && x 12 12)
                    clear * - r19764 b19765 b19766 d19747
                    omega
                  have d19767 : (x 14 10).toNat = 1 := by
                    have r19768 : 1 ≤ (x 14 10).toNat + (x 13 1 && x 13 11).toNat + (x 12 2 && x 12 12).toNat + (x 11 3 && x 11 13).toNat + (x 10 4 && x 10 14).toNat + (x 9 5).toNat := by have q := hcov10 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b19769 := hb (x 9 5)
                    have b19770 := hb (x 14 10)
                    have b19771 := hb (x 13 1 && x 13 11)
                    have b19772 := hb (x 12 2 && x 12 12)
                    have b19773 := hb (x 11 3 && x 11 13)
                    have b19774 := hb (x 10 4 && x 10 14)
                    clear * - r19768 b19769 b19770 b19771 b19772 b19773 b19774 d19743 d19763 d19274 d19707 d19598
                    omega
                  have d19775 : (x 14 2).toNat = 1 := by
                    have r19776 : (x 14 10).toNat ≤ (x 14 2).toNat := himp _ _ (hp10 14)
                    have b19777 := hb (x 14 2)
                    have b19778 := hb (x 14 10)
                    clear * - r19776 b19777 b19778 d19767
                    omega
                  have d19779 : (x 16 12).toNat = 0 := by
                    have r19780 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19781 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                    have e19782 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                    have b19783 := hb (x 13 3)
                    have b19784 := hb (x 14 2)
                    have b19785 := hb (x 15 13)
                    have b19786 := hb (x 16 12)
                    clear * - r19780 e19781 e19782 b19783 b19784 b19785 b19786 d19775
                    omega
                  have d19787 : (x 15 13).toNat = 0 := by
                    have r19788 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19789 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                    have e19790 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                    have b19791 := hb (x 13 3)
                    have b19792 := hb (x 14 2)
                    have b19793 := hb (x 15 13)
                    have b19794 := hb (x 16 12)
                    clear * - r19788 e19789 e19790 b19791 b19792 b19793 b19794 d19779 d19775
                    omega
                  have d19795 : (x 14 1 && x 14 14).toNat = 1 := by
                    have r19796 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b19797 := hb (x 13 2)
                    have b19798 := hb (x 15 13)
                    have b19799 := hb (x 14 1 && x 14 14)
                    clear * - r19796 b19797 b19798 b19799 d19787 d19327
                    omega
                  have d19800 : (x 14 1).toNat = 1 := by
                    have r19801 := hand1 (x 14 1) (x 14 14)
                    have b19802 := hb (x 14 1)
                    have b19803 := hb (x 14 1 && x 14 14)
                    clear * - r19801 b19802 b19803 d19795
                    omega
                  have d19804 : (x 15 14).toNat = 0 := by
                    have r19805 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b19806 := hb (x 14 1)
                    have b19807 := hb (x 15 14)
                    clear * - r19805 b19806 b19807 d19800
                    omega
                  have d19808 : (x 15 6).toNat = 0 := by
                    have r19809 : (x 15 6).toNat ≤ (x 15 14).toNat := himp _ _ (hp6 15)
                    have b19810 := hb (x 15 6)
                    have b19811 := hb (x 15 14)
                    clear * - r19809 b19810 b19811 d19804
                    omega
                  have d19812 : (x 15 2).toNat = 0 := by
                    have r19813 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
                    have b19814 := hb (x 15 2)
                    have b19815 := hb (x 15 14)
                    clear * - r19813 b19814 b19815 d19804
                    omega
                  have d19816 : (x 15 10).toNat = 0 := by
                    have r19817 : (x 15 10).toNat ≤ (x 15 2).toNat := himp _ _ (hp10 15)
                    have b19818 := hb (x 15 2)
                    have b19819 := hb (x 15 10)
                    clear * - r19817 b19818 b19819 d19812
                    omega
                  have d19820 : (x 12 3).toNat = 0 := by
                    have r19821 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b19822 := hb (x 1 14)
                    have b19823 := hb (x 2 13)
                    have b19824 := hb (x 3 12)
                    have b19825 := hb (x 4 11)
                    have b19826 := hb (x 5 10)
                    have b19827 := hb (x 6 9)
                    have b19828 := hb (x 7 8)
                    have b19829 := hb (x 8 7)
                    have b19830 := hb (x 9 6)
                    have b19831 := hb (x 10 5)
                    have b19832 := hb (x 11 4)
                    have b19833 := hb (x 12 3)
                    have b19834 := hb (x 13 2)
                    have b19835 := hb (x 14 1)
                    clear * - r19821 b19822 b19823 b19824 b19825 b19826 b19827 b19828 b19829 b19830 b19831 b19832 b19833 b19834 b19835 d19800 d19327 d19058 d19078 d19094 d18971 d18895 d18915 d18935 d18955 d17982 d17966 g30
                    omega
                  have d19836 : (x 12 3 && x 12 13).toNat = 0 := by
                    have r19837 := hand1 (x 12 3) (x 12 13)
                    have b19838 := hb (x 12 3)
                    have b19839 := hb (x 12 3 && x 12 13)
                    clear * - r19837 b19838 b19839 d19820
                    omega
                  have d19840 : (x 14 1 && x 14 11).toNat = 1 := by
                    have r19841 : 1 ≤ (x 15 10).toNat + (x 14 1 && x 14 11).toNat + (x 13 2 && x 13 12).toNat + (x 12 3 && x 12 13).toNat + (x 11 4 && x 11 14).toNat + (x 10 5).toNat := by have q := hcov10 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b19842 := hb (x 10 5)
                    have b19843 := hb (x 15 10)
                    have b19844 := hb (x 14 1 && x 14 11)
                    have b19845 := hb (x 13 2 && x 13 12)
                    have b19846 := hb (x 12 3 && x 12 13)
                    have b19847 := hb (x 11 4 && x 11 14)
                    clear * - r19841 b19842 b19843 b19844 b19845 b19846 b19847 d19816 d19331 d19836 d19074 d19078
                    omega
                  have d19848 : (x 14 11).toNat = 1 := by
                    have r19849 := hand2 (x 14 1) (x 14 11)
                    have b19850 := hb (x 14 11)
                    have b19851 := hb (x 14 1 && x 14 11)
                    clear * - r19849 b19850 b19851 d19840
                    omega
                  have d19852 : (x 14 3).toNat = 1 := by
                    have r19853 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
                    have b19854 := hb (x 14 3)
                    have b19855 := hb (x 14 11)
                    clear * - r19853 b19854 b19855 d19848
                    omega
                  have d19856 : (x 17 12).toNat = 0 := by
                    have r19857 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19858 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                    have e19859 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                    have b19860 := hb (x 14 3)
                    have b19861 := hb (x 15 2)
                    have b19862 := hb (x 16 13)
                    have b19863 := hb (x 17 12)
                    clear * - r19857 e19858 e19859 b19860 b19861 b19862 b19863 d19812 d19852
                    omega
                  have d19864 : (x 17 4).toNat = 0 := by
                    have r19865 : (x 17 4).toNat ≤ (x 17 12).toNat := himp _ _ (hp4 17)
                    have b19866 := hb (x 17 4)
                    have b19867 := hb (x 17 12)
                    clear * - r19865 b19866 b19867 d19856
                    omega
                  have d19868 : (x 17 4 && x 17 13).toNat = 0 := by
                    have r19869 := hand1 (x 17 4) (x 17 13)
                    have b19870 := hb (x 17 4)
                    have b19871 := hb (x 17 4 && x 17 13)
                    clear * - r19869 b19870 b19871 d19864
                    omega
                  have d19872 : (x 16 13).toNat = 0 := by
                    have r19873 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19874 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                    have e19875 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                    have b19876 := hb (x 14 3)
                    have b19877 := hb (x 15 2)
                    have b19878 := hb (x 16 13)
                    have b19879 := hb (x 17 12)
                    clear * - r19873 e19874 e19875 b19876 b19877 b19878 b19879 d19856 d19812 d19852
                    omega
                  have d19880 : (x 16 5).toNat = 0 := by
                    have r19881 : (x 16 5).toNat ≤ (x 16 13).toNat := himp _ _ (hp5 16)
                    have b19882 := hb (x 16 5)
                    have b19883 := hb (x 16 13)
                    clear * - r19881 b19882 b19883 d19872
                    omega
                  have d19884 : (x 16 5 && x 16 14).toNat = 0 := by
                    have r19885 := hand1 (x 16 5) (x 16 14)
                    have b19886 := hb (x 16 5)
                    have b19887 := hb (x 16 5 && x 16 14)
                    clear * - r19885 b19886 b19887 d19880
                    omega
                  have d19888 : (x 17 8).toNat = 0 := by
                    have r19889 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19890 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
                    have e19891 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
                    have e19892 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
                    have e19893 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
                    have e19894 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
                    have e19895 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
                    have b19896 := hb (x 10 7)
                    have b19897 := hb (x 11 6)
                    have b19898 := hb (x 12 5)
                    have b19899 := hb (x 13 4)
                    have b19900 := hb (x 14 11)
                    have b19901 := hb (x 15 10)
                    have b19902 := hb (x 16 9)
                    have b19903 := hb (x 17 8)
                    clear * - r19889 e19890 e19891 e19892 e19893 e19894 e19895 b19896 b19897 b19898 b19899 b19900 b19901 b19902 b19903 d19816 d19848
                    omega
                  have d19904 : (x 16 9).toNat = 0 := by
                    have r19905 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19906 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
                    have e19907 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
                    have e19908 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
                    have e19909 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
                    have e19910 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
                    have e19911 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
                    have b19912 := hb (x 10 7)
                    have b19913 := hb (x 11 6)
                    have b19914 := hb (x 12 5)
                    have b19915 := hb (x 13 4)
                    have b19916 := hb (x 14 11)
                    have b19917 := hb (x 15 10)
                    have b19918 := hb (x 16 9)
                    have b19919 := hb (x 17 8)
                    clear * - r19905 e19906 e19907 e19908 e19909 e19910 e19911 b19912 b19913 b19914 b19915 b19916 b19917 b19918 b19919 d19888 d19816 d19848
                    omega
                  have d19920 : (x 13 4).toNat = 0 := by
                    have r19921 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19922 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
                    have e19923 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
                    have e19924 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
                    have e19925 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
                    have e19926 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
                    have e19927 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
                    have b19928 := hb (x 10 7)
                    have b19929 := hb (x 11 6)
                    have b19930 := hb (x 12 5)
                    have b19931 := hb (x 13 4)
                    have b19932 := hb (x 14 11)
                    have b19933 := hb (x 15 10)
                    have b19934 := hb (x 16 9)
                    have b19935 := hb (x 17 8)
                    clear * - r19921 e19922 e19923 e19924 e19925 e19926 e19927 b19928 b19929 b19930 b19931 b19932 b19933 b19934 b19935 d19888 d19904 d19816 d19848
                    omega
                  have d19936 : (x 12 5).toNat = 0 := by
                    have r19937 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19938 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
                    have e19939 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
                    have e19940 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
                    have e19941 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
                    have e19942 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
                    have e19943 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
                    have b19944 := hb (x 10 7)
                    have b19945 := hb (x 11 6)
                    have b19946 := hb (x 12 5)
                    have b19947 := hb (x 13 4)
                    have b19948 := hb (x 14 11)
                    have b19949 := hb (x 15 10)
                    have b19950 := hb (x 16 9)
                    have b19951 := hb (x 17 8)
                    clear * - r19937 e19938 e19939 e19940 e19941 e19942 e19943 b19944 b19945 b19946 b19947 b19948 b19949 b19950 b19951 d19888 d19904 d19816 d19848 d19920
                    omega
                  have d19952 : (x 11 6).toNat = 0 := by
                    have r19953 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19954 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
                    have e19955 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
                    have e19956 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
                    have e19957 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
                    have e19958 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
                    have e19959 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
                    have b19960 := hb (x 10 7)
                    have b19961 := hb (x 11 6)
                    have b19962 := hb (x 12 5)
                    have b19963 := hb (x 13 4)
                    have b19964 := hb (x 14 11)
                    have b19965 := hb (x 15 10)
                    have b19966 := hb (x 16 9)
                    have b19967 := hb (x 17 8)
                    clear * - r19953 e19954 e19955 e19956 e19957 e19958 e19959 b19960 b19961 b19962 b19963 b19964 b19965 b19966 b19967 d19888 d19904 d19816 d19848 d19920 d19936
                    omega
                  have d19968 : (x 10 7).toNat = 0 := by
                    have r19969 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19970 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
                    have e19971 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
                    have e19972 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
                    have e19973 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
                    have e19974 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
                    have e19975 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
                    have b19976 := hb (x 10 7)
                    have b19977 := hb (x 11 6)
                    have b19978 := hb (x 12 5)
                    have b19979 := hb (x 13 4)
                    have b19980 := hb (x 14 11)
                    have b19981 := hb (x 15 10)
                    have b19982 := hb (x 16 9)
                    have b19983 := hb (x 17 8)
                    clear * - r19969 e19970 e19971 e19972 e19973 e19974 e19975 b19976 b19977 b19978 b19979 b19980 b19981 b19982 b19983 d19888 d19904 d19816 d19848 d19920 d19936 d19952
                    omega
                  have d19984 : (x 13 3).toNat = 0 := by
                    have r19985 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e19986 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                    have e19987 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                    have b19988 := hb (x 13 3)
                    have b19989 := hb (x 14 2)
                    have b19990 := hb (x 15 13)
                    have b19991 := hb (x 16 12)
                    clear * - r19985 e19986 e19987 b19988 b19989 b19990 b19991 d19779 d19787 d19775
                    omega
                  have d19992 : (x 15 1).toNat = 0 := by
                    have r19993 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b19994 := hb (x 2 14)
                    have b19995 := hb (x 3 13)
                    have b19996 := hb (x 4 12)
                    have b19997 := hb (x 5 11)
                    have b19998 := hb (x 6 10)
                    have b19999 := hb (x 7 9)
                    have b20000 := hb (x 8 8)
                    have b20001 := hb (x 9 7)
                    have b20002 := hb (x 10 6)
                    have b20003 := hb (x 11 5)
                    have b20004 := hb (x 12 4)
                    have b20005 := hb (x 13 3)
                    have b20006 := hb (x 14 2)
                    have b20007 := hb (x 15 1)
                    clear * - r19993 b19994 b19995 b19996 b19997 b19998 b19999 b20000 b20001 b20002 b20003 b20004 b20005 b20006 b20007 d19775 d19984 d19278 d18766 d18786 d18802 d18822 d17914 d17909 d17801
                    omega
                  have d20008 : (x 15 1 && x 15 7).toNat = 0 := by
                    have r20009 := hand1 (x 15 1) (x 15 7)
                    have b20010 := hb (x 15 1)
                    have b20011 := hb (x 15 1 && x 15 7)
                    clear * - r20009 b20010 b20011 d19992
                    omega
                  have d20012 : (x 12 4).toNat = 0 := by
                    have r20013 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b20014 := hb (x 2 14)
                    have b20015 := hb (x 3 13)
                    have b20016 := hb (x 4 12)
                    have b20017 := hb (x 5 11)
                    have b20018 := hb (x 6 10)
                    have b20019 := hb (x 7 9)
                    have b20020 := hb (x 8 8)
                    have b20021 := hb (x 9 7)
                    have b20022 := hb (x 10 6)
                    have b20023 := hb (x 11 5)
                    have b20024 := hb (x 12 4)
                    have b20025 := hb (x 13 3)
                    have b20026 := hb (x 14 2)
                    have b20027 := hb (x 15 1)
                    clear * - r20013 b20014 b20015 b20016 b20017 b20018 b20019 b20020 b20021 b20022 b20023 b20024 b20025 b20026 b20027 d19992 d19775 d19984 d19278 d18766 d18786 d18802 d18822 d17914 d17909 d17801
                    omega
                  have d20028 : (x 10 6).toNat = 0 := by
                    have r20029 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b20030 := hb (x 2 14)
                    have b20031 := hb (x 3 13)
                    have b20032 := hb (x 4 12)
                    have b20033 := hb (x 5 11)
                    have b20034 := hb (x 6 10)
                    have b20035 := hb (x 7 9)
                    have b20036 := hb (x 8 8)
                    have b20037 := hb (x 9 7)
                    have b20038 := hb (x 10 6)
                    have b20039 := hb (x 11 5)
                    have b20040 := hb (x 12 4)
                    have b20041 := hb (x 13 3)
                    have b20042 := hb (x 14 2)
                    have b20043 := hb (x 15 1)
                    clear * - r20029 b20030 b20031 b20032 b20033 b20034 b20035 b20036 b20037 b20038 b20039 b20040 b20041 b20042 b20043 d19992 d19775 d19984 d20012 d19278 d18766 d18786 d18802 d18822 d17914 d17909 d17801
                    omega
                  have d20044 : (x 10 6 && x 10 12).toNat = 0 := by
                    have r20045 := hand1 (x 10 6) (x 10 12)
                    have b20046 := hb (x 10 6)
                    have b20047 := hb (x 10 6 && x 10 12)
                    clear * - r20045 b20046 b20047 d20028
                    omega
                  have d20048 : (x 16 6).toNat = 1 := by
                    have r20049 : 1 ≤ (x 16 6).toNat + (x 15 1 && x 15 7).toNat + (x 14 2 && x 14 8).toNat + (x 13 3 && x 13 9).toNat + (x 12 4 && x 12 10).toNat + (x 11 5 && x 11 11).toNat + (x 10 6 && x 10 12).toNat + (x 9 7 && x 9 13).toNat + (x 8 8 && x 8 14).toNat + (x 7 9).toNat := by have q := hcov6 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b20050 := hb (x 7 9)
                    have b20051 := hb (x 16 6)
                    have b20052 := hb (x 15 1 && x 15 7)
                    have b20053 := hb (x 14 2 && x 14 8)
                    have b20054 := hb (x 13 3 && x 13 9)
                    have b20055 := hb (x 12 4 && x 12 10)
                    have b20056 := hb (x 11 5 && x 11 11)
                    have b20057 := hb (x 10 6 && x 10 12)
                    have b20058 := hb (x 9 7 && x 9 13)
                    have b20059 := hb (x 8 8 && x 8 14)
                    clear * - r20049 b20050 b20051 b20052 b20053 b20054 b20055 b20056 b20057 b20058 b20059 d20008 d19631 d19651 d19671 d19282 d20044 d19594 d18782 d18786
                    omega
                  have d20060 : (x 22 8).toNat = 0 := by
                    have r20061 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e20062 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
                    have e20063 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
                    have e20064 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
                    have e20065 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
                    have e20066 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
                    have e20067 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
                    have b20068 := hb (x 15 7)
                    have b20069 := hb (x 16 6)
                    have b20070 := hb (x 17 5)
                    have b20071 := hb (x 18 4)
                    have b20072 := hb (x 19 11)
                    have b20073 := hb (x 20 10)
                    have b20074 := hb (x 21 9)
                    have b20075 := hb (x 22 8)
                    clear * - r20061 e20062 e20063 e20064 e20065 e20066 e20067 b20068 b20069 b20070 b20071 b20072 b20073 b20074 b20075 d20048
                    omega
                  have d20076 : (x 21 9).toNat = 0 := by
                    have r20077 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e20078 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
                    have e20079 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
                    have e20080 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
                    have e20081 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
                    have e20082 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
                    have e20083 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
                    have b20084 := hb (x 15 7)
                    have b20085 := hb (x 16 6)
                    have b20086 := hb (x 17 5)
                    have b20087 := hb (x 18 4)
                    have b20088 := hb (x 19 11)
                    have b20089 := hb (x 20 10)
                    have b20090 := hb (x 21 9)
                    have b20091 := hb (x 22 8)
                    clear * - r20077 e20078 e20079 e20080 e20081 e20082 e20083 b20084 b20085 b20086 b20087 b20088 b20089 b20090 b20091 d20060 d20048
                    omega
                  have d20092 : (x 20 10).toNat = 0 := by
                    have r20093 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e20094 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
                    have e20095 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
                    have e20096 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
                    have e20097 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
                    have e20098 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
                    have e20099 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
                    have b20100 := hb (x 15 7)
                    have b20101 := hb (x 16 6)
                    have b20102 := hb (x 17 5)
                    have b20103 := hb (x 18 4)
                    have b20104 := hb (x 19 11)
                    have b20105 := hb (x 20 10)
                    have b20106 := hb (x 21 9)
                    have b20107 := hb (x 22 8)
                    clear * - r20093 e20094 e20095 e20096 e20097 e20098 e20099 b20100 b20101 b20102 b20103 b20104 b20105 b20106 b20107 d20060 d20076 d20048
                    omega
                  have d20108 : (x 20 1 && x 20 10).toNat = 0 := by
                    have r20109 := hand2 (x 20 1) (x 20 10)
                    have b20110 := hb (x 20 10)
                    have b20111 := hb (x 20 1 && x 20 10)
                    clear * - r20109 b20110 b20111 d20092
                    omega
                  have d20112 : (x 19 11).toNat = 0 := by
                    have r20113 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e20114 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
                    have e20115 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
                    have e20116 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
                    have e20117 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
                    have e20118 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
                    have e20119 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
                    have b20120 := hb (x 15 7)
                    have b20121 := hb (x 16 6)
                    have b20122 := hb (x 17 5)
                    have b20123 := hb (x 18 4)
                    have b20124 := hb (x 19 11)
                    have b20125 := hb (x 20 10)
                    have b20126 := hb (x 21 9)
                    have b20127 := hb (x 22 8)
                    clear * - r20113 e20114 e20115 e20116 e20117 e20118 e20119 b20120 b20121 b20122 b20123 b20124 b20125 b20126 b20127 d20060 d20076 d20092 d20048
                    omega
                  have d20128 : (x 19 2 && x 19 11).toNat = 0 := by
                    have r20129 := hand2 (x 19 2) (x 19 11)
                    have b20130 := hb (x 19 11)
                    have b20131 := hb (x 19 2 && x 19 11)
                    clear * - r20129 b20130 b20131 d20112
                    omega
                  have d20132 : (x 18 3 && x 18 12).toNat = 1 := by
                    have r20133 : 1 ≤ (x 21 9).toNat + (x 20 1 && x 20 10).toNat + (x 19 2 && x 19 11).toNat + (x 18 3 && x 18 12).toNat + (x 17 4 && x 17 13).toNat + (x 16 5 && x 16 14).toNat + (x 15 6).toNat := by have q := hcov9 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b20134 := hb (x 15 6)
                    have b20135 := hb (x 21 9)
                    have b20136 := hb (x 20 1 && x 20 10)
                    have b20137 := hb (x 19 2 && x 19 11)
                    have b20138 := hb (x 18 3 && x 18 12)
                    have b20139 := hb (x 17 4 && x 17 13)
                    have b20140 := hb (x 16 5 && x 16 14)
                    clear * - r20133 b20134 b20135 b20136 b20137 b20138 b20139 b20140 d20076 d20108 d20128 d19868 d19884 d19808
                    omega
                  have d20141 : (x 18 12).toNat = 1 := by
                    have r20142 := hand2 (x 18 3) (x 18 12)
                    have b20143 := hb (x 18 12)
                    have b20144 := hb (x 18 3 && x 18 12)
                    clear * - r20142 b20143 b20144 d20132
                    omega
                  have d20145 : (x 17 13).toNat = 0 := by
                    have r20146 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e20147 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
                    have e20148 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
                    have b20149 := hb (x 15 3)
                    have b20150 := hb (x 16 2)
                    have b20151 := hb (x 17 13)
                    have b20152 := hb (x 18 12)
                    clear * - r20146 e20147 e20148 b20149 b20150 b20151 b20152 d20141
                    omega
                  have d20153 : (x 16 1 && x 16 14).toNat = 1 := by
                    have r20154 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := by have q := hcov13 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b20155 := hb (x 15 2)
                    have b20156 := hb (x 17 13)
                    have b20157 := hb (x 16 1 && x 16 14)
                    clear * - r20154 b20155 b20156 b20157 d20145 d19812
                    omega
                  have d20158 : (x 16 1).toNat = 1 := by
                    have r20159 := hand1 (x 16 1) (x 16 14)
                    have b20160 := hb (x 16 1)
                    have b20161 := hb (x 16 1 && x 16 14)
                    clear * - r20159 b20160 b20161 d20153
                    omega
                  have d20162 : (x 9 8).toNat = 0 := by
                    have r20163 : (x 16 1).toNat + (x 15 2).toNat + (x 14 3).toNat + (x 13 4).toNat + (x 12 5).toNat + (x 11 6).toNat + (x 10 7).toNat + (x 9 8).toNat + (x 8 9).toNat + (x 7 10).toNat + (x 6 11).toNat + (x 5 12).toNat + (x 4 13).toNat + (x 3 14).toNat = 3 := by have q := hcount 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b20164 := hb (x 3 14)
                    have b20165 := hb (x 4 13)
                    have b20166 := hb (x 5 12)
                    have b20167 := hb (x 6 11)
                    have b20168 := hb (x 7 10)
                    have b20169 := hb (x 8 9)
                    have b20170 := hb (x 9 8)
                    have b20171 := hb (x 10 7)
                    have b20172 := hb (x 11 6)
                    have b20173 := hb (x 12 5)
                    have b20174 := hb (x 13 4)
                    have b20175 := hb (x 14 3)
                    have b20176 := hb (x 15 2)
                    have b20177 := hb (x 16 1)
                    clear * - r20163 b20164 b20165 b20166 b20167 b20168 b20169 b20170 b20171 b20172 b20173 b20174 b20175 b20176 b20177 d20158 d19812 d19852 d19920 d19936 d19952 d19968 d17994 d18010 d17897
                    omega
                  have d20178 : (x 8 9).toNat = 0 := by
                    have r20179 : (x 16 1).toNat + (x 15 2).toNat + (x 14 3).toNat + (x 13 4).toNat + (x 12 5).toNat + (x 11 6).toNat + (x 10 7).toNat + (x 9 8).toNat + (x 8 9).toNat + (x 7 10).toNat + (x 6 11).toNat + (x 5 12).toNat + (x 4 13).toNat + (x 3 14).toNat = 3 := by have q := hcount 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b20180 := hb (x 3 14)
                    have b20181 := hb (x 4 13)
                    have b20182 := hb (x 5 12)
                    have b20183 := hb (x 6 11)
                    have b20184 := hb (x 7 10)
                    have b20185 := hb (x 8 9)
                    have b20186 := hb (x 9 8)
                    have b20187 := hb (x 10 7)
                    have b20188 := hb (x 11 6)
                    have b20189 := hb (x 12 5)
                    have b20190 := hb (x 13 4)
                    have b20191 := hb (x 14 3)
                    have b20192 := hb (x 15 2)
                    have b20193 := hb (x 16 1)
                    clear * - r20179 b20180 b20181 b20182 b20183 b20184 b20185 b20186 b20187 b20188 b20189 b20190 b20191 b20192 b20193 d20158 d19812 d19852 d19920 d19936 d19952 d19968 d20162 d17994 d18010 d17897
                    omega
                  have d20194 : (x 7 1 && x 7 10).toNat = 1 := by
                    have r20195 : 1 ≤ (x 8 9).toNat + (x 7 1 && x 7 10).toNat + (x 6 2 && x 6 11).toNat + (x 5 3 && x 5 12).toNat + (x 4 4 && x 4 13).toNat + (x 3 5 && x 3 14).toNat + (x 2 6).toNat := by have q := hcov9 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b20196 := hb (x 2 6)
                    have b20197 := hb (x 8 9)
                    have b20198 := hb (x 7 1 && x 7 10)
                    have b20199 := hb (x 6 2 && x 6 11)
                    have b20200 := hb (x 5 3 && x 5 12)
                    have b20201 := hb (x 4 4 && x 4 13)
                    have b20202 := hb (x 3 5 && x 3 14)
                    clear * - r20195 b20196 b20197 b20198 b20199 b20200 b20201 b20202 d20178 d19458 d18002 d17930 d18871 d18879
                    omega
                  have d20203 : (x 7 10).toNat = 1 := by
                    have r20204 := hand2 (x 7 1) (x 7 10)
                    have b20205 := hb (x 7 10)
                    have b20206 := hb (x 7 1 && x 7 10)
                    clear * - r20204 b20205 b20206 d20194
                    omega
                  have d20207 : (x 6 11).toNat = 0 := by
                    have r20208 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e20209 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                    have e20210 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                    have e20211 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                    have e20212 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                    have e20213 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                    have e20214 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                    have b20215 := hb (x 2 7)
                    have b20216 := hb (x 3 6)
                    have b20217 := hb (x 4 5)
                    have b20218 := hb (x 5 4)
                    have b20219 := hb (x 6 11)
                    have b20220 := hb (x 7 10)
                    have b20221 := hb (x 8 9)
                    have b20222 := hb (x 9 8)
                    clear * - r20208 e20209 e20210 e20211 e20212 e20213 e20214 b20215 b20216 b20217 b20218 b20219 b20220 b20221 b20222 d20162 d20178 d20203 d18006 d18018
                    omega
                  have r20223 : (x 16 1).toNat + (x 15 2).toNat + (x 14 3).toNat + (x 13 4).toNat + (x 12 5).toNat + (x 11 6).toNat + (x 10 7).toNat + (x 9 8).toNat + (x 8 9).toNat + (x 7 10).toNat + (x 6 11).toNat + (x 5 12).toNat + (x 4 13).toNat + (x 3 14).toNat = 3 := by have q := hcount 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b20224 := hb (x 3 14)
                  have b20225 := hb (x 4 13)
                  have b20226 := hb (x 5 12)
                  have b20227 := hb (x 6 11)
                  have b20228 := hb (x 7 10)
                  have b20229 := hb (x 8 9)
                  have b20230 := hb (x 9 8)
                  have b20231 := hb (x 10 7)
                  have b20232 := hb (x 11 6)
                  have b20233 := hb (x 12 5)
                  have b20234 := hb (x 13 4)
                  have b20235 := hb (x 14 3)
                  have b20236 := hb (x 15 2)
                  have b20237 := hb (x 16 1)
                  linarith only [r20223, b20224, b20225, b20226, b20227, b20228, b20229, b20230, b20231, b20232, b20233, b20234, b20235, b20236, b20237, d20158, d19812, d19852, d19920, d19936, d19952, d19968, d20162, d20178, d20203, d20207, d17994, d18010, d17897]
              · have f20238 : (x (-1) 4).toNat = 1 := by rw [h17815]; rfl
                have d20239 : (x (-1) 12).toNat = 1 := by
                  have r20240 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
                  have b20241 := hb (x (-1) 4)
                  have b20242 := hb (x (-1) 12)
                  clear * - r20240 b20241 b20242 f20238
                  omega
                have d20243 : (x (-2) 13).toNat = 0 := by
                  have r20244 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e20245 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                  have e20246 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                  have b20247 := hb (x (-4) 3)
                  have b20248 := hb (x (-3) 2)
                  have b20249 := hb (x (-2) 13)
                  have b20250 := hb (x (-1) 12)
                  clear * - r20244 e20245 e20246 b20247 b20248 b20249 b20250 d20239 d17623
                  omega
                have d20251 : (x (-4) 2).toNat = 1 := by
                  have r20252 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b20253 := hb (x (-4) 2)
                  have b20254 := hb (x (-2) 13)
                  have b20255 := hb (x (-3) 1 && x (-3) 14)
                  clear * - r20252 b20253 b20254 b20255 d20243 d17595
                  omega
                have d20256 : (x (-4) 3).toNat = 0 := by
                  have r20257 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e20258 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                  have e20259 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                  have b20260 := hb (x (-4) 3)
                  have b20261 := hb (x (-3) 2)
                  have b20262 := hb (x (-2) 13)
                  have b20263 := hb (x (-1) 12)
                  clear * - r20257 e20258 e20259 b20260 b20261 b20262 b20263 d20239 d20243 d17623
                  omega
                have d20264 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
                  have r20265 := hand1 (x (-4) 3) (x (-4) 14)
                  have b20266 := hb (x (-4) 3)
                  have b20267 := hb (x (-4) 3 && x (-4) 14)
                  clear * - r20265 b20266 b20267 d20256
                  omega
                have d20268 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
                  have r20269 := hand1 (x (-4) 3) (x (-4) 13)
                  have b20270 := hb (x (-4) 3)
                  have b20271 := hb (x (-4) 3 && x (-4) 13)
                  clear * - r20269 b20270 b20271 d20256
                  omega
                have d20272 : (x (-2) 12).toNat = 0 := by
                  have r20273 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e20274 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                  have e20275 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                  have b20276 := hb (x (-5) 3)
                  have b20277 := hb (x (-4) 2)
                  have b20278 := hb (x (-3) 13)
                  have b20279 := hb (x (-2) 12)
                  clear * - r20273 e20274 e20275 b20276 b20277 b20278 b20279 d17668 d20251
                  omega
                have d20280 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
                  have r20281 := hand2 (x (-2) 1) (x (-2) 12)
                  have b20282 := hb (x (-2) 12)
                  have b20283 := hb (x (-2) 1 && x (-2) 12)
                  clear * - r20281 b20282 b20283 d20272
                  omega
                have d20284 : (x (-5) 4).toNat = 1 := by
                  have r20285 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b20286 := hb (x (-5) 4)
                  have b20287 := hb (x (-1) 11)
                  have b20288 := hb (x (-2) 1 && x (-2) 12)
                  have b20289 := hb (x (-3) 2 && x (-3) 13)
                  have b20290 := hb (x (-4) 3 && x (-4) 14)
                  clear * - r20285 b20286 b20287 b20288 b20289 b20290 g11 d20280 d17627 d20264
                  omega
                have d20291 : (x (-5) 12).toNat = 1 := by
                  have r20292 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
                  have b20293 := hb (x (-5) 4)
                  have b20294 := hb (x (-5) 12)
                  clear * - r20292 b20293 b20294 d20284
                  omega
                have d20295 : (x (-6) 13).toNat = 0 := by
                  have r20296 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e20297 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                  have e20298 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                  have b20299 := hb (x (-8) 3)
                  have b20300 := hb (x (-7) 2)
                  have b20301 := hb (x (-6) 13)
                  have b20302 := hb (x (-5) 12)
                  clear * - r20296 e20297 e20298 b20299 b20300 b20301 b20302 d20291
                  omega
                have d20303 : (x (-6) 5).toNat = 0 := by
                  have r20304 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
                  have b20305 := hb (x (-6) 5)
                  have b20306 := hb (x (-6) 13)
                  clear * - r20304 b20305 b20306 d20295
                  omega
                have d20307 : (x (-7) 2).toNat = 0 := by
                  have r20308 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e20309 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                  have e20310 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                  have b20311 := hb (x (-8) 3)
                  have b20312 := hb (x (-7) 2)
                  have b20313 := hb (x (-6) 13)
                  have b20314 := hb (x (-5) 12)
                  clear * - r20308 e20309 e20310 b20311 b20312 b20313 b20314 d20291 d20295
                  omega
                have d20315 : (x (-6) 1 && x (-6) 14).toNat = 1 := by
                  have r20316 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b20317 := hb (x (-7) 2)
                  have b20318 := hb (x (-5) 13)
                  have b20319 := hb (x (-6) 1 && x (-6) 14)
                  clear * - r20316 b20317 b20318 b20319 g3 d20307
                  omega
                have d20320 : (x (-6) 1).toNat = 1 := by
                  have r20321 := hand1 (x (-6) 1) (x (-6) 14)
                  have b20322 := hb (x (-6) 1)
                  have b20323 := hb (x (-6) 1 && x (-6) 14)
                  clear * - r20321 b20322 b20323 d20315
                  omega
                have d20324 : (x (-5) 14).toNat = 0 := by
                  have r20325 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b20326 := hb (x (-6) 1)
                  have b20327 := hb (x (-5) 14)
                  clear * - r20325 b20326 b20327 d20320
                  omega
                have d20328 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
                  have r20329 := hand2 (x (-5) 4) (x (-5) 14)
                  have b20330 := hb (x (-5) 14)
                  have b20331 := hb (x (-5) 4 && x (-5) 14)
                  clear * - r20329 b20330 b20331 d20324
                  omega
                have r20332 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20333 := hb (x (-6) 5)
                have b20334 := hb (x (-1) 10)
                have b20335 := hb (x (-2) 1 && x (-2) 11)
                have b20336 := hb (x (-3) 2 && x (-3) 12)
                have b20337 := hb (x (-4) 3 && x (-4) 13)
                have b20338 := hb (x (-5) 4 && x (-5) 14)
                linarith only [r20332, b20333, b20334, b20335, b20336, b20337, b20338, g10, g72, d17631, d20268, d20328, d20303]
            · have f20339 : (x 1 3).toNat = 1 := by rw [h17805]; rfl
              have d20340 : (x 4 12).toNat = 0 := by
                have r20341 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20342 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e20343 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b20344 := hb (x 1 3)
                have b20345 := hb (x 2 2)
                have b20346 := hb (x 3 13)
                have b20347 := hb (x 4 12)
                clear * - r20341 e20342 e20343 b20344 b20345 b20346 b20347 f20339
                omega
              have d20348 : (x 4 1 && x 4 12).toNat = 0 := by
                have r20349 := hand2 (x 4 1) (x 4 12)
                have b20350 := hb (x 4 12)
                have b20351 := hb (x 4 1 && x 4 12)
                clear * - r20349 b20350 b20351 d20340
                omega
              have d20352 : (x 4 4).toNat = 0 := by
                have r20353 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
                have b20354 := hb (x 4 4)
                have b20355 := hb (x 4 12)
                clear * - r20353 b20354 b20355 d20340
                omega
              have d20356 : (x 3 13).toNat = 0 := by
                have r20357 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20358 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e20359 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b20360 := hb (x 1 3)
                have b20361 := hb (x 2 2)
                have b20362 := hb (x 3 13)
                have b20363 := hb (x 4 12)
                clear * - r20357 e20358 e20359 b20360 b20361 b20362 b20363 d20340 f20339
                omega
              have d20364 : (x 3 2 && x 3 13).toNat = 0 := by
                have r20365 := hand2 (x 3 2) (x 3 13)
                have b20366 := hb (x 3 13)
                have b20367 := hb (x 3 2 && x 3 13)
                clear * - r20365 b20366 b20367 d20356
                omega
              have d20368 : (x 2 1 && x 2 14).toNat = 1 := by
                have r20369 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20370 := hb (x 1 2)
                have b20371 := hb (x 3 13)
                have b20372 := hb (x 2 1 && x 2 14)
                clear * - r20369 b20370 b20371 b20372 d20356 g23
                omega
              have d20373 : (x 2 1).toNat = 1 := by
                have r20374 := hand1 (x 2 1) (x 2 14)
                have b20375 := hb (x 2 1)
                have b20376 := hb (x 2 1 && x 2 14)
                clear * - r20374 b20375 b20376 d20368
                omega
              have d20377 : (x 3 14).toNat = 0 := by
                have r20378 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20379 := hb (x 2 1)
                have b20380 := hb (x 3 14)
                clear * - r20378 b20379 b20380 d20373
                omega
              have d20381 : (x 3 1 && x 3 14).toNat = 0 := by
                have r20382 := hand2 (x 3 1) (x 3 14)
                have b20383 := hb (x 3 14)
                have b20384 := hb (x 3 1 && x 3 14)
                clear * - r20382 b20383 b20384 d20377
                omega
              have d20385 : (x 3 2).toNat = 0 := by
                have r20386 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
                have b20387 := hb (x 3 2)
                have b20388 := hb (x 3 14)
                clear * - r20386 b20387 b20388 d20377
                omega
              have d20389 : (x 2 2).toNat = 0 := by
                have r20390 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20391 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e20392 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b20393 := hb (x 1 3)
                have b20394 := hb (x 2 2)
                have b20395 := hb (x 3 13)
                have b20396 := hb (x 4 12)
                clear * - r20390 e20391 e20392 b20393 b20394 b20395 b20396 d20340 d20356 f20339
                omega
              have d20397 : (x 4 13).toNat = 1 := by
                have r20398 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20399 := hb (x 2 2)
                have b20400 := hb (x 4 13)
                have b20401 := hb (x 3 1 && x 3 14)
                clear * - r20398 b20399 b20400 b20401 d20381 d20389
                omega
              have d20402 : (x 4 1).toNat = 1 := by
                have r20403 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
                have b20404 := hb (x 4 1)
                have b20405 := hb (x 4 13)
                clear * - r20403 b20404 b20405 d20397
                omega
              have d20406 : (x 5 14).toNat = 0 := by
                have r20407 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20408 := hb (x 4 1)
                have b20409 := hb (x 5 14)
                clear * - r20407 b20408 b20409 d20402
                omega
              have d20410 : (x 5 3 && x 5 14).toNat = 0 := by
                have r20411 := hand2 (x 5 3) (x 5 14)
                have b20412 := hb (x 5 14)
                have b20413 := hb (x 5 3 && x 5 14)
                clear * - r20411 b20412 b20413 d20406
                omega
              have d20414 : (x 5 2).toNat = 0 := by
                have r20415 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
                have b20416 := hb (x 5 2)
                have b20417 := hb (x 5 14)
                clear * - r20415 b20416 b20417 d20406
                omega
              have d20418 : (x 5 12).toNat = 0 := by
                have r20419 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20420 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                have e20421 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                have b20422 := hb (x 2 3)
                have b20423 := hb (x 3 2)
                have b20424 := hb (x 4 13)
                have b20425 := hb (x 5 12)
                clear * - r20419 e20420 e20421 b20422 b20423 b20424 b20425 d20397 d20385
                omega
              have d20426 : (x 5 4).toNat = 0 := by
                have r20427 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
                have b20428 := hb (x 5 4)
                have b20429 := hb (x 5 12)
                clear * - r20427 b20428 b20429 d20418
                omega
              have d20430 : (x 2 3).toNat = 0 := by
                have r20431 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20432 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                have e20433 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                have b20434 := hb (x 2 3)
                have b20435 := hb (x 3 2)
                have b20436 := hb (x 4 13)
                have b20437 := hb (x 5 12)
                clear * - r20431 e20432 e20433 b20434 b20435 b20436 b20437 d20418 d20397 d20385
                omega
              have d20438 : (x 2 3 && x 2 14).toNat = 0 := by
                have r20439 := hand1 (x 2 3) (x 2 14)
                have b20440 := hb (x 2 3)
                have b20441 := hb (x 2 3 && x 2 14)
                clear * - r20439 b20440 b20441 d20430
                omega
              have d20442 : (x 5 11).toNat = 1 := by
                have r20443 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20444 := hb (x 1 4)
                have b20445 := hb (x 5 11)
                have b20446 := hb (x 4 1 && x 4 12)
                have b20447 := hb (x 3 2 && x 3 13)
                have b20448 := hb (x 2 3 && x 2 14)
                clear * - r20443 b20444 b20445 b20446 b20447 b20448 d20348 d20364 d20438 g24
                omega
              have d20449 : (x 5 3).toNat = 1 := by
                have r20450 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
                have b20451 := hb (x 5 3)
                have b20452 := hb (x 5 11)
                clear * - r20450 b20451 b20452 d20442
                omega
              have d20453 : (x 8 12).toNat = 0 := by
                have r20454 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20455 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                have e20456 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                have b20457 := hb (x 5 3)
                have b20458 := hb (x 6 2)
                have b20459 := hb (x 7 13)
                have b20460 := hb (x 8 12)
                clear * - r20454 e20455 e20456 b20457 b20458 b20459 b20460 d20449
                omega
              have d20461 : (x 8 1 && x 8 12).toNat = 0 := by
                have r20462 := hand2 (x 8 1) (x 8 12)
                have b20463 := hb (x 8 12)
                have b20464 := hb (x 8 1 && x 8 12)
                clear * - r20462 b20463 b20464 d20453
                omega
              have d20465 : (x 8 4).toNat = 0 := by
                have r20466 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
                have b20467 := hb (x 8 4)
                have b20468 := hb (x 8 12)
                clear * - r20466 b20467 b20468 d20453
                omega
              have d20469 : (x 7 13).toNat = 0 := by
                have r20470 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20471 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                have e20472 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                have b20473 := hb (x 5 3)
                have b20474 := hb (x 6 2)
                have b20475 := hb (x 7 13)
                have b20476 := hb (x 8 12)
                clear * - r20470 e20471 e20472 b20473 b20474 b20475 b20476 d20453 d20449
                omega
              have d20477 : (x 7 2 && x 7 13).toNat = 0 := by
                have r20478 := hand2 (x 7 2) (x 7 13)
                have b20479 := hb (x 7 13)
                have b20480 := hb (x 7 2 && x 7 13)
                clear * - r20478 b20479 b20480 d20469
                omega
              have d20481 : (x 6 1 && x 6 14).toNat = 1 := by
                have r20482 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20483 := hb (x 5 2)
                have b20484 := hb (x 7 13)
                have b20485 := hb (x 6 1 && x 6 14)
                clear * - r20482 b20483 b20484 b20485 d20469 d20414
                omega
              have d20486 : (x 6 1).toNat = 1 := by
                have r20487 := hand1 (x 6 1) (x 6 14)
                have b20488 := hb (x 6 1)
                have b20489 := hb (x 6 1 && x 6 14)
                clear * - r20487 b20488 b20489 d20481
                omega
              have d20490 : (x 7 14).toNat = 0 := by
                have r20491 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20492 := hb (x 6 1)
                have b20493 := hb (x 7 14)
                clear * - r20491 b20492 b20493 d20486
                omega
              have d20494 : (x 7 1 && x 7 14).toNat = 0 := by
                have r20495 := hand2 (x 7 1) (x 7 14)
                have b20496 := hb (x 7 14)
                have b20497 := hb (x 7 1 && x 7 14)
                clear * - r20495 b20496 b20497 d20490
                omega
              have d20498 : (x 7 2).toNat = 0 := by
                have r20499 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
                have b20500 := hb (x 7 2)
                have b20501 := hb (x 7 14)
                clear * - r20499 b20500 b20501 d20490
                omega
              have d20502 : (x 6 2).toNat = 0 := by
                have r20503 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20504 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                have e20505 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                have b20506 := hb (x 5 3)
                have b20507 := hb (x 6 2)
                have b20508 := hb (x 7 13)
                have b20509 := hb (x 8 12)
                clear * - r20503 e20504 e20505 b20506 b20507 b20508 b20509 d20453 d20469 d20449
                omega
              have d20510 : (x 6 2 && x 6 13).toNat = 0 := by
                have r20511 := hand1 (x 6 2) (x 6 13)
                have b20512 := hb (x 6 2)
                have b20513 := hb (x 6 2 && x 6 13)
                clear * - r20511 b20512 b20513 d20502
                omega
              have d20514 : (x 8 13).toNat = 1 := by
                have r20515 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20516 := hb (x 6 2)
                have b20517 := hb (x 8 13)
                have b20518 := hb (x 7 1 && x 7 14)
                clear * - r20515 b20516 b20517 b20518 d20494 d20502
                omega
              have d20519 : (x 8 1).toNat = 1 := by
                have r20520 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
                have b20521 := hb (x 8 1)
                have b20522 := hb (x 8 13)
                clear * - r20520 b20521 b20522 d20514
                omega
              have d20523 : (x 9 14).toNat = 0 := by
                have r20524 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20525 := hb (x 8 1)
                have b20526 := hb (x 9 14)
                clear * - r20524 b20525 b20526 d20519
                omega
              have d20527 : (x 9 3 && x 9 14).toNat = 0 := by
                have r20528 := hand2 (x 9 3) (x 9 14)
                have b20529 := hb (x 9 14)
                have b20530 := hb (x 9 3 && x 9 14)
                clear * - r20528 b20529 b20530 d20523
                omega
              have d20531 : (x 9 2).toNat = 0 := by
                have r20532 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
                have b20533 := hb (x 9 2)
                have b20534 := hb (x 9 14)
                clear * - r20532 b20533 b20534 d20523
                omega
              have d20535 : (x 9 12).toNat = 0 := by
                have r20536 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20537 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                have e20538 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                have b20539 := hb (x 6 3)
                have b20540 := hb (x 7 2)
                have b20541 := hb (x 8 13)
                have b20542 := hb (x 9 12)
                clear * - r20536 e20537 e20538 b20539 b20540 b20541 b20542 d20514 d20498
                omega
              have d20543 : (x 9 4).toNat = 0 := by
                have r20544 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
                have b20545 := hb (x 9 4)
                have b20546 := hb (x 9 12)
                clear * - r20544 b20545 b20546 d20535
                omega
              have d20547 : (x 6 3).toNat = 0 := by
                have r20548 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20549 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                have e20550 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                have b20551 := hb (x 6 3)
                have b20552 := hb (x 7 2)
                have b20553 := hb (x 8 13)
                have b20554 := hb (x 9 12)
                clear * - r20548 e20549 e20550 b20551 b20552 b20553 b20554 d20535 d20514 d20498
                omega
              have d20555 : (x 6 3 && x 6 14).toNat = 0 := by
                have r20556 := hand1 (x 6 3) (x 6 14)
                have b20557 := hb (x 6 3)
                have b20558 := hb (x 6 3 && x 6 14)
                clear * - r20556 b20557 b20558 d20547
                omega
              have d20559 : (x 9 11).toNat = 1 := by
                have r20560 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20561 := hb (x 5 4)
                have b20562 := hb (x 9 11)
                have b20563 := hb (x 8 1 && x 8 12)
                have b20564 := hb (x 7 2 && x 7 13)
                have b20565 := hb (x 6 3 && x 6 14)
                clear * - r20560 b20561 b20562 b20563 b20564 b20565 d20461 d20477 d20555 d20426
                omega
              have d20566 : (x 9 3).toNat = 1 := by
                have r20567 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
                have b20568 := hb (x 9 3)
                have b20569 := hb (x 9 11)
                clear * - r20567 b20568 b20569 d20559
                omega
              have d20570 : (x 12 12).toNat = 0 := by
                have r20571 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20572 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
                have e20573 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
                have b20574 := hb (x 9 3)
                have b20575 := hb (x 10 2)
                have b20576 := hb (x 11 13)
                have b20577 := hb (x 12 12)
                clear * - r20571 e20572 e20573 b20574 b20575 b20576 b20577 d20566
                omega
              have d20578 : (x 12 1 && x 12 12).toNat = 0 := by
                have r20579 := hand2 (x 12 1) (x 12 12)
                have b20580 := hb (x 12 12)
                have b20581 := hb (x 12 1 && x 12 12)
                clear * - r20579 b20580 b20581 d20570
                omega
              have d20582 : (x 12 4).toNat = 0 := by
                have r20583 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
                have b20584 := hb (x 12 4)
                have b20585 := hb (x 12 12)
                clear * - r20583 b20584 b20585 d20570
                omega
              have d20586 : (x 11 13).toNat = 0 := by
                have r20587 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20588 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
                have e20589 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
                have b20590 := hb (x 9 3)
                have b20591 := hb (x 10 2)
                have b20592 := hb (x 11 13)
                have b20593 := hb (x 12 12)
                clear * - r20587 e20588 e20589 b20590 b20591 b20592 b20593 d20570 d20566
                omega
              have d20594 : (x 11 2 && x 11 13).toNat = 0 := by
                have r20595 := hand2 (x 11 2) (x 11 13)
                have b20596 := hb (x 11 13)
                have b20597 := hb (x 11 2 && x 11 13)
                clear * - r20595 b20596 b20597 d20586
                omega
              have d20598 : (x 10 1 && x 10 14).toNat = 1 := by
                have r20599 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20600 := hb (x 9 2)
                have b20601 := hb (x 11 13)
                have b20602 := hb (x 10 1 && x 10 14)
                clear * - r20599 b20600 b20601 b20602 d20586 d20531
                omega
              have d20603 : (x 10 14).toNat = 1 := by
                have r20604 := hand2 (x 10 1) (x 10 14)
                have b20605 := hb (x 10 14)
                have b20606 := hb (x 10 1 && x 10 14)
                clear * - r20604 b20605 b20606 d20598
                omega
              have d20607 : (x 9 1).toNat = 0 := by
                have r20608 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20609 := hb (x 9 1)
                have b20610 := hb (x 10 14)
                clear * - r20608 b20609 b20610 d20603
                omega
              have d20611 : (x 9 13).toNat = 0 := by
                have r20612 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
                have b20613 := hb (x 9 1)
                have b20614 := hb (x 9 13)
                clear * - r20612 b20613 b20614 d20607
                omega
              have d20615 : (x 8 1 && x 8 14).toNat = 1 := by
                have r20616 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20617 := hb (x 7 2)
                have b20618 := hb (x 9 13)
                have b20619 := hb (x 8 1 && x 8 14)
                clear * - r20616 b20617 b20618 b20619 d20611 d20498
                omega
              have d20620 : (x 8 14).toNat = 1 := by
                have r20621 := hand2 (x 8 1) (x 8 14)
                have b20622 := hb (x 8 14)
                have b20623 := hb (x 8 1 && x 8 14)
                clear * - r20621 b20622 b20623 d20615
                omega
              have d20624 : (x 7 1).toNat = 0 := by
                have r20625 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20626 := hb (x 7 1)
                have b20627 := hb (x 8 14)
                clear * - r20625 b20626 b20627 d20620
                omega
              have d20628 : (x 7 1 && x 7 12).toNat = 0 := by
                have r20629 := hand1 (x 7 1) (x 7 12)
                have b20630 := hb (x 7 1)
                have b20631 := hb (x 7 1 && x 7 12)
                clear * - r20629 b20630 b20631 d20624
                omega
              have d20632 : (x 8 11).toNat = 1 := by
                have r20633 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20634 := hb (x 4 4)
                have b20635 := hb (x 8 11)
                have b20636 := hb (x 7 1 && x 7 12)
                have b20637 := hb (x 6 2 && x 6 13)
                have b20638 := hb (x 5 3 && x 5 14)
                clear * - r20633 b20634 b20635 b20636 b20637 b20638 d20628 d20510 d20410 d20352
                omega
              have d20639 : (x 8 3).toNat = 1 := by
                have r20640 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
                have b20641 := hb (x 8 3)
                have b20642 := hb (x 8 11)
                clear * - r20640 b20641 b20642 d20632
                omega
              have d20643 : (x 11 12).toNat = 0 := by
                have r20644 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20645 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                have e20646 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                have b20647 := hb (x 8 3)
                have b20648 := hb (x 9 2)
                have b20649 := hb (x 10 13)
                have b20650 := hb (x 11 12)
                clear * - r20644 e20645 e20646 b20647 b20648 b20649 b20650 d20531 d20639
                omega
              have d20651 : (x 11 1 && x 11 12).toNat = 0 := by
                have r20652 := hand2 (x 11 1) (x 11 12)
                have b20653 := hb (x 11 12)
                have b20654 := hb (x 11 1 && x 11 12)
                clear * - r20652 b20653 b20654 d20643
                omega
              have d20655 : (x 10 13).toNat = 0 := by
                have r20656 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20657 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                have e20658 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                have b20659 := hb (x 8 3)
                have b20660 := hb (x 9 2)
                have b20661 := hb (x 10 13)
                have b20662 := hb (x 11 12)
                clear * - r20656 e20657 e20658 b20659 b20660 b20661 b20662 d20643 d20531 d20639
                omega
              have d20663 : (x 10 2 && x 10 13).toNat = 0 := by
                have r20664 := hand2 (x 10 2) (x 10 13)
                have b20665 := hb (x 10 13)
                have b20666 := hb (x 10 2 && x 10 13)
                clear * - r20664 b20665 b20666 d20655
                omega
              have d20667 : (x 12 11).toNat = 1 := by
                have r20668 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20669 := hb (x 8 4)
                have b20670 := hb (x 12 11)
                have b20671 := hb (x 11 1 && x 11 12)
                have b20672 := hb (x 10 2 && x 10 13)
                have b20673 := hb (x 9 3 && x 9 14)
                clear * - r20668 b20669 b20670 b20671 b20672 b20673 d20651 d20663 d20527 d20465
                omega
              have d20674 : (x 12 3).toNat = 1 := by
                have r20675 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
                have b20676 := hb (x 12 3)
                have b20677 := hb (x 12 11)
                clear * - r20675 b20676 b20677 d20667
                omega
              have d20678 : (x 15 12).toNat = 0 := by
                have r20679 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20680 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
                have e20681 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
                have b20682 := hb (x 12 3)
                have b20683 := hb (x 13 2)
                have b20684 := hb (x 14 13)
                have b20685 := hb (x 15 12)
                clear * - r20679 e20680 e20681 b20682 b20683 b20684 b20685 d20674
                omega
              have d20686 : (x 15 1 && x 15 12).toNat = 0 := by
                have r20687 := hand2 (x 15 1) (x 15 12)
                have b20688 := hb (x 15 12)
                have b20689 := hb (x 15 1 && x 15 12)
                clear * - r20687 b20688 b20689 d20678
                omega
              have d20690 : (x 14 13).toNat = 0 := by
                have r20691 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20692 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
                have e20693 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
                have b20694 := hb (x 12 3)
                have b20695 := hb (x 13 2)
                have b20696 := hb (x 14 13)
                have b20697 := hb (x 15 12)
                clear * - r20691 e20692 e20693 b20694 b20695 b20696 b20697 d20678 d20674
                omega
              have d20698 : (x 14 2 && x 14 13).toNat = 0 := by
                have r20699 := hand2 (x 14 2) (x 14 13)
                have b20700 := hb (x 14 13)
                have b20701 := hb (x 14 2 && x 14 13)
                clear * - r20699 b20700 b20701 d20690
                omega
              have d20702 : (x 13 2).toNat = 0 := by
                have r20703 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20704 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
                have e20705 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
                have b20706 := hb (x 12 3)
                have b20707 := hb (x 13 2)
                have b20708 := hb (x 14 13)
                have b20709 := hb (x 15 12)
                clear * - r20703 e20704 e20705 b20706 b20707 b20708 b20709 d20678 d20690 d20674
                omega
              have d20710 : (x 10 1).toNat = 1 := by
                have r20711 := hand1 (x 10 1) (x 10 14)
                have b20712 := hb (x 10 1)
                have b20713 := hb (x 10 1 && x 10 14)
                clear * - r20711 b20712 b20713 d20598
                omega
              have d20714 : (x 11 14).toNat = 0 := by
                have r20715 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20716 := hb (x 10 1)
                have b20717 := hb (x 11 14)
                clear * - r20715 b20716 b20717 d20710
                omega
              have d20718 : (x 11 1 && x 11 14).toNat = 0 := by
                have r20719 := hand2 (x 11 1) (x 11 14)
                have b20720 := hb (x 11 14)
                have b20721 := hb (x 11 1 && x 11 14)
                clear * - r20719 b20720 b20721 d20714
                omega
              have d20722 : (x 11 2).toNat = 0 := by
                have r20723 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
                have b20724 := hb (x 11 2)
                have b20725 := hb (x 11 14)
                clear * - r20723 b20724 b20725 d20714
                omega
              have d20726 : (x 10 2).toNat = 0 := by
                have r20727 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20728 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
                have e20729 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
                have b20730 := hb (x 9 3)
                have b20731 := hb (x 10 2)
                have b20732 := hb (x 11 13)
                have b20733 := hb (x 12 12)
                clear * - r20727 e20728 e20729 b20730 b20731 b20732 b20733 d20570 d20586 d20566
                omega
              have d20734 : (x 12 13).toNat = 1 := by
                have r20735 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20736 := hb (x 10 2)
                have b20737 := hb (x 12 13)
                have b20738 := hb (x 11 1 && x 11 14)
                clear * - r20735 b20736 b20737 b20738 d20718 d20726
                omega
              have d20739 : (x 12 1).toNat = 1 := by
                have r20740 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
                have b20741 := hb (x 12 1)
                have b20742 := hb (x 12 13)
                clear * - r20740 b20741 b20742 d20734
                omega
              have d20743 : (x 13 14).toNat = 0 := by
                have r20744 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20745 := hb (x 12 1)
                have b20746 := hb (x 13 14)
                clear * - r20744 b20745 b20746 d20739
                omega
              have d20747 : (x 13 1 && x 13 14).toNat = 0 := by
                have r20748 := hand2 (x 13 1) (x 13 14)
                have b20749 := hb (x 13 14)
                have b20750 := hb (x 13 1 && x 13 14)
                clear * - r20748 b20749 b20750 d20743
                omega
              have d20751 : (x 12 2).toNat = 1 := by
                have r20752 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20753 := hb (x 12 2)
                have b20754 := hb (x 14 13)
                have b20755 := hb (x 13 1 && x 13 14)
                clear * - r20752 b20753 b20754 b20755 d20690 d20747
                omega
              have d20756 : (x 14 12).toNat = 0 := by
                have r20757 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20758 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
                have e20759 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
                have b20760 := hb (x 11 3)
                have b20761 := hb (x 12 2)
                have b20762 := hb (x 13 13)
                have b20763 := hb (x 14 12)
                clear * - r20757 e20758 e20759 b20760 b20761 b20762 b20763 d20751
                omega
              have d20764 : (x 14 4).toNat = 0 := by
                have r20765 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
                have b20766 := hb (x 14 4)
                have b20767 := hb (x 14 12)
                clear * - r20765 b20766 b20767 d20756
                omega
              have d20768 : (x 14 4 && x 14 14).toNat = 0 := by
                have r20769 := hand1 (x 14 4) (x 14 14)
                have b20770 := hb (x 14 4)
                have b20771 := hb (x 14 4 && x 14 14)
                clear * - r20769 b20770 b20771 d20764
                omega
              have d20772 : (x 13 13).toNat = 0 := by
                have r20773 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20774 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
                have e20775 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
                have b20776 := hb (x 11 3)
                have b20777 := hb (x 12 2)
                have b20778 := hb (x 13 13)
                have b20779 := hb (x 14 12)
                clear * - r20773 e20774 e20775 b20776 b20777 b20778 b20779 d20756 d20751
                omega
              have d20780 : (x 13 5).toNat = 0 := by
                have r20781 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
                have b20782 := hb (x 13 5)
                have b20783 := hb (x 13 13)
                clear * - r20781 b20782 b20783 d20772
                omega
              have d20784 : (x 13 3 && x 13 14).toNat = 0 := by
                have r20785 := hand2 (x 13 3) (x 13 14)
                have b20786 := hb (x 13 14)
                have b20787 := hb (x 13 3 && x 13 14)
                clear * - r20785 b20786 b20787 d20743
                omega
              have d20788 : (x 16 11).toNat = 1 := by
                have r20789 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20790 := hb (x 12 4)
                have b20791 := hb (x 16 11)
                have b20792 := hb (x 15 1 && x 15 12)
                have b20793 := hb (x 14 2 && x 14 13)
                have b20794 := hb (x 13 3 && x 13 14)
                clear * - r20789 b20790 b20791 b20792 b20793 b20794 d20686 d20698 d20784 d20582
                omega
              have d20795 : (x 16 3).toNat = 1 := by
                have r20796 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
                have b20797 := hb (x 16 3)
                have b20798 := hb (x 16 11)
                clear * - r20796 b20797 b20798 d20788
                omega
              have d20799 : (x 19 12).toNat = 0 := by
                have r20800 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20801 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
                have e20802 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
                have b20803 := hb (x 16 3)
                have b20804 := hb (x 17 2)
                have b20805 := hb (x 18 13)
                have b20806 := hb (x 19 12)
                clear * - r20800 e20801 e20802 b20803 b20804 b20805 b20806 d20795
                omega
              have d20807 : (x 18 13).toNat = 0 := by
                have r20808 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20809 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
                have e20810 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
                have b20811 := hb (x 16 3)
                have b20812 := hb (x 17 2)
                have b20813 := hb (x 18 13)
                have b20814 := hb (x 19 12)
                clear * - r20808 e20809 e20810 b20811 b20812 b20813 b20814 d20799 d20795
                omega
              have d20815 : (x 17 2).toNat = 0 := by
                have r20816 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20817 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
                have e20818 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
                have b20819 := hb (x 16 3)
                have b20820 := hb (x 17 2)
                have b20821 := hb (x 18 13)
                have b20822 := hb (x 19 12)
                clear * - r20816 e20817 e20818 b20819 b20820 b20821 b20822 d20799 d20807 d20795
                omega
              have d20823 : (x 13 12).toNat = 0 := by
                have r20824 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20825 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
                have e20826 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
                have b20827 := hb (x 10 3)
                have b20828 := hb (x 11 2)
                have b20829 := hb (x 12 13)
                have b20830 := hb (x 13 12)
                clear * - r20824 e20825 e20826 b20827 b20828 b20829 b20830 d20734 d20722
                omega
              have d20831 : (x 13 4).toNat = 0 := by
                have r20832 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
                have b20833 := hb (x 13 4)
                have b20834 := hb (x 13 12)
                clear * - r20832 b20833 b20834 d20823
                omega
              have d20835 : (x 10 3).toNat = 0 := by
                have r20836 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20837 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
                have e20838 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
                have b20839 := hb (x 10 3)
                have b20840 := hb (x 11 2)
                have b20841 := hb (x 12 13)
                have b20842 := hb (x 13 12)
                clear * - r20836 e20837 e20838 b20839 b20840 b20841 b20842 d20823 d20734 d20722
                omega
              have d20843 : (x 10 3 && x 10 14).toNat = 0 := by
                have r20844 := hand1 (x 10 3) (x 10 14)
                have b20845 := hb (x 10 3)
                have b20846 := hb (x 10 3 && x 10 14)
                clear * - r20844 b20845 b20846 d20835
                omega
              have d20847 : (x 13 11).toNat = 1 := by
                have r20848 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20849 := hb (x 9 4)
                have b20850 := hb (x 13 11)
                have b20851 := hb (x 12 1 && x 12 12)
                have b20852 := hb (x 11 2 && x 11 13)
                have b20853 := hb (x 10 3 && x 10 14)
                clear * - r20848 b20849 b20850 b20851 b20852 b20853 d20578 d20594 d20843 d20543
                omega
              have d20854 : (x 13 3).toNat = 1 := by
                have r20855 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
                have b20856 := hb (x 13 3)
                have b20857 := hb (x 13 11)
                clear * - r20855 b20856 b20857 d20847
                omega
              have d20858 : (x 16 12).toNat = 0 := by
                have r20859 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20860 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                have e20861 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                have b20862 := hb (x 13 3)
                have b20863 := hb (x 14 2)
                have b20864 := hb (x 15 13)
                have b20865 := hb (x 16 12)
                clear * - r20859 e20860 e20861 b20862 b20863 b20864 b20865 d20854
                omega
              have d20866 : (x 16 1 && x 16 12).toNat = 0 := by
                have r20867 := hand2 (x 16 1) (x 16 12)
                have b20868 := hb (x 16 12)
                have b20869 := hb (x 16 1 && x 16 12)
                clear * - r20867 b20868 b20869 d20858
                omega
              have d20870 : (x 16 2 && x 16 12).toNat = 0 := by
                have r20871 := hand2 (x 16 2) (x 16 12)
                have b20872 := hb (x 16 12)
                have b20873 := hb (x 16 2 && x 16 12)
                clear * - r20871 b20872 b20873 d20858
                omega
              have d20874 : (x 15 13).toNat = 0 := by
                have r20875 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20876 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                have e20877 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                have b20878 := hb (x 13 3)
                have b20879 := hb (x 14 2)
                have b20880 := hb (x 15 13)
                have b20881 := hb (x 16 12)
                clear * - r20875 e20876 e20877 b20878 b20879 b20880 b20881 d20858 d20854
                omega
              have d20882 : (x 15 2 && x 15 13).toNat = 0 := by
                have r20883 := hand2 (x 15 2) (x 15 13)
                have b20884 := hb (x 15 13)
                have b20885 := hb (x 15 2 && x 15 13)
                clear * - r20883 b20884 b20885 d20874
                omega
              have d20886 : (x 15 3 && x 15 13).toNat = 0 := by
                have r20887 := hand2 (x 15 3) (x 15 13)
                have b20888 := hb (x 15 13)
                have b20889 := hb (x 15 3 && x 15 13)
                clear * - r20887 b20888 b20889 d20874
                omega
              have d20890 : (x 14 1 && x 14 14).toNat = 1 := by
                have r20891 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20892 := hb (x 13 2)
                have b20893 := hb (x 15 13)
                have b20894 := hb (x 14 1 && x 14 14)
                clear * - r20891 b20892 b20893 b20894 d20874 d20702
                omega
              have d20895 : (x 14 1).toNat = 1 := by
                have r20896 := hand1 (x 14 1) (x 14 14)
                have b20897 := hb (x 14 1)
                have b20898 := hb (x 14 1 && x 14 14)
                clear * - r20896 b20897 b20898 d20890
                omega
              have d20899 : (x 15 14).toNat = 0 := by
                have r20900 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20901 := hb (x 14 1)
                have b20902 := hb (x 15 14)
                clear * - r20900 b20901 b20902 d20895
                omega
              have d20903 : (x 15 1 && x 15 14).toNat = 0 := by
                have r20904 := hand2 (x 15 1) (x 15 14)
                have b20905 := hb (x 15 14)
                have b20906 := hb (x 15 1 && x 15 14)
                clear * - r20904 b20905 b20906 d20899
                omega
              have d20907 : (x 15 2).toNat = 0 := by
                have r20908 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
                have b20909 := hb (x 15 2)
                have b20910 := hb (x 15 14)
                clear * - r20908 b20909 b20910 d20899
                omega
              have d20911 : (x 14 2).toNat = 0 := by
                have r20912 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20913 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                have e20914 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                have b20915 := hb (x 13 3)
                have b20916 := hb (x 14 2)
                have b20917 := hb (x 15 13)
                have b20918 := hb (x 16 12)
                clear * - r20912 e20913 e20914 b20915 b20916 b20917 b20918 d20858 d20874 d20854
                omega
              have d20919 : (x 16 13).toNat = 1 := by
                have r20920 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20921 := hb (x 14 2)
                have b20922 := hb (x 16 13)
                have b20923 := hb (x 15 1 && x 15 14)
                clear * - r20920 b20921 b20922 b20923 d20903 d20911
                omega
              have d20924 : (x 17 12).toNat = 0 := by
                have r20925 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20926 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                have e20927 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                have b20928 := hb (x 14 3)
                have b20929 := hb (x 15 2)
                have b20930 := hb (x 16 13)
                have b20931 := hb (x 17 12)
                clear * - r20925 e20926 e20927 b20928 b20929 b20930 b20931 d20919 d20907
                omega
              have d20932 : (x 14 3).toNat = 0 := by
                have r20933 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20934 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                have e20935 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                have b20936 := hb (x 14 3)
                have b20937 := hb (x 15 2)
                have b20938 := hb (x 16 13)
                have b20939 := hb (x 17 12)
                clear * - r20933 e20934 e20935 b20936 b20937 b20938 b20939 d20924 d20919 d20907
                omega
              have d20940 : (x 14 3 && x 14 14).toNat = 0 := by
                have r20941 := hand1 (x 14 3) (x 14 14)
                have b20942 := hb (x 14 3)
                have b20943 := hb (x 14 3 && x 14 14)
                clear * - r20941 b20942 b20943 d20932
                omega
              have d20944 : (x 17 11).toNat = 1 := by
                have r20945 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20946 := hb (x 13 4)
                have b20947 := hb (x 17 11)
                have b20948 := hb (x 16 1 && x 16 12)
                have b20949 := hb (x 15 2 && x 15 13)
                have b20950 := hb (x 14 3 && x 14 14)
                clear * - r20945 b20946 b20947 b20948 b20949 b20950 d20866 d20882 d20940 d20831
                omega
              have d20951 : (x 17 3).toNat = 1 := by
                have r20952 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
                have b20953 := hb (x 17 3)
                have b20954 := hb (x 17 11)
                clear * - r20952 b20953 b20954 d20944
                omega
              have d20955 : (x 20 12).toNat = 0 := by
                have r20956 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20957 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
                have e20958 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
                have b20959 := hb (x 17 3)
                have b20960 := hb (x 18 2)
                have b20961 := hb (x 19 13)
                have b20962 := hb (x 20 12)
                clear * - r20956 e20957 e20958 b20959 b20960 b20961 b20962 d20951
                omega
              have d20963 : (x 19 13).toNat = 0 := by
                have r20964 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20965 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
                have e20966 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
                have b20967 := hb (x 17 3)
                have b20968 := hb (x 18 2)
                have b20969 := hb (x 19 13)
                have b20970 := hb (x 20 12)
                clear * - r20964 e20965 e20966 b20967 b20968 b20969 b20970 d20955 d20951
                omega
              have d20971 : (x 18 1 && x 18 14).toNat = 1 := by
                have r20972 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20973 := hb (x 17 2)
                have b20974 := hb (x 19 13)
                have b20975 := hb (x 18 1 && x 18 14)
                clear * - r20972 b20973 b20974 b20975 d20963 d20815
                omega
              have d20976 : (x 18 14).toNat = 1 := by
                have r20977 := hand2 (x 18 1) (x 18 14)
                have b20978 := hb (x 18 14)
                have b20979 := hb (x 18 1 && x 18 14)
                clear * - r20977 b20978 b20979 d20971
                omega
              have d20980 : (x 17 1).toNat = 0 := by
                have r20981 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20982 := hb (x 17 1)
                have b20983 := hb (x 18 14)
                clear * - r20981 b20982 b20983 d20976
                omega
              have d20984 : (x 17 1 && x 17 11).toNat = 0 := by
                have r20985 := hand1 (x 17 1) (x 17 11)
                have b20986 := hb (x 17 1)
                have b20987 := hb (x 17 1 && x 17 11)
                clear * - r20985 b20986 b20987 d20980
                omega
              have d20988 : (x 18 2).toNat = 0 := by
                have r20989 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20990 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
                have e20991 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
                have b20992 := hb (x 17 3)
                have b20993 := hb (x 18 2)
                have b20994 := hb (x 19 13)
                have b20995 := hb (x 20 12)
                clear * - r20989 e20990 e20991 b20992 b20993 b20994 b20995 d20955 d20963 d20951
                omega
              have d20996 : (x 18 10).toNat = 0 := by
                have r20997 : (x 18 10).toNat ≤ (x 18 2).toNat := himp _ _ (hp10 18)
                have b20998 := hb (x 18 2)
                have b20999 := hb (x 18 10)
                clear * - r20997 b20998 b20999 d20988
                omega
              have r21000 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := by have q := hcov10 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21001 := hb (x 13 5)
              have b21002 := hb (x 18 10)
              have b21003 := hb (x 17 1 && x 17 11)
              have b21004 := hb (x 16 2 && x 16 12)
              have b21005 := hb (x 15 3 && x 15 13)
              have b21006 := hb (x 14 4 && x 14 14)
              linarith only [r21000, b21001, b21002, b21003, b21004, b21005, b21006, d20996, d20984, d20870, d20886, d20768, d20780]
          · have f21007 : (x 1 1).toNat = 1 := by rw [h17799]; rfl
            have d21008 : (x 2 14).toNat = 0 := by
              have r21009 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21010 := hb (x 1 1)
              have b21011 := hb (x 2 14)
              clear * - r21009 b21010 b21011 f21007
              omega
            have d21012 : (x 2 1 && x 2 14).toNat = 0 := by
              have r21013 := hand2 (x 2 1) (x 2 14)
              have b21014 := hb (x 2 14)
              have b21015 := hb (x 2 1 && x 2 14)
              clear * - r21013 b21014 b21015 d21008
              omega
            have d21016 : (x 2 2).toNat = 0 := by
              have r21017 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
              have b21018 := hb (x 2 2)
              have b21019 := hb (x 2 14)
              clear * - r21017 b21018 b21019 d21008
              omega
            have d21020 : (x 2 10).toNat = 0 := by
              have r21021 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
              have b21022 := hb (x 2 2)
              have b21023 := hb (x 2 10)
              clear * - r21021 b21022 b21023 d21016
              omega
            have d21024 : (x 2 1 && x 2 10).toNat = 0 := by
              have r21025 := hand2 (x 2 1) (x 2 10)
              have b21026 := hb (x 2 10)
              have b21027 := hb (x 2 1 && x 2 10)
              clear * - r21025 b21026 b21027 d21020
              omega
            have d21028 : (x 2 9 && x 2 10).toNat = 0 := by
              have r21029 := hand2 (x 2 9) (x 2 10)
              have b21030 := hb (x 2 10)
              have b21031 := hb (x 2 9 && x 2 10)
              clear * - r21029 b21030 b21031 d21020
              omega
            have d21032 : (x 3 13).toNat = 1 := by
              have r21033 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21034 := hb (x 1 2)
              have b21035 := hb (x 3 13)
              have b21036 := hb (x 2 1 && x 2 14)
              clear * - r21033 b21034 b21035 b21036 d21012 g23
              omega
            have d21037 : (x 3 1).toNat = 1 := by
              have r21038 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
              have b21039 := hb (x 3 1)
              have b21040 := hb (x 3 13)
              clear * - r21038 b21039 b21040 d21032
              omega
            have d21041 : (x 4 14).toNat = 0 := by
              have r21042 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21043 := hb (x 3 1)
              have b21044 := hb (x 4 14)
              clear * - r21042 b21043 b21044 d21037
              omega
            have d21045 : (x 4 1 && x 4 14).toNat = 0 := by
              have r21046 := hand2 (x 4 1) (x 4 14)
              have b21047 := hb (x 4 14)
              have b21048 := hb (x 4 1 && x 4 14)
              clear * - r21046 b21047 b21048 d21041
              omega
            have d21049 : (x 4 2).toNat = 0 := by
              have r21050 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
              have b21051 := hb (x 4 2)
              have b21052 := hb (x 4 14)
              clear * - r21050 b21051 b21052 d21041
              omega
            have d21053 : (x 4 10).toNat = 0 := by
              have r21054 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
              have b21055 := hb (x 4 2)
              have b21056 := hb (x 4 10)
              clear * - r21054 b21055 b21056 d21049
              omega
            have d21057 : (x 4 12).toNat = 0 := by
              have r21058 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21059 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e21060 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b21061 := hb (x 1 3)
              have b21062 := hb (x 2 2)
              have b21063 := hb (x 3 13)
              have b21064 := hb (x 4 12)
              clear * - r21058 e21059 e21060 b21061 b21062 b21063 b21064 d21032 d21016
              omega
            have d21065 : (x 1 3).toNat = 0 := by
              have r21066 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21067 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e21068 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b21069 := hb (x 1 3)
              have b21070 := hb (x 2 2)
              have b21071 := hb (x 3 13)
              have b21072 := hb (x 4 12)
              clear * - r21066 e21067 e21068 b21069 b21070 b21071 b21072 d21057 d21032 d21016
              omega
            have d21073 : (x 1 11).toNat = 0 := by
              have r21074 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
              have b21075 := hb (x 1 3)
              have b21076 := hb (x 1 11)
              clear * - r21074 b21075 b21076 d21065
              omega
            have d21077 : (x 3 1 && x 3 11).toNat = 1 := by
              have r21078 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21079 := hb (x (-1) 5)
              have b21080 := hb (x 4 10)
              have b21081 := hb (x 3 1 && x 3 11)
              have b21082 := hb (x 2 2 && x 2 12)
              have b21083 := hb (x 1 3 && x 1 13)
              have b21084 := hb (x 0 4 && x 0 14)
              clear * - r21078 b21079 b21080 b21081 b21082 b21083 b21084 d21053 g78 g79 g80 g8
              omega
            have d21085 : (x 3 11).toNat = 1 := by
              have r21086 := hand2 (x 3 1) (x 3 11)
              have b21087 := hb (x 3 11)
              have b21088 := hb (x 3 1 && x 3 11)
              clear * - r21086 b21087 b21088 d21077
              omega
            have d21089 : (x 3 3).toNat = 1 := by
              have r21090 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
              have b21091 := hb (x 3 3)
              have b21092 := hb (x 3 11)
              clear * - r21090 b21091 b21092 d21085
              omega
            have d21093 : (x 6 12).toNat = 0 := by
              have r21094 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21095 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
              have e21096 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
              have b21097 := hb (x 3 3)
              have b21098 := hb (x 4 2)
              have b21099 := hb (x 5 13)
              have b21100 := hb (x 6 12)
              clear * - r21094 e21095 e21096 b21097 b21098 b21099 b21100 d21049 d21089
              omega
            have d21101 : (x 5 13).toNat = 0 := by
              have r21102 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21103 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
              have e21104 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
              have b21105 := hb (x 3 3)
              have b21106 := hb (x 4 2)
              have b21107 := hb (x 5 13)
              have b21108 := hb (x 6 12)
              clear * - r21102 e21103 e21104 b21105 b21106 b21107 b21108 d21093 d21049 d21089
              omega
            have d21109 : (x 3 2).toNat = 1 := by
              have r21110 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21111 := hb (x 3 2)
              have b21112 := hb (x 5 13)
              have b21113 := hb (x 4 1 && x 4 14)
              clear * - r21110 b21111 b21112 b21113 d21101 d21045
              omega
            have d21114 : (x 3 14).toNat = 1 := by
              have r21115 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
              have b21116 := hb (x 3 2)
              have b21117 := hb (x 3 14)
              clear * - r21115 b21116 b21117 d21109
              omega
            have d21118 : (x 2 1).toNat = 0 := by
              have r21119 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21120 := hb (x 2 1)
              have b21121 := hb (x 3 14)
              clear * - r21119 b21120 b21121 d21114
              omega
            have d21122 : (x 2 13).toNat = 0 := by
              have r21123 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
              have b21124 := hb (x 2 1)
              have b21125 := hb (x 2 13)
              clear * - r21123 b21124 b21125 d21118
              omega
            have d21126 : (x 2 5).toNat = 0 := by
              have r21127 : (x 2 5).toNat ≤ (x 2 13).toNat := himp _ _ (hp5 2)
              have b21128 := hb (x 2 5)
              have b21129 := hb (x 2 13)
              clear * - r21127 b21128 b21129 d21122
              omega
            have d21130 : (x 2 9).toNat = 0 := by
              have r21131 : (x 2 9).toNat ≤ (x 2 1).toNat := himp _ _ (hp9 2)
              have b21132 := hb (x 2 1)
              have b21133 := hb (x 2 9)
              clear * - r21131 b21132 b21133 d21118
              omega
            have r21134 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r21135 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r21136 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r21137 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e21138 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e21139 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e21140 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e21141 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e21142 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e21143 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have r21144 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e21145 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
            have e21146 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
            have e21147 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
            have e21148 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
            have e21149 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
            have e21150 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
            have r21151 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e21152 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e21153 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have r21154 : 1 ≤ (x 11 1).toNat + (x 10 1 && x 10 2).toNat + (x 9 2 && x 9 3).toNat + (x 8 3 && x 8 4).toNat + (x 7 4 && x 7 5).toNat + (x 6 5 && x 6 6).toNat + (x 5 6 && x 5 7).toNat + (x 4 7 && x 4 8).toNat + (x 3 8 && x 3 9).toNat + (x 2 9 && x 2 10).toNat + (x 1 10 && x 1 11).toNat + (x 0 11 && x 0 12).toNat + (x (-1) 12 && x (-1) 13).toNat + (x (-2) 13 && x (-2) 14).toNat + (x (-3) 14).toNat := by have q := hcov1 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r21155 : 1 ≤ (x 1 2).toNat + (x 0 1 && x 0 3).toNat + (x (-1) 2 && x (-1) 4).toNat + (x (-2) 3 && x (-2) 5).toNat + (x (-3) 4 && x (-3) 6).toNat + (x (-4) 5 && x (-4) 7).toNat + (x (-5) 6 && x (-5) 8).toNat + (x (-6) 7 && x (-6) 9).toNat + (x (-7) 8 && x (-7) 10).toNat + (x (-8) 9 && x (-8) 11).toNat + (x (-9) 10 && x (-9) 12).toNat + (x (-10) 11 && x (-10) 13).toNat + (x (-11) 12 && x (-11) 14).toNat + (x (-12) 13).toNat := by have q := hcov2 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r21156 : 1 ≤ (x 2 5).toNat + (x 1 1 && x 1 6).toNat + (x 0 2 && x 0 7).toNat + (x (-1) 3 && x (-1) 8).toNat + (x (-2) 4 && x (-2) 9).toNat + (x (-3) 5 && x (-3) 10).toNat + (x (-4) 6 && x (-4) 11).toNat + (x (-5) 7 && x (-5) 12).toNat + (x (-6) 8 && x (-6) 13).toNat + (x (-7) 9 && x (-7) 14).toNat + (x (-8) 10).toNat := by have q := hcov5 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r21157 : 1 ≤ (x 2 9).toNat + (x 1 1 && x 1 10).toNat + (x 0 2 && x 0 11).toNat + (x (-1) 3 && x (-1) 12).toNat + (x (-2) 4 && x (-2) 13).toNat + (x (-3) 5 && x (-3) 14).toNat + (x (-4) 6).toNat := by have q := hcov9 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r21158 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r21159 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r21160 : 1 ≤ (x (-11) 13).toNat + (x (-12) 1 && x (-12) 14).toNat + (x (-13) 2).toNat := by have q := hcov13 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r21161 : (x (-13) 2).toNat ≤ (x (-13) 14).toNat := himp _ _ (hp2 (-13))
            have r21162 := hand2 (x 10 1) (x 10 2)
            have r21163 := hand2 (x 9 2) (x 9 3)
            have r21164 := hand2 (x 8 3) (x 8 4)
            have r21165 := hand2 (x 7 4) (x 7 5)
            have r21166 := hand2 (x 6 5) (x 6 6)
            have r21167 := hand2 (x 5 6) (x 5 7)
            have r21168 := hand2 (x 4 7) (x 4 8)
            have r21169 := hand1 (x 3 8) (x 3 9)
            have r21170 := hand1 (x (-2) 13) (x (-2) 14)
            have r21171 := hand2 (x (-4) 5) (x (-4) 7)
            have r21172 := hand1 (x (-7) 8) (x (-7) 10)
            have r21173 := hand1 (x (-8) 9) (x (-8) 11)
            have r21174 := hand1 (x (-9) 10) (x (-9) 12)
            have r21175 := hand1 (x (-10) 11) (x (-10) 13)
            have r21176 := hand1 (x (-11) 12) (x (-11) 14)
            have r21177 := hand2 (x (-2) 4) (x (-2) 9)
            have r21178 := hand2 (x (-4) 6) (x (-4) 11)
            have r21179 := hand1 (x (-5) 7) (x (-5) 12)
            have r21180 := hand1 (x (-6) 8) (x (-6) 13)
            have r21181 := hand1 (x (-7) 9) (x (-7) 14)
            have r21182 := hand1 (x (-2) 4) (x (-2) 13)
            have r21183 := hand1 (x (-2) 5) (x (-2) 14)
            have r21184 := hand1 (x (-4) 3) (x (-4) 13)
            have r21185 := hand1 (x (-5) 4) (x (-5) 14)
            have r21186 := hand2 (x (-12) 1) (x (-12) 14)
            linarith only [r21134, r21135, r21136, r21137, e21138, e21139, e21140, e21141, e21142, e21143, r21144, e21145, e21146, e21147, e21148, e21149, e21150, r21151, e21152, e21153, r21154, r21155, r21156, r21157, r21158, r21159, r21160, r21161, r21162, r21163, r21164, r21165, r21166, r21167, r21168, r21169, r21170, r21171, r21172, r21173, r21174, r21175, r21176, r21177, r21178, r21179, r21180, r21181, r21182, r21183, r21184, r21185, r21186, d17777, d17757, d17603, d17623, d17704, d17672, d17615, d17643, d17591, g4, d17660, g6, g7, g10, g12, g13, g14, g19, g20, f21007, g23, g27, d21073, d21126, d21130, d21020, d21028, g33, g34, g35, g36, g37, g38, d17619, d17773, d17793, g49, d17568, g50, d17651, g64, g65, g66, d17611, d21024, g67, g68, g69, g72, d17631]
        · have f21303 : (x 0 10).toNat = 1 := by rw [h17797]; rfl
          have d21304 : (x 2 8).toNat = 0 := by
            have r21305 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e21306 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
            have e21307 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
            have e21308 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
            have e21309 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
            have e21310 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
            have e21311 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
            have b21312 := hb (x (-5) 7)
            have b21313 := hb (x (-4) 6)
            have b21314 := hb (x (-3) 5)
            have b21315 := hb (x (-2) 4)
            have b21316 := hb (x (-1) 11)
            have b21317 := hb (x 0 10)
            have b21318 := hb (x 1 9)
            have b21319 := hb (x 2 8)
            clear * - r21305 e21306 e21307 e21308 e21309 e21310 e21311 b21312 b21313 b21314 b21315 b21316 b21317 b21318 b21319 f21303 g11 d17672
            omega
          have d21320 : (x 1 9).toNat = 0 := by
            have r21321 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e21322 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
            have e21323 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
            have e21324 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
            have e21325 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
            have e21326 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
            have e21327 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
            have b21328 := hb (x (-5) 7)
            have b21329 := hb (x (-4) 6)
            have b21330 := hb (x (-3) 5)
            have b21331 := hb (x (-2) 4)
            have b21332 := hb (x (-1) 11)
            have b21333 := hb (x 0 10)
            have b21334 := hb (x 1 9)
            have b21335 := hb (x 2 8)
            clear * - r21321 e21322 e21323 e21324 e21325 e21326 e21327 b21328 b21329 b21330 b21331 b21332 b21333 b21334 b21335 d21304 f21303 g11 d17672
            omega
          have d21336 : (x (-2) 4).toNat = 0 := by
            have r21337 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e21338 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
            have e21339 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
            have e21340 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
            have e21341 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
            have e21342 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
            have e21343 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
            have b21344 := hb (x (-5) 7)
            have b21345 := hb (x (-4) 6)
            have b21346 := hb (x (-3) 5)
            have b21347 := hb (x (-2) 4)
            have b21348 := hb (x (-1) 11)
            have b21349 := hb (x 0 10)
            have b21350 := hb (x 1 9)
            have b21351 := hb (x 2 8)
            clear * - r21337 e21338 e21339 e21340 e21341 e21342 e21343 b21344 b21345 b21346 b21347 b21348 b21349 b21350 b21351 d21304 d21320 f21303 g11 d17672
            omega
          have d21352 : (x (-2) 4 && x (-2) 13).toNat = 0 := by
            have r21353 := hand1 (x (-2) 4) (x (-2) 13)
            have b21354 := hb (x (-2) 4)
            have b21355 := hb (x (-2) 4 && x (-2) 13)
            clear * - r21353 b21354 b21355 d21336
            omega
          have d21356 : (x (-4) 6).toNat = 0 := by
            have r21357 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e21358 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
            have e21359 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
            have e21360 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
            have e21361 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
            have e21362 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
            have e21363 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
            have b21364 := hb (x (-5) 7)
            have b21365 := hb (x (-4) 6)
            have b21366 := hb (x (-3) 5)
            have b21367 := hb (x (-2) 4)
            have b21368 := hb (x (-1) 11)
            have b21369 := hb (x 0 10)
            have b21370 := hb (x 1 9)
            have b21371 := hb (x 2 8)
            clear * - r21357 e21358 e21359 e21360 e21361 e21362 e21363 b21364 b21365 b21366 b21367 b21368 b21369 b21370 b21371 d21304 d21320 f21303 g11 d21336 d17672
            omega
          have d21372 : (x 2 9).toNat = 1 := by
            have r21373 : 1 ≤ (x 2 9).toNat + (x 1 1 && x 1 10).toNat + (x 0 2 && x 0 11).toNat + (x (-1) 3 && x (-1) 12).toNat + (x (-2) 4 && x (-2) 13).toNat + (x (-3) 5 && x (-3) 14).toNat + (x (-4) 6).toNat := by have q := hcov9 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b21374 := hb (x (-4) 6)
            have b21375 := hb (x 2 9)
            have b21376 := hb (x 1 1 && x 1 10)
            have b21377 := hb (x 0 2 && x 0 11)
            have b21378 := hb (x (-1) 3 && x (-1) 12)
            have b21379 := hb (x (-2) 4 && x (-2) 13)
            have b21380 := hb (x (-3) 5 && x (-3) 14)
            clear * - r21373 b21374 b21375 b21376 b21377 b21378 b21379 b21380 g64 g65 g66 d21352 d17611 d21356
            omega
          have d21381 : (x 2 1).toNat = 1 := by
            have r21382 : (x 2 9).toNat ≤ (x 2 1).toNat := himp _ _ (hp9 2)
            have b21383 := hb (x 2 1)
            have b21384 := hb (x 2 9)
            clear * - r21382 b21383 b21384 d21372
            omega
          have d21385 : (x 3 14).toNat = 0 := by
            have r21386 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b21387 := hb (x 2 1)
            have b21388 := hb (x 3 14)
            clear * - r21386 b21387 b21388 d21381
            omega
          have d21389 : (x 3 2).toNat = 0 := by
            have r21390 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
            have b21391 := hb (x 3 2)
            have b21392 := hb (x 3 14)
            clear * - r21390 b21391 b21392 d21385
            omega
          have d21393 : (x 3 8).toNat = 0 := by
            have r21394 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e21395 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
            have e21396 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
            have e21397 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
            have e21398 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
            have e21399 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
            have e21400 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
            have b21401 := hb (x (-4) 7)
            have b21402 := hb (x (-3) 6)
            have b21403 := hb (x (-2) 5)
            have b21404 := hb (x (-1) 4)
            have b21405 := hb (x 0 11)
            have b21406 := hb (x 1 10)
            have b21407 := hb (x 2 9)
            have b21408 := hb (x 3 8)
            clear * - r21394 e21395 e21396 e21397 e21398 e21399 e21400 b21401 b21402 b21403 b21404 b21405 b21406 b21407 b21408 d21372 g27 g19 d17615
            omega
          have d21409 : (x (-1) 4).toNat = 0 := by
            have r21410 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e21411 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
            have e21412 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
            have e21413 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
            have e21414 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
            have e21415 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
            have e21416 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
            have b21417 := hb (x (-4) 7)
            have b21418 := hb (x (-3) 6)
            have b21419 := hb (x (-2) 5)
            have b21420 := hb (x (-1) 4)
            have b21421 := hb (x 0 11)
            have b21422 := hb (x 1 10)
            have b21423 := hb (x 2 9)
            have b21424 := hb (x 3 8)
            clear * - r21410 e21411 e21412 e21413 e21414 e21415 e21416 b21417 b21418 b21419 b21420 b21421 b21422 b21423 b21424 d21393 d21372 g27 g19 d17615
            omega
          have d21425 : (x 3 11).toNat = 1 := by
            have r21426 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b21427 := hb (x (-1) 4)
            have b21428 := hb (x 3 11)
            have b21429 := hb (x 2 1 && x 2 12)
            have b21430 := hb (x 1 2 && x 1 13)
            have b21431 := hb (x 0 3 && x 0 14)
            clear * - r21426 b21427 b21428 b21429 b21430 b21431 g84 g85 g86 d21409
            omega
          have d21432 : (x 3 3).toNat = 1 := by
            have r21433 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
            have b21434 := hb (x 3 3)
            have b21435 := hb (x 3 11)
            clear * - r21433 b21434 b21435 d21425
            omega
          have d21436 : (x 6 12).toNat = 0 := by
            have r21437 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e21438 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
            have e21439 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
            have b21440 := hb (x 3 3)
            have b21441 := hb (x 4 2)
            have b21442 := hb (x 5 13)
            have b21443 := hb (x 6 12)
            clear * - r21437 e21438 e21439 b21440 b21441 b21442 b21443 d21432
            omega
          have d21444 : (x 5 13).toNat = 0 := by
            have r21445 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e21446 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
            have e21447 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
            have b21448 := hb (x 3 3)
            have b21449 := hb (x 4 2)
            have b21450 := hb (x 5 13)
            have b21451 := hb (x 6 12)
            clear * - r21445 e21446 e21447 b21448 b21449 b21450 b21451 d21436 d21432
            omega
          have d21452 : (x 4 1 && x 4 14).toNat = 1 := by
            have r21453 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b21454 := hb (x 3 2)
            have b21455 := hb (x 5 13)
            have b21456 := hb (x 4 1 && x 4 14)
            clear * - r21453 b21454 b21455 b21456 d21444 d21389
            omega
          have d21457 : (x 4 14).toNat = 1 := by
            have r21458 := hand2 (x 4 1) (x 4 14)
            have b21459 := hb (x 4 14)
            have b21460 := hb (x 4 1 && x 4 14)
            clear * - r21458 b21459 b21460 d21452
            omega
          have d21461 : (x 3 1).toNat = 0 := by
            have r21462 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b21463 := hb (x 3 1)
            have b21464 := hb (x 4 14)
            clear * - r21462 b21463 b21464 d21457
            omega
          have d21465 : (x 3 1 && x 3 11).toNat = 0 := by
            have r21466 := hand1 (x 3 1) (x 3 11)
            have b21467 := hb (x 3 1)
            have b21468 := hb (x 3 1 && x 3 11)
            clear * - r21466 b21467 b21468 d21461
            omega
          have d21469 : (x 4 10).toNat = 1 := by
            have r21470 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b21471 := hb (x (-1) 5)
            have b21472 := hb (x 4 10)
            have b21473 := hb (x 3 1 && x 3 11)
            have b21474 := hb (x 2 2 && x 2 12)
            have b21475 := hb (x 1 3 && x 1 13)
            have b21476 := hb (x 0 4 && x 0 14)
            clear * - r21470 b21471 b21472 b21473 b21474 b21475 b21476 d21465 g78 g79 g80 g8
            omega
          have d21477 : (x 4 2).toNat = 1 := by
            have r21478 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
            have b21479 := hb (x 4 2)
            have b21480 := hb (x 4 10)
            clear * - r21478 b21479 b21480 d21469
            omega
          have r21481 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21482 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e21483 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b21484 := hb (x 3 3)
          have b21485 := hb (x 4 2)
          have b21486 := hb (x 5 13)
          have b21487 := hb (x 6 12)
          linarith only [r21481, e21482, e21483, b21484, b21485, b21486, b21487, d21436, d21444, d21477, d21432]
      · have f21488 : (x 0 9).toNat = 1 := by rw [h17572]; rfl
        have d21489 : (x 1 8).toNat = 0 := by
          have r21490 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21491 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e21492 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e21493 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e21494 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e21495 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e21496 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b21497 := hb (x (-6) 7)
          have b21498 := hb (x (-5) 6)
          have b21499 := hb (x (-4) 5)
          have b21500 := hb (x (-3) 4)
          have b21501 := hb (x (-2) 11)
          have b21502 := hb (x (-1) 10)
          have b21503 := hb (x 0 9)
          have b21504 := hb (x 1 8)
          clear * - r21490 e21491 e21492 e21493 e21494 e21495 e21496 b21497 b21498 b21499 b21500 b21501 b21502 b21503 b21504 f21488 g10 g5
          omega
        have d21505 : (x (-3) 4).toNat = 0 := by
          have r21506 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21507 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e21508 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e21509 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e21510 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e21511 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e21512 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b21513 := hb (x (-6) 7)
          have b21514 := hb (x (-5) 6)
          have b21515 := hb (x (-4) 5)
          have b21516 := hb (x (-3) 4)
          have b21517 := hb (x (-2) 11)
          have b21518 := hb (x (-1) 10)
          have b21519 := hb (x 0 9)
          have b21520 := hb (x 1 8)
          clear * - r21506 e21507 e21508 e21509 e21510 e21511 e21512 b21513 b21514 b21515 b21516 b21517 b21518 b21519 b21520 d21489 f21488 g10 g5
          omega
        have d21521 : (x (-3) 4 && x (-3) 14).toNat = 0 := by
          have r21522 := hand1 (x (-3) 4) (x (-3) 14)
          have b21523 := hb (x (-3) 4)
          have b21524 := hb (x (-3) 4 && x (-3) 14)
          clear * - r21522 b21523 b21524 d21505
          omega
        have d21525 : (x (-4) 5).toNat = 1 := by
          have r21526 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21527 := hb (x (-4) 5)
          have b21528 := hb (x 1 10)
          have b21529 := hb (x 0 1 && x 0 11)
          have b21530 := hb (x (-1) 2 && x (-1) 12)
          have b21531 := hb (x (-2) 3 && x (-2) 13)
          have b21532 := hb (x (-3) 4 && x (-3) 14)
          clear * - r21526 b21527 b21528 b21529 b21530 b21531 b21532 g27 g73 g74 g75 d21521
          omega
        have r21533 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21534 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
        have e21535 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
        have e21536 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
        have e21537 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
        have e21538 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
        have e21539 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
        have b21540 := hb (x (-6) 7)
        have b21541 := hb (x (-5) 6)
        have b21542 := hb (x (-4) 5)
        have b21543 := hb (x (-3) 4)
        have b21544 := hb (x (-2) 11)
        have b21545 := hb (x (-1) 10)
        have b21546 := hb (x 0 9)
        have b21547 := hb (x 1 8)
        linarith only [r21533, e21534, e21535, e21536, e21537, e21538, e21539, b21540, b21541, b21542, b21543, b21544, b21545, b21546, b21547, d21489, f21488, g10, g5, d21505, d21525]
    · have f21548 : (x 0 7).toNat = 1 := by rw [h17562]; rfl
      have d21549 : (x 7 8).toNat = 0 := by
        have r21550 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21551 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e21552 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e21553 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e21554 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e21555 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e21556 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b21557 := hb (x 0 7)
        have b21558 := hb (x 1 6)
        have b21559 := hb (x 2 5)
        have b21560 := hb (x 3 4)
        have b21561 := hb (x 4 11)
        have b21562 := hb (x 5 10)
        have b21563 := hb (x 6 9)
        have b21564 := hb (x 7 8)
        clear * - r21550 e21551 e21552 e21553 e21554 e21555 e21556 b21557 b21558 b21559 b21560 b21561 b21562 b21563 b21564 g26 f21548
        omega
      have d21565 : (x 7 1 && x 7 8).toNat = 0 := by
        have r21566 := hand2 (x 7 1) (x 7 8)
        have b21567 := hb (x 7 8)
        have b21568 := hb (x 7 1 && x 7 8)
        clear * - r21566 b21567 b21568 d21549
        omega
      have d21569 : (x 7 3 && x 7 8).toNat = 0 := by
        have r21570 := hand2 (x 7 3) (x 7 8)
        have b21571 := hb (x 7 8)
        have b21572 := hb (x 7 3 && x 7 8)
        clear * - r21570 b21571 b21572 d21549
        omega
      have d21573 : (x 6 9).toNat = 0 := by
        have r21574 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21575 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e21576 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e21577 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e21578 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e21579 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e21580 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b21581 := hb (x 0 7)
        have b21582 := hb (x 1 6)
        have b21583 := hb (x 2 5)
        have b21584 := hb (x 3 4)
        have b21585 := hb (x 4 11)
        have b21586 := hb (x 5 10)
        have b21587 := hb (x 6 9)
        have b21588 := hb (x 7 8)
        clear * - r21574 e21575 e21576 e21577 e21578 e21579 e21580 b21581 b21582 b21583 b21584 b21585 b21586 b21587 b21588 d21549 g26 f21548
        omega
      have d21589 : (x 6 2 && x 6 9).toNat = 0 := by
        have r21590 := hand2 (x 6 2) (x 6 9)
        have b21591 := hb (x 6 9)
        have b21592 := hb (x 6 2 && x 6 9)
        clear * - r21590 b21591 b21592 d21573
        omega
      have d21593 : (x 6 4 && x 6 9).toNat = 0 := by
        have r21594 := hand2 (x 6 4) (x 6 9)
        have b21595 := hb (x 6 9)
        have b21596 := hb (x 6 4 && x 6 9)
        clear * - r21594 b21595 b21596 d21573
        omega
      have d21597 : (x 5 10).toNat = 0 := by
        have r21598 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21599 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e21600 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e21601 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e21602 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e21603 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e21604 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b21605 := hb (x 0 7)
        have b21606 := hb (x 1 6)
        have b21607 := hb (x 2 5)
        have b21608 := hb (x 3 4)
        have b21609 := hb (x 4 11)
        have b21610 := hb (x 5 10)
        have b21611 := hb (x 6 9)
        have b21612 := hb (x 7 8)
        clear * - r21598 e21599 e21600 e21601 e21602 e21603 e21604 b21605 b21606 b21607 b21608 b21609 b21610 b21611 b21612 d21549 d21573 g26 f21548
        omega
      have d21613 : (x 5 1 && x 5 10).toNat = 0 := by
        have r21614 := hand2 (x 5 1) (x 5 10)
        have b21615 := hb (x 5 10)
        have b21616 := hb (x 5 1 && x 5 10)
        clear * - r21614 b21615 b21616 d21597
        omega
      have d21617 : (x 5 3 && x 5 10).toNat = 0 := by
        have r21618 := hand2 (x 5 3) (x 5 10)
        have b21619 := hb (x 5 10)
        have b21620 := hb (x 5 3 && x 5 10)
        clear * - r21618 b21619 b21620 d21597
        omega
      have d21621 : (x 5 5 && x 5 10).toNat = 0 := by
        have r21622 := hand2 (x 5 5) (x 5 10)
        have b21623 := hb (x 5 10)
        have b21624 := hb (x 5 5 && x 5 10)
        clear * - r21622 b21623 b21624 d21597
        omega
      have d21625 : (x 4 11).toNat = 0 := by
        have r21626 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21627 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e21628 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e21629 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e21630 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e21631 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e21632 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b21633 := hb (x 0 7)
        have b21634 := hb (x 1 6)
        have b21635 := hb (x 2 5)
        have b21636 := hb (x 3 4)
        have b21637 := hb (x 4 11)
        have b21638 := hb (x 5 10)
        have b21639 := hb (x 6 9)
        have b21640 := hb (x 7 8)
        clear * - r21626 e21627 e21628 e21629 e21630 e21631 e21632 b21633 b21634 b21635 b21636 b21637 b21638 b21639 b21640 d21549 d21573 d21597 g26 f21548
        omega
      have d21641 : (x 4 1 && x 4 11).toNat = 0 := by
        have r21642 := hand2 (x 4 1) (x 4 11)
        have b21643 := hb (x 4 11)
        have b21644 := hb (x 4 1 && x 4 11)
        clear * - r21642 b21643 b21644 d21625
        omega
      have d21645 : (x 4 2 && x 4 11).toNat = 0 := by
        have r21646 := hand2 (x 4 2) (x 4 11)
        have b21647 := hb (x 4 11)
        have b21648 := hb (x 4 2 && x 4 11)
        clear * - r21646 b21647 b21648 d21625
        omega
      have d21649 : (x 3 3 && x 3 12).toNat = 1 := by
        have r21650 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21651 := hb (x 0 6)
        have b21652 := hb (x 6 9)
        have b21653 := hb (x 5 1 && x 5 10)
        have b21654 := hb (x 4 2 && x 4 11)
        have b21655 := hb (x 3 3 && x 3 12)
        have b21656 := hb (x 2 4 && x 2 13)
        have b21657 := hb (x 1 5 && x 1 14)
        clear * - r21650 b21651 b21652 b21653 b21654 b21655 b21656 b21657 d21573 d21613 d21645 g70 g71 f17561
        omega
      have d21658 : (x 3 12).toNat = 1 := by
        have r21659 := hand2 (x 3 3) (x 3 12)
        have b21660 := hb (x 3 12)
        have b21661 := hb (x 3 3 && x 3 12)
        clear * - r21659 b21660 b21661 d21649
        omega
      have d21662 : (x 2 13).toNat = 0 := by
        have r21663 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21664 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
        have e21665 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
        have b21666 := hb (x 0 3)
        have b21667 := hb (x 1 2)
        have b21668 := hb (x 2 13)
        have b21669 := hb (x 3 12)
        clear * - r21663 e21664 e21665 b21666 b21667 b21668 b21669 d21658 g23 g15
        omega
      have d21670 : (x 2 3 && x 2 13).toNat = 0 := by
        have r21671 := hand2 (x 2 3) (x 2 13)
        have b21672 := hb (x 2 13)
        have b21673 := hb (x 2 3 && x 2 13)
        clear * - r21671 b21672 b21673 d21662
        omega
      have d21674 : (x 3 2 && x 3 12).toNat = 1 := by
        have r21675 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21676 := hb (x 0 5)
        have b21677 := hb (x 5 10)
        have b21678 := hb (x 4 1 && x 4 11)
        have b21679 := hb (x 3 2 && x 3 12)
        have b21680 := hb (x 2 3 && x 2 13)
        have b21681 := hb (x 1 4 && x 1 14)
        clear * - r21675 b21676 b21677 b21678 b21679 b21680 b21681 d21597 d21641 d21670 g81 g17
        omega
      have d21682 : (x 3 2).toNat = 1 := by
        have r21683 := hand1 (x 3 2) (x 3 12)
        have b21684 := hb (x 3 2)
        have b21685 := hb (x 3 2 && x 3 12)
        clear * - r21683 b21684 b21685 d21674
        omega
      have d21686 : (x 3 14).toNat = 1 := by
        have r21687 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
        have b21688 := hb (x 3 2)
        have b21689 := hb (x 3 14)
        clear * - r21687 b21688 b21689 d21682
        omega
      have d21690 : (x 2 1).toNat = 0 := by
        have r21691 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21692 := hb (x 2 1)
        have b21693 := hb (x 3 14)
        clear * - r21691 b21692 b21693 d21686
        omega
      have d21694 : (x 2 1 && x 2 14).toNat = 0 := by
        have r21695 := hand1 (x 2 1) (x 2 14)
        have b21696 := hb (x 2 1)
        have b21697 := hb (x 2 1 && x 2 14)
        clear * - r21695 b21696 b21697 d21690
        omega
      have d21698 : (x 3 13).toNat = 1 := by
        have r21699 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21700 := hb (x 1 2)
        have b21701 := hb (x 3 13)
        have b21702 := hb (x 2 1 && x 2 14)
        clear * - r21699 b21700 b21701 b21702 d21694 g23
        omega
      have d21703 : (x 3 1).toNat = 1 := by
        have r21704 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
        have b21705 := hb (x 3 1)
        have b21706 := hb (x 3 13)
        clear * - r21704 b21705 b21706 d21698
        omega
      have d21707 : (x 4 14).toNat = 0 := by
        have r21708 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21709 := hb (x 3 1)
        have b21710 := hb (x 4 14)
        clear * - r21708 b21709 b21710 d21703
        omega
      have d21711 : (x 4 3 && x 4 14).toNat = 0 := by
        have r21712 := hand2 (x 4 3) (x 4 14)
        have b21713 := hb (x 4 14)
        have b21714 := hb (x 4 3 && x 4 14)
        clear * - r21712 b21713 b21714 d21707
        omega
      have d21715 : (x 4 6).toNat = 0 := by
        have r21716 : (x 4 6).toNat ≤ (x 4 14).toNat := himp _ _ (hp6 4)
        have b21717 := hb (x 4 6)
        have b21718 := hb (x 4 14)
        clear * - r21716 b21717 b21718 d21707
        omega
      have d21719 : (x 4 6 && x 4 11).toNat = 0 := by
        have r21720 := hand1 (x 4 6) (x 4 11)
        have b21721 := hb (x 4 6)
        have b21722 := hb (x 4 6 && x 4 11)
        clear * - r21720 b21721 b21722 d21715
        omega
      have d21723 : (x 4 2).toNat = 0 := by
        have r21724 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
        have b21725 := hb (x 4 2)
        have b21726 := hb (x 4 14)
        clear * - r21724 b21725 b21726 d21707
        omega
      have d21727 : (x 4 10).toNat = 0 := by
        have r21728 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
        have b21729 := hb (x 4 2)
        have b21730 := hb (x 4 10)
        clear * - r21728 b21729 b21730 d21723
        omega
      have d21731 : (x 3 1 && x 3 11).toNat = 1 := by
        have r21732 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21733 := hb (x (-1) 5)
        have b21734 := hb (x 4 10)
        have b21735 := hb (x 3 1 && x 3 11)
        have b21736 := hb (x 2 2 && x 2 12)
        have b21737 := hb (x 1 3 && x 1 13)
        have b21738 := hb (x 0 4 && x 0 14)
        clear * - r21732 b21733 b21734 b21735 b21736 b21737 b21738 d21727 g78 g79 g80 g8
        omega
      have d21739 : (x 3 11).toNat = 1 := by
        have r21740 := hand2 (x 3 1) (x 3 11)
        have b21741 := hb (x 3 11)
        have b21742 := hb (x 3 1 && x 3 11)
        clear * - r21740 b21741 b21742 d21731
        omega
      have d21743 : (x 3 3).toNat = 1 := by
        have r21744 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
        have b21745 := hb (x 3 3)
        have b21746 := hb (x 3 11)
        clear * - r21744 b21745 b21746 d21739
        omega
      have d21747 : (x 6 12).toNat = 0 := by
        have r21748 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21749 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
        have e21750 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
        have b21751 := hb (x 3 3)
        have b21752 := hb (x 4 2)
        have b21753 := hb (x 5 13)
        have b21754 := hb (x 6 12)
        clear * - r21748 e21749 e21750 b21751 b21752 b21753 b21754 d21723 d21743
        omega
      have d21755 : (x 6 1 && x 6 12).toNat = 0 := by
        have r21756 := hand2 (x 6 1) (x 6 12)
        have b21757 := hb (x 6 12)
        have b21758 := hb (x 6 1 && x 6 12)
        clear * - r21756 b21757 b21758 d21747
        omega
      have d21759 : (x 6 4).toNat = 0 := by
        have r21760 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
        have b21761 := hb (x 6 4)
        have b21762 := hb (x 6 12)
        clear * - r21760 b21761 b21762 d21747
        omega
      have d21763 : (x 5 13).toNat = 0 := by
        have r21764 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21765 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
        have e21766 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
        have b21767 := hb (x 3 3)
        have b21768 := hb (x 4 2)
        have b21769 := hb (x 5 13)
        have b21770 := hb (x 6 12)
        clear * - r21764 e21765 e21766 b21767 b21768 b21769 b21770 d21747 d21723 d21743
        omega
      have d21771 : (x 5 2 && x 5 13).toNat = 0 := by
        have r21772 := hand2 (x 5 2) (x 5 13)
        have b21773 := hb (x 5 13)
        have b21774 := hb (x 5 2 && x 5 13)
        clear * - r21772 b21773 b21774 d21763
        omega
      have d21775 : (x 5 5).toNat = 0 := by
        have r21776 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
        have b21777 := hb (x 5 5)
        have b21778 := hb (x 5 13)
        clear * - r21776 b21777 b21778 d21763
        omega
      have d21779 : (x 4 12).toNat = 0 := by
        have r21780 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21781 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e21782 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b21783 := hb (x 1 3)
        have b21784 := hb (x 2 2)
        have b21785 := hb (x 3 13)
        have b21786 := hb (x 4 12)
        clear * - r21780 e21781 e21782 b21783 b21784 b21785 b21786 d21698
        omega
      have d21787 : (x 4 3 && x 4 12).toNat = 0 := by
        have r21788 := hand2 (x 4 3) (x 4 12)
        have b21789 := hb (x 4 12)
        have b21790 := hb (x 4 3 && x 4 12)
        clear * - r21788 b21789 b21790 d21779
        omega
      have d21791 : (x 4 4).toNat = 0 := by
        have r21792 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
        have b21793 := hb (x 4 4)
        have b21794 := hb (x 4 12)
        clear * - r21792 b21793 b21794 d21779
        omega
      have d21795 : (x 4 4 && x 4 11).toNat = 0 := by
        have r21796 := hand1 (x 4 4) (x 4 11)
        have b21797 := hb (x 4 4)
        have b21798 := hb (x 4 4 && x 4 11)
        clear * - r21796 b21797 b21798 d21791
        omega
      have d21799 : (x 2 9).toNat = 0 := by
        have r21800 : (x 2 9).toNat ≤ (x 2 1).toNat := himp _ _ (hp9 2)
        have b21801 := hb (x 2 1)
        have b21802 := hb (x 2 9)
        clear * - r21800 b21801 b21802 d21690
        omega
      have d21803 : (x 2 6 && x 2 13).toNat = 0 := by
        have r21804 := hand2 (x 2 6) (x 2 13)
        have b21805 := hb (x 2 13)
        have b21806 := hb (x 2 6 && x 2 13)
        clear * - r21804 b21805 b21806 d21662
        omega
      have d21807 : (x 2 8 && x 2 13).toNat = 0 := by
        have r21808 := hand2 (x 2 8) (x 2 13)
        have b21809 := hb (x 2 13)
        have b21810 := hb (x 2 8 && x 2 13)
        clear * - r21808 b21809 b21810 d21662
        omega
      have d21811 : (x 2 5).toNat = 0 := by
        have r21812 : (x 2 5).toNat ≤ (x 2 13).toNat := himp _ _ (hp5 2)
        have b21813 := hb (x 2 5)
        have b21814 := hb (x 2 13)
        clear * - r21812 b21813 b21814 d21662
        omega
      have d21815 : (x 2 5 && x 2 14).toNat = 0 := by
        have r21816 := hand1 (x 2 5) (x 2 14)
        have b21817 := hb (x 2 5)
        have b21818 := hb (x 2 5 && x 2 14)
        clear * - r21816 b21817 b21818 d21811
        omega
      have d21819 : (x 3 4).toNat = 0 := by
        have r21820 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21821 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e21822 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e21823 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e21824 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e21825 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e21826 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b21827 := hb (x 0 7)
        have b21828 := hb (x 1 6)
        have b21829 := hb (x 2 5)
        have b21830 := hb (x 3 4)
        have b21831 := hb (x 4 11)
        have b21832 := hb (x 5 10)
        have b21833 := hb (x 6 9)
        have b21834 := hb (x 7 8)
        clear * - r21820 e21821 e21822 e21823 e21824 e21825 e21826 b21827 b21828 b21829 b21830 b21831 b21832 b21833 b21834 d21549 d21573 d21597 d21625 d21811 g26 f21548
        omega
      have d21835 : (x 3 4 && x 3 13).toNat = 0 := by
        have r21836 := hand1 (x 3 4) (x 3 13)
        have b21837 := hb (x 3 4)
        have b21838 := hb (x 3 4 && x 3 13)
        clear * - r21836 b21837 b21838 d21819
        omega
      have d21839 : (x 7 11).toNat = 1 := by
        have r21840 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21841 := hb (x 3 4)
        have b21842 := hb (x 7 11)
        have b21843 := hb (x 6 1 && x 6 12)
        have b21844 := hb (x 5 2 && x 5 13)
        have b21845 := hb (x 4 3 && x 4 14)
        clear * - r21840 b21841 b21842 b21843 b21844 b21845 d21755 d21771 d21711 d21819
        omega
      have d21846 : (x 7 3).toNat = 1 := by
        have r21847 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
        have b21848 := hb (x 7 3)
        have b21849 := hb (x 7 11)
        clear * - r21847 b21848 b21849 d21839
        omega
      have d21850 : (x 10 12).toNat = 0 := by
        have r21851 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21852 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
        have e21853 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
        have b21854 := hb (x 7 3)
        have b21855 := hb (x 8 2)
        have b21856 := hb (x 9 13)
        have b21857 := hb (x 10 12)
        clear * - r21851 e21852 e21853 b21854 b21855 b21856 b21857 d21846
        omega
      have d21858 : (x 9 13).toNat = 0 := by
        have r21859 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21860 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
        have e21861 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
        have b21862 := hb (x 7 3)
        have b21863 := hb (x 8 2)
        have b21864 := hb (x 9 13)
        have b21865 := hb (x 10 12)
        clear * - r21859 e21860 e21861 b21862 b21863 b21864 b21865 d21850 d21846
        omega
      have d21866 : (x 8 2).toNat = 0 := by
        have r21867 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21868 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
        have e21869 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
        have b21870 := hb (x 7 3)
        have b21871 := hb (x 8 2)
        have b21872 := hb (x 9 13)
        have b21873 := hb (x 10 12)
        clear * - r21867 e21868 e21869 b21870 b21871 b21872 b21873 d21850 d21858 d21846
        omega
      have d21874 : (x 8 2 && x 8 7).toNat = 0 := by
        have r21875 := hand1 (x 8 2) (x 8 7)
        have b21876 := hb (x 8 2)
        have b21877 := hb (x 8 2 && x 8 7)
        clear * - r21875 b21876 b21877 d21866
        omega
      have d21878 : (x 8 10).toNat = 0 := by
        have r21879 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
        have b21880 := hb (x 8 2)
        have b21881 := hb (x 8 10)
        clear * - r21879 b21880 b21881 d21866
        omega
      have d21882 : (x 10 8).toNat = 0 := by
        have r21883 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21884 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
        have e21885 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
        have e21886 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
        have e21887 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
        have e21888 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
        have e21889 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
        have b21890 := hb (x 3 7)
        have b21891 := hb (x 4 6)
        have b21892 := hb (x 5 5)
        have b21893 := hb (x 6 4)
        have b21894 := hb (x 7 11)
        have b21895 := hb (x 8 10)
        have b21896 := hb (x 9 9)
        have b21897 := hb (x 10 8)
        clear * - r21883 e21884 e21885 e21886 e21887 e21888 e21889 b21890 b21891 b21892 b21893 b21894 b21895 b21896 b21897 d21878 d21839 d21759 d21775 d21715
        omega
      have d21898 : (x 9 9).toNat = 0 := by
        have r21899 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21900 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
        have e21901 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
        have e21902 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
        have e21903 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
        have e21904 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
        have e21905 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
        have b21906 := hb (x 3 7)
        have b21907 := hb (x 4 6)
        have b21908 := hb (x 5 5)
        have b21909 := hb (x 6 4)
        have b21910 := hb (x 7 11)
        have b21911 := hb (x 8 10)
        have b21912 := hb (x 9 9)
        have b21913 := hb (x 10 8)
        clear * - r21899 e21900 e21901 e21902 e21903 e21904 e21905 b21906 b21907 b21908 b21909 b21910 b21911 b21912 b21913 d21882 d21878 d21839 d21759 d21775 d21715
        omega
      have d21914 : (x 3 7).toNat = 0 := by
        have r21915 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21916 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
        have e21917 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
        have e21918 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
        have e21919 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
        have e21920 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
        have e21921 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
        have b21922 := hb (x 3 7)
        have b21923 := hb (x 4 6)
        have b21924 := hb (x 5 5)
        have b21925 := hb (x 6 4)
        have b21926 := hb (x 7 11)
        have b21927 := hb (x 8 10)
        have b21928 := hb (x 9 9)
        have b21929 := hb (x 10 8)
        clear * - r21915 e21916 e21917 e21918 e21919 e21920 e21921 b21922 b21923 b21924 b21925 b21926 b21927 b21928 b21929 d21882 d21898 d21878 d21839 d21759 d21775 d21715
        omega
      have d21930 : (x 3 7 && x 3 12).toNat = 0 := by
        have r21931 := hand1 (x 3 7) (x 3 12)
        have b21932 := hb (x 3 7)
        have b21933 := hb (x 3 7 && x 3 12)
        clear * - r21931 b21932 b21933 d21914
        omega
      have r21934 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e21935 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e21936 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e21937 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e21938 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e21939 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e21940 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have r21941 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e21942 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e21943 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e21944 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e21945 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e21946 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e21947 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have r21948 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e21949 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e21950 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e21951 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e21952 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e21953 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e21954 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have r21955 : 1 ≤ (x 10 5).toNat + (x 9 1 && x 9 6).toNat + (x 8 2 && x 8 7).toNat + (x 7 3 && x 7 8).toNat + (x 6 4 && x 6 9).toNat + (x 5 5 && x 5 10).toNat + (x 4 6 && x 4 11).toNat + (x 3 7 && x 3 12).toNat + (x 2 8 && x 2 13).toNat + (x 1 9 && x 1 14).toNat + (x 0 10).toNat := by have q := hcov5 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r21956 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := by have q := hcov7 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r21957 : 1 ≤ (x 2 9).toNat + (x 1 1 && x 1 10).toNat + (x 0 2 && x 0 11).toNat + (x (-1) 3 && x (-1) 12).toNat + (x (-2) 4 && x (-2) 13).toNat + (x (-3) 5 && x (-3) 14).toNat + (x (-4) 6).toNat := by have q := hcov9 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r21958 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r21959 := hand2 (x 9 1) (x 9 6)
      have r21960 := hand1 (x 3 5) (x 3 12)
      have r21961 := hand1 (x (-2) 4) (x (-2) 13)
      have r21962 := hand1 (x (-3) 5) (x (-3) 14)
      have r21963 := hand2 (x 6 1) (x 6 10)
      have r21964 := hand2 (x 5 2) (x 5 11)
      linarith only [r21934, e21935, e21936, e21937, e21938, e21939, e21940, r21941, e21942, e21943, e21944, e21945, e21946, e21947, r21948, e21949, e21950, e21951, e21952, e21953, e21954, r21955, r21956, r21957, r21958, r21959, r21960, r21961, r21962, r21963, r21964, g11, g18, g26, d21799, d21791, d21874, d21569, d21593, d21621, d21719, d21930, d21807, g53, d21565, d21589, d21617, d21795, d21803, g54, g64, g65, g66, d21787, d21835, d21815]
  · have f22018 : (x 0 6).toNat = 1 := by rw [h17560]; rfl
    have d22019 : (x 6 8).toNat = 0 := by
      have r22020 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22021 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e22022 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e22023 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e22024 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e22025 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e22026 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b22027 := hb (x (-1) 7)
      have b22028 := hb (x 0 6)
      have b22029 := hb (x 1 5)
      have b22030 := hb (x 2 4)
      have b22031 := hb (x 3 11)
      have b22032 := hb (x 4 10)
      have b22033 := hb (x 5 9)
      have b22034 := hb (x 6 8)
      clear * - r22020 e22021 e22022 e22023 e22024 e22025 e22026 b22027 b22028 b22029 b22030 b22031 b22032 b22033 b22034 g31 g25 f22018
      omega
    have d22035 : (x 5 9).toNat = 0 := by
      have r22036 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22037 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e22038 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e22039 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e22040 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e22041 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e22042 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b22043 := hb (x (-1) 7)
      have b22044 := hb (x 0 6)
      have b22045 := hb (x 1 5)
      have b22046 := hb (x 2 4)
      have b22047 := hb (x 3 11)
      have b22048 := hb (x 4 10)
      have b22049 := hb (x 5 9)
      have b22050 := hb (x 6 8)
      clear * - r22036 e22037 e22038 e22039 e22040 e22041 e22042 b22043 b22044 b22045 b22046 b22047 b22048 b22049 b22050 d22019 g31 g25 f22018
      omega
    have d22051 : (x 4 10).toNat = 0 := by
      have r22052 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22053 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e22054 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e22055 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e22056 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e22057 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e22058 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b22059 := hb (x (-1) 7)
      have b22060 := hb (x 0 6)
      have b22061 := hb (x 1 5)
      have b22062 := hb (x 2 4)
      have b22063 := hb (x 3 11)
      have b22064 := hb (x 4 10)
      have b22065 := hb (x 5 9)
      have b22066 := hb (x 6 8)
      clear * - r22052 e22053 e22054 e22055 e22056 e22057 e22058 b22059 b22060 b22061 b22062 b22063 b22064 b22065 b22066 d22019 d22035 g31 g25 f22018
      omega
    have d22067 : (x 3 1 && x 3 11).toNat = 1 := by
      have r22068 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b22069 := hb (x (-1) 5)
      have b22070 := hb (x 4 10)
      have b22071 := hb (x 3 1 && x 3 11)
      have b22072 := hb (x 2 2 && x 2 12)
      have b22073 := hb (x 1 3 && x 1 13)
      have b22074 := hb (x 0 4 && x 0 14)
      clear * - r22068 b22069 b22070 b22071 b22072 b22073 b22074 d22051 g78 g79 g80 g8
      omega
    have d22075 : (x 3 11).toNat = 1 := by
      have r22076 := hand2 (x 3 1) (x 3 11)
      have b22077 := hb (x 3 11)
      have b22078 := hb (x 3 1 && x 3 11)
      clear * - r22076 b22077 b22078 d22067
      omega
    have r22079 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e22080 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e22081 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e22082 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e22083 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e22084 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e22085 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b22086 := hb (x (-1) 7)
    have b22087 := hb (x 0 6)
    have b22088 := hb (x 1 5)
    have b22089 := hb (x 2 4)
    have b22090 := hb (x 3 11)
    have b22091 := hb (x 4 10)
    have b22092 := hb (x 5 9)
    have b22093 := hb (x 6 8)
    linarith only [r22079, e22080, e22081, e22082, e22083, e22084, e22085, b22086, b22087, b22088, b22089, b22090, b22091, b22092, b22093, d22019, d22035, d22051, d22075, g31, g25, f22018]

theorem cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a1100 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-7) 11).toNat = 0)
    (g1 : (x (-6) 6).toNat = 0)
    (g2 : (x (-6) 10).toNat = 0)
    (g3 : (x (-5) 13).toNat = 0)
    (g4 : (x (-2) 3).toNat = 0)
    (g5 : (x (-2) 11).toNat = 0)
    (g6 : (x (-1) 2).toNat = 0)
    (g7 : (x (-1) 3).toNat = 0)
    (g8 : (x (-1) 5).toNat = 0)
    (g9 : (x (-1) 9).toNat = 0)
    (g10 : (x (-1) 10).toNat = 0)
    (g11 : (x (-1) 11).toNat = 0)
    (g12 : (x (-1) 13).toNat = 0)
    (g13 : (x 0 1).toNat = 1)
    (g14 : (x 0 2).toNat = 1)
    (g15 : (x 0 3).toNat = 0)
    (g16 : (x 0 4).toNat = 0)
    (g17 : (x 0 5).toNat = 0)
    (g18 : (x 0 8).toNat = 0)
    (g19 : (x 0 11).toNat = 0)
    (g20 : (x 0 12).toNat = 1)
    (g21 : (x 0 13).toNat = 1)
    (g22 : (x 0 14).toNat = 1)
    (g23 : (x 1 2).toNat = 0)
    (g24 : (x 1 4).toNat = 0)
    (g25 : (x 1 5).toNat = 0)
    (g26 : (x 1 6).toNat = 0)
    (g27 : (x 1 10).toNat = 0)
    (g28 : (x 1 12).toNat = 0)
    (g29 : (x 1 13).toNat = 0)
    (g30 : (x 1 14).toNat = 0)
    (g31 : (x 2 4).toNat = 0)
    (g32 : (x 2 12).toNat = 0)
    (g33 : (x 1 10 && x 1 11).toNat = 0)
    (g34 : (x 0 11 && x 0 12).toNat = 0)
    (g35 : (x (-1) 12 && x (-1) 13).toNat = 0)
    (g36 : (x 0 1 && x 0 3).toNat = 0)
    (g37 : (x (-1) 2 && x (-1) 4).toNat = 0)
    (g38 : (x (-2) 3 && x (-2) 5).toNat = 0)
    (g39 : (x 2 9 && x 2 12).toNat = 0)
    (g40 : (x 1 10 && x 1 13).toNat = 0)
    (g41 : (x 0 11 && x 0 14).toNat = 0)
    (g42 : (x 0 4 && x 0 8).toNat = 0)
    (g43 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g44 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g45 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g46 : (x (-5) 9 && x (-5) 13).toNat = 0)
    (g47 : (x (-6) 5 && x (-6) 10).toNat = 0)
    (g48 : (x (-7) 6 && x (-7) 11).toNat = 0)
    (g49 : (x 1 1 && x 1 6).toNat = 0)
    (g50 : (x (-1) 3 && x (-1) 8).toNat = 0)
    (g51 : (x 1 6 && x 1 11).toNat = 0)
    (g52 : (x (-1) 8 && x (-1) 13).toNat = 0)
    (g53 : (x 1 9 && x 1 14).toNat = 0)
    (g54 : (x 1 7 && x 1 14).toNat = 0)
    (g55 : (x (-6) 1 && x (-6) 10).toNat = 0)
    (g56 : (x (-7) 2 && x (-7) 11).toNat = 0)
    (g57 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g58 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g59 : (x (-5) 4 && x (-5) 13).toNat = 0)
    (g60 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g61 : (x (-2) 2 && x (-2) 11).toNat = 0)
    (g62 : (x (-3) 3 && x (-3) 12).toNat = 0)
    (g63 : (x (-5) 5 && x (-5) 14).toNat = 0)
    (g64 : (x 1 1 && x 1 10).toNat = 0)
    (g65 : (x 0 2 && x 0 11).toNat = 0)
    (g66 : (x (-1) 3 && x (-1) 12).toNat = 0)
    (g67 : (x 1 2 && x 1 11).toNat = 0)
    (g68 : (x 0 3 && x 0 12).toNat = 0)
    (g69 : (x (-1) 4 && x (-1) 13).toNat = 0)
    (g70 : (x 2 4 && x 2 13).toNat = 0)
    (g71 : (x 1 5 && x 1 14).toNat = 0)
    (g72 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g73 : (x 0 1 && x 0 11).toNat = 0)
    (g74 : (x (-1) 2 && x (-1) 12).toNat = 0)
    (g75 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g76 : (x 1 2 && x 1 12).toNat = 0)
    (g77 : (x 0 3 && x 0 13).toNat = 0)
    (g78 : (x 2 2 && x 2 12).toNat = 0)
    (g79 : (x 1 3 && x 1 13).toNat = 0)
    (g80 : (x 0 4 && x 0 14).toNat = 0)
    (g81 : (x 1 4 && x 1 14).toNat = 0)
    (g82 : (x (-6) 2 && x (-6) 13).toNat = 0)
    (g83 : (x (-7) 3 && x (-7) 14).toNat = 0)
    (g84 : (x 2 1 && x 2 12).toNat = 0)
    (g85 : (x 1 2 && x 1 13).toNat = 0)
    (g86 : (x 0 3 && x 0 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a1100_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83 g84 g85 g86
