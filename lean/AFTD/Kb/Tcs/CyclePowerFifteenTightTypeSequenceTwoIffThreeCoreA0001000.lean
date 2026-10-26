import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a0001000

Topic: combinatorics   Node: e54490a78792

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP; the same generator on the same window refutes x(0,2) != x(0,3) (a case-split tree of 109 + 3 nodes).

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_two_iff_three_core: under the layer-free tight-cover constraints for k = 15 and 79 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a0001000_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 3).toNat = 0)
    (g1 : (x (-3) 5).toNat = 0)
    (g2 : (x (-3) 9).toNat = 0)
    (g3 : (x (-3) 11).toNat = 0)
    (g4 : (x (-3) 13).toNat = 0)
    (g5 : (x (-2) 2).toNat = 1)
    (g6 : (x (-1) 1).toNat = 0)
    (g7 : (x (-1) 3).toNat = 0)
    (g8 : (x (-1) 5).toNat = 0)
    (g9 : (x (-1) 9).toNat = 0)
    (g10 : (x (-1) 11).toNat = 0)
    (g11 : (x (-1) 13).toNat = 0)
    (g12 : (x 0 1).toNat = 1)
    (g13 : (x 0 2).toNat = 1)
    (g14 : (x 0 4).toNat = 0)
    (g15 : (x 0 5).toNat = 0)
    (g16 : (x 0 6).toNat = 0)
    (g17 : (x 0 7).toNat = 0)
    (g18 : (x 0 8).toNat = 0)
    (g19 : (x 0 9).toNat = 0)
    (g20 : (x 0 10).toNat = 0)
    (g21 : (x 0 11).toNat = 0)
    (g22 : (x 0 13).toNat = 0)
    (g23 : (x 0 14).toNat = 1)
    (g24 : (x 1 2).toNat = 0)
    (g25 : (x 1 5).toNat = 0)
    (g26 : (x 1 6).toNat = 0)
    (g27 : (x 1 10).toNat = 0)
    (g28 : (x 1 13).toNat = 0)
    (g29 : (x 2 4).toNat = 0)
    (g30 : (x 2 12).toNat = 0)
    (g31 : (x 0 1 && x 0 4).toNat = 0)
    (g32 : (x (-1) 2 && x (-1) 5).toNat = 0)
    (g33 : (x 0 2 && x 0 5).toNat = 0)
    (g34 : (x (-1) 3 && x (-1) 6).toNat = 0)
    (g35 : (x (-3) 5 && x (-3) 8).toNat = 0)
    (g36 : (x 2 4 && x 2 8).toNat = 0)
    (g37 : (x 1 5 && x 1 9).toNat = 0)
    (g38 : (x 0 6 && x 0 10).toNat = 0)
    (g39 : (x (-1) 7 && x (-1) 11).toNat = 0)
    (g40 : (x (-3) 9 && x (-3) 13).toNat = 0)
    (g41 : (x 0 1 && x 0 6).toNat = 0)
    (g42 : (x (-3) 4 && x (-3) 9).toNat = 0)
    (g43 : (x 1 1 && x 1 6).toNat = 0)
    (g44 : (x 0 2 && x 0 7).toNat = 0)
    (g45 : (x (-1) 3 && x (-1) 8).toNat = 0)
    (g46 : (x (-3) 5 && x (-3) 10).toNat = 0)
    (g47 : (x 0 1 && x 0 7).toNat = 0)
    (g48 : (x 2 6 && x 2 12).toNat = 0)
    (g49 : (x 1 7 && x 1 13).toNat = 0)
    (g50 : (x 0 8 && x 0 14).toNat = 0)
    (g51 : (x 0 2 && x 0 9).toNat = 0)
    (g52 : (x (-1) 3 && x (-1) 10).toNat = 0)
    (g53 : (x (-3) 5 && x (-3) 12).toNat = 0)
    (g54 : (x 1 7 && x 1 14).toNat = 0)
    (g55 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g56 : (x 0 4 && x 0 13).toNat = 0)
    (g57 : (x (-1) 5 && x (-1) 14).toNat = 0)
    (g58 : (x 0 1 && x 0 11).toNat = 0)
    (g59 : (x 0 2 && x 0 12).toNat = 0)
    (g60 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g61 : (x 1 2 && x 1 12).toNat = 0)
    (g62 : (x 0 3 && x 0 13).toNat = 0)
    (g63 : (x 2 2 && x 2 12).toNat = 0)
    (g64 : (x 1 3 && x 1 13).toNat = 0)
    (g65 : (x 0 4 && x 0 14).toNat = 0)
    (g66 : (x (-3) 1 && x (-3) 12).toNat = 0)
    (g67 : (x (-3) 2 && x (-3) 13).toNat = 0)
    (g68 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g69 : (x (-3) 3 && x (-3) 14).toNat = 0)
    (g70 : (x 0 1 && x 0 12).toNat = 0)
    (g71 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g72 : (x 0 2 && x 0 13).toNat = 0)
    (g73 : (x (-1) 3 && x (-1) 14).toNat = 0)
    (g74 : (x 2 1 && x 2 12).toNat = 0)
    (g75 : (x 1 2 && x 1 13).toNat = 0)
    (g76 : (x 0 3 && x 0 14).toNat = 0)
    (g77 : (x 1 3 && x 1 14).toNat = 0)
    (g78 : (x (-3) 1 && x (-3) 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  cases h2656 : x 1 1
  · have f2657 : (x 1 1).toNat = 0 := by rw [h2656]; rfl
    have d2658 : (x 1 1 && x 1 12).toNat = 0 := by
      have r2659 := hand1 (x 1 1) (x 1 12)
      have b2660 := hb (x 1 1)
      have b2661 := hb (x 1 1 && x 1 12)
      clear * - r2659 b2660 b2661 f2657
      omega
    have d2662 : (x 1 1 && x 1 8).toNat = 0 := by
      have r2663 := hand1 (x 1 1) (x 1 8)
      have b2664 := hb (x 1 1)
      have b2665 := hb (x 1 1 && x 1 8)
      clear * - r2663 b2664 b2665 f2657
      omega
    have d2666 : (x 1 1 && x 1 4).toNat = 0 := by
      have r2667 := hand1 (x 1 1) (x 1 4)
      have b2668 := hb (x 1 1)
      have b2669 := hb (x 1 1 && x 1 4)
      clear * - r2667 b2668 b2669 f2657
      omega
    have d2670 : (x 1 9).toNat = 0 := by
      have r2671 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
      have b2672 := hb (x 1 1)
      have b2673 := hb (x 1 9)
      clear * - r2671 b2672 b2673 f2657
      omega
    have d2674 : (x 2 14).toNat = 1 := by
      have r2675 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2676 := hb (x 1 1)
      have b2677 := hb (x 2 14)
      clear * - r2675 b2676 b2677 f2657
      omega
    cases h2678 : x (-1) 2
    · have f2679 : (x (-1) 2).toNat = 0 := by rw [h2678]; rfl
      have d2680 : (x (-1) 2 && x (-1) 12).toNat = 0 := by
        have r2681 := hand1 (x (-1) 2) (x (-1) 12)
        have b2682 := hb (x (-1) 2)
        have b2683 := hb (x (-1) 2 && x (-1) 12)
        clear * - r2681 b2682 b2683 f2679
        omega
      have d2684 : (x (-1) 2 && x (-1) 8).toNat = 0 := by
        have r2685 := hand1 (x (-1) 2) (x (-1) 8)
        have b2686 := hb (x (-1) 2)
        have b2687 := hb (x (-1) 2 && x (-1) 8)
        clear * - r2685 b2686 b2687 f2679
        omega
      have d2688 : (x (-1) 2 && x (-1) 7).toNat = 0 := by
        have r2689 := hand1 (x (-1) 2) (x (-1) 7)
        have b2690 := hb (x (-1) 2)
        have b2691 := hb (x (-1) 2 && x (-1) 7)
        clear * - r2689 b2690 b2691 f2679
        omega
      have d2692 : (x (-1) 2 && x (-1) 6).toNat = 0 := by
        have r2693 := hand1 (x (-1) 2) (x (-1) 6)
        have b2694 := hb (x (-1) 2)
        have b2695 := hb (x (-1) 2 && x (-1) 6)
        clear * - r2693 b2694 b2695 f2679
        omega
      have d2696 : (x (-1) 10).toNat = 0 := by
        have r2697 : (x (-1) 10).toNat ≤ (x (-1) 2).toNat := himp _ _ (hp10 (-1))
        have b2698 := hb (x (-1) 2)
        have b2699 := hb (x (-1) 10)
        clear * - r2697 b2698 b2699 f2679
        omega
      cases h2700 : x 1 3
      · have f2701 : (x 1 3).toNat = 0 := by rw [h2700]; rfl
        have d2702 : (x 1 3 && x 1 12).toNat = 0 := by
          have r2703 := hand1 (x 1 3) (x 1 12)
          have b2704 := hb (x 1 3)
          have b2705 := hb (x 1 3 && x 1 12)
          clear * - r2703 b2704 b2705 f2701
          omega
        have d2706 : (x 1 11).toNat = 0 := by
          have r2707 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
          have b2708 := hb (x 1 3)
          have b2709 := hb (x 1 11)
          clear * - r2707 b2708 b2709 f2701
          omega
        cases h2710 : x (-1) 4
        · have f2711 : (x (-1) 4).toNat = 0 := by rw [h2710]; rfl
          have d2712 : (x (-1) 4 && x (-1) 14).toNat = 0 := by
            have r2713 := hand1 (x (-1) 4) (x (-1) 14)
            have b2714 := hb (x (-1) 4)
            have b2715 := hb (x (-1) 4 && x (-1) 14)
            clear * - r2713 b2714 b2715 f2711
            omega
          have d2716 : (x 3 11).toNat = 1 := by
            have r2717 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b2718 := hb (x (-1) 4)
            have b2719 := hb (x 3 11)
            have b2720 := hb (x 2 1 && x 2 12)
            have b2721 := hb (x 1 2 && x 1 13)
            have b2722 := hb (x 0 3 && x 0 14)
            clear * - r2717 b2718 b2719 b2720 b2721 b2722 g74 g75 g76 f2711
            omega
          have d2723 : (x 3 3).toNat = 1 := by
            have r2724 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
            have b2725 := hb (x 3 3)
            have b2726 := hb (x 3 11)
            clear * - r2724 b2725 b2726 d2716
            omega
          have d2727 : (x 6 12).toNat = 0 := by
            have r2728 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e2729 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
            have e2730 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
            have b2731 := hb (x 3 3)
            have b2732 := hb (x 4 2)
            have b2733 := hb (x 5 13)
            have b2734 := hb (x 6 12)
            clear * - r2728 e2729 e2730 b2731 b2732 b2733 b2734 d2723
            omega
          have d2735 : (x 6 2 && x 6 12).toNat = 0 := by
            have r2736 := hand2 (x 6 2) (x 6 12)
            have b2737 := hb (x 6 12)
            have b2738 := hb (x 6 2 && x 6 12)
            clear * - r2736 b2737 b2738 d2727
            omega
          have d2739 : (x 6 3 && x 6 12).toNat = 0 := by
            have r2740 := hand2 (x 6 3) (x 6 12)
            have b2741 := hb (x 6 12)
            have b2742 := hb (x 6 3 && x 6 12)
            clear * - r2740 b2741 b2742 d2727
            omega
          have d2743 : (x 6 4).toNat = 0 := by
            have r2744 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
            have b2745 := hb (x 6 4)
            have b2746 := hb (x 6 12)
            clear * - r2744 b2745 b2746 d2727
            omega
          have d2747 : (x 6 4 && x 6 10).toNat = 0 := by
            have r2748 := hand1 (x 6 4) (x 6 10)
            have b2749 := hb (x 6 4)
            have b2750 := hb (x 6 4 && x 6 10)
            clear * - r2748 b2749 b2750 d2743
            omega
          have d2751 : (x 5 13).toNat = 0 := by
            have r2752 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e2753 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
            have e2754 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
            have b2755 := hb (x 3 3)
            have b2756 := hb (x 4 2)
            have b2757 := hb (x 5 13)
            have b2758 := hb (x 6 12)
            clear * - r2752 e2753 e2754 b2755 b2756 b2757 b2758 d2727 d2723
            omega
          have d2759 : (x 5 3 && x 5 13).toNat = 0 := by
            have r2760 := hand2 (x 5 3) (x 5 13)
            have b2761 := hb (x 5 13)
            have b2762 := hb (x 5 3 && x 5 13)
            clear * - r2760 b2761 b2762 d2751
            omega
          have d2763 : (x 5 4 && x 5 13).toNat = 0 := by
            have r2764 := hand2 (x 5 4) (x 5 13)
            have b2765 := hb (x 5 13)
            have b2766 := hb (x 5 4 && x 5 13)
            clear * - r2764 b2765 b2766 d2751
            omega
          have d2767 : (x 5 5).toNat = 0 := by
            have r2768 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
            have b2769 := hb (x 5 5)
            have b2770 := hb (x 5 13)
            clear * - r2768 b2769 b2770 d2751
            omega
          have d2771 : (x 5 5 && x 5 11).toNat = 0 := by
            have r2772 := hand1 (x 5 5) (x 5 11)
            have b2773 := hb (x 5 5)
            have b2774 := hb (x 5 5 && x 5 11)
            clear * - r2772 b2773 b2774 d2767
            omega
          have d2775 : (x 4 2).toNat = 0 := by
            have r2776 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e2777 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
            have e2778 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
            have b2779 := hb (x 3 3)
            have b2780 := hb (x 4 2)
            have b2781 := hb (x 5 13)
            have b2782 := hb (x 6 12)
            clear * - r2776 e2777 e2778 b2779 b2780 b2781 b2782 d2727 d2751 d2723
            omega
          have d2783 : (x 4 2 && x 4 6).toNat = 0 := by
            have r2784 := hand1 (x 4 2) (x 4 6)
            have b2785 := hb (x 4 2)
            have b2786 := hb (x 4 2 && x 4 6)
            clear * - r2784 b2785 b2786 d2775
            omega
          have d2787 : (x 4 10).toNat = 0 := by
            have r2788 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
            have b2789 := hb (x 4 2)
            have b2790 := hb (x 4 10)
            clear * - r2788 b2789 b2790 d2775
            omega
          have d2791 : (x 4 4 && x 4 10).toNat = 0 := by
            have r2792 := hand2 (x 4 4) (x 4 10)
            have b2793 := hb (x 4 10)
            have b2794 := hb (x 4 4 && x 4 10)
            clear * - r2792 b2793 b2794 d2787
            omega
          have d2795 : (x 3 1 && x 3 11).toNat = 1 := by
            have r2796 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b2797 := hb (x (-1) 5)
            have b2798 := hb (x 4 10)
            have b2799 := hb (x 3 1 && x 3 11)
            have b2800 := hb (x 2 2 && x 2 12)
            have b2801 := hb (x 1 3 && x 1 13)
            have b2802 := hb (x 0 4 && x 0 14)
            clear * - r2796 b2797 b2798 b2799 b2800 b2801 b2802 d2787 g63 g64 g65 g8
            omega
          have d2803 : (x 3 1).toNat = 1 := by
            have r2804 := hand1 (x 3 1) (x 3 11)
            have b2805 := hb (x 3 1)
            have b2806 := hb (x 3 1 && x 3 11)
            clear * - r2804 b2805 b2806 d2795
            omega
          have d2807 : (x 4 14).toNat = 0 := by
            have r2808 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b2809 := hb (x 3 1)
            have b2810 := hb (x 4 14)
            clear * - r2808 b2809 b2810 d2803
            omega
          have d2811 : (x 4 1 && x 4 14).toNat = 0 := by
            have r2812 := hand2 (x 4 1) (x 4 14)
            have b2813 := hb (x 4 14)
            have b2814 := hb (x 4 1 && x 4 14)
            clear * - r2812 b2813 b2814 d2807
            omega
          have d2815 : (x 3 2).toNat = 1 := by
            have r2816 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b2817 := hb (x 3 2)
            have b2818 := hb (x 5 13)
            have b2819 := hb (x 4 1 && x 4 14)
            clear * - r2816 b2817 b2818 b2819 d2751 d2811
            omega
          have d2820 : (x 3 14).toNat = 1 := by
            have r2821 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
            have b2822 := hb (x 3 2)
            have b2823 := hb (x 3 14)
            clear * - r2821 b2822 b2823 d2815
            omega
          have d2824 : (x 2 1).toNat = 0 := by
            have r2825 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b2826 := hb (x 2 1)
            have b2827 := hb (x 3 14)
            clear * - r2825 b2826 b2827 d2820
            omega
          have d2828 : (x 2 1 && x 2 14).toNat = 0 := by
            have r2829 := hand1 (x 2 1) (x 2 14)
            have b2830 := hb (x 2 1)
            have b2831 := hb (x 2 1 && x 2 14)
            clear * - r2829 b2830 b2831 d2824
            omega
          have d2832 : (x 3 13).toNat = 1 := by
            have r2833 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b2834 := hb (x 1 2)
            have b2835 := hb (x 3 13)
            have b2836 := hb (x 2 1 && x 2 14)
            clear * - r2833 b2834 b2835 b2836 d2828 g24
            omega
          have d2837 : (x 4 12).toNat = 0 := by
            have r2838 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e2839 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e2840 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b2841 := hb (x 1 3)
            have b2842 := hb (x 2 2)
            have b2843 := hb (x 3 13)
            have b2844 := hb (x 4 12)
            clear * - r2838 e2839 e2840 b2841 b2842 b2843 b2844 d2832 f2701
            omega
          have d2845 : (x 4 3 && x 4 12).toNat = 0 := by
            have r2846 := hand2 (x 4 3) (x 4 12)
            have b2847 := hb (x 4 12)
            have b2848 := hb (x 4 3 && x 4 12)
            clear * - r2846 b2847 b2848 d2837
            omega
          have d2849 : (x 4 6 && x 4 12).toNat = 0 := by
            have r2850 := hand2 (x 4 6) (x 4 12)
            have b2851 := hb (x 4 12)
            have b2852 := hb (x 4 6 && x 4 12)
            clear * - r2850 b2851 b2852 d2837
            omega
          have d2853 : (x 4 7 && x 4 12).toNat = 0 := by
            have r2854 := hand2 (x 4 7) (x 4 12)
            have b2855 := hb (x 4 12)
            have b2856 := hb (x 4 7 && x 4 12)
            clear * - r2854 b2855 b2856 d2837
            omega
          have d2857 : (x 4 4).toNat = 0 := by
            have r2858 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
            have b2859 := hb (x 4 4)
            have b2860 := hb (x 4 12)
            clear * - r2858 b2859 b2860 d2837
            omega
          have d2861 : (x 4 4 && x 4 14).toNat = 0 := by
            have r2862 := hand1 (x 4 4) (x 4 14)
            have b2863 := hb (x 4 4)
            have b2864 := hb (x 4 4 && x 4 14)
            clear * - r2862 b2863 b2864 d2857
            omega
          have d2865 : (x 4 4 && x 4 11).toNat = 0 := by
            have r2866 := hand1 (x 4 4) (x 4 11)
            have b2867 := hb (x 4 4)
            have b2868 := hb (x 4 4 && x 4 11)
            clear * - r2866 b2867 b2868 d2857
            omega
          have d2869 : (x 2 2).toNat = 0 := by
            have r2870 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e2871 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e2872 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b2873 := hb (x 1 3)
            have b2874 := hb (x 2 2)
            have b2875 := hb (x 3 13)
            have b2876 := hb (x 4 12)
            clear * - r2870 e2871 e2872 b2873 b2874 b2875 b2876 d2837 d2832 f2701
            omega
          have d2877 : (x 2 2 && x 2 11).toNat = 0 := by
            have r2878 := hand1 (x 2 2) (x 2 11)
            have b2879 := hb (x 2 2)
            have b2880 := hb (x 2 2 && x 2 11)
            clear * - r2878 b2879 b2880 d2869
            omega
          have d2881 : (x 2 1 && x 2 11).toNat = 0 := by
            have r2882 := hand1 (x 2 1) (x 2 11)
            have b2883 := hb (x 2 1)
            have b2884 := hb (x 2 1 && x 2 11)
            clear * - r2882 b2883 b2884 d2824
            omega
          have d2885 : (x 2 13).toNat = 0 := by
            have r2886 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
            have b2887 := hb (x 2 1)
            have b2888 := hb (x 2 13)
            clear * - r2886 b2887 b2888 d2824
            omega
          have d2889 : (x 2 6 && x 2 13).toNat = 0 := by
            have r2890 := hand2 (x 2 6) (x 2 13)
            have b2891 := hb (x 2 13)
            have b2892 := hb (x 2 6 && x 2 13)
            clear * - r2890 b2891 b2892 d2885
            omega
          have d2893 : (x 2 9 && x 2 13).toNat = 0 := by
            have r2894 := hand2 (x 2 9) (x 2 13)
            have b2895 := hb (x 2 13)
            have b2896 := hb (x 2 9 && x 2 13)
            clear * - r2894 b2895 b2896 d2885
            omega
          have d2897 : (x 2 5).toNat = 0 := by
            have r2898 : (x 2 5).toNat ≤ (x 2 13).toNat := himp _ _ (hp5 2)
            have b2899 := hb (x 2 5)
            have b2900 := hb (x 2 13)
            clear * - r2898 b2899 b2900 d2885
            omega
          have d2901 : (x 2 5 && x 2 14).toNat = 0 := by
            have r2902 := hand1 (x 2 5) (x 2 14)
            have b2903 := hb (x 2 5)
            have b2904 := hb (x 2 5 && x 2 14)
            clear * - r2902 b2903 b2904 d2897
            omega
          have d2905 : (x 2 9).toNat = 0 := by
            have r2906 : (x 2 9).toNat ≤ (x 2 1).toNat := himp _ _ (hp9 2)
            have b2907 := hb (x 2 1)
            have b2908 := hb (x 2 9)
            clear * - r2906 b2907 b2908 d2824
            omega
          have d2909 : (x 2 9 && x 2 14).toNat = 0 := by
            have r2910 := hand1 (x 2 9) (x 2 14)
            have b2911 := hb (x 2 9)
            have b2912 := hb (x 2 9 && x 2 14)
            clear * - r2910 b2911 b2912 d2905
            omega
          have d2913 : (x 5 12).toNat = 0 := by
            have r2914 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e2915 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e2916 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b2917 := hb (x 2 3)
            have b2918 := hb (x 3 2)
            have b2919 := hb (x 4 13)
            have b2920 := hb (x 5 12)
            clear * - r2914 e2915 e2916 b2917 b2918 b2919 b2920 d2815
            omega
          have d2921 : (x 5 4).toNat = 0 := by
            have r2922 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
            have b2923 := hb (x 5 4)
            have b2924 := hb (x 5 12)
            clear * - r2922 b2923 b2924 d2913
            omega
          have d2925 : (x 5 4 && x 5 14).toNat = 0 := by
            have r2926 := hand1 (x 5 4) (x 5 14)
            have b2927 := hb (x 5 4)
            have b2928 := hb (x 5 4 && x 5 14)
            clear * - r2926 b2927 b2928 d2921
            omega
          have d2929 : (x 4 13).toNat = 0 := by
            have r2930 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e2931 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e2932 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b2933 := hb (x 2 3)
            have b2934 := hb (x 3 2)
            have b2935 := hb (x 4 13)
            have b2936 := hb (x 5 12)
            clear * - r2930 e2931 e2932 b2933 b2934 b2935 b2936 d2913 d2815
            omega
          have d2937 : (x 4 5).toNat = 0 := by
            have r2938 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
            have b2939 := hb (x 4 5)
            have b2940 := hb (x 4 13)
            clear * - r2938 b2939 b2940 d2929
            omega
          have d2941 : (x 4 5 && x 4 14).toNat = 0 := by
            have r2942 := hand1 (x 4 5) (x 4 14)
            have b2943 := hb (x 4 5)
            have b2944 := hb (x 4 5 && x 4 14)
            clear * - r2942 b2943 b2944 d2937
            omega
          have d2945 : (x 2 3).toNat = 0 := by
            have r2946 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e2947 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e2948 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b2949 := hb (x 2 3)
            have b2950 := hb (x 3 2)
            have b2951 := hb (x 4 13)
            have b2952 := hb (x 5 12)
            clear * - r2946 e2947 e2948 b2949 b2950 b2951 b2952 d2913 d2929 d2815
            omega
          have d2953 : (x 2 11).toNat = 0 := by
            have r2954 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
            have b2955 := hb (x 2 3)
            have b2956 := hb (x 2 11)
            clear * - r2954 b2955 b2956 d2945
            omega
          have d2957 : (x (-2) 4).toNat = 1 := by
            have r2958 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := by have q := hcov11 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b2959 := hb (x (-2) 4)
            have b2960 := hb (x 2 11)
            have b2961 := hb (x 1 1 && x 1 12)
            have b2962 := hb (x 0 2 && x 0 13)
            have b2963 := hb (x (-1) 3 && x (-1) 14)
            clear * - r2958 b2959 b2960 b2961 b2962 b2963 d2953 d2658 g72 g73
            omega
          have d2964 : (x (-2) 12).toNat = 1 := by
            have r2965 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
            have b2966 := hb (x (-2) 4)
            have b2967 := hb (x (-2) 12)
            clear * - r2965 b2966 b2967 d2957
            omega
          have d2968 : (x (-4) 2).toNat = 0 := by
            have r2969 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e2970 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
            have e2971 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
            have b2972 := hb (x (-5) 3)
            have b2973 := hb (x (-4) 2)
            have b2974 := hb (x (-3) 13)
            have b2975 := hb (x (-2) 12)
            clear * - r2969 e2970 e2971 b2972 b2973 b2974 b2975 d2964 g4
            omega
          have d2976 : (x (-4) 2 && x (-4) 13).toNat = 0 := by
            have r2977 := hand1 (x (-4) 2) (x (-4) 13)
            have b2978 := hb (x (-4) 2)
            have b2979 := hb (x (-4) 2 && x (-4) 13)
            clear * - r2977 b2978 b2979 d2968
            omega
          have d2980 : (x (-4) 10).toNat = 0 := by
            have r2981 : (x (-4) 10).toNat ≤ (x (-4) 2).toNat := himp _ _ (hp10 (-4))
            have b2982 := hb (x (-4) 2)
            have b2983 := hb (x (-4) 10)
            clear * - r2981 b2982 b2983 d2968
            omega
          have d2984 : (x (-4) 5 && x (-4) 10).toNat = 0 := by
            have r2985 := hand2 (x (-4) 5) (x (-4) 10)
            have b2986 := hb (x (-4) 10)
            have b2987 := hb (x (-4) 5 && x (-4) 10)
            clear * - r2985 b2986 b2987 d2980
            omega
          have d2988 : (x (-2) 13).toNat = 1 := by
            have r2989 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b2990 := hb (x (-4) 2)
            have b2991 := hb (x (-2) 13)
            have b2992 := hb (x (-3) 1 && x (-3) 14)
            clear * - r2989 b2990 b2991 b2992 g78 d2968
            omega
          have d2993 : (x (-2) 1).toNat = 1 := by
            have r2994 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
            have b2995 := hb (x (-2) 1)
            have b2996 := hb (x (-2) 13)
            clear * - r2994 b2995 b2996 d2988
            omega
          have d2997 : (x (-1) 14).toNat = 0 := by
            have r2998 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b2999 := hb (x (-2) 1)
            have b3000 := hb (x (-1) 14)
            clear * - r2998 b2999 b3000 d2993
            omega
          have d3001 : (x (-1) 6).toNat = 0 := by
            have r3002 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
            have b3003 := hb (x (-1) 6)
            have b3004 := hb (x (-1) 14)
            clear * - r3002 b3003 b3004 d2997
            omega
          have d3005 : (x (-1) 12).toNat = 0 := by
            have r3006 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e3007 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e3008 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b3009 := hb (x (-4) 3)
            have b3010 := hb (x (-3) 2)
            have b3011 := hb (x (-2) 13)
            have b3012 := hb (x (-1) 12)
            clear * - r3006 e3007 e3008 b3009 b3010 b3011 b3012 d2988
            omega
          have d3013 : (x (-3) 2).toNat = 0 := by
            have r3014 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e3015 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e3016 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b3017 := hb (x (-4) 3)
            have b3018 := hb (x (-3) 2)
            have b3019 := hb (x (-2) 13)
            have b3020 := hb (x (-1) 12)
            clear * - r3014 e3015 e3016 b3017 b3018 b3019 b3020 d3005 d2988
            omega
          have d3021 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
            have r3022 := hand1 (x (-3) 2) (x (-3) 12)
            have b3023 := hb (x (-3) 2)
            have b3024 := hb (x (-3) 2 && x (-3) 12)
            clear * - r3022 b3023 b3024 d3013
            omega
          have d3025 : (x (-3) 10).toNat = 0 := by
            have r3026 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
            have b3027 := hb (x (-3) 2)
            have b3028 := hb (x (-3) 10)
            clear * - r3026 b3027 b3028 d3013
            omega
          have d3029 : (x (-3) 4 && x (-3) 10).toNat = 0 := by
            have r3030 := hand2 (x (-3) 4) (x (-3) 10)
            have b3031 := hb (x (-3) 10)
            have b3032 := hb (x (-3) 4 && x (-3) 10)
            clear * - r3030 b3031 b3032 d3025
            omega
          have d3033 : (x (-4) 3).toNat = 0 := by
            have r3034 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e3035 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e3036 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b3037 := hb (x (-4) 3)
            have b3038 := hb (x (-3) 2)
            have b3039 := hb (x (-2) 13)
            have b3040 := hb (x (-1) 12)
            clear * - r3034 e3035 e3036 b3037 b3038 b3039 b3040 d3005 d2988 d3013
            omega
          have d3041 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
            have r3042 := hand1 (x (-4) 3) (x (-4) 13)
            have b3043 := hb (x (-4) 3)
            have b3044 := hb (x (-4) 3 && x (-4) 13)
            clear * - r3042 b3043 b3044 d3033
            omega
          have d3045 : (x (-4) 11).toNat = 0 := by
            have r3046 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
            have b3047 := hb (x (-4) 3)
            have b3048 := hb (x (-4) 11)
            clear * - r3046 b3047 b3048 d3033
            omega
          have d3049 : (x (-4) 5 && x (-4) 11).toNat = 0 := by
            have r3050 := hand2 (x (-4) 5) (x (-4) 11)
            have b3051 := hb (x (-4) 11)
            have b3052 := hb (x (-4) 5 && x (-4) 11)
            clear * - r3050 b3051 b3052 d3045
            omega
          have d3053 : (x (-4) 6 && x (-4) 11).toNat = 0 := by
            have r3054 := hand2 (x (-4) 6) (x (-4) 11)
            have b3055 := hb (x (-4) 11)
            have b3056 := hb (x (-4) 6 && x (-4) 11)
            clear * - r3054 b3055 b3056 d3045
            omega
          have d3057 : (x (-5) 3).toNat = 0 := by
            have r3058 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e3059 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
            have e3060 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
            have b3061 := hb (x (-5) 3)
            have b3062 := hb (x (-4) 2)
            have b3063 := hb (x (-3) 13)
            have b3064 := hb (x (-2) 12)
            clear * - r3058 e3059 e3060 b3061 b3062 b3063 b3064 d2964 g4 d2968
            omega
          have d3065 : (x (-5) 3 && x (-5) 14).toNat = 0 := by
            have r3066 := hand1 (x (-5) 3) (x (-5) 14)
            have b3067 := hb (x (-5) 3)
            have b3068 := hb (x (-5) 3 && x (-5) 14)
            clear * - r3066 b3067 b3068 d3057
            omega
          have d3069 : (x (-5) 11).toNat = 0 := by
            have r3070 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
            have b3071 := hb (x (-5) 3)
            have b3072 := hb (x (-5) 11)
            clear * - r3070 b3071 b3072 d3057
            omega
          have d3073 : (x (-5) 6 && x (-5) 11).toNat = 0 := by
            have r3074 := hand2 (x (-5) 6) (x (-5) 11)
            have b3075 := hb (x (-5) 11)
            have b3076 := hb (x (-5) 6 && x (-5) 11)
            clear * - r3074 b3075 b3076 d3069
            omega
          have d3077 : (x 4 6).toNat = 0 := by
            have r3078 : (x 4 6).toNat ≤ (x 4 14).toNat := himp _ _ (hp6 4)
            have b3079 := hb (x 4 6)
            have b3080 := hb (x 4 14)
            clear * - r3078 b3079 b3080 d2807
            omega
          have d3081 : (x 6 8).toNat = 0 := by
            have r3082 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e3083 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
            have e3084 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
            have e3085 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
            have e3086 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
            have e3087 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
            have e3088 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
            have b3089 := hb (x (-1) 7)
            have b3090 := hb (x 0 6)
            have b3091 := hb (x 1 5)
            have b3092 := hb (x 2 4)
            have b3093 := hb (x 3 11)
            have b3094 := hb (x 4 10)
            have b3095 := hb (x 5 9)
            have b3096 := hb (x 6 8)
            clear * - r3082 e3083 e3084 e3085 e3086 e3087 e3088 b3089 b3090 b3091 b3092 b3093 b3094 b3095 b3096 d2787 d2716 g29 g25 g16
            omega
          have d3097 : (x 6 2 && x 6 8).toNat = 0 := by
            have r3098 := hand2 (x 6 2) (x 6 8)
            have b3099 := hb (x 6 8)
            have b3100 := hb (x 6 2 && x 6 8)
            clear * - r3098 b3099 b3100 d3081
            omega
          have d3101 : (x 6 8 && x 6 13).toNat = 0 := by
            have r3102 := hand1 (x 6 8) (x 6 13)
            have b3103 := hb (x 6 8)
            have b3104 := hb (x 6 8 && x 6 13)
            clear * - r3102 b3103 b3104 d3081
            omega
          have d3105 : (x 5 9).toNat = 0 := by
            have r3106 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e3107 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
            have e3108 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
            have e3109 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
            have e3110 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
            have e3111 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
            have e3112 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
            have b3113 := hb (x (-1) 7)
            have b3114 := hb (x 0 6)
            have b3115 := hb (x 1 5)
            have b3116 := hb (x 2 4)
            have b3117 := hb (x 3 11)
            have b3118 := hb (x 4 10)
            have b3119 := hb (x 5 9)
            have b3120 := hb (x 6 8)
            clear * - r3106 e3107 e3108 e3109 e3110 e3111 e3112 b3113 b3114 b3115 b3116 b3117 b3118 b3119 b3120 d3081 d2787 d2716 g29 g25 g16
            omega
          have d3121 : (x 5 3 && x 5 9).toNat = 0 := by
            have r3122 := hand2 (x 5 3) (x 5 9)
            have b3123 := hb (x 5 9)
            have b3124 := hb (x 5 3 && x 5 9)
            clear * - r3122 b3123 b3124 d3105
            omega
          have d3125 : (x 5 9 && x 5 14).toNat = 0 := by
            have r3126 := hand1 (x 5 9) (x 5 14)
            have b3127 := hb (x 5 9)
            have b3128 := hb (x 5 9 && x 5 14)
            clear * - r3126 b3127 b3128 d3105
            omega
          have d3129 : (x 2 8).toNat = 0 := by
            have r3130 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e3131 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
            have e3132 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
            have e3133 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
            have e3134 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
            have e3135 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
            have e3136 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
            have b3137 := hb (x (-5) 7)
            have b3138 := hb (x (-4) 6)
            have b3139 := hb (x (-3) 5)
            have b3140 := hb (x (-2) 4)
            have b3141 := hb (x (-1) 11)
            have b3142 := hb (x 0 10)
            have b3143 := hb (x 1 9)
            have b3144 := hb (x 2 8)
            clear * - r3130 e3131 e3132 e3133 e3134 e3135 e3136 b3137 b3138 b3139 b3140 b3141 b3142 b3143 b3144 d2670 g20 g10 d2957 g1
            omega
          have d3145 : (x 2 8 && x 2 14).toNat = 0 := by
            have r3146 := hand1 (x 2 8) (x 2 14)
            have b3147 := hb (x 2 8)
            have b3148 := hb (x 2 8 && x 2 14)
            clear * - r3146 b3147 b3148 d3129
            omega
          have d3149 : (x (-4) 6).toNat = 0 := by
            have r3150 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e3151 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
            have e3152 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
            have e3153 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
            have e3154 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
            have e3155 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
            have e3156 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
            have b3157 := hb (x (-5) 7)
            have b3158 := hb (x (-4) 6)
            have b3159 := hb (x (-3) 5)
            have b3160 := hb (x (-2) 4)
            have b3161 := hb (x (-1) 11)
            have b3162 := hb (x 0 10)
            have b3163 := hb (x 1 9)
            have b3164 := hb (x 2 8)
            clear * - r3150 e3151 e3152 e3153 e3154 e3155 e3156 b3157 b3158 b3159 b3160 b3161 b3162 b3163 b3164 d3129 d2670 g20 g10 d2957 g1
            omega
          have d3165 : (x (-4) 6 && x (-4) 13).toNat = 0 := by
            have r3166 := hand1 (x (-4) 6) (x (-4) 13)
            have b3167 := hb (x (-4) 6)
            have b3168 := hb (x (-4) 6 && x (-4) 13)
            clear * - r3166 b3167 b3168 d3149
            omega
          have d3169 : (x (-4) 6 && x (-4) 9).toNat = 0 := by
            have r3170 := hand1 (x (-4) 6) (x (-4) 9)
            have b3171 := hb (x (-4) 6)
            have b3172 := hb (x (-4) 6 && x (-4) 9)
            clear * - r3170 b3171 b3172 d3149
            omega
          have d3173 : (x (-5) 7).toNat = 0 := by
            have r3174 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e3175 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
            have e3176 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
            have e3177 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
            have e3178 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
            have e3179 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
            have e3180 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
            have b3181 := hb (x (-5) 7)
            have b3182 := hb (x (-4) 6)
            have b3183 := hb (x (-3) 5)
            have b3184 := hb (x (-2) 4)
            have b3185 := hb (x (-1) 11)
            have b3186 := hb (x 0 10)
            have b3187 := hb (x 1 9)
            have b3188 := hb (x 2 8)
            clear * - r3174 e3175 e3176 e3177 e3178 e3179 e3180 b3181 b3182 b3183 b3184 b3185 b3186 b3187 b3188 d3129 d2670 g20 g10 d2957 g1 d3149
            omega
          have d3189 : (x (-5) 7 && x (-5) 14).toNat = 0 := by
            have r3190 := hand1 (x (-5) 7) (x (-5) 14)
            have b3191 := hb (x (-5) 7)
            have b3192 := hb (x (-5) 7 && x (-5) 14)
            clear * - r3190 b3191 b3192 d3173
            omega
          have d3193 : (x (-5) 7 && x (-5) 12).toNat = 0 := by
            have r3194 := hand1 (x (-5) 7) (x (-5) 12)
            have b3195 := hb (x (-5) 7)
            have b3196 := hb (x (-5) 7 && x (-5) 12)
            clear * - r3194 b3195 b3196 d3173
            omega
          have d3197 : (x (-5) 7 && x (-5) 10).toNat = 0 := by
            have r3198 := hand1 (x (-5) 7) (x (-5) 10)
            have b3199 := hb (x (-5) 7)
            have b3200 := hb (x (-5) 7 && x (-5) 10)
            clear * - r3198 b3199 b3200 d3173
            omega
          cases h3201 : x 1 4
          · have f3202 : (x 1 4).toNat = 0 := by rw [h3201]; rfl
            cases h3203 : x 1 7
            · have f3204 : (x 1 7).toNat = 0 := by rw [h3203]; rfl
              cases h3205 : x (-1) 8
              · have f3206 : (x (-1) 8).toNat = 0 := by rw [h3205]; rfl
                cases h3207 : x 1 8
                · have f3208 : (x 1 8).toNat = 0 := by rw [h3207]; rfl
                  cases h3209 : x (-2) 3
                  · have f3210 : (x (-2) 3).toNat = 0 := by rw [h3209]; rfl
                    have d3211 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
                      have r3212 := hand1 (x (-2) 3) (x (-2) 14)
                      have b3213 := hb (x (-2) 3)
                      have b3214 := hb (x (-2) 3 && x (-2) 14)
                      clear * - r3212 b3213 b3214 f3210
                      omega
                    have d3215 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
                      have r3216 := hand1 (x (-2) 3) (x (-2) 13)
                      have b3217 := hb (x (-2) 3)
                      have b3218 := hb (x (-2) 3 && x (-2) 13)
                      clear * - r3216 b3217 b3218 f3210
                      omega
                    have d3219 : (x (-3) 4).toNat = 1 := by
                      have r3220 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b3221 := hb (x (-3) 4)
                      have b3222 := hb (x 1 11)
                      have b3223 := hb (x 0 1 && x 0 12)
                      have b3224 := hb (x (-1) 2 && x (-1) 13)
                      have b3225 := hb (x (-2) 3 && x (-2) 14)
                      clear * - r3220 b3221 b3222 b3223 b3224 b3225 d2706 g70 g71 d3211
                      omega
                    have d3226 : (x (-3) 12).toNat = 1 := by
                      have r3227 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
                      have b3228 := hb (x (-3) 4)
                      have b3229 := hb (x (-3) 12)
                      clear * - r3227 b3228 b3229 d3219
                      omega
                    have d3230 : (x (-4) 13).toNat = 0 := by
                      have r3231 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e3232 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                      have e3233 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                      have b3234 := hb (x (-6) 3)
                      have b3235 := hb (x (-5) 2)
                      have b3236 := hb (x (-4) 13)
                      have b3237 := hb (x (-3) 12)
                      clear * - r3231 e3232 e3233 b3234 b3235 b3236 b3237 d3226
                      omega
                    have d3238 : (x (-4) 5).toNat = 0 := by
                      have r3239 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
                      have b3240 := hb (x (-4) 5)
                      have b3241 := hb (x (-4) 13)
                      clear * - r3239 b3240 b3241 d3230
                      omega
                    have d3242 : (x (-5) 2).toNat = 0 := by
                      have r3243 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e3244 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                      have e3245 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                      have b3246 := hb (x (-6) 3)
                      have b3247 := hb (x (-5) 2)
                      have b3248 := hb (x (-4) 13)
                      have b3249 := hb (x (-3) 12)
                      clear * - r3243 e3244 e3245 b3246 b3247 b3248 b3249 d3226 d3230
                      omega
                    have d3250 : (x (-4) 1 && x (-4) 14).toNat = 1 := by
                      have r3251 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b3252 := hb (x (-5) 2)
                      have b3253 := hb (x (-3) 13)
                      have b3254 := hb (x (-4) 1 && x (-4) 14)
                      clear * - r3251 b3252 b3253 b3254 g4 d3242
                      omega
                    have d3255 : (x (-4) 1).toNat = 1 := by
                      have r3256 := hand1 (x (-4) 1) (x (-4) 14)
                      have b3257 := hb (x (-4) 1)
                      have b3258 := hb (x (-4) 1 && x (-4) 14)
                      clear * - r3256 b3257 b3258 d3250
                      omega
                    have d3259 : (x (-3) 14).toNat = 0 := by
                      have r3260 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b3261 := hb (x (-4) 1)
                      have b3262 := hb (x (-3) 14)
                      clear * - r3260 b3261 b3262 d3255
                      omega
                    have d3263 : (x (-3) 4 && x (-3) 14).toNat = 0 := by
                      have r3264 := hand2 (x (-3) 4) (x (-3) 14)
                      have b3265 := hb (x (-3) 14)
                      have b3266 := hb (x (-3) 4 && x (-3) 14)
                      clear * - r3264 b3265 b3266 d3259
                      omega
                    have r3267 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b3268 := hb (x (-4) 5)
                    have b3269 := hb (x 1 10)
                    have b3270 := hb (x 0 1 && x 0 11)
                    have b3271 := hb (x (-1) 2 && x (-1) 12)
                    have b3272 := hb (x (-2) 3 && x (-2) 13)
                    have b3273 := hb (x (-3) 4 && x (-3) 14)
                    linarith only [r3267, b3268, b3269, b3270, b3271, b3272, b3273, g27, g58, d2680, d3215, d3263, d3238]
                  · have f3274 : (x (-2) 3).toNat = 1 := by rw [h3209]; rfl
                    have d3275 : (x 1 12).toNat = 0 := by
                      have r3276 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e3277 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
                      have e3278 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
                      have b3279 := hb (x (-2) 3)
                      have b3280 := hb (x (-1) 2)
                      have b3281 := hb (x 0 13)
                      have b3282 := hb (x 1 12)
                      clear * - r3276 e3277 e3278 b3279 b3280 b3281 b3282 g22 f2679 f3274
                      omega
                    cases h3283 : x (-2) 5
                    · have f3284 : (x (-2) 5).toNat = 0 := by rw [h3283]; rfl
                      have d3285 : (x 3 10).toNat = 1 := by
                        have r3286 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3287 := hb (x (-2) 5)
                        have b3288 := hb (x 3 10)
                        have b3289 := hb (x 2 1 && x 2 11)
                        have b3290 := hb (x 1 2 && x 1 12)
                        have b3291 := hb (x 0 3 && x 0 13)
                        have b3292 := hb (x (-1) 4 && x (-1) 14)
                        clear * - r3286 b3287 b3288 b3289 b3290 b3291 b3292 d2881 g61 g62 d2712 f3284
                        omega
                      have d3293 : (x 5 8).toNat = 0 := by
                        have r3294 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3295 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                        have e3296 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                        have e3297 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                        have e3298 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                        have e3299 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                        have e3300 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                        have b3301 := hb (x (-2) 7)
                        have b3302 := hb (x (-1) 6)
                        have b3303 := hb (x 0 5)
                        have b3304 := hb (x 1 4)
                        have b3305 := hb (x 2 11)
                        have b3306 := hb (x 3 10)
                        have b3307 := hb (x 4 9)
                        have b3308 := hb (x 5 8)
                        clear * - r3294 e3295 e3296 e3297 e3298 e3299 e3300 b3301 b3302 b3303 b3304 b3305 b3306 b3307 b3308 d3285 d2953 f3202 g15 d3001
                        omega
                      have d3309 : (x 4 9).toNat = 0 := by
                        have r3310 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3311 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                        have e3312 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                        have e3313 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                        have e3314 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                        have e3315 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                        have e3316 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                        have b3317 := hb (x (-2) 7)
                        have b3318 := hb (x (-1) 6)
                        have b3319 := hb (x 0 5)
                        have b3320 := hb (x 1 4)
                        have b3321 := hb (x 2 11)
                        have b3322 := hb (x 3 10)
                        have b3323 := hb (x 4 9)
                        have b3324 := hb (x 5 8)
                        clear * - r3310 e3311 e3312 e3313 e3314 e3315 e3316 b3317 b3318 b3319 b3320 b3321 b3322 b3323 b3324 d3293 d3285 d2953 f3202 g15 d3001
                        omega
                      have d3325 : (x (-2) 7).toNat = 0 := by
                        have r3326 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3327 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                        have e3328 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                        have e3329 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                        have e3330 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                        have e3331 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                        have e3332 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                        have b3333 := hb (x (-2) 7)
                        have b3334 := hb (x (-1) 6)
                        have b3335 := hb (x 0 5)
                        have b3336 := hb (x 1 4)
                        have b3337 := hb (x 2 11)
                        have b3338 := hb (x 3 10)
                        have b3339 := hb (x 4 9)
                        have b3340 := hb (x 5 8)
                        clear * - r3326 e3327 e3328 e3329 e3330 e3331 e3332 b3333 b3334 b3335 b3336 b3337 b3338 b3339 b3340 d3293 d3309 d3285 d2953 f3202 g15 d3001
                        omega
                      have d3341 : (x (-2) 3 && x (-2) 7).toNat = 0 := by
                        have r3342 := hand2 (x (-2) 3) (x (-2) 7)
                        have b3343 := hb (x (-2) 7)
                        have b3344 := hb (x (-2) 3 && x (-2) 7)
                        clear * - r3342 b3343 b3344 d3325
                        omega
                      have d3345 : (x (-2) 4 && x (-2) 7).toNat = 0 := by
                        have r3346 := hand2 (x (-2) 4) (x (-2) 7)
                        have b3347 := hb (x (-2) 7)
                        have b3348 := hb (x (-2) 4 && x (-2) 7)
                        clear * - r3346 b3347 b3348 d3325
                        omega
                      have r3349 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r3350 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r3351 : 1 ≤ (x 2 3).toNat + (x 1 1 && x 1 4).toNat + (x 0 2 && x 0 5).toNat + (x (-1) 3 && x (-1) 6).toNat + (x (-2) 4 && x (-2) 7).toNat + (x (-3) 5 && x (-3) 8).toNat + (x (-4) 6 && x (-4) 9).toNat + (x (-5) 7 && x (-5) 10).toNat + (x (-6) 8 && x (-6) 11).toNat + (x (-7) 9 && x (-7) 12).toNat + (x (-8) 10 && x (-8) 13).toNat + (x (-9) 11 && x (-9) 14).toNat + (x (-10) 12).toNat := by have q := hcov3 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r3352 : 1 ≤ (x 1 4).toNat + (x 0 1 && x 0 5).toNat + (x (-1) 2 && x (-1) 6).toNat + (x (-2) 3 && x (-2) 7).toNat + (x (-3) 4 && x (-3) 8).toNat + (x (-4) 5 && x (-4) 9).toNat + (x (-5) 6 && x (-5) 10).toNat + (x (-6) 7 && x (-6) 11).toNat + (x (-7) 8 && x (-7) 12).toNat + (x (-8) 9 && x (-8) 13).toNat + (x (-9) 10 && x (-9) 14).toNat + (x (-10) 11).toNat := by have q := hcov4 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e3353 : (x 0 1 && x 0 5).toNat = (x 0 5).toNat := handr _ _ (fun h => hp13 0 (hp5 0 (h)))
                      have e3354 : (x (-9) 10 && x (-9) 14).toNat = (x (-9) 10).toNat := handl _ _ (fun h => hp2 (-9) (hp10 (-9) (h)))
                      have r3355 : 1 ≤ (x (-11) 13).toNat + (x (-12) 1 && x (-12) 14).toNat + (x (-13) 2).toNat := by have q := hcov13 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r3356 : (x (-13) 2).toNat ≤ (x (-13) 14).toNat := himp _ _ (hp2 (-13))
                      have r3357 := hand1 (x (-6) 8) (x (-6) 11)
                      have r3358 := hand1 (x (-7) 9) (x (-7) 12)
                      have r3359 := hand1 (x (-8) 10) (x (-8) 13)
                      have r3360 := hand1 (x (-9) 11) (x (-9) 14)
                      have r3361 := hand1 (x (-3) 4) (x (-3) 8)
                      have r3362 := hand1 (x (-4) 5) (x (-4) 9)
                      have r3363 := hand1 (x (-5) 6) (x (-5) 10)
                      have r3364 := hand1 (x (-6) 7) (x (-6) 11)
                      have r3365 := hand1 (x (-7) 8) (x (-7) 12)
                      have r3366 := hand1 (x (-8) 9) (x (-8) 13)
                      have r3367 := hand2 (x (-12) 1) (x (-12) 14)
                      linarith only [r3349, r3350, r3351, r3352, e3353, e3354, r3355, r3356, r3357, r3358, r3359, r3360, r3361, r3362, r3363, r3364, r3365, r3366, r3367, d3173, d3149, g1, f3274, d2957, f2679, g7, g12, g13, g15, f2657, f3202, d2945, d2666, g33, g34, d3345, g35, d3169, d3197, d2692, d3341]
                    · have f3420 : (x (-2) 5).toNat = 1 := by rw [h3283]; rfl
                      have d3421 : (x 3 8).toNat = 0 := by
                        have r3422 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3423 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
                        have e3424 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
                        have e3425 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
                        have e3426 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
                        have e3427 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
                        have e3428 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
                        have b3429 := hb (x (-4) 7)
                        have b3430 := hb (x (-3) 6)
                        have b3431 := hb (x (-2) 5)
                        have b3432 := hb (x (-1) 4)
                        have b3433 := hb (x 0 11)
                        have b3434 := hb (x 1 10)
                        have b3435 := hb (x 2 9)
                        have b3436 := hb (x 3 8)
                        clear * - r3422 e3423 e3424 e3425 e3426 e3427 e3428 b3429 b3430 b3431 b3432 b3433 b3434 b3435 b3436 d2905 g27 g21 f2711 f3420
                        omega
                      have d3437 : (x 3 8 && x 3 13).toNat = 0 := by
                        have r3438 := hand1 (x 3 8) (x 3 13)
                        have b3439 := hb (x 3 8)
                        have b3440 := hb (x 3 8 && x 3 13)
                        clear * - r3438 b3439 b3440 d3421
                        omega
                      have d3441 : (x 3 8 && x 3 12).toNat = 0 := by
                        have r3442 := hand1 (x 3 8) (x 3 12)
                        have b3443 := hb (x 3 8)
                        have b3444 := hb (x 3 8 && x 3 12)
                        clear * - r3442 b3443 b3444 d3421
                        omega
                      cases h3445 : x (-2) 6
                      · have f3446 : (x (-2) 6).toNat = 0 := by rw [h3445]; rfl
                        have d3447 : (x (-2) 3 && x (-2) 6).toNat = 0 := by
                          have r3448 := hand2 (x (-2) 3) (x (-2) 6)
                          have b3449 := hb (x (-2) 6)
                          have b3450 := hb (x (-2) 3 && x (-2) 6)
                          clear * - r3448 b3449 b3450 f3446
                          omega
                        have r3451 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r3452 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r3453 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3454 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                        have e3455 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                        have e3456 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                        have e3457 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                        have e3458 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                        have e3459 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                        have r3460 : 1 ≤ (x 1 3).toNat + (x 0 1 && x 0 4).toNat + (x (-1) 2 && x (-1) 5).toNat + (x (-2) 3 && x (-2) 6).toNat + (x (-3) 4 && x (-3) 7).toNat + (x (-4) 5 && x (-4) 8).toNat + (x (-5) 6 && x (-5) 9).toNat + (x (-6) 7 && x (-6) 10).toNat + (x (-7) 8 && x (-7) 11).toNat + (x (-8) 9 && x (-8) 12).toNat + (x (-9) 10 && x (-9) 13).toNat + (x (-10) 11 && x (-10) 14).toNat + (x (-11) 12).toNat := by have q := hcov3 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r3461 : 1 ≤ (x 2 3).toNat + (x 1 1 && x 1 4).toNat + (x 0 2 && x 0 5).toNat + (x (-1) 3 && x (-1) 6).toNat + (x (-2) 4 && x (-2) 7).toNat + (x (-3) 5 && x (-3) 8).toNat + (x (-4) 6 && x (-4) 9).toNat + (x (-5) 7 && x (-5) 10).toNat + (x (-6) 8 && x (-6) 11).toNat + (x (-7) 9 && x (-7) 12).toNat + (x (-8) 10 && x (-8) 13).toNat + (x (-9) 11 && x (-9) 14).toNat + (x (-10) 12).toNat := by have q := hcov3 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r3462 : 1 ≤ (x 4 9).toNat + (x 3 1 && x 3 10).toNat + (x 2 2 && x 2 11).toNat + (x 1 3 && x 1 12).toNat + (x 0 4 && x 0 13).toNat + (x (-1) 5 && x (-1) 14).toNat + (x (-2) 6).toNat := by have q := hcov9 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r3463 : 1 ≤ (x (-11) 13).toNat + (x (-12) 1 && x (-12) 14).toNat + (x (-13) 2).toNat := by have q := hcov13 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r3464 : (x (-13) 2).toNat ≤ (x (-13) 14).toNat := himp _ _ (hp2 (-13))
                        have r3465 := hand1 (x (-3) 4) (x (-3) 7)
                        have r3466 := hand1 (x (-4) 5) (x (-4) 8)
                        have r3467 := hand1 (x (-5) 6) (x (-5) 9)
                        have r3468 := hand1 (x (-6) 7) (x (-6) 10)
                        have r3469 := hand1 (x (-7) 8) (x (-7) 11)
                        have r3470 := hand1 (x (-8) 9) (x (-8) 12)
                        have r3471 := hand1 (x (-9) 10) (x (-9) 13)
                        have r3472 := hand1 (x (-10) 11) (x (-10) 14)
                        have r3473 := hand2 (x (-2) 4) (x (-2) 7)
                        have r3474 := hand1 (x (-6) 8) (x (-6) 11)
                        have r3475 := hand1 (x (-7) 9) (x (-7) 12)
                        have r3476 := hand1 (x (-8) 10) (x (-8) 13)
                        have r3477 := hand1 (x (-9) 11) (x (-9) 14)
                        have r3478 := hand2 (x 3 1) (x 3 10)
                        have r3479 := hand2 (x (-12) 1) (x (-12) 14)
                        linarith only [r3451, r3452, r3453, e3454, e3455, e3456, e3457, e3458, e3459, r3460, r3461, r3462, r3463, r3464, r3465, r3466, r3467, r3468, r3469, r3470, r3471, r3472, r3473, r3474, r3475, r3476, r3477, r3478, r3479, d3173, d3149, g1, f3274, d2957, f3446, f2679, g7, d3001, g12, g13, g15, f2657, f2701, f3202, d2945, d2953, g31, g32, d3447, d2666, g33, g34, g35, d3169, d3197, d2877, d2702, g56, g57]
                      · have f3548 : (x (-2) 6).toNat = 1 := by rw [h3445]; rfl
                        cases h3549 : x 2 6
                        · have f3550 : (x 2 6).toNat = 0 := by rw [h3549]; rfl
                          cases h3551 : x (-2) 7
                          · have f3552 : (x (-2) 7).toNat = 0 := by rw [h3551]; rfl
                            have d3553 : (x (-2) 3 && x (-2) 7).toNat = 0 := by
                              have r3554 := hand2 (x (-2) 3) (x (-2) 7)
                              have b3555 := hb (x (-2) 7)
                              have b3556 := hb (x (-2) 3 && x (-2) 7)
                              clear * - r3554 b3555 b3556 f3552
                              omega
                            have d3557 : (x (-2) 4 && x (-2) 7).toNat = 0 := by
                              have r3558 := hand2 (x (-2) 4) (x (-2) 7)
                              have b3559 := hb (x (-2) 7)
                              have b3560 := hb (x (-2) 4 && x (-2) 7)
                              clear * - r3558 b3559 b3560 f3552
                              omega
                            have r3561 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r3562 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r3563 : 1 ≤ (x 2 3).toNat + (x 1 1 && x 1 4).toNat + (x 0 2 && x 0 5).toNat + (x (-1) 3 && x (-1) 6).toNat + (x (-2) 4 && x (-2) 7).toNat + (x (-3) 5 && x (-3) 8).toNat + (x (-4) 6 && x (-4) 9).toNat + (x (-5) 7 && x (-5) 10).toNat + (x (-6) 8 && x (-6) 11).toNat + (x (-7) 9 && x (-7) 12).toNat + (x (-8) 10 && x (-8) 13).toNat + (x (-9) 11 && x (-9) 14).toNat + (x (-10) 12).toNat := by have q := hcov3 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r3564 : 1 ≤ (x 1 4).toNat + (x 0 1 && x 0 5).toNat + (x (-1) 2 && x (-1) 6).toNat + (x (-2) 3 && x (-2) 7).toNat + (x (-3) 4 && x (-3) 8).toNat + (x (-4) 5 && x (-4) 9).toNat + (x (-5) 6 && x (-5) 10).toNat + (x (-6) 7 && x (-6) 11).toNat + (x (-7) 8 && x (-7) 12).toNat + (x (-8) 9 && x (-8) 13).toNat + (x (-9) 10 && x (-9) 14).toNat + (x (-10) 11).toNat := by have q := hcov4 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e3565 : (x 0 1 && x 0 5).toNat = (x 0 5).toNat := handr _ _ (fun h => hp13 0 (hp5 0 (h)))
                            have e3566 : (x (-9) 10 && x (-9) 14).toNat = (x (-9) 10).toNat := handl _ _ (fun h => hp2 (-9) (hp10 (-9) (h)))
                            have r3567 : 1 ≤ (x (-11) 13).toNat + (x (-12) 1 && x (-12) 14).toNat + (x (-13) 2).toNat := by have q := hcov13 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r3568 : (x (-13) 2).toNat ≤ (x (-13) 14).toNat := himp _ _ (hp2 (-13))
                            have r3569 := hand1 (x (-6) 8) (x (-6) 11)
                            have r3570 := hand1 (x (-7) 9) (x (-7) 12)
                            have r3571 := hand1 (x (-8) 10) (x (-8) 13)
                            have r3572 := hand1 (x (-9) 11) (x (-9) 14)
                            have r3573 := hand1 (x (-3) 4) (x (-3) 8)
                            have r3574 := hand1 (x (-4) 5) (x (-4) 9)
                            have r3575 := hand1 (x (-5) 6) (x (-5) 10)
                            have r3576 := hand1 (x (-6) 7) (x (-6) 11)
                            have r3577 := hand1 (x (-7) 8) (x (-7) 12)
                            have r3578 := hand1 (x (-8) 9) (x (-8) 13)
                            have r3579 := hand2 (x (-12) 1) (x (-12) 14)
                            linarith only [r3561, r3562, r3563, r3564, e3565, e3566, r3567, r3568, r3569, r3570, r3571, r3572, r3573, r3574, r3575, r3576, r3577, r3578, r3579, d3173, d3149, g1, f3274, d2957, f2679, g7, g12, g13, g15, f2657, f3202, d2945, d2666, g33, g34, d3557, g35, d3169, d3197, d2692, d3553]
                          · have f3632 : (x (-2) 7).toNat = 1 := by rw [h3551]; rfl
                            have d3633 : (x 5 8).toNat = 0 := by
                              have r3634 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e3635 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                              have e3636 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                              have e3637 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                              have e3638 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                              have e3639 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                              have e3640 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                              have b3641 := hb (x (-2) 7)
                              have b3642 := hb (x (-1) 6)
                              have b3643 := hb (x 0 5)
                              have b3644 := hb (x 1 4)
                              have b3645 := hb (x 2 11)
                              have b3646 := hb (x 3 10)
                              have b3647 := hb (x 4 9)
                              have b3648 := hb (x 5 8)
                              clear * - r3634 e3635 e3636 e3637 e3638 e3639 e3640 b3641 b3642 b3643 b3644 b3645 b3646 b3647 b3648 d2953 f3202 g15 d3001 f3632
                              omega
                            have d3649 : (x 4 9).toNat = 0 := by
                              have r3650 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e3651 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                              have e3652 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                              have e3653 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                              have e3654 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                              have e3655 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                              have e3656 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                              have b3657 := hb (x (-2) 7)
                              have b3658 := hb (x (-1) 6)
                              have b3659 := hb (x 0 5)
                              have b3660 := hb (x 1 4)
                              have b3661 := hb (x 2 11)
                              have b3662 := hb (x 3 10)
                              have b3663 := hb (x 4 9)
                              have b3664 := hb (x 5 8)
                              clear * - r3650 e3651 e3652 e3653 e3654 e3655 e3656 b3657 b3658 b3659 b3660 b3661 b3662 b3663 b3664 d3633 d2953 f3202 g15 d3001 f3632
                              omega
                            have d3665 : (x 3 10).toNat = 0 := by
                              have r3666 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e3667 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                              have e3668 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                              have e3669 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                              have e3670 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                              have e3671 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                              have e3672 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                              have b3673 := hb (x (-2) 7)
                              have b3674 := hb (x (-1) 6)
                              have b3675 := hb (x 0 5)
                              have b3676 := hb (x 1 4)
                              have b3677 := hb (x 2 11)
                              have b3678 := hb (x 3 10)
                              have b3679 := hb (x 4 9)
                              have b3680 := hb (x 5 8)
                              clear * - r3666 e3667 e3668 e3669 e3670 e3671 e3672 b3673 b3674 b3675 b3676 b3677 b3678 b3679 b3680 d3633 d3649 d2953 f3202 g15 d3001 f3632
                              omega
                            have r3681 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r3682 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r3683 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r3684 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e3685 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
                            have e3686 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
                            have e3687 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
                            have e3688 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
                            have e3689 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
                            have e3690 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
                            have r3691 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e3692 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                            have e3693 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                            have e3694 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                            have e3695 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                            have e3696 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                            have e3697 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                            have r3698 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e3699 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
                            have e3700 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
                            have e3701 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
                            have e3702 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
                            have e3703 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
                            have e3704 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
                            have r3705 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e3706 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                            have e3707 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                            have r3708 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e3709 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
                            have e3710 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
                            have r3711 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e3712 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                            have e3713 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                            have r3714 : 1 ≤ (x 11 5).toNat + (x 10 1 && x 10 6).toNat + (x 9 2 && x 9 7).toNat + (x 8 3 && x 8 8).toNat + (x 7 4 && x 7 9).toNat + (x 6 5 && x 6 10).toNat + (x 5 6 && x 5 11).toNat + (x 4 7 && x 4 12).toNat + (x 3 8 && x 3 13).toNat + (x 2 9 && x 2 14).toNat + (x 1 10).toNat := by have q := hcov5 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r3715 : 1 ≤ (x 14 5).toNat + (x 13 1 && x 13 6).toNat + (x 12 2 && x 12 7).toNat + (x 11 3 && x 11 8).toNat + (x 10 4 && x 10 9).toNat + (x 9 5 && x 9 10).toNat + (x 8 6 && x 8 11).toNat + (x 7 7 && x 7 12).toNat + (x 6 8 && x 6 13).toNat + (x 5 9 && x 5 14).toNat + (x 4 10).toNat := by have q := hcov5 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r3716 : 1 ≤ (x 9 10).toNat + (x 8 1 && x 8 11).toNat + (x 7 2 && x 7 12).toNat + (x 6 3 && x 6 13).toNat + (x 5 4 && x 5 14).toNat + (x 4 5).toNat := by have q := hcov10 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r3717 : 1 ≤ (x 11 10).toNat + (x 10 1 && x 10 11).toNat + (x 9 2 && x 9 12).toNat + (x 8 3 && x 8 13).toNat + (x 7 4 && x 7 14).toNat + (x 6 5).toNat := by have q := hcov10 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r3718 : 1 ≤ (x 14 11).toNat + (x 13 1 && x 13 12).toNat + (x 12 2 && x 12 13).toNat + (x 11 3 && x 11 14).toNat + (x 10 4).toNat := by have q := hcov11 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r3719 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r3720 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r3721 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
                            have r3722 := hand2 (x 10 1) (x 10 6)
                            have r3723 := hand2 (x 9 2) (x 9 7)
                            have r3724 := hand2 (x 8 3) (x 8 8)
                            have r3725 := hand2 (x 7 4) (x 7 9)
                            have r3726 := hand2 (x 6 5) (x 6 10)
                            have r3727 := hand1 (x 5 6) (x 5 11)
                            have r3728 := hand1 (x 13 1) (x 13 6)
                            have r3729 := hand1 (x 12 2) (x 12 7)
                            have r3730 := hand2 (x 11 3) (x 11 8)
                            have r3731 := hand2 (x 10 4) (x 10 9)
                            have r3732 := hand1 (x 9 5) (x 9 10)
                            have r3733 := hand1 (x 8 6) (x 8 11)
                            have r3734 := hand1 (x 7 7) (x 7 12)
                            have r3735 := hand2 (x 8 1) (x 8 11)
                            have r3736 := hand1 (x 7 2) (x 7 12)
                            have r3737 := hand1 (x 6 3) (x 6 13)
                            have r3738 := hand2 (x 10 1) (x 10 11)
                            have r3739 := hand2 (x 9 2) (x 9 12)
                            have r3740 := hand2 (x 8 3) (x 8 13)
                            have r3741 := hand1 (x 7 4) (x 7 14)
                            have r3742 := hand2 (x 13 1) (x 13 12)
                            have r3743 := hand2 (x 12 2) (x 12 13)
                            have r3744 := hand1 (x 11 3) (x 11 14)
                            have r3745 := hand1 (x 15 1) (x 15 12)
                            have r3746 := hand1 (x 14 2) (x 14 13)
                            have r3747 := hand1 (x 13 3) (x 13 14)
                            have r3748 := hand1 (x 15 1) (x 15 14)
                            have b3800 := hb (x 12 1)
                            linarith only [r3681, r3682, r3683, r3684, e3685, e3686, e3687, e3688, e3689, e3690, r3691, e3692, e3693, e3694, e3695, e3696, e3697, r3698, e3699, e3700, e3701, e3702, e3703, e3704, r3705, e3706, e3707, r3708, e3709, e3710, r3711, e3712, e3713, r3714, r3715, r3716, r3717, r3718, r3719, r3720, r3721, r3722, r3723, r3724, r3725, r3726, r3727, r3728, r3729, r3730, r3731, r3732, r3733, r3734, r3735, r3736, r3737, r3738, r3739, r3740, r3741, r3742, r3743, r3744, r3745, r3746, r3747, r3748, b3800, d2997, g22, g23, g27, d3275, g28, d2953, g30, d2674, d3665, d2716, d2832, d2937, d3649, d2787, d2837, d3633, d3105, d3081, d2853, d3437, d2909, d3101, d3125, d2925]
                        · have f3857 : (x 2 6).toNat = 1 := by rw [h3549]; rfl
                          have d3858 : (x 8 8).toNat = 0 := by
                            have r3859 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e3860 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                            have e3861 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                            have e3862 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                            have e3863 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                            have e3864 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                            have e3865 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                            have b3866 := hb (x 1 7)
                            have b3867 := hb (x 2 6)
                            have b3868 := hb (x 3 5)
                            have b3869 := hb (x 4 4)
                            have b3870 := hb (x 5 11)
                            have b3871 := hb (x 6 10)
                            have b3872 := hb (x 7 9)
                            have b3873 := hb (x 8 8)
                            clear * - r3859 e3860 e3861 e3862 e3863 e3864 e3865 b3866 b3867 b3868 b3869 b3870 b3871 b3872 b3873 d2857 f3857 f3204
                            omega
                          have d3874 : (x 8 3 && x 8 8).toNat = 0 := by
                            have r3875 := hand2 (x 8 3) (x 8 8)
                            have b3876 := hb (x 8 8)
                            have b3877 := hb (x 8 3 && x 8 8)
                            clear * - r3875 b3876 b3877 d3858
                            omega
                          have d3878 : (x 7 9).toNat = 0 := by
                            have r3879 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e3880 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                            have e3881 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                            have e3882 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                            have e3883 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                            have e3884 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                            have e3885 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                            have b3886 := hb (x 1 7)
                            have b3887 := hb (x 2 6)
                            have b3888 := hb (x 3 5)
                            have b3889 := hb (x 4 4)
                            have b3890 := hb (x 5 11)
                            have b3891 := hb (x 6 10)
                            have b3892 := hb (x 7 9)
                            have b3893 := hb (x 8 8)
                            clear * - r3879 e3880 e3881 e3882 e3883 e3884 e3885 b3886 b3887 b3888 b3889 b3890 b3891 b3892 b3893 d3858 d2857 f3857 f3204
                            omega
                          have d3894 : (x 7 4 && x 7 9).toNat = 0 := by
                            have r3895 := hand2 (x 7 4) (x 7 9)
                            have b3896 := hb (x 7 9)
                            have b3897 := hb (x 7 4 && x 7 9)
                            clear * - r3895 b3896 b3897 d3878
                            omega
                          have d3898 : (x 6 10).toNat = 0 := by
                            have r3899 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e3900 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                            have e3901 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                            have e3902 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                            have e3903 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                            have e3904 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                            have e3905 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                            have b3906 := hb (x 1 7)
                            have b3907 := hb (x 2 6)
                            have b3908 := hb (x 3 5)
                            have b3909 := hb (x 4 4)
                            have b3910 := hb (x 5 11)
                            have b3911 := hb (x 6 10)
                            have b3912 := hb (x 7 9)
                            have b3913 := hb (x 8 8)
                            clear * - r3899 e3900 e3901 e3902 e3903 e3904 e3905 b3906 b3907 b3908 b3909 b3910 b3911 b3912 b3913 d3858 d3878 d2857 f3857 f3204
                            omega
                          have d3914 : (x 6 1 && x 6 10).toNat = 0 := by
                            have r3915 := hand2 (x 6 1) (x 6 10)
                            have b3916 := hb (x 6 10)
                            have b3917 := hb (x 6 1 && x 6 10)
                            clear * - r3915 b3916 b3917 d3898
                            omega
                          have d3918 : (x 6 5 && x 6 10).toNat = 0 := by
                            have r3919 := hand2 (x 6 5) (x 6 10)
                            have b3920 := hb (x 6 10)
                            have b3921 := hb (x 6 5 && x 6 10)
                            clear * - r3919 b3920 b3921 d3898
                            omega
                          have d3922 : (x 5 11).toNat = 0 := by
                            have r3923 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e3924 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                            have e3925 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                            have e3926 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                            have e3927 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                            have e3928 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                            have e3929 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                            have b3930 := hb (x 1 7)
                            have b3931 := hb (x 2 6)
                            have b3932 := hb (x 3 5)
                            have b3933 := hb (x 4 4)
                            have b3934 := hb (x 5 11)
                            have b3935 := hb (x 6 10)
                            have b3936 := hb (x 7 9)
                            have b3937 := hb (x 8 8)
                            clear * - r3923 e3924 e3925 e3926 e3927 e3928 e3929 b3930 b3931 b3932 b3933 b3934 b3935 b3936 b3937 d3858 d3878 d3898 d2857 f3857 f3204
                            omega
                          have d3938 : (x 5 2 && x 5 11).toNat = 0 := by
                            have r3939 := hand2 (x 5 2) (x 5 11)
                            have b3940 := hb (x 5 11)
                            have b3941 := hb (x 5 2 && x 5 11)
                            clear * - r3939 b3940 b3941 d3922
                            omega
                          have d3942 : (x 3 4 && x 3 13).toNat = 1 := by
                            have r3943 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have b3944 := hb (x 1 6)
                            have b3945 := hb (x 7 9)
                            have b3946 := hb (x 6 1 && x 6 10)
                            have b3947 := hb (x 5 2 && x 5 11)
                            have b3948 := hb (x 4 3 && x 4 12)
                            have b3949 := hb (x 3 4 && x 3 13)
                            have b3950 := hb (x 2 5 && x 2 14)
                            clear * - r3943 b3944 b3945 b3946 b3947 b3948 b3949 b3950 d3878 d3914 d3938 d2845 d2901 g26
                            omega
                          have d3951 : (x 3 4).toNat = 1 := by
                            have r3952 := hand1 (x 3 4) (x 3 13)
                            have b3953 := hb (x 3 4)
                            have b3954 := hb (x 3 4 && x 3 13)
                            clear * - r3952 b3953 b3954 d3942
                            omega
                          have d3955 : (x 5 6 && x 5 11).toNat = 0 := by
                            have r3956 := hand2 (x 5 6) (x 5 11)
                            have b3957 := hb (x 5 11)
                            have b3958 := hb (x 5 6 && x 5 11)
                            clear * - r3956 b3957 b3958 d3922
                            omega
                          have d3959 : (x 3 5).toNat = 0 := by
                            have r3960 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e3961 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                            have e3962 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                            have e3963 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                            have e3964 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                            have e3965 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                            have e3966 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                            have b3967 := hb (x 1 7)
                            have b3968 := hb (x 2 6)
                            have b3969 := hb (x 3 5)
                            have b3970 := hb (x 4 4)
                            have b3971 := hb (x 5 11)
                            have b3972 := hb (x 6 10)
                            have b3973 := hb (x 7 9)
                            have b3974 := hb (x 8 8)
                            clear * - r3960 e3961 e3962 e3963 e3964 e3965 e3966 b3967 b3968 b3969 b3970 b3971 b3972 b3973 b3974 d3858 d3878 d3898 d3922 d2857 f3857 f3204
                            omega
                          have d3975 : (x 3 5 && x 3 12).toNat = 0 := by
                            have r3976 := hand1 (x 3 5) (x 3 12)
                            have b3977 := hb (x 3 5)
                            have b3978 := hb (x 3 5 && x 3 12)
                            clear * - r3976 b3977 b3978 d3959
                            omega
                          have d3979 : (x 3 5 && x 3 11).toNat = 0 := by
                            have r3980 := hand1 (x 3 5) (x 3 11)
                            have b3981 := hb (x 3 5)
                            have b3982 := hb (x 3 5 && x 3 11)
                            clear * - r3980 b3981 b3982 d3959
                            omega
                          have d3983 : (x 7 8).toNat = 0 := by
                            have r3984 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e3985 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
                            have e3986 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
                            have e3987 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
                            have e3988 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
                            have e3989 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
                            have e3990 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
                            have b3991 := hb (x 0 7)
                            have b3992 := hb (x 1 6)
                            have b3993 := hb (x 2 5)
                            have b3994 := hb (x 3 4)
                            have b3995 := hb (x 4 11)
                            have b3996 := hb (x 5 10)
                            have b3997 := hb (x 6 9)
                            have b3998 := hb (x 7 8)
                            clear * - r3984 e3985 e3986 e3987 e3988 e3989 e3990 b3991 b3992 b3993 b3994 b3995 b3996 b3997 b3998 d3951 d2897 g26 g17
                            omega
                          have d3999 : (x 7 1 && x 7 8).toNat = 0 := by
                            have r4000 := hand2 (x 7 1) (x 7 8)
                            have b4001 := hb (x 7 8)
                            have b4002 := hb (x 7 1 && x 7 8)
                            clear * - r4000 b4001 b4002 d3983
                            omega
                          have d4003 : (x 7 4 && x 7 8).toNat = 0 := by
                            have r4004 := hand2 (x 7 4) (x 7 8)
                            have b4005 := hb (x 7 8)
                            have b4006 := hb (x 7 4 && x 7 8)
                            clear * - r4004 b4005 b4006 d3983
                            omega
                          have d4007 : (x 6 9).toNat = 0 := by
                            have r4008 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e4009 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
                            have e4010 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
                            have e4011 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
                            have e4012 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
                            have e4013 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
                            have e4014 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
                            have b4015 := hb (x 0 7)
                            have b4016 := hb (x 1 6)
                            have b4017 := hb (x 2 5)
                            have b4018 := hb (x 3 4)
                            have b4019 := hb (x 4 11)
                            have b4020 := hb (x 5 10)
                            have b4021 := hb (x 6 9)
                            have b4022 := hb (x 7 8)
                            clear * - r4008 e4009 e4010 e4011 e4012 e4013 e4014 b4015 b4016 b4017 b4018 b4019 b4020 b4021 b4022 d3983 d3951 d2897 g26 g17
                            omega
                          have d4023 : (x 6 2 && x 6 9).toNat = 0 := by
                            have r4024 := hand2 (x 6 2) (x 6 9)
                            have b4025 := hb (x 6 9)
                            have b4026 := hb (x 6 2 && x 6 9)
                            clear * - r4024 b4025 b4026 d4007
                            omega
                          have d4027 : (x 6 5 && x 6 9).toNat = 0 := by
                            have r4028 := hand2 (x 6 5) (x 6 9)
                            have b4029 := hb (x 6 9)
                            have b4030 := hb (x 6 5 && x 6 9)
                            clear * - r4028 b4029 b4030 d4007
                            omega
                          have d4031 : (x 5 10).toNat = 0 := by
                            have r4032 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e4033 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
                            have e4034 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
                            have e4035 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
                            have e4036 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
                            have e4037 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
                            have e4038 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
                            have b4039 := hb (x 0 7)
                            have b4040 := hb (x 1 6)
                            have b4041 := hb (x 2 5)
                            have b4042 := hb (x 3 4)
                            have b4043 := hb (x 4 11)
                            have b4044 := hb (x 5 10)
                            have b4045 := hb (x 6 9)
                            have b4046 := hb (x 7 8)
                            clear * - r4032 e4033 e4034 e4035 e4036 e4037 e4038 b4039 b4040 b4041 b4042 b4043 b4044 b4045 b4046 d3983 d4007 d3951 d2897 g26 g17
                            omega
                          have d4047 : (x 5 3 && x 5 10).toNat = 0 := by
                            have r4048 := hand2 (x 5 3) (x 5 10)
                            have b4049 := hb (x 5 10)
                            have b4050 := hb (x 5 3 && x 5 10)
                            clear * - r4048 b4049 b4050 d4031
                            omega
                          have d4051 : (x 5 6 && x 5 10).toNat = 0 := by
                            have r4052 := hand2 (x 5 6) (x 5 10)
                            have b4053 := hb (x 5 10)
                            have b4054 := hb (x 5 6 && x 5 10)
                            clear * - r4052 b4053 b4054 d4031
                            omega
                          have d4055 : (x 4 11).toNat = 0 := by
                            have r4056 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e4057 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
                            have e4058 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
                            have e4059 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
                            have e4060 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
                            have e4061 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
                            have e4062 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
                            have b4063 := hb (x 0 7)
                            have b4064 := hb (x 1 6)
                            have b4065 := hb (x 2 5)
                            have b4066 := hb (x 3 4)
                            have b4067 := hb (x 4 11)
                            have b4068 := hb (x 5 10)
                            have b4069 := hb (x 6 9)
                            have b4070 := hb (x 7 8)
                            clear * - r4056 e4057 e4058 e4059 e4060 e4061 e4062 b4063 b4064 b4065 b4066 b4067 b4068 b4069 b4070 d3983 d4007 d4031 d3951 d2897 g26 g17
                            omega
                          have d4071 : (x 4 7 && x 4 11).toNat = 0 := by
                            have r4072 := hand2 (x 4 7) (x 4 11)
                            have b4073 := hb (x 4 11)
                            have b4074 := hb (x 4 7 && x 4 11)
                            clear * - r4072 b4073 b4074 d4055
                            omega
                          have d4075 : (x 8 7).toNat = 1 := by
                            have r4076 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := by have q := hcov7 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have b4077 := hb (x 0 8)
                            have b4078 := hb (x 8 7)
                            have b4079 := hb (x 7 1 && x 7 8)
                            have b4080 := hb (x 6 2 && x 6 9)
                            have b4081 := hb (x 5 3 && x 5 10)
                            have b4082 := hb (x 4 4 && x 4 11)
                            have b4083 := hb (x 3 5 && x 3 12)
                            have b4084 := hb (x 2 6 && x 2 13)
                            have b4085 := hb (x 1 7 && x 1 14)
                            clear * - r4076 b4077 b4078 b4079 b4080 b4081 b4082 b4083 b4084 b4085 d3999 d4023 d4047 d2865 d3975 d2889 g54 g18
                            omega
                          have d4086 : (x 15 8).toNat = 0 := by
                            have r4087 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e4088 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                            have e4089 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                            have e4090 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                            have e4091 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                            have e4092 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                            have e4093 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                            have b4094 := hb (x 8 7)
                            have b4095 := hb (x 9 6)
                            have b4096 := hb (x 10 5)
                            have b4097 := hb (x 11 4)
                            have b4098 := hb (x 12 11)
                            have b4099 := hb (x 13 10)
                            have b4100 := hb (x 14 9)
                            have b4101 := hb (x 15 8)
                            clear * - r4087 e4088 e4089 e4090 e4091 e4092 e4093 b4094 b4095 b4096 b4097 b4098 b4099 b4100 b4101 d4075
                            omega
                          have d4102 : (x 14 9).toNat = 0 := by
                            have r4103 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e4104 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                            have e4105 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                            have e4106 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                            have e4107 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                            have e4108 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                            have e4109 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                            have b4110 := hb (x 8 7)
                            have b4111 := hb (x 9 6)
                            have b4112 := hb (x 10 5)
                            have b4113 := hb (x 11 4)
                            have b4114 := hb (x 12 11)
                            have b4115 := hb (x 13 10)
                            have b4116 := hb (x 14 9)
                            have b4117 := hb (x 15 8)
                            clear * - r4103 e4104 e4105 e4106 e4107 e4108 e4109 b4110 b4111 b4112 b4113 b4114 b4115 b4116 b4117 d4086 d4075
                            omega
                          have d4118 : (x 13 10).toNat = 0 := by
                            have r4119 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e4120 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                            have e4121 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                            have e4122 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                            have e4123 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                            have e4124 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                            have e4125 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                            have b4126 := hb (x 8 7)
                            have b4127 := hb (x 9 6)
                            have b4128 := hb (x 10 5)
                            have b4129 := hb (x 11 4)
                            have b4130 := hb (x 12 11)
                            have b4131 := hb (x 13 10)
                            have b4132 := hb (x 14 9)
                            have b4133 := hb (x 15 8)
                            clear * - r4119 e4120 e4121 e4122 e4123 e4124 e4125 b4126 b4127 b4128 b4129 b4130 b4131 b4132 b4133 d4086 d4102 d4075
                            omega
                          have d4134 : (x 12 11).toNat = 0 := by
                            have r4135 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e4136 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                            have e4137 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                            have e4138 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                            have e4139 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                            have e4140 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                            have e4141 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                            have b4142 := hb (x 8 7)
                            have b4143 := hb (x 9 6)
                            have b4144 := hb (x 10 5)
                            have b4145 := hb (x 11 4)
                            have b4146 := hb (x 12 11)
                            have b4147 := hb (x 13 10)
                            have b4148 := hb (x 14 9)
                            have b4149 := hb (x 15 8)
                            clear * - r4135 e4136 e4137 e4138 e4139 e4140 e4141 b4142 b4143 b4144 b4145 b4146 b4147 b4148 b4149 d4086 d4102 d4118 d4075
                            omega
                          have d4150 : (x 11 4).toNat = 0 := by
                            have r4151 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e4152 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                            have e4153 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                            have e4154 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                            have e4155 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                            have e4156 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                            have e4157 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                            have b4158 := hb (x 8 7)
                            have b4159 := hb (x 9 6)
                            have b4160 := hb (x 10 5)
                            have b4161 := hb (x 11 4)
                            have b4162 := hb (x 12 11)
                            have b4163 := hb (x 13 10)
                            have b4164 := hb (x 14 9)
                            have b4165 := hb (x 15 8)
                            clear * - r4151 e4152 e4153 e4154 e4155 e4156 e4157 b4158 b4159 b4160 b4161 b4162 b4163 b4164 b4165 d4086 d4102 d4118 d4134 d4075
                            omega
                          have d4166 : (x 10 5).toNat = 0 := by
                            have r4167 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e4168 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                            have e4169 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                            have e4170 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                            have e4171 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                            have e4172 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                            have e4173 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                            have b4174 := hb (x 8 7)
                            have b4175 := hb (x 9 6)
                            have b4176 := hb (x 10 5)
                            have b4177 := hb (x 11 4)
                            have b4178 := hb (x 12 11)
                            have b4179 := hb (x 13 10)
                            have b4180 := hb (x 14 9)
                            have b4181 := hb (x 15 8)
                            clear * - r4167 e4168 e4169 e4170 e4171 e4172 e4173 b4174 b4175 b4176 b4177 b4178 b4179 b4180 b4181 d4086 d4102 d4118 d4134 d4150 d4075
                            omega
                          have d4182 : (x 9 6).toNat = 0 := by
                            have r4183 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e4184 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                            have e4185 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                            have e4186 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                            have e4187 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                            have e4188 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                            have e4189 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                            have b4190 := hb (x 8 7)
                            have b4191 := hb (x 9 6)
                            have b4192 := hb (x 10 5)
                            have b4193 := hb (x 11 4)
                            have b4194 := hb (x 12 11)
                            have b4195 := hb (x 13 10)
                            have b4196 := hb (x 14 9)
                            have b4197 := hb (x 15 8)
                            clear * - r4183 e4184 e4185 e4186 e4187 e4188 e4189 b4190 b4191 b4192 b4193 b4194 b4195 b4196 b4197 d4086 d4102 d4118 d4134 d4150 d4166 d4075
                            omega
                          have d4198 : (x 9 2 && x 9 6).toNat = 0 := by
                            have r4199 := hand2 (x 9 2) (x 9 6)
                            have b4200 := hb (x 9 6)
                            have b4201 := hb (x 9 2 && x 9 6)
                            clear * - r4199 b4200 b4201 d4182
                            omega
                          have d4202 : (x 8 3 && x 8 7).toNat = 1 := by
                            have r4203 : 1 ≤ (x 11 4).toNat + (x 10 1 && x 10 5).toNat + (x 9 2 && x 9 6).toNat + (x 8 3 && x 8 7).toNat + (x 7 4 && x 7 8).toNat + (x 6 5 && x 6 9).toNat + (x 5 6 && x 5 10).toNat + (x 4 7 && x 4 11).toNat + (x 3 8 && x 3 12).toNat + (x 2 9 && x 2 13).toNat + (x 1 10 && x 1 14).toNat + (x 0 11).toNat := by have q := hcov4 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e4204 : (x 10 1 && x 10 5).toNat = (x 10 5).toNat := handr _ _ (fun h => hp13 10 (hp5 10 (h)))
                            have e4205 : (x 1 10 && x 1 14).toNat = (x 1 10).toNat := handl _ _ (fun h => hp2 1 (hp10 1 (h)))
                            have b4206 := hb (x 0 11)
                            have b4207 := hb (x 1 10)
                            have b4208 := hb (x 10 5)
                            have b4209 := hb (x 11 4)
                            have b4210 := hb (x 9 2 && x 9 6)
                            have b4211 := hb (x 8 3 && x 8 7)
                            have b4212 := hb (x 7 4 && x 7 8)
                            have b4213 := hb (x 6 5 && x 6 9)
                            have b4214 := hb (x 5 6 && x 5 10)
                            have b4215 := hb (x 4 7 && x 4 11)
                            have b4216 := hb (x 3 8 && x 3 12)
                            have b4217 := hb (x 2 9 && x 2 13)
                            clear * - r4203 e4204 e4205 b4206 b4207 b4208 b4209 b4210 b4211 b4212 b4213 b4214 b4215 b4216 b4217 d4150 d4166 d4198 d4003 d4027 d4051 d4071 d3441 d2893 g27 g21
                            omega
                          have d4218 : (x 8 3).toNat = 1 := by
                            have r4219 := hand1 (x 8 3) (x 8 7)
                            have b4220 := hb (x 8 3)
                            have b4221 := hb (x 8 3 && x 8 7)
                            clear * - r4219 b4220 b4221 d4202
                            omega
                          have d4222 : (x 11 12).toNat = 0 := by
                            have r4223 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e4224 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                            have e4225 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                            have b4226 := hb (x 8 3)
                            have b4227 := hb (x 9 2)
                            have b4228 := hb (x 10 13)
                            have b4229 := hb (x 11 12)
                            clear * - r4223 e4224 e4225 b4226 b4227 b4228 b4229 d4218
                            omega
                          have d4230 : (x 10 13).toNat = 0 := by
                            have r4231 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e4232 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                            have e4233 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                            have b4234 := hb (x 8 3)
                            have b4235 := hb (x 9 2)
                            have b4236 := hb (x 10 13)
                            have b4237 := hb (x 11 12)
                            clear * - r4231 e4232 e4233 b4234 b4235 b4236 b4237 d4222 d4218
                            omega
                          have d4238 : (x 9 2).toNat = 0 := by
                            have r4239 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e4240 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                            have e4241 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                            have b4242 := hb (x 8 3)
                            have b4243 := hb (x 9 2)
                            have b4244 := hb (x 10 13)
                            have b4245 := hb (x 11 12)
                            clear * - r4239 e4240 e4241 b4242 b4243 b4244 b4245 d4222 d4230 d4218
                            omega
                          have d4246 : (x 9 2 && x 9 7).toNat = 0 := by
                            have r4247 := hand1 (x 9 2) (x 9 7)
                            have b4248 := hb (x 9 2)
                            have b4249 := hb (x 9 2 && x 9 7)
                            clear * - r4247 b4248 b4249 d4238
                            omega
                          have r4250 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r4251 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e4252 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
                          have e4253 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
                          have e4254 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
                          have e4255 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
                          have e4256 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
                          have e4257 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
                          have r4258 : 1 ≤ (x 11 5).toNat + (x 10 1 && x 10 6).toNat + (x 9 2 && x 9 7).toNat + (x 8 3 && x 8 8).toNat + (x 7 4 && x 7 9).toNat + (x 6 5 && x 6 10).toNat + (x 5 6 && x 5 11).toNat + (x 4 7 && x 4 12).toNat + (x 3 8 && x 3 13).toNat + (x 2 9 && x 2 14).toNat + (x 1 10).toNat := by have q := hcov5 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r4259 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r4260 : 1 ≤ (x 14 10).toNat + (x 13 1 && x 13 11).toNat + (x 12 2 && x 12 12).toNat + (x 11 3 && x 11 13).toNat + (x 10 4 && x 10 14).toNat + (x 9 5).toNat := by have q := hcov10 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r4261 := hand2 (x 10 1) (x 10 6)
                          have r4262 := hand2 (x 7 1) (x 7 7)
                          have r4263 := hand2 (x 13 1) (x 13 11)
                          have r4264 := hand1 (x 12 2) (x 12 12)
                          have r4265 := hand1 (x 11 3) (x 11 13)
                          have r4266 := hand1 (x 10 4) (x 10 14)
                          linarith only [r4250, r4251, e4252, e4253, e4254, e4255, e4256, e4257, r4258, r4259, r4260, r4261, r4262, r4263, r4264, r4265, r4266, g9, g23, g27, g28, g30, d2716, d2787, d3105, d3081, d4246, d3874, d3894, d3918, d3955, d2853, d3437, d2909, d3097, d3121, d2791, d3979, g48, g49, g50]
                · have f4312 : (x 1 8).toNat = 1 := by rw [h3207]; rfl
                  have d4313 : (x (-2) 11).toNat = 0 := by
                    have r4314 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4315 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                    have e4316 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                    have e4317 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                    have e4318 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                    have e4319 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                    have e4320 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                    have b4321 := hb (x (-6) 7)
                    have b4322 := hb (x (-5) 6)
                    have b4323 := hb (x (-4) 5)
                    have b4324 := hb (x (-3) 4)
                    have b4325 := hb (x (-2) 11)
                    have b4326 := hb (x (-1) 10)
                    have b4327 := hb (x 0 9)
                    have b4328 := hb (x 1 8)
                    clear * - r4314 e4315 e4316 e4317 e4318 e4319 e4320 b4321 b4322 b4323 b4324 b4325 b4326 b4327 b4328 f4312 g19 d2696
                    omega
                  have d4329 : (x (-2) 4 && x (-2) 11).toNat = 0 := by
                    have r4330 := hand2 (x (-2) 4) (x (-2) 11)
                    have b4331 := hb (x (-2) 11)
                    have b4332 := hb (x (-2) 4 && x (-2) 11)
                    clear * - r4330 b4331 b4332 d4313
                    omega
                  have d4333 : (x (-6) 4).toNat = 1 := by
                    have r4334 : 1 ≤ (x (-2) 11).toNat + (x (-3) 1 && x (-3) 12).toNat + (x (-4) 2 && x (-4) 13).toNat + (x (-5) 3 && x (-5) 14).toNat + (x (-6) 4).toNat := by have q := hcov11 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b4335 := hb (x (-6) 4)
                    have b4336 := hb (x (-2) 11)
                    have b4337 := hb (x (-3) 1 && x (-3) 12)
                    have b4338 := hb (x (-4) 2 && x (-4) 13)
                    have b4339 := hb (x (-5) 3 && x (-5) 14)
                    clear * - r4334 b4335 b4336 b4337 b4338 b4339 d4313 g66 d2976 d3065
                    omega
                  have d4340 : (x (-6) 12).toNat = 1 := by
                    have r4341 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
                    have b4342 := hb (x (-6) 4)
                    have b4343 := hb (x (-6) 12)
                    clear * - r4341 b4342 b4343 d4333
                    omega
                  have d4344 : (x (-7) 13).toNat = 0 := by
                    have r4345 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4346 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
                    have e4347 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
                    have b4348 := hb (x (-9) 3)
                    have b4349 := hb (x (-8) 2)
                    have b4350 := hb (x (-7) 13)
                    have b4351 := hb (x (-6) 12)
                    clear * - r4345 e4346 e4347 b4348 b4349 b4350 b4351 d4340
                    omega
                  have d4352 : (x (-7) 8 && x (-7) 13).toNat = 0 := by
                    have r4353 := hand2 (x (-7) 8) (x (-7) 13)
                    have b4354 := hb (x (-7) 13)
                    have b4355 := hb (x (-7) 8 && x (-7) 13)
                    clear * - r4353 b4354 b4355 d4344
                    omega
                  have d4356 : (x (-7) 5).toNat = 0 := by
                    have r4357 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
                    have b4358 := hb (x (-7) 5)
                    have b4359 := hb (x (-7) 13)
                    clear * - r4357 b4358 b4359 d4344
                    omega
                  have d4360 : (x (-8) 2).toNat = 0 := by
                    have r4361 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4362 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
                    have e4363 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
                    have b4364 := hb (x (-9) 3)
                    have b4365 := hb (x (-8) 2)
                    have b4366 := hb (x (-7) 13)
                    have b4367 := hb (x (-6) 12)
                    clear * - r4361 e4362 e4363 b4364 b4365 b4366 b4367 d4340 d4344
                    omega
                  have d4368 : (x (-8) 10).toNat = 0 := by
                    have r4369 : (x (-8) 10).toNat ≤ (x (-8) 2).toNat := himp _ _ (hp10 (-8))
                    have b4370 := hb (x (-8) 2)
                    have b4371 := hb (x (-8) 10)
                    clear * - r4369 b4370 b4371 d4360
                    omega
                  have d4372 : (x (-8) 1 && x (-8) 10).toNat = 0 := by
                    have r4373 := hand2 (x (-8) 1) (x (-8) 10)
                    have b4374 := hb (x (-8) 10)
                    have b4375 := hb (x (-8) 1 && x (-8) 10)
                    clear * - r4373 b4374 b4375 d4368
                    omega
                  have d4376 : (x (-9) 3).toNat = 0 := by
                    have r4377 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4378 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
                    have e4379 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
                    have b4380 := hb (x (-9) 3)
                    have b4381 := hb (x (-8) 2)
                    have b4382 := hb (x (-7) 13)
                    have b4383 := hb (x (-6) 12)
                    clear * - r4377 e4378 e4379 b4380 b4381 b4382 b4383 d4340 d4344 d4360
                    omega
                  have d4384 : (x (-9) 11).toNat = 0 := by
                    have r4385 : (x (-9) 11).toNat ≤ (x (-9) 3).toNat := himp _ _ (hp11 (-9))
                    have b4386 := hb (x (-9) 3)
                    have b4387 := hb (x (-9) 11)
                    clear * - r4385 b4386 b4387 d4376
                    omega
                  have d4388 : (x (-9) 2 && x (-9) 11).toNat = 0 := by
                    have r4389 := hand2 (x (-9) 2) (x (-9) 11)
                    have b4390 := hb (x (-9) 11)
                    have b4391 := hb (x (-9) 2 && x (-9) 11)
                    clear * - r4389 b4390 b4391 d4384
                    omega
                  have d4392 : (x (-3) 4).toNat = 0 := by
                    have r4393 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4394 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                    have e4395 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                    have e4396 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                    have e4397 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                    have e4398 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                    have e4399 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                    have b4400 := hb (x (-6) 7)
                    have b4401 := hb (x (-5) 6)
                    have b4402 := hb (x (-4) 5)
                    have b4403 := hb (x (-3) 4)
                    have b4404 := hb (x (-2) 11)
                    have b4405 := hb (x (-1) 10)
                    have b4406 := hb (x 0 9)
                    have b4407 := hb (x 1 8)
                    clear * - r4393 e4394 e4395 e4396 e4397 e4398 e4399 b4400 b4401 b4402 b4403 b4404 b4405 b4406 b4407 f4312 g19 d2696 d4313
                    omega
                  have d4408 : (x (-4) 5).toNat = 0 := by
                    have r4409 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4410 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                    have e4411 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                    have e4412 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                    have e4413 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                    have e4414 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                    have e4415 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                    have b4416 := hb (x (-6) 7)
                    have b4417 := hb (x (-5) 6)
                    have b4418 := hb (x (-4) 5)
                    have b4419 := hb (x (-3) 4)
                    have b4420 := hb (x (-2) 11)
                    have b4421 := hb (x (-1) 10)
                    have b4422 := hb (x 0 9)
                    have b4423 := hb (x 1 8)
                    clear * - r4409 e4410 e4411 e4412 e4413 e4414 e4415 b4416 b4417 b4418 b4419 b4420 b4421 b4422 b4423 f4312 g19 d2696 d4313 d4392
                    omega
                  have d4424 : (x (-5) 6).toNat = 0 := by
                    have r4425 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4426 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                    have e4427 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                    have e4428 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                    have e4429 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                    have e4430 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                    have e4431 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                    have b4432 := hb (x (-6) 7)
                    have b4433 := hb (x (-5) 6)
                    have b4434 := hb (x (-4) 5)
                    have b4435 := hb (x (-3) 4)
                    have b4436 := hb (x (-2) 11)
                    have b4437 := hb (x (-1) 10)
                    have b4438 := hb (x 0 9)
                    have b4439 := hb (x 1 8)
                    clear * - r4425 e4426 e4427 e4428 e4429 e4430 e4431 b4432 b4433 b4434 b4435 b4436 b4437 b4438 b4439 f4312 g19 d2696 d4313 d4392 d4408
                    omega
                  have d4440 : (x (-6) 7).toNat = 0 := by
                    have r4441 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4442 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                    have e4443 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                    have e4444 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                    have e4445 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                    have e4446 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                    have e4447 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                    have b4448 := hb (x (-6) 7)
                    have b4449 := hb (x (-5) 6)
                    have b4450 := hb (x (-4) 5)
                    have b4451 := hb (x (-3) 4)
                    have b4452 := hb (x (-2) 11)
                    have b4453 := hb (x (-1) 10)
                    have b4454 := hb (x 0 9)
                    have b4455 := hb (x 1 8)
                    clear * - r4441 e4442 e4443 e4444 e4445 e4446 e4447 b4448 b4449 b4450 b4451 b4452 b4453 b4454 b4455 f4312 g19 d2696 d4313 d4392 d4408 d4424
                    omega
                  have d4456 : (x (-6) 7 && x (-6) 12).toNat = 0 := by
                    have r4457 := hand1 (x (-6) 7) (x (-6) 12)
                    have b4458 := hb (x (-6) 7)
                    have b4459 := hb (x (-6) 7 && x (-6) 12)
                    clear * - r4457 b4458 b4459 d4440
                    omega
                  have d4460 : (x (-2) 8).toNat = 0 := by
                    have r4461 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4462 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                    have e4463 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                    have e4464 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                    have e4465 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                    have e4466 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                    have e4467 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                    have b4468 := hb (x (-9) 7)
                    have b4469 := hb (x (-8) 6)
                    have b4470 := hb (x (-7) 5)
                    have b4471 := hb (x (-6) 4)
                    have b4472 := hb (x (-5) 11)
                    have b4473 := hb (x (-4) 10)
                    have b4474 := hb (x (-3) 9)
                    have b4475 := hb (x (-2) 8)
                    clear * - r4461 e4462 e4463 e4464 e4465 e4466 e4467 b4468 b4469 b4470 b4471 b4472 b4473 b4474 b4475 g2 d2980 d3069 d4333 d4356
                    omega
                  have d4476 : (x (-2) 3 && x (-2) 8).toNat = 0 := by
                    have r4477 := hand2 (x (-2) 3) (x (-2) 8)
                    have b4478 := hb (x (-2) 8)
                    have b4479 := hb (x (-2) 3 && x (-2) 8)
                    clear * - r4477 b4478 b4479 d4460
                    omega
                  have d4480 : (x (-2) 8 && x (-2) 12).toNat = 0 := by
                    have r4481 := hand1 (x (-2) 8) (x (-2) 12)
                    have b4482 := hb (x (-2) 8)
                    have b4483 := hb (x (-2) 8 && x (-2) 12)
                    clear * - r4481 b4482 b4483 d4460
                    omega
                  have d4484 : (x 3 3 && x 3 7).toNat = 1 := by
                    have r4485 : 1 ≤ (x 6 4).toNat + (x 5 1 && x 5 5).toNat + (x 4 2 && x 4 6).toNat + (x 3 3 && x 3 7).toNat + (x 2 4 && x 2 8).toNat + (x 1 5 && x 1 9).toNat + (x 0 6 && x 0 10).toNat + (x (-1) 7 && x (-1) 11).toNat + (x (-2) 8 && x (-2) 12).toNat + (x (-3) 9 && x (-3) 13).toNat + (x (-4) 10 && x (-4) 14).toNat + (x (-5) 11).toNat := by have q := hcov4 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4486 : (x 5 1 && x 5 5).toNat = (x 5 5).toNat := handr _ _ (fun h => hp13 5 (hp5 5 (h)))
                    have e4487 : (x (-4) 10 && x (-4) 14).toNat = (x (-4) 10).toNat := handl _ _ (fun h => hp2 (-4) (hp10 (-4) (h)))
                    have b4488 := hb (x (-5) 11)
                    have b4489 := hb (x (-4) 10)
                    have b4490 := hb (x 5 5)
                    have b4491 := hb (x 6 4)
                    have b4492 := hb (x 4 2 && x 4 6)
                    have b4493 := hb (x 3 3 && x 3 7)
                    have b4494 := hb (x 2 4 && x 2 8)
                    have b4495 := hb (x 1 5 && x 1 9)
                    have b4496 := hb (x 0 6 && x 0 10)
                    have b4497 := hb (x (-1) 7 && x (-1) 11)
                    have b4498 := hb (x (-2) 8 && x (-2) 12)
                    have b4499 := hb (x (-3) 9 && x (-3) 13)
                    clear * - r4485 e4486 e4487 b4488 b4489 b4490 b4491 b4492 b4493 b4494 b4495 b4496 b4497 b4498 b4499 d2743 d2767 d2783 g36 g37 g38 g39 d4480 g40 d2980 d3069
                    omega
                  have d4500 : (x 3 7).toNat = 1 := by
                    have r4501 := hand2 (x 3 3) (x 3 7)
                    have b4502 := hb (x 3 7)
                    have b4503 := hb (x 3 3 && x 3 7)
                    clear * - r4501 b4502 b4503 d4484
                    omega
                  have d4504 : (x 10 8).toNat = 0 := by
                    have r4505 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4506 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                    have e4507 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                    have e4508 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                    have e4509 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                    have e4510 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                    have e4511 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                    have b4512 := hb (x 3 7)
                    have b4513 := hb (x 4 6)
                    have b4514 := hb (x 5 5)
                    have b4515 := hb (x 6 4)
                    have b4516 := hb (x 7 11)
                    have b4517 := hb (x 8 10)
                    have b4518 := hb (x 9 9)
                    have b4519 := hb (x 10 8)
                    clear * - r4505 e4506 e4507 e4508 e4509 e4510 e4511 b4512 b4513 b4514 b4515 b4516 b4517 b4518 b4519 d2743 d2767 d3077 d4500
                    omega
                  have d4520 : (x 9 9).toNat = 0 := by
                    have r4521 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4522 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                    have e4523 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                    have e4524 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                    have e4525 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                    have e4526 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                    have e4527 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                    have b4528 := hb (x 3 7)
                    have b4529 := hb (x 4 6)
                    have b4530 := hb (x 5 5)
                    have b4531 := hb (x 6 4)
                    have b4532 := hb (x 7 11)
                    have b4533 := hb (x 8 10)
                    have b4534 := hb (x 9 9)
                    have b4535 := hb (x 10 8)
                    clear * - r4521 e4522 e4523 e4524 e4525 e4526 e4527 b4528 b4529 b4530 b4531 b4532 b4533 b4534 b4535 d4504 d2743 d2767 d3077 d4500
                    omega
                  have d4536 : (x 8 10).toNat = 0 := by
                    have r4537 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4538 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                    have e4539 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                    have e4540 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                    have e4541 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                    have e4542 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                    have e4543 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                    have b4544 := hb (x 3 7)
                    have b4545 := hb (x 4 6)
                    have b4546 := hb (x 5 5)
                    have b4547 := hb (x 6 4)
                    have b4548 := hb (x 7 11)
                    have b4549 := hb (x 8 10)
                    have b4550 := hb (x 9 9)
                    have b4551 := hb (x 10 8)
                    clear * - r4537 e4538 e4539 e4540 e4541 e4542 e4543 b4544 b4545 b4546 b4547 b4548 b4549 b4550 b4551 d4504 d4520 d2743 d2767 d3077 d4500
                    omega
                  have d4552 : (x 8 1 && x 8 10).toNat = 0 := by
                    have r4553 := hand2 (x 8 1) (x 8 10)
                    have b4554 := hb (x 8 10)
                    have b4555 := hb (x 8 1 && x 8 10)
                    clear * - r4553 b4554 b4555 d4536
                    omega
                  have d4556 : (x 7 11).toNat = 0 := by
                    have r4557 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4558 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                    have e4559 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                    have e4560 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                    have e4561 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                    have e4562 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                    have e4563 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                    have b4564 := hb (x 3 7)
                    have b4565 := hb (x 4 6)
                    have b4566 := hb (x 5 5)
                    have b4567 := hb (x 6 4)
                    have b4568 := hb (x 7 11)
                    have b4569 := hb (x 8 10)
                    have b4570 := hb (x 9 9)
                    have b4571 := hb (x 10 8)
                    clear * - r4557 e4558 e4559 e4560 e4561 e4562 e4563 b4564 b4565 b4566 b4567 b4568 b4569 b4570 b4571 d4504 d4520 d4536 d2743 d2767 d3077 d4500
                    omega
                  have d4572 : (x 7 2 && x 7 11).toNat = 0 := by
                    have r4573 := hand2 (x 7 2) (x 7 11)
                    have b4574 := hb (x 7 11)
                    have b4575 := hb (x 7 2 && x 7 11)
                    clear * - r4573 b4574 b4575 d4556
                    omega
                  have d4576 : (x 3 6).toNat = 1 := by
                    have r4577 : 1 ≤ (x 9 9).toNat + (x 8 1 && x 8 10).toNat + (x 7 2 && x 7 11).toNat + (x 6 3 && x 6 12).toNat + (x 5 4 && x 5 13).toNat + (x 4 5 && x 4 14).toNat + (x 3 6).toNat := by have q := hcov9 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b4578 := hb (x 3 6)
                    have b4579 := hb (x 9 9)
                    have b4580 := hb (x 8 1 && x 8 10)
                    have b4581 := hb (x 7 2 && x 7 11)
                    have b4582 := hb (x 6 3 && x 6 12)
                    have b4583 := hb (x 5 4 && x 5 13)
                    have b4584 := hb (x 4 5 && x 4 14)
                    clear * - r4577 b4578 b4579 b4580 b4581 b4582 b4583 b4584 d4520 d4552 d4572 d2739 d2763 d2941
                    omega
                  have d4585 : (x 9 8).toNat = 0 := by
                    have r4586 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4587 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                    have e4588 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                    have e4589 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                    have e4590 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                    have e4591 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                    have e4592 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                    have b4593 := hb (x 2 7)
                    have b4594 := hb (x 3 6)
                    have b4595 := hb (x 4 5)
                    have b4596 := hb (x 5 4)
                    have b4597 := hb (x 6 11)
                    have b4598 := hb (x 7 10)
                    have b4599 := hb (x 8 9)
                    have b4600 := hb (x 9 8)
                    clear * - r4586 e4587 e4588 e4589 e4590 e4591 e4592 b4593 b4594 b4595 b4596 b4597 b4598 b4599 b4600 d2921 d2937 d4576
                    omega
                  have d4601 : (x 8 9).toNat = 0 := by
                    have r4602 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4603 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                    have e4604 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                    have e4605 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                    have e4606 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                    have e4607 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                    have e4608 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                    have b4609 := hb (x 2 7)
                    have b4610 := hb (x 3 6)
                    have b4611 := hb (x 4 5)
                    have b4612 := hb (x 5 4)
                    have b4613 := hb (x 6 11)
                    have b4614 := hb (x 7 10)
                    have b4615 := hb (x 8 9)
                    have b4616 := hb (x 9 8)
                    clear * - r4602 e4603 e4604 e4605 e4606 e4607 e4608 b4609 b4610 b4611 b4612 b4613 b4614 b4615 b4616 d4585 d2921 d2937 d4576
                    omega
                  have d4617 : (x 7 10).toNat = 0 := by
                    have r4618 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4619 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                    have e4620 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                    have e4621 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                    have e4622 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                    have e4623 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                    have e4624 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                    have b4625 := hb (x 2 7)
                    have b4626 := hb (x 3 6)
                    have b4627 := hb (x 4 5)
                    have b4628 := hb (x 5 4)
                    have b4629 := hb (x 6 11)
                    have b4630 := hb (x 7 10)
                    have b4631 := hb (x 8 9)
                    have b4632 := hb (x 9 8)
                    clear * - r4618 e4619 e4620 e4621 e4622 e4623 e4624 b4625 b4626 b4627 b4628 b4629 b4630 b4631 b4632 d4585 d4601 d2921 d2937 d4576
                    omega
                  have d4633 : (x 6 11).toNat = 0 := by
                    have r4634 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4635 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                    have e4636 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                    have e4637 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                    have e4638 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                    have e4639 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                    have e4640 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                    have b4641 := hb (x 2 7)
                    have b4642 := hb (x 3 6)
                    have b4643 := hb (x 4 5)
                    have b4644 := hb (x 5 4)
                    have b4645 := hb (x 6 11)
                    have b4646 := hb (x 7 10)
                    have b4647 := hb (x 8 9)
                    have b4648 := hb (x 9 8)
                    clear * - r4634 e4635 e4636 e4637 e4638 e4639 e4640 b4641 b4642 b4643 b4644 b4645 b4646 b4647 b4648 d4585 d4601 d4617 d2921 d2937 d4576
                    omega
                  have d4649 : (x 2 7).toNat = 0 := by
                    have r4650 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4651 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                    have e4652 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                    have e4653 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                    have e4654 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                    have e4655 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                    have e4656 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                    have b4657 := hb (x 2 7)
                    have b4658 := hb (x 3 6)
                    have b4659 := hb (x 4 5)
                    have b4660 := hb (x 5 4)
                    have b4661 := hb (x 6 11)
                    have b4662 := hb (x 7 10)
                    have b4663 := hb (x 8 9)
                    have b4664 := hb (x 9 8)
                    clear * - r4650 e4651 e4652 e4653 e4654 e4655 e4656 b4657 b4658 b4659 b4660 b4661 b4662 b4663 b4664 d4585 d4601 d4617 d4633 d2921 d2937 d4576
                    omega
                  have d4665 : (x (-6) 8).toNat = 1 := by
                    have r4666 : 1 ≤ (x 2 7).toNat + (x 1 1 && x 1 8).toNat + (x 0 2 && x 0 9).toNat + (x (-1) 3 && x (-1) 10).toNat + (x (-2) 4 && x (-2) 11).toNat + (x (-3) 5 && x (-3) 12).toNat + (x (-4) 6 && x (-4) 13).toNat + (x (-5) 7 && x (-5) 14).toNat + (x (-6) 8).toNat := by have q := hcov7 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b4667 := hb (x (-6) 8)
                    have b4668 := hb (x 2 7)
                    have b4669 := hb (x 1 1 && x 1 8)
                    have b4670 := hb (x 0 2 && x 0 9)
                    have b4671 := hb (x (-1) 3 && x (-1) 10)
                    have b4672 := hb (x (-2) 4 && x (-2) 11)
                    have b4673 := hb (x (-3) 5 && x (-3) 12)
                    have b4674 := hb (x (-4) 6 && x (-4) 13)
                    have b4675 := hb (x (-5) 7 && x (-5) 14)
                    clear * - r4666 b4667 b4668 b4669 b4670 b4671 b4672 b4673 b4674 b4675 d4649 d2662 g51 g52 d4329 g53 d3165 d3189
                    omega
                  have d4676 : (x (-7) 9).toNat = 0 := by
                    have r4677 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4678 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
                    have e4679 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
                    have e4680 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
                    have e4681 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
                    have e4682 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
                    have e4683 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
                    have b4684 := hb (x (-13) 7)
                    have b4685 := hb (x (-12) 6)
                    have b4686 := hb (x (-11) 5)
                    have b4687 := hb (x (-10) 4)
                    have b4688 := hb (x (-9) 11)
                    have b4689 := hb (x (-8) 10)
                    have b4690 := hb (x (-7) 9)
                    have b4691 := hb (x (-6) 8)
                    clear * - r4677 e4678 e4679 e4680 e4681 e4682 e4683 b4684 b4685 b4686 b4687 b4688 b4689 b4690 b4691 d4665 d4368 d4384
                    omega
                  have d4692 : (x (-10) 12).toNat = 0 := by
                    have r4693 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b4694 := hb (x (-12) 14)
                    have b4695 := hb (x (-11) 13)
                    have b4696 := hb (x (-10) 12)
                    have b4697 := hb (x (-9) 11)
                    have b4698 := hb (x (-8) 10)
                    have b4699 := hb (x (-7) 9)
                    have b4700 := hb (x (-6) 8)
                    have b4701 := hb (x (-5) 7)
                    have b4702 := hb (x (-4) 6)
                    have b4703 := hb (x (-3) 5)
                    have b4704 := hb (x (-2) 4)
                    have b4705 := hb (x (-1) 3)
                    have b4706 := hb (x 0 2)
                    have b4707 := hb (x 1 1)
                    clear * - r4693 b4694 b4695 b4696 b4697 b4698 b4699 b4700 b4701 b4702 b4703 b4704 b4705 b4706 b4707 f2657 g13 g7 d2957 g1 d3149 d3173 d4665 d4676 d4368 d4384
                    omega
                  have d4708 : (x (-10) 3 && x (-10) 12).toNat = 0 := by
                    have r4709 := hand2 (x (-10) 3) (x (-10) 12)
                    have b4710 := hb (x (-10) 12)
                    have b4711 := hb (x (-10) 3 && x (-10) 12)
                    clear * - r4709 b4710 b4711 d4692
                    omega
                  have d4712 : (x (-11) 13).toNat = 0 := by
                    have r4713 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b4714 := hb (x (-12) 14)
                    have b4715 := hb (x (-11) 13)
                    have b4716 := hb (x (-10) 12)
                    have b4717 := hb (x (-9) 11)
                    have b4718 := hb (x (-8) 10)
                    have b4719 := hb (x (-7) 9)
                    have b4720 := hb (x (-6) 8)
                    have b4721 := hb (x (-5) 7)
                    have b4722 := hb (x (-4) 6)
                    have b4723 := hb (x (-3) 5)
                    have b4724 := hb (x (-2) 4)
                    have b4725 := hb (x (-1) 3)
                    have b4726 := hb (x 0 2)
                    have b4727 := hb (x 1 1)
                    clear * - r4713 b4714 b4715 b4716 b4717 b4718 b4719 b4720 b4721 b4722 b4723 b4724 b4725 b4726 b4727 f2657 g13 g7 d2957 g1 d3149 d3173 d4665 d4676 d4368 d4384 d4692
                    omega
                  have d4728 : (x (-11) 4 && x (-11) 13).toNat = 0 := by
                    have r4729 := hand2 (x (-11) 4) (x (-11) 13)
                    have b4730 := hb (x (-11) 13)
                    have b4731 := hb (x (-11) 4 && x (-11) 13)
                    clear * - r4729 b4730 b4731 d4712
                    omega
                  have d4732 : (x (-12) 14).toNat = 0 := by
                    have r4733 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b4734 := hb (x (-12) 14)
                    have b4735 := hb (x (-11) 13)
                    have b4736 := hb (x (-10) 12)
                    have b4737 := hb (x (-9) 11)
                    have b4738 := hb (x (-8) 10)
                    have b4739 := hb (x (-7) 9)
                    have b4740 := hb (x (-6) 8)
                    have b4741 := hb (x (-5) 7)
                    have b4742 := hb (x (-4) 6)
                    have b4743 := hb (x (-3) 5)
                    have b4744 := hb (x (-2) 4)
                    have b4745 := hb (x (-1) 3)
                    have b4746 := hb (x 0 2)
                    have b4747 := hb (x 1 1)
                    clear * - r4733 b4734 b4735 b4736 b4737 b4738 b4739 b4740 b4741 b4742 b4743 b4744 b4745 b4746 b4747 f2657 g13 g7 d2957 g1 d3149 d3173 d4665 d4676 d4368 d4384 d4692 d4712
                    omega
                  have d4748 : (x (-12) 1 && x (-12) 14).toNat = 0 := by
                    have r4749 := hand2 (x (-12) 1) (x (-12) 14)
                    have b4750 := hb (x (-12) 14)
                    have b4751 := hb (x (-12) 1 && x (-12) 14)
                    clear * - r4749 b4750 b4751 d4732
                    omega
                  have d4752 : (x (-13) 2).toNat = 1 := by
                    have r4753 : 1 ≤ (x (-11) 13).toNat + (x (-12) 1 && x (-12) 14).toNat + (x (-13) 2).toNat := by have q := hcov13 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b4754 := hb (x (-13) 2)
                    have b4755 := hb (x (-11) 13)
                    have b4756 := hb (x (-12) 1 && x (-12) 14)
                    clear * - r4753 b4754 b4755 b4756 d4712 d4748
                    omega
                  have d4757 : (x (-11) 12).toNat = 0 := by
                    have r4758 : (x (-11) 12).toNat + (x (-12) 1 && x (-12) 13).toNat + (x (-13) 2 && x (-13) 14).toNat + (x (-14) 3).toNat = 1 := by have q := hd12 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4759 : (x (-12) 1 && x (-12) 13).toNat = (x (-12) 13).toNat := handr _ _ (fun h => hp13 (-12) (h))
                    have e4760 : (x (-13) 2 && x (-13) 14).toNat = (x (-13) 2).toNat := handl _ _ (fun h => hp2 (-13) (h))
                    have b4761 := hb (x (-14) 3)
                    have b4762 := hb (x (-13) 2)
                    have b4763 := hb (x (-12) 13)
                    have b4764 := hb (x (-11) 12)
                    clear * - r4758 e4759 e4760 b4761 b4762 b4763 b4764 d4752
                    omega
                  have d4765 : (x (-11) 4).toNat = 0 := by
                    have r4766 : (x (-11) 4).toNat ≤ (x (-11) 12).toNat := himp _ _ (hp4 (-11))
                    have b4767 := hb (x (-11) 4)
                    have b4768 := hb (x (-11) 12)
                    clear * - r4766 b4767 b4768 d4757
                    omega
                  have d4769 : (x (-12) 13).toNat = 0 := by
                    have r4770 : (x (-11) 12).toNat + (x (-12) 1 && x (-12) 13).toNat + (x (-13) 2 && x (-13) 14).toNat + (x (-14) 3).toNat = 1 := by have q := hd12 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4771 : (x (-12) 1 && x (-12) 13).toNat = (x (-12) 13).toNat := handr _ _ (fun h => hp13 (-12) (h))
                    have e4772 : (x (-13) 2 && x (-13) 14).toNat = (x (-13) 2).toNat := handl _ _ (fun h => hp2 (-13) (h))
                    have b4773 := hb (x (-14) 3)
                    have b4774 := hb (x (-13) 2)
                    have b4775 := hb (x (-12) 13)
                    have b4776 := hb (x (-11) 12)
                    clear * - r4770 e4771 e4772 b4773 b4774 b4775 b4776 d4757 d4752
                    omega
                  have d4777 : (x (-12) 5).toNat = 0 := by
                    have r4778 : (x (-12) 5).toNat ≤ (x (-12) 13).toNat := himp _ _ (hp5 (-12))
                    have b4779 := hb (x (-12) 5)
                    have b4780 := hb (x (-12) 13)
                    clear * - r4778 b4779 b4780 d4769
                    omega
                  have d4781 : (x (-12) 5 && x (-12) 14).toNat = 0 := by
                    have r4782 := hand1 (x (-12) 5) (x (-12) 14)
                    have b4783 := hb (x (-12) 5)
                    have b4784 := hb (x (-12) 5 && x (-12) 14)
                    clear * - r4782 b4783 b4784 d4777
                    omega
                  have d4785 : (x (-13) 6).toNat = 1 := by
                    have r4786 : 1 ≤ (x (-7) 9).toNat + (x (-8) 1 && x (-8) 10).toNat + (x (-9) 2 && x (-9) 11).toNat + (x (-10) 3 && x (-10) 12).toNat + (x (-11) 4 && x (-11) 13).toNat + (x (-12) 5 && x (-12) 14).toNat + (x (-13) 6).toNat := by have q := hcov9 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b4787 := hb (x (-13) 6)
                    have b4788 := hb (x (-7) 9)
                    have b4789 := hb (x (-8) 1 && x (-8) 10)
                    have b4790 := hb (x (-9) 2 && x (-9) 11)
                    have b4791 := hb (x (-10) 3 && x (-10) 12)
                    have b4792 := hb (x (-11) 4 && x (-11) 13)
                    have b4793 := hb (x (-12) 5 && x (-12) 14)
                    clear * - r4786 b4787 b4788 b4789 b4790 b4791 b4792 b4793 d4676 d4372 d4388 d4708 d4728 d4781
                    omega
                  have d4794 : (x (-7) 8).toNat = 0 := by
                    have r4795 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4796 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
                    have e4797 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
                    have e4798 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
                    have e4799 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
                    have e4800 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
                    have e4801 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
                    have b4802 := hb (x (-14) 7)
                    have b4803 := hb (x (-13) 6)
                    have b4804 := hb (x (-12) 5)
                    have b4805 := hb (x (-11) 4)
                    have b4806 := hb (x (-10) 11)
                    have b4807 := hb (x (-9) 10)
                    have b4808 := hb (x (-8) 9)
                    have b4809 := hb (x (-7) 8)
                    clear * - r4795 e4796 e4797 e4798 e4799 e4800 e4801 b4802 b4803 b4804 b4805 b4806 b4807 b4808 b4809 d4765 d4777 d4785
                    omega
                  have d4810 : (x (-8) 9).toNat = 0 := by
                    have r4811 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4812 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
                    have e4813 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
                    have e4814 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
                    have e4815 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
                    have e4816 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
                    have e4817 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
                    have b4818 := hb (x (-14) 7)
                    have b4819 := hb (x (-13) 6)
                    have b4820 := hb (x (-12) 5)
                    have b4821 := hb (x (-11) 4)
                    have b4822 := hb (x (-10) 11)
                    have b4823 := hb (x (-9) 10)
                    have b4824 := hb (x (-8) 9)
                    have b4825 := hb (x (-7) 8)
                    clear * - r4811 e4812 e4813 e4814 e4815 e4816 e4817 b4818 b4819 b4820 b4821 b4822 b4823 b4824 b4825 d4794 d4765 d4777 d4785
                    omega
                  have d4826 : (x (-8) 9 && x (-8) 14).toNat = 0 := by
                    have r4827 := hand1 (x (-8) 9) (x (-8) 14)
                    have b4828 := hb (x (-8) 9)
                    have b4829 := hb (x (-8) 9 && x (-8) 14)
                    clear * - r4827 b4828 b4829 d4810
                    omega
                  have d4830 : (x (-9) 10).toNat = 1 := by
                    have r4831 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := by have q := hcov5 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b4832 := hb (x (-9) 10)
                    have b4833 := hb (x 1 5)
                    have b4834 := hb (x 0 1 && x 0 6)
                    have b4835 := hb (x (-1) 2 && x (-1) 7)
                    have b4836 := hb (x (-2) 3 && x (-2) 8)
                    have b4837 := hb (x (-3) 4 && x (-3) 9)
                    have b4838 := hb (x (-4) 5 && x (-4) 10)
                    have b4839 := hb (x (-5) 6 && x (-5) 11)
                    have b4840 := hb (x (-6) 7 && x (-6) 12)
                    have b4841 := hb (x (-7) 8 && x (-7) 13)
                    have b4842 := hb (x (-8) 9 && x (-8) 14)
                    clear * - r4831 b4832 b4833 b4834 b4835 b4836 b4837 b4838 b4839 b4840 b4841 b4842 g25 g41 d2688 d4476 g42 d2984 d3073 d4456 d4352 d4826
                    omega
                  have d4843 : (x (-9) 2).toNat = 1 := by
                    have r4844 : (x (-9) 10).toNat ≤ (x (-9) 2).toNat := himp _ _ (hp10 (-9))
                    have b4845 := hb (x (-9) 2)
                    have b4846 := hb (x (-9) 10)
                    clear * - r4844 b4845 b4846 d4830
                    omega
                  have d4847 : (x (-7) 12).toNat = 0 := by
                    have r4848 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4849 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
                    have e4850 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
                    have b4851 := hb (x (-10) 3)
                    have b4852 := hb (x (-9) 2)
                    have b4853 := hb (x (-8) 13)
                    have b4854 := hb (x (-7) 12)
                    clear * - r4848 e4849 e4850 b4851 b4852 b4853 b4854 d4843
                    omega
                  have d4855 : (x (-8) 13).toNat = 0 := by
                    have r4856 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4857 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
                    have e4858 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
                    have b4859 := hb (x (-10) 3)
                    have b4860 := hb (x (-9) 2)
                    have b4861 := hb (x (-8) 13)
                    have b4862 := hb (x (-7) 12)
                    clear * - r4856 e4857 e4858 b4859 b4860 b4861 b4862 d4847 d4843
                    omega
                  have d4863 : (x (-10) 3).toNat = 0 := by
                    have r4864 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4865 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
                    have e4866 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
                    have b4867 := hb (x (-10) 3)
                    have b4868 := hb (x (-9) 2)
                    have b4869 := hb (x (-8) 13)
                    have b4870 := hb (x (-7) 12)
                    clear * - r4864 e4865 e4866 b4867 b4868 b4869 b4870 d4847 d4855 d4843
                    omega
                  have d4871 : (x (-10) 11).toNat = 0 := by
                    have r4872 : (x (-10) 11).toNat ≤ (x (-10) 3).toNat := himp _ _ (hp11 (-10))
                    have b4873 := hb (x (-10) 3)
                    have b4874 := hb (x (-10) 11)
                    clear * - r4872 b4873 b4874 d4863
                    omega
                  have r4875 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e4876 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
                  have e4877 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
                  have e4878 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
                  have e4879 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
                  have e4880 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
                  have e4881 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
                  have b4882 := hb (x (-14) 7)
                  have b4883 := hb (x (-13) 6)
                  have b4884 := hb (x (-12) 5)
                  have b4885 := hb (x (-11) 4)
                  have b4886 := hb (x (-10) 11)
                  have b4887 := hb (x (-9) 10)
                  have b4888 := hb (x (-8) 9)
                  have b4889 := hb (x (-7) 8)
                  linarith only [r4875, e4876, e4877, e4878, e4879, e4880, e4881, b4882, b4883, b4884, b4885, b4886, b4887, b4888, b4889, d4794, d4810, d4830, d4871, d4765, d4777, d4785]
              · have f4890 : (x (-1) 8).toNat = 1 := by rw [h3205]; rfl
                have d4891 : (x (-2) 9).toNat = 0 := by
                  have r4892 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e4893 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                  have e4894 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                  have e4895 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                  have e4896 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                  have e4897 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                  have e4898 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                  have b4899 := hb (x (-8) 7)
                  have b4900 := hb (x (-7) 6)
                  have b4901 := hb (x (-6) 5)
                  have b4902 := hb (x (-5) 4)
                  have b4903 := hb (x (-4) 11)
                  have b4904 := hb (x (-3) 10)
                  have b4905 := hb (x (-2) 9)
                  have b4906 := hb (x (-1) 8)
                  clear * - r4892 e4893 e4894 e4895 e4896 e4897 e4898 b4899 b4900 b4901 b4902 b4903 b4904 b4905 b4906 f4890 d3025 d3045
                  omega
                have d4907 : (x (-2) 3 && x (-2) 9).toNat = 0 := by
                  have r4908 := hand2 (x (-2) 3) (x (-2) 9)
                  have b4909 := hb (x (-2) 9)
                  have b4910 := hb (x (-2) 3 && x (-2) 9)
                  clear * - r4908 b4909 b4910 d4891
                  omega
                have d4911 : (x (-2) 4 && x (-2) 9).toNat = 0 := by
                  have r4912 := hand2 (x (-2) 4) (x (-2) 9)
                  have b4913 := hb (x (-2) 9)
                  have b4914 := hb (x (-2) 4 && x (-2) 9)
                  clear * - r4912 b4913 b4914 d4891
                  omega
                have d4915 : (x (-5) 4).toNat = 0 := by
                  have r4916 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e4917 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                  have e4918 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                  have e4919 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                  have e4920 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                  have e4921 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                  have e4922 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                  have b4923 := hb (x (-8) 7)
                  have b4924 := hb (x (-7) 6)
                  have b4925 := hb (x (-6) 5)
                  have b4926 := hb (x (-5) 4)
                  have b4927 := hb (x (-4) 11)
                  have b4928 := hb (x (-3) 10)
                  have b4929 := hb (x (-2) 9)
                  have b4930 := hb (x (-1) 8)
                  clear * - r4916 e4917 e4918 e4919 e4920 e4921 e4922 b4923 b4924 b4925 b4926 b4927 b4928 b4929 b4930 f4890 d4891 d3025 d3045
                  omega
                have d4931 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
                  have r4932 := hand1 (x (-5) 4) (x (-5) 14)
                  have b4933 := hb (x (-5) 4)
                  have b4934 := hb (x (-5) 4 && x (-5) 14)
                  clear * - r4932 b4933 b4934 d4915
                  omega
                have d4935 : (x (-6) 5).toNat = 0 := by
                  have r4936 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e4937 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                  have e4938 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                  have e4939 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                  have e4940 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                  have e4941 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                  have e4942 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                  have b4943 := hb (x (-8) 7)
                  have b4944 := hb (x (-7) 6)
                  have b4945 := hb (x (-6) 5)
                  have b4946 := hb (x (-5) 4)
                  have b4947 := hb (x (-4) 11)
                  have b4948 := hb (x (-3) 10)
                  have b4949 := hb (x (-2) 9)
                  have b4950 := hb (x (-1) 8)
                  clear * - r4936 e4937 e4938 e4939 e4940 e4941 e4942 b4943 b4944 b4945 b4946 b4947 b4948 b4949 b4950 f4890 d4891 d3025 d3045 d4915
                  omega
                have d4951 : (x (-2) 1 && x (-2) 11).toNat = 1 := by
                  have r4952 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b4953 := hb (x (-6) 5)
                  have b4954 := hb (x (-1) 10)
                  have b4955 := hb (x (-2) 1 && x (-2) 11)
                  have b4956 := hb (x (-3) 2 && x (-3) 12)
                  have b4957 := hb (x (-4) 3 && x (-4) 13)
                  have b4958 := hb (x (-5) 4 && x (-5) 14)
                  clear * - r4952 b4953 b4954 b4955 b4956 b4957 b4958 d2696 d3021 d3041 d4931 d4935
                  omega
                have d4959 : (x (-2) 11).toNat = 1 := by
                  have r4960 := hand2 (x (-2) 1) (x (-2) 11)
                  have b4961 := hb (x (-2) 11)
                  have b4962 := hb (x (-2) 1 && x (-2) 11)
                  clear * - r4960 b4961 b4962 d4951
                  omega
                have d4963 : (x (-2) 3).toNat = 1 := by
                  have r4964 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
                  have b4965 := hb (x (-2) 3)
                  have b4966 := hb (x (-2) 11)
                  clear * - r4964 b4965 b4966 d4959
                  omega
                have d4967 : (x 1 8).toNat = 0 := by
                  have r4968 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e4969 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                  have e4970 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                  have e4971 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                  have e4972 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                  have e4973 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                  have e4974 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                  have b4975 := hb (x (-6) 7)
                  have b4976 := hb (x (-5) 6)
                  have b4977 := hb (x (-4) 5)
                  have b4978 := hb (x (-3) 4)
                  have b4979 := hb (x (-2) 11)
                  have b4980 := hb (x (-1) 10)
                  have b4981 := hb (x 0 9)
                  have b4982 := hb (x 1 8)
                  clear * - r4968 e4969 e4970 e4971 e4972 e4973 e4974 b4975 b4976 b4977 b4978 b4979 b4980 b4981 b4982 g19 d2696 d4959
                  omega
                have d4983 : (x (-3) 4).toNat = 0 := by
                  have r4984 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e4985 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                  have e4986 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                  have e4987 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                  have e4988 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                  have e4989 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                  have e4990 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                  have b4991 := hb (x (-6) 7)
                  have b4992 := hb (x (-5) 6)
                  have b4993 := hb (x (-4) 5)
                  have b4994 := hb (x (-3) 4)
                  have b4995 := hb (x (-2) 11)
                  have b4996 := hb (x (-1) 10)
                  have b4997 := hb (x 0 9)
                  have b4998 := hb (x 1 8)
                  clear * - r4984 e4985 e4986 e4987 e4988 e4989 e4990 b4991 b4992 b4993 b4994 b4995 b4996 b4997 b4998 d4967 g19 d2696 d4959
                  omega
                have d4999 : (x (-4) 5).toNat = 0 := by
                  have r5000 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e5001 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                  have e5002 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                  have e5003 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                  have e5004 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                  have e5005 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                  have e5006 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                  have b5007 := hb (x (-6) 7)
                  have b5008 := hb (x (-5) 6)
                  have b5009 := hb (x (-4) 5)
                  have b5010 := hb (x (-3) 4)
                  have b5011 := hb (x (-2) 11)
                  have b5012 := hb (x (-1) 10)
                  have b5013 := hb (x 0 9)
                  have b5014 := hb (x 1 8)
                  clear * - r5000 e5001 e5002 e5003 e5004 e5005 e5006 b5007 b5008 b5009 b5010 b5011 b5012 b5013 b5014 d4967 g19 d2696 d4959 d4983
                  omega
                have d5015 : (x (-5) 6).toNat = 0 := by
                  have r5016 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e5017 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                  have e5018 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                  have e5019 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                  have e5020 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                  have e5021 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                  have e5022 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                  have b5023 := hb (x (-6) 7)
                  have b5024 := hb (x (-5) 6)
                  have b5025 := hb (x (-4) 5)
                  have b5026 := hb (x (-3) 4)
                  have b5027 := hb (x (-2) 11)
                  have b5028 := hb (x (-1) 10)
                  have b5029 := hb (x 0 9)
                  have b5030 := hb (x 1 8)
                  clear * - r5016 e5017 e5018 e5019 e5020 e5021 e5022 b5023 b5024 b5025 b5026 b5027 b5028 b5029 b5030 d4967 g19 d2696 d4959 d4983 d4999
                  omega
                have d5031 : (x (-5) 6 && x (-5) 12).toNat = 0 := by
                  have r5032 := hand1 (x (-5) 6) (x (-5) 12)
                  have b5033 := hb (x (-5) 6)
                  have b5034 := hb (x (-5) 6 && x (-5) 12)
                  clear * - r5032 b5033 b5034 d5015
                  omega
                have d5035 : (x (-6) 7).toNat = 0 := by
                  have r5036 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e5037 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                  have e5038 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                  have e5039 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                  have e5040 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                  have e5041 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                  have e5042 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                  have b5043 := hb (x (-6) 7)
                  have b5044 := hb (x (-5) 6)
                  have b5045 := hb (x (-4) 5)
                  have b5046 := hb (x (-3) 4)
                  have b5047 := hb (x (-2) 11)
                  have b5048 := hb (x (-1) 10)
                  have b5049 := hb (x 0 9)
                  have b5050 := hb (x 1 8)
                  clear * - r5036 e5037 e5038 e5039 e5040 e5041 e5042 b5043 b5044 b5045 b5046 b5047 b5048 b5049 b5050 d4967 g19 d2696 d4959 d4983 d4999 d5015
                  omega
                have d5051 : (x (-6) 7 && x (-6) 13).toNat = 0 := by
                  have r5052 := hand1 (x (-6) 7) (x (-6) 13)
                  have b5053 := hb (x (-6) 7)
                  have b5054 := hb (x (-6) 7 && x (-6) 13)
                  clear * - r5052 b5053 b5054 d5035
                  omega
                have r5055 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r5056 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r5057 : 1 ≤ (x 2 5).toNat + (x 1 1 && x 1 6).toNat + (x 0 2 && x 0 7).toNat + (x (-1) 3 && x (-1) 8).toNat + (x (-2) 4 && x (-2) 9).toNat + (x (-3) 5 && x (-3) 10).toNat + (x (-4) 6 && x (-4) 11).toNat + (x (-5) 7 && x (-5) 12).toNat + (x (-6) 8 && x (-6) 13).toNat + (x (-7) 9 && x (-7) 14).toNat + (x (-8) 10).toNat := by have q := hcov5 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r5058 : 1 ≤ (x 1 6).toNat + (x 0 1 && x 0 7).toNat + (x (-1) 2 && x (-1) 8).toNat + (x (-2) 3 && x (-2) 9).toNat + (x (-3) 4 && x (-3) 10).toNat + (x (-4) 5 && x (-4) 11).toNat + (x (-5) 6 && x (-5) 12).toNat + (x (-6) 7 && x (-6) 13).toNat + (x (-7) 8 && x (-7) 14).toNat + (x (-8) 9).toNat := by have q := hcov6 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r5059 : 1 ≤ (x (-11) 13).toNat + (x (-12) 1 && x (-12) 14).toNat + (x (-13) 2).toNat := by have q := hcov13 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r5060 : (x (-13) 2).toNat ≤ (x (-13) 14).toNat := himp _ _ (hp2 (-13))
                have r5061 := hand1 (x (-6) 8) (x (-6) 13)
                have r5062 := hand1 (x (-7) 9) (x (-7) 14)
                have r5063 := hand1 (x (-7) 8) (x (-7) 14)
                have r5064 := hand2 (x (-12) 1) (x (-12) 14)
                linarith only [r5055, r5056, r5057, r5058, r5059, r5060, r5061, r5062, r5063, r5064, d5035, d5015, d3173, d4999, d3149, d4983, g1, d4963, d2957, f2679, g7, g12, g13, f2657, g26, d2897, g43, g44, g45, d4911, g46, d3053, d3193, g47, d2684, d4907, d3029, d3049, d5031, d5051]
            · have f5114 : (x 1 7).toNat = 1 := by rw [h3203]; rfl
              have d5115 : (x 8 8).toNat = 0 := by
                have r5116 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e5117 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e5118 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e5119 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e5120 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e5121 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e5122 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b5123 := hb (x 1 7)
                have b5124 := hb (x 2 6)
                have b5125 := hb (x 3 5)
                have b5126 := hb (x 4 4)
                have b5127 := hb (x 5 11)
                have b5128 := hb (x 6 10)
                have b5129 := hb (x 7 9)
                have b5130 := hb (x 8 8)
                clear * - r5116 e5117 e5118 e5119 e5120 e5121 e5122 b5123 b5124 b5125 b5126 b5127 b5128 b5129 b5130 d2857 f5114
                omega
              have d5131 : (x 8 2 && x 8 8).toNat = 0 := by
                have r5132 := hand2 (x 8 2) (x 8 8)
                have b5133 := hb (x 8 8)
                have b5134 := hb (x 8 2 && x 8 8)
                clear * - r5132 b5133 b5134 d5115
                omega
              have d5135 : (x 7 9).toNat = 0 := by
                have r5136 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e5137 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e5138 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e5139 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e5140 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e5141 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e5142 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b5143 := hb (x 1 7)
                have b5144 := hb (x 2 6)
                have b5145 := hb (x 3 5)
                have b5146 := hb (x 4 4)
                have b5147 := hb (x 5 11)
                have b5148 := hb (x 6 10)
                have b5149 := hb (x 7 9)
                have b5150 := hb (x 8 8)
                clear * - r5136 e5137 e5138 e5139 e5140 e5141 e5142 b5143 b5144 b5145 b5146 b5147 b5148 b5149 b5150 d5115 d2857 f5114
                omega
              have d5151 : (x 7 3 && x 7 9).toNat = 0 := by
                have r5152 := hand2 (x 7 3) (x 7 9)
                have b5153 := hb (x 7 9)
                have b5154 := hb (x 7 3 && x 7 9)
                clear * - r5152 b5153 b5154 d5135
                omega
              have d5155 : (x 6 10).toNat = 0 := by
                have r5156 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e5157 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e5158 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e5159 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e5160 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e5161 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e5162 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b5163 := hb (x 1 7)
                have b5164 := hb (x 2 6)
                have b5165 := hb (x 3 5)
                have b5166 := hb (x 4 4)
                have b5167 := hb (x 5 11)
                have b5168 := hb (x 6 10)
                have b5169 := hb (x 7 9)
                have b5170 := hb (x 8 8)
                clear * - r5156 e5157 e5158 e5159 e5160 e5161 e5162 b5163 b5164 b5165 b5166 b5167 b5168 b5169 b5170 d5115 d5135 d2857 f5114
                omega
              have d5171 : (x 5 11).toNat = 0 := by
                have r5172 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e5173 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e5174 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e5175 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e5176 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e5177 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e5178 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b5179 := hb (x 1 7)
                have b5180 := hb (x 2 6)
                have b5181 := hb (x 3 5)
                have b5182 := hb (x 4 4)
                have b5183 := hb (x 5 11)
                have b5184 := hb (x 6 10)
                have b5185 := hb (x 7 9)
                have b5186 := hb (x 8 8)
                clear * - r5172 e5173 e5174 e5175 e5176 e5177 e5178 b5179 b5180 b5181 b5182 b5183 b5184 b5185 b5186 d5115 d5135 d5155 d2857 f5114
                omega
              have d5187 : (x 3 5).toNat = 0 := by
                have r5188 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e5189 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e5190 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e5191 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e5192 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e5193 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e5194 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b5195 := hb (x 1 7)
                have b5196 := hb (x 2 6)
                have b5197 := hb (x 3 5)
                have b5198 := hb (x 4 4)
                have b5199 := hb (x 5 11)
                have b5200 := hb (x 6 10)
                have b5201 := hb (x 7 9)
                have b5202 := hb (x 8 8)
                clear * - r5188 e5189 e5190 e5191 e5192 e5193 e5194 b5195 b5196 b5197 b5198 b5199 b5200 b5201 b5202 d5115 d5135 d5155 d5171 d2857 f5114
                omega
              have d5203 : (x 3 5 && x 3 11).toNat = 0 := by
                have r5204 := hand1 (x 3 5) (x 3 11)
                have b5205 := hb (x 3 5)
                have b5206 := hb (x 3 5 && x 3 11)
                clear * - r5204 b5205 b5206 d5187
                omega
              have r5207 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r5208 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e5209 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
              have e5210 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
              have e5211 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
              have e5212 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
              have e5213 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
              have e5214 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
              have r5215 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e5216 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
              have e5217 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
              have e5218 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
              have e5219 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
              have e5220 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
              have e5221 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
              have r5222 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r5223 : 1 ≤ (x 10 6).toNat + (x 9 1 && x 9 7).toNat + (x 8 2 && x 8 8).toNat + (x 7 3 && x 7 9).toNat + (x 6 4 && x 6 10).toNat + (x 5 5 && x 5 11).toNat + (x 4 6 && x 4 12).toNat + (x 3 7 && x 3 13).toNat + (x 2 8 && x 2 14).toNat + (x 1 9).toNat := by have q := hcov6 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r5224 : 1 ≤ (x 8 10).toNat + (x 7 1 && x 7 11).toNat + (x 6 2 && x 6 12).toNat + (x 5 3 && x 5 13).toNat + (x 4 4 && x 4 14).toNat + (x 3 5).toNat := by have q := hcov10 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r5225 : 1 ≤ (x 14 10).toNat + (x 13 1 && x 13 11).toNat + (x 12 2 && x 12 12).toNat + (x 11 3 && x 11 13).toNat + (x 10 4 && x 10 14).toNat + (x 9 5).toNat := by have q := hcov10 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r5226 := hand2 (x 7 1) (x 7 7)
              have r5227 := hand2 (x 9 1) (x 9 7)
              have r5228 := hand1 (x 3 7) (x 3 13)
              have r5229 := hand2 (x 7 1) (x 7 11)
              have r5230 := hand2 (x 13 1) (x 13 11)
              have r5231 := hand1 (x 12 2) (x 12 12)
              have r5232 := hand1 (x 11 3) (x 11 13)
              have r5233 := hand1 (x 10 4) (x 10 14)
              linarith only [r5207, r5208, e5209, e5210, e5211, e5212, e5213, e5214, r5215, e5216, e5217, e5218, e5219, e5220, e5221, r5222, r5223, r5224, r5225, r5226, r5227, r5228, r5229, r5230, r5231, r5232, r5233, g9, g23, d2670, g28, g30, d5187, d2716, d3077, d2787, d2767, d3105, d2743, d3081, d3097, d3121, d2791, d5203, g48, g49, g50, d5131, d5151, d2747, d2771, d2849, d3145, d2735, d2759, d2861]
          · have f5291 : (x 1 4).toNat = 1 := by rw [h3201]; rfl
            have d5292 : (x 1 12).toNat = 1 := by
              have r5293 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
              have b5294 := hb (x 1 4)
              have b5295 := hb (x 1 12)
              clear * - r5293 b5294 b5295 f5291
              omega
            have d5296 : (x (-2) 3).toNat = 0 := by
              have r5297 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e5298 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
              have e5299 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
              have b5300 := hb (x (-2) 3)
              have b5301 := hb (x (-1) 2)
              have b5302 := hb (x 0 13)
              have b5303 := hb (x 1 12)
              clear * - r5297 e5298 e5299 b5300 b5301 b5302 b5303 d5292 g22 f2679
              omega
            have d5304 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
              have r5305 := hand1 (x (-2) 3) (x (-2) 14)
              have b5306 := hb (x (-2) 3)
              have b5307 := hb (x (-2) 3 && x (-2) 14)
              clear * - r5305 b5306 b5307 d5296
              omega
            have d5308 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
              have r5309 := hand1 (x (-2) 3) (x (-2) 13)
              have b5310 := hb (x (-2) 3)
              have b5311 := hb (x (-2) 3 && x (-2) 13)
              clear * - r5309 b5310 b5311 d5296
              omega
            have d5312 : (x (-3) 4).toNat = 1 := by
              have r5313 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b5314 := hb (x (-3) 4)
              have b5315 := hb (x 1 11)
              have b5316 := hb (x 0 1 && x 0 12)
              have b5317 := hb (x (-1) 2 && x (-1) 13)
              have b5318 := hb (x (-2) 3 && x (-2) 14)
              clear * - r5313 b5314 b5315 b5316 b5317 b5318 d2706 g70 g71 d5304
              omega
            have d5319 : (x (-3) 12).toNat = 1 := by
              have r5320 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
              have b5321 := hb (x (-3) 4)
              have b5322 := hb (x (-3) 12)
              clear * - r5320 b5321 b5322 d5312
              omega
            have d5323 : (x (-4) 13).toNat = 0 := by
              have r5324 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e5325 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
              have e5326 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
              have b5327 := hb (x (-6) 3)
              have b5328 := hb (x (-5) 2)
              have b5329 := hb (x (-4) 13)
              have b5330 := hb (x (-3) 12)
              clear * - r5324 e5325 e5326 b5327 b5328 b5329 b5330 d5319
              omega
            have d5331 : (x (-4) 5).toNat = 0 := by
              have r5332 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
              have b5333 := hb (x (-4) 5)
              have b5334 := hb (x (-4) 13)
              clear * - r5332 b5333 b5334 d5323
              omega
            have d5335 : (x (-5) 2).toNat = 0 := by
              have r5336 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e5337 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
              have e5338 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
              have b5339 := hb (x (-6) 3)
              have b5340 := hb (x (-5) 2)
              have b5341 := hb (x (-4) 13)
              have b5342 := hb (x (-3) 12)
              clear * - r5336 e5337 e5338 b5339 b5340 b5341 b5342 d5319 d5323
              omega
            have d5343 : (x (-4) 1 && x (-4) 14).toNat = 1 := by
              have r5344 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b5345 := hb (x (-5) 2)
              have b5346 := hb (x (-3) 13)
              have b5347 := hb (x (-4) 1 && x (-4) 14)
              clear * - r5344 b5345 b5346 b5347 g4 d5335
              omega
            have d5348 : (x (-4) 1).toNat = 1 := by
              have r5349 := hand1 (x (-4) 1) (x (-4) 14)
              have b5350 := hb (x (-4) 1)
              have b5351 := hb (x (-4) 1 && x (-4) 14)
              clear * - r5349 b5350 b5351 d5343
              omega
            have d5352 : (x (-3) 14).toNat = 0 := by
              have r5353 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b5354 := hb (x (-4) 1)
              have b5355 := hb (x (-3) 14)
              clear * - r5353 b5354 b5355 d5348
              omega
            have d5356 : (x (-3) 4 && x (-3) 14).toNat = 0 := by
              have r5357 := hand2 (x (-3) 4) (x (-3) 14)
              have b5358 := hb (x (-3) 14)
              have b5359 := hb (x (-3) 4 && x (-3) 14)
              clear * - r5357 b5358 b5359 d5352
              omega
            have r5360 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b5361 := hb (x (-4) 5)
            have b5362 := hb (x 1 10)
            have b5363 := hb (x 0 1 && x 0 11)
            have b5364 := hb (x (-1) 2 && x (-1) 12)
            have b5365 := hb (x (-2) 3 && x (-2) 13)
            have b5366 := hb (x (-3) 4 && x (-3) 14)
            linarith only [r5360, b5361, b5362, b5363, b5364, b5365, b5366, g27, g58, d2680, d5308, d5356, d5331]
        · have f5367 : (x (-1) 4).toNat = 1 := by rw [h2710]; rfl
          have d5368 : (x (-1) 12).toNat = 1 := by
            have r5369 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
            have b5370 := hb (x (-1) 4)
            have b5371 := hb (x (-1) 12)
            clear * - r5369 b5370 b5371 f5367
            omega
          have d5372 : (x (-2) 13).toNat = 0 := by
            have r5373 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e5374 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e5375 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b5376 := hb (x (-4) 3)
            have b5377 := hb (x (-3) 2)
            have b5378 := hb (x (-2) 13)
            have b5379 := hb (x (-1) 12)
            clear * - r5373 e5374 e5375 b5376 b5377 b5378 b5379 d5368
            omega
          have d5380 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
            have r5381 := hand2 (x (-2) 2) (x (-2) 13)
            have b5382 := hb (x (-2) 13)
            have b5383 := hb (x (-2) 2 && x (-2) 13)
            clear * - r5381 b5382 b5383 d5372
            omega
          have d5384 : (x (-4) 2).toNat = 1 := by
            have r5385 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b5386 := hb (x (-4) 2)
            have b5387 := hb (x (-2) 13)
            have b5388 := hb (x (-3) 1 && x (-3) 14)
            clear * - r5385 b5386 b5387 b5388 d5372 g78
            omega
          have d5389 : (x (-4) 14).toNat = 1 := by
            have r5390 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
            have b5391 := hb (x (-4) 2)
            have b5392 := hb (x (-4) 14)
            clear * - r5390 b5391 b5392 d5384
            omega
          have d5393 : (x (-5) 1).toNat = 0 := by
            have r5394 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b5395 := hb (x (-5) 1)
            have b5396 := hb (x (-4) 14)
            clear * - r5394 b5395 b5396 d5389
            omega
          have d5397 : (x (-5) 1 && x (-5) 14).toNat = 0 := by
            have r5398 := hand1 (x (-5) 1) (x (-5) 14)
            have b5399 := hb (x (-5) 1)
            have b5400 := hb (x (-5) 1 && x (-5) 14)
            clear * - r5398 b5399 b5400 d5393
            omega
          have d5401 : (x (-5) 13).toNat = 0 := by
            have r5402 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
            have b5403 := hb (x (-5) 1)
            have b5404 := hb (x (-5) 13)
            clear * - r5402 b5403 b5404 d5393
            omega
          have d5405 : (x (-3) 2).toNat = 0 := by
            have r5406 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e5407 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e5408 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b5409 := hb (x (-4) 3)
            have b5410 := hb (x (-3) 2)
            have b5411 := hb (x (-2) 13)
            have b5412 := hb (x (-1) 12)
            clear * - r5406 e5407 e5408 b5409 b5410 b5411 b5412 d5368 d5372
            omega
          have d5413 : (x (-4) 3).toNat = 0 := by
            have r5414 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e5415 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e5416 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b5417 := hb (x (-4) 3)
            have b5418 := hb (x (-3) 2)
            have b5419 := hb (x (-2) 13)
            have b5420 := hb (x (-1) 12)
            clear * - r5414 e5415 e5416 b5417 b5418 b5419 b5420 d5368 d5372 d5405
            omega
          have d5421 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
            have r5422 := hand1 (x (-4) 3) (x (-4) 14)
            have b5423 := hb (x (-4) 3)
            have b5424 := hb (x (-4) 3 && x (-4) 14)
            clear * - r5422 b5423 b5424 d5413
            omega
          have d5425 : (x (-2) 12).toNat = 0 := by
            have r5426 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e5427 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
            have e5428 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
            have b5429 := hb (x (-5) 3)
            have b5430 := hb (x (-4) 2)
            have b5431 := hb (x (-3) 13)
            have b5432 := hb (x (-2) 12)
            clear * - r5426 e5427 e5428 b5429 b5430 b5431 b5432 g4 d5384
            omega
          have d5433 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
            have r5434 := hand2 (x (-2) 1) (x (-2) 12)
            have b5435 := hb (x (-2) 12)
            have b5436 := hb (x (-2) 1 && x (-2) 12)
            clear * - r5434 b5435 b5436 d5425
            omega
          have d5437 : (x (-5) 3).toNat = 0 := by
            have r5438 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e5439 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
            have e5440 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
            have b5441 := hb (x (-5) 3)
            have b5442 := hb (x (-4) 2)
            have b5443 := hb (x (-3) 13)
            have b5444 := hb (x (-2) 12)
            clear * - r5438 e5439 e5440 b5441 b5442 b5443 b5444 d5425 g4 d5384
            omega
          have d5445 : (x (-5) 11).toNat = 0 := by
            have r5446 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
            have b5447 := hb (x (-5) 3)
            have b5448 := hb (x (-5) 11)
            clear * - r5446 b5447 b5448 d5437
            omega
          have d5449 : (x (-4) 4).toNat = 1 := by
            have r5450 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b5451 := hb (x (-4) 4)
            have b5452 := hb (x 0 11)
            have b5453 := hb (x (-1) 1 && x (-1) 12)
            have b5454 := hb (x (-2) 2 && x (-2) 13)
            have b5455 := hb (x (-3) 3 && x (-3) 14)
            clear * - r5450 b5451 b5452 b5453 b5454 b5455 g21 g68 d5380 g69
            omega
          have d5456 : (x (-4) 12).toNat = 1 := by
            have r5457 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
            have b5458 := hb (x (-4) 4)
            have b5459 := hb (x (-4) 12)
            clear * - r5457 b5458 b5459 d5449
            omega
          have d5460 : (x (-6) 2).toNat = 0 := by
            have r5461 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e5462 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
            have e5463 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
            have b5464 := hb (x (-7) 3)
            have b5465 := hb (x (-6) 2)
            have b5466 := hb (x (-5) 13)
            have b5467 := hb (x (-4) 12)
            clear * - r5461 e5462 e5463 b5464 b5465 b5466 b5467 d5456 d5401
            omega
          have d5468 : (x (-4) 13).toNat = 1 := by
            have r5469 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b5470 := hb (x (-6) 2)
            have b5471 := hb (x (-4) 13)
            have b5472 := hb (x (-5) 1 && x (-5) 14)
            clear * - r5469 b5470 b5471 b5472 d5397 d5460
            omega
          have d5473 : (x (-3) 12).toNat = 0 := by
            have r5474 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e5475 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
            have e5476 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
            have b5477 := hb (x (-6) 3)
            have b5478 := hb (x (-5) 2)
            have b5479 := hb (x (-4) 13)
            have b5480 := hb (x (-3) 12)
            clear * - r5474 e5475 e5476 b5477 b5478 b5479 b5480 d5468
            omega
          have d5481 : (x (-5) 2).toNat = 0 := by
            have r5482 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e5483 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
            have e5484 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
            have b5485 := hb (x (-6) 3)
            have b5486 := hb (x (-5) 2)
            have b5487 := hb (x (-4) 13)
            have b5488 := hb (x (-3) 12)
            clear * - r5482 e5483 e5484 b5485 b5486 b5487 b5488 d5473 d5468
            omega
          have d5489 : (x (-5) 10).toNat = 0 := by
            have r5490 : (x (-5) 10).toNat ≤ (x (-5) 2).toNat := himp _ _ (hp10 (-5))
            have b5491 := hb (x (-5) 2)
            have b5492 := hb (x (-5) 10)
            clear * - r5490 b5491 b5492 d5481
            omega
          have d5493 : (x (-6) 3).toNat = 0 := by
            have r5494 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e5495 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
            have e5496 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
            have b5497 := hb (x (-6) 3)
            have b5498 := hb (x (-5) 2)
            have b5499 := hb (x (-4) 13)
            have b5500 := hb (x (-3) 12)
            clear * - r5494 e5495 e5496 b5497 b5498 b5499 b5500 d5473 d5468 d5481
            omega
          have d5501 : (x (-6) 11).toNat = 0 := by
            have r5502 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
            have b5503 := hb (x (-6) 3)
            have b5504 := hb (x (-6) 11)
            clear * - r5502 b5503 b5504 d5493
            omega
          have d5505 : (x (-6) 1 && x (-6) 11).toNat = 0 := by
            have r5506 := hand2 (x (-6) 1) (x (-6) 11)
            have b5507 := hb (x (-6) 11)
            have b5508 := hb (x (-6) 1 && x (-6) 11)
            clear * - r5506 b5507 b5508 d5501
            omega
          have d5509 : (x (-5) 4).toNat = 1 := by
            have r5510 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b5511 := hb (x (-5) 4)
            have b5512 := hb (x (-1) 11)
            have b5513 := hb (x (-2) 1 && x (-2) 12)
            have b5514 := hb (x (-3) 2 && x (-3) 13)
            have b5515 := hb (x (-4) 3 && x (-4) 14)
            clear * - r5510 b5511 b5512 b5513 b5514 b5515 g10 d5433 g67 d5421
            omega
          have d5516 : (x (-5) 12).toNat = 1 := by
            have r5517 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
            have b5518 := hb (x (-5) 4)
            have b5519 := hb (x (-5) 12)
            clear * - r5517 b5518 b5519 d5509
            omega
          have d5520 : (x (-6) 13).toNat = 0 := by
            have r5521 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e5522 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
            have e5523 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
            have b5524 := hb (x (-8) 3)
            have b5525 := hb (x (-7) 2)
            have b5526 := hb (x (-6) 13)
            have b5527 := hb (x (-5) 12)
            clear * - r5521 e5522 e5523 b5524 b5525 b5526 b5527 d5516
            omega
          have d5528 : (x (-7) 2).toNat = 0 := by
            have r5529 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e5530 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
            have e5531 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
            have b5532 := hb (x (-8) 3)
            have b5533 := hb (x (-7) 2)
            have b5534 := hb (x (-6) 13)
            have b5535 := hb (x (-5) 12)
            clear * - r5529 e5530 e5531 b5532 b5533 b5534 b5535 d5516 d5520
            omega
          have d5536 : (x (-7) 2 && x (-7) 13).toNat = 0 := by
            have r5537 := hand1 (x (-7) 2) (x (-7) 13)
            have b5538 := hb (x (-7) 2)
            have b5539 := hb (x (-7) 2 && x (-7) 13)
            clear * - r5537 b5538 b5539 d5528
            omega
          have d5540 : (x (-7) 2 && x (-7) 12).toNat = 0 := by
            have r5541 := hand1 (x (-7) 2) (x (-7) 12)
            have b5542 := hb (x (-7) 2)
            have b5543 := hb (x (-7) 2 && x (-7) 12)
            clear * - r5541 b5542 b5543 d5528
            omega
          have d5544 : (x (-6) 1 && x (-6) 14).toNat = 1 := by
            have r5545 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b5546 := hb (x (-7) 2)
            have b5547 := hb (x (-5) 13)
            have b5548 := hb (x (-6) 1 && x (-6) 14)
            clear * - r5545 b5546 b5547 b5548 d5401 d5528
            omega
          have d5549 : (x (-6) 14).toNat = 1 := by
            have r5550 := hand2 (x (-6) 1) (x (-6) 14)
            have b5551 := hb (x (-6) 14)
            have b5552 := hb (x (-6) 1 && x (-6) 14)
            clear * - r5550 b5551 b5552 d5544
            omega
          have d5553 : (x (-7) 1).toNat = 0 := by
            have r5554 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b5555 := hb (x (-7) 1)
            have b5556 := hb (x (-6) 14)
            clear * - r5554 b5555 b5556 d5549
            omega
          have d5557 : (x (-7) 1 && x (-7) 14).toNat = 0 := by
            have r5558 := hand1 (x (-7) 1) (x (-7) 14)
            have b5559 := hb (x (-7) 1)
            have b5560 := hb (x (-7) 1 && x (-7) 14)
            clear * - r5558 b5559 b5560 d5553
            omega
          have d5561 : (x (-8) 2).toNat = 1 := by
            have r5562 : 1 ≤ (x (-6) 13).toNat + (x (-7) 1 && x (-7) 14).toNat + (x (-8) 2).toNat := by have q := hcov13 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b5563 := hb (x (-8) 2)
            have b5564 := hb (x (-6) 13)
            have b5565 := hb (x (-7) 1 && x (-7) 14)
            clear * - r5562 b5563 b5564 b5565 d5520 d5557
            omega
          have d5566 : (x (-8) 14).toNat = 1 := by
            have r5567 : (x (-8) 2).toNat ≤ (x (-8) 14).toNat := himp _ _ (hp2 (-8))
            have b5568 := hb (x (-8) 2)
            have b5569 := hb (x (-8) 14)
            clear * - r5567 b5568 b5569 d5561
            omega
          have d5570 : (x (-9) 1).toNat = 0 := by
            have r5571 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b5572 := hb (x (-9) 1)
            have b5573 := hb (x (-8) 14)
            clear * - r5571 b5572 b5573 d5566
            omega
          have d5574 : (x (-9) 13).toNat = 0 := by
            have r5575 : (x (-9) 13).toNat ≤ (x (-9) 1).toNat := himp _ _ (hp13 (-9))
            have b5576 := hb (x (-9) 1)
            have b5577 := hb (x (-9) 13)
            clear * - r5575 b5576 b5577 d5570
            omega
          have d5578 : (x (-6) 12).toNat = 0 := by
            have r5579 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e5580 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
            have e5581 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
            have b5582 := hb (x (-9) 3)
            have b5583 := hb (x (-8) 2)
            have b5584 := hb (x (-7) 13)
            have b5585 := hb (x (-6) 12)
            clear * - r5579 e5580 e5581 b5582 b5583 b5584 b5585 d5561
            omega
          have d5586 : (x (-6) 1 && x (-6) 12).toNat = 0 := by
            have r5587 := hand2 (x (-6) 1) (x (-6) 12)
            have b5588 := hb (x (-6) 12)
            have b5589 := hb (x (-6) 1 && x (-6) 12)
            clear * - r5587 b5588 b5589 d5578
            omega
          have d5590 : (x (-8) 3).toNat = 0 := by
            have r5591 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e5592 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
            have e5593 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
            have b5594 := hb (x (-8) 3)
            have b5595 := hb (x (-7) 2)
            have b5596 := hb (x (-6) 13)
            have b5597 := hb (x (-5) 12)
            clear * - r5591 e5592 e5593 b5594 b5595 b5596 b5597 d5516 d5520 d5528
            omega
          have d5598 : (x (-8) 3 && x (-8) 14).toNat = 0 := by
            have r5599 := hand1 (x (-8) 3) (x (-8) 14)
            have b5600 := hb (x (-8) 3)
            have b5601 := hb (x (-8) 3 && x (-8) 14)
            clear * - r5599 b5600 b5601 d5590
            omega
          have d5602 : (x (-8) 3 && x (-8) 13).toNat = 0 := by
            have r5603 := hand1 (x (-8) 3) (x (-8) 13)
            have b5604 := hb (x (-8) 3)
            have b5605 := hb (x (-8) 3 && x (-8) 13)
            clear * - r5603 b5604 b5605 d5590
            omega
          have d5606 : (x (-9) 4).toNat = 1 := by
            have r5607 : 1 ≤ (x (-5) 11).toNat + (x (-6) 1 && x (-6) 12).toNat + (x (-7) 2 && x (-7) 13).toNat + (x (-8) 3 && x (-8) 14).toNat + (x (-9) 4).toNat := by have q := hcov11 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b5608 := hb (x (-9) 4)
            have b5609 := hb (x (-5) 11)
            have b5610 := hb (x (-6) 1 && x (-6) 12)
            have b5611 := hb (x (-7) 2 && x (-7) 13)
            have b5612 := hb (x (-8) 3 && x (-8) 14)
            clear * - r5607 b5608 b5609 b5610 b5611 b5612 d5445 d5586 d5536 d5598
            omega
          have d5613 : (x (-9) 12).toNat = 1 := by
            have r5614 : (x (-9) 4).toNat ≤ (x (-9) 12).toNat := himp _ _ (hp4 (-9))
            have b5615 := hb (x (-9) 4)
            have b5616 := hb (x (-9) 12)
            clear * - r5614 b5615 b5616 d5606
            omega
          have d5617 : (x (-10) 13).toNat = 0 := by
            have r5618 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e5619 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
            have e5620 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
            have b5621 := hb (x (-12) 3)
            have b5622 := hb (x (-11) 2)
            have b5623 := hb (x (-10) 13)
            have b5624 := hb (x (-9) 12)
            clear * - r5618 e5619 e5620 b5621 b5622 b5623 b5624 d5613
            omega
          have d5625 : (x (-10) 5).toNat = 0 := by
            have r5626 : (x (-10) 5).toNat ≤ (x (-10) 13).toNat := himp _ _ (hp5 (-10))
            have b5627 := hb (x (-10) 5)
            have b5628 := hb (x (-10) 13)
            clear * - r5626 b5627 b5628 d5617
            omega
          have d5629 : (x (-11) 2).toNat = 0 := by
            have r5630 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e5631 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
            have e5632 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
            have b5633 := hb (x (-12) 3)
            have b5634 := hb (x (-11) 2)
            have b5635 := hb (x (-10) 13)
            have b5636 := hb (x (-9) 12)
            clear * - r5630 e5631 e5632 b5633 b5634 b5635 b5636 d5613 d5617
            omega
          have d5637 : (x (-10) 1 && x (-10) 14).toNat = 1 := by
            have r5638 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b5639 := hb (x (-11) 2)
            have b5640 := hb (x (-9) 13)
            have b5641 := hb (x (-10) 1 && x (-10) 14)
            clear * - r5638 b5639 b5640 b5641 d5574 d5629
            omega
          have d5642 : (x (-10) 1).toNat = 1 := by
            have r5643 := hand1 (x (-10) 1) (x (-10) 14)
            have b5644 := hb (x (-10) 1)
            have b5645 := hb (x (-10) 1 && x (-10) 14)
            clear * - r5643 b5644 b5645 d5637
            omega
          have d5646 : (x (-9) 14).toNat = 0 := by
            have r5647 : (x (-9) 14).toNat + (x (-10) 1).toNat = 1 := by have q := hd14 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b5648 := hb (x (-10) 1)
            have b5649 := hb (x (-9) 14)
            clear * - r5647 b5648 b5649 d5642
            omega
          have d5650 : (x (-9) 4 && x (-9) 14).toNat = 0 := by
            have r5651 := hand2 (x (-9) 4) (x (-9) 14)
            have b5652 := hb (x (-9) 14)
            have b5653 := hb (x (-9) 4 && x (-9) 14)
            clear * - r5651 b5652 b5653 d5646
            omega
          have r5654 : 1 ≤ (x (-5) 10).toNat + (x (-6) 1 && x (-6) 11).toNat + (x (-7) 2 && x (-7) 12).toNat + (x (-8) 3 && x (-8) 13).toNat + (x (-9) 4 && x (-9) 14).toNat + (x (-10) 5).toNat := by have q := hcov10 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b5655 := hb (x (-10) 5)
          have b5656 := hb (x (-5) 10)
          have b5657 := hb (x (-6) 1 && x (-6) 11)
          have b5658 := hb (x (-7) 2 && x (-7) 12)
          have b5659 := hb (x (-8) 3 && x (-8) 13)
          have b5660 := hb (x (-9) 4 && x (-9) 14)
          linarith only [r5654, b5655, b5656, b5657, b5658, b5659, b5660, d5489, d5505, d5540, d5602, d5650, d5625]
      · have f5661 : (x 1 3).toNat = 1 := by rw [h2700]; rfl
        have d5662 : (x 4 12).toNat = 0 := by
          have r5663 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5664 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e5665 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b5666 := hb (x 1 3)
          have b5667 := hb (x 2 2)
          have b5668 := hb (x 3 13)
          have b5669 := hb (x 4 12)
          clear * - r5663 e5664 e5665 b5666 b5667 b5668 b5669 f5661
          omega
        have d5670 : (x 3 13).toNat = 0 := by
          have r5671 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5672 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e5673 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b5674 := hb (x 1 3)
          have b5675 := hb (x 2 2)
          have b5676 := hb (x 3 13)
          have b5677 := hb (x 4 12)
          clear * - r5671 e5672 e5673 b5674 b5675 b5676 b5677 d5662 f5661
          omega
        have d5678 : (x 2 1 && x 2 14).toNat = 1 := by
          have r5679 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b5680 := hb (x 1 2)
          have b5681 := hb (x 3 13)
          have b5682 := hb (x 2 1 && x 2 14)
          clear * - r5679 b5680 b5681 b5682 d5670 g24
          omega
        have d5683 : (x 2 1).toNat = 1 := by
          have r5684 := hand1 (x 2 1) (x 2 14)
          have b5685 := hb (x 2 1)
          have b5686 := hb (x 2 1 && x 2 14)
          clear * - r5684 b5685 b5686 d5678
          omega
        have d5687 : (x 3 14).toNat = 0 := by
          have r5688 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b5689 := hb (x 2 1)
          have b5690 := hb (x 3 14)
          clear * - r5688 b5689 b5690 d5683
          omega
        have d5691 : (x 3 1 && x 3 14).toNat = 0 := by
          have r5692 := hand2 (x 3 1) (x 3 14)
          have b5693 := hb (x 3 14)
          have b5694 := hb (x 3 1 && x 3 14)
          clear * - r5692 b5693 b5694 d5687
          omega
        have d5695 : (x 3 2).toNat = 0 := by
          have r5696 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
          have b5697 := hb (x 3 2)
          have b5698 := hb (x 3 14)
          clear * - r5696 b5697 b5698 d5687
          omega
        have d5699 : (x 2 2).toNat = 0 := by
          have r5700 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5701 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e5702 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b5703 := hb (x 1 3)
          have b5704 := hb (x 2 2)
          have b5705 := hb (x 3 13)
          have b5706 := hb (x 4 12)
          clear * - r5700 e5701 e5702 b5703 b5704 b5705 b5706 d5662 d5670 f5661
          omega
        have d5707 : (x 2 2 && x 2 13).toNat = 0 := by
          have r5708 := hand1 (x 2 2) (x 2 13)
          have b5709 := hb (x 2 2)
          have b5710 := hb (x 2 2 && x 2 13)
          clear * - r5708 b5709 b5710 d5699
          omega
        have d5711 : (x 4 13).toNat = 1 := by
          have r5712 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b5713 := hb (x 2 2)
          have b5714 := hb (x 4 13)
          have b5715 := hb (x 3 1 && x 3 14)
          clear * - r5712 b5713 b5714 b5715 d5691 d5699
          omega
        have d5716 : (x 4 1).toNat = 1 := by
          have r5717 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
          have b5718 := hb (x 4 1)
          have b5719 := hb (x 4 13)
          clear * - r5717 b5718 b5719 d5711
          omega
        have d5720 : (x 5 14).toNat = 0 := by
          have r5721 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b5722 := hb (x 4 1)
          have b5723 := hb (x 5 14)
          clear * - r5721 b5722 b5723 d5716
          omega
        have d5724 : (x 5 1 && x 5 14).toNat = 0 := by
          have r5725 := hand2 (x 5 1) (x 5 14)
          have b5726 := hb (x 5 14)
          have b5727 := hb (x 5 1 && x 5 14)
          clear * - r5725 b5726 b5727 d5720
          omega
        have d5728 : (x 5 2).toNat = 0 := by
          have r5729 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
          have b5730 := hb (x 5 2)
          have b5731 := hb (x 5 14)
          clear * - r5729 b5730 b5731 d5720
          omega
        have d5732 : (x 5 12).toNat = 0 := by
          have r5733 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5734 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e5735 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b5736 := hb (x 2 3)
          have b5737 := hb (x 3 2)
          have b5738 := hb (x 4 13)
          have b5739 := hb (x 5 12)
          clear * - r5733 e5734 e5735 b5736 b5737 b5738 b5739 d5711 d5695
          omega
        have d5740 : (x 2 3).toNat = 0 := by
          have r5741 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5742 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e5743 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b5744 := hb (x 2 3)
          have b5745 := hb (x 3 2)
          have b5746 := hb (x 4 13)
          have b5747 := hb (x 5 12)
          clear * - r5741 e5742 e5743 b5744 b5745 b5746 b5747 d5732 d5711 d5695
          omega
        have d5748 : (x 2 11).toNat = 0 := by
          have r5749 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
          have b5750 := hb (x 2 3)
          have b5751 := hb (x 2 11)
          clear * - r5749 b5750 b5751 d5740
          omega
        have d5752 : (x (-2) 4).toNat = 1 := by
          have r5753 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := by have q := hcov11 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b5754 := hb (x (-2) 4)
          have b5755 := hb (x 2 11)
          have b5756 := hb (x 1 1 && x 1 12)
          have b5757 := hb (x 0 2 && x 0 13)
          have b5758 := hb (x (-1) 3 && x (-1) 14)
          clear * - r5753 b5754 b5755 b5756 b5757 b5758 d5748 d2658 g72 g73
          omega
        have d5759 : (x (-2) 12).toNat = 1 := by
          have r5760 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
          have b5761 := hb (x (-2) 4)
          have b5762 := hb (x (-2) 12)
          clear * - r5760 b5761 b5762 d5752
          omega
        have d5763 : (x (-4) 2).toNat = 0 := by
          have r5764 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5765 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
          have e5766 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
          have b5767 := hb (x (-5) 3)
          have b5768 := hb (x (-4) 2)
          have b5769 := hb (x (-3) 13)
          have b5770 := hb (x (-2) 12)
          clear * - r5764 e5765 e5766 b5767 b5768 b5769 b5770 d5759 g4
          omega
        have d5771 : (x (-2) 13).toNat = 1 := by
          have r5772 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b5773 := hb (x (-4) 2)
          have b5774 := hb (x (-2) 13)
          have b5775 := hb (x (-3) 1 && x (-3) 14)
          clear * - r5772 b5773 b5774 b5775 g78 d5763
          omega
        have d5776 : (x (-1) 12).toNat = 0 := by
          have r5777 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5778 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e5779 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b5780 := hb (x (-4) 3)
          have b5781 := hb (x (-3) 2)
          have b5782 := hb (x (-2) 13)
          have b5783 := hb (x (-1) 12)
          clear * - r5777 e5778 e5779 b5780 b5781 b5782 b5783 d5771
          omega
        have d5784 : (x (-1) 4).toNat = 0 := by
          have r5785 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
          have b5786 := hb (x (-1) 4)
          have b5787 := hb (x (-1) 12)
          clear * - r5785 b5786 b5787 d5776
          omega
        have d5788 : (x 3 11).toNat = 1 := by
          have r5789 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b5790 := hb (x (-1) 4)
          have b5791 := hb (x 3 11)
          have b5792 := hb (x 2 1 && x 2 12)
          have b5793 := hb (x 1 2 && x 1 13)
          have b5794 := hb (x 0 3 && x 0 14)
          clear * - r5789 b5790 b5791 b5792 b5793 b5794 g74 g75 g76 d5784
          omega
        have d5795 : (x 3 3).toNat = 1 := by
          have r5796 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
          have b5797 := hb (x 3 3)
          have b5798 := hb (x 3 11)
          clear * - r5796 b5797 b5798 d5788
          omega
        have d5799 : (x 6 12).toNat = 0 := by
          have r5800 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5801 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e5802 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b5803 := hb (x 3 3)
          have b5804 := hb (x 4 2)
          have b5805 := hb (x 5 13)
          have b5806 := hb (x 6 12)
          clear * - r5800 e5801 e5802 b5803 b5804 b5805 b5806 d5795
          omega
        have d5807 : (x 5 13).toNat = 0 := by
          have r5808 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5809 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e5810 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b5811 := hb (x 3 3)
          have b5812 := hb (x 4 2)
          have b5813 := hb (x 5 13)
          have b5814 := hb (x 6 12)
          clear * - r5808 e5809 e5810 b5811 b5812 b5813 b5814 d5799 d5795
          omega
        have d5815 : (x 4 1 && x 4 14).toNat = 1 := by
          have r5816 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b5817 := hb (x 3 2)
          have b5818 := hb (x 5 13)
          have b5819 := hb (x 4 1 && x 4 14)
          clear * - r5816 b5817 b5818 b5819 d5807 d5695
          omega
        have d5820 : (x 4 14).toNat = 1 := by
          have r5821 := hand2 (x 4 1) (x 4 14)
          have b5822 := hb (x 4 14)
          have b5823 := hb (x 4 1 && x 4 14)
          clear * - r5821 b5822 b5823 d5815
          omega
        have d5824 : (x 3 1).toNat = 0 := by
          have r5825 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b5826 := hb (x 3 1)
          have b5827 := hb (x 4 14)
          clear * - r5825 b5826 b5827 d5820
          omega
        have d5828 : (x 3 1 && x 3 12).toNat = 0 := by
          have r5829 := hand1 (x 3 1) (x 3 12)
          have b5830 := hb (x 3 1)
          have b5831 := hb (x 3 1 && x 3 12)
          clear * - r5829 b5830 b5831 d5824
          omega
        have d5832 : (x 4 11).toNat = 1 := by
          have r5833 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b5834 := hb (x 0 4)
          have b5835 := hb (x 4 11)
          have b5836 := hb (x 3 1 && x 3 12)
          have b5837 := hb (x 2 2 && x 2 13)
          have b5838 := hb (x 1 3 && x 1 14)
          clear * - r5833 b5834 b5835 b5836 b5837 b5838 d5828 d5707 g77 g14
          omega
        have d5839 : (x 4 3).toNat = 1 := by
          have r5840 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
          have b5841 := hb (x 4 3)
          have b5842 := hb (x 4 11)
          clear * - r5840 b5841 b5842 d5832
          omega
        have d5843 : (x 7 12).toNat = 0 := by
          have r5844 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5845 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
          have e5846 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
          have b5847 := hb (x 4 3)
          have b5848 := hb (x 5 2)
          have b5849 := hb (x 6 13)
          have b5850 := hb (x 7 12)
          clear * - r5844 e5845 e5846 b5847 b5848 b5849 b5850 d5728 d5839
          omega
        have d5851 : (x 6 13).toNat = 0 := by
          have r5852 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5853 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
          have e5854 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
          have b5855 := hb (x 4 3)
          have b5856 := hb (x 5 2)
          have b5857 := hb (x 6 13)
          have b5858 := hb (x 7 12)
          clear * - r5852 e5853 e5854 b5855 b5856 b5857 b5858 d5843 d5728 d5839
          omega
        have d5859 : (x 4 2).toNat = 1 := by
          have r5860 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b5861 := hb (x 4 2)
          have b5862 := hb (x 6 13)
          have b5863 := hb (x 5 1 && x 5 14)
          clear * - r5860 b5861 b5862 b5863 d5851 d5724
          omega
        have r5864 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5865 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
        have e5866 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
        have b5867 := hb (x 3 3)
        have b5868 := hb (x 4 2)
        have b5869 := hb (x 5 13)
        have b5870 := hb (x 6 12)
        linarith only [r5864, e5865, e5866, b5867, b5868, b5869, b5870, d5799, d5807, d5859, d5795]
    · have f5871 : (x (-1) 2).toNat = 1 := by rw [h2678]; rfl
      have d5872 : (x (-1) 14).toNat = 1 := by
        have r5873 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
        have b5874 := hb (x (-1) 2)
        have b5875 := hb (x (-1) 14)
        clear * - r5873 b5874 b5875 f5871
        omega
      have d5876 : (x (-2) 1).toNat = 0 := by
        have r5877 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b5878 := hb (x (-2) 1)
        have b5879 := hb (x (-1) 14)
        clear * - r5877 b5878 b5879 d5872
        omega
      have d5880 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
        have r5881 := hand1 (x (-2) 1) (x (-2) 14)
        have b5882 := hb (x (-2) 1)
        have b5883 := hb (x (-2) 1 && x (-2) 14)
        clear * - r5881 b5882 b5883 d5876
        omega
      have d5884 : (x (-2) 13).toNat = 0 := by
        have r5885 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
        have b5886 := hb (x (-2) 1)
        have b5887 := hb (x (-2) 13)
        clear * - r5885 b5886 b5887 d5876
        omega
      have d5888 : (x (-3) 2).toNat = 1 := by
        have r5889 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b5890 := hb (x (-3) 2)
        have b5891 := hb (x (-1) 13)
        have b5892 := hb (x (-2) 1 && x (-2) 14)
        clear * - r5889 b5890 b5891 b5892 g11 d5880
        omega
      have d5893 : (x (-3) 14).toNat = 1 := by
        have r5894 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
        have b5895 := hb (x (-3) 2)
        have b5896 := hb (x (-3) 14)
        clear * - r5894 b5895 b5896 d5888
        omega
      have d5897 : (x (-4) 1).toNat = 0 := by
        have r5898 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b5899 := hb (x (-4) 1)
        have b5900 := hb (x (-3) 14)
        clear * - r5898 b5899 b5900 d5893
        omega
      have d5901 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
        have r5902 := hand1 (x (-4) 1) (x (-4) 14)
        have b5903 := hb (x (-4) 1)
        have b5904 := hb (x (-4) 1 && x (-4) 14)
        clear * - r5902 b5903 b5904 d5897
        omega
      have d5905 : (x (-4) 13).toNat = 0 := by
        have r5906 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
        have b5907 := hb (x (-4) 1)
        have b5908 := hb (x (-4) 13)
        clear * - r5906 b5907 b5908 d5897
        omega
      have d5909 : (x (-4) 2).toNat = 1 := by
        have r5910 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b5911 := hb (x (-4) 2)
        have b5912 := hb (x (-2) 13)
        have b5913 := hb (x (-3) 1 && x (-3) 14)
        clear * - r5910 b5911 b5912 b5913 d5884 g78
        omega
      have d5914 : (x (-5) 2).toNat = 1 := by
        have r5915 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b5916 := hb (x (-5) 2)
        have b5917 := hb (x (-3) 13)
        have b5918 := hb (x (-4) 1 && x (-4) 14)
        clear * - r5915 b5916 b5917 b5918 g4 d5901
        omega
      have d5919 : (x 1 12).toNat = 0 := by
        have r5920 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5921 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e5922 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b5923 := hb (x (-2) 3)
        have b5924 := hb (x (-1) 2)
        have b5925 := hb (x 0 13)
        have b5926 := hb (x 1 12)
        clear * - r5920 e5921 e5922 b5923 b5924 b5925 b5926 g22 f5871
        omega
      have d5927 : (x (-2) 3).toNat = 0 := by
        have r5928 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5929 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e5930 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b5931 := hb (x (-2) 3)
        have b5932 := hb (x (-1) 2)
        have b5933 := hb (x 0 13)
        have b5934 := hb (x 1 12)
        clear * - r5928 e5929 e5930 b5931 b5932 b5933 b5934 d5919 g22 f5871
        omega
      have d5935 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
        have r5936 := hand1 (x (-2) 3) (x (-2) 14)
        have b5937 := hb (x (-2) 3)
        have b5938 := hb (x (-2) 3 && x (-2) 14)
        clear * - r5936 b5937 b5938 d5927
        omega
      have d5939 : (x (-1) 12).toNat = 0 := by
        have r5940 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5941 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e5942 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b5943 := hb (x (-4) 3)
        have b5944 := hb (x (-3) 2)
        have b5945 := hb (x (-2) 13)
        have b5946 := hb (x (-1) 12)
        clear * - r5940 e5941 e5942 b5943 b5944 b5945 b5946 d5884 d5888
        omega
      have d5947 : (x (-1) 4).toNat = 0 := by
        have r5948 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
        have b5949 := hb (x (-1) 4)
        have b5950 := hb (x (-1) 12)
        clear * - r5948 b5949 b5950 d5939
        omega
      have d5951 : (x (-2) 12).toNat = 0 := by
        have r5952 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5953 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e5954 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have b5955 := hb (x (-5) 3)
        have b5956 := hb (x (-4) 2)
        have b5957 := hb (x (-3) 13)
        have b5958 := hb (x (-2) 12)
        clear * - r5952 e5953 e5954 b5955 b5956 b5957 b5958 g4 d5909
        omega
      have d5959 : (x (-2) 4).toNat = 0 := by
        have r5960 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
        have b5961 := hb (x (-2) 4)
        have b5962 := hb (x (-2) 12)
        clear * - r5960 b5961 b5962 d5951
        omega
      have d5963 : (x (-3) 12).toNat = 0 := by
        have r5964 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5965 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
        have e5966 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
        have b5967 := hb (x (-6) 3)
        have b5968 := hb (x (-5) 2)
        have b5969 := hb (x (-4) 13)
        have b5970 := hb (x (-3) 12)
        clear * - r5964 e5965 e5966 b5967 b5968 b5969 b5970 d5905 d5914
        omega
      have d5971 : (x (-3) 4).toNat = 0 := by
        have r5972 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
        have b5973 := hb (x (-3) 4)
        have b5974 := hb (x (-3) 12)
        clear * - r5972 b5973 b5974 d5963
        omega
      have d5975 : (x 3 11).toNat = 1 := by
        have r5976 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b5977 := hb (x (-1) 4)
        have b5978 := hb (x 3 11)
        have b5979 := hb (x 2 1 && x 2 12)
        have b5980 := hb (x 1 2 && x 1 13)
        have b5981 := hb (x 0 3 && x 0 14)
        clear * - r5976 b5977 b5978 b5979 b5980 b5981 g74 g75 g76 d5947
        omega
      have d5982 : (x 3 3).toNat = 1 := by
        have r5983 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
        have b5984 := hb (x 3 3)
        have b5985 := hb (x 3 11)
        clear * - r5983 b5984 b5985 d5975
        omega
      have d5986 : (x 6 12).toNat = 0 := by
        have r5987 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5988 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
        have e5989 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
        have b5990 := hb (x 3 3)
        have b5991 := hb (x 4 2)
        have b5992 := hb (x 5 13)
        have b5993 := hb (x 6 12)
        clear * - r5987 e5988 e5989 b5990 b5991 b5992 b5993 d5982
        omega
      have d5994 : (x 5 13).toNat = 0 := by
        have r5995 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5996 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
        have e5997 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
        have b5998 := hb (x 3 3)
        have b5999 := hb (x 4 2)
        have b6000 := hb (x 5 13)
        have b6001 := hb (x 6 12)
        clear * - r5995 e5996 e5997 b5998 b5999 b6000 b6001 d5986 d5982
        omega
      have d6002 : (x 2 11).toNat = 1 := by
        have r6003 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := by have q := hcov11 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b6004 := hb (x (-2) 4)
        have b6005 := hb (x 2 11)
        have b6006 := hb (x 1 1 && x 1 12)
        have b6007 := hb (x 0 2 && x 0 13)
        have b6008 := hb (x (-1) 3 && x (-1) 14)
        clear * - r6003 b6004 b6005 b6006 b6007 b6008 d2658 g72 g73 d5959
        omega
      have d6009 : (x 2 3).toNat = 1 := by
        have r6010 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
        have b6011 := hb (x 2 3)
        have b6012 := hb (x 2 11)
        clear * - r6010 b6011 b6012 d6002
        omega
      have d6013 : (x 5 12).toNat = 0 := by
        have r6014 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6015 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e6016 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b6017 := hb (x 2 3)
        have b6018 := hb (x 3 2)
        have b6019 := hb (x 4 13)
        have b6020 := hb (x 5 12)
        clear * - r6014 e6015 e6016 b6017 b6018 b6019 b6020 d6009
        omega
      have d6021 : (x 4 13).toNat = 0 := by
        have r6022 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6023 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e6024 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b6025 := hb (x 2 3)
        have b6026 := hb (x 3 2)
        have b6027 := hb (x 4 13)
        have b6028 := hb (x 5 12)
        clear * - r6022 e6023 e6024 b6025 b6026 b6027 b6028 d6013 d6009
        omega
      have d6029 : (x 3 2).toNat = 0 := by
        have r6030 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6031 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e6032 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b6033 := hb (x 2 3)
        have b6034 := hb (x 3 2)
        have b6035 := hb (x 4 13)
        have b6036 := hb (x 5 12)
        clear * - r6030 e6031 e6032 b6033 b6034 b6035 b6036 d6013 d6021 d6009
        omega
      have d6037 : (x 4 1 && x 4 14).toNat = 1 := by
        have r6038 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b6039 := hb (x 3 2)
        have b6040 := hb (x 5 13)
        have b6041 := hb (x 4 1 && x 4 14)
        clear * - r6038 b6039 b6040 b6041 d5994 d6029
        omega
      have d6042 : (x 4 14).toNat = 1 := by
        have r6043 := hand2 (x 4 1) (x 4 14)
        have b6044 := hb (x 4 14)
        have b6045 := hb (x 4 1 && x 4 14)
        clear * - r6043 b6044 b6045 d6037
        omega
      have d6046 : (x 3 1).toNat = 0 := by
        have r6047 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b6048 := hb (x 3 1)
        have b6049 := hb (x 4 14)
        clear * - r6047 b6048 b6049 d6042
        omega
      have d6050 : (x 3 1 && x 3 14).toNat = 0 := by
        have r6051 := hand1 (x 3 1) (x 3 14)
        have b6052 := hb (x 3 1)
        have b6053 := hb (x 3 1 && x 3 14)
        clear * - r6051 b6052 b6053 d6046
        omega
      have d6054 : (x 2 2).toNat = 1 := by
        have r6055 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b6056 := hb (x 2 2)
        have b6057 := hb (x 4 13)
        have b6058 := hb (x 3 1 && x 3 14)
        clear * - r6055 b6056 b6057 b6058 d6021 d6050
        omega
      have d6059 : (x 4 12).toNat = 0 := by
        have r6060 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6061 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e6062 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b6063 := hb (x 1 3)
        have b6064 := hb (x 2 2)
        have b6065 := hb (x 3 13)
        have b6066 := hb (x 4 12)
        clear * - r6060 e6061 e6062 b6063 b6064 b6065 b6066 d6054
        omega
      have d6067 : (x 3 13).toNat = 0 := by
        have r6068 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6069 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e6070 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b6071 := hb (x 1 3)
        have b6072 := hb (x 2 2)
        have b6073 := hb (x 3 13)
        have b6074 := hb (x 4 12)
        clear * - r6068 e6069 e6070 b6071 b6072 b6073 b6074 d6059 d6054
        omega
      have d6075 : (x 1 3).toNat = 0 := by
        have r6076 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6077 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e6078 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b6079 := hb (x 1 3)
        have b6080 := hb (x 2 2)
        have b6081 := hb (x 3 13)
        have b6082 := hb (x 4 12)
        clear * - r6076 e6077 e6078 b6079 b6080 b6081 b6082 d6059 d6067 d6054
        omega
      have d6083 : (x 1 11).toNat = 0 := by
        have r6084 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
        have b6085 := hb (x 1 3)
        have b6086 := hb (x 1 11)
        clear * - r6084 b6085 b6086 d6075
        omega
      have r6087 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6088 := hb (x (-3) 4)
      have b6089 := hb (x 1 11)
      have b6090 := hb (x 0 1 && x 0 12)
      have b6091 := hb (x (-1) 2 && x (-1) 13)
      have b6092 := hb (x (-2) 3 && x (-2) 14)
      linarith only [r6087, b6088, b6089, b6090, b6091, b6092, d6083, g70, g71, d5935, d5971]
  · have f6093 : (x 1 1).toNat = 1 := by rw [h2656]; rfl
    have d6094 : (x 2 14).toNat = 0 := by
      have r6095 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6096 := hb (x 1 1)
      have b6097 := hb (x 2 14)
      clear * - r6095 b6096 b6097 f6093
      omega
    have d6098 : (x 2 1 && x 2 14).toNat = 0 := by
      have r6099 := hand2 (x 2 1) (x 2 14)
      have b6100 := hb (x 2 14)
      have b6101 := hb (x 2 1 && x 2 14)
      clear * - r6099 b6100 b6101 d6094
      omega
    have d6102 : (x 2 2).toNat = 0 := by
      have r6103 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
      have b6104 := hb (x 2 2)
      have b6105 := hb (x 2 14)
      clear * - r6103 b6104 b6105 d6094
      omega
    have d6106 : (x 2 10).toNat = 0 := by
      have r6107 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
      have b6108 := hb (x 2 2)
      have b6109 := hb (x 2 10)
      clear * - r6107 b6108 b6109 d6102
      omega
    have d6110 : (x 3 13).toNat = 1 := by
      have r6111 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6112 := hb (x 1 2)
      have b6113 := hb (x 3 13)
      have b6114 := hb (x 2 1 && x 2 14)
      clear * - r6111 b6112 b6113 b6114 d6098 g24
      omega
    have d6115 : (x 3 1).toNat = 1 := by
      have r6116 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
      have b6117 := hb (x 3 1)
      have b6118 := hb (x 3 13)
      clear * - r6116 b6117 b6118 d6110
      omega
    have d6119 : (x 4 14).toNat = 0 := by
      have r6120 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6121 := hb (x 3 1)
      have b6122 := hb (x 4 14)
      clear * - r6120 b6121 b6122 d6115
      omega
    have d6123 : (x 4 1 && x 4 14).toNat = 0 := by
      have r6124 := hand2 (x 4 1) (x 4 14)
      have b6125 := hb (x 4 14)
      have b6126 := hb (x 4 1 && x 4 14)
      clear * - r6124 b6125 b6126 d6119
      omega
    have d6127 : (x 4 2).toNat = 0 := by
      have r6128 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
      have b6129 := hb (x 4 2)
      have b6130 := hb (x 4 14)
      clear * - r6128 b6129 b6130 d6119
      omega
    have d6131 : (x 4 10).toNat = 0 := by
      have r6132 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
      have b6133 := hb (x 4 2)
      have b6134 := hb (x 4 10)
      clear * - r6132 b6133 b6134 d6127
      omega
    have d6135 : (x 4 12).toNat = 0 := by
      have r6136 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6137 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e6138 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b6139 := hb (x 1 3)
      have b6140 := hb (x 2 2)
      have b6141 := hb (x 3 13)
      have b6142 := hb (x 4 12)
      clear * - r6136 e6137 e6138 b6139 b6140 b6141 b6142 d6110 d6102
      omega
    have d6143 : (x 1 3).toNat = 0 := by
      have r6144 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6145 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e6146 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b6147 := hb (x 1 3)
      have b6148 := hb (x 2 2)
      have b6149 := hb (x 3 13)
      have b6150 := hb (x 4 12)
      clear * - r6144 e6145 e6146 b6147 b6148 b6149 b6150 d6135 d6110 d6102
      omega
    have d6151 : (x 1 11).toNat = 0 := by
      have r6152 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
      have b6153 := hb (x 1 3)
      have b6154 := hb (x 1 11)
      clear * - r6152 b6153 b6154 d6143
      omega
    have d6155 : (x 1 1 && x 1 11).toNat = 0 := by
      have r6156 := hand2 (x 1 1) (x 1 11)
      have b6157 := hb (x 1 11)
      have b6158 := hb (x 1 1 && x 1 11)
      clear * - r6156 b6157 b6158 d6151
      omega
    have d6159 : (x 3 1 && x 3 11).toNat = 1 := by
      have r6160 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6161 := hb (x (-1) 5)
      have b6162 := hb (x 4 10)
      have b6163 := hb (x 3 1 && x 3 11)
      have b6164 := hb (x 2 2 && x 2 12)
      have b6165 := hb (x 1 3 && x 1 13)
      have b6166 := hb (x 0 4 && x 0 14)
      clear * - r6160 b6161 b6162 b6163 b6164 b6165 b6166 d6131 g63 g64 g65 g8
      omega
    have d6167 : (x 3 11).toNat = 1 := by
      have r6168 := hand2 (x 3 1) (x 3 11)
      have b6169 := hb (x 3 11)
      have b6170 := hb (x 3 1 && x 3 11)
      clear * - r6168 b6169 b6170 d6159
      omega
    have d6171 : (x 3 3).toNat = 1 := by
      have r6172 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
      have b6173 := hb (x 3 3)
      have b6174 := hb (x 3 11)
      clear * - r6172 b6173 b6174 d6167
      omega
    have d6175 : (x 6 12).toNat = 0 := by
      have r6176 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6177 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e6178 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b6179 := hb (x 3 3)
      have b6180 := hb (x 4 2)
      have b6181 := hb (x 5 13)
      have b6182 := hb (x 6 12)
      clear * - r6176 e6177 e6178 b6179 b6180 b6181 b6182 d6127 d6171
      omega
    have d6183 : (x 5 13).toNat = 0 := by
      have r6184 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6185 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e6186 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b6187 := hb (x 3 3)
      have b6188 := hb (x 4 2)
      have b6189 := hb (x 5 13)
      have b6190 := hb (x 6 12)
      clear * - r6184 e6185 e6186 b6187 b6188 b6189 b6190 d6175 d6127 d6171
      omega
    have d6191 : (x 3 2).toNat = 1 := by
      have r6192 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6193 := hb (x 3 2)
      have b6194 := hb (x 5 13)
      have b6195 := hb (x 4 1 && x 4 14)
      clear * - r6192 b6193 b6194 b6195 d6183 d6123
      omega
    have d6196 : (x 3 14).toNat = 1 := by
      have r6197 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
      have b6198 := hb (x 3 2)
      have b6199 := hb (x 3 14)
      clear * - r6197 b6198 b6199 d6191
      omega
    have d6200 : (x 2 1).toNat = 0 := by
      have r6201 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6202 := hb (x 2 1)
      have b6203 := hb (x 3 14)
      clear * - r6201 b6202 b6203 d6196
      omega
    have d6204 : (x 2 13).toNat = 0 := by
      have r6205 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
      have b6206 := hb (x 2 1)
      have b6207 := hb (x 2 13)
      clear * - r6205 b6206 b6207 d6200
      omega
    have d6208 : (x 2 5).toNat = 0 := by
      have r6209 : (x 2 5).toNat ≤ (x 2 13).toNat := himp _ _ (hp5 2)
      have b6210 := hb (x 2 5)
      have b6211 := hb (x 2 13)
      clear * - r6209 b6210 b6211 d6204
      omega
    have d6212 : (x (-2) 4 && x (-2) 14).toNat = 1 := by
      have r6213 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6214 := hb (x (-3) 5)
      have b6215 := hb (x 2 10)
      have b6216 := hb (x 1 1 && x 1 11)
      have b6217 := hb (x 0 2 && x 0 12)
      have b6218 := hb (x (-1) 3 && x (-1) 13)
      have b6219 := hb (x (-2) 4 && x (-2) 14)
      clear * - r6213 b6214 b6215 b6216 b6217 b6218 b6219 d6106 d6155 g59 g60 g1
      omega
    have d6220 : (x (-2) 4).toNat = 1 := by
      have r6221 := hand1 (x (-2) 4) (x (-2) 14)
      have b6222 := hb (x (-2) 4)
      have b6223 := hb (x (-2) 4 && x (-2) 14)
      clear * - r6221 b6222 b6223 d6212
      omega
    have d6224 : (x (-2) 12).toNat = 1 := by
      have r6225 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
      have b6226 := hb (x (-2) 4)
      have b6227 := hb (x (-2) 12)
      clear * - r6225 b6226 b6227 d6220
      omega
    have d6228 : (x (-4) 2).toNat = 0 := by
      have r6229 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6230 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e6231 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have b6232 := hb (x (-5) 3)
      have b6233 := hb (x (-4) 2)
      have b6234 := hb (x (-3) 13)
      have b6235 := hb (x (-2) 12)
      clear * - r6229 e6230 e6231 b6232 b6233 b6234 b6235 d6224 g4
      omega
    have d6236 : (x (-2) 13).toNat = 1 := by
      have r6237 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6238 := hb (x (-4) 2)
      have b6239 := hb (x (-2) 13)
      have b6240 := hb (x (-3) 1 && x (-3) 14)
      clear * - r6237 b6238 b6239 b6240 g78 d6228
      omega
    have d6241 : (x (-2) 1).toNat = 1 := by
      have r6242 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
      have b6243 := hb (x (-2) 1)
      have b6244 := hb (x (-2) 13)
      clear * - r6242 b6243 b6244 d6236
      omega
    have d6245 : (x (-1) 12).toNat = 0 := by
      have r6246 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6247 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e6248 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b6249 := hb (x (-4) 3)
      have b6250 := hb (x (-3) 2)
      have b6251 := hb (x (-2) 13)
      have b6252 := hb (x (-1) 12)
      clear * - r6246 e6247 e6248 b6249 b6250 b6251 b6252 d6236
      omega
    have d6253 : (x (-3) 2).toNat = 0 := by
      have r6254 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6255 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e6256 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b6257 := hb (x (-4) 3)
      have b6258 := hb (x (-3) 2)
      have b6259 := hb (x (-2) 13)
      have b6260 := hb (x (-1) 12)
      clear * - r6254 e6255 e6256 b6257 b6258 b6259 b6260 d6245 d6236
      omega
    have d6261 : (x (-3) 10).toNat = 0 := by
      have r6262 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
      have b6263 := hb (x (-3) 2)
      have b6264 := hb (x (-3) 10)
      clear * - r6262 b6263 b6264 d6253
      omega
    have d6265 : (x (-4) 3).toNat = 0 := by
      have r6266 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6267 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e6268 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b6269 := hb (x (-4) 3)
      have b6270 := hb (x (-3) 2)
      have b6271 := hb (x (-2) 13)
      have b6272 := hb (x (-1) 12)
      clear * - r6266 e6267 e6268 b6269 b6270 b6271 b6272 d6245 d6236 d6253
      omega
    have d6273 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
      have r6274 := hand1 (x (-4) 3) (x (-4) 12)
      have b6275 := hb (x (-4) 3)
      have b6276 := hb (x (-4) 3 && x (-4) 12)
      clear * - r6274 b6275 b6276 d6265
      omega
    have d6277 : (x (-4) 11).toNat = 0 := by
      have r6278 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
      have b6279 := hb (x (-4) 3)
      have b6280 := hb (x (-4) 11)
      clear * - r6278 b6279 b6280 d6265
      omega
    have d6281 : (x (-4) 6 && x (-4) 11).toNat = 0 := by
      have r6282 := hand2 (x (-4) 6) (x (-4) 11)
      have b6283 := hb (x (-4) 11)
      have b6284 := hb (x (-4) 6 && x (-4) 11)
      clear * - r6282 b6283 b6284 d6277
      omega
    have d6285 : (x 2 8).toNat = 0 := by
      have r6286 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6287 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e6288 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e6289 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e6290 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e6291 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e6292 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b6293 := hb (x (-5) 7)
      have b6294 := hb (x (-4) 6)
      have b6295 := hb (x (-3) 5)
      have b6296 := hb (x (-2) 4)
      have b6297 := hb (x (-1) 11)
      have b6298 := hb (x 0 10)
      have b6299 := hb (x 1 9)
      have b6300 := hb (x 2 8)
      clear * - r6286 e6287 e6288 e6289 e6290 e6291 e6292 b6293 b6294 b6295 b6296 b6297 b6298 b6299 b6300 g20 g10 d6220 g1
      omega
    have d6301 : (x 1 9).toNat = 0 := by
      have r6302 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6303 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e6304 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e6305 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e6306 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e6307 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e6308 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b6309 := hb (x (-5) 7)
      have b6310 := hb (x (-4) 6)
      have b6311 := hb (x (-3) 5)
      have b6312 := hb (x (-2) 4)
      have b6313 := hb (x (-1) 11)
      have b6314 := hb (x 0 10)
      have b6315 := hb (x 1 9)
      have b6316 := hb (x 2 8)
      clear * - r6302 e6303 e6304 e6305 e6306 e6307 e6308 b6309 b6310 b6311 b6312 b6313 b6314 b6315 b6316 d6285 g20 g10 d6220 g1
      omega
    have d6317 : (x (-4) 6).toNat = 0 := by
      have r6318 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6319 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e6320 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e6321 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e6322 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e6323 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e6324 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b6325 := hb (x (-5) 7)
      have b6326 := hb (x (-4) 6)
      have b6327 := hb (x (-3) 5)
      have b6328 := hb (x (-2) 4)
      have b6329 := hb (x (-1) 11)
      have b6330 := hb (x 0 10)
      have b6331 := hb (x 1 9)
      have b6332 := hb (x 2 8)
      clear * - r6318 e6319 e6320 e6321 e6322 e6323 e6324 b6325 b6326 b6327 b6328 b6329 b6330 b6331 b6332 d6285 d6301 g20 g10 d6220 g1
      omega
    have d6333 : (x (-5) 7).toNat = 0 := by
      have r6334 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6335 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e6336 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e6337 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e6338 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e6339 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e6340 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b6341 := hb (x (-5) 7)
      have b6342 := hb (x (-4) 6)
      have b6343 := hb (x (-3) 5)
      have b6344 := hb (x (-2) 4)
      have b6345 := hb (x (-1) 11)
      have b6346 := hb (x 0 10)
      have b6347 := hb (x 1 9)
      have b6348 := hb (x 2 8)
      clear * - r6334 e6335 e6336 e6337 e6338 e6339 e6340 b6341 b6342 b6343 b6344 b6345 b6346 b6347 b6348 d6285 d6301 g20 g10 d6220 g1 d6317
      omega
    have d6349 : (x (-5) 7 && x (-5) 12).toNat = 0 := by
      have r6350 := hand1 (x (-5) 7) (x (-5) 12)
      have b6351 := hb (x (-5) 7)
      have b6352 := hb (x (-5) 7 && x (-5) 12)
      clear * - r6350 b6351 b6352 d6333
      omega
    have d6353 : (x (-6) 8).toNat = 0 := by
      have r6354 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6355 := hb (x (-12) 14)
      have b6356 := hb (x (-11) 13)
      have b6357 := hb (x (-10) 12)
      have b6358 := hb (x (-9) 11)
      have b6359 := hb (x (-8) 10)
      have b6360 := hb (x (-7) 9)
      have b6361 := hb (x (-6) 8)
      have b6362 := hb (x (-5) 7)
      have b6363 := hb (x (-4) 6)
      have b6364 := hb (x (-3) 5)
      have b6365 := hb (x (-2) 4)
      have b6366 := hb (x (-1) 3)
      have b6367 := hb (x 0 2)
      have b6368 := hb (x 1 1)
      clear * - r6354 b6355 b6356 b6357 b6358 b6359 b6360 b6361 b6362 b6363 b6364 b6365 b6366 b6367 b6368 f6093 g13 g7 d6220 g1 d6317 d6333
      omega
    have d6369 : (x (-6) 8 && x (-6) 13).toNat = 0 := by
      have r6370 := hand1 (x (-6) 8) (x (-6) 13)
      have b6371 := hb (x (-6) 8)
      have b6372 := hb (x (-6) 8 && x (-6) 13)
      clear * - r6370 b6371 b6372 d6353
      omega
    have d6373 : (x (-7) 9).toNat = 0 := by
      have r6374 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6375 := hb (x (-12) 14)
      have b6376 := hb (x (-11) 13)
      have b6377 := hb (x (-10) 12)
      have b6378 := hb (x (-9) 11)
      have b6379 := hb (x (-8) 10)
      have b6380 := hb (x (-7) 9)
      have b6381 := hb (x (-6) 8)
      have b6382 := hb (x (-5) 7)
      have b6383 := hb (x (-4) 6)
      have b6384 := hb (x (-3) 5)
      have b6385 := hb (x (-2) 4)
      have b6386 := hb (x (-1) 3)
      have b6387 := hb (x 0 2)
      have b6388 := hb (x 1 1)
      clear * - r6374 b6375 b6376 b6377 b6378 b6379 b6380 b6381 b6382 b6383 b6384 b6385 b6386 b6387 b6388 f6093 g13 g7 d6220 g1 d6317 d6333 d6353
      omega
    have d6389 : (x (-7) 9 && x (-7) 14).toNat = 0 := by
      have r6390 := hand1 (x (-7) 9) (x (-7) 14)
      have b6391 := hb (x (-7) 9)
      have b6392 := hb (x (-7) 9 && x (-7) 14)
      clear * - r6390 b6391 b6392 d6373
      omega
    have d6393 : (x (-8) 10).toNat = 0 := by
      have r6394 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6395 := hb (x (-12) 14)
      have b6396 := hb (x (-11) 13)
      have b6397 := hb (x (-10) 12)
      have b6398 := hb (x (-9) 11)
      have b6399 := hb (x (-8) 10)
      have b6400 := hb (x (-7) 9)
      have b6401 := hb (x (-6) 8)
      have b6402 := hb (x (-5) 7)
      have b6403 := hb (x (-4) 6)
      have b6404 := hb (x (-3) 5)
      have b6405 := hb (x (-2) 4)
      have b6406 := hb (x (-1) 3)
      have b6407 := hb (x 0 2)
      have b6408 := hb (x 1 1)
      clear * - r6394 b6395 b6396 b6397 b6398 b6399 b6400 b6401 b6402 b6403 b6404 b6405 b6406 b6407 b6408 f6093 g13 g7 d6220 g1 d6317 d6333 d6353 d6373
      omega
    have d6409 : (x (-8) 1 && x (-8) 10).toNat = 0 := by
      have r6410 := hand2 (x (-8) 1) (x (-8) 10)
      have b6411 := hb (x (-8) 10)
      have b6412 := hb (x (-8) 1 && x (-8) 10)
      clear * - r6410 b6411 b6412 d6393
      omega
    have d6413 : (x (-2) 4 && x (-2) 9).toNat = 1 := by
      have r6414 : 1 ≤ (x 2 5).toNat + (x 1 1 && x 1 6).toNat + (x 0 2 && x 0 7).toNat + (x (-1) 3 && x (-1) 8).toNat + (x (-2) 4 && x (-2) 9).toNat + (x (-3) 5 && x (-3) 10).toNat + (x (-4) 6 && x (-4) 11).toNat + (x (-5) 7 && x (-5) 12).toNat + (x (-6) 8 && x (-6) 13).toNat + (x (-7) 9 && x (-7) 14).toNat + (x (-8) 10).toNat := by have q := hcov5 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6415 := hb (x (-8) 10)
      have b6416 := hb (x 2 5)
      have b6417 := hb (x 1 1 && x 1 6)
      have b6418 := hb (x 0 2 && x 0 7)
      have b6419 := hb (x (-1) 3 && x (-1) 8)
      have b6420 := hb (x (-2) 4 && x (-2) 9)
      have b6421 := hb (x (-3) 5 && x (-3) 10)
      have b6422 := hb (x (-4) 6 && x (-4) 11)
      have b6423 := hb (x (-5) 7 && x (-5) 12)
      have b6424 := hb (x (-6) 8 && x (-6) 13)
      have b6425 := hb (x (-7) 9 && x (-7) 14)
      clear * - r6414 b6415 b6416 b6417 b6418 b6419 b6420 b6421 b6422 b6423 b6424 b6425 d6208 g43 g44 g45 g46 d6281 d6349 d6369 d6389 d6393
      omega
    have d6426 : (x (-2) 9).toNat = 1 := by
      have r6427 := hand2 (x (-2) 4) (x (-2) 9)
      have b6428 := hb (x (-2) 9)
      have b6429 := hb (x (-2) 4 && x (-2) 9)
      clear * - r6427 b6428 b6429 d6413
      omega
    have d6430 : (x (-1) 8).toNat = 0 := by
      have r6431 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6432 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
      have e6433 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
      have e6434 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
      have e6435 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
      have e6436 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
      have e6437 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
      have b6438 := hb (x (-8) 7)
      have b6439 := hb (x (-7) 6)
      have b6440 := hb (x (-6) 5)
      have b6441 := hb (x (-5) 4)
      have b6442 := hb (x (-4) 11)
      have b6443 := hb (x (-3) 10)
      have b6444 := hb (x (-2) 9)
      have b6445 := hb (x (-1) 8)
      clear * - r6431 e6432 e6433 e6434 e6435 e6436 e6437 b6438 b6439 b6440 b6441 b6442 b6443 b6444 b6445 d6426 d6261 d6277
      omega
    have d6446 : (x (-5) 4).toNat = 0 := by
      have r6447 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6448 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
      have e6449 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
      have e6450 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
      have e6451 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
      have e6452 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
      have e6453 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
      have b6454 := hb (x (-8) 7)
      have b6455 := hb (x (-7) 6)
      have b6456 := hb (x (-6) 5)
      have b6457 := hb (x (-5) 4)
      have b6458 := hb (x (-4) 11)
      have b6459 := hb (x (-3) 10)
      have b6460 := hb (x (-2) 9)
      have b6461 := hb (x (-1) 8)
      clear * - r6447 e6448 e6449 e6450 e6451 e6452 e6453 b6454 b6455 b6456 b6457 b6458 b6459 b6460 b6461 d6430 d6426 d6261 d6277
      omega
    have d6462 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
      have r6463 := hand1 (x (-5) 4) (x (-5) 13)
      have b6464 := hb (x (-5) 4)
      have b6465 := hb (x (-5) 4 && x (-5) 13)
      clear * - r6463 b6464 b6465 d6446
      omega
    have d6466 : (x (-6) 5).toNat = 0 := by
      have r6467 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6468 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
      have e6469 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
      have e6470 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
      have e6471 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
      have e6472 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
      have e6473 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
      have b6474 := hb (x (-8) 7)
      have b6475 := hb (x (-7) 6)
      have b6476 := hb (x (-6) 5)
      have b6477 := hb (x (-5) 4)
      have b6478 := hb (x (-4) 11)
      have b6479 := hb (x (-3) 10)
      have b6480 := hb (x (-2) 9)
      have b6481 := hb (x (-1) 8)
      clear * - r6467 e6468 e6469 e6470 e6471 e6472 e6473 b6474 b6475 b6476 b6477 b6478 b6479 b6480 b6481 d6430 d6426 d6261 d6277 d6446
      omega
    have d6482 : (x (-6) 5 && x (-6) 14).toNat = 0 := by
      have r6483 := hand1 (x (-6) 5) (x (-6) 14)
      have b6484 := hb (x (-6) 5)
      have b6485 := hb (x (-6) 5 && x (-6) 14)
      clear * - r6483 b6484 b6485 d6466
      omega
    have d6486 : (x (-7) 6).toNat = 0 := by
      have r6487 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6488 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
      have e6489 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
      have e6490 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
      have e6491 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
      have e6492 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
      have e6493 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
      have b6494 := hb (x (-8) 7)
      have b6495 := hb (x (-7) 6)
      have b6496 := hb (x (-6) 5)
      have b6497 := hb (x (-5) 4)
      have b6498 := hb (x (-4) 11)
      have b6499 := hb (x (-3) 10)
      have b6500 := hb (x (-2) 9)
      have b6501 := hb (x (-1) 8)
      clear * - r6487 e6488 e6489 e6490 e6491 e6492 e6493 b6494 b6495 b6496 b6497 b6498 b6499 b6500 b6501 d6430 d6426 d6261 d6277 d6446 d6466
      omega
    have d6502 : (x (-2) 1 && x (-2) 10).toNat = 1 := by
      have r6503 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6504 := hb (x (-7) 6)
      have b6505 := hb (x (-1) 9)
      have b6506 := hb (x (-2) 1 && x (-2) 10)
      have b6507 := hb (x (-3) 2 && x (-3) 11)
      have b6508 := hb (x (-4) 3 && x (-4) 12)
      have b6509 := hb (x (-5) 4 && x (-5) 13)
      have b6510 := hb (x (-6) 5 && x (-6) 14)
      clear * - r6503 b6504 b6505 b6506 b6507 b6508 b6509 b6510 g9 g55 d6273 d6462 d6482 d6486
      omega
    have d6511 : (x (-2) 10).toNat = 1 := by
      have r6512 := hand2 (x (-2) 1) (x (-2) 10)
      have b6513 := hb (x (-2) 10)
      have b6514 := hb (x (-2) 1 && x (-2) 10)
      clear * - r6512 b6513 b6514 d6502
      omega
    have d6515 : (x (-4) 4).toNat = 0 := by
      have r6516 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6517 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
      have e6518 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
      have e6519 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
      have e6520 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
      have e6521 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
      have e6522 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
      have b6523 := hb (x (-7) 7)
      have b6524 := hb (x (-6) 6)
      have b6525 := hb (x (-5) 5)
      have b6526 := hb (x (-4) 4)
      have b6527 := hb (x (-3) 11)
      have b6528 := hb (x (-2) 10)
      have b6529 := hb (x (-1) 9)
      have b6530 := hb (x 0 8)
      clear * - r6516 e6517 e6518 e6519 e6520 e6521 e6522 b6523 b6524 b6525 b6526 b6527 b6528 b6529 b6530 g18 g9 d6511 g3
      omega
    have d6531 : (x (-5) 5).toNat = 0 := by
      have r6532 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6533 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
      have e6534 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
      have e6535 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
      have e6536 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
      have e6537 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
      have e6538 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
      have b6539 := hb (x (-7) 7)
      have b6540 := hb (x (-6) 6)
      have b6541 := hb (x (-5) 5)
      have b6542 := hb (x (-4) 4)
      have b6543 := hb (x (-3) 11)
      have b6544 := hb (x (-2) 10)
      have b6545 := hb (x (-1) 9)
      have b6546 := hb (x 0 8)
      clear * - r6532 e6533 e6534 e6535 e6536 e6537 e6538 b6539 b6540 b6541 b6542 b6543 b6544 b6545 b6546 g18 g9 d6511 g3 d6515
      omega
    have d6547 : (x (-6) 6).toNat = 0 := by
      have r6548 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6549 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
      have e6550 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
      have e6551 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
      have e6552 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
      have e6553 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
      have e6554 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
      have b6555 := hb (x (-7) 7)
      have b6556 := hb (x (-6) 6)
      have b6557 := hb (x (-5) 5)
      have b6558 := hb (x (-4) 4)
      have b6559 := hb (x (-3) 11)
      have b6560 := hb (x (-2) 10)
      have b6561 := hb (x (-1) 9)
      have b6562 := hb (x 0 8)
      clear * - r6548 e6549 e6550 e6551 e6552 e6553 e6554 b6555 b6556 b6557 b6558 b6559 b6560 b6561 b6562 g18 g9 d6511 g3 d6515 d6531
      omega
    have d6563 : (x (-6) 1 && x (-6) 6).toNat = 0 := by
      have r6564 := hand2 (x (-6) 1) (x (-6) 6)
      have b6565 := hb (x (-6) 6)
      have b6566 := hb (x (-6) 1 && x (-6) 6)
      clear * - r6564 b6565 b6566 d6547
      omega
    have d6567 : (x (-7) 7).toNat = 0 := by
      have r6568 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6569 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
      have e6570 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
      have e6571 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
      have e6572 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
      have e6573 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
      have e6574 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
      have b6575 := hb (x (-7) 7)
      have b6576 := hb (x (-6) 6)
      have b6577 := hb (x (-5) 5)
      have b6578 := hb (x (-4) 4)
      have b6579 := hb (x (-3) 11)
      have b6580 := hb (x (-2) 10)
      have b6581 := hb (x (-1) 9)
      have b6582 := hb (x 0 8)
      clear * - r6568 e6569 e6570 e6571 e6572 e6573 e6574 b6575 b6576 b6577 b6578 b6579 b6580 b6581 b6582 g18 g9 d6511 g3 d6515 d6531 d6547
      omega
    have d6583 : (x (-7) 2 && x (-7) 7).toNat = 0 := by
      have r6584 := hand2 (x (-7) 2) (x (-7) 7)
      have b6585 := hb (x (-7) 7)
      have b6586 := hb (x (-7) 2 && x (-7) 7)
      clear * - r6584 b6585 b6586 d6567
      omega
    have d6587 : (x (-8) 7).toNat = 0 := by
      have r6588 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6589 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
      have e6590 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
      have e6591 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
      have e6592 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
      have e6593 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
      have e6594 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
      have b6595 := hb (x (-8) 7)
      have b6596 := hb (x (-7) 6)
      have b6597 := hb (x (-6) 5)
      have b6598 := hb (x (-5) 4)
      have b6599 := hb (x (-4) 11)
      have b6600 := hb (x (-3) 10)
      have b6601 := hb (x (-2) 9)
      have b6602 := hb (x (-1) 8)
      clear * - r6588 e6589 e6590 e6591 e6592 e6593 e6594 b6595 b6596 b6597 b6598 b6599 b6600 b6601 b6602 d6430 d6426 d6261 d6277 d6446 d6466 d6486
      omega
    have d6603 : (x (-9) 11).toNat = 0 := by
      have r6604 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6605 := hb (x (-12) 14)
      have b6606 := hb (x (-11) 13)
      have b6607 := hb (x (-10) 12)
      have b6608 := hb (x (-9) 11)
      have b6609 := hb (x (-8) 10)
      have b6610 := hb (x (-7) 9)
      have b6611 := hb (x (-6) 8)
      have b6612 := hb (x (-5) 7)
      have b6613 := hb (x (-4) 6)
      have b6614 := hb (x (-3) 5)
      have b6615 := hb (x (-2) 4)
      have b6616 := hb (x (-1) 3)
      have b6617 := hb (x 0 2)
      have b6618 := hb (x 1 1)
      clear * - r6604 b6605 b6606 b6607 b6608 b6609 b6610 b6611 b6612 b6613 b6614 b6615 b6616 b6617 b6618 f6093 g13 g7 d6220 g1 d6317 d6333 d6353 d6373 d6393
      omega
    have d6619 : (x (-9) 1 && x (-9) 11).toNat = 0 := by
      have r6620 := hand2 (x (-9) 1) (x (-9) 11)
      have b6621 := hb (x (-9) 11)
      have b6622 := hb (x (-9) 1 && x (-9) 11)
      clear * - r6620 b6621 b6622 d6603
      omega
    have d6623 : (x (-9) 2 && x (-9) 11).toNat = 0 := by
      have r6624 := hand2 (x (-9) 2) (x (-9) 11)
      have b6625 := hb (x (-9) 11)
      have b6626 := hb (x (-9) 2 && x (-9) 11)
      clear * - r6624 b6625 b6626 d6603
      omega
    have d6627 : (x (-10) 12).toNat = 0 := by
      have r6628 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6629 := hb (x (-12) 14)
      have b6630 := hb (x (-11) 13)
      have b6631 := hb (x (-10) 12)
      have b6632 := hb (x (-9) 11)
      have b6633 := hb (x (-8) 10)
      have b6634 := hb (x (-7) 9)
      have b6635 := hb (x (-6) 8)
      have b6636 := hb (x (-5) 7)
      have b6637 := hb (x (-4) 6)
      have b6638 := hb (x (-3) 5)
      have b6639 := hb (x (-2) 4)
      have b6640 := hb (x (-1) 3)
      have b6641 := hb (x 0 2)
      have b6642 := hb (x 1 1)
      clear * - r6628 b6629 b6630 b6631 b6632 b6633 b6634 b6635 b6636 b6637 b6638 b6639 b6640 b6641 b6642 f6093 g13 g7 d6220 g1 d6317 d6333 d6353 d6373 d6393 d6603
      omega
    have d6643 : (x (-10) 2 && x (-10) 12).toNat = 0 := by
      have r6644 := hand2 (x (-10) 2) (x (-10) 12)
      have b6645 := hb (x (-10) 12)
      have b6646 := hb (x (-10) 2 && x (-10) 12)
      clear * - r6644 b6645 b6646 d6627
      omega
    have d6647 : (x (-10) 3 && x (-10) 12).toNat = 0 := by
      have r6648 := hand2 (x (-10) 3) (x (-10) 12)
      have b6649 := hb (x (-10) 12)
      have b6650 := hb (x (-10) 3 && x (-10) 12)
      clear * - r6648 b6649 b6650 d6627
      omega
    have d6651 : (x (-11) 13).toNat = 0 := by
      have r6652 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6653 := hb (x (-12) 14)
      have b6654 := hb (x (-11) 13)
      have b6655 := hb (x (-10) 12)
      have b6656 := hb (x (-9) 11)
      have b6657 := hb (x (-8) 10)
      have b6658 := hb (x (-7) 9)
      have b6659 := hb (x (-6) 8)
      have b6660 := hb (x (-5) 7)
      have b6661 := hb (x (-4) 6)
      have b6662 := hb (x (-3) 5)
      have b6663 := hb (x (-2) 4)
      have b6664 := hb (x (-1) 3)
      have b6665 := hb (x 0 2)
      have b6666 := hb (x 1 1)
      clear * - r6652 b6653 b6654 b6655 b6656 b6657 b6658 b6659 b6660 b6661 b6662 b6663 b6664 b6665 b6666 f6093 g13 g7 d6220 g1 d6317 d6333 d6353 d6373 d6393 d6603 d6627
      omega
    have d6667 : (x (-11) 3 && x (-11) 13).toNat = 0 := by
      have r6668 := hand2 (x (-11) 3) (x (-11) 13)
      have b6669 := hb (x (-11) 13)
      have b6670 := hb (x (-11) 3 && x (-11) 13)
      clear * - r6668 b6669 b6670 d6651
      omega
    have d6671 : (x (-11) 4 && x (-11) 13).toNat = 0 := by
      have r6672 := hand2 (x (-11) 4) (x (-11) 13)
      have b6673 := hb (x (-11) 13)
      have b6674 := hb (x (-11) 4 && x (-11) 13)
      clear * - r6672 b6673 b6674 d6651
      omega
    have d6675 : (x (-12) 14).toNat = 0 := by
      have r6676 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6677 := hb (x (-12) 14)
      have b6678 := hb (x (-11) 13)
      have b6679 := hb (x (-10) 12)
      have b6680 := hb (x (-9) 11)
      have b6681 := hb (x (-8) 10)
      have b6682 := hb (x (-7) 9)
      have b6683 := hb (x (-6) 8)
      have b6684 := hb (x (-5) 7)
      have b6685 := hb (x (-4) 6)
      have b6686 := hb (x (-3) 5)
      have b6687 := hb (x (-2) 4)
      have b6688 := hb (x (-1) 3)
      have b6689 := hb (x 0 2)
      have b6690 := hb (x 1 1)
      clear * - r6676 b6677 b6678 b6679 b6680 b6681 b6682 b6683 b6684 b6685 b6686 b6687 b6688 b6689 b6690 f6093 g13 g7 d6220 g1 d6317 d6333 d6353 d6373 d6393 d6603 d6627 d6651
      omega
    have d6691 : (x (-12) 1 && x (-12) 14).toNat = 0 := by
      have r6692 := hand2 (x (-12) 1) (x (-12) 14)
      have b6693 := hb (x (-12) 14)
      have b6694 := hb (x (-12) 1 && x (-12) 14)
      clear * - r6692 b6693 b6694 d6675
      omega
    have d6695 : (x (-13) 2).toNat = 1 := by
      have r6696 : 1 ≤ (x (-11) 13).toNat + (x (-12) 1 && x (-12) 14).toNat + (x (-13) 2).toNat := by have q := hcov13 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6697 := hb (x (-13) 2)
      have b6698 := hb (x (-11) 13)
      have b6699 := hb (x (-12) 1 && x (-12) 14)
      clear * - r6696 b6697 b6698 b6699 d6651 d6691
      omega
    have d6700 : (x (-13) 14).toNat = 1 := by
      have r6701 : (x (-13) 2).toNat ≤ (x (-13) 14).toNat := himp _ _ (hp2 (-13))
      have b6702 := hb (x (-13) 2)
      have b6703 := hb (x (-13) 14)
      clear * - r6701 b6702 b6703 d6695
      omega
    have d6704 : (x (-14) 1).toNat = 0 := by
      have r6705 : (x (-13) 14).toNat + (x (-14) 1).toNat = 1 := by have q := hd14 (-13); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6706 := hb (x (-14) 1)
      have b6707 := hb (x (-13) 14)
      clear * - r6705 b6706 b6707 d6700
      omega
    have d6708 : (x (-14) 1 && x (-14) 14).toNat = 0 := by
      have r6709 := hand1 (x (-14) 1) (x (-14) 14)
      have b6710 := hb (x (-14) 1)
      have b6711 := hb (x (-14) 1 && x (-14) 14)
      clear * - r6709 b6710 b6711 d6704
      omega
    have d6712 : (x (-14) 1 && x (-14) 11).toNat = 0 := by
      have r6713 := hand1 (x (-14) 1) (x (-14) 11)
      have b6714 := hb (x (-14) 1)
      have b6715 := hb (x (-14) 1 && x (-14) 11)
      clear * - r6713 b6714 b6715 d6704
      omega
    have d6716 : (x (-14) 13).toNat = 0 := by
      have r6717 : (x (-14) 13).toNat ≤ (x (-14) 1).toNat := himp _ _ (hp13 (-14))
      have b6718 := hb (x (-14) 1)
      have b6719 := hb (x (-14) 13)
      clear * - r6717 b6718 b6719 d6704
      omega
    have d6720 : (x (-14) 5).toNat = 0 := by
      have r6721 : (x (-14) 5).toNat ≤ (x (-14) 13).toNat := himp _ _ (hp5 (-14))
      have b6722 := hb (x (-14) 5)
      have b6723 := hb (x (-14) 13)
      clear * - r6721 b6722 b6723 d6716
      omega
    have d6724 : (x (-14) 9).toNat = 0 := by
      have r6725 : (x (-14) 9).toNat ≤ (x (-14) 1).toNat := himp _ _ (hp9 (-14))
      have b6726 := hb (x (-14) 1)
      have b6727 := hb (x (-14) 9)
      clear * - r6725 b6726 b6727 d6704
      omega
    have d6728 : (x (-14) 9 && x (-14) 14).toNat = 0 := by
      have r6729 := hand1 (x (-14) 9) (x (-14) 14)
      have b6730 := hb (x (-14) 9)
      have b6731 := hb (x (-14) 9 && x (-14) 14)
      clear * - r6729 b6730 b6731 d6724
      omega
    have d6732 : (x (-11) 12).toNat = 0 := by
      have r6733 : (x (-11) 12).toNat + (x (-12) 1 && x (-12) 13).toNat + (x (-13) 2 && x (-13) 14).toNat + (x (-14) 3).toNat = 1 := by have q := hd12 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6734 : (x (-12) 1 && x (-12) 13).toNat = (x (-12) 13).toNat := handr _ _ (fun h => hp13 (-12) (h))
      have e6735 : (x (-13) 2 && x (-13) 14).toNat = (x (-13) 2).toNat := handl _ _ (fun h => hp2 (-13) (h))
      have b6736 := hb (x (-14) 3)
      have b6737 := hb (x (-13) 2)
      have b6738 := hb (x (-12) 13)
      have b6739 := hb (x (-11) 12)
      clear * - r6733 e6734 e6735 b6736 b6737 b6738 b6739 d6695
      omega
    have d6740 : (x (-11) 2 && x (-11) 12).toNat = 0 := by
      have r6741 := hand2 (x (-11) 2) (x (-11) 12)
      have b6742 := hb (x (-11) 12)
      have b6743 := hb (x (-11) 2 && x (-11) 12)
      clear * - r6741 b6742 b6743 d6732
      omega
    have d6744 : (x (-11) 4).toNat = 0 := by
      have r6745 : (x (-11) 4).toNat ≤ (x (-11) 12).toNat := himp _ _ (hp4 (-11))
      have b6746 := hb (x (-11) 4)
      have b6747 := hb (x (-11) 12)
      clear * - r6745 b6746 b6747 d6732
      omega
    have d6748 : (x (-12) 13).toNat = 0 := by
      have r6749 : (x (-11) 12).toNat + (x (-12) 1 && x (-12) 13).toNat + (x (-13) 2 && x (-13) 14).toNat + (x (-14) 3).toNat = 1 := by have q := hd12 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6750 : (x (-12) 1 && x (-12) 13).toNat = (x (-12) 13).toNat := handr _ _ (fun h => hp13 (-12) (h))
      have e6751 : (x (-13) 2 && x (-13) 14).toNat = (x (-13) 2).toNat := handl _ _ (fun h => hp2 (-13) (h))
      have b6752 := hb (x (-14) 3)
      have b6753 := hb (x (-13) 2)
      have b6754 := hb (x (-12) 13)
      have b6755 := hb (x (-11) 12)
      clear * - r6749 e6750 e6751 b6752 b6753 b6754 b6755 d6732 d6695
      omega
    have d6756 : (x (-12) 3 && x (-12) 13).toNat = 0 := by
      have r6757 := hand2 (x (-12) 3) (x (-12) 13)
      have b6758 := hb (x (-12) 13)
      have b6759 := hb (x (-12) 3 && x (-12) 13)
      clear * - r6757 b6758 b6759 d6748
      omega
    have d6760 : (x (-12) 5).toNat = 0 := by
      have r6761 : (x (-12) 5).toNat ≤ (x (-12) 13).toNat := himp _ _ (hp5 (-12))
      have b6762 := hb (x (-12) 5)
      have b6763 := hb (x (-12) 13)
      clear * - r6761 b6762 b6763 d6748
      omega
    have d6764 : (x (-12) 5 && x (-12) 14).toNat = 0 := by
      have r6765 := hand1 (x (-12) 5) (x (-12) 14)
      have b6766 := hb (x (-12) 5)
      have b6767 := hb (x (-12) 5 && x (-12) 14)
      clear * - r6765 b6766 b6767 d6760
      omega
    have d6768 : (x (-13) 6).toNat = 1 := by
      have r6769 : 1 ≤ (x (-7) 9).toNat + (x (-8) 1 && x (-8) 10).toNat + (x (-9) 2 && x (-9) 11).toNat + (x (-10) 3 && x (-10) 12).toNat + (x (-11) 4 && x (-11) 13).toNat + (x (-12) 5 && x (-12) 14).toNat + (x (-13) 6).toNat := by have q := hcov9 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6770 := hb (x (-13) 6)
      have b6771 := hb (x (-7) 9)
      have b6772 := hb (x (-8) 1 && x (-8) 10)
      have b6773 := hb (x (-9) 2 && x (-9) 11)
      have b6774 := hb (x (-10) 3 && x (-10) 12)
      have b6775 := hb (x (-11) 4 && x (-11) 13)
      have b6776 := hb (x (-12) 5 && x (-12) 14)
      clear * - r6769 b6770 b6771 b6772 b6773 b6774 b6775 b6776 d6373 d6409 d6623 d6647 d6671 d6764
      omega
    have d6777 : (x (-7) 8).toNat = 0 := by
      have r6778 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6779 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
      have e6780 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
      have e6781 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
      have e6782 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
      have e6783 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
      have e6784 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
      have b6785 := hb (x (-14) 7)
      have b6786 := hb (x (-13) 6)
      have b6787 := hb (x (-12) 5)
      have b6788 := hb (x (-11) 4)
      have b6789 := hb (x (-10) 11)
      have b6790 := hb (x (-9) 10)
      have b6791 := hb (x (-8) 9)
      have b6792 := hb (x (-7) 8)
      clear * - r6778 e6779 e6780 e6781 e6782 e6783 e6784 b6785 b6786 b6787 b6788 b6789 b6790 b6791 b6792 d6744 d6760 d6768
      omega
    have d6793 : (x (-8) 9).toNat = 0 := by
      have r6794 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6795 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
      have e6796 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
      have e6797 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
      have e6798 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
      have e6799 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
      have e6800 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
      have b6801 := hb (x (-14) 7)
      have b6802 := hb (x (-13) 6)
      have b6803 := hb (x (-12) 5)
      have b6804 := hb (x (-11) 4)
      have b6805 := hb (x (-10) 11)
      have b6806 := hb (x (-9) 10)
      have b6807 := hb (x (-8) 9)
      have b6808 := hb (x (-7) 8)
      clear * - r6794 e6795 e6796 e6797 e6798 e6799 e6800 b6801 b6802 b6803 b6804 b6805 b6806 b6807 b6808 d6777 d6744 d6760 d6768
      omega
    have d6809 : (x (-9) 10).toNat = 0 := by
      have r6810 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6811 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
      have e6812 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
      have e6813 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
      have e6814 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
      have e6815 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
      have e6816 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
      have b6817 := hb (x (-14) 7)
      have b6818 := hb (x (-13) 6)
      have b6819 := hb (x (-12) 5)
      have b6820 := hb (x (-11) 4)
      have b6821 := hb (x (-10) 11)
      have b6822 := hb (x (-9) 10)
      have b6823 := hb (x (-8) 9)
      have b6824 := hb (x (-7) 8)
      clear * - r6810 e6811 e6812 e6813 e6814 e6815 e6816 b6817 b6818 b6819 b6820 b6821 b6822 b6823 b6824 d6777 d6793 d6744 d6760 d6768
      omega
    have d6825 : (x (-10) 11).toNat = 0 := by
      have r6826 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6827 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
      have e6828 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
      have e6829 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
      have e6830 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
      have e6831 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
      have e6832 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
      have b6833 := hb (x (-14) 7)
      have b6834 := hb (x (-13) 6)
      have b6835 := hb (x (-12) 5)
      have b6836 := hb (x (-11) 4)
      have b6837 := hb (x (-10) 11)
      have b6838 := hb (x (-9) 10)
      have b6839 := hb (x (-8) 9)
      have b6840 := hb (x (-7) 8)
      clear * - r6826 e6827 e6828 e6829 e6830 e6831 e6832 b6833 b6834 b6835 b6836 b6837 b6838 b6839 b6840 d6777 d6793 d6809 d6744 d6760 d6768
      omega
    have d6841 : (x (-10) 1 && x (-10) 11).toNat = 0 := by
      have r6842 := hand2 (x (-10) 1) (x (-10) 11)
      have b6843 := hb (x (-10) 11)
      have b6844 := hb (x (-10) 1 && x (-10) 11)
      clear * - r6842 b6843 b6844 d6825
      omega
    have d6845 : (x (-13) 4 && x (-13) 14).toNat = 1 := by
      have r6846 : 1 ≤ (x (-9) 10).toNat + (x (-10) 1 && x (-10) 11).toNat + (x (-11) 2 && x (-11) 12).toNat + (x (-12) 3 && x (-12) 13).toNat + (x (-13) 4 && x (-13) 14).toNat + (x (-14) 5).toNat := by have q := hcov10 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6847 := hb (x (-14) 5)
      have b6848 := hb (x (-9) 10)
      have b6849 := hb (x (-10) 1 && x (-10) 11)
      have b6850 := hb (x (-11) 2 && x (-11) 12)
      have b6851 := hb (x (-12) 3 && x (-12) 13)
      have b6852 := hb (x (-13) 4 && x (-13) 14)
      clear * - r6846 b6847 b6848 b6849 b6850 b6851 b6852 d6809 d6841 d6740 d6756 d6720
      omega
    have d6853 : (x (-13) 4).toNat = 1 := by
      have r6854 := hand1 (x (-13) 4) (x (-13) 14)
      have b6855 := hb (x (-13) 4)
      have b6856 := hb (x (-13) 4 && x (-13) 14)
      clear * - r6854 b6855 b6856 d6845
      omega
    have d6857 : (x (-13) 12).toNat = 1 := by
      have r6858 : (x (-13) 4).toNat ≤ (x (-13) 12).toNat := himp _ _ (hp4 (-13))
      have b6859 := hb (x (-13) 4)
      have b6860 := hb (x (-13) 12)
      clear * - r6858 b6859 b6860 d6853
      omega
    have d6861 : (x (-15) 2).toNat = 0 := by
      have r6862 : (x (-13) 12).toNat + (x (-14) 1 && x (-14) 13).toNat + (x (-15) 2 && x (-15) 14).toNat + (x (-16) 3).toNat = 1 := by have q := hd12 (-13); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6863 : (x (-14) 1 && x (-14) 13).toNat = (x (-14) 13).toNat := handr _ _ (fun h => hp13 (-14) (h))
      have e6864 : (x (-15) 2 && x (-15) 14).toNat = (x (-15) 2).toNat := handl _ _ (fun h => hp2 (-15) (h))
      have b6865 := hb (x (-16) 3)
      have b6866 := hb (x (-15) 2)
      have b6867 := hb (x (-14) 13)
      have b6868 := hb (x (-13) 12)
      clear * - r6862 e6863 e6864 b6865 b6866 b6867 b6868 d6857 d6716
      omega
    have d6869 : (x (-15) 2 && x (-15) 12).toNat = 0 := by
      have r6870 := hand1 (x (-15) 2) (x (-15) 12)
      have b6871 := hb (x (-15) 2)
      have b6872 := hb (x (-15) 2 && x (-15) 12)
      clear * - r6870 b6871 b6872 d6861
      omega
    have d6873 : (x (-15) 10).toNat = 0 := by
      have r6874 : (x (-15) 10).toNat ≤ (x (-15) 2).toNat := himp _ _ (hp10 (-15))
      have b6875 := hb (x (-15) 2)
      have b6876 := hb (x (-15) 10)
      clear * - r6874 b6875 b6876 d6861
      omega
    have d6877 : (x (-15) 1 && x (-15) 10).toNat = 0 := by
      have r6878 := hand2 (x (-15) 1) (x (-15) 10)
      have b6879 := hb (x (-15) 10)
      have b6880 := hb (x (-15) 1 && x (-15) 10)
      clear * - r6878 b6879 b6880 d6873
      omega
    have d6881 : (x (-13) 13).toNat = 1 := by
      have r6882 : 1 ≤ (x (-13) 13).toNat + (x (-14) 1 && x (-14) 14).toNat + (x (-15) 2).toNat := by have q := hcov13 (-13); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6883 := hb (x (-15) 2)
      have b6884 := hb (x (-13) 13)
      have b6885 := hb (x (-14) 1 && x (-14) 14)
      clear * - r6882 b6883 b6884 b6885 d6708 d6861
      omega
    have d6886 : (x (-12) 12).toNat = 0 := by
      have r6887 : (x (-12) 12).toNat + (x (-13) 1 && x (-13) 13).toNat + (x (-14) 2 && x (-14) 14).toNat + (x (-15) 3).toNat = 1 := by have q := hd12 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6888 : (x (-13) 1 && x (-13) 13).toNat = (x (-13) 13).toNat := handr _ _ (fun h => hp13 (-13) (h))
      have e6889 : (x (-14) 2 && x (-14) 14).toNat = (x (-14) 2).toNat := handl _ _ (fun h => hp2 (-14) (h))
      have b6890 := hb (x (-15) 3)
      have b6891 := hb (x (-14) 2)
      have b6892 := hb (x (-13) 13)
      have b6893 := hb (x (-12) 12)
      clear * - r6887 e6888 e6889 b6890 b6891 b6892 b6893 d6881
      omega
    have d6894 : (x (-12) 7 && x (-12) 12).toNat = 0 := by
      have r6895 := hand2 (x (-12) 7) (x (-12) 12)
      have b6896 := hb (x (-12) 12)
      have b6897 := hb (x (-12) 7 && x (-12) 12)
      clear * - r6895 b6896 b6897 d6886
      omega
    have d6898 : (x (-12) 4).toNat = 0 := by
      have r6899 : (x (-12) 4).toNat ≤ (x (-12) 12).toNat := himp _ _ (hp4 (-12))
      have b6900 := hb (x (-12) 4)
      have b6901 := hb (x (-12) 12)
      clear * - r6899 b6900 b6901 d6886
      omega
    have d6902 : (x (-12) 4 && x (-12) 14).toNat = 0 := by
      have r6903 := hand1 (x (-12) 4) (x (-12) 14)
      have b6904 := hb (x (-12) 4)
      have b6905 := hb (x (-12) 4 && x (-12) 14)
      clear * - r6903 b6904 b6905 d6898
      omega
    have d6906 : (x (-13) 5).toNat = 1 := by
      have r6907 : 1 ≤ (x (-8) 10).toNat + (x (-9) 1 && x (-9) 11).toNat + (x (-10) 2 && x (-10) 12).toNat + (x (-11) 3 && x (-11) 13).toNat + (x (-12) 4 && x (-12) 14).toNat + (x (-13) 5).toNat := by have q := hcov10 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6908 := hb (x (-13) 5)
      have b6909 := hb (x (-8) 10)
      have b6910 := hb (x (-9) 1 && x (-9) 11)
      have b6911 := hb (x (-10) 2 && x (-10) 12)
      have b6912 := hb (x (-11) 3 && x (-11) 13)
      have b6913 := hb (x (-12) 4 && x (-12) 14)
      clear * - r6907 b6908 b6909 b6910 b6911 b6912 b6913 d6393 d6619 d6643 d6667 d6902
      omega
    have d6914 : (x (-8) 8).toNat = 0 := by
      have r6915 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6916 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
      have e6917 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
      have e6918 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
      have e6919 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
      have e6920 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
      have e6921 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
      have b6922 := hb (x (-15) 7)
      have b6923 := hb (x (-14) 6)
      have b6924 := hb (x (-13) 5)
      have b6925 := hb (x (-12) 4)
      have b6926 := hb (x (-11) 11)
      have b6927 := hb (x (-10) 10)
      have b6928 := hb (x (-9) 9)
      have b6929 := hb (x (-8) 8)
      clear * - r6915 e6916 e6917 e6918 e6919 e6920 e6921 b6922 b6923 b6924 b6925 b6926 b6927 b6928 b6929 d6898 d6906
      omega
    have d6930 : (x (-8) 3 && x (-8) 8).toNat = 0 := by
      have r6931 := hand2 (x (-8) 3) (x (-8) 8)
      have b6932 := hb (x (-8) 8)
      have b6933 := hb (x (-8) 3 && x (-8) 8)
      clear * - r6931 b6932 b6933 d6914
      omega
    have d6934 : (x (-9) 9).toNat = 0 := by
      have r6935 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6936 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
      have e6937 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
      have e6938 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
      have e6939 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
      have e6940 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
      have e6941 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
      have b6942 := hb (x (-15) 7)
      have b6943 := hb (x (-14) 6)
      have b6944 := hb (x (-13) 5)
      have b6945 := hb (x (-12) 4)
      have b6946 := hb (x (-11) 11)
      have b6947 := hb (x (-10) 10)
      have b6948 := hb (x (-9) 9)
      have b6949 := hb (x (-8) 8)
      clear * - r6935 e6936 e6937 e6938 e6939 e6940 e6941 b6942 b6943 b6944 b6945 b6946 b6947 b6948 b6949 d6914 d6898 d6906
      omega
    have d6950 : (x (-9) 4 && x (-9) 9).toNat = 0 := by
      have r6951 := hand2 (x (-9) 4) (x (-9) 9)
      have b6952 := hb (x (-9) 9)
      have b6953 := hb (x (-9) 4 && x (-9) 9)
      clear * - r6951 b6952 b6953 d6934
      omega
    have d6954 : (x (-10) 10).toNat = 0 := by
      have r6955 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6956 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
      have e6957 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
      have e6958 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
      have e6959 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
      have e6960 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
      have e6961 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
      have b6962 := hb (x (-15) 7)
      have b6963 := hb (x (-14) 6)
      have b6964 := hb (x (-13) 5)
      have b6965 := hb (x (-12) 4)
      have b6966 := hb (x (-11) 11)
      have b6967 := hb (x (-10) 10)
      have b6968 := hb (x (-9) 9)
      have b6969 := hb (x (-8) 8)
      clear * - r6955 e6956 e6957 e6958 e6959 e6960 e6961 b6962 b6963 b6964 b6965 b6966 b6967 b6968 b6969 d6914 d6934 d6898 d6906
      omega
    have d6970 : (x (-10) 5 && x (-10) 10).toNat = 0 := by
      have r6971 := hand2 (x (-10) 5) (x (-10) 10)
      have b6972 := hb (x (-10) 10)
      have b6973 := hb (x (-10) 5 && x (-10) 10)
      clear * - r6971 b6972 b6973 d6954
      omega
    have d6974 : (x (-11) 11).toNat = 0 := by
      have r6975 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6976 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
      have e6977 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
      have e6978 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
      have e6979 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
      have e6980 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
      have e6981 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
      have b6982 := hb (x (-15) 7)
      have b6983 := hb (x (-14) 6)
      have b6984 := hb (x (-13) 5)
      have b6985 := hb (x (-12) 4)
      have b6986 := hb (x (-11) 11)
      have b6987 := hb (x (-10) 10)
      have b6988 := hb (x (-9) 9)
      have b6989 := hb (x (-8) 8)
      clear * - r6975 e6976 e6977 e6978 e6979 e6980 e6981 b6982 b6983 b6984 b6985 b6986 b6987 b6988 b6989 d6914 d6934 d6954 d6898 d6906
      omega
    have d6990 : (x (-11) 6 && x (-11) 11).toNat = 0 := by
      have r6991 := hand2 (x (-11) 6) (x (-11) 11)
      have b6992 := hb (x (-11) 11)
      have b6993 := hb (x (-11) 6 && x (-11) 11)
      clear * - r6991 b6992 b6993 d6974
      omega
    have d6994 : (x (-13) 8 && x (-13) 13).toNat = 1 := by
      have r6995 : 1 ≤ (x (-5) 5).toNat + (x (-6) 1 && x (-6) 6).toNat + (x (-7) 2 && x (-7) 7).toNat + (x (-8) 3 && x (-8) 8).toNat + (x (-9) 4 && x (-9) 9).toNat + (x (-10) 5 && x (-10) 10).toNat + (x (-11) 6 && x (-11) 11).toNat + (x (-12) 7 && x (-12) 12).toNat + (x (-13) 8 && x (-13) 13).toNat + (x (-14) 9 && x (-14) 14).toNat + (x (-15) 10).toNat := by have q := hcov5 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6996 := hb (x (-15) 10)
      have b6997 := hb (x (-5) 5)
      have b6998 := hb (x (-6) 1 && x (-6) 6)
      have b6999 := hb (x (-7) 2 && x (-7) 7)
      have b7000 := hb (x (-8) 3 && x (-8) 8)
      have b7001 := hb (x (-9) 4 && x (-9) 9)
      have b7002 := hb (x (-10) 5 && x (-10) 10)
      have b7003 := hb (x (-11) 6 && x (-11) 11)
      have b7004 := hb (x (-12) 7 && x (-12) 12)
      have b7005 := hb (x (-13) 8 && x (-13) 13)
      have b7006 := hb (x (-14) 9 && x (-14) 14)
      clear * - r6995 b6996 b6997 b6998 b6999 b7000 b7001 b7002 b7003 b7004 b7005 b7006 d6531 d6563 d6583 d6930 d6950 d6970 d6990 d6894 d6728 d6873
      omega
    have d7007 : (x (-13) 8).toNat = 1 := by
      have r7008 := hand1 (x (-13) 8) (x (-13) 13)
      have b7009 := hb (x (-13) 8)
      have b7010 := hb (x (-13) 8 && x (-13) 13)
      clear * - r7008 b7009 b7010 d6994
      omega
    have d7011 : (x (-16) 11).toNat = 0 := by
      have r7012 : (x (-13) 8).toNat + (x (-14) 1 && x (-14) 9).toNat + (x (-15) 2 && x (-15) 10).toNat + (x (-16) 3 && x (-16) 11).toNat + (x (-17) 4 && x (-17) 12).toNat + (x (-18) 5 && x (-18) 13).toNat + (x (-19) 6 && x (-19) 14).toNat + (x (-20) 7).toNat = 1 := by have q := hd8 (-13); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7013 : (x (-14) 1 && x (-14) 9).toNat = (x (-14) 9).toNat := handr _ _ (fun h => hp9 (-14) (h))
      have e7014 : (x (-15) 2 && x (-15) 10).toNat = (x (-15) 10).toNat := handr _ _ (fun h => hp10 (-15) (h))
      have e7015 : (x (-16) 3 && x (-16) 11).toNat = (x (-16) 11).toNat := handr _ _ (fun h => hp11 (-16) (h))
      have e7016 : (x (-17) 4 && x (-17) 12).toNat = (x (-17) 4).toNat := handl _ _ (fun h => hp4 (-17) (h))
      have e7017 : (x (-18) 5 && x (-18) 13).toNat = (x (-18) 5).toNat := handl _ _ (fun h => hp5 (-18) (h))
      have e7018 : (x (-19) 6 && x (-19) 14).toNat = (x (-19) 6).toNat := handl _ _ (fun h => hp6 (-19) (h))
      have b7019 := hb (x (-20) 7)
      have b7020 := hb (x (-19) 6)
      have b7021 := hb (x (-18) 5)
      have b7022 := hb (x (-17) 4)
      have b7023 := hb (x (-16) 11)
      have b7024 := hb (x (-15) 10)
      have b7025 := hb (x (-14) 9)
      have b7026 := hb (x (-13) 8)
      clear * - r7012 e7013 e7014 e7015 e7016 e7017 e7018 b7019 b7020 b7021 b7022 b7023 b7024 b7025 b7026 d7007 d6724 d6873
      omega
    have d7027 : (x (-16) 2 && x (-16) 11).toNat = 0 := by
      have r7028 := hand2 (x (-16) 2) (x (-16) 11)
      have b7029 := hb (x (-16) 11)
      have b7030 := hb (x (-16) 2 && x (-16) 11)
      clear * - r7028 b7029 b7030 d7011
      omega
    have d7031 : (x (-17) 4).toNat = 0 := by
      have r7032 : (x (-13) 8).toNat + (x (-14) 1 && x (-14) 9).toNat + (x (-15) 2 && x (-15) 10).toNat + (x (-16) 3 && x (-16) 11).toNat + (x (-17) 4 && x (-17) 12).toNat + (x (-18) 5 && x (-18) 13).toNat + (x (-19) 6 && x (-19) 14).toNat + (x (-20) 7).toNat = 1 := by have q := hd8 (-13); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7033 : (x (-14) 1 && x (-14) 9).toNat = (x (-14) 9).toNat := handr _ _ (fun h => hp9 (-14) (h))
      have e7034 : (x (-15) 2 && x (-15) 10).toNat = (x (-15) 10).toNat := handr _ _ (fun h => hp10 (-15) (h))
      have e7035 : (x (-16) 3 && x (-16) 11).toNat = (x (-16) 11).toNat := handr _ _ (fun h => hp11 (-16) (h))
      have e7036 : (x (-17) 4 && x (-17) 12).toNat = (x (-17) 4).toNat := handl _ _ (fun h => hp4 (-17) (h))
      have e7037 : (x (-18) 5 && x (-18) 13).toNat = (x (-18) 5).toNat := handl _ _ (fun h => hp5 (-18) (h))
      have e7038 : (x (-19) 6 && x (-19) 14).toNat = (x (-19) 6).toNat := handl _ _ (fun h => hp6 (-19) (h))
      have b7039 := hb (x (-20) 7)
      have b7040 := hb (x (-19) 6)
      have b7041 := hb (x (-18) 5)
      have b7042 := hb (x (-17) 4)
      have b7043 := hb (x (-16) 11)
      have b7044 := hb (x (-15) 10)
      have b7045 := hb (x (-14) 9)
      have b7046 := hb (x (-13) 8)
      clear * - r7032 e7033 e7034 e7035 e7036 e7037 e7038 b7039 b7040 b7041 b7042 b7043 b7044 b7045 b7046 d7007 d6724 d6873 d7011
      omega
    have d7047 : (x (-17) 4 && x (-17) 14).toNat = 0 := by
      have r7048 := hand1 (x (-17) 4) (x (-17) 14)
      have b7049 := hb (x (-17) 4)
      have b7050 := hb (x (-17) 4 && x (-17) 14)
      clear * - r7048 b7049 b7050 d7031
      omega
    have d7051 : (x (-18) 5).toNat = 0 := by
      have r7052 : (x (-13) 8).toNat + (x (-14) 1 && x (-14) 9).toNat + (x (-15) 2 && x (-15) 10).toNat + (x (-16) 3 && x (-16) 11).toNat + (x (-17) 4 && x (-17) 12).toNat + (x (-18) 5 && x (-18) 13).toNat + (x (-19) 6 && x (-19) 14).toNat + (x (-20) 7).toNat = 1 := by have q := hd8 (-13); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7053 : (x (-14) 1 && x (-14) 9).toNat = (x (-14) 9).toNat := handr _ _ (fun h => hp9 (-14) (h))
      have e7054 : (x (-15) 2 && x (-15) 10).toNat = (x (-15) 10).toNat := handr _ _ (fun h => hp10 (-15) (h))
      have e7055 : (x (-16) 3 && x (-16) 11).toNat = (x (-16) 11).toNat := handr _ _ (fun h => hp11 (-16) (h))
      have e7056 : (x (-17) 4 && x (-17) 12).toNat = (x (-17) 4).toNat := handl _ _ (fun h => hp4 (-17) (h))
      have e7057 : (x (-18) 5 && x (-18) 13).toNat = (x (-18) 5).toNat := handl _ _ (fun h => hp5 (-18) (h))
      have e7058 : (x (-19) 6 && x (-19) 14).toNat = (x (-19) 6).toNat := handl _ _ (fun h => hp6 (-19) (h))
      have b7059 := hb (x (-20) 7)
      have b7060 := hb (x (-19) 6)
      have b7061 := hb (x (-18) 5)
      have b7062 := hb (x (-17) 4)
      have b7063 := hb (x (-16) 11)
      have b7064 := hb (x (-15) 10)
      have b7065 := hb (x (-14) 9)
      have b7066 := hb (x (-13) 8)
      clear * - r7052 e7053 e7054 e7055 e7056 e7057 e7058 b7059 b7060 b7061 b7062 b7063 b7064 b7065 b7066 d7007 d6724 d6873 d7011 d7031
      omega
    have d7067 : (x (-16) 3).toNat = 0 := by
      have r7068 : (x (-13) 12).toNat + (x (-14) 1 && x (-14) 13).toNat + (x (-15) 2 && x (-15) 14).toNat + (x (-16) 3).toNat = 1 := by have q := hd12 (-13); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7069 : (x (-14) 1 && x (-14) 13).toNat = (x (-14) 13).toNat := handr _ _ (fun h => hp13 (-14) (h))
      have e7070 : (x (-15) 2 && x (-15) 14).toNat = (x (-15) 2).toNat := handl _ _ (fun h => hp2 (-15) (h))
      have b7071 := hb (x (-16) 3)
      have b7072 := hb (x (-15) 2)
      have b7073 := hb (x (-14) 13)
      have b7074 := hb (x (-13) 12)
      clear * - r7068 e7069 e7070 b7071 b7072 b7073 b7074 d6857 d6716 d6861
      omega
    have d7075 : (x (-16) 3 && x (-16) 13).toNat = 0 := by
      have r7076 := hand1 (x (-16) 3) (x (-16) 13)
      have b7077 := hb (x (-16) 3)
      have b7078 := hb (x (-16) 3 && x (-16) 13)
      clear * - r7076 b7077 b7078 d7067
      omega
    have d7079 : (x (-13) 10).toNat = 1 := by
      have r7080 : 1 ≤ (x (-13) 10).toNat + (x (-14) 1 && x (-14) 11).toNat + (x (-15) 2 && x (-15) 12).toNat + (x (-16) 3 && x (-16) 13).toNat + (x (-17) 4 && x (-17) 14).toNat + (x (-18) 5).toNat := by have q := hcov10 (-13); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7081 := hb (x (-18) 5)
      have b7082 := hb (x (-13) 10)
      have b7083 := hb (x (-14) 1 && x (-14) 11)
      have b7084 := hb (x (-15) 2 && x (-15) 12)
      have b7085 := hb (x (-16) 3 && x (-16) 13)
      have b7086 := hb (x (-17) 4 && x (-17) 14)
      clear * - r7080 b7081 b7082 b7083 b7084 b7085 b7086 d6712 d6869 d7075 d7047 d7051
      omega
    have d7087 : (x (-11) 8).toNat = 0 := by
      have r7088 : (x (-11) 8).toNat + (x (-12) 1 && x (-12) 9).toNat + (x (-13) 2 && x (-13) 10).toNat + (x (-14) 3 && x (-14) 11).toNat + (x (-15) 4 && x (-15) 12).toNat + (x (-16) 5 && x (-16) 13).toNat + (x (-17) 6 && x (-17) 14).toNat + (x (-18) 7).toNat = 1 := by have q := hd8 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7089 : (x (-12) 1 && x (-12) 9).toNat = (x (-12) 9).toNat := handr _ _ (fun h => hp9 (-12) (h))
      have e7090 : (x (-13) 2 && x (-13) 10).toNat = (x (-13) 10).toNat := handr _ _ (fun h => hp10 (-13) (h))
      have e7091 : (x (-14) 3 && x (-14) 11).toNat = (x (-14) 11).toNat := handr _ _ (fun h => hp11 (-14) (h))
      have e7092 : (x (-15) 4 && x (-15) 12).toNat = (x (-15) 4).toNat := handl _ _ (fun h => hp4 (-15) (h))
      have e7093 : (x (-16) 5 && x (-16) 13).toNat = (x (-16) 5).toNat := handl _ _ (fun h => hp5 (-16) (h))
      have e7094 : (x (-17) 6 && x (-17) 14).toNat = (x (-17) 6).toNat := handl _ _ (fun h => hp6 (-17) (h))
      have b7095 := hb (x (-18) 7)
      have b7096 := hb (x (-17) 6)
      have b7097 := hb (x (-16) 5)
      have b7098 := hb (x (-15) 4)
      have b7099 := hb (x (-14) 11)
      have b7100 := hb (x (-13) 10)
      have b7101 := hb (x (-12) 9)
      have b7102 := hb (x (-11) 8)
      clear * - r7088 e7089 e7090 e7091 e7092 e7093 e7094 b7095 b7096 b7097 b7098 b7099 b7100 b7101 b7102 d7079
      omega
    have d7103 : (x (-12) 9).toNat = 0 := by
      have r7104 : (x (-11) 8).toNat + (x (-12) 1 && x (-12) 9).toNat + (x (-13) 2 && x (-13) 10).toNat + (x (-14) 3 && x (-14) 11).toNat + (x (-15) 4 && x (-15) 12).toNat + (x (-16) 5 && x (-16) 13).toNat + (x (-17) 6 && x (-17) 14).toNat + (x (-18) 7).toNat = 1 := by have q := hd8 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7105 : (x (-12) 1 && x (-12) 9).toNat = (x (-12) 9).toNat := handr _ _ (fun h => hp9 (-12) (h))
      have e7106 : (x (-13) 2 && x (-13) 10).toNat = (x (-13) 10).toNat := handr _ _ (fun h => hp10 (-13) (h))
      have e7107 : (x (-14) 3 && x (-14) 11).toNat = (x (-14) 11).toNat := handr _ _ (fun h => hp11 (-14) (h))
      have e7108 : (x (-15) 4 && x (-15) 12).toNat = (x (-15) 4).toNat := handl _ _ (fun h => hp4 (-15) (h))
      have e7109 : (x (-16) 5 && x (-16) 13).toNat = (x (-16) 5).toNat := handl _ _ (fun h => hp5 (-16) (h))
      have e7110 : (x (-17) 6 && x (-17) 14).toNat = (x (-17) 6).toNat := handl _ _ (fun h => hp6 (-17) (h))
      have b7111 := hb (x (-18) 7)
      have b7112 := hb (x (-17) 6)
      have b7113 := hb (x (-16) 5)
      have b7114 := hb (x (-15) 4)
      have b7115 := hb (x (-14) 11)
      have b7116 := hb (x (-13) 10)
      have b7117 := hb (x (-12) 9)
      have b7118 := hb (x (-11) 8)
      clear * - r7104 e7105 e7106 e7107 e7108 e7109 e7110 b7111 b7112 b7113 b7114 b7115 b7116 b7117 b7118 d7087 d7079
      omega
    have d7119 : (x (-14) 11).toNat = 0 := by
      have r7120 : (x (-11) 8).toNat + (x (-12) 1 && x (-12) 9).toNat + (x (-13) 2 && x (-13) 10).toNat + (x (-14) 3 && x (-14) 11).toNat + (x (-15) 4 && x (-15) 12).toNat + (x (-16) 5 && x (-16) 13).toNat + (x (-17) 6 && x (-17) 14).toNat + (x (-18) 7).toNat = 1 := by have q := hd8 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7121 : (x (-12) 1 && x (-12) 9).toNat = (x (-12) 9).toNat := handr _ _ (fun h => hp9 (-12) (h))
      have e7122 : (x (-13) 2 && x (-13) 10).toNat = (x (-13) 10).toNat := handr _ _ (fun h => hp10 (-13) (h))
      have e7123 : (x (-14) 3 && x (-14) 11).toNat = (x (-14) 11).toNat := handr _ _ (fun h => hp11 (-14) (h))
      have e7124 : (x (-15) 4 && x (-15) 12).toNat = (x (-15) 4).toNat := handl _ _ (fun h => hp4 (-15) (h))
      have e7125 : (x (-16) 5 && x (-16) 13).toNat = (x (-16) 5).toNat := handl _ _ (fun h => hp5 (-16) (h))
      have e7126 : (x (-17) 6 && x (-17) 14).toNat = (x (-17) 6).toNat := handl _ _ (fun h => hp6 (-17) (h))
      have b7127 := hb (x (-18) 7)
      have b7128 := hb (x (-17) 6)
      have b7129 := hb (x (-16) 5)
      have b7130 := hb (x (-15) 4)
      have b7131 := hb (x (-14) 11)
      have b7132 := hb (x (-13) 10)
      have b7133 := hb (x (-12) 9)
      have b7134 := hb (x (-11) 8)
      clear * - r7120 e7121 e7122 e7123 e7124 e7125 e7126 b7127 b7128 b7129 b7130 b7131 b7132 b7133 b7134 d7087 d7103 d7079
      omega
    have d7135 : (x (-9) 8).toNat = 0 := by
      have r7136 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7137 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
      have e7138 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
      have e7139 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
      have e7140 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
      have e7141 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
      have e7142 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
      have b7143 := hb (x (-16) 7)
      have b7144 := hb (x (-15) 6)
      have b7145 := hb (x (-14) 5)
      have b7146 := hb (x (-13) 4)
      have b7147 := hb (x (-12) 11)
      have b7148 := hb (x (-11) 10)
      have b7149 := hb (x (-10) 9)
      have b7150 := hb (x (-9) 8)
      clear * - r7136 e7137 e7138 e7139 e7140 e7141 e7142 b7143 b7144 b7145 b7146 b7147 b7148 b7149 b7150 d6853 d6720
      omega
    have d7151 : (x (-10) 9).toNat = 0 := by
      have r7152 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7153 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
      have e7154 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
      have e7155 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
      have e7156 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
      have e7157 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
      have e7158 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
      have b7159 := hb (x (-16) 7)
      have b7160 := hb (x (-15) 6)
      have b7161 := hb (x (-14) 5)
      have b7162 := hb (x (-13) 4)
      have b7163 := hb (x (-12) 11)
      have b7164 := hb (x (-11) 10)
      have b7165 := hb (x (-10) 9)
      have b7166 := hb (x (-9) 8)
      clear * - r7152 e7153 e7154 e7155 e7156 e7157 e7158 b7159 b7160 b7161 b7162 b7163 b7164 b7165 b7166 d7135 d6853 d6720
      omega
    have d7167 : (x (-11) 10).toNat = 0 := by
      have r7168 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7169 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
      have e7170 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
      have e7171 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
      have e7172 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
      have e7173 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
      have e7174 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
      have b7175 := hb (x (-16) 7)
      have b7176 := hb (x (-15) 6)
      have b7177 := hb (x (-14) 5)
      have b7178 := hb (x (-13) 4)
      have b7179 := hb (x (-12) 11)
      have b7180 := hb (x (-11) 10)
      have b7181 := hb (x (-10) 9)
      have b7182 := hb (x (-9) 8)
      clear * - r7168 e7169 e7170 e7171 e7172 e7173 e7174 b7175 b7176 b7177 b7178 b7179 b7180 b7181 b7182 d7135 d7151 d6853 d6720
      omega
    have d7183 : (x (-12) 11).toNat = 0 := by
      have r7184 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7185 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
      have e7186 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
      have e7187 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
      have e7188 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
      have e7189 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
      have e7190 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
      have b7191 := hb (x (-16) 7)
      have b7192 := hb (x (-15) 6)
      have b7193 := hb (x (-14) 5)
      have b7194 := hb (x (-13) 4)
      have b7195 := hb (x (-12) 11)
      have b7196 := hb (x (-11) 10)
      have b7197 := hb (x (-10) 9)
      have b7198 := hb (x (-9) 8)
      clear * - r7184 e7185 e7186 e7187 e7188 e7189 e7190 b7191 b7192 b7193 b7194 b7195 b7196 b7197 b7198 d7135 d7151 d7167 d6853 d6720
      omega
    have d7199 : (x (-14) 14).toNat = 1 := by
      have r7200 : (x (-1) 1).toNat + (x (-2) 2).toNat + (x (-3) 3).toNat + (x (-4) 4).toNat + (x (-5) 5).toNat + (x (-6) 6).toNat + (x (-7) 7).toNat + (x (-8) 8).toNat + (x (-9) 9).toNat + (x (-10) 10).toNat + (x (-11) 11).toNat + (x (-12) 12).toNat + (x (-13) 13).toNat + (x (-14) 14).toNat = 3 := by have q := hcount 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7201 := hb (x (-14) 14)
      have b7202 := hb (x (-13) 13)
      have b7203 := hb (x (-12) 12)
      have b7204 := hb (x (-11) 11)
      have b7205 := hb (x (-10) 10)
      have b7206 := hb (x (-9) 9)
      have b7207 := hb (x (-8) 8)
      have b7208 := hb (x (-7) 7)
      have b7209 := hb (x (-6) 6)
      have b7210 := hb (x (-5) 5)
      have b7211 := hb (x (-4) 4)
      have b7212 := hb (x (-3) 3)
      have b7213 := hb (x (-2) 2)
      have b7214 := hb (x (-1) 1)
      clear * - r7200 b7201 b7202 b7203 b7204 b7205 b7206 b7207 b7208 b7209 b7210 b7211 b7212 b7213 b7214 g6 g5 g0 d6515 d6531 d6547 d6567 d6914 d6934 d6954 d6974 d6886 d6881
      omega
    have d7215 : (x (-15) 1).toNat = 0 := by
      have r7216 : (x (-14) 14).toNat + (x (-15) 1).toNat = 1 := by have q := hd14 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7217 := hb (x (-15) 1)
      have b7218 := hb (x (-14) 14)
      clear * - r7216 b7217 b7218 d7199
      omega
    have d7219 : (x (-15) 1 && x (-15) 14).toNat = 0 := by
      have r7220 := hand1 (x (-15) 1) (x (-15) 14)
      have b7221 := hb (x (-15) 1)
      have b7222 := hb (x (-15) 1 && x (-15) 14)
      clear * - r7220 b7221 b7222 d7215
      omega
    have d7223 : (x (-16) 2).toNat = 1 := by
      have r7224 : 1 ≤ (x (-14) 13).toNat + (x (-15) 1 && x (-15) 14).toNat + (x (-16) 2).toNat := by have q := hcov13 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7225 := hb (x (-16) 2)
      have b7226 := hb (x (-14) 13)
      have b7227 := hb (x (-15) 1 && x (-15) 14)
      clear * - r7224 b7225 b7226 b7227 d6716 d7219
      omega
    have d7228 : (x (-16) 14).toNat = 1 := by
      have r7229 : (x (-16) 2).toNat ≤ (x (-16) 14).toNat := himp _ _ (hp2 (-16))
      have b7230 := hb (x (-16) 2)
      have b7231 := hb (x (-16) 14)
      clear * - r7229 b7230 b7231 d7223
      omega
    have d7232 : (x (-17) 1).toNat = 0 := by
      have r7233 : (x (-16) 14).toNat + (x (-17) 1).toNat = 1 := by have q := hd14 (-16); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7234 := hb (x (-17) 1)
      have b7235 := hb (x (-16) 14)
      clear * - r7233 b7234 b7235 d7228
      omega
    have d7236 : (x (-17) 13).toNat = 0 := by
      have r7237 : (x (-17) 13).toNat ≤ (x (-17) 1).toNat := himp _ _ (hp13 (-17))
      have b7238 := hb (x (-17) 1)
      have b7239 := hb (x (-17) 13)
      clear * - r7237 b7238 b7239 d7232
      omega
    have d7240 : (x (-14) 12).toNat = 0 := by
      have r7241 : (x (-14) 12).toNat + (x (-15) 1 && x (-15) 13).toNat + (x (-16) 2 && x (-16) 14).toNat + (x (-17) 3).toNat = 1 := by have q := hd12 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7242 : (x (-15) 1 && x (-15) 13).toNat = (x (-15) 13).toNat := handr _ _ (fun h => hp13 (-15) (h))
      have e7243 : (x (-16) 2 && x (-16) 14).toNat = (x (-16) 2).toNat := handl _ _ (fun h => hp2 (-16) (h))
      have b7244 := hb (x (-17) 3)
      have b7245 := hb (x (-16) 2)
      have b7246 := hb (x (-15) 13)
      have b7247 := hb (x (-14) 12)
      clear * - r7241 e7242 e7243 b7244 b7245 b7246 b7247 d7223
      omega
    have d7248 : (x (-15) 13).toNat = 0 := by
      have r7249 : (x (-14) 12).toNat + (x (-15) 1 && x (-15) 13).toNat + (x (-16) 2 && x (-16) 14).toNat + (x (-17) 3).toNat = 1 := by have q := hd12 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7250 : (x (-15) 1 && x (-15) 13).toNat = (x (-15) 13).toNat := handr _ _ (fun h => hp13 (-15) (h))
      have e7251 : (x (-16) 2 && x (-16) 14).toNat = (x (-16) 2).toNat := handl _ _ (fun h => hp2 (-16) (h))
      have b7252 := hb (x (-17) 3)
      have b7253 := hb (x (-16) 2)
      have b7254 := hb (x (-15) 13)
      have b7255 := hb (x (-14) 12)
      clear * - r7249 e7250 e7251 b7252 b7253 b7254 b7255 d7240 d7223
      omega
    have d7256 : (x (-17) 3).toNat = 0 := by
      have r7257 : (x (-14) 12).toNat + (x (-15) 1 && x (-15) 13).toNat + (x (-16) 2 && x (-16) 14).toNat + (x (-17) 3).toNat = 1 := by have q := hd12 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7258 : (x (-15) 1 && x (-15) 13).toNat = (x (-15) 13).toNat := handr _ _ (fun h => hp13 (-15) (h))
      have e7259 : (x (-16) 2 && x (-16) 14).toNat = (x (-16) 2).toNat := handl _ _ (fun h => hp2 (-16) (h))
      have b7260 := hb (x (-17) 3)
      have b7261 := hb (x (-16) 2)
      have b7262 := hb (x (-15) 13)
      have b7263 := hb (x (-14) 12)
      clear * - r7257 e7258 e7259 b7260 b7261 b7262 b7263 d7240 d7248 d7223
      omega
    have d7264 : (x (-17) 3 && x (-17) 14).toNat = 0 := by
      have r7265 := hand1 (x (-17) 3) (x (-17) 14)
      have b7266 := hb (x (-17) 3)
      have b7267 := hb (x (-17) 3 && x (-17) 14)
      clear * - r7265 b7266 b7267 d7256
      omega
    have d7268 : (x (-17) 3 && x (-17) 12).toNat = 0 := by
      have r7269 := hand1 (x (-17) 3) (x (-17) 12)
      have b7270 := hb (x (-17) 3)
      have b7271 := hb (x (-17) 3 && x (-17) 12)
      clear * - r7269 b7270 b7271 d7256
      omega
    have d7272 : (x (-17) 11).toNat = 0 := by
      have r7273 : (x (-17) 11).toNat ≤ (x (-17) 3).toNat := himp _ _ (hp11 (-17))
      have b7274 := hb (x (-17) 3)
      have b7275 := hb (x (-17) 11)
      clear * - r7273 b7274 b7275 d7256
      omega
    have d7276 : (x (-15) 1 && x (-15) 12).toNat = 0 := by
      have r7277 := hand1 (x (-15) 1) (x (-15) 12)
      have b7278 := hb (x (-15) 1)
      have b7279 := hb (x (-15) 1 && x (-15) 12)
      clear * - r7277 b7278 b7279 d7215
      omega
    have d7280 : (x (-15) 9).toNat = 0 := by
      have r7281 : (x (-15) 9).toNat ≤ (x (-15) 1).toNat := himp _ _ (hp9 (-15))
      have b7282 := hb (x (-15) 1)
      have b7283 := hb (x (-15) 9)
      clear * - r7281 b7282 b7283 d7215
      omega
    have d7284 : (x (-15) 14).toNat = 1 := by
      have r7285 : (x (-2) 1).toNat + (x (-3) 2).toNat + (x (-4) 3).toNat + (x (-5) 4).toNat + (x (-6) 5).toNat + (x (-7) 6).toNat + (x (-8) 7).toNat + (x (-9) 8).toNat + (x (-10) 9).toNat + (x (-11) 10).toNat + (x (-12) 11).toNat + (x (-13) 12).toNat + (x (-14) 13).toNat + (x (-15) 14).toNat = 3 := by have q := hcount (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7286 := hb (x (-15) 14)
      have b7287 := hb (x (-14) 13)
      have b7288 := hb (x (-13) 12)
      have b7289 := hb (x (-12) 11)
      have b7290 := hb (x (-11) 10)
      have b7291 := hb (x (-10) 9)
      have b7292 := hb (x (-9) 8)
      have b7293 := hb (x (-8) 7)
      have b7294 := hb (x (-7) 6)
      have b7295 := hb (x (-6) 5)
      have b7296 := hb (x (-5) 4)
      have b7297 := hb (x (-4) 3)
      have b7298 := hb (x (-3) 2)
      have b7299 := hb (x (-2) 1)
      clear * - r7285 b7286 b7287 b7288 b7289 b7290 b7291 b7292 b7293 b7294 b7295 b7296 b7297 b7298 b7299 d6241 d6253 d6265 d6446 d6466 d6486 d6587 d7135 d7151 d7167 d7183 d6857 d6716
      omega
    have d7300 : (x (-16) 1).toNat = 0 := by
      have r7301 : (x (-15) 14).toNat + (x (-16) 1).toNat = 1 := by have q := hd14 (-15); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7302 := hb (x (-16) 1)
      have b7303 := hb (x (-15) 14)
      clear * - r7301 b7302 b7303 d7284
      omega
    have d7304 : (x (-16) 1 && x (-16) 14).toNat = 0 := by
      have r7305 := hand1 (x (-16) 1) (x (-16) 14)
      have b7306 := hb (x (-16) 1)
      have b7307 := hb (x (-16) 1 && x (-16) 14)
      clear * - r7305 b7306 b7307 d7300
      omega
    have d7308 : (x (-17) 2).toNat = 1 := by
      have r7309 : 1 ≤ (x (-15) 13).toNat + (x (-16) 1 && x (-16) 14).toNat + (x (-17) 2).toNat := by have q := hcov13 (-15); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7310 := hb (x (-17) 2)
      have b7311 := hb (x (-15) 13)
      have b7312 := hb (x (-16) 1 && x (-16) 14)
      clear * - r7309 b7310 b7311 b7312 d7248 d7304
      omega
    have d7313 : (x (-17) 14).toNat = 1 := by
      have r7314 : (x (-17) 2).toNat ≤ (x (-17) 14).toNat := himp _ _ (hp2 (-17))
      have b7315 := hb (x (-17) 2)
      have b7316 := hb (x (-17) 14)
      clear * - r7314 b7315 b7316 d7308
      omega
    have d7317 : (x (-18) 1).toNat = 0 := by
      have r7318 : (x (-17) 14).toNat + (x (-18) 1).toNat = 1 := by have q := hd14 (-17); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7319 := hb (x (-18) 1)
      have b7320 := hb (x (-17) 14)
      clear * - r7318 b7319 b7320 d7313
      omega
    have d7321 : (x (-18) 1 && x (-18) 14).toNat = 0 := by
      have r7322 := hand1 (x (-18) 1) (x (-18) 14)
      have b7323 := hb (x (-18) 1)
      have b7324 := hb (x (-18) 1 && x (-18) 14)
      clear * - r7322 b7323 b7324 d7317
      omega
    have d7325 : (x (-19) 2).toNat = 1 := by
      have r7326 : 1 ≤ (x (-17) 13).toNat + (x (-18) 1 && x (-18) 14).toNat + (x (-19) 2).toNat := by have q := hcov13 (-17); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7327 := hb (x (-19) 2)
      have b7328 := hb (x (-17) 13)
      have b7329 := hb (x (-18) 1 && x (-18) 14)
      clear * - r7326 b7327 b7328 b7329 d7236 d7321
      omega
    have d7330 : (x (-17) 12).toNat = 0 := by
      have r7331 : (x (-17) 12).toNat + (x (-18) 1 && x (-18) 13).toNat + (x (-19) 2 && x (-19) 14).toNat + (x (-20) 3).toNat = 1 := by have q := hd12 (-17); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7332 : (x (-18) 1 && x (-18) 13).toNat = (x (-18) 13).toNat := handr _ _ (fun h => hp13 (-18) (h))
      have e7333 : (x (-19) 2 && x (-19) 14).toNat = (x (-19) 2).toNat := handl _ _ (fun h => hp2 (-19) (h))
      have b7334 := hb (x (-20) 3)
      have b7335 := hb (x (-19) 2)
      have b7336 := hb (x (-18) 13)
      have b7337 := hb (x (-17) 12)
      clear * - r7331 e7332 e7333 b7334 b7335 b7336 b7337 d7325
      omega
    have d7338 : (x (-18) 13).toNat = 0 := by
      have r7339 : (x (-17) 12).toNat + (x (-18) 1 && x (-18) 13).toNat + (x (-19) 2 && x (-19) 14).toNat + (x (-20) 3).toNat = 1 := by have q := hd12 (-17); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7340 : (x (-18) 1 && x (-18) 13).toNat = (x (-18) 13).toNat := handr _ _ (fun h => hp13 (-18) (h))
      have e7341 : (x (-19) 2 && x (-19) 14).toNat = (x (-19) 2).toNat := handl _ _ (fun h => hp2 (-19) (h))
      have b7342 := hb (x (-20) 3)
      have b7343 := hb (x (-19) 2)
      have b7344 := hb (x (-18) 13)
      have b7345 := hb (x (-17) 12)
      clear * - r7339 e7340 e7341 b7342 b7343 b7344 b7345 d7330 d7325
      omega
    have d7346 : (x (-18) 4 && x (-18) 13).toNat = 0 := by
      have r7347 := hand2 (x (-18) 4) (x (-18) 13)
      have b7348 := hb (x (-18) 13)
      have b7349 := hb (x (-18) 4 && x (-18) 13)
      clear * - r7347 b7348 b7349 d7338
      omega
    have d7350 : (x (-15) 12).toNat = 0 := by
      have r7351 : (x (-15) 12).toNat + (x (-16) 1 && x (-16) 13).toNat + (x (-17) 2 && x (-17) 14).toNat + (x (-18) 3).toNat = 1 := by have q := hd12 (-15); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7352 : (x (-16) 1 && x (-16) 13).toNat = (x (-16) 13).toNat := handr _ _ (fun h => hp13 (-16) (h))
      have e7353 : (x (-17) 2 && x (-17) 14).toNat = (x (-17) 2).toNat := handl _ _ (fun h => hp2 (-17) (h))
      have b7354 := hb (x (-18) 3)
      have b7355 := hb (x (-17) 2)
      have b7356 := hb (x (-16) 13)
      have b7357 := hb (x (-15) 12)
      clear * - r7351 e7352 e7353 b7354 b7355 b7356 b7357 d7308
      omega
    have d7358 : (x (-16) 13).toNat = 0 := by
      have r7359 : (x (-15) 12).toNat + (x (-16) 1 && x (-16) 13).toNat + (x (-17) 2 && x (-17) 14).toNat + (x (-18) 3).toNat = 1 := by have q := hd12 (-15); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7360 : (x (-16) 1 && x (-16) 13).toNat = (x (-16) 13).toNat := handr _ _ (fun h => hp13 (-16) (h))
      have e7361 : (x (-17) 2 && x (-17) 14).toNat = (x (-17) 2).toNat := handl _ _ (fun h => hp2 (-17) (h))
      have b7362 := hb (x (-18) 3)
      have b7363 := hb (x (-17) 2)
      have b7364 := hb (x (-16) 13)
      have b7365 := hb (x (-15) 12)
      clear * - r7359 e7360 e7361 b7362 b7363 b7364 b7365 d7350 d7308
      omega
    have d7366 : (x (-16) 2 && x (-16) 13).toNat = 0 := by
      have r7367 := hand2 (x (-16) 2) (x (-16) 13)
      have b7368 := hb (x (-16) 13)
      have b7369 := hb (x (-16) 2 && x (-16) 13)
      clear * - r7367 b7368 b7369 d7358
      omega
    have d7370 : (x (-18) 4).toNat = 1 := by
      have r7371 : 1 ≤ (x (-14) 11).toNat + (x (-15) 1 && x (-15) 12).toNat + (x (-16) 2 && x (-16) 13).toNat + (x (-17) 3 && x (-17) 14).toNat + (x (-18) 4).toNat := by have q := hcov11 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7372 := hb (x (-18) 4)
      have b7373 := hb (x (-14) 11)
      have b7374 := hb (x (-15) 1 && x (-15) 12)
      have b7375 := hb (x (-16) 2 && x (-16) 13)
      have b7376 := hb (x (-17) 3 && x (-17) 14)
      clear * - r7371 b7372 b7373 b7374 b7375 b7376 d7119 d7276 d7366 d7264
      omega
    have d7377 : (x (-14) 8).toNat = 0 := by
      have r7378 : (x (-14) 8).toNat + (x (-15) 1 && x (-15) 9).toNat + (x (-16) 2 && x (-16) 10).toNat + (x (-17) 3 && x (-17) 11).toNat + (x (-18) 4 && x (-18) 12).toNat + (x (-19) 5 && x (-19) 13).toNat + (x (-20) 6 && x (-20) 14).toNat + (x (-21) 7).toNat = 1 := by have q := hd8 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7379 : (x (-15) 1 && x (-15) 9).toNat = (x (-15) 9).toNat := handr _ _ (fun h => hp9 (-15) (h))
      have e7380 : (x (-16) 2 && x (-16) 10).toNat = (x (-16) 10).toNat := handr _ _ (fun h => hp10 (-16) (h))
      have e7381 : (x (-17) 3 && x (-17) 11).toNat = (x (-17) 11).toNat := handr _ _ (fun h => hp11 (-17) (h))
      have e7382 : (x (-18) 4 && x (-18) 12).toNat = (x (-18) 4).toNat := handl _ _ (fun h => hp4 (-18) (h))
      have e7383 : (x (-19) 5 && x (-19) 13).toNat = (x (-19) 5).toNat := handl _ _ (fun h => hp5 (-19) (h))
      have e7384 : (x (-20) 6 && x (-20) 14).toNat = (x (-20) 6).toNat := handl _ _ (fun h => hp6 (-20) (h))
      have b7385 := hb (x (-21) 7)
      have b7386 := hb (x (-20) 6)
      have b7387 := hb (x (-19) 5)
      have b7388 := hb (x (-18) 4)
      have b7389 := hb (x (-17) 11)
      have b7390 := hb (x (-16) 10)
      have b7391 := hb (x (-15) 9)
      have b7392 := hb (x (-14) 8)
      clear * - r7378 e7379 e7380 e7381 e7382 e7383 e7384 b7385 b7386 b7387 b7388 b7389 b7390 b7391 b7392 d7280 d7272 d7370
      omega
    have d7393 : (x (-16) 10).toNat = 0 := by
      have r7394 : (x (-14) 8).toNat + (x (-15) 1 && x (-15) 9).toNat + (x (-16) 2 && x (-16) 10).toNat + (x (-17) 3 && x (-17) 11).toNat + (x (-18) 4 && x (-18) 12).toNat + (x (-19) 5 && x (-19) 13).toNat + (x (-20) 6 && x (-20) 14).toNat + (x (-21) 7).toNat = 1 := by have q := hd8 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7395 : (x (-15) 1 && x (-15) 9).toNat = (x (-15) 9).toNat := handr _ _ (fun h => hp9 (-15) (h))
      have e7396 : (x (-16) 2 && x (-16) 10).toNat = (x (-16) 10).toNat := handr _ _ (fun h => hp10 (-16) (h))
      have e7397 : (x (-17) 3 && x (-17) 11).toNat = (x (-17) 11).toNat := handr _ _ (fun h => hp11 (-17) (h))
      have e7398 : (x (-18) 4 && x (-18) 12).toNat = (x (-18) 4).toNat := handl _ _ (fun h => hp4 (-18) (h))
      have e7399 : (x (-19) 5 && x (-19) 13).toNat = (x (-19) 5).toNat := handl _ _ (fun h => hp5 (-19) (h))
      have e7400 : (x (-20) 6 && x (-20) 14).toNat = (x (-20) 6).toNat := handl _ _ (fun h => hp6 (-20) (h))
      have b7401 := hb (x (-21) 7)
      have b7402 := hb (x (-20) 6)
      have b7403 := hb (x (-19) 5)
      have b7404 := hb (x (-18) 4)
      have b7405 := hb (x (-17) 11)
      have b7406 := hb (x (-16) 10)
      have b7407 := hb (x (-15) 9)
      have b7408 := hb (x (-14) 8)
      clear * - r7394 e7395 e7396 e7397 e7398 e7399 e7400 b7401 b7402 b7403 b7404 b7405 b7406 b7407 b7408 d7377 d7280 d7272 d7370
      omega
    have d7409 : (x (-19) 5).toNat = 0 := by
      have r7410 : (x (-14) 8).toNat + (x (-15) 1 && x (-15) 9).toNat + (x (-16) 2 && x (-16) 10).toNat + (x (-17) 3 && x (-17) 11).toNat + (x (-18) 4 && x (-18) 12).toNat + (x (-19) 5 && x (-19) 13).toNat + (x (-20) 6 && x (-20) 14).toNat + (x (-21) 7).toNat = 1 := by have q := hd8 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7411 : (x (-15) 1 && x (-15) 9).toNat = (x (-15) 9).toNat := handr _ _ (fun h => hp9 (-15) (h))
      have e7412 : (x (-16) 2 && x (-16) 10).toNat = (x (-16) 10).toNat := handr _ _ (fun h => hp10 (-16) (h))
      have e7413 : (x (-17) 3 && x (-17) 11).toNat = (x (-17) 11).toNat := handr _ _ (fun h => hp11 (-17) (h))
      have e7414 : (x (-18) 4 && x (-18) 12).toNat = (x (-18) 4).toNat := handl _ _ (fun h => hp4 (-18) (h))
      have e7415 : (x (-19) 5 && x (-19) 13).toNat = (x (-19) 5).toNat := handl _ _ (fun h => hp5 (-19) (h))
      have e7416 : (x (-20) 6 && x (-20) 14).toNat = (x (-20) 6).toNat := handl _ _ (fun h => hp6 (-20) (h))
      have b7417 := hb (x (-21) 7)
      have b7418 := hb (x (-20) 6)
      have b7419 := hb (x (-19) 5)
      have b7420 := hb (x (-18) 4)
      have b7421 := hb (x (-17) 11)
      have b7422 := hb (x (-16) 10)
      have b7423 := hb (x (-15) 9)
      have b7424 := hb (x (-14) 8)
      clear * - r7410 e7411 e7412 e7413 e7414 e7415 e7416 b7417 b7418 b7419 b7420 b7421 b7422 b7423 b7424 d7377 d7280 d7393 d7272 d7370
      omega
    have d7425 : (x (-19) 5 && x (-19) 14).toNat = 0 := by
      have r7426 := hand1 (x (-19) 5) (x (-19) 14)
      have b7427 := hb (x (-19) 5)
      have b7428 := hb (x (-19) 5 && x (-19) 14)
      clear * - r7426 b7427 b7428 d7409
      omega
    have d7429 : (x (-20) 6).toNat = 1 := by
      have r7430 : 1 ≤ (x (-14) 9).toNat + (x (-15) 1 && x (-15) 10).toNat + (x (-16) 2 && x (-16) 11).toNat + (x (-17) 3 && x (-17) 12).toNat + (x (-18) 4 && x (-18) 13).toNat + (x (-19) 5 && x (-19) 14).toNat + (x (-20) 6).toNat := by have q := hcov9 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7431 := hb (x (-20) 6)
      have b7432 := hb (x (-14) 9)
      have b7433 := hb (x (-15) 1 && x (-15) 10)
      have b7434 := hb (x (-16) 2 && x (-16) 11)
      have b7435 := hb (x (-17) 3 && x (-17) 12)
      have b7436 := hb (x (-18) 4 && x (-18) 13)
      have b7437 := hb (x (-19) 5 && x (-19) 14)
      clear * - r7430 b7431 b7432 b7433 b7434 b7435 b7436 b7437 d6724 d6877 d7027 d7268 d7346 d7425
      omega
    have r7438 : (x (-14) 8).toNat + (x (-15) 1 && x (-15) 9).toNat + (x (-16) 2 && x (-16) 10).toNat + (x (-17) 3 && x (-17) 11).toNat + (x (-18) 4 && x (-18) 12).toNat + (x (-19) 5 && x (-19) 13).toNat + (x (-20) 6 && x (-20) 14).toNat + (x (-21) 7).toNat = 1 := by have q := hd8 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7439 : (x (-15) 1 && x (-15) 9).toNat = (x (-15) 9).toNat := handr _ _ (fun h => hp9 (-15) (h))
    have e7440 : (x (-16) 2 && x (-16) 10).toNat = (x (-16) 10).toNat := handr _ _ (fun h => hp10 (-16) (h))
    have e7441 : (x (-17) 3 && x (-17) 11).toNat = (x (-17) 11).toNat := handr _ _ (fun h => hp11 (-17) (h))
    have e7442 : (x (-18) 4 && x (-18) 12).toNat = (x (-18) 4).toNat := handl _ _ (fun h => hp4 (-18) (h))
    have e7443 : (x (-19) 5 && x (-19) 13).toNat = (x (-19) 5).toNat := handl _ _ (fun h => hp5 (-19) (h))
    have e7444 : (x (-20) 6 && x (-20) 14).toNat = (x (-20) 6).toNat := handl _ _ (fun h => hp6 (-20) (h))
    have b7445 := hb (x (-21) 7)
    have b7446 := hb (x (-20) 6)
    have b7447 := hb (x (-19) 5)
    have b7448 := hb (x (-18) 4)
    have b7449 := hb (x (-17) 11)
    have b7450 := hb (x (-16) 10)
    have b7451 := hb (x (-15) 9)
    have b7452 := hb (x (-14) 8)
    linarith only [r7438, e7439, e7440, e7441, e7442, e7443, e7444, b7445, b7446, b7447, b7448, b7449, b7450, b7451, b7452, d7377, d7280, d7393, d7272, d7370, d7409, d7429]

theorem cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a0001000 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 3).toNat = 0)
    (g1 : (x (-3) 5).toNat = 0)
    (g2 : (x (-3) 9).toNat = 0)
    (g3 : (x (-3) 11).toNat = 0)
    (g4 : (x (-3) 13).toNat = 0)
    (g5 : (x (-2) 2).toNat = 1)
    (g6 : (x (-1) 1).toNat = 0)
    (g7 : (x (-1) 3).toNat = 0)
    (g8 : (x (-1) 5).toNat = 0)
    (g9 : (x (-1) 9).toNat = 0)
    (g10 : (x (-1) 11).toNat = 0)
    (g11 : (x (-1) 13).toNat = 0)
    (g12 : (x 0 1).toNat = 1)
    (g13 : (x 0 2).toNat = 1)
    (g14 : (x 0 4).toNat = 0)
    (g15 : (x 0 5).toNat = 0)
    (g16 : (x 0 6).toNat = 0)
    (g17 : (x 0 7).toNat = 0)
    (g18 : (x 0 8).toNat = 0)
    (g19 : (x 0 9).toNat = 0)
    (g20 : (x 0 10).toNat = 0)
    (g21 : (x 0 11).toNat = 0)
    (g22 : (x 0 13).toNat = 0)
    (g23 : (x 0 14).toNat = 1)
    (g24 : (x 1 2).toNat = 0)
    (g25 : (x 1 5).toNat = 0)
    (g26 : (x 1 6).toNat = 0)
    (g27 : (x 1 10).toNat = 0)
    (g28 : (x 1 13).toNat = 0)
    (g29 : (x 2 4).toNat = 0)
    (g30 : (x 2 12).toNat = 0)
    (g31 : (x 0 1 && x 0 4).toNat = 0)
    (g32 : (x (-1) 2 && x (-1) 5).toNat = 0)
    (g33 : (x 0 2 && x 0 5).toNat = 0)
    (g34 : (x (-1) 3 && x (-1) 6).toNat = 0)
    (g35 : (x (-3) 5 && x (-3) 8).toNat = 0)
    (g36 : (x 2 4 && x 2 8).toNat = 0)
    (g37 : (x 1 5 && x 1 9).toNat = 0)
    (g38 : (x 0 6 && x 0 10).toNat = 0)
    (g39 : (x (-1) 7 && x (-1) 11).toNat = 0)
    (g40 : (x (-3) 9 && x (-3) 13).toNat = 0)
    (g41 : (x 0 1 && x 0 6).toNat = 0)
    (g42 : (x (-3) 4 && x (-3) 9).toNat = 0)
    (g43 : (x 1 1 && x 1 6).toNat = 0)
    (g44 : (x 0 2 && x 0 7).toNat = 0)
    (g45 : (x (-1) 3 && x (-1) 8).toNat = 0)
    (g46 : (x (-3) 5 && x (-3) 10).toNat = 0)
    (g47 : (x 0 1 && x 0 7).toNat = 0)
    (g48 : (x 2 6 && x 2 12).toNat = 0)
    (g49 : (x 1 7 && x 1 13).toNat = 0)
    (g50 : (x 0 8 && x 0 14).toNat = 0)
    (g51 : (x 0 2 && x 0 9).toNat = 0)
    (g52 : (x (-1) 3 && x (-1) 10).toNat = 0)
    (g53 : (x (-3) 5 && x (-3) 12).toNat = 0)
    (g54 : (x 1 7 && x 1 14).toNat = 0)
    (g55 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g56 : (x 0 4 && x 0 13).toNat = 0)
    (g57 : (x (-1) 5 && x (-1) 14).toNat = 0)
    (g58 : (x 0 1 && x 0 11).toNat = 0)
    (g59 : (x 0 2 && x 0 12).toNat = 0)
    (g60 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g61 : (x 1 2 && x 1 12).toNat = 0)
    (g62 : (x 0 3 && x 0 13).toNat = 0)
    (g63 : (x 2 2 && x 2 12).toNat = 0)
    (g64 : (x 1 3 && x 1 13).toNat = 0)
    (g65 : (x 0 4 && x 0 14).toNat = 0)
    (g66 : (x (-3) 1 && x (-3) 12).toNat = 0)
    (g67 : (x (-3) 2 && x (-3) 13).toNat = 0)
    (g68 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g69 : (x (-3) 3 && x (-3) 14).toNat = 0)
    (g70 : (x 0 1 && x 0 12).toNat = 0)
    (g71 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g72 : (x 0 2 && x 0 13).toNat = 0)
    (g73 : (x (-1) 3 && x (-1) 14).toNat = 0)
    (g74 : (x 2 1 && x 2 12).toNat = 0)
    (g75 : (x 1 2 && x 1 13).toNat = 0)
    (g76 : (x 0 3 && x 0 14).toNat = 0)
    (g77 : (x 1 3 && x 1 14).toNat = 0)
    (g78 : (x (-3) 1 && x (-3) 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a0001000_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78
