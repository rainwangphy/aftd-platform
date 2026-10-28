import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b00001

Topic: combinatorics   Node: c07e44f97d20

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_six_iff_seven_core: under the layer-free tight-cover constraints for k = 15 and 4 fixed bits of the class-type sequence near position 0, the constraints are contradictory. Its module also proves the sibling branches cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b0000001, cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b000001.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b0000001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 2).toNat = 0)
    (g1 : (x 0 3).toNat = 0)
    (g2 : (x 0 4).toNat = 0)
    (g3 : (x 0 5).toNat = 0)
    (g4 : (x 0 6).toNat = 0)
    (g5 : (x 0 7).toNat = 1)
    (g6 : (x 0 8).toNat = 0)
    (g7 : (x 0 9).toNat = 0)
    (g8 : (x 0 10).toNat = 0)
    (g9 : (x 0 11).toNat = 0)
    (g10 : (x 0 12).toNat = 0)
    (g11 : (x 0 13).toNat = 0)
    (g12 : (x 0 14).toNat = 0)
    (g13 : (x 1 1).toNat = 1)
    (g14 : (x 1 6).toNat = 0)
    (g15 : (x 1 14).toNat = 1)
    (g16 : (x 2 5).toNat = 0)
    (g17 : (x 3 4).toNat = 0)
    (g18 : (x 4 11).toNat = 0)
    (g19 : (x 5 10).toNat = 0)
    (g20 : (x 6 9).toNat = 0)
    (g21 : (x 7 8).toNat = 0)
    (g22 : (x 7 8 && x 7 10).toNat = 0)
    (g23 : (x 6 9 && x 6 11).toNat = 0)
    (g24 : (x 5 10 && x 5 12).toNat = 0)
    (g25 : (x 4 11 && x 4 13).toNat = 0)
    (g26 : (x 1 2 && x 1 6).toNat = 0)
    (g27 : (x 0 3 && x 0 7).toNat = 0)
    (g28 : (x 0 4 && x 0 8).toNat = 0)
    (g29 : (x 0 6 && x 0 10).toNat = 0)
    (g30 : (x 7 4 && x 7 8).toNat = 0)
    (g31 : (x 6 5 && x 6 9).toNat = 0)
    (g32 : (x 5 6 && x 5 10).toNat = 0)
    (g33 : (x 4 7 && x 4 11).toNat = 0)
    (g34 : (x 1 1 && x 1 6).toNat = 0)
    (g35 : (x 0 2 && x 0 7).toNat = 0)
    (g36 : (x 7 3 && x 7 8).toNat = 0)
    (g37 : (x 6 4 && x 6 9).toNat = 0)
    (g38 : (x 5 5 && x 5 10).toNat = 0)
    (g39 : (x 4 6 && x 4 11).toNat = 0)
    (g40 : (x 0 5 && x 0 11).toNat = 0)
    (g41 : (x 0 3 && x 0 10).toNat = 0)
    (g42 : (x 3 4 && x 3 11).toNat = 0)
    (g43 : (x 2 5 && x 2 12).toNat = 0)
    (g44 : (x 1 6 && x 1 13).toNat = 0)
    (g45 : (x 0 7 && x 0 14).toNat = 0)
    (g46 : (x 7 1 && x 7 8).toNat = 0)
    (g47 : (x 6 2 && x 6 9).toNat = 0)
    (g48 : (x 5 3 && x 5 10).toNat = 0)
    (g49 : (x 4 4 && x 4 11).toNat = 0)
    (g50 : (x 0 2 && x 0 11).toNat = 0)
    (g51 : (x 0 3 && x 0 12).toNat = 0)
    (g52 : (x 5 1 && x 5 10).toNat = 0)
    (g53 : (x 4 2 && x 4 11).toNat = 0)
    (g54 : (x 3 4 && x 3 13).toNat = 0)
    (g55 : (x 2 5 && x 2 14).toNat = 0)
    (g56 : (x 0 2 && x 0 12).toNat = 0)
    (g57 : (x 4 1 && x 4 11).toNat = 0)
    (g58 : (x 3 4 && x 3 14).toNat = 0)
    (g59 : (x 0 1 && x 0 12).toNat = 0)
    (g60 : (x 0 3 && x 0 14).toNat = 0)
    (g61 : (x 0 1 && x 0 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d2668 : (x 2 14).toNat = 0 := by
    have r2669 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2670 := hb (x 1 1)
    have b2671 := hb (x 2 14)
    clear * - r2669 b2670 b2671 g13
    omega
  have d2672 : (x 2 1 && x 2 14).toNat = 0 := by
    have r2673 := hand2 (x 2 1) (x 2 14)
    have b2674 := hb (x 2 14)
    have b2675 := hb (x 2 1 && x 2 14)
    clear * - r2673 b2674 b2675 d2668
    omega
  have d2676 : (x 2 6).toNat = 0 := by
    have r2677 : (x 2 6).toNat ≤ (x 2 14).toNat := himp _ _ (hp6 2)
    have b2678 := hb (x 2 6)
    have b2679 := hb (x 2 14)
    clear * - r2677 b2678 b2679 d2668
    omega
  have d2680 : (x 2 6 && x 2 13).toNat = 0 := by
    have r2681 := hand1 (x 2 6) (x 2 13)
    have b2682 := hb (x 2 6)
    have b2683 := hb (x 2 6 && x 2 13)
    clear * - r2681 b2682 b2683 d2676
    omega
  have d2684 : (x 2 2 && x 2 6).toNat = 0 := by
    have r2685 := hand2 (x 2 2) (x 2 6)
    have b2686 := hb (x 2 6)
    have b2687 := hb (x 2 2 && x 2 6)
    clear * - r2685 b2686 b2687 d2676
    omega
  have d2688 : (x 2 2).toNat = 0 := by
    have r2689 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
    have b2690 := hb (x 2 2)
    have b2691 := hb (x 2 14)
    clear * - r2689 b2690 b2691 d2668
    omega
  have d2692 : (x 2 2 && x 2 13).toNat = 0 := by
    have r2693 := hand1 (x 2 2) (x 2 13)
    have b2694 := hb (x 2 2)
    have b2695 := hb (x 2 2 && x 2 13)
    clear * - r2693 b2694 b2695 d2688
    omega
  have d2696 : (x 2 10).toNat = 0 := by
    have r2697 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
    have b2698 := hb (x 2 2)
    have b2699 := hb (x 2 10)
    clear * - r2697 b2698 b2699 d2688
    omega
  have d2700 : (x 2 1 && x 2 10).toNat = 0 := by
    have r2701 := hand2 (x 2 1) (x 2 10)
    have b2702 := hb (x 2 10)
    have b2703 := hb (x 2 1 && x 2 10)
    clear * - r2701 b2702 b2703 d2696
    omega
  cases h2704 : x (-1) 2
  · have f2705 : (x (-1) 2).toNat = 0 := by rw [h2704]; rfl
    have d2706 : (x (-1) 2 && x (-1) 13).toNat = 0 := by
      have r2707 := hand1 (x (-1) 2) (x (-1) 13)
      have b2708 := hb (x (-1) 2)
      have b2709 := hb (x (-1) 2 && x (-1) 13)
      clear * - r2707 b2708 b2709 f2705
      omega
    have d2710 : (x (-1) 10).toNat = 0 := by
      have r2711 : (x (-1) 10).toNat ≤ (x (-1) 2).toNat := himp _ _ (hp10 (-1))
      have b2712 := hb (x (-1) 2)
      have b2713 := hb (x (-1) 10)
      clear * - r2711 b2712 b2713 f2705
      omega
    have d2714 : (x (-1) 1 && x (-1) 10).toNat = 0 := by
      have r2715 := hand2 (x (-1) 1) (x (-1) 10)
      have b2716 := hb (x (-1) 10)
      have b2717 := hb (x (-1) 1 && x (-1) 10)
      clear * - r2715 b2716 b2717 d2710
      omega
    have d2718 : (x 1 13).toNat = 1 := by
      have r2719 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2720 := hb (x (-1) 2)
      have b2721 := hb (x 1 13)
      have b2722 := hb (x 0 1 && x 0 14)
      clear * - r2719 b2720 b2721 b2722 g61 f2705
      omega
    have d2723 : (x 2 12).toNat = 0 := by
      have r2724 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2725 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e2726 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b2727 := hb (x (-1) 3)
      have b2728 := hb (x 0 2)
      have b2729 := hb (x 1 13)
      have b2730 := hb (x 2 12)
      clear * - r2724 e2725 e2726 b2727 b2728 b2729 b2730 d2718 g0
      omega
    have d2731 : (x 2 1 && x 2 12).toNat = 0 := by
      have r2732 := hand2 (x 2 1) (x 2 12)
      have b2733 := hb (x 2 12)
      have b2734 := hb (x 2 1 && x 2 12)
      clear * - r2732 b2733 b2734 d2723
      omega
    have d2735 : (x 2 4).toNat = 0 := by
      have r2736 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
      have b2737 := hb (x 2 4)
      have b2738 := hb (x 2 12)
      clear * - r2736 b2737 b2738 d2723
      omega
    have d2739 : (x 2 4 && x 2 13).toNat = 0 := by
      have r2740 := hand1 (x 2 4) (x 2 13)
      have b2741 := hb (x 2 4)
      have b2742 := hb (x 2 4 && x 2 13)
      clear * - r2740 b2741 b2742 d2735
      omega
    have d2743 : (x 2 4 && x 2 8).toNat = 0 := by
      have r2744 := hand1 (x 2 4) (x 2 8)
      have b2745 := hb (x 2 4)
      have b2746 := hb (x 2 4 && x 2 8)
      clear * - r2744 b2745 b2746 d2735
      omega
    have d2747 : (x (-1) 3).toNat = 0 := by
      have r2748 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2749 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e2750 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b2751 := hb (x (-1) 3)
      have b2752 := hb (x 0 2)
      have b2753 := hb (x 1 13)
      have b2754 := hb (x 2 12)
      clear * - r2748 e2749 e2750 b2751 b2752 b2753 b2754 d2723 d2718 g0
      omega
    have d2755 : (x (-1) 3 && x (-1) 13).toNat = 0 := by
      have r2756 := hand1 (x (-1) 3) (x (-1) 13)
      have b2757 := hb (x (-1) 3)
      have b2758 := hb (x (-1) 3 && x (-1) 13)
      clear * - r2756 b2757 b2758 d2747
      omega
    have d2759 : (x (-1) 3 && x (-1) 12).toNat = 0 := by
      have r2760 := hand1 (x (-1) 3) (x (-1) 12)
      have b2761 := hb (x (-1) 3)
      have b2762 := hb (x (-1) 3 && x (-1) 12)
      clear * - r2760 b2761 b2762 d2747
      omega
    have d2763 : (x (-1) 3 && x (-1) 8).toNat = 0 := by
      have r2764 := hand1 (x (-1) 3) (x (-1) 8)
      have b2765 := hb (x (-1) 3)
      have b2766 := hb (x (-1) 3 && x (-1) 8)
      clear * - r2764 b2765 b2766 d2747
      omega
    have d2767 : (x (-1) 11).toNat = 0 := by
      have r2768 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
      have b2769 := hb (x (-1) 3)
      have b2770 := hb (x (-1) 11)
      clear * - r2768 b2769 b2770 d2747
      omega
    have d2771 : (x (-1) 4 && x (-1) 11).toNat = 0 := by
      have r2772 := hand2 (x (-1) 4) (x (-1) 11)
      have b2773 := hb (x (-1) 11)
      have b2774 := hb (x (-1) 4 && x (-1) 11)
      clear * - r2772 b2773 b2774 d2767
      omega
    have d2775 : (x (-1) 7 && x (-1) 11).toNat = 0 := by
      have r2776 := hand2 (x (-1) 7) (x (-1) 11)
      have b2777 := hb (x (-1) 11)
      have b2778 := hb (x (-1) 7 && x (-1) 11)
      clear * - r2776 b2777 b2778 d2767
      omega
    cases h2779 : x 1 2
    · have f2780 : (x 1 2).toNat = 0 := by rw [h2779]; rfl
      have d2781 : (x 1 2 && x 1 13).toNat = 0 := by
        have r2782 := hand1 (x 1 2) (x 1 13)
        have b2783 := hb (x 1 2)
        have b2784 := hb (x 1 2 && x 1 13)
        clear * - r2782 b2783 b2784 f2780
        omega
      have d2785 : (x 1 2 && x 1 9).toNat = 0 := by
        have r2786 := hand1 (x 1 2) (x 1 9)
        have b2787 := hb (x 1 2)
        have b2788 := hb (x 1 2 && x 1 9)
        clear * - r2786 b2787 b2788 f2780
        omega
      have d2789 : (x 1 10).toNat = 0 := by
        have r2790 : (x 1 10).toNat ≤ (x 1 2).toNat := himp _ _ (hp10 1)
        have b2791 := hb (x 1 2)
        have b2792 := hb (x 1 10)
        clear * - r2790 b2791 b2792 f2780
        omega
      have d2793 : (x 1 1 && x 1 10).toNat = 0 := by
        have r2794 := hand2 (x 1 1) (x 1 10)
        have b2795 := hb (x 1 10)
        have b2796 := hb (x 1 1 && x 1 10)
        clear * - r2794 b2795 b2796 d2789
        omega
      have d2797 : (x 3 13).toNat = 1 := by
        have r2798 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b2799 := hb (x 1 2)
        have b2800 := hb (x 3 13)
        have b2801 := hb (x 2 1 && x 2 14)
        clear * - r2798 b2799 b2800 b2801 d2672 f2780
        omega
      have d2802 : (x 3 1).toNat = 1 := by
        have r2803 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
        have b2804 := hb (x 3 1)
        have b2805 := hb (x 3 13)
        clear * - r2803 b2804 b2805 d2797
        omega
      have d2806 : (x 4 14).toNat = 0 := by
        have r2807 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b2808 := hb (x 3 1)
        have b2809 := hb (x 4 14)
        clear * - r2807 b2808 b2809 d2802
        omega
      have d2810 : (x 4 3 && x 4 14).toNat = 0 := by
        have r2811 := hand2 (x 4 3) (x 4 14)
        have b2812 := hb (x 4 14)
        have b2813 := hb (x 4 3 && x 4 14)
        clear * - r2811 b2812 b2813 d2806
        omega
      have d2814 : (x 4 6).toNat = 0 := by
        have r2815 : (x 4 6).toNat ≤ (x 4 14).toNat := himp _ _ (hp6 4)
        have b2816 := hb (x 4 6)
        have b2817 := hb (x 4 14)
        clear * - r2815 b2816 b2817 d2806
        omega
      have d2818 : (x 4 2 && x 4 6).toNat = 0 := by
        have r2819 := hand2 (x 4 2) (x 4 6)
        have b2820 := hb (x 4 6)
        have b2821 := hb (x 4 2 && x 4 6)
        clear * - r2819 b2820 b2821 d2814
        omega
      have d2822 : (x 4 2).toNat = 0 := by
        have r2823 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
        have b2824 := hb (x 4 2)
        have b2825 := hb (x 4 14)
        clear * - r2823 b2824 b2825 d2806
        omega
      have d2826 : (x 4 12).toNat = 0 := by
        have r2827 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e2828 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e2829 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b2830 := hb (x 1 3)
        have b2831 := hb (x 2 2)
        have b2832 := hb (x 3 13)
        have b2833 := hb (x 4 12)
        clear * - r2827 e2828 e2829 b2830 b2831 b2832 b2833 d2797 d2688
        omega
      have d2834 : (x 4 3 && x 4 12).toNat = 0 := by
        have r2835 := hand2 (x 4 3) (x 4 12)
        have b2836 := hb (x 4 12)
        have b2837 := hb (x 4 3 && x 4 12)
        clear * - r2835 b2836 b2837 d2826
        omega
      have d2838 : (x 4 4).toNat = 0 := by
        have r2839 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
        have b2840 := hb (x 4 4)
        have b2841 := hb (x 4 12)
        clear * - r2839 b2840 b2841 d2826
        omega
      have d2842 : (x 1 3).toNat = 0 := by
        have r2843 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e2844 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e2845 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b2846 := hb (x 1 3)
        have b2847 := hb (x 2 2)
        have b2848 := hb (x 3 13)
        have b2849 := hb (x 4 12)
        clear * - r2843 e2844 e2845 b2846 b2847 b2848 b2849 d2826 d2797 d2688
        omega
      have d2850 : (x 1 3 && x 1 14).toNat = 0 := by
        have r2851 := hand1 (x 1 3) (x 1 14)
        have b2852 := hb (x 1 3)
        have b2853 := hb (x 1 3 && x 1 14)
        clear * - r2851 b2852 b2853 d2842
        omega
      have d2854 : (x 1 11).toNat = 0 := by
        have r2855 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
        have b2856 := hb (x 1 3)
        have b2857 := hb (x 1 11)
        clear * - r2855 b2856 b2857 d2842
        omega
      have d2858 : (x 1 1 && x 1 11).toNat = 0 := by
        have r2859 := hand2 (x 1 1) (x 1 11)
        have b2860 := hb (x 1 11)
        have b2861 := hb (x 1 1 && x 1 11)
        clear * - r2859 b2860 b2861 d2854
        omega
      have d2862 : (x 3 1 && x 3 12).toNat = 1 := by
        have r2863 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b2864 := hb (x 0 4)
        have b2865 := hb (x 4 11)
        have b2866 := hb (x 3 1 && x 3 12)
        have b2867 := hb (x 2 2 && x 2 13)
        have b2868 := hb (x 1 3 && x 1 14)
        clear * - r2863 b2864 b2865 b2866 b2867 b2868 g18 d2692 d2850 g2
        omega
      have d2869 : (x 3 12).toNat = 1 := by
        have r2870 := hand2 (x 3 1) (x 3 12)
        have b2871 := hb (x 3 12)
        have b2872 := hb (x 3 1 && x 3 12)
        clear * - r2870 b2871 b2872 d2862
        omega
      have d2873 : (x 2 13).toNat = 0 := by
        have r2874 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e2875 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
        have e2876 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
        have b2877 := hb (x 0 3)
        have b2878 := hb (x 1 2)
        have b2879 := hb (x 2 13)
        have b2880 := hb (x 3 12)
        clear * - r2874 e2875 e2876 b2877 b2878 b2879 b2880 d2869 f2780 g1
        omega
      have d2881 : (x 2 8 && x 2 13).toNat = 0 := by
        have r2882 := hand2 (x 2 8) (x 2 13)
        have b2883 := hb (x 2 13)
        have b2884 := hb (x 2 8 && x 2 13)
        clear * - r2882 b2883 b2884 d2873
        omega
      cases h2885 : x (-1) 4
      · have f2886 : (x (-1) 4).toNat = 0 := by rw [h2885]; rfl
        have d2887 : (x 3 11).toNat = 1 := by
          have r2888 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2889 := hb (x (-1) 4)
          have b2890 := hb (x 3 11)
          have b2891 := hb (x 2 1 && x 2 12)
          have b2892 := hb (x 1 2 && x 1 13)
          have b2893 := hb (x 0 3 && x 0 14)
          clear * - r2888 b2889 b2890 b2891 b2892 b2893 d2731 d2781 g60 f2886
          omega
        have d2894 : (x 3 3).toNat = 1 := by
          have r2895 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
          have b2896 := hb (x 3 3)
          have b2897 := hb (x 3 11)
          clear * - r2895 b2896 b2897 d2887
          omega
        have d2898 : (x 6 12).toNat = 0 := by
          have r2899 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e2900 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e2901 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b2902 := hb (x 3 3)
          have b2903 := hb (x 4 2)
          have b2904 := hb (x 5 13)
          have b2905 := hb (x 6 12)
          clear * - r2899 e2900 e2901 b2902 b2903 b2904 b2905 d2822 d2894
          omega
        have d2906 : (x 6 1 && x 6 12).toNat = 0 := by
          have r2907 := hand2 (x 6 1) (x 6 12)
          have b2908 := hb (x 6 12)
          have b2909 := hb (x 6 1 && x 6 12)
          clear * - r2907 b2908 b2909 d2898
          omega
        have d2910 : (x 6 4).toNat = 0 := by
          have r2911 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
          have b2912 := hb (x 6 4)
          have b2913 := hb (x 6 12)
          clear * - r2911 b2912 b2913 d2898
          omega
        have d2914 : (x 5 13).toNat = 0 := by
          have r2915 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e2916 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e2917 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b2918 := hb (x 3 3)
          have b2919 := hb (x 4 2)
          have b2920 := hb (x 5 13)
          have b2921 := hb (x 6 12)
          clear * - r2915 e2916 e2917 b2918 b2919 b2920 b2921 d2898 d2822 d2894
          omega
        have d2922 : (x 5 2 && x 5 13).toNat = 0 := by
          have r2923 := hand2 (x 5 2) (x 5 13)
          have b2924 := hb (x 5 13)
          have b2925 := hb (x 5 2 && x 5 13)
          clear * - r2923 b2924 b2925 d2914
          omega
        have d2926 : (x 7 11).toNat = 1 := by
          have r2927 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2928 := hb (x 3 4)
          have b2929 := hb (x 7 11)
          have b2930 := hb (x 6 1 && x 6 12)
          have b2931 := hb (x 5 2 && x 5 13)
          have b2932 := hb (x 4 3 && x 4 14)
          clear * - r2927 b2928 b2929 b2930 b2931 b2932 d2906 d2922 d2810 g17
          omega
        have d2933 : (x 7 3).toNat = 1 := by
          have r2934 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
          have b2935 := hb (x 7 3)
          have b2936 := hb (x 7 11)
          clear * - r2934 b2935 b2936 d2926
          omega
        have d2937 : (x 10 12).toNat = 0 := by
          have r2938 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e2939 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
          have e2940 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
          have b2941 := hb (x 7 3)
          have b2942 := hb (x 8 2)
          have b2943 := hb (x 9 13)
          have b2944 := hb (x 10 12)
          clear * - r2938 e2939 e2940 b2941 b2942 b2943 b2944 d2933
          omega
        have d2945 : (x 9 13).toNat = 0 := by
          have r2946 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e2947 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
          have e2948 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
          have b2949 := hb (x 7 3)
          have b2950 := hb (x 8 2)
          have b2951 := hb (x 9 13)
          have b2952 := hb (x 10 12)
          clear * - r2946 e2947 e2948 b2949 b2950 b2951 b2952 d2937 d2933
          omega
        have d2953 : (x 8 2).toNat = 0 := by
          have r2954 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e2955 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
          have e2956 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
          have b2957 := hb (x 7 3)
          have b2958 := hb (x 8 2)
          have b2959 := hb (x 9 13)
          have b2960 := hb (x 10 12)
          clear * - r2954 e2955 e2956 b2957 b2958 b2959 b2960 d2937 d2945 d2933
          omega
        have d2961 : (x 8 2 && x 8 7).toNat = 0 := by
          have r2962 := hand1 (x 8 2) (x 8 7)
          have b2963 := hb (x 8 2)
          have b2964 := hb (x 8 2 && x 8 7)
          clear * - r2962 b2963 b2964 d2953
          omega
        have d2965 : (x 8 10).toNat = 0 := by
          have r2966 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
          have b2967 := hb (x 8 2)
          have b2968 := hb (x 8 10)
          clear * - r2966 b2967 b2968 d2953
          omega
        have d2969 : (x 5 5).toNat = 0 := by
          have r2970 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
          have b2971 := hb (x 5 5)
          have b2972 := hb (x 5 13)
          clear * - r2970 b2971 b2972 d2914
          omega
        have d2973 : (x 10 8).toNat = 0 := by
          have r2974 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e2975 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
          have e2976 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
          have e2977 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
          have e2978 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
          have e2979 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
          have e2980 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
          have b2981 := hb (x 3 7)
          have b2982 := hb (x 4 6)
          have b2983 := hb (x 5 5)
          have b2984 := hb (x 6 4)
          have b2985 := hb (x 7 11)
          have b2986 := hb (x 8 10)
          have b2987 := hb (x 9 9)
          have b2988 := hb (x 10 8)
          clear * - r2974 e2975 e2976 e2977 e2978 e2979 e2980 b2981 b2982 b2983 b2984 b2985 b2986 b2987 b2988 d2965 d2926 d2910 d2969 d2814
          omega
        have d2989 : (x 9 9).toNat = 0 := by
          have r2990 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e2991 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
          have e2992 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
          have e2993 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
          have e2994 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
          have e2995 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
          have e2996 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
          have b2997 := hb (x 3 7)
          have b2998 := hb (x 4 6)
          have b2999 := hb (x 5 5)
          have b3000 := hb (x 6 4)
          have b3001 := hb (x 7 11)
          have b3002 := hb (x 8 10)
          have b3003 := hb (x 9 9)
          have b3004 := hb (x 10 8)
          clear * - r2990 e2991 e2992 e2993 e2994 e2995 e2996 b2997 b2998 b2999 b3000 b3001 b3002 b3003 b3004 d2973 d2965 d2926 d2910 d2969 d2814
          omega
        have d3005 : (x 3 7).toNat = 0 := by
          have r3006 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e3007 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
          have e3008 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
          have e3009 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
          have e3010 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
          have e3011 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
          have e3012 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
          have b3013 := hb (x 3 7)
          have b3014 := hb (x 4 6)
          have b3015 := hb (x 5 5)
          have b3016 := hb (x 6 4)
          have b3017 := hb (x 7 11)
          have b3018 := hb (x 8 10)
          have b3019 := hb (x 9 9)
          have b3020 := hb (x 10 8)
          clear * - r3006 e3007 e3008 e3009 e3010 e3011 e3012 b3013 b3014 b3015 b3016 b3017 b3018 b3019 b3020 d2973 d2989 d2965 d2926 d2910 d2969 d2814
          omega
        have d3021 : (x 3 7 && x 3 12).toNat = 0 := by
          have r3022 := hand1 (x 3 7) (x 3 12)
          have b3023 := hb (x 3 7)
          have b3024 := hb (x 3 7 && x 3 12)
          clear * - r3022 b3023 b3024 d3005
          omega
        have r3025 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e3026 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e3027 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e3028 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e3029 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e3030 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e3031 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have r3032 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e3033 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e3034 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e3035 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e3036 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e3037 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e3038 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have r3039 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e3040 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
        have e3041 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
        have e3042 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
        have e3043 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
        have e3044 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
        have e3045 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
        have r3046 : 1 ≤ (x 10 5).toNat + (x 9 1 && x 9 6).toNat + (x 8 2 && x 8 7).toNat + (x 7 3 && x 7 8).toNat + (x 6 4 && x 6 9).toNat + (x 5 5 && x 5 10).toNat + (x 4 6 && x 4 11).toNat + (x 3 7 && x 3 12).toNat + (x 2 8 && x 2 13).toNat + (x 1 9 && x 1 14).toNat + (x 0 10).toNat := by have q := hcov5 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r3047 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := by have q := hcov7 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r3048 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r3049 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r3050 := hand2 (x 9 1) (x 9 6)
        have r3051 := hand1 (x 1 9) (x 1 14)
        have r3052 := hand1 (x 3 5) (x 3 12)
        have r3053 := hand1 (x 1 7) (x 1 14)
        have r3054 := hand2 (x 6 1) (x 6 10)
        have r3055 := hand2 (x 5 2) (x 5 11)
        have r3056 := hand1 (x (-2) 4) (x (-2) 14)
        linarith only [r3025, e3026, e3027, e3028, e3029, e3030, e3031, r3032, e3033, e3034, e3035, e3036, e3037, e3038, r3039, e3040, e3041, e3042, e3043, e3044, e3045, r3046, r3047, r3048, r3049, r3050, r3051, r3052, r3053, r3054, r3055, r3056, d2767, g6, g8, g14, d2676, d2696, d2838, d2961, g36, g37, g38, g39, d3021, d2881, g46, g47, g48, g49, d2680, d2834, g54, g55, d2858, g56, d2755]
      · have f3109 : (x (-1) 4).toNat = 1 := by rw [h2885]; rfl
        have d3110 : (x (-1) 12).toNat = 1 := by
          have r3111 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
          have b3112 := hb (x (-1) 4)
          have b3113 := hb (x (-1) 12)
          clear * - r3111 b3112 b3113 f3109
          omega
        have d3114 : (x (-2) 13).toNat = 0 := by
          have r3115 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e3116 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e3117 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b3118 := hb (x (-4) 3)
          have b3119 := hb (x (-3) 2)
          have b3120 := hb (x (-2) 13)
          have b3121 := hb (x (-1) 12)
          clear * - r3115 e3116 e3117 b3118 b3119 b3120 b3121 d3110
          omega
        have d3122 : (x (-2) 4 && x (-2) 13).toNat = 0 := by
          have r3123 := hand2 (x (-2) 4) (x (-2) 13)
          have b3124 := hb (x (-2) 13)
          have b3125 := hb (x (-2) 4 && x (-2) 13)
          clear * - r3123 b3124 b3125 d3114
          omega
        have d3126 : (x (-2) 5).toNat = 0 := by
          have r3127 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
          have b3128 := hb (x (-2) 5)
          have b3129 := hb (x (-2) 13)
          clear * - r3127 b3128 b3129 d3114
          omega
        have d3130 : (x (-2) 5 && x (-2) 12).toNat = 0 := by
          have r3131 := hand1 (x (-2) 5) (x (-2) 12)
          have b3132 := hb (x (-2) 5)
          have b3133 := hb (x (-2) 5 && x (-2) 12)
          clear * - r3131 b3132 b3133 d3126
          omega
        have d3134 : (x (-3) 2).toNat = 0 := by
          have r3135 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e3136 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e3137 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b3138 := hb (x (-4) 3)
          have b3139 := hb (x (-3) 2)
          have b3140 := hb (x (-2) 13)
          have b3141 := hb (x (-1) 12)
          clear * - r3135 e3136 e3137 b3138 b3139 b3140 b3141 d3110 d3114
          omega
        have d3142 : (x (-3) 2 && x (-3) 13).toNat = 0 := by
          have r3143 := hand1 (x (-3) 2) (x (-3) 13)
          have b3144 := hb (x (-3) 2)
          have b3145 := hb (x (-3) 2 && x (-3) 13)
          clear * - r3143 b3144 b3145 d3134
          omega
        have d3146 : (x (-3) 10).toNat = 0 := by
          have r3147 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
          have b3148 := hb (x (-3) 2)
          have b3149 := hb (x (-3) 10)
          clear * - r3147 b3148 b3149 d3134
          omega
        have d3150 : (x (-3) 1 && x (-3) 10).toNat = 0 := by
          have r3151 := hand2 (x (-3) 1) (x (-3) 10)
          have b3152 := hb (x (-3) 10)
          have b3153 := hb (x (-3) 1 && x (-3) 10)
          clear * - r3151 b3152 b3153 d3146
          omega
        have d3154 : (x (-3) 5 && x (-3) 10).toNat = 0 := by
          have r3155 := hand2 (x (-3) 5) (x (-3) 10)
          have b3156 := hb (x (-3) 10)
          have b3157 := hb (x (-3) 5 && x (-3) 10)
          clear * - r3155 b3156 b3157 d3146
          omega
        have d3158 : (x (-4) 3).toNat = 0 := by
          have r3159 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e3160 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e3161 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b3162 := hb (x (-4) 3)
          have b3163 := hb (x (-3) 2)
          have b3164 := hb (x (-2) 13)
          have b3165 := hb (x (-1) 12)
          clear * - r3159 e3160 e3161 b3162 b3163 b3164 b3165 d3110 d3114 d3134
          omega
        have d3166 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
          have r3167 := hand1 (x (-4) 3) (x (-4) 14)
          have b3168 := hb (x (-4) 3)
          have b3169 := hb (x (-4) 3 && x (-4) 14)
          clear * - r3167 b3168 b3169 d3158
          omega
        have d3170 : (x (-4) 11).toNat = 0 := by
          have r3171 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
          have b3172 := hb (x (-4) 3)
          have b3173 := hb (x (-4) 11)
          clear * - r3171 b3172 b3173 d3158
          omega
        have d3174 : (x (-4) 2 && x (-4) 11).toNat = 0 := by
          have r3175 := hand2 (x (-4) 2) (x (-4) 11)
          have b3176 := hb (x (-4) 11)
          have b3177 := hb (x (-4) 2 && x (-4) 11)
          clear * - r3175 b3176 b3177 d3170
          omega
        have d3178 : (x (-4) 6 && x (-4) 11).toNat = 0 := by
          have r3179 := hand2 (x (-4) 6) (x (-4) 11)
          have b3180 := hb (x (-4) 11)
          have b3181 := hb (x (-4) 6 && x (-4) 11)
          clear * - r3179 b3180 b3181 d3170
          omega
        have d3182 : (x 3 8).toNat = 0 := by
          have r3183 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e3184 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e3185 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e3186 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e3187 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e3188 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e3189 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b3190 := hb (x (-4) 7)
          have b3191 := hb (x (-3) 6)
          have b3192 := hb (x (-2) 5)
          have b3193 := hb (x (-1) 4)
          have b3194 := hb (x 0 11)
          have b3195 := hb (x 1 10)
          have b3196 := hb (x 2 9)
          have b3197 := hb (x 3 8)
          clear * - r3183 e3184 e3185 e3186 e3187 e3188 e3189 b3190 b3191 b3192 b3193 b3194 b3195 b3196 b3197 d2789 g9 f3109 d3126
          omega
        have d3198 : (x 2 9).toNat = 0 := by
          have r3199 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e3200 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e3201 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e3202 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e3203 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e3204 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e3205 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b3206 := hb (x (-4) 7)
          have b3207 := hb (x (-3) 6)
          have b3208 := hb (x (-2) 5)
          have b3209 := hb (x (-1) 4)
          have b3210 := hb (x 0 11)
          have b3211 := hb (x 1 10)
          have b3212 := hb (x 2 9)
          have b3213 := hb (x 3 8)
          clear * - r3199 e3200 e3201 e3202 e3203 e3204 e3205 b3206 b3207 b3208 b3209 b3210 b3211 b3212 b3213 d3182 d2789 g9 f3109 d3126
          omega
        have d3214 : (x (-3) 6).toNat = 0 := by
          have r3215 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e3216 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e3217 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e3218 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e3219 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e3220 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e3221 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b3222 := hb (x (-4) 7)
          have b3223 := hb (x (-3) 6)
          have b3224 := hb (x (-2) 5)
          have b3225 := hb (x (-1) 4)
          have b3226 := hb (x 0 11)
          have b3227 := hb (x 1 10)
          have b3228 := hb (x 2 9)
          have b3229 := hb (x 3 8)
          clear * - r3215 e3216 e3217 e3218 e3219 e3220 e3221 b3222 b3223 b3224 b3225 b3226 b3227 b3228 b3229 d3182 d3198 d2789 g9 f3109 d3126
          omega
        have d3230 : (x (-3) 6 && x (-3) 13).toNat = 0 := by
          have r3231 := hand1 (x (-3) 6) (x (-3) 13)
          have b3232 := hb (x (-3) 6)
          have b3233 := hb (x (-3) 6 && x (-3) 13)
          clear * - r3231 b3232 b3233 d3214
          omega
        have d3234 : (x (-4) 7).toNat = 0 := by
          have r3235 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e3236 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e3237 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e3238 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e3239 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e3240 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e3241 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b3242 := hb (x (-4) 7)
          have b3243 := hb (x (-3) 6)
          have b3244 := hb (x (-2) 5)
          have b3245 := hb (x (-1) 4)
          have b3246 := hb (x 0 11)
          have b3247 := hb (x 1 10)
          have b3248 := hb (x 2 9)
          have b3249 := hb (x 3 8)
          clear * - r3235 e3236 e3237 e3238 e3239 e3240 e3241 b3242 b3243 b3244 b3245 b3246 b3247 b3248 b3249 d3182 d3198 d2789 g9 f3109 d3126 d3214
          omega
        have d3250 : (x (-4) 7 && x (-4) 14).toNat = 0 := by
          have r3251 := hand1 (x (-4) 7) (x (-4) 14)
          have b3252 := hb (x (-4) 7)
          have b3253 := hb (x (-4) 7 && x (-4) 14)
          clear * - r3251 b3252 b3253 d3234
          omega
        have r3254 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e3255 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
        have e3256 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
        have e3257 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
        have e3258 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
        have e3259 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
        have e3260 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
        have r3261 : (x (-5) 8).toNat + (x (-6) 1 && x (-6) 9).toNat + (x (-7) 2 && x (-7) 10).toNat + (x (-8) 3 && x (-8) 11).toNat + (x (-9) 4 && x (-9) 12).toNat + (x (-10) 5 && x (-10) 13).toNat + (x (-11) 6 && x (-11) 14).toNat + (x (-12) 7).toNat = 1 := by have q := hd8 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e3262 : (x (-6) 1 && x (-6) 9).toNat = (x (-6) 9).toNat := handr _ _ (fun h => hp9 (-6) (h))
        have e3263 : (x (-7) 2 && x (-7) 10).toNat = (x (-7) 10).toNat := handr _ _ (fun h => hp10 (-7) (h))
        have e3264 : (x (-8) 3 && x (-8) 11).toNat = (x (-8) 11).toNat := handr _ _ (fun h => hp11 (-8) (h))
        have e3265 : (x (-9) 4 && x (-9) 12).toNat = (x (-9) 4).toNat := handl _ _ (fun h => hp4 (-9) (h))
        have e3266 : (x (-10) 5 && x (-10) 13).toNat = (x (-10) 5).toNat := handl _ _ (fun h => hp5 (-10) (h))
        have e3267 : (x (-11) 6 && x (-11) 14).toNat = (x (-11) 6).toNat := handl _ _ (fun h => hp6 (-11) (h))
        have r3268 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e3269 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
        have e3270 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
        have e3271 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
        have e3272 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
        have e3273 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
        have e3274 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
        have r3275 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e3276 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e3277 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e3278 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e3279 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e3280 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e3281 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have r3282 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e3283 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e3284 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e3285 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e3286 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e3287 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e3288 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have r3289 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e3290 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
        have e3291 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
        have e3292 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
        have e3293 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
        have e3294 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
        have e3295 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
        have r3296 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e3297 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
        have e3298 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
        have r3299 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e3300 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
        have e3301 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
        have r3302 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e3303 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e3304 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have r3305 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e3306 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
        have e3307 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
        have r3308 : 1 ≤ (x 6 4).toNat + (x 5 1 && x 5 5).toNat + (x 4 2 && x 4 6).toNat + (x 3 3 && x 3 7).toNat + (x 2 4 && x 2 8).toNat + (x 1 5 && x 1 9).toNat + (x 0 6 && x 0 10).toNat + (x (-1) 7 && x (-1) 11).toNat + (x (-2) 8 && x (-2) 12).toNat + (x (-3) 9 && x (-3) 13).toNat + (x (-4) 10 && x (-4) 14).toNat + (x (-5) 11).toNat := by have q := hcov4 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e3309 : (x 5 1 && x 5 5).toNat = (x 5 5).toNat := handr _ _ (fun h => hp13 5 (hp5 5 (h)))
        have e3310 : (x (-4) 10 && x (-4) 14).toNat = (x (-4) 10).toNat := handl _ _ (fun h => hp2 (-4) (hp10 (-4) (h)))
        have r3311 : 1 ≤ (x 2 5).toNat + (x 1 1 && x 1 6).toNat + (x 0 2 && x 0 7).toNat + (x (-1) 3 && x (-1) 8).toNat + (x (-2) 4 && x (-2) 9).toNat + (x (-3) 5 && x (-3) 10).toNat + (x (-4) 6 && x (-4) 11).toNat + (x (-5) 7 && x (-5) 12).toNat + (x (-6) 8 && x (-6) 13).toNat + (x (-7) 9 && x (-7) 14).toNat + (x (-8) 10).toNat := by have q := hcov5 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r3312 : 1 ≤ (x 3 7).toNat + (x 2 1 && x 2 8).toNat + (x 1 2 && x 1 9).toNat + (x 0 3 && x 0 10).toNat + (x (-1) 4 && x (-1) 11).toNat + (x (-2) 5 && x (-2) 12).toNat + (x (-3) 6 && x (-3) 13).toNat + (x (-4) 7 && x (-4) 14).toNat + (x (-5) 8).toNat := by have q := hcov7 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r3313 : 1 ≤ (x (-6) 9).toNat + (x (-7) 1 && x (-7) 10).toNat + (x (-8) 2 && x (-8) 11).toNat + (x (-9) 3 && x (-9) 12).toNat + (x (-10) 4 && x (-10) 13).toNat + (x (-11) 5 && x (-11) 14).toNat + (x (-12) 6).toNat := by have q := hcov9 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r3314 : 1 ≤ (x (-2) 9).toNat + (x (-3) 1 && x (-3) 10).toNat + (x (-4) 2 && x (-4) 11).toNat + (x (-5) 3 && x (-5) 12).toNat + (x (-6) 4 && x (-6) 13).toNat + (x (-7) 5 && x (-7) 14).toNat + (x (-8) 6).toNat := by have q := hcov9 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r3315 : 1 ≤ (x 2 9).toNat + (x 1 1 && x 1 10).toNat + (x 0 2 && x 0 11).toNat + (x (-1) 3 && x (-1) 12).toNat + (x (-2) 4 && x (-2) 13).toNat + (x (-3) 5 && x (-3) 14).toNat + (x (-4) 6).toNat := by have q := hcov9 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r3316 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r3317 : 1 ≤ (x (-5) 11).toNat + (x (-6) 1 && x (-6) 12).toNat + (x (-7) 2 && x (-7) 13).toNat + (x (-8) 3 && x (-8) 14).toNat + (x (-9) 4).toNat := by have q := hcov11 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r3318 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r3319 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r3320 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
        have r3321 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
        have r3322 := hand1 (x 3 3) (x 3 7)
        have r3323 := hand2 (x 1 5) (x 1 9)
        have r3324 := hand1 (x (-2) 8) (x (-2) 12)
        have r3325 := hand1 (x (-3) 9) (x (-3) 13)
        have r3326 := hand2 (x (-2) 4) (x (-2) 9)
        have r3327 := hand1 (x (-5) 7) (x (-5) 12)
        have r3328 := hand1 (x (-6) 8) (x (-6) 13)
        have r3329 := hand1 (x (-7) 9) (x (-7) 14)
        have r3330 := hand2 (x 2 1) (x 2 8)
        have r3331 := hand2 (x (-7) 1) (x (-7) 10)
        have r3332 := hand2 (x (-8) 2) (x (-8) 11)
        have r3333 := hand1 (x (-9) 3) (x (-9) 12)
        have r3334 := hand1 (x (-10) 4) (x (-10) 13)
        have r3335 := hand1 (x (-11) 5) (x (-11) 14)
        have r3336 := hand1 (x (-5) 3) (x (-5) 12)
        have r3337 := hand2 (x (-6) 4) (x (-6) 13)
        have r3338 := hand1 (x (-7) 5) (x (-7) 14)
        have r3339 := hand1 (x (-3) 5) (x (-3) 14)
        have r3340 := hand1 (x (-2) 4) (x (-2) 14)
        have r3341 := hand2 (x (-6) 1) (x (-6) 12)
        have r3342 := hand1 (x (-7) 2) (x (-7) 13)
        have r3343 := hand1 (x (-8) 3) (x (-8) 14)
        have r3344 := hand2 (x (-2) 1) (x (-2) 12)
        have r3345 := hand2 (x 6 1) (x 6 12)
        have r3346 := hand2 (x 5 2) (x 5 13)
        linarith only [r3254, e3255, e3256, e3257, e3258, e3259, e3260, r3261, e3262, e3263, e3264, e3265, e3266, e3267, r3268, e3269, e3270, e3271, e3272, e3273, e3274, r3275, e3276, e3277, e3278, e3279, e3280, e3281, r3282, e3283, e3284, e3285, e3286, e3287, e3288, r3289, e3290, e3291, e3292, e3293, e3294, e3295, r3296, e3297, e3298, r3299, e3300, e3301, r3302, e3303, e3304, r3305, e3306, e3307, r3308, e3309, e3310, r3311, r3312, r3313, r3314, r3315, r3316, r3317, r3318, r3319, r3320, r3321, r3322, r3323, r3324, r3325, r3326, r3327, r3328, r3329, r3330, r3331, r3332, r3333, r3334, r3335, r3336, r3337, r3338, r3339, r3340, r3341, r3342, r3343, r3344, r3345, r3346, d3170, d3146, d2767, g8, g16, d3198, d2696, g17, d2822, d2814, d2818, d2743, g29, d2775, g34, g35, d2763, d3154, d3178, d2785, g41, d2771, d3130, d3230, d3250, d3150, d3174, d2793, g50, d2759, d3122, d2858, g56, d2755, d3142, d3166, d2810]
    · have f3467 : (x 1 2).toNat = 1 := by rw [h2779]; rfl
      have d3468 : (x 3 12).toNat = 0 := by
        have r3469 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e3470 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
        have e3471 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
        have b3472 := hb (x 0 3)
        have b3473 := hb (x 1 2)
        have b3474 := hb (x 2 13)
        have b3475 := hb (x 3 12)
        clear * - r3469 e3470 e3471 b3472 b3473 b3474 b3475 f3467 g1
        omega
      have d3476 : (x 3 1 && x 3 12).toNat = 0 := by
        have r3477 := hand2 (x 3 1) (x 3 12)
        have b3478 := hb (x 3 12)
        have b3479 := hb (x 3 1 && x 3 12)
        clear * - r3477 b3478 b3479 d3468
        omega
      have d3480 : (x 3 2 && x 3 12).toNat = 0 := by
        have r3481 := hand2 (x 3 2) (x 3 12)
        have b3482 := hb (x 3 12)
        have b3483 := hb (x 3 2 && x 3 12)
        clear * - r3481 b3482 b3483 d3468
        omega
      have d3484 : (x 3 3 && x 3 12).toNat = 0 := by
        have r3485 := hand2 (x 3 3) (x 3 12)
        have b3486 := hb (x 3 12)
        have b3487 := hb (x 3 3 && x 3 12)
        clear * - r3485 b3486 b3487 d3468
        omega
      have d3488 : (x 3 5 && x 3 12).toNat = 0 := by
        have r3489 := hand2 (x 3 5) (x 3 12)
        have b3490 := hb (x 3 12)
        have b3491 := hb (x 3 5 && x 3 12)
        clear * - r3489 b3490 b3491 d3468
        omega
      have d3492 : (x 3 8 && x 3 12).toNat = 0 := by
        have r3493 := hand2 (x 3 8) (x 3 12)
        have b3494 := hb (x 3 12)
        have b3495 := hb (x 3 8 && x 3 12)
        clear * - r3493 b3494 b3495 d3468
        omega
      have d3496 : (x 3 12 && x 3 14).toNat = 0 := by
        have r3497 := hand1 (x 3 12) (x 3 14)
        have b3498 := hb (x 3 12)
        have b3499 := hb (x 3 12 && x 3 14)
        clear * - r3497 b3498 b3499 d3468
        omega
      have d3500 : (x 2 13).toNat = 0 := by
        have r3501 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e3502 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
        have e3503 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
        have b3504 := hb (x 0 3)
        have b3505 := hb (x 1 2)
        have b3506 := hb (x 2 13)
        have b3507 := hb (x 3 12)
        clear * - r3501 e3502 e3503 b3504 b3505 b3506 b3507 d3468 f3467 g1
        omega
      have d3508 : (x 2 3 && x 2 13).toNat = 0 := by
        have r3509 := hand2 (x 2 3) (x 2 13)
        have b3510 := hb (x 2 13)
        have b3511 := hb (x 2 3 && x 2 13)
        clear * - r3509 b3510 b3511 d3500
        omega
      have d3512 : (x 2 9 && x 2 13).toNat = 0 := by
        have r3513 := hand2 (x 2 9) (x 2 13)
        have b3514 := hb (x 2 13)
        have b3515 := hb (x 2 9 && x 2 13)
        clear * - r3513 b3514 b3515 d3500
        omega
      have d3516 : (x 1 3 && x 1 14).toNat = 1 := by
        have r3517 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b3518 := hb (x 0 4)
        have b3519 := hb (x 4 11)
        have b3520 := hb (x 3 1 && x 3 12)
        have b3521 := hb (x 2 2 && x 2 13)
        have b3522 := hb (x 1 3 && x 1 14)
        clear * - r3517 b3518 b3519 b3520 b3521 b3522 g18 d3476 d2692 g2
        omega
      have d3523 : (x 1 3).toNat = 1 := by
        have r3524 := hand1 (x 1 3) (x 1 14)
        have b3525 := hb (x 1 3)
        have b3526 := hb (x 1 3 && x 1 14)
        clear * - r3524 b3525 b3526 d3516
        omega
      have d3527 : (x 4 12).toNat = 0 := by
        have r3528 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e3529 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e3530 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b3531 := hb (x 1 3)
        have b3532 := hb (x 2 2)
        have b3533 := hb (x 3 13)
        have b3534 := hb (x 4 12)
        clear * - r3528 e3529 e3530 b3531 b3532 b3533 b3534 d2688 d3523
        omega
      have d3535 : (x 4 3 && x 4 12).toNat = 0 := by
        have r3536 := hand2 (x 4 3) (x 4 12)
        have b3537 := hb (x 4 12)
        have b3538 := hb (x 4 3 && x 4 12)
        clear * - r3536 b3537 b3538 d3527
        omega
      have d3539 : (x 4 4).toNat = 0 := by
        have r3540 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
        have b3541 := hb (x 4 4)
        have b3542 := hb (x 4 12)
        clear * - r3540 b3541 b3542 d3527
        omega
      have d3543 : (x 3 13).toNat = 0 := by
        have r3544 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e3545 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e3546 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b3547 := hb (x 1 3)
        have b3548 := hb (x 2 2)
        have b3549 := hb (x 3 13)
        have b3550 := hb (x 4 12)
        clear * - r3544 e3545 e3546 b3547 b3548 b3549 b3550 d3527 d2688 d3523
        omega
      have d3551 : (x 3 5).toNat = 0 := by
        have r3552 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
        have b3553 := hb (x 3 5)
        have b3554 := hb (x 3 13)
        clear * - r3552 b3553 b3554 d3543
        omega
      have d3555 : (x 1 4 && x 1 14).toNat = 1 := by
        have r3556 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b3557 := hb (x 0 5)
        have b3558 := hb (x 5 10)
        have b3559 := hb (x 4 1 && x 4 11)
        have b3560 := hb (x 3 2 && x 3 12)
        have b3561 := hb (x 2 3 && x 2 13)
        have b3562 := hb (x 1 4 && x 1 14)
        clear * - r3556 b3557 b3558 b3559 b3560 b3561 b3562 g19 g57 d3480 d3508 g3
        omega
      have d3563 : (x 1 4).toNat = 1 := by
        have r3564 := hand1 (x 1 4) (x 1 14)
        have b3565 := hb (x 1 4)
        have b3566 := hb (x 1 4 && x 1 14)
        clear * - r3564 b3565 b3566 d3555
        omega
      have d3567 : (x 1 12).toNat = 1 := by
        have r3568 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
        have b3569 := hb (x 1 4)
        have b3570 := hb (x 1 12)
        clear * - r3568 b3569 b3570 d3563
        omega
      have d3571 : (x (-2) 3).toNat = 0 := by
        have r3572 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e3573 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e3574 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b3575 := hb (x (-2) 3)
        have b3576 := hb (x (-1) 2)
        have b3577 := hb (x 0 13)
        have b3578 := hb (x 1 12)
        clear * - r3572 e3573 e3574 b3575 b3576 b3577 b3578 d3567 g11 f2705
        omega
      have d3579 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
        have r3580 := hand1 (x (-2) 3) (x (-2) 14)
        have b3581 := hb (x (-2) 3)
        have b3582 := hb (x (-2) 3 && x (-2) 14)
        clear * - r3580 b3581 b3582 d3571
        omega
      have d3583 : (x (-2) 11).toNat = 0 := by
        have r3584 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
        have b3585 := hb (x (-2) 3)
        have b3586 := hb (x (-2) 11)
        clear * - r3584 b3585 b3586 d3571
        omega
      have d3587 : (x (-2) 1 && x (-2) 11).toNat = 0 := by
        have r3588 := hand2 (x (-2) 1) (x (-2) 11)
        have b3589 := hb (x (-2) 11)
        have b3590 := hb (x (-2) 1 && x (-2) 11)
        clear * - r3588 b3589 b3590 d3583
        omega
      have d3591 : (x (-2) 2 && x (-2) 11).toNat = 0 := by
        have r3592 := hand2 (x (-2) 2) (x (-2) 11)
        have b3593 := hb (x (-2) 11)
        have b3594 := hb (x (-2) 2 && x (-2) 11)
        clear * - r3592 b3593 b3594 d3583
        omega
      have d3595 : (x 1 5 && x 1 14).toNat = 1 := by
        have r3596 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b3597 := hb (x 0 6)
        have b3598 := hb (x 6 9)
        have b3599 := hb (x 5 1 && x 5 10)
        have b3600 := hb (x 4 2 && x 4 11)
        have b3601 := hb (x 3 3 && x 3 12)
        have b3602 := hb (x 2 4 && x 2 13)
        have b3603 := hb (x 1 5 && x 1 14)
        clear * - r3596 b3597 b3598 b3599 b3600 b3601 b3602 b3603 g20 g52 g53 d3484 d2739 g4
        omega
      have d3604 : (x 1 5).toNat = 1 := by
        have r3605 := hand1 (x 1 5) (x 1 14)
        have b3606 := hb (x 1 5)
        have b3607 := hb (x 1 5 && x 1 14)
        clear * - r3605 b3606 b3607 d3595
        omega
      have d3608 : (x 6 8).toNat = 0 := by
        have r3609 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e3610 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e3611 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e3612 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e3613 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e3614 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e3615 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b3616 := hb (x (-1) 7)
        have b3617 := hb (x 0 6)
        have b3618 := hb (x 1 5)
        have b3619 := hb (x 2 4)
        have b3620 := hb (x 3 11)
        have b3621 := hb (x 4 10)
        have b3622 := hb (x 5 9)
        have b3623 := hb (x 6 8)
        clear * - r3609 e3610 e3611 e3612 e3613 e3614 e3615 b3616 b3617 b3618 b3619 b3620 b3621 b3622 b3623 d2735 d3604 g4
        omega
      have d3624 : (x 6 1 && x 6 8).toNat = 0 := by
        have r3625 := hand2 (x 6 1) (x 6 8)
        have b3626 := hb (x 6 8)
        have b3627 := hb (x 6 1 && x 6 8)
        clear * - r3625 b3626 b3627 d3608
        omega
      have d3628 : (x 6 8 && x 6 12).toNat = 0 := by
        have r3629 := hand1 (x 6 8) (x 6 12)
        have b3630 := hb (x 6 8)
        have b3631 := hb (x 6 8 && x 6 12)
        clear * - r3629 b3630 b3631 d3608
        omega
      have d3632 : (x 5 9).toNat = 0 := by
        have r3633 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e3634 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e3635 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e3636 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e3637 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e3638 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e3639 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b3640 := hb (x (-1) 7)
        have b3641 := hb (x 0 6)
        have b3642 := hb (x 1 5)
        have b3643 := hb (x 2 4)
        have b3644 := hb (x 3 11)
        have b3645 := hb (x 4 10)
        have b3646 := hb (x 5 9)
        have b3647 := hb (x 6 8)
        clear * - r3633 e3634 e3635 e3636 e3637 e3638 e3639 b3640 b3641 b3642 b3643 b3644 b3645 b3646 b3647 d3608 d2735 d3604 g4
        omega
      have d3648 : (x 5 2 && x 5 9).toNat = 0 := by
        have r3649 := hand2 (x 5 2) (x 5 9)
        have b3650 := hb (x 5 9)
        have b3651 := hb (x 5 2 && x 5 9)
        clear * - r3649 b3650 b3651 d3632
        omega
      have d3652 : (x 5 9 && x 5 13).toNat = 0 := by
        have r3653 := hand1 (x 5 9) (x 5 13)
        have b3654 := hb (x 5 9)
        have b3655 := hb (x 5 9 && x 5 13)
        clear * - r3653 b3654 b3655 d3632
        omega
      have d3656 : (x 4 10).toNat = 0 := by
        have r3657 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e3658 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e3659 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e3660 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e3661 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e3662 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e3663 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b3664 := hb (x (-1) 7)
        have b3665 := hb (x 0 6)
        have b3666 := hb (x 1 5)
        have b3667 := hb (x 2 4)
        have b3668 := hb (x 3 11)
        have b3669 := hb (x 4 10)
        have b3670 := hb (x 5 9)
        have b3671 := hb (x 6 8)
        clear * - r3657 e3658 e3659 e3660 e3661 e3662 e3663 b3664 b3665 b3666 b3667 b3668 b3669 b3670 b3671 d3608 d3632 d2735 d3604 g4
        omega
      have d3672 : (x 4 3 && x 4 10).toNat = 0 := by
        have r3673 := hand2 (x 4 3) (x 4 10)
        have b3674 := hb (x 4 10)
        have b3675 := hb (x 4 3 && x 4 10)
        clear * - r3673 b3674 b3675 d3656
        omega
      have d3676 : (x 3 11).toNat = 0 := by
        have r3677 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e3678 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e3679 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e3680 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e3681 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e3682 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e3683 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b3684 := hb (x (-1) 7)
        have b3685 := hb (x 0 6)
        have b3686 := hb (x 1 5)
        have b3687 := hb (x 2 4)
        have b3688 := hb (x 3 11)
        have b3689 := hb (x 4 10)
        have b3690 := hb (x 5 9)
        have b3691 := hb (x 6 8)
        clear * - r3677 e3678 e3679 e3680 e3681 e3682 e3683 b3684 b3685 b3686 b3687 b3688 b3689 b3690 b3691 d3608 d3632 d3656 d2735 d3604 g4
        omega
      have d3692 : (x (-1) 7).toNat = 0 := by
        have r3693 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e3694 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e3695 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e3696 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e3697 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e3698 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e3699 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b3700 := hb (x (-1) 7)
        have b3701 := hb (x 0 6)
        have b3702 := hb (x 1 5)
        have b3703 := hb (x 2 4)
        have b3704 := hb (x 3 11)
        have b3705 := hb (x 4 10)
        have b3706 := hb (x 5 9)
        have b3707 := hb (x 6 8)
        clear * - r3693 e3694 e3695 e3696 e3697 e3698 e3699 b3700 b3701 b3702 b3703 b3704 b3705 b3706 b3707 d3608 d3632 d3656 d3676 d2735 d3604 g4
        omega
      have d3708 : (x 5 8).toNat = 0 := by
        have r3709 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e3710 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
        have e3711 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
        have e3712 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
        have e3713 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
        have e3714 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
        have e3715 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
        have b3716 := hb (x (-2) 7)
        have b3717 := hb (x (-1) 6)
        have b3718 := hb (x 0 5)
        have b3719 := hb (x 1 4)
        have b3720 := hb (x 2 11)
        have b3721 := hb (x 3 10)
        have b3722 := hb (x 4 9)
        have b3723 := hb (x 5 8)
        clear * - r3709 e3710 e3711 e3712 e3713 e3714 e3715 b3716 b3717 b3718 b3719 b3720 b3721 b3722 b3723 d3563 g3
        omega
      have d3724 : (x 4 9).toNat = 0 := by
        have r3725 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e3726 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
        have e3727 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
        have e3728 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
        have e3729 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
        have e3730 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
        have e3731 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
        have b3732 := hb (x (-2) 7)
        have b3733 := hb (x (-1) 6)
        have b3734 := hb (x 0 5)
        have b3735 := hb (x 1 4)
        have b3736 := hb (x 2 11)
        have b3737 := hb (x 3 10)
        have b3738 := hb (x 4 9)
        have b3739 := hb (x 5 8)
        clear * - r3725 e3726 e3727 e3728 e3729 e3730 e3731 b3732 b3733 b3734 b3735 b3736 b3737 b3738 b3739 d3708 d3563 g3
        omega
      have d3740 : (x 3 10).toNat = 0 := by
        have r3741 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e3742 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
        have e3743 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
        have e3744 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
        have e3745 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
        have e3746 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
        have e3747 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
        have b3748 := hb (x (-2) 7)
        have b3749 := hb (x (-1) 6)
        have b3750 := hb (x 0 5)
        have b3751 := hb (x 1 4)
        have b3752 := hb (x 2 11)
        have b3753 := hb (x 3 10)
        have b3754 := hb (x 4 9)
        have b3755 := hb (x 5 8)
        clear * - r3741 e3742 e3743 e3744 e3745 e3746 e3747 b3748 b3749 b3750 b3751 b3752 b3753 b3754 b3755 d3708 d3724 d3563 g3
        omega
      have d3756 : (x 2 11).toNat = 0 := by
        have r3757 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e3758 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
        have e3759 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
        have e3760 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
        have e3761 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
        have e3762 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
        have e3763 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
        have b3764 := hb (x (-2) 7)
        have b3765 := hb (x (-1) 6)
        have b3766 := hb (x 0 5)
        have b3767 := hb (x 1 4)
        have b3768 := hb (x 2 11)
        have b3769 := hb (x 3 10)
        have b3770 := hb (x 4 9)
        have b3771 := hb (x 5 8)
        clear * - r3757 e3758 e3759 e3760 e3761 e3762 e3763 b3764 b3765 b3766 b3767 b3768 b3769 b3770 b3771 d3708 d3724 d3740 d3563 g3
        omega
      have d3772 : (x (-1) 6).toNat = 0 := by
        have r3773 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e3774 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
        have e3775 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
        have e3776 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
        have e3777 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
        have e3778 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
        have e3779 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
        have b3780 := hb (x (-2) 7)
        have b3781 := hb (x (-1) 6)
        have b3782 := hb (x 0 5)
        have b3783 := hb (x 1 4)
        have b3784 := hb (x 2 11)
        have b3785 := hb (x 3 10)
        have b3786 := hb (x 4 9)
        have b3787 := hb (x 5 8)
        clear * - r3773 e3774 e3775 e3776 e3777 e3778 e3779 b3780 b3781 b3782 b3783 b3784 b3785 b3786 b3787 d3708 d3724 d3740 d3756 d3563 g3
        omega
      have d3788 : (x (-1) 6 && x (-1) 12).toNat = 0 := by
        have r3789 := hand1 (x (-1) 6) (x (-1) 12)
        have b3790 := hb (x (-1) 6)
        have b3791 := hb (x (-1) 6 && x (-1) 12)
        clear * - r3789 b3790 b3791 d3772
        omega
      have d3792 : (x (-2) 7).toNat = 0 := by
        have r3793 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e3794 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
        have e3795 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
        have e3796 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
        have e3797 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
        have e3798 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
        have e3799 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
        have b3800 := hb (x (-2) 7)
        have b3801 := hb (x (-1) 6)
        have b3802 := hb (x 0 5)
        have b3803 := hb (x 1 4)
        have b3804 := hb (x 2 11)
        have b3805 := hb (x 3 10)
        have b3806 := hb (x 4 9)
        have b3807 := hb (x 5 8)
        clear * - r3793 e3794 e3795 e3796 e3797 e3798 e3799 b3800 b3801 b3802 b3803 b3804 b3805 b3806 b3807 d3708 d3724 d3740 d3756 d3563 g3 d3772
        omega
      have d3808 : (x (-2) 7 && x (-2) 13).toNat = 0 := by
        have r3809 := hand1 (x (-2) 7) (x (-2) 13)
        have b3810 := hb (x (-2) 7)
        have b3811 := hb (x (-2) 7 && x (-2) 13)
        clear * - r3809 b3810 b3811 d3792
        omega
      cases h3812 : x (-1) 4
      · have f3813 : (x (-1) 4).toNat = 0 := by rw [h3812]; rfl
        have d3814 : (x (-1) 4 && x (-1) 13).toNat = 0 := by
          have r3815 := hand1 (x (-1) 4) (x (-1) 13)
          have b3816 := hb (x (-1) 4)
          have b3817 := hb (x (-1) 4 && x (-1) 13)
          clear * - r3815 b3816 b3817 f3813
          omega
        have d3818 : (x (-1) 4 && x (-1) 8).toNat = 0 := by
          have r3819 := hand1 (x (-1) 4) (x (-1) 8)
          have b3820 := hb (x (-1) 4)
          have b3821 := hb (x (-1) 4 && x (-1) 8)
          clear * - r3819 b3820 b3821 f3813
          omega
        cases h3822 : x (-1) 5
        · have f3823 : (x (-1) 5).toNat = 0 := by rw [h3822]; rfl
          have d3824 : (x (-1) 5 && x (-1) 9).toNat = 0 := by
            have r3825 := hand1 (x (-1) 5) (x (-1) 9)
            have b3826 := hb (x (-1) 5)
            have b3827 := hb (x (-1) 5 && x (-1) 9)
            clear * - r3825 b3826 b3827 f3823
            omega
          cases h3828 : x 1 7
          · have f3829 : (x 1 7).toNat = 0 := by rw [h3828]; rfl
            have d3830 : (x 1 7 && x 1 14).toNat = 0 := by
              have r3831 := hand1 (x 1 7) (x 1 14)
              have b3832 := hb (x 1 7)
              have b3833 := hb (x 1 7 && x 1 14)
              clear * - r3831 b3832 b3833 f3829
              omega
            have d3834 : (x 1 3 && x 1 7).toNat = 0 := by
              have r3835 := hand2 (x 1 3) (x 1 7)
              have b3836 := hb (x 1 7)
              have b3837 := hb (x 1 3 && x 1 7)
              clear * - r3835 b3836 b3837 f3829
              omega
            have d3838 : (x 8 7).toNat = 1 := by
              have r3839 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := by have q := hcov7 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b3840 := hb (x 0 8)
              have b3841 := hb (x 8 7)
              have b3842 := hb (x 7 1 && x 7 8)
              have b3843 := hb (x 6 2 && x 6 9)
              have b3844 := hb (x 5 3 && x 5 10)
              have b3845 := hb (x 4 4 && x 4 11)
              have b3846 := hb (x 3 5 && x 3 12)
              have b3847 := hb (x 2 6 && x 2 13)
              have b3848 := hb (x 1 7 && x 1 14)
              clear * - r3839 b3840 b3841 b3842 b3843 b3844 b3845 b3846 b3847 b3848 g46 g47 g48 g49 d3488 d2680 d3830 g6
              omega
            have d3849 : (x 15 8).toNat = 0 := by
              have r3850 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e3851 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
              have e3852 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
              have e3853 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
              have e3854 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
              have e3855 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
              have e3856 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
              have b3857 := hb (x 8 7)
              have b3858 := hb (x 9 6)
              have b3859 := hb (x 10 5)
              have b3860 := hb (x 11 4)
              have b3861 := hb (x 12 11)
              have b3862 := hb (x 13 10)
              have b3863 := hb (x 14 9)
              have b3864 := hb (x 15 8)
              clear * - r3850 e3851 e3852 e3853 e3854 e3855 e3856 b3857 b3858 b3859 b3860 b3861 b3862 b3863 b3864 d3838
              omega
            have d3865 : (x 15 4 && x 15 8).toNat = 0 := by
              have r3866 := hand2 (x 15 4) (x 15 8)
              have b3867 := hb (x 15 8)
              have b3868 := hb (x 15 4 && x 15 8)
              clear * - r3866 b3867 b3868 d3849
              omega
            have d3869 : (x 14 9).toNat = 0 := by
              have r3870 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e3871 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
              have e3872 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
              have e3873 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
              have e3874 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
              have e3875 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
              have e3876 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
              have b3877 := hb (x 8 7)
              have b3878 := hb (x 9 6)
              have b3879 := hb (x 10 5)
              have b3880 := hb (x 11 4)
              have b3881 := hb (x 12 11)
              have b3882 := hb (x 13 10)
              have b3883 := hb (x 14 9)
              have b3884 := hb (x 15 8)
              clear * - r3870 e3871 e3872 e3873 e3874 e3875 e3876 b3877 b3878 b3879 b3880 b3881 b3882 b3883 b3884 d3849 d3838
              omega
            have d3885 : (x 14 5 && x 14 9).toNat = 0 := by
              have r3886 := hand2 (x 14 5) (x 14 9)
              have b3887 := hb (x 14 9)
              have b3888 := hb (x 14 5 && x 14 9)
              clear * - r3886 b3887 b3888 d3869
              omega
            have d3889 : (x 13 10).toNat = 0 := by
              have r3890 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e3891 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
              have e3892 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
              have e3893 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
              have e3894 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
              have e3895 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
              have e3896 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
              have b3897 := hb (x 8 7)
              have b3898 := hb (x 9 6)
              have b3899 := hb (x 10 5)
              have b3900 := hb (x 11 4)
              have b3901 := hb (x 12 11)
              have b3902 := hb (x 13 10)
              have b3903 := hb (x 14 9)
              have b3904 := hb (x 15 8)
              clear * - r3890 e3891 e3892 e3893 e3894 e3895 e3896 b3897 b3898 b3899 b3900 b3901 b3902 b3903 b3904 d3849 d3869 d3838
              omega
            have d3905 : (x 13 1 && x 13 10).toNat = 0 := by
              have r3906 := hand2 (x 13 1) (x 13 10)
              have b3907 := hb (x 13 10)
              have b3908 := hb (x 13 1 && x 13 10)
              clear * - r3906 b3907 b3908 d3889
              omega
            have d3909 : (x 13 6 && x 13 10).toNat = 0 := by
              have r3910 := hand2 (x 13 6) (x 13 10)
              have b3911 := hb (x 13 10)
              have b3912 := hb (x 13 6 && x 13 10)
              clear * - r3910 b3911 b3912 d3889
              omega
            have d3913 : (x 12 11).toNat = 0 := by
              have r3914 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e3915 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
              have e3916 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
              have e3917 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
              have e3918 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
              have e3919 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
              have e3920 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
              have b3921 := hb (x 8 7)
              have b3922 := hb (x 9 6)
              have b3923 := hb (x 10 5)
              have b3924 := hb (x 11 4)
              have b3925 := hb (x 12 11)
              have b3926 := hb (x 13 10)
              have b3927 := hb (x 14 9)
              have b3928 := hb (x 15 8)
              clear * - r3914 e3915 e3916 e3917 e3918 e3919 e3920 b3921 b3922 b3923 b3924 b3925 b3926 b3927 b3928 d3849 d3869 d3889 d3838
              omega
            have d3929 : (x 12 2 && x 12 11).toNat = 0 := by
              have r3930 := hand2 (x 12 2) (x 12 11)
              have b3931 := hb (x 12 11)
              have b3932 := hb (x 12 2 && x 12 11)
              clear * - r3930 b3931 b3932 d3913
              omega
            have d3933 : (x 12 7 && x 12 11).toNat = 0 := by
              have r3934 := hand2 (x 12 7) (x 12 11)
              have b3935 := hb (x 12 11)
              have b3936 := hb (x 12 7 && x 12 11)
              clear * - r3934 b3935 b3936 d3913
              omega
            have d3937 : (x 11 4).toNat = 0 := by
              have r3938 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e3939 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
              have e3940 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
              have e3941 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
              have e3942 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
              have e3943 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
              have e3944 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
              have b3945 := hb (x 8 7)
              have b3946 := hb (x 9 6)
              have b3947 := hb (x 10 5)
              have b3948 := hb (x 11 4)
              have b3949 := hb (x 12 11)
              have b3950 := hb (x 13 10)
              have b3951 := hb (x 14 9)
              have b3952 := hb (x 15 8)
              clear * - r3938 e3939 e3940 e3941 e3942 e3943 e3944 b3945 b3946 b3947 b3948 b3949 b3950 b3951 b3952 d3849 d3869 d3889 d3913 d3838
              omega
            have d3953 : (x 11 4 && x 11 13).toNat = 0 := by
              have r3954 := hand1 (x 11 4) (x 11 13)
              have b3955 := hb (x 11 4)
              have b3956 := hb (x 11 4 && x 11 13)
              clear * - r3954 b3955 b3956 d3937
              omega
            have d3957 : (x 11 4 && x 11 6).toNat = 0 := by
              have r3958 := hand1 (x 11 4) (x 11 6)
              have b3959 := hb (x 11 4)
              have b3960 := hb (x 11 4 && x 11 6)
              clear * - r3958 b3959 b3960 d3937
              omega
            have d3961 : (x 10 5).toNat = 0 := by
              have r3962 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e3963 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
              have e3964 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
              have e3965 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
              have e3966 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
              have e3967 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
              have e3968 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
              have b3969 := hb (x 8 7)
              have b3970 := hb (x 9 6)
              have b3971 := hb (x 10 5)
              have b3972 := hb (x 11 4)
              have b3973 := hb (x 12 11)
              have b3974 := hb (x 13 10)
              have b3975 := hb (x 14 9)
              have b3976 := hb (x 15 8)
              clear * - r3962 e3963 e3964 e3965 e3966 e3967 e3968 b3969 b3970 b3971 b3972 b3973 b3974 b3975 b3976 d3849 d3869 d3889 d3913 d3937 d3838
              omega
            have d3977 : (x 10 5 && x 10 14).toNat = 0 := by
              have r3978 := hand1 (x 10 5) (x 10 14)
              have b3979 := hb (x 10 5)
              have b3980 := hb (x 10 5 && x 10 14)
              clear * - r3978 b3979 b3980 d3961
              omega
            have d3981 : (x 10 5 && x 10 7).toNat = 0 := by
              have r3982 := hand1 (x 10 5) (x 10 7)
              have b3983 := hb (x 10 5)
              have b3984 := hb (x 10 5 && x 10 7)
              clear * - r3982 b3983 b3984 d3961
              omega
            have d3985 : (x 9 6).toNat = 0 := by
              have r3986 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e3987 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
              have e3988 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
              have e3989 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
              have e3990 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
              have e3991 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
              have e3992 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
              have b3993 := hb (x 8 7)
              have b3994 := hb (x 9 6)
              have b3995 := hb (x 10 5)
              have b3996 := hb (x 11 4)
              have b3997 := hb (x 12 11)
              have b3998 := hb (x 13 10)
              have b3999 := hb (x 14 9)
              have b4000 := hb (x 15 8)
              clear * - r3986 e3987 e3988 e3989 e3990 e3991 e3992 b3993 b3994 b3995 b3996 b3997 b3998 b3999 b4000 d3849 d3869 d3889 d3913 d3937 d3961 d3838
              omega
            have d4001 : (x 9 6 && x 9 8).toNat = 0 := by
              have r4002 := hand1 (x 9 6) (x 9 8)
              have b4003 := hb (x 9 6)
              have b4004 := hb (x 9 6 && x 9 8)
              clear * - r4002 b4003 b4004 d3985
              omega
            cases h4005 : x (-1) 8
            · have f4006 : (x (-1) 8).toNat = 0 := by rw [h4005]; rfl
              have d4007 : (x 7 7).toNat = 1 := by
                have r4008 : 1 ≤ (x 7 7).toNat + (x 6 1 && x 6 8).toNat + (x 5 2 && x 5 9).toNat + (x 4 3 && x 4 10).toNat + (x 3 4 && x 3 11).toNat + (x 2 5 && x 2 12).toNat + (x 1 6 && x 1 13).toNat + (x 0 7 && x 0 14).toNat + (x (-1) 8).toNat := by have q := hcov7 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4009 := hb (x (-1) 8)
                have b4010 := hb (x 7 7)
                have b4011 := hb (x 6 1 && x 6 8)
                have b4012 := hb (x 5 2 && x 5 9)
                have b4013 := hb (x 4 3 && x 4 10)
                have b4014 := hb (x 3 4 && x 3 11)
                have b4015 := hb (x 2 5 && x 2 12)
                have b4016 := hb (x 1 6 && x 1 13)
                have b4017 := hb (x 0 7 && x 0 14)
                clear * - r4008 b4009 b4010 b4011 b4012 b4013 b4014 b4015 b4016 b4017 d3624 d3648 d3672 g42 g43 g44 g45 f4006
                omega
              have d4018 : (x 14 8).toNat = 0 := by
                have r4019 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4020 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                have e4021 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                have e4022 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                have e4023 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                have e4024 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                have e4025 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                have b4026 := hb (x 7 7)
                have b4027 := hb (x 8 6)
                have b4028 := hb (x 9 5)
                have b4029 := hb (x 10 4)
                have b4030 := hb (x 11 11)
                have b4031 := hb (x 12 10)
                have b4032 := hb (x 13 9)
                have b4033 := hb (x 14 8)
                clear * - r4019 e4020 e4021 e4022 e4023 e4024 e4025 b4026 b4027 b4028 b4029 b4030 b4031 b4032 b4033 d4007
                omega
              have d4034 : (x 13 9).toNat = 0 := by
                have r4035 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4036 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                have e4037 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                have e4038 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                have e4039 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                have e4040 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                have e4041 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                have b4042 := hb (x 7 7)
                have b4043 := hb (x 8 6)
                have b4044 := hb (x 9 5)
                have b4045 := hb (x 10 4)
                have b4046 := hb (x 11 11)
                have b4047 := hb (x 12 10)
                have b4048 := hb (x 13 9)
                have b4049 := hb (x 14 8)
                clear * - r4035 e4036 e4037 e4038 e4039 e4040 e4041 b4042 b4043 b4044 b4045 b4046 b4047 b4048 b4049 d4018 d4007
                omega
              have d4050 : (x 12 10).toNat = 0 := by
                have r4051 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4052 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                have e4053 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                have e4054 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                have e4055 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                have e4056 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                have e4057 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                have b4058 := hb (x 7 7)
                have b4059 := hb (x 8 6)
                have b4060 := hb (x 9 5)
                have b4061 := hb (x 10 4)
                have b4062 := hb (x 11 11)
                have b4063 := hb (x 12 10)
                have b4064 := hb (x 13 9)
                have b4065 := hb (x 14 8)
                clear * - r4051 e4052 e4053 e4054 e4055 e4056 e4057 b4058 b4059 b4060 b4061 b4062 b4063 b4064 b4065 d4018 d4034 d4007
                omega
              have d4066 : (x 11 11).toNat = 0 := by
                have r4067 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4068 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                have e4069 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                have e4070 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                have e4071 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                have e4072 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                have e4073 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                have b4074 := hb (x 7 7)
                have b4075 := hb (x 8 6)
                have b4076 := hb (x 9 5)
                have b4077 := hb (x 10 4)
                have b4078 := hb (x 11 11)
                have b4079 := hb (x 12 10)
                have b4080 := hb (x 13 9)
                have b4081 := hb (x 14 8)
                clear * - r4067 e4068 e4069 e4070 e4071 e4072 e4073 b4074 b4075 b4076 b4077 b4078 b4079 b4080 b4081 d4018 d4034 d4050 d4007
                omega
              have d4082 : (x 10 4).toNat = 0 := by
                have r4083 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4084 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                have e4085 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                have e4086 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                have e4087 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                have e4088 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                have e4089 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                have b4090 := hb (x 7 7)
                have b4091 := hb (x 8 6)
                have b4092 := hb (x 9 5)
                have b4093 := hb (x 10 4)
                have b4094 := hb (x 11 11)
                have b4095 := hb (x 12 10)
                have b4096 := hb (x 13 9)
                have b4097 := hb (x 14 8)
                clear * - r4083 e4084 e4085 e4086 e4087 e4088 e4089 b4090 b4091 b4092 b4093 b4094 b4095 b4096 b4097 d4018 d4034 d4050 d4066 d4007
                omega
              have d4098 : (x 10 4 && x 10 13).toNat = 0 := by
                have r4099 := hand1 (x 10 4) (x 10 13)
                have b4100 := hb (x 10 4)
                have b4101 := hb (x 10 4 && x 10 13)
                clear * - r4099 b4100 b4101 d4082
                omega
              have d4102 : (x 10 4 && x 10 8).toNat = 0 := by
                have r4103 := hand1 (x 10 4) (x 10 8)
                have b4104 := hb (x 10 4)
                have b4105 := hb (x 10 4 && x 10 8)
                clear * - r4103 b4104 b4105 d4082
                omega
              have d4106 : (x 9 5).toNat = 0 := by
                have r4107 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4108 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                have e4109 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                have e4110 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                have e4111 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                have e4112 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                have e4113 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                have b4114 := hb (x 7 7)
                have b4115 := hb (x 8 6)
                have b4116 := hb (x 9 5)
                have b4117 := hb (x 10 4)
                have b4118 := hb (x 11 11)
                have b4119 := hb (x 12 10)
                have b4120 := hb (x 13 9)
                have b4121 := hb (x 14 8)
                clear * - r4107 e4108 e4109 e4110 e4111 e4112 e4113 b4114 b4115 b4116 b4117 b4118 b4119 b4120 b4121 d4018 d4034 d4050 d4066 d4082 d4007
                omega
              have d4122 : (x 9 5 && x 9 14).toNat = 0 := by
                have r4123 := hand1 (x 9 5) (x 9 14)
                have b4124 := hb (x 9 5)
                have b4125 := hb (x 9 5 && x 9 14)
                clear * - r4123 b4124 b4125 d4106
                omega
              have d4126 : (x 9 5 && x 9 9).toNat = 0 := by
                have r4127 := hand1 (x 9 5) (x 9 9)
                have b4128 := hb (x 9 5)
                have b4129 := hb (x 9 5 && x 9 9)
                clear * - r4127 b4128 b4129 d4106
                omega
              have d4130 : (x 8 6).toNat = 0 := by
                have r4131 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4132 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                have e4133 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                have e4134 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                have e4135 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                have e4136 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                have e4137 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                have b4138 := hb (x 7 7)
                have b4139 := hb (x 8 6)
                have b4140 := hb (x 9 5)
                have b4141 := hb (x 10 4)
                have b4142 := hb (x 11 11)
                have b4143 := hb (x 12 10)
                have b4144 := hb (x 13 9)
                have b4145 := hb (x 14 8)
                clear * - r4131 e4132 e4133 e4134 e4135 e4136 e4137 b4138 b4139 b4140 b4141 b4142 b4143 b4144 b4145 d4018 d4034 d4050 d4066 d4082 d4106 d4007
                omega
              have d4146 : (x 8 6 && x 8 10).toNat = 0 := by
                have r4147 := hand1 (x 8 6) (x 8 10)
                have b4148 := hb (x 8 6)
                have b4149 := hb (x 8 6 && x 8 10)
                clear * - r4147 b4148 b4149 d4130
                omega
              have d4150 : (x 11 3 && x 11 12).toNat = 1 := by
                have r4151 : 1 ≤ (x 14 9).toNat + (x 13 1 && x 13 10).toNat + (x 12 2 && x 12 11).toNat + (x 11 3 && x 11 12).toNat + (x 10 4 && x 10 13).toNat + (x 9 5 && x 9 14).toNat + (x 8 6).toNat := by have q := hcov9 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4152 := hb (x 8 6)
                have b4153 := hb (x 14 9)
                have b4154 := hb (x 13 1 && x 13 10)
                have b4155 := hb (x 12 2 && x 12 11)
                have b4156 := hb (x 11 3 && x 11 12)
                have b4157 := hb (x 10 4 && x 10 13)
                have b4158 := hb (x 9 5 && x 9 14)
                clear * - r4151 b4152 b4153 b4154 b4155 b4156 b4157 b4158 d3869 d3905 d3929 d4098 d4122 d4130
                omega
              have d4159 : (x 11 12).toNat = 1 := by
                have r4160 := hand2 (x 11 3) (x 11 12)
                have b4161 := hb (x 11 12)
                have b4162 := hb (x 11 3 && x 11 12)
                clear * - r4160 b4161 b4162 d4150
                omega
              have d4163 : (x 10 13).toNat = 0 := by
                have r4164 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4165 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                have e4166 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                have b4167 := hb (x 8 3)
                have b4168 := hb (x 9 2)
                have b4169 := hb (x 10 13)
                have b4170 := hb (x 11 12)
                clear * - r4164 e4165 e4166 b4167 b4168 b4169 b4170 d4159
                omega
              have d4171 : (x 10 2 && x 10 13).toNat = 0 := by
                have r4172 := hand2 (x 10 2) (x 10 13)
                have b4173 := hb (x 10 13)
                have b4174 := hb (x 10 2 && x 10 13)
                clear * - r4172 b4173 b4174 d4163
                omega
              have d4175 : (x 10 9 && x 10 13).toNat = 0 := by
                have r4176 := hand2 (x 10 9) (x 10 13)
                have b4177 := hb (x 10 13)
                have b4178 := hb (x 10 9 && x 10 13)
                clear * - r4176 b4177 b4178 d4163
                omega
              have d4179 : (x 9 2).toNat = 0 := by
                have r4180 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4181 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                have e4182 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                have b4183 := hb (x 8 3)
                have b4184 := hb (x 9 2)
                have b4185 := hb (x 10 13)
                have b4186 := hb (x 11 12)
                clear * - r4180 e4181 e4182 b4183 b4184 b4185 b4186 d4159 d4163
                omega
              have d4187 : (x 9 2 && x 9 13).toNat = 0 := by
                have r4188 := hand1 (x 9 2) (x 9 13)
                have b4189 := hb (x 9 2)
                have b4190 := hb (x 9 2 && x 9 13)
                clear * - r4188 b4189 b4190 d4179
                omega
              have d4191 : (x 9 10).toNat = 0 := by
                have r4192 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
                have b4193 := hb (x 9 2)
                have b4194 := hb (x 9 10)
                clear * - r4192 b4193 b4194 d4179
                omega
              have d4195 : (x 8 3).toNat = 0 := by
                have r4196 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4197 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                have e4198 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                have b4199 := hb (x 8 3)
                have b4200 := hb (x 9 2)
                have b4201 := hb (x 10 13)
                have b4202 := hb (x 11 12)
                clear * - r4196 e4197 e4198 b4199 b4200 b4201 b4202 d4159 d4163 d4179
                omega
              have d4203 : (x 8 3 && x 8 14).toNat = 0 := by
                have r4204 := hand1 (x 8 3) (x 8 14)
                have b4205 := hb (x 8 3)
                have b4206 := hb (x 8 3 && x 8 14)
                clear * - r4204 b4205 b4206 d4195
                omega
              have d4207 : (x 8 11).toNat = 0 := by
                have r4208 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
                have b4209 := hb (x 8 3)
                have b4210 := hb (x 8 11)
                clear * - r4208 b4209 b4210 d4195
                omega
              have d4211 : (x 11 3).toNat = 1 := by
                have r4212 := hand1 (x 11 3) (x 11 12)
                have b4213 := hb (x 11 3)
                have b4214 := hb (x 11 3 && x 11 12)
                clear * - r4212 b4213 b4214 d4150
                omega
              have d4215 : (x 14 12).toNat = 0 := by
                have r4216 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4217 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
                have e4218 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
                have b4219 := hb (x 11 3)
                have b4220 := hb (x 12 2)
                have b4221 := hb (x 13 13)
                have b4222 := hb (x 14 12)
                clear * - r4216 e4217 e4218 b4219 b4220 b4221 b4222 d4211
                omega
              have d4223 : (x 14 1 && x 14 12).toNat = 0 := by
                have r4224 := hand2 (x 14 1) (x 14 12)
                have b4225 := hb (x 14 12)
                have b4226 := hb (x 14 1 && x 14 12)
                clear * - r4224 b4225 b4226 d4215
                omega
              have d4227 : (x 14 2 && x 14 12).toNat = 0 := by
                have r4228 := hand2 (x 14 2) (x 14 12)
                have b4229 := hb (x 14 12)
                have b4230 := hb (x 14 2 && x 14 12)
                clear * - r4228 b4229 b4230 d4215
                omega
              have d4231 : (x 14 4).toNat = 0 := by
                have r4232 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
                have b4233 := hb (x 14 4)
                have b4234 := hb (x 14 12)
                clear * - r4232 b4233 b4234 d4215
                omega
              have d4235 : (x 13 13).toNat = 0 := by
                have r4236 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4237 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
                have e4238 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
                have b4239 := hb (x 11 3)
                have b4240 := hb (x 12 2)
                have b4241 := hb (x 13 13)
                have b4242 := hb (x 14 12)
                clear * - r4236 e4237 e4238 b4239 b4240 b4241 b4242 d4215 d4211
                omega
              have d4243 : (x 13 2 && x 13 13).toNat = 0 := by
                have r4244 := hand2 (x 13 2) (x 13 13)
                have b4245 := hb (x 13 13)
                have b4246 := hb (x 13 2 && x 13 13)
                clear * - r4244 b4245 b4246 d4235
                omega
              have d4247 : (x 13 3 && x 13 13).toNat = 0 := by
                have r4248 := hand2 (x 13 3) (x 13 13)
                have b4249 := hb (x 13 13)
                have b4250 := hb (x 13 3 && x 13 13)
                clear * - r4248 b4249 b4250 d4235
                omega
              have d4251 : (x 13 5).toNat = 0 := by
                have r4252 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
                have b4253 := hb (x 13 5)
                have b4254 := hb (x 13 13)
                clear * - r4252 b4253 b4254 d4235
                omega
              have d4255 : (x 12 2).toNat = 0 := by
                have r4256 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4257 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
                have e4258 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
                have b4259 := hb (x 11 3)
                have b4260 := hb (x 12 2)
                have b4261 := hb (x 13 13)
                have b4262 := hb (x 14 12)
                clear * - r4256 e4257 e4258 b4259 b4260 b4261 b4262 d4215 d4235 d4211
                omega
              have d4263 : (x 12 2 && x 12 6).toNat = 0 := by
                have r4264 := hand1 (x 12 2) (x 12 6)
                have b4265 := hb (x 12 2)
                have b4266 := hb (x 12 2 && x 12 6)
                clear * - r4264 b4265 b4266 d4255
                omega
              have d4267 : (x 13 1).toNat = 0 := by
                have r4268 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4269 := hb (x 0 14)
                have b4270 := hb (x 1 13)
                have b4271 := hb (x 2 12)
                have b4272 := hb (x 3 11)
                have b4273 := hb (x 4 10)
                have b4274 := hb (x 5 9)
                have b4275 := hb (x 6 8)
                have b4276 := hb (x 7 7)
                have b4277 := hb (x 8 6)
                have b4278 := hb (x 9 5)
                have b4279 := hb (x 10 4)
                have b4280 := hb (x 11 3)
                have b4281 := hb (x 12 2)
                have b4282 := hb (x 13 1)
                clear * - r4268 b4269 b4270 b4271 b4272 b4273 b4274 b4275 b4276 b4277 b4278 b4279 b4280 b4281 b4282 d4255 d4211 d4082 d4106 d4130 d4007 d3608 d3632 d3656 d3676 d2723 d2718 g12
                omega
              have d4283 : (x 13 1 && x 13 14).toNat = 0 := by
                have r4284 := hand1 (x 13 1) (x 13 14)
                have b4285 := hb (x 13 1)
                have b4286 := hb (x 13 1 && x 13 14)
                clear * - r4284 b4285 b4286 d4267
                omega
              have d4287 : (x 14 13).toNat = 1 := by
                have r4288 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4289 := hb (x 12 2)
                have b4290 := hb (x 14 13)
                have b4291 := hb (x 13 1 && x 13 14)
                clear * - r4288 b4289 b4290 b4291 d4283 d4255
                omega
              have d4292 : (x 14 1).toNat = 1 := by
                have r4293 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
                have b4294 := hb (x 14 1)
                have b4295 := hb (x 14 13)
                clear * - r4293 b4294 b4295 d4287
                omega
              have d4296 : (x 15 14).toNat = 0 := by
                have r4297 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4298 := hb (x 14 1)
                have b4299 := hb (x 15 14)
                clear * - r4297 b4298 b4299 d4292
                omega
              have d4300 : (x 15 2).toNat = 0 := by
                have r4301 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
                have b4302 := hb (x 15 2)
                have b4303 := hb (x 15 14)
                clear * - r4301 b4302 b4303 d4296
                omega
              have d4304 : (x 13 2).toNat = 0 := by
                have r4305 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4306 := hb (x 1 14)
                have b4307 := hb (x 2 13)
                have b4308 := hb (x 3 12)
                have b4309 := hb (x 4 11)
                have b4310 := hb (x 5 10)
                have b4311 := hb (x 6 9)
                have b4312 := hb (x 7 8)
                have b4313 := hb (x 8 7)
                have b4314 := hb (x 9 6)
                have b4315 := hb (x 10 5)
                have b4316 := hb (x 11 4)
                have b4317 := hb (x 12 3)
                have b4318 := hb (x 13 2)
                have b4319 := hb (x 14 1)
                clear * - r4305 b4306 b4307 b4308 b4309 b4310 b4311 b4312 b4313 b4314 b4315 b4316 b4317 b4318 b4319 d4292 d3937 d3961 d3985 d3838 g21 g20 g19 g18 d3468 d3500 g15
                omega
              have d4320 : (x 13 2 && x 13 11).toNat = 0 := by
                have r4321 := hand1 (x 13 2) (x 13 11)
                have b4322 := hb (x 13 2)
                have b4323 := hb (x 13 2 && x 13 11)
                clear * - r4321 b4322 b4323 d4304
                omega
              have d4324 : (x 12 3).toNat = 0 := by
                have r4325 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4326 := hb (x 1 14)
                have b4327 := hb (x 2 13)
                have b4328 := hb (x 3 12)
                have b4329 := hb (x 4 11)
                have b4330 := hb (x 5 10)
                have b4331 := hb (x 6 9)
                have b4332 := hb (x 7 8)
                have b4333 := hb (x 8 7)
                have b4334 := hb (x 9 6)
                have b4335 := hb (x 10 5)
                have b4336 := hb (x 11 4)
                have b4337 := hb (x 12 3)
                have b4338 := hb (x 13 2)
                have b4339 := hb (x 14 1)
                clear * - r4325 b4326 b4327 b4328 b4329 b4330 b4331 b4332 b4333 b4334 b4335 b4336 b4337 b4338 b4339 d4292 d4304 d3937 d3961 d3985 d3838 g21 g20 g19 g18 d3468 d3500 g15
                omega
              have d4340 : (x 12 3 && x 12 14).toNat = 0 := by
                have r4341 := hand1 (x 12 3) (x 12 14)
                have b4342 := hb (x 12 3)
                have b4343 := hb (x 12 3 && x 12 14)
                clear * - r4341 b4342 b4343 d4324
                omega
              have d4344 : (x 15 11).toNat = 1 := by
                have r4345 : 1 ≤ (x 15 11).toNat + (x 14 1 && x 14 12).toNat + (x 13 2 && x 13 13).toNat + (x 12 3 && x 12 14).toNat + (x 11 4).toNat := by have q := hcov11 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4346 := hb (x 11 4)
                have b4347 := hb (x 15 11)
                have b4348 := hb (x 14 1 && x 14 12)
                have b4349 := hb (x 13 2 && x 13 13)
                have b4350 := hb (x 12 3 && x 12 14)
                clear * - r4345 b4346 b4347 b4348 b4349 b4350 d4223 d4243 d4340 d3937
                omega
              have d4351 : (x 15 3).toNat = 1 := by
                have r4352 : (x 15 11).toNat ≤ (x 15 3).toNat := himp _ _ (hp11 15)
                have b4353 := hb (x 15 3)
                have b4354 := hb (x 15 11)
                clear * - r4352 b4353 b4354 d4344
                omega
              have d4355 : (x 18 12).toNat = 0 := by
                have r4356 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4357 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
                have e4358 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
                have b4359 := hb (x 15 3)
                have b4360 := hb (x 16 2)
                have b4361 := hb (x 17 13)
                have b4362 := hb (x 18 12)
                clear * - r4356 e4357 e4358 b4359 b4360 b4361 b4362 d4351
                omega
              have d4363 : (x 18 2 && x 18 12).toNat = 0 := by
                have r4364 := hand2 (x 18 2) (x 18 12)
                have b4365 := hb (x 18 12)
                have b4366 := hb (x 18 2 && x 18 12)
                clear * - r4364 b4365 b4366 d4355
                omega
              have d4367 : (x 18 4).toNat = 0 := by
                have r4368 : (x 18 4).toNat ≤ (x 18 12).toNat := himp _ _ (hp4 18)
                have b4369 := hb (x 18 4)
                have b4370 := hb (x 18 12)
                clear * - r4368 b4369 b4370 d4355
                omega
              have d4371 : (x 18 4 && x 18 13).toNat = 0 := by
                have r4372 := hand1 (x 18 4) (x 18 13)
                have b4373 := hb (x 18 4)
                have b4374 := hb (x 18 4 && x 18 13)
                clear * - r4372 b4373 b4374 d4367
                omega
              have d4375 : (x 17 13).toNat = 0 := by
                have r4376 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4377 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
                have e4378 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
                have b4379 := hb (x 15 3)
                have b4380 := hb (x 16 2)
                have b4381 := hb (x 17 13)
                have b4382 := hb (x 18 12)
                clear * - r4376 e4377 e4378 b4379 b4380 b4381 b4382 d4355 d4351
                omega
              have d4383 : (x 17 3 && x 17 13).toNat = 0 := by
                have r4384 := hand2 (x 17 3) (x 17 13)
                have b4385 := hb (x 17 13)
                have b4386 := hb (x 17 3 && x 17 13)
                clear * - r4384 b4385 b4386 d4375
                omega
              have d4387 : (x 17 5).toNat = 0 := by
                have r4388 : (x 17 5).toNat ≤ (x 17 13).toNat := himp _ _ (hp5 17)
                have b4389 := hb (x 17 5)
                have b4390 := hb (x 17 13)
                clear * - r4388 b4389 b4390 d4375
                omega
              have d4391 : (x 17 5 && x 17 14).toNat = 0 := by
                have r4392 := hand1 (x 17 5) (x 17 14)
                have b4393 := hb (x 17 5)
                have b4394 := hb (x 17 5 && x 17 14)
                clear * - r4392 b4393 b4394 d4387
                omega
              have d4395 : (x 16 1 && x 16 14).toNat = 1 := by
                have r4396 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := by have q := hcov13 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4397 := hb (x 15 2)
                have b4398 := hb (x 17 13)
                have b4399 := hb (x 16 1 && x 16 14)
                clear * - r4396 b4397 b4398 b4399 d4375 d4300
                omega
              have d4400 : (x 16 14).toNat = 1 := by
                have r4401 := hand2 (x 16 1) (x 16 14)
                have b4402 := hb (x 16 14)
                have b4403 := hb (x 16 1 && x 16 14)
                clear * - r4401 b4402 b4403 d4395
                omega
              have d4404 : (x 15 1).toNat = 0 := by
                have r4405 : (x 16 14).toNat + (x 15 1).toNat = 1 := by have q := hd14 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4406 := hb (x 15 1)
                have b4407 := hb (x 16 14)
                clear * - r4405 b4406 b4407 d4400
                omega
              have d4408 : (x 15 1 && x 15 11).toNat = 0 := by
                have r4409 := hand1 (x 15 1) (x 15 11)
                have b4410 := hb (x 15 1)
                have b4411 := hb (x 15 1 && x 15 11)
                clear * - r4409 b4410 b4411 d4404
                omega
              have d4412 : (x 15 13).toNat = 0 := by
                have r4413 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
                have b4414 := hb (x 15 1)
                have b4415 := hb (x 15 13)
                clear * - r4413 b4414 b4415 d4404
                omega
              have d4416 : (x 15 5).toNat = 0 := by
                have r4417 : (x 15 5).toNat ≤ (x 15 13).toNat := himp _ _ (hp5 15)
                have b4418 := hb (x 15 5)
                have b4419 := hb (x 15 13)
                clear * - r4417 b4418 b4419 d4412
                omega
              have d4420 : (x 15 9).toNat = 0 := by
                have r4421 : (x 15 9).toNat ≤ (x 15 1).toNat := himp _ _ (hp9 15)
                have b4422 := hb (x 15 1)
                have b4423 := hb (x 15 9)
                clear * - r4421 b4422 b4423 d4404
                omega
              have d4424 : (x 16 1).toNat = 1 := by
                have r4425 := hand1 (x 16 1) (x 16 14)
                have b4426 := hb (x 16 1)
                have b4427 := hb (x 16 1 && x 16 14)
                clear * - r4425 b4426 b4427 d4395
                omega
              have d4428 : (x 17 14).toNat = 0 := by
                have r4429 : (x 17 14).toNat + (x 16 1).toNat = 1 := by have q := hd14 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4430 := hb (x 16 1)
                have b4431 := hb (x 17 14)
                clear * - r4429 b4430 b4431 d4424
                omega
              have d4432 : (x 17 1 && x 17 14).toNat = 0 := by
                have r4433 := hand2 (x 17 1) (x 17 14)
                have b4434 := hb (x 17 14)
                have b4435 := hb (x 17 1 && x 17 14)
                clear * - r4433 b4434 b4435 d4428
                omega
              have d4436 : (x 17 6).toNat = 0 := by
                have r4437 : (x 17 6).toNat ≤ (x 17 14).toNat := himp _ _ (hp6 17)
                have b4438 := hb (x 17 6)
                have b4439 := hb (x 17 14)
                clear * - r4437 b4438 b4439 d4428
                omega
              have d4440 : (x 17 2 && x 17 6).toNat = 0 := by
                have r4441 := hand2 (x 17 2) (x 17 6)
                have b4442 := hb (x 17 6)
                have b4443 := hb (x 17 2 && x 17 6)
                clear * - r4441 b4442 b4443 d4436
                omega
              have d4444 : (x 17 2).toNat = 0 := by
                have r4445 : (x 17 2).toNat ≤ (x 17 14).toNat := himp _ _ (hp2 17)
                have b4446 := hb (x 17 2)
                have b4447 := hb (x 17 14)
                clear * - r4445 b4446 b4447 d4428
                omega
              have d4448 : (x 16 2).toNat = 0 := by
                have r4449 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4450 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
                have e4451 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
                have b4452 := hb (x 15 3)
                have b4453 := hb (x 16 2)
                have b4454 := hb (x 17 13)
                have b4455 := hb (x 18 12)
                clear * - r4449 e4450 e4451 b4452 b4453 b4454 b4455 d4355 d4375 d4351
                omega
              have d4456 : (x 16 10).toNat = 0 := by
                have r4457 : (x 16 10).toNat ≤ (x 16 2).toNat := himp _ _ (hp10 16)
                have b4458 := hb (x 16 2)
                have b4459 := hb (x 16 10)
                clear * - r4457 b4458 b4459 d4448
                omega
              have d4460 : (x 18 13).toNat = 1 := by
                have r4461 : 1 ≤ (x 18 13).toNat + (x 17 1 && x 17 14).toNat + (x 16 2).toNat := by have q := hcov13 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4462 := hb (x 16 2)
                have b4463 := hb (x 18 13)
                have b4464 := hb (x 17 1 && x 17 14)
                clear * - r4461 b4462 b4463 b4464 d4432 d4448
                omega
              have d4465 : (x 19 12).toNat = 0 := by
                have r4466 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4467 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
                have e4468 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
                have b4469 := hb (x 16 3)
                have b4470 := hb (x 17 2)
                have b4471 := hb (x 18 13)
                have b4472 := hb (x 19 12)
                clear * - r4466 e4467 e4468 b4469 b4470 b4471 b4472 d4460 d4444
                omega
              have d4473 : (x 19 3 && x 19 12).toNat = 0 := by
                have r4474 := hand2 (x 19 3) (x 19 12)
                have b4475 := hb (x 19 12)
                have b4476 := hb (x 19 3 && x 19 12)
                clear * - r4474 b4475 b4476 d4465
                omega
              have d4477 : (x 19 4).toNat = 0 := by
                have r4478 : (x 19 4).toNat ≤ (x 19 12).toNat := himp _ _ (hp4 19)
                have b4479 := hb (x 19 4)
                have b4480 := hb (x 19 12)
                clear * - r4478 b4479 b4480 d4465
                omega
              have d4481 : (x 16 3).toNat = 0 := by
                have r4482 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4483 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
                have e4484 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
                have b4485 := hb (x 16 3)
                have b4486 := hb (x 17 2)
                have b4487 := hb (x 18 13)
                have b4488 := hb (x 19 12)
                clear * - r4482 e4483 e4484 b4485 b4486 b4487 b4488 d4465 d4460 d4444
                omega
              have d4489 : (x 16 3 && x 16 7).toNat = 0 := by
                have r4490 := hand1 (x 16 3) (x 16 7)
                have b4491 := hb (x 16 3)
                have b4492 := hb (x 16 3 && x 16 7)
                clear * - r4490 b4491 b4492 d4481
                omega
              have d4493 : (x 18 8).toNat = 0 := by
                have r4494 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4495 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
                have e4496 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
                have e4497 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
                have e4498 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
                have e4499 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
                have e4500 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
                have b4501 := hb (x 11 7)
                have b4502 := hb (x 12 6)
                have b4503 := hb (x 13 5)
                have b4504 := hb (x 14 4)
                have b4505 := hb (x 15 11)
                have b4506 := hb (x 16 10)
                have b4507 := hb (x 17 9)
                have b4508 := hb (x 18 8)
                clear * - r4494 e4495 e4496 e4497 e4498 e4499 e4500 b4501 b4502 b4503 b4504 b4505 b4506 b4507 b4508 d4456 d4344 d4231 d4251
                omega
              have d4509 : (x 17 9).toNat = 0 := by
                have r4510 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4511 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
                have e4512 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
                have e4513 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
                have e4514 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
                have e4515 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
                have e4516 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
                have b4517 := hb (x 11 7)
                have b4518 := hb (x 12 6)
                have b4519 := hb (x 13 5)
                have b4520 := hb (x 14 4)
                have b4521 := hb (x 15 11)
                have b4522 := hb (x 16 10)
                have b4523 := hb (x 17 9)
                have b4524 := hb (x 18 8)
                clear * - r4510 e4511 e4512 e4513 e4514 e4515 e4516 b4517 b4518 b4519 b4520 b4521 b4522 b4523 b4524 d4493 d4456 d4344 d4231 d4251
                omega
              have d4525 : (x 12 6).toNat = 0 := by
                have r4526 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4527 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
                have e4528 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
                have e4529 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
                have e4530 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
                have e4531 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
                have e4532 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
                have b4533 := hb (x 11 7)
                have b4534 := hb (x 12 6)
                have b4535 := hb (x 13 5)
                have b4536 := hb (x 14 4)
                have b4537 := hb (x 15 11)
                have b4538 := hb (x 16 10)
                have b4539 := hb (x 17 9)
                have b4540 := hb (x 18 8)
                clear * - r4526 e4527 e4528 e4529 e4530 e4531 e4532 b4533 b4534 b4535 b4536 b4537 b4538 b4539 b4540 d4493 d4509 d4456 d4344 d4231 d4251
                omega
              have d4541 : (x 11 7).toNat = 0 := by
                have r4542 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4543 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
                have e4544 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
                have e4545 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
                have e4546 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
                have e4547 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
                have e4548 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
                have b4549 := hb (x 11 7)
                have b4550 := hb (x 12 6)
                have b4551 := hb (x 13 5)
                have b4552 := hb (x 14 4)
                have b4553 := hb (x 15 11)
                have b4554 := hb (x 16 10)
                have b4555 := hb (x 17 9)
                have b4556 := hb (x 18 8)
                clear * - r4542 e4543 e4544 e4545 e4546 e4547 e4548 b4549 b4550 b4551 b4552 b4553 b4554 b4555 b4556 d4493 d4509 d4456 d4344 d4231 d4251 d4525
                omega
              have d4557 : (x 11 3 && x 11 7).toNat = 0 := by
                have r4558 := hand2 (x 11 3) (x 11 7)
                have b4559 := hb (x 11 7)
                have b4560 := hb (x 11 3 && x 11 7)
                clear * - r4558 b4559 b4560 d4541
                omega
              have d4561 : (x 7 7 && x 7 11).toNat = 1 := by
                have r4562 : 1 ≤ (x 14 4).toNat + (x 13 1 && x 13 5).toNat + (x 12 2 && x 12 6).toNat + (x 11 3 && x 11 7).toNat + (x 10 4 && x 10 8).toNat + (x 9 5 && x 9 9).toNat + (x 8 6 && x 8 10).toNat + (x 7 7 && x 7 11).toNat + (x 6 8 && x 6 12).toNat + (x 5 9 && x 5 13).toNat + (x 4 10 && x 4 14).toNat + (x 3 11).toNat := by have q := hcov4 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4563 : (x 13 1 && x 13 5).toNat = (x 13 5).toNat := handr _ _ (fun h => hp13 13 (hp5 13 (h)))
                have e4564 : (x 4 10 && x 4 14).toNat = (x 4 10).toNat := handl _ _ (fun h => hp2 4 (hp10 4 (h)))
                have b4565 := hb (x 3 11)
                have b4566 := hb (x 4 10)
                have b4567 := hb (x 13 5)
                have b4568 := hb (x 14 4)
                have b4569 := hb (x 12 2 && x 12 6)
                have b4570 := hb (x 11 3 && x 11 7)
                have b4571 := hb (x 10 4 && x 10 8)
                have b4572 := hb (x 9 5 && x 9 9)
                have b4573 := hb (x 8 6 && x 8 10)
                have b4574 := hb (x 7 7 && x 7 11)
                have b4575 := hb (x 6 8 && x 6 12)
                have b4576 := hb (x 5 9 && x 5 13)
                clear * - r4562 e4563 e4564 b4565 b4566 b4567 b4568 b4569 b4570 b4571 b4572 b4573 b4574 b4575 b4576 d4231 d4251 d4263 d4557 d4102 d4126 d4146 d3628 d3652 d3656 d3676
                omega
              have d4577 : (x 7 11).toNat = 1 := by
                have r4578 := hand2 (x 7 7) (x 7 11)
                have b4579 := hb (x 7 11)
                have b4580 := hb (x 7 7 && x 7 11)
                clear * - r4578 b4579 b4580 d4561
                omega
              have d4581 : (x 7 3).toNat = 1 := by
                have r4582 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
                have b4583 := hb (x 7 3)
                have b4584 := hb (x 7 11)
                clear * - r4582 b4583 b4584 d4577
                omega
              have d4585 : (x 10 12).toNat = 0 := by
                have r4586 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4587 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                have e4588 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                have b4589 := hb (x 7 3)
                have b4590 := hb (x 8 2)
                have b4591 := hb (x 9 13)
                have b4592 := hb (x 10 12)
                clear * - r4586 e4587 e4588 b4589 b4590 b4591 b4592 d4581
                omega
              have d4593 : (x 10 1 && x 10 12).toNat = 0 := by
                have r4594 := hand2 (x 10 1) (x 10 12)
                have b4595 := hb (x 10 12)
                have b4596 := hb (x 10 1 && x 10 12)
                clear * - r4594 b4595 b4596 d4585
                omega
              have d4597 : (x 7 4).toNat = 1 := by
                have r4598 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4599 := hb (x 7 4)
                have b4600 := hb (x 11 11)
                have b4601 := hb (x 10 1 && x 10 12)
                have b4602 := hb (x 9 2 && x 9 13)
                have b4603 := hb (x 8 3 && x 8 14)
                clear * - r4598 b4599 b4600 b4601 b4602 b4603 d4066 d4593 d4187 d4203
                omega
              have d4604 : (x 7 12).toNat = 1 := by
                have r4605 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
                have b4606 := hb (x 7 4)
                have b4607 := hb (x 7 12)
                clear * - r4605 b4606 b4607 d4597
                omega
              have d4608 : (x 6 13).toNat = 0 := by
                have r4609 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4610 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                have e4611 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                have b4612 := hb (x 4 3)
                have b4613 := hb (x 5 2)
                have b4614 := hb (x 6 13)
                have b4615 := hb (x 7 12)
                clear * - r4609 e4610 e4611 b4612 b4613 b4614 b4615 d4604
                omega
              have d4616 : (x 6 2 && x 6 13).toNat = 0 := by
                have r4617 := hand2 (x 6 2) (x 6 13)
                have b4618 := hb (x 6 13)
                have b4619 := hb (x 6 2 && x 6 13)
                clear * - r4617 b4618 b4619 d4608
                omega
              have d4620 : (x 6 5).toNat = 0 := by
                have r4621 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
                have b4622 := hb (x 6 5)
                have b4623 := hb (x 6 13)
                clear * - r4621 b4622 b4623 d4608
                omega
              have d4624 : (x 5 2).toNat = 0 := by
                have r4625 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4626 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                have e4627 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                have b4628 := hb (x 4 3)
                have b4629 := hb (x 5 2)
                have b4630 := hb (x 6 13)
                have b4631 := hb (x 7 12)
                clear * - r4625 e4626 e4627 b4628 b4629 b4630 b4631 d4604 d4608
                omega
              have d4632 : (x 11 8).toNat = 0 := by
                have r4633 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4634 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
                have e4635 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
                have e4636 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
                have e4637 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
                have e4638 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
                have e4639 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
                have b4640 := hb (x 4 7)
                have b4641 := hb (x 5 6)
                have b4642 := hb (x 6 5)
                have b4643 := hb (x 7 4)
                have b4644 := hb (x 8 11)
                have b4645 := hb (x 9 10)
                have b4646 := hb (x 10 9)
                have b4647 := hb (x 11 8)
                clear * - r4633 e4634 e4635 e4636 e4637 e4638 e4639 b4640 b4641 b4642 b4643 b4644 b4645 b4646 b4647 d4191 d4207 d4597 d4620
                omega
              have d4648 : (x 11 8 && x 11 12).toNat = 0 := by
                have r4649 := hand1 (x 11 8) (x 11 12)
                have b4650 := hb (x 11 8)
                have b4651 := hb (x 11 8 && x 11 12)
                clear * - r4649 b4650 b4651 d4632
                omega
              have d4652 : (x 18 5).toNat = 1 := by
                have r4653 : 1 ≤ (x 19 4).toNat + (x 18 1 && x 18 5).toNat + (x 17 2 && x 17 6).toNat + (x 16 3 && x 16 7).toNat + (x 15 4 && x 15 8).toNat + (x 14 5 && x 14 9).toNat + (x 13 6 && x 13 10).toNat + (x 12 7 && x 12 11).toNat + (x 11 8 && x 11 12).toNat + (x 10 9 && x 10 13).toNat + (x 9 10 && x 9 14).toNat + (x 8 11).toNat := by have q := hcov4 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4654 : (x 18 1 && x 18 5).toNat = (x 18 5).toNat := handr _ _ (fun h => hp13 18 (hp5 18 (h)))
                have e4655 : (x 9 10 && x 9 14).toNat = (x 9 10).toNat := handl _ _ (fun h => hp2 9 (hp10 9 (h)))
                have b4656 := hb (x 8 11)
                have b4657 := hb (x 9 10)
                have b4658 := hb (x 18 5)
                have b4659 := hb (x 19 4)
                have b4660 := hb (x 17 2 && x 17 6)
                have b4661 := hb (x 16 3 && x 16 7)
                have b4662 := hb (x 15 4 && x 15 8)
                have b4663 := hb (x 14 5 && x 14 9)
                have b4664 := hb (x 13 6 && x 13 10)
                have b4665 := hb (x 12 7 && x 12 11)
                have b4666 := hb (x 11 8 && x 11 12)
                have b4667 := hb (x 10 9 && x 10 13)
                clear * - r4653 e4654 e4655 b4656 b4657 b4658 b4659 b4660 b4661 b4662 b4663 b4664 b4665 b4666 b4667 d4477 d4440 d4489 d3865 d3885 d3909 d3933 d4648 d4175 d4191 d4207
                omega
              have d4668 : (x 23 8).toNat = 0 := by
                have r4669 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4670 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
                have e4671 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
                have e4672 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
                have e4673 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
                have e4674 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
                have e4675 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
                have b4676 := hb (x 16 7)
                have b4677 := hb (x 17 6)
                have b4678 := hb (x 18 5)
                have b4679 := hb (x 19 4)
                have b4680 := hb (x 20 11)
                have b4681 := hb (x 21 10)
                have b4682 := hb (x 22 9)
                have b4683 := hb (x 23 8)
                clear * - r4669 e4670 e4671 e4672 e4673 e4674 e4675 b4676 b4677 b4678 b4679 b4680 b4681 b4682 b4683 d4477 d4652 d4436
                omega
              have d4684 : (x 22 9).toNat = 0 := by
                have r4685 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4686 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
                have e4687 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
                have e4688 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
                have e4689 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
                have e4690 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
                have e4691 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
                have b4692 := hb (x 16 7)
                have b4693 := hb (x 17 6)
                have b4694 := hb (x 18 5)
                have b4695 := hb (x 19 4)
                have b4696 := hb (x 20 11)
                have b4697 := hb (x 21 10)
                have b4698 := hb (x 22 9)
                have b4699 := hb (x 23 8)
                clear * - r4685 e4686 e4687 e4688 e4689 e4690 e4691 b4692 b4693 b4694 b4695 b4696 b4697 b4698 b4699 d4668 d4477 d4652 d4436
                omega
              have d4700 : (x 21 10).toNat = 0 := by
                have r4701 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4702 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
                have e4703 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
                have e4704 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
                have e4705 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
                have e4706 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
                have e4707 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
                have b4708 := hb (x 16 7)
                have b4709 := hb (x 17 6)
                have b4710 := hb (x 18 5)
                have b4711 := hb (x 19 4)
                have b4712 := hb (x 20 11)
                have b4713 := hb (x 21 10)
                have b4714 := hb (x 22 9)
                have b4715 := hb (x 23 8)
                clear * - r4701 e4702 e4703 e4704 e4705 e4706 e4707 b4708 b4709 b4710 b4711 b4712 b4713 b4714 b4715 d4668 d4684 d4477 d4652 d4436
                omega
              have d4716 : (x 21 1 && x 21 10).toNat = 0 := by
                have r4717 := hand2 (x 21 1) (x 21 10)
                have b4718 := hb (x 21 10)
                have b4719 := hb (x 21 1 && x 21 10)
                clear * - r4717 b4718 b4719 d4700
                omega
              have d4720 : (x 20 11).toNat = 0 := by
                have r4721 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4722 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
                have e4723 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
                have e4724 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
                have e4725 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
                have e4726 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
                have e4727 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
                have b4728 := hb (x 16 7)
                have b4729 := hb (x 17 6)
                have b4730 := hb (x 18 5)
                have b4731 := hb (x 19 4)
                have b4732 := hb (x 20 11)
                have b4733 := hb (x 21 10)
                have b4734 := hb (x 22 9)
                have b4735 := hb (x 23 8)
                clear * - r4721 e4722 e4723 e4724 e4725 e4726 e4727 b4728 b4729 b4730 b4731 b4732 b4733 b4734 b4735 d4668 d4684 d4700 d4477 d4652 d4436
                omega
              have d4736 : (x 20 2 && x 20 11).toNat = 0 := by
                have r4737 := hand2 (x 20 2) (x 20 11)
                have b4738 := hb (x 20 11)
                have b4739 := hb (x 20 2 && x 20 11)
                clear * - r4737 b4738 b4739 d4720
                omega
              have d4740 : (x 16 6).toNat = 1 := by
                have r4741 : 1 ≤ (x 22 9).toNat + (x 21 1 && x 21 10).toNat + (x 20 2 && x 20 11).toNat + (x 19 3 && x 19 12).toNat + (x 18 4 && x 18 13).toNat + (x 17 5 && x 17 14).toNat + (x 16 6).toNat := by have q := hcov9 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4742 := hb (x 16 6)
                have b4743 := hb (x 22 9)
                have b4744 := hb (x 21 1 && x 21 10)
                have b4745 := hb (x 20 2 && x 20 11)
                have b4746 := hb (x 19 3 && x 19 12)
                have b4747 := hb (x 18 4 && x 18 13)
                have b4748 := hb (x 17 5 && x 17 14)
                clear * - r4741 b4742 b4743 b4744 b4745 b4746 b4747 b4748 d4684 d4716 d4736 d4473 d4371 d4391
                omega
              have d4749 : (x 22 8).toNat = 0 := by
                have r4750 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4751 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
                have e4752 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
                have e4753 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
                have e4754 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
                have e4755 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
                have e4756 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
                have b4757 := hb (x 15 7)
                have b4758 := hb (x 16 6)
                have b4759 := hb (x 17 5)
                have b4760 := hb (x 18 4)
                have b4761 := hb (x 19 11)
                have b4762 := hb (x 20 10)
                have b4763 := hb (x 21 9)
                have b4764 := hb (x 22 8)
                clear * - r4750 e4751 e4752 e4753 e4754 e4755 e4756 b4757 b4758 b4759 b4760 b4761 b4762 b4763 b4764 d4367 d4387 d4740
                omega
              have d4765 : (x 21 9).toNat = 0 := by
                have r4766 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4767 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
                have e4768 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
                have e4769 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
                have e4770 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
                have e4771 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
                have e4772 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
                have b4773 := hb (x 15 7)
                have b4774 := hb (x 16 6)
                have b4775 := hb (x 17 5)
                have b4776 := hb (x 18 4)
                have b4777 := hb (x 19 11)
                have b4778 := hb (x 20 10)
                have b4779 := hb (x 21 9)
                have b4780 := hb (x 22 8)
                clear * - r4766 e4767 e4768 e4769 e4770 e4771 e4772 b4773 b4774 b4775 b4776 b4777 b4778 b4779 b4780 d4749 d4367 d4387 d4740
                omega
              have d4781 : (x 20 10).toNat = 0 := by
                have r4782 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4783 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
                have e4784 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
                have e4785 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
                have e4786 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
                have e4787 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
                have e4788 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
                have b4789 := hb (x 15 7)
                have b4790 := hb (x 16 6)
                have b4791 := hb (x 17 5)
                have b4792 := hb (x 18 4)
                have b4793 := hb (x 19 11)
                have b4794 := hb (x 20 10)
                have b4795 := hb (x 21 9)
                have b4796 := hb (x 22 8)
                clear * - r4782 e4783 e4784 e4785 e4786 e4787 e4788 b4789 b4790 b4791 b4792 b4793 b4794 b4795 b4796 d4749 d4765 d4367 d4387 d4740
                omega
              have d4797 : (x 19 11).toNat = 0 := by
                have r4798 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4799 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
                have e4800 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
                have e4801 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
                have e4802 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
                have e4803 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
                have e4804 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
                have b4805 := hb (x 15 7)
                have b4806 := hb (x 16 6)
                have b4807 := hb (x 17 5)
                have b4808 := hb (x 18 4)
                have b4809 := hb (x 19 11)
                have b4810 := hb (x 20 10)
                have b4811 := hb (x 21 9)
                have b4812 := hb (x 22 8)
                clear * - r4798 e4799 e4800 e4801 e4802 e4803 e4804 b4805 b4806 b4807 b4808 b4809 b4810 b4811 b4812 d4749 d4765 d4781 d4367 d4387 d4740
                omega
              have d4813 : (x 19 1 && x 19 11).toNat = 0 := by
                have r4814 := hand2 (x 19 1) (x 19 11)
                have b4815 := hb (x 19 11)
                have b4816 := hb (x 19 1 && x 19 11)
                clear * - r4814 b4815 b4816 d4797
                omega
              have d4817 : (x 16 4 && x 16 14).toNat = 1 := by
                have r4818 : 1 ≤ (x 20 10).toNat + (x 19 1 && x 19 11).toNat + (x 18 2 && x 18 12).toNat + (x 17 3 && x 17 13).toNat + (x 16 4 && x 16 14).toNat + (x 15 5).toNat := by have q := hcov10 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4819 := hb (x 15 5)
                have b4820 := hb (x 20 10)
                have b4821 := hb (x 19 1 && x 19 11)
                have b4822 := hb (x 18 2 && x 18 12)
                have b4823 := hb (x 17 3 && x 17 13)
                have b4824 := hb (x 16 4 && x 16 14)
                clear * - r4818 b4819 b4820 b4821 b4822 b4823 b4824 d4781 d4813 d4363 d4383 d4416
                omega
              have d4825 : (x 16 4).toNat = 1 := by
                have r4826 := hand1 (x 16 4) (x 16 14)
                have b4827 := hb (x 16 4)
                have b4828 := hb (x 16 4 && x 16 14)
                clear * - r4826 b4827 b4828 d4817
                omega
              have d4829 : (x 16 12).toNat = 1 := by
                have r4830 : (x 16 4).toNat ≤ (x 16 12).toNat := himp _ _ (hp4 16)
                have b4831 := hb (x 16 4)
                have b4832 := hb (x 16 12)
                clear * - r4830 b4831 b4832 d4825
                omega
              have d4833 : (x 14 2).toNat = 0 := by
                have r4834 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4835 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                have e4836 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                have b4837 := hb (x 13 3)
                have b4838 := hb (x 14 2)
                have b4839 := hb (x 15 13)
                have b4840 := hb (x 16 12)
                clear * - r4834 e4835 e4836 b4837 b4838 b4839 b4840 d4829 d4412
                omega
              have d4841 : (x 14 10).toNat = 0 := by
                have r4842 : (x 14 10).toNat ≤ (x 14 2).toNat := himp _ _ (hp10 14)
                have b4843 := hb (x 14 2)
                have b4844 := hb (x 14 10)
                clear * - r4842 b4843 b4844 d4833
                omega
              have d4845 : (x 14 1 && x 14 10).toNat = 0 := by
                have r4846 := hand2 (x 14 1) (x 14 10)
                have b4847 := hb (x 14 10)
                have b4848 := hb (x 14 1 && x 14 10)
                clear * - r4846 b4847 b4848 d4841
                omega
              have d4849 : (x 12 3 && x 12 12).toNat = 1 := by
                have r4850 : 1 ≤ (x 15 9).toNat + (x 14 1 && x 14 10).toNat + (x 13 2 && x 13 11).toNat + (x 12 3 && x 12 12).toNat + (x 11 4 && x 11 13).toNat + (x 10 5 && x 10 14).toNat + (x 9 6).toNat := by have q := hcov9 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4851 := hb (x 9 6)
                have b4852 := hb (x 15 9)
                have b4853 := hb (x 14 1 && x 14 10)
                have b4854 := hb (x 13 2 && x 13 11)
                have b4855 := hb (x 12 3 && x 12 12)
                have b4856 := hb (x 11 4 && x 11 13)
                have b4857 := hb (x 10 5 && x 10 14)
                clear * - r4850 b4851 b4852 b4853 b4854 b4855 b4856 b4857 d4420 d4845 d4320 d3953 d3977 d3985
                omega
              have d4858 : (x 12 12).toNat = 1 := by
                have r4859 := hand2 (x 12 3) (x 12 12)
                have b4860 := hb (x 12 12)
                have b4861 := hb (x 12 3 && x 12 12)
                clear * - r4859 b4860 b4861 d4849
                omega
              have d4862 : (x 11 13).toNat = 0 := by
                have r4863 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4864 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
                have e4865 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
                have b4866 := hb (x 9 3)
                have b4867 := hb (x 10 2)
                have b4868 := hb (x 11 13)
                have b4869 := hb (x 12 12)
                clear * - r4863 e4864 e4865 b4866 b4867 b4868 b4869 d4858
                omega
              have d4870 : (x 11 5).toNat = 0 := by
                have r4871 : (x 11 5).toNat ≤ (x 11 13).toNat := himp _ _ (hp5 11)
                have b4872 := hb (x 11 5)
                have b4873 := hb (x 11 13)
                clear * - r4871 b4872 b4873 d4862
                omega
              have d4874 : (x 12 4 && x 12 14).toNat = 1 := by
                have r4875 : 1 ≤ (x 16 10).toNat + (x 15 1 && x 15 11).toNat + (x 14 2 && x 14 12).toNat + (x 13 3 && x 13 13).toNat + (x 12 4 && x 12 14).toNat + (x 11 5).toNat := by have q := hcov10 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4876 := hb (x 11 5)
                have b4877 := hb (x 16 10)
                have b4878 := hb (x 15 1 && x 15 11)
                have b4879 := hb (x 14 2 && x 14 12)
                have b4880 := hb (x 13 3 && x 13 13)
                have b4881 := hb (x 12 4 && x 12 14)
                clear * - r4875 b4876 b4877 b4878 b4879 b4880 b4881 d4456 d4408 d4227 d4247 d4870
                omega
              have d4882 : (x 12 14).toNat = 1 := by
                have r4883 := hand2 (x 12 4) (x 12 14)
                have b4884 := hb (x 12 14)
                have b4885 := hb (x 12 4 && x 12 14)
                clear * - r4883 b4884 b4885 d4874
                omega
              have d4886 : (x 11 1).toNat = 0 := by
                have r4887 : (x 12 14).toNat + (x 11 1).toNat = 1 := by have q := hd14 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4888 := hb (x 11 1)
                have b4889 := hb (x 12 14)
                clear * - r4887 b4888 b4889 d4882
                omega
              have d4890 : (x 11 1 && x 11 12).toNat = 0 := by
                have r4891 := hand1 (x 11 1) (x 11 12)
                have b4892 := hb (x 11 1)
                have b4893 := hb (x 11 1 && x 11 12)
                clear * - r4891 b4892 b4893 d4886
                omega
              have d4894 : (x 10 1 && x 10 14).toNat = 1 := by
                have r4895 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4896 := hb (x 9 2)
                have b4897 := hb (x 11 13)
                have b4898 := hb (x 10 1 && x 10 14)
                clear * - r4895 b4896 b4897 b4898 d4862 d4179
                omega
              have d4899 : (x 10 14).toNat = 1 := by
                have r4900 := hand2 (x 10 1) (x 10 14)
                have b4901 := hb (x 10 14)
                have b4902 := hb (x 10 1 && x 10 14)
                clear * - r4900 b4901 b4902 d4894
                omega
              have d4903 : (x 9 1).toNat = 0 := by
                have r4904 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4905 := hb (x 9 1)
                have b4906 := hb (x 10 14)
                clear * - r4904 b4905 b4906 d4899
                omega
              have d4907 : (x 9 1 && x 9 14).toNat = 0 := by
                have r4908 := hand1 (x 9 1) (x 9 14)
                have b4909 := hb (x 9 1)
                have b4910 := hb (x 9 1 && x 9 14)
                clear * - r4908 b4909 b4910 d4903
                omega
              have d4911 : (x 8 2).toNat = 1 := by
                have r4912 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4913 := hb (x 8 2)
                have b4914 := hb (x 10 13)
                have b4915 := hb (x 9 1 && x 9 14)
                clear * - r4912 b4913 b4914 b4915 d4163 d4907
                omega
              have d4916 : (x 8 14).toNat = 1 := by
                have r4917 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
                have b4918 := hb (x 8 2)
                have b4919 := hb (x 8 14)
                clear * - r4917 b4918 b4919 d4911
                omega
              have d4920 : (x 7 1).toNat = 0 := by
                have r4921 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4922 := hb (x 7 1)
                have b4923 := hb (x 8 14)
                clear * - r4921 b4922 b4923 d4916
                omega
              have d4924 : (x 7 1 && x 7 14).toNat = 0 := by
                have r4925 := hand1 (x 7 1) (x 7 14)
                have b4926 := hb (x 7 1)
                have b4927 := hb (x 7 1 && x 7 14)
                clear * - r4925 b4926 b4927 d4920
                omega
              have d4928 : (x 7 1 && x 7 12).toNat = 0 := by
                have r4929 := hand1 (x 7 1) (x 7 12)
                have b4930 := hb (x 7 1)
                have b4931 := hb (x 7 1 && x 7 12)
                clear * - r4929 b4930 b4931 d4920
                omega
              have d4932 : (x 5 3 && x 5 14).toNat = 1 := by
                have r4933 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4934 := hb (x 4 4)
                have b4935 := hb (x 8 11)
                have b4936 := hb (x 7 1 && x 7 12)
                have b4937 := hb (x 6 2 && x 6 13)
                have b4938 := hb (x 5 3 && x 5 14)
                clear * - r4933 b4934 b4935 b4936 b4937 b4938 d4207 d4928 d4616 d3539
                omega
              have d4939 : (x 5 14).toNat = 1 := by
                have r4940 := hand2 (x 5 3) (x 5 14)
                have b4941 := hb (x 5 14)
                have b4942 := hb (x 5 3 && x 5 14)
                clear * - r4940 b4941 b4942 d4932
                omega
              have d4943 : (x 4 1).toNat = 0 := by
                have r4944 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4945 := hb (x 4 1)
                have b4946 := hb (x 5 14)
                clear * - r4944 b4945 b4946 d4939
                omega
              have d4947 : (x 4 13).toNat = 0 := by
                have r4948 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
                have b4949 := hb (x 4 1)
                have b4950 := hb (x 4 13)
                clear * - r4948 b4949 b4950 d4943
                omega
              have d4951 : (x 3 1 && x 3 14).toNat = 1 := by
                have r4952 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4953 := hb (x 2 2)
                have b4954 := hb (x 4 13)
                have b4955 := hb (x 3 1 && x 3 14)
                clear * - r4952 b4953 b4954 b4955 d4947 d2688
                omega
              have d4956 : (x 3 1).toNat = 1 := by
                have r4957 := hand1 (x 3 1) (x 3 14)
                have b4958 := hb (x 3 1)
                have b4959 := hb (x 3 1 && x 3 14)
                clear * - r4957 b4958 b4959 d4951
                omega
              have d4960 : (x 4 14).toNat = 0 := by
                have r4961 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4962 := hb (x 3 1)
                have b4963 := hb (x 4 14)
                clear * - r4961 b4962 b4963 d4956
                omega
              have d4964 : (x 4 2).toNat = 0 := by
                have r4965 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
                have b4966 := hb (x 4 2)
                have b4967 := hb (x 4 14)
                clear * - r4965 b4966 b4967 d4960
                omega
              have d4968 : (x 5 1 && x 5 14).toNat = 1 := by
                have r4969 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4970 := hb (x 4 2)
                have b4971 := hb (x 6 13)
                have b4972 := hb (x 5 1 && x 5 14)
                clear * - r4969 b4970 b4971 b4972 d4608 d4964
                omega
              have d4973 : (x 5 1).toNat = 1 := by
                have r4974 := hand1 (x 5 1) (x 5 14)
                have b4975 := hb (x 5 1)
                have b4976 := hb (x 5 1 && x 5 14)
                clear * - r4974 b4975 b4976 d4968
                omega
              have d4977 : (x 6 14).toNat = 0 := by
                have r4978 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4979 := hb (x 5 1)
                have b4980 := hb (x 6 14)
                clear * - r4978 b4979 b4980 d4973
                omega
              have d4981 : (x 6 1 && x 6 14).toNat = 0 := by
                have r4982 := hand2 (x 6 1) (x 6 14)
                have b4983 := hb (x 6 14)
                have b4984 := hb (x 6 1 && x 6 14)
                clear * - r4982 b4983 b4984 d4977
                omega
              have d4985 : (x 7 13).toNat = 1 := by
                have r4986 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4987 := hb (x 5 2)
                have b4988 := hb (x 7 13)
                have b4989 := hb (x 6 1 && x 6 14)
                clear * - r4986 b4987 b4988 b4989 d4981 d4624
                omega
              have d4990 : (x 8 12).toNat = 0 := by
                have r4991 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4992 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                have e4993 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                have b4994 := hb (x 5 3)
                have b4995 := hb (x 6 2)
                have b4996 := hb (x 7 13)
                have b4997 := hb (x 8 12)
                clear * - r4991 e4992 e4993 b4994 b4995 b4996 b4997 d4985
                omega
              have d4998 : (x 8 4).toNat = 0 := by
                have r4999 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
                have b5000 := hb (x 8 4)
                have b5001 := hb (x 8 12)
                clear * - r4999 b5000 b5001 d4990
                omega
              have d5002 : (x 9 3 && x 9 14).toNat = 1 := by
                have r5003 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b5004 := hb (x 8 4)
                have b5005 := hb (x 12 11)
                have b5006 := hb (x 11 1 && x 11 12)
                have b5007 := hb (x 10 2 && x 10 13)
                have b5008 := hb (x 9 3 && x 9 14)
                clear * - r5003 b5004 b5005 b5006 b5007 b5008 d3913 d4890 d4171 d4998
                omega
              have d5009 : (x 9 14).toNat = 1 := by
                have r5010 := hand2 (x 9 3) (x 9 14)
                have b5011 := hb (x 9 14)
                have b5012 := hb (x 9 3 && x 9 14)
                clear * - r5010 b5011 b5012 d5002
                omega
              have d5013 : (x 8 1).toNat = 0 := by
                have r5014 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b5015 := hb (x 8 1)
                have b5016 := hb (x 9 14)
                clear * - r5014 b5015 b5016 d5009
                omega
              have d5017 : (x 8 13).toNat = 0 := by
                have r5018 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
                have b5019 := hb (x 8 1)
                have b5020 := hb (x 8 13)
                clear * - r5018 b5019 b5020 d5013
                omega
              have d5021 : (x 6 2).toNat = 1 := by
                have r5022 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b5023 := hb (x 6 2)
                have b5024 := hb (x 8 13)
                have b5025 := hb (x 7 1 && x 7 14)
                clear * - r5022 b5023 b5024 b5025 d5017 d4924
                omega
              have r5026 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e5027 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
              have e5028 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
              have b5029 := hb (x 5 3)
              have b5030 := hb (x 6 2)
              have b5031 := hb (x 7 13)
              have b5032 := hb (x 8 12)
              linarith only [r5026, e5027, e5028, b5029, b5030, b5031, b5032, d4990, d4985, d5021]
            · have f5033 : (x (-1) 8).toNat = 1 := by rw [h4005]; rfl
              have d5034 : (x (-2) 9).toNat = 0 := by
                have r5035 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e5036 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e5037 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e5038 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e5039 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e5040 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e5041 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have b5042 := hb (x (-8) 7)
                have b5043 := hb (x (-7) 6)
                have b5044 := hb (x (-6) 5)
                have b5045 := hb (x (-5) 4)
                have b5046 := hb (x (-4) 11)
                have b5047 := hb (x (-3) 10)
                have b5048 := hb (x (-2) 9)
                have b5049 := hb (x (-1) 8)
                clear * - r5035 e5036 e5037 e5038 e5039 e5040 e5041 b5042 b5043 b5044 b5045 b5046 b5047 b5048 b5049 f5033
                omega
              have d5050 : (x (-2) 5 && x (-2) 9).toNat = 0 := by
                have r5051 := hand2 (x (-2) 5) (x (-2) 9)
                have b5052 := hb (x (-2) 9)
                have b5053 := hb (x (-2) 5 && x (-2) 9)
                clear * - r5051 b5052 b5053 d5034
                omega
              have d5054 : (x (-3) 10).toNat = 0 := by
                have r5055 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e5056 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e5057 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e5058 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e5059 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e5060 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e5061 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have b5062 := hb (x (-8) 7)
                have b5063 := hb (x (-7) 6)
                have b5064 := hb (x (-6) 5)
                have b5065 := hb (x (-5) 4)
                have b5066 := hb (x (-4) 11)
                have b5067 := hb (x (-3) 10)
                have b5068 := hb (x (-2) 9)
                have b5069 := hb (x (-1) 8)
                clear * - r5055 e5056 e5057 e5058 e5059 e5060 e5061 b5062 b5063 b5064 b5065 b5066 b5067 b5068 b5069 f5033 d5034
                omega
              have d5070 : (x (-3) 6 && x (-3) 10).toNat = 0 := by
                have r5071 := hand2 (x (-3) 6) (x (-3) 10)
                have b5072 := hb (x (-3) 10)
                have b5073 := hb (x (-3) 6 && x (-3) 10)
                clear * - r5071 b5072 b5073 d5054
                omega
              have d5074 : (x (-4) 11).toNat = 0 := by
                have r5075 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e5076 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e5077 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e5078 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e5079 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e5080 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e5081 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have b5082 := hb (x (-8) 7)
                have b5083 := hb (x (-7) 6)
                have b5084 := hb (x (-6) 5)
                have b5085 := hb (x (-5) 4)
                have b5086 := hb (x (-4) 11)
                have b5087 := hb (x (-3) 10)
                have b5088 := hb (x (-2) 9)
                have b5089 := hb (x (-1) 8)
                clear * - r5075 e5076 e5077 e5078 e5079 e5080 e5081 b5082 b5083 b5084 b5085 b5086 b5087 b5088 b5089 f5033 d5034 d5054
                omega
              have d5090 : (x (-4) 7 && x (-4) 11).toNat = 0 := by
                have r5091 := hand2 (x (-4) 7) (x (-4) 11)
                have b5092 := hb (x (-4) 11)
                have b5093 := hb (x (-4) 7 && x (-4) 11)
                clear * - r5091 b5092 b5093 d5074
                omega
              have d5094 : (x (-5) 4).toNat = 0 := by
                have r5095 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e5096 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e5097 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e5098 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e5099 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e5100 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e5101 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have b5102 := hb (x (-8) 7)
                have b5103 := hb (x (-7) 6)
                have b5104 := hb (x (-6) 5)
                have b5105 := hb (x (-5) 4)
                have b5106 := hb (x (-4) 11)
                have b5107 := hb (x (-3) 10)
                have b5108 := hb (x (-2) 9)
                have b5109 := hb (x (-1) 8)
                clear * - r5095 e5096 e5097 e5098 e5099 e5100 e5101 b5102 b5103 b5104 b5105 b5106 b5107 b5108 b5109 f5033 d5034 d5054 d5074
                omega
              have d5110 : (x (-5) 4 && x (-5) 11).toNat = 0 := by
                have r5111 := hand1 (x (-5) 4) (x (-5) 11)
                have b5112 := hb (x (-5) 4)
                have b5113 := hb (x (-5) 4 && x (-5) 11)
                clear * - r5111 b5112 b5113 d5094
                omega
              have d5114 : (x (-5) 4 && x (-5) 8).toNat = 0 := by
                have r5115 := hand1 (x (-5) 4) (x (-5) 8)
                have b5116 := hb (x (-5) 4)
                have b5117 := hb (x (-5) 4 && x (-5) 8)
                clear * - r5115 b5116 b5117 d5094
                omega
              have d5118 : (x (-6) 5).toNat = 0 := by
                have r5119 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e5120 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e5121 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e5122 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e5123 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e5124 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e5125 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have b5126 := hb (x (-8) 7)
                have b5127 := hb (x (-7) 6)
                have b5128 := hb (x (-6) 5)
                have b5129 := hb (x (-5) 4)
                have b5130 := hb (x (-4) 11)
                have b5131 := hb (x (-3) 10)
                have b5132 := hb (x (-2) 9)
                have b5133 := hb (x (-1) 8)
                clear * - r5119 e5120 e5121 e5122 e5123 e5124 e5125 b5126 b5127 b5128 b5129 b5130 b5131 b5132 b5133 f5033 d5034 d5054 d5074 d5094
                omega
              have d5134 : (x (-6) 5 && x (-6) 12).toNat = 0 := by
                have r5135 := hand1 (x (-6) 5) (x (-6) 12)
                have b5136 := hb (x (-6) 5)
                have b5137 := hb (x (-6) 5 && x (-6) 12)
                clear * - r5135 b5136 b5137 d5118
                omega
              have d5138 : (x (-6) 5 && x (-6) 9).toNat = 0 := by
                have r5139 := hand1 (x (-6) 5) (x (-6) 9)
                have b5140 := hb (x (-6) 5)
                have b5141 := hb (x (-6) 5 && x (-6) 9)
                clear * - r5139 b5140 b5141 d5118
                omega
              have d5142 : (x (-7) 6).toNat = 0 := by
                have r5143 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e5144 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e5145 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e5146 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e5147 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e5148 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e5149 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have b5150 := hb (x (-8) 7)
                have b5151 := hb (x (-7) 6)
                have b5152 := hb (x (-6) 5)
                have b5153 := hb (x (-5) 4)
                have b5154 := hb (x (-4) 11)
                have b5155 := hb (x (-3) 10)
                have b5156 := hb (x (-2) 9)
                have b5157 := hb (x (-1) 8)
                clear * - r5143 e5144 e5145 e5146 e5147 e5148 e5149 b5150 b5151 b5152 b5153 b5154 b5155 b5156 b5157 f5033 d5034 d5054 d5074 d5094 d5118
                omega
              have d5158 : (x (-7) 6 && x (-7) 13).toNat = 0 := by
                have r5159 := hand1 (x (-7) 6) (x (-7) 13)
                have b5160 := hb (x (-7) 6)
                have b5161 := hb (x (-7) 6 && x (-7) 13)
                clear * - r5159 b5160 b5161 d5142
                omega
              have d5162 : (x (-7) 6 && x (-7) 10).toNat = 0 := by
                have r5163 := hand1 (x (-7) 6) (x (-7) 10)
                have b5164 := hb (x (-7) 6)
                have b5165 := hb (x (-7) 6 && x (-7) 10)
                clear * - r5163 b5164 b5165 d5142
                omega
              have d5166 : (x (-8) 7).toNat = 0 := by
                have r5167 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e5168 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e5169 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e5170 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e5171 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e5172 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e5173 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have b5174 := hb (x (-8) 7)
                have b5175 := hb (x (-7) 6)
                have b5176 := hb (x (-6) 5)
                have b5177 := hb (x (-5) 4)
                have b5178 := hb (x (-4) 11)
                have b5179 := hb (x (-3) 10)
                have b5180 := hb (x (-2) 9)
                have b5181 := hb (x (-1) 8)
                clear * - r5167 e5168 e5169 e5170 e5171 e5172 e5173 b5174 b5175 b5176 b5177 b5178 b5179 b5180 b5181 f5033 d5034 d5054 d5074 d5094 d5118 d5142
                omega
              have d5182 : (x (-8) 7 && x (-8) 14).toNat = 0 := by
                have r5183 := hand1 (x (-8) 7) (x (-8) 14)
                have b5184 := hb (x (-8) 7)
                have b5185 := hb (x (-8) 7 && x (-8) 14)
                clear * - r5183 b5184 b5185 d5166
                omega
              have d5186 : (x (-8) 7 && x (-8) 11).toNat = 0 := by
                have r5187 := hand1 (x (-8) 7) (x (-8) 11)
                have b5188 := hb (x (-8) 7)
                have b5189 := hb (x (-8) 7 && x (-8) 11)
                clear * - r5187 b5188 b5189 d5166
                omega
              have r5190 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r5191 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r5192 : (x 5 1).toNat + (x 4 2).toNat + (x 3 3).toNat + (x 2 4).toNat + (x 1 5).toNat + (x 0 6).toNat + (x (-1) 7).toNat + (x (-2) 8).toNat + (x (-3) 9).toNat + (x (-4) 10).toNat + (x (-5) 11).toNat + (x (-6) 12).toNat + (x (-7) 13).toNat + (x (-8) 14).toNat = 3 := by have q := hcount 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r5193 : (x 6 1).toNat + (x 5 2).toNat + (x 4 3).toNat + (x 3 4).toNat + (x 2 5).toNat + (x 1 6).toNat + (x 0 7).toNat + (x (-1) 8).toNat + (x (-2) 9).toNat + (x (-3) 10).toNat + (x (-4) 11).toNat + (x (-5) 12).toNat + (x (-6) 13).toNat + (x (-7) 14).toNat = 3 := by have q := hcount 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r5194 : (x 16 1).toNat + (x 15 2).toNat + (x 14 3).toNat + (x 13 4).toNat + (x 12 5).toNat + (x 11 6).toNat + (x 10 7).toNat + (x 9 8).toNat + (x 8 9).toNat + (x 7 10).toNat + (x 6 11).toNat + (x 5 12).toNat + (x 4 13).toNat + (x 3 14).toNat = 3 := by have q := hcount 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r5195 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e5196 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
              have e5197 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
              have e5198 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
              have e5199 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
              have e5200 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
              have e5201 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
              have r5202 : (x (-5) 8).toNat + (x (-6) 1 && x (-6) 9).toNat + (x (-7) 2 && x (-7) 10).toNat + (x (-8) 3 && x (-8) 11).toNat + (x (-9) 4 && x (-9) 12).toNat + (x (-10) 5 && x (-10) 13).toNat + (x (-11) 6 && x (-11) 14).toNat + (x (-12) 7).toNat = 1 := by have q := hd8 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e5203 : (x (-6) 1 && x (-6) 9).toNat = (x (-6) 9).toNat := handr _ _ (fun h => hp9 (-6) (h))
              have e5204 : (x (-7) 2 && x (-7) 10).toNat = (x (-7) 10).toNat := handr _ _ (fun h => hp10 (-7) (h))
              have e5205 : (x (-8) 3 && x (-8) 11).toNat = (x (-8) 11).toNat := handr _ _ (fun h => hp11 (-8) (h))
              have e5206 : (x (-9) 4 && x (-9) 12).toNat = (x (-9) 4).toNat := handl _ _ (fun h => hp4 (-9) (h))
              have e5207 : (x (-10) 5 && x (-10) 13).toNat = (x (-10) 5).toNat := handl _ _ (fun h => hp5 (-10) (h))
              have e5208 : (x (-11) 6 && x (-11) 14).toNat = (x (-11) 6).toNat := handl _ _ (fun h => hp6 (-11) (h))
              have r5209 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r5210 : 1 ≤ (x 15 2).toNat + (x 14 1 && x 14 3).toNat + (x 13 2 && x 13 4).toNat + (x 12 3 && x 12 5).toNat + (x 11 4 && x 11 6).toNat + (x 10 5 && x 10 7).toNat + (x 9 6 && x 9 8).toNat + (x 8 7 && x 8 9).toNat + (x 7 8 && x 7 10).toNat + (x 6 9 && x 6 11).toNat + (x 5 10 && x 5 12).toNat + (x 4 11 && x 4 13).toNat + (x 3 12 && x 3 14).toNat + (x 2 13).toNat := by have q := hcov2 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r5211 : 1 ≤ (x (-1) 4).toNat + (x (-2) 1 && x (-2) 5).toNat + (x (-3) 2 && x (-3) 6).toNat + (x (-4) 3 && x (-4) 7).toNat + (x (-5) 4 && x (-5) 8).toNat + (x (-6) 5 && x (-6) 9).toNat + (x (-7) 6 && x (-7) 10).toNat + (x (-8) 7 && x (-8) 11).toNat + (x (-9) 8 && x (-9) 12).toNat + (x (-10) 9 && x (-10) 13).toNat + (x (-11) 10 && x (-11) 14).toNat + (x (-12) 11).toNat := by have q := hcov4 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e5212 : (x (-2) 1 && x (-2) 5).toNat = (x (-2) 5).toNat := handr _ _ (fun h => hp13 (-2) (hp5 (-2) (h)))
              have e5213 : (x (-11) 10 && x (-11) 14).toNat = (x (-11) 10).toNat := handl _ _ (fun h => hp2 (-11) (hp10 (-11) (h)))
              have r5214 : 1 ≤ (x 3 4).toNat + (x 2 1 && x 2 5).toNat + (x 1 2 && x 1 6).toNat + (x 0 3 && x 0 7).toNat + (x (-1) 4 && x (-1) 8).toNat + (x (-2) 5 && x (-2) 9).toNat + (x (-3) 6 && x (-3) 10).toNat + (x (-4) 7 && x (-4) 11).toNat + (x (-5) 8 && x (-5) 12).toNat + (x (-6) 9 && x (-6) 13).toNat + (x (-7) 10 && x (-7) 14).toNat + (x (-8) 11).toNat := by have q := hcov4 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e5215 : (x 2 1 && x 2 5).toNat = (x 2 5).toNat := handr _ _ (fun h => hp13 2 (hp5 2 (h)))
              have e5216 : (x (-7) 10 && x (-7) 14).toNat = (x (-7) 10).toNat := handl _ _ (fun h => hp2 (-7) (hp10 (-7) (h)))
              have r5217 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e5218 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
              have e5219 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
              have r5220 : 1 ≤ (x (-1) 7).toNat + (x (-2) 1 && x (-2) 8).toNat + (x (-3) 2 && x (-3) 9).toNat + (x (-4) 3 && x (-4) 10).toNat + (x (-5) 4 && x (-5) 11).toNat + (x (-6) 5 && x (-6) 12).toNat + (x (-7) 6 && x (-7) 13).toNat + (x (-8) 7 && x (-8) 14).toNat + (x (-9) 8).toNat := by have q := hcov7 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r5221 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r5222 : 1 ≤ (x (-5) 11).toNat + (x (-6) 1 && x (-6) 12).toNat + (x (-7) 2 && x (-7) 13).toNat + (x (-8) 3 && x (-8) 14).toNat + (x (-9) 4).toNat := by have q := hcov11 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r5223 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r5224 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r5225 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r5226 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r5227 : (x (-11) 2).toNat ≤ (x (-11) 14).toNat := himp _ _ (hp2 (-11))
              have r5228 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
              have r5229 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
              have r5230 := hand2 (x 14 1) (x 14 3)
              have r5231 := hand2 (x 13 2) (x 13 4)
              have r5232 := hand2 (x 12 3) (x 12 5)
              have r5233 := hand2 (x 8 7) (x 8 9)
              have r5234 := hand2 (x (-3) 2) (x (-3) 6)
              have r5235 := hand2 (x (-4) 3) (x (-4) 7)
              have r5236 := hand2 (x (-9) 8) (x (-9) 12)
              have r5237 := hand2 (x (-10) 9) (x (-10) 13)
              have r5238 := hand1 (x (-5) 8) (x (-5) 12)
              have r5239 := hand1 (x (-6) 9) (x (-6) 13)
              have r5240 := hand1 (x (-2) 6) (x (-2) 10)
              have r5241 := hand1 (x (-3) 7) (x (-3) 11)
              have r5242 := hand1 (x (-4) 8) (x (-4) 12)
              have r5243 := hand1 (x (-5) 9) (x (-5) 13)
              have r5244 := hand2 (x (-2) 1) (x (-2) 8)
              have r5245 := hand2 (x (-3) 2) (x (-3) 9)
              have r5246 := hand2 (x (-4) 3) (x (-4) 10)
              have r5247 := hand2 (x 6 1) (x 6 11)
              have r5248 := hand1 (x 5 2) (x 5 12)
              have r5249 := hand1 (x 4 3) (x 4 13)
              have r5250 := hand2 (x (-6) 1) (x (-6) 12)
              have r5251 := hand2 (x (-7) 2) (x (-7) 13)
              have r5252 := hand2 (x (-8) 3) (x (-8) 14)
              have r5253 := hand2 (x (-5) 1) (x (-5) 12)
              have r5254 := hand2 (x (-6) 2) (x (-6) 13)
              have r5255 := hand2 (x (-7) 3) (x (-7) 14)
              have r5256 := hand2 (x (-10) 1) (x (-10) 14)
              have r5257 := hand1 (x 3 1) (x 3 14)
              have r5258 := hand1 (x 5 1) (x 5 14)
              linarith only [r5190, r5191, r5192, r5193, r5194, r5195, e5196, e5197, e5198, e5199, e5200, e5201, r5202, e5203, e5204, e5205, e5206, e5207, e5208, r5209, r5210, r5211, e5212, e5213, r5214, e5215, e5216, r5217, e5218, e5219, r5220, r5221, r5222, r5223, r5224, r5225, r5226, r5227, r5228, r5229, r5230, r5231, r5232, r5233, r5234, r5235, r5236, r5237, r5238, r5239, r5240, r5241, r5242, r5243, r5244, r5245, r5246, r5247, r5248, r5249, r5250, r5251, r5252, r5253, r5254, r5255, r5256, r5257, r5258, d5074, d5054, d5034, f3813, f3823, d3692, f5033, g1, g2, g4, g5, f3467, d3523, d3604, g14, d2688, d2735, g16, d3500, g17, d3551, d3539, d3957, d3981, d4001, g22, g23, g24, g25, d3496, d5114, d5138, d5162, d5186, g26, g27, d3818, d5050, d5070, d5090, d2684, d3834, g28, d3824, d5110, d5134, d5158, d5182, g58]
          · have f5403 : (x 1 7).toNat = 1 := by rw [h3828]; rfl
            have d5404 : (x 8 8).toNat = 0 := by
              have r5405 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e5406 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e5407 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e5408 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e5409 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e5410 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e5411 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b5412 := hb (x 1 7)
              have b5413 := hb (x 2 6)
              have b5414 := hb (x 3 5)
              have b5415 := hb (x 4 4)
              have b5416 := hb (x 5 11)
              have b5417 := hb (x 6 10)
              have b5418 := hb (x 7 9)
              have b5419 := hb (x 8 8)
              clear * - r5405 e5406 e5407 e5408 e5409 e5410 e5411 b5412 b5413 b5414 b5415 b5416 b5417 b5418 b5419 d3539 d3551 d2676 f5403
              omega
            have d5420 : (x 7 9).toNat = 0 := by
              have r5421 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e5422 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e5423 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e5424 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e5425 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e5426 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e5427 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b5428 := hb (x 1 7)
              have b5429 := hb (x 2 6)
              have b5430 := hb (x 3 5)
              have b5431 := hb (x 4 4)
              have b5432 := hb (x 5 11)
              have b5433 := hb (x 6 10)
              have b5434 := hb (x 7 9)
              have b5435 := hb (x 8 8)
              clear * - r5421 e5422 e5423 e5424 e5425 e5426 e5427 b5428 b5429 b5430 b5431 b5432 b5433 b5434 b5435 d5404 d3539 d3551 d2676 f5403
              omega
            have d5436 : (x 6 10).toNat = 0 := by
              have r5437 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e5438 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e5439 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e5440 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e5441 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e5442 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e5443 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b5444 := hb (x 1 7)
              have b5445 := hb (x 2 6)
              have b5446 := hb (x 3 5)
              have b5447 := hb (x 4 4)
              have b5448 := hb (x 5 11)
              have b5449 := hb (x 6 10)
              have b5450 := hb (x 7 9)
              have b5451 := hb (x 8 8)
              clear * - r5437 e5438 e5439 e5440 e5441 e5442 e5443 b5444 b5445 b5446 b5447 b5448 b5449 b5450 b5451 d5404 d5420 d3539 d3551 d2676 f5403
              omega
            have d5452 : (x 6 1 && x 6 10).toNat = 0 := by
              have r5453 := hand2 (x 6 1) (x 6 10)
              have b5454 := hb (x 6 10)
              have b5455 := hb (x 6 1 && x 6 10)
              clear * - r5453 b5454 b5455 d5436
              omega
            have d5456 : (x 5 2 && x 5 11).toNat = 1 := by
              have r5457 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b5458 := hb (x 1 6)
              have b5459 := hb (x 7 9)
              have b5460 := hb (x 6 1 && x 6 10)
              have b5461 := hb (x 5 2 && x 5 11)
              have b5462 := hb (x 4 3 && x 4 12)
              have b5463 := hb (x 3 4 && x 3 13)
              have b5464 := hb (x 2 5 && x 2 14)
              clear * - r5457 b5458 b5459 b5460 b5461 b5462 b5463 b5464 d5420 d5452 d3535 g54 g55 g14
              omega
            have d5465 : (x 5 11).toNat = 1 := by
              have r5466 := hand2 (x 5 2) (x 5 11)
              have b5467 := hb (x 5 11)
              have b5468 := hb (x 5 2 && x 5 11)
              clear * - r5466 b5467 b5468 d5456
              omega
            have r5469 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e5470 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e5471 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e5472 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e5473 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e5474 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e5475 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have b5476 := hb (x 1 7)
            have b5477 := hb (x 2 6)
            have b5478 := hb (x 3 5)
            have b5479 := hb (x 4 4)
            have b5480 := hb (x 5 11)
            have b5481 := hb (x 6 10)
            have b5482 := hb (x 7 9)
            have b5483 := hb (x 8 8)
            linarith only [r5469, e5470, e5471, e5472, e5473, e5474, e5475, b5476, b5477, b5478, b5479, b5480, b5481, b5482, b5483, d5404, d5420, d5436, d5465, d3539, d3551, d2676, f5403]
        · have f5484 : (x (-1) 5).toNat = 1 := by rw [h3822]; rfl
          have d5485 : (x (-1) 13).toNat = 1 := by
            have r5486 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
            have b5487 := hb (x (-1) 5)
            have b5488 := hb (x (-1) 13)
            clear * - r5486 b5487 b5488 f5484
            omega
          have d5489 : (x (-2) 2).toNat = 0 := by
            have r5490 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e5491 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
            have e5492 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
            have b5493 := hb (x (-3) 3)
            have b5494 := hb (x (-2) 2)
            have b5495 := hb (x (-1) 13)
            have b5496 := hb (x 0 12)
            clear * - r5490 e5491 e5492 b5493 b5494 b5495 b5496 g10 d5485
            omega
          have d5497 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
            have r5498 := hand1 (x (-2) 2) (x (-2) 13)
            have b5499 := hb (x (-2) 2)
            have b5500 := hb (x (-2) 2 && x (-2) 13)
            clear * - r5498 b5499 b5500 d5489
            omega
          have d5501 : (x (-2) 10).toNat = 0 := by
            have r5502 : (x (-2) 10).toNat ≤ (x (-2) 2).toNat := himp _ _ (hp10 (-2))
            have b5503 := hb (x (-2) 2)
            have b5504 := hb (x (-2) 10)
            clear * - r5502 b5503 b5504 d5489
            omega
          have d5505 : (x (-1) 1 && x (-1) 14).toNat = 1 := by
            have r5506 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b5507 := hb (x (-2) 2)
            have b5508 := hb (x 0 13)
            have b5509 := hb (x (-1) 1 && x (-1) 14)
            clear * - r5506 b5507 b5508 b5509 g11 d5489
            omega
          have d5510 : (x (-1) 14).toNat = 1 := by
            have r5511 := hand2 (x (-1) 1) (x (-1) 14)
            have b5512 := hb (x (-1) 14)
            have b5513 := hb (x (-1) 1 && x (-1) 14)
            clear * - r5511 b5512 b5513 d5505
            omega
          have d5514 : (x (-2) 1).toNat = 0 := by
            have r5515 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b5516 := hb (x (-2) 1)
            have b5517 := hb (x (-1) 14)
            clear * - r5515 b5516 b5517 d5510
            omega
          have d5518 : (x (-2) 13).toNat = 0 := by
            have r5519 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
            have b5520 := hb (x (-2) 1)
            have b5521 := hb (x (-2) 13)
            clear * - r5519 b5520 b5521 d5514
            omega
          have d5522 : (x (-2) 5).toNat = 0 := by
            have r5523 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
            have b5524 := hb (x (-2) 5)
            have b5525 := hb (x (-2) 13)
            clear * - r5523 b5524 b5525 d5518
            omega
          have d5526 : (x (-2) 5 && x (-2) 14).toNat = 0 := by
            have r5527 := hand1 (x (-2) 5) (x (-2) 14)
            have b5528 := hb (x (-2) 5)
            have b5529 := hb (x (-2) 5 && x (-2) 14)
            clear * - r5527 b5528 b5529 d5522
            omega
          have d5530 : (x (-3) 3).toNat = 0 := by
            have r5531 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e5532 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
            have e5533 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
            have b5534 := hb (x (-3) 3)
            have b5535 := hb (x (-2) 2)
            have b5536 := hb (x (-1) 13)
            have b5537 := hb (x 0 12)
            clear * - r5531 e5532 e5533 b5534 b5535 b5536 b5537 g10 d5485 d5489
            omega
          have d5538 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
            have r5539 := hand1 (x (-3) 3) (x (-3) 14)
            have b5540 := hb (x (-3) 3)
            have b5541 := hb (x (-3) 3 && x (-3) 14)
            clear * - r5539 b5540 b5541 d5530
            omega
          have d5542 : (x (-3) 3 && x (-3) 12).toNat = 0 := by
            have r5543 := hand1 (x (-3) 3) (x (-3) 12)
            have b5544 := hb (x (-3) 3)
            have b5545 := hb (x (-3) 3 && x (-3) 12)
            clear * - r5543 b5544 b5545 d5530
            omega
          have d5546 : (x (-3) 11).toNat = 0 := by
            have r5547 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
            have b5548 := hb (x (-3) 3)
            have b5549 := hb (x (-3) 11)
            clear * - r5547 b5548 b5549 d5530
            omega
          have d5550 : (x 4 8).toNat = 0 := by
            have r5551 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e5552 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
            have e5553 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
            have e5554 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
            have e5555 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
            have e5556 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
            have e5557 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
            have b5558 := hb (x (-3) 7)
            have b5559 := hb (x (-2) 6)
            have b5560 := hb (x (-1) 5)
            have b5561 := hb (x 0 4)
            have b5562 := hb (x 1 11)
            have b5563 := hb (x 2 10)
            have b5564 := hb (x 3 9)
            have b5565 := hb (x 4 8)
            clear * - r5551 e5552 e5553 e5554 e5555 e5556 e5557 b5558 b5559 b5560 b5561 b5562 b5563 b5564 b5565 d2696 g2 f5484
            omega
          have d5566 : (x 3 9).toNat = 0 := by
            have r5567 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e5568 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
            have e5569 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
            have e5570 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
            have e5571 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
            have e5572 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
            have e5573 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
            have b5574 := hb (x (-3) 7)
            have b5575 := hb (x (-2) 6)
            have b5576 := hb (x (-1) 5)
            have b5577 := hb (x 0 4)
            have b5578 := hb (x 1 11)
            have b5579 := hb (x 2 10)
            have b5580 := hb (x 3 9)
            have b5581 := hb (x 4 8)
            clear * - r5567 e5568 e5569 e5570 e5571 e5572 e5573 b5574 b5575 b5576 b5577 b5578 b5579 b5580 b5581 d5550 d2696 g2 f5484
            omega
          have d5582 : (x 1 11).toNat = 0 := by
            have r5583 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e5584 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
            have e5585 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
            have e5586 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
            have e5587 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
            have e5588 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
            have e5589 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
            have b5590 := hb (x (-3) 7)
            have b5591 := hb (x (-2) 6)
            have b5592 := hb (x (-1) 5)
            have b5593 := hb (x 0 4)
            have b5594 := hb (x 1 11)
            have b5595 := hb (x 2 10)
            have b5596 := hb (x 3 9)
            have b5597 := hb (x 4 8)
            clear * - r5583 e5584 e5585 e5586 e5587 e5588 e5589 b5590 b5591 b5592 b5593 b5594 b5595 b5596 b5597 d5550 d5566 d2696 g2 f5484
            omega
          have d5598 : (x 1 2 && x 1 11).toNat = 0 := by
            have r5599 := hand2 (x 1 2) (x 1 11)
            have b5600 := hb (x 1 11)
            have b5601 := hb (x 1 2 && x 1 11)
            clear * - r5599 b5600 b5601 d5582
            omega
          have d5602 : (x (-3) 6).toNat = 1 := by
            have r5603 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b5604 := hb (x (-3) 6)
            have b5605 := hb (x 3 9)
            have b5606 := hb (x 2 1 && x 2 10)
            have b5607 := hb (x 1 2 && x 1 11)
            have b5608 := hb (x 0 3 && x 0 12)
            have b5609 := hb (x (-1) 4 && x (-1) 13)
            have b5610 := hb (x (-2) 5 && x (-2) 14)
            clear * - r5603 b5604 b5605 b5606 b5607 b5608 b5609 b5610 d5566 d2700 d5598 g51 d3814 d5526
            omega
          have d5611 : (x (-3) 14).toNat = 1 := by
            have r5612 : (x (-3) 6).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp6 (-3))
            have b5613 := hb (x (-3) 6)
            have b5614 := hb (x (-3) 14)
            clear * - r5612 b5613 b5614 d5602
            omega
          have d5615 : (x (-4) 1).toNat = 0 := by
            have r5616 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b5617 := hb (x (-4) 1)
            have b5618 := hb (x (-3) 14)
            clear * - r5616 b5617 b5618 d5611
            omega
          have d5619 : (x (-4) 1 && x (-4) 12).toNat = 0 := by
            have r5620 := hand1 (x (-4) 1) (x (-4) 12)
            have b5621 := hb (x (-4) 1)
            have b5622 := hb (x (-4) 1 && x (-4) 12)
            clear * - r5620 b5621 b5622 d5615
            omega
          have d5623 : (x (-4) 13).toNat = 0 := by
            have r5624 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
            have b5625 := hb (x (-4) 1)
            have b5626 := hb (x (-4) 13)
            clear * - r5624 b5625 b5626 d5615
            omega
          have d5627 : (x (-4) 4 && x (-4) 13).toNat = 0 := by
            have r5628 := hand2 (x (-4) 4) (x (-4) 13)
            have b5629 := hb (x (-4) 13)
            have b5630 := hb (x (-4) 4 && x (-4) 13)
            clear * - r5628 b5629 b5630 d5623
            omega
          have d5631 : (x (-4) 9).toNat = 0 := by
            have r5632 : (x (-4) 9).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp9 (-4))
            have b5633 := hb (x (-4) 1)
            have b5634 := hb (x (-4) 9)
            clear * - r5632 b5633 b5634 d5615
            omega
          have d5635 : (x (-3) 4).toNat = 1 := by
            have r5636 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b5637 := hb (x (-3) 4)
            have b5638 := hb (x 1 11)
            have b5639 := hb (x 0 1 && x 0 12)
            have b5640 := hb (x (-1) 2 && x (-1) 13)
            have b5641 := hb (x (-2) 3 && x (-2) 14)
            clear * - r5636 b5637 b5638 b5639 b5640 b5641 d5582 g59 d2706 d3579
            omega
          have d5642 : (x (-3) 12).toNat = 1 := by
            have r5643 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
            have b5644 := hb (x (-3) 4)
            have b5645 := hb (x (-3) 12)
            clear * - r5643 b5644 b5645 d5635
            omega
          have d5646 : (x (-5) 2).toNat = 0 := by
            have r5647 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e5648 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
            have e5649 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
            have b5650 := hb (x (-6) 3)
            have b5651 := hb (x (-5) 2)
            have b5652 := hb (x (-4) 13)
            have b5653 := hb (x (-3) 12)
            clear * - r5647 e5648 e5649 b5650 b5651 b5652 b5653 d5642 d5623
            omega
          have d5654 : (x (-5) 2 && x (-5) 13).toNat = 0 := by
            have r5655 := hand1 (x (-5) 2) (x (-5) 13)
            have b5656 := hb (x (-5) 2)
            have b5657 := hb (x (-5) 2 && x (-5) 13)
            clear * - r5655 b5656 b5657 d5646
            omega
          have d5658 : (x (-5) 10).toNat = 0 := by
            have r5659 : (x (-5) 10).toNat ≤ (x (-5) 2).toNat := himp _ _ (hp10 (-5))
            have b5660 := hb (x (-5) 2)
            have b5661 := hb (x (-5) 10)
            clear * - r5659 b5660 b5661 d5646
            omega
          have d5662 : (x (-6) 3).toNat = 0 := by
            have r5663 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e5664 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
            have e5665 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
            have b5666 := hb (x (-6) 3)
            have b5667 := hb (x (-5) 2)
            have b5668 := hb (x (-4) 13)
            have b5669 := hb (x (-3) 12)
            clear * - r5663 e5664 e5665 b5666 b5667 b5668 b5669 d5642 d5623 d5646
            omega
          have d5670 : (x (-6) 3 && x (-6) 14).toNat = 0 := by
            have r5671 := hand1 (x (-6) 3) (x (-6) 14)
            have b5672 := hb (x (-6) 3)
            have b5673 := hb (x (-6) 3 && x (-6) 14)
            clear * - r5671 b5672 b5673 d5662
            omega
          have d5674 : (x (-7) 4).toNat = 1 := by
            have r5675 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := by have q := hcov11 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b5676 := hb (x (-7) 4)
            have b5677 := hb (x (-3) 11)
            have b5678 := hb (x (-4) 1 && x (-4) 12)
            have b5679 := hb (x (-5) 2 && x (-5) 13)
            have b5680 := hb (x (-6) 3 && x (-6) 14)
            clear * - r5675 b5676 b5677 b5678 b5679 b5680 d5546 d5619 d5654 d5670
            omega
          have d5681 : (x (-7) 12).toNat = 1 := by
            have r5682 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
            have b5683 := hb (x (-7) 4)
            have b5684 := hb (x (-7) 12)
            clear * - r5682 b5683 b5684 d5674
            omega
          have d5685 : (x (-8) 13).toNat = 0 := by
            have r5686 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e5687 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
            have e5688 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
            have b5689 := hb (x (-10) 3)
            have b5690 := hb (x (-9) 2)
            have b5691 := hb (x (-8) 13)
            have b5692 := hb (x (-7) 12)
            clear * - r5686 e5687 e5688 b5689 b5690 b5691 b5692 d5681
            omega
          have d5693 : (x (-8) 5).toNat = 0 := by
            have r5694 : (x (-8) 5).toNat ≤ (x (-8) 13).toNat := himp _ _ (hp5 (-8))
            have b5695 := hb (x (-8) 5)
            have b5696 := hb (x (-8) 13)
            clear * - r5694 b5695 b5696 d5685
            omega
          have d5697 : (x (-6) 11).toNat = 0 := by
            have r5698 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
            have b5699 := hb (x (-6) 3)
            have b5700 := hb (x (-6) 11)
            clear * - r5698 b5699 b5700 d5662
            omega
          have d5701 : (x 3 8).toNat = 0 := by
            have r5702 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e5703 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
            have e5704 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
            have e5705 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
            have e5706 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
            have e5707 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
            have e5708 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
            have b5709 := hb (x (-4) 7)
            have b5710 := hb (x (-3) 6)
            have b5711 := hb (x (-2) 5)
            have b5712 := hb (x (-1) 4)
            have b5713 := hb (x 0 11)
            have b5714 := hb (x 1 10)
            have b5715 := hb (x 2 9)
            have b5716 := hb (x 3 8)
            clear * - r5702 e5703 e5704 e5705 e5706 e5707 e5708 b5709 b5710 b5711 b5712 b5713 b5714 b5715 b5716 g9 f3813 d5522 d5602
            omega
          have d5717 : (x 3 2 && x 3 8).toNat = 0 := by
            have r5718 := hand2 (x 3 2) (x 3 8)
            have b5719 := hb (x 3 8)
            have b5720 := hb (x 3 2 && x 3 8)
            clear * - r5718 b5719 b5720 d5701
            omega
          have d5721 : (x 2 9).toNat = 0 := by
            have r5722 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e5723 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
            have e5724 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
            have e5725 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
            have e5726 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
            have e5727 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
            have e5728 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
            have b5729 := hb (x (-4) 7)
            have b5730 := hb (x (-3) 6)
            have b5731 := hb (x (-2) 5)
            have b5732 := hb (x (-1) 4)
            have b5733 := hb (x 0 11)
            have b5734 := hb (x 1 10)
            have b5735 := hb (x 2 9)
            have b5736 := hb (x 3 8)
            clear * - r5722 e5723 e5724 e5725 e5726 e5727 e5728 b5729 b5730 b5731 b5732 b5733 b5734 b5735 b5736 d5701 g9 f3813 d5522 d5602
            omega
          have d5737 : (x 2 3 && x 2 9).toNat = 0 := by
            have r5738 := hand2 (x 2 3) (x 2 9)
            have b5739 := hb (x 2 9)
            have b5740 := hb (x 2 3 && x 2 9)
            clear * - r5738 b5739 b5740 d5721
            omega
          have d5741 : (x 1 10).toNat = 0 := by
            have r5742 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e5743 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
            have e5744 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
            have e5745 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
            have e5746 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
            have e5747 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
            have e5748 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
            have b5749 := hb (x (-4) 7)
            have b5750 := hb (x (-3) 6)
            have b5751 := hb (x (-2) 5)
            have b5752 := hb (x (-1) 4)
            have b5753 := hb (x 0 11)
            have b5754 := hb (x 1 10)
            have b5755 := hb (x 2 9)
            have b5756 := hb (x 3 8)
            clear * - r5742 e5743 e5744 e5745 e5746 e5747 e5748 b5749 b5750 b5751 b5752 b5753 b5754 b5755 b5756 d5701 d5721 g9 f3813 d5522 d5602
            omega
          have d5757 : (x 1 4 && x 1 10).toNat = 0 := by
            have r5758 := hand2 (x 1 4) (x 1 10)
            have b5759 := hb (x 1 10)
            have b5760 := hb (x 1 4 && x 1 10)
            clear * - r5758 b5759 b5760 d5741
            omega
          have d5761 : (x (-3) 8).toNat = 0 := by
            have r5762 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e5763 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
            have e5764 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
            have e5765 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
            have e5766 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
            have e5767 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
            have e5768 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
            have b5769 := hb (x (-10) 7)
            have b5770 := hb (x (-9) 6)
            have b5771 := hb (x (-8) 5)
            have b5772 := hb (x (-7) 4)
            have b5773 := hb (x (-6) 11)
            have b5774 := hb (x (-5) 10)
            have b5775 := hb (x (-4) 9)
            have b5776 := hb (x (-3) 8)
            clear * - r5762 e5763 e5764 e5765 e5766 e5767 e5768 b5769 b5770 b5771 b5772 b5773 b5774 b5775 b5776 d5631 d5658 d5697 d5674 d5693
            omega
          have d5777 : (x (-3) 8 && x (-3) 14).toNat = 0 := by
            have r5778 := hand1 (x (-3) 8) (x (-3) 14)
            have b5779 := hb (x (-3) 8)
            have b5780 := hb (x (-3) 8 && x (-3) 14)
            clear * - r5778 b5779 b5780 d5761
            omega
          have r5781 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r5782 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5783 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e5784 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e5785 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e5786 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e5787 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e5788 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have r5789 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5790 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e5791 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e5792 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e5793 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e5794 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e5795 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have r5796 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5797 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
          have e5798 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
          have e5799 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
          have e5800 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
          have e5801 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
          have e5802 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
          have r5803 : 1 ≤ (x 11 4).toNat + (x 10 1 && x 10 5).toNat + (x 9 2 && x 9 6).toNat + (x 8 3 && x 8 7).toNat + (x 7 4 && x 7 8).toNat + (x 6 5 && x 6 9).toNat + (x 5 6 && x 5 10).toNat + (x 4 7 && x 4 11).toNat + (x 3 8 && x 3 12).toNat + (x 2 9 && x 2 13).toNat + (x 1 10 && x 1 14).toNat + (x 0 11).toNat := by have q := hcov4 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5804 : (x 10 1 && x 10 5).toNat = (x 10 5).toNat := handr _ _ (fun h => hp13 10 (hp5 10 (h)))
          have e5805 : (x 1 10 && x 1 14).toNat = (x 1 10).toNat := handl _ _ (fun h => hp2 1 (hp10 1 (h)))
          have r5806 : 1 ≤ (x 5 6).toNat + (x 4 1 && x 4 7).toNat + (x 3 2 && x 3 8).toNat + (x 2 3 && x 2 9).toNat + (x 1 4 && x 1 10).toNat + (x 0 5 && x 0 11).toNat + (x (-1) 6 && x (-1) 12).toNat + (x (-2) 7 && x (-2) 13).toNat + (x (-3) 8 && x (-3) 14).toNat + (x (-4) 9).toNat := by have q := hcov6 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r5807 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := by have q := hcov7 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r5808 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r5809 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r5810 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r5811 := hand1 (x 9 2) (x 9 6)
          have r5812 := hand1 (x 8 3) (x 8 7)
          have r5813 := hand2 (x 4 1) (x 4 7)
          have r5814 := hand1 (x 1 7) (x 1 14)
          have r5815 := hand1 (x (-5) 5) (x (-5) 14)
          have r5816 := hand2 (x 6 1) (x 6 10)
          have r5817 := hand2 (x 5 2) (x 5 11)
          have r5818 := hand2 (x (-1) 1) (x (-1) 12)
          linarith only [r5781, r5782, e5783, e5784, e5785, e5786, e5787, e5788, r5789, e5790, e5791, e5792, e5793, e5794, e5795, r5796, e5797, e5798, e5799, e5800, e5801, e5802, r5803, e5804, e5805, r5806, r5807, r5808, r5809, r5810, r5811, r5812, r5813, r5814, r5815, r5816, r5817, r5818, d5631, d5546, d5611, d5501, d5518, g6, g7, g9, g14, d5741, d2676, d5721, d3551, d5701, d3539, g30, g31, g32, g33, d3492, d3512, d5717, d5737, d5757, g40, d3788, d3808, d5777, g46, g47, g48, g49, d3488, d2680, d2714, d3591, d5542, d5627, d3535, g54, g55, d5497, d5538]
      · have f5896 : (x (-1) 4).toNat = 1 := by rw [h3812]; rfl
        have d5897 : (x (-1) 12).toNat = 1 := by
          have r5898 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
          have b5899 := hb (x (-1) 4)
          have b5900 := hb (x (-1) 12)
          clear * - r5898 b5899 b5900 f5896
          omega
        have d5901 : (x (-2) 13).toNat = 0 := by
          have r5902 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5903 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e5904 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b5905 := hb (x (-4) 3)
          have b5906 := hb (x (-3) 2)
          have b5907 := hb (x (-2) 13)
          have b5908 := hb (x (-1) 12)
          clear * - r5902 e5903 e5904 b5905 b5906 b5907 b5908 d5897
          omega
        have d5909 : (x (-2) 4 && x (-2) 13).toNat = 0 := by
          have r5910 := hand2 (x (-2) 4) (x (-2) 13)
          have b5911 := hb (x (-2) 13)
          have b5912 := hb (x (-2) 4 && x (-2) 13)
          clear * - r5910 b5911 b5912 d5901
          omega
        have d5913 : (x (-2) 5).toNat = 0 := by
          have r5914 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
          have b5915 := hb (x (-2) 5)
          have b5916 := hb (x (-2) 13)
          clear * - r5914 b5915 b5916 d5901
          omega
        have d5917 : (x (-2) 5 && x (-2) 9).toNat = 0 := by
          have r5918 := hand1 (x (-2) 5) (x (-2) 9)
          have b5919 := hb (x (-2) 5)
          have b5920 := hb (x (-2) 5 && x (-2) 9)
          clear * - r5918 b5919 b5920 d5913
          omega
        have d5921 : (x (-3) 2).toNat = 0 := by
          have r5922 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5923 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e5924 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b5925 := hb (x (-4) 3)
          have b5926 := hb (x (-3) 2)
          have b5927 := hb (x (-2) 13)
          have b5928 := hb (x (-1) 12)
          clear * - r5922 e5923 e5924 b5925 b5926 b5927 b5928 d5897 d5901
          omega
        have d5929 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
          have r5930 := hand1 (x (-3) 2) (x (-3) 12)
          have b5931 := hb (x (-3) 2)
          have b5932 := hb (x (-3) 2 && x (-3) 12)
          clear * - r5930 b5931 b5932 d5921
          omega
        have d5933 : (x (-3) 10).toNat = 0 := by
          have r5934 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
          have b5935 := hb (x (-3) 2)
          have b5936 := hb (x (-3) 10)
          clear * - r5934 b5935 b5936 d5921
          omega
        have d5937 : (x (-3) 5 && x (-3) 10).toNat = 0 := by
          have r5938 := hand2 (x (-3) 5) (x (-3) 10)
          have b5939 := hb (x (-3) 10)
          have b5940 := hb (x (-3) 5 && x (-3) 10)
          clear * - r5938 b5939 b5940 d5933
          omega
        have d5941 : (x (-3) 6 && x (-3) 10).toNat = 0 := by
          have r5942 := hand2 (x (-3) 6) (x (-3) 10)
          have b5943 := hb (x (-3) 10)
          have b5944 := hb (x (-3) 6 && x (-3) 10)
          clear * - r5942 b5943 b5944 d5933
          omega
        have d5945 : (x (-4) 3).toNat = 0 := by
          have r5946 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5947 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e5948 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b5949 := hb (x (-4) 3)
          have b5950 := hb (x (-3) 2)
          have b5951 := hb (x (-2) 13)
          have b5952 := hb (x (-1) 12)
          clear * - r5946 e5947 e5948 b5949 b5950 b5951 b5952 d5897 d5901 d5921
          omega
        have d5953 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
          have r5954 := hand1 (x (-4) 3) (x (-4) 13)
          have b5955 := hb (x (-4) 3)
          have b5956 := hb (x (-4) 3 && x (-4) 13)
          clear * - r5954 b5955 b5956 d5945
          omega
        have d5957 : (x (-4) 11).toNat = 0 := by
          have r5958 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
          have b5959 := hb (x (-4) 3)
          have b5960 := hb (x (-4) 11)
          clear * - r5958 b5959 b5960 d5945
          omega
        have d5961 : (x (-4) 6 && x (-4) 11).toNat = 0 := by
          have r5962 := hand2 (x (-4) 6) (x (-4) 11)
          have b5963 := hb (x (-4) 11)
          have b5964 := hb (x (-4) 6 && x (-4) 11)
          clear * - r5962 b5963 b5964 d5957
          omega
        have d5965 : (x (-4) 7 && x (-4) 11).toNat = 0 := by
          have r5966 := hand2 (x (-4) 7) (x (-4) 11)
          have b5967 := hb (x (-4) 11)
          have b5968 := hb (x (-4) 7 && x (-4) 11)
          clear * - r5966 b5967 b5968 d5957
          omega
        have d5969 : (x 3 8).toNat = 0 := by
          have r5970 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5971 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e5972 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e5973 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e5974 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e5975 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e5976 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b5977 := hb (x (-4) 7)
          have b5978 := hb (x (-3) 6)
          have b5979 := hb (x (-2) 5)
          have b5980 := hb (x (-1) 4)
          have b5981 := hb (x 0 11)
          have b5982 := hb (x 1 10)
          have b5983 := hb (x 2 9)
          have b5984 := hb (x 3 8)
          clear * - r5970 e5971 e5972 e5973 e5974 e5975 e5976 b5977 b5978 b5979 b5980 b5981 b5982 b5983 b5984 g9 f5896 d5913
          omega
        have d5985 : (x 2 9).toNat = 0 := by
          have r5986 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5987 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e5988 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e5989 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e5990 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e5991 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e5992 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b5993 := hb (x (-4) 7)
          have b5994 := hb (x (-3) 6)
          have b5995 := hb (x (-2) 5)
          have b5996 := hb (x (-1) 4)
          have b5997 := hb (x 0 11)
          have b5998 := hb (x 1 10)
          have b5999 := hb (x 2 9)
          have b6000 := hb (x 3 8)
          clear * - r5986 e5987 e5988 e5989 e5990 e5991 e5992 b5993 b5994 b5995 b5996 b5997 b5998 b5999 b6000 d5969 g9 f5896 d5913
          omega
        have d6001 : (x 1 10).toNat = 0 := by
          have r6002 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e6003 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e6004 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e6005 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e6006 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e6007 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e6008 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b6009 := hb (x (-4) 7)
          have b6010 := hb (x (-3) 6)
          have b6011 := hb (x (-2) 5)
          have b6012 := hb (x (-1) 4)
          have b6013 := hb (x 0 11)
          have b6014 := hb (x 1 10)
          have b6015 := hb (x 2 9)
          have b6016 := hb (x 3 8)
          clear * - r6002 e6003 e6004 e6005 e6006 e6007 e6008 b6009 b6010 b6011 b6012 b6013 b6014 b6015 b6016 d5969 d5985 g9 f5896 d5913
          omega
        have d6017 : (x 1 1 && x 1 10).toNat = 0 := by
          have r6018 := hand2 (x 1 1) (x 1 10)
          have b6019 := hb (x 1 10)
          have b6020 := hb (x 1 1 && x 1 10)
          clear * - r6018 b6019 b6020 d6001
          omega
        have d6021 : (x (-3) 6).toNat = 0 := by
          have r6022 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e6023 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e6024 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e6025 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e6026 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e6027 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e6028 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b6029 := hb (x (-4) 7)
          have b6030 := hb (x (-3) 6)
          have b6031 := hb (x (-2) 5)
          have b6032 := hb (x (-1) 4)
          have b6033 := hb (x 0 11)
          have b6034 := hb (x 1 10)
          have b6035 := hb (x 2 9)
          have b6036 := hb (x 3 8)
          clear * - r6022 e6023 e6024 e6025 e6026 e6027 e6028 b6029 b6030 b6031 b6032 b6033 b6034 b6035 b6036 d5969 d5985 d6001 g9 f5896 d5913
          omega
        have d6037 : (x (-4) 7).toNat = 0 := by
          have r6038 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e6039 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e6040 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e6041 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e6042 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e6043 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e6044 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b6045 := hb (x (-4) 7)
          have b6046 := hb (x (-3) 6)
          have b6047 := hb (x (-2) 5)
          have b6048 := hb (x (-1) 4)
          have b6049 := hb (x 0 11)
          have b6050 := hb (x 1 10)
          have b6051 := hb (x 2 9)
          have b6052 := hb (x 3 8)
          clear * - r6038 e6039 e6040 e6041 e6042 e6043 e6044 b6045 b6046 b6047 b6048 b6049 b6050 b6051 b6052 d5969 d5985 d6001 g9 f5896 d5913 d6021
          omega
        have r6053 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r6054 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r6055 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6056 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e6057 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e6058 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e6059 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e6060 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e6061 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have r6062 : 1 ≤ (x 3 4).toNat + (x 2 1 && x 2 5).toNat + (x 1 2 && x 1 6).toNat + (x 0 3 && x 0 7).toNat + (x (-1) 4 && x (-1) 8).toNat + (x (-2) 5 && x (-2) 9).toNat + (x (-3) 6 && x (-3) 10).toNat + (x (-4) 7 && x (-4) 11).toNat + (x (-5) 8 && x (-5) 12).toNat + (x (-6) 9 && x (-6) 13).toNat + (x (-7) 10 && x (-7) 14).toNat + (x (-8) 11).toNat := by have q := hcov4 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6063 : (x 2 1 && x 2 5).toNat = (x 2 5).toNat := handr _ _ (fun h => hp13 2 (hp5 2 (h)))
        have e6064 : (x (-7) 10 && x (-7) 14).toNat = (x (-7) 10).toNat := handl _ _ (fun h => hp2 (-7) (hp10 (-7) (h)))
        have r6065 : 1 ≤ (x 2 5).toNat + (x 1 1 && x 1 6).toNat + (x 0 2 && x 0 7).toNat + (x (-1) 3 && x (-1) 8).toNat + (x (-2) 4 && x (-2) 9).toNat + (x (-3) 5 && x (-3) 10).toNat + (x (-4) 6 && x (-4) 11).toNat + (x (-5) 7 && x (-5) 12).toNat + (x (-6) 8 && x (-6) 13).toNat + (x (-7) 9 && x (-7) 14).toNat + (x (-8) 10).toNat := by have q := hcov5 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r6066 : 1 ≤ (x 2 9).toNat + (x 1 1 && x 1 10).toNat + (x 0 2 && x 0 11).toNat + (x (-1) 3 && x (-1) 12).toNat + (x (-2) 4 && x (-2) 13).toNat + (x (-3) 5 && x (-3) 14).toNat + (x (-4) 6).toNat := by have q := hcov9 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r6067 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r6068 : 1 ≤ (x (-10) 13).toNat + (x (-11) 1 && x (-11) 14).toNat + (x (-12) 2).toNat := by have q := hcov13 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r6069 : (x (-12) 2).toNat ≤ (x (-12) 14).toNat := himp _ _ (hp2 (-12))
        have r6070 := hand2 (x (-1) 4) (x (-1) 8)
        have r6071 := hand1 (x (-5) 8) (x (-5) 12)
        have r6072 := hand1 (x (-6) 9) (x (-6) 13)
        have r6073 := hand2 (x (-2) 4) (x (-2) 9)
        have r6074 := hand1 (x (-5) 7) (x (-5) 12)
        have r6075 := hand1 (x (-6) 8) (x (-6) 13)
        have r6076 := hand1 (x (-7) 9) (x (-7) 14)
        have r6077 := hand1 (x (-3) 5) (x (-3) 14)
        have r6078 := hand1 (x (-5) 4) (x (-5) 14)
        have r6079 := hand2 (x (-11) 1) (x (-11) 14)
        linarith only [r6053, r6054, r6055, e6056, e6057, e6058, e6059, e6060, e6061, r6062, e6063, e6064, r6065, r6066, r6067, r6068, r6069, r6070, r6071, r6072, r6073, r6074, r6075, r6076, r6077, r6078, r6079, d6037, d5957, d6021, d5933, d5913, d2747, f5896, d2710, g0, g1, g13, f3467, g16, d5985, g17, g26, g27, d5917, d5941, d5965, g34, g35, d2763, d5937, d5961, d6017, g50, d2759, d5909, d3587, d5929, d5953]
  · have f6148 : (x (-1) 2).toNat = 1 := by rw [h2704]; rfl
    have d6149 : (x 1 12).toNat = 0 := by
      have r6150 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6151 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e6152 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b6153 := hb (x (-2) 3)
      have b6154 := hb (x (-1) 2)
      have b6155 := hb (x 0 13)
      have b6156 := hb (x 1 12)
      clear * - r6150 e6151 e6152 b6153 b6154 b6155 b6156 g11 f6148
      omega
    have d6157 : (x 1 4).toNat = 0 := by
      have r6158 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
      have b6159 := hb (x 1 4)
      have b6160 := hb (x 1 12)
      clear * - r6158 b6159 b6160 d6149
      omega
    have d6161 : (x 1 4 && x 1 14).toNat = 0 := by
      have r6162 := hand1 (x 1 4) (x 1 14)
      have b6163 := hb (x 1 4)
      have b6164 := hb (x 1 4 && x 1 14)
      clear * - r6162 b6163 b6164 d6157
      omega
    have r6165 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6166 : (x 16 1).toNat + (x 15 2).toNat + (x 14 3).toNat + (x 13 4).toNat + (x 12 5).toNat + (x 11 6).toNat + (x 10 7).toNat + (x 9 8).toNat + (x 8 9).toNat + (x 7 10).toNat + (x 6 11).toNat + (x 5 12).toNat + (x 4 13).toNat + (x 3 14).toNat = 3 := by have q := hcount 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6167 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6168 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e6169 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e6170 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e6171 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e6172 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e6173 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have r6174 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6175 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
    have e6176 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
    have e6177 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
    have e6178 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
    have e6179 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
    have e6180 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
    have r6181 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6182 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
    have e6183 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
    have e6184 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
    have e6185 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
    have e6186 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
    have e6187 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
    have r6188 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6189 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
    have e6190 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
    have e6191 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
    have e6192 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
    have e6193 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
    have e6194 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
    have r6195 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6196 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e6197 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have r6198 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6199 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e6200 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have r6201 : 1 ≤ (x 17 6).toNat + (x 16 1 && x 16 7).toNat + (x 15 2 && x 15 8).toNat + (x 14 3 && x 14 9).toNat + (x 13 4 && x 13 10).toNat + (x 12 5 && x 12 11).toNat + (x 11 6 && x 11 12).toNat + (x 10 7 && x 10 13).toNat + (x 9 8 && x 9 14).toNat + (x 8 9).toNat := by have q := hcov6 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6202 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := by have q := hcov7 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6203 : 1 ≤ (x 16 7).toNat + (x 15 1 && x 15 8).toNat + (x 14 2 && x 14 9).toNat + (x 13 3 && x 13 10).toNat + (x 12 4 && x 12 11).toNat + (x 11 5 && x 11 12).toNat + (x 10 6 && x 10 13).toNat + (x 9 7 && x 9 14).toNat + (x 8 8).toNat := by have q := hcov7 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6204 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6205 : 1 ≤ (x 15 9).toNat + (x 14 1 && x 14 10).toNat + (x 13 2 && x 13 11).toNat + (x 12 3 && x 12 12).toNat + (x 11 4 && x 11 13).toNat + (x 10 5 && x 10 14).toNat + (x 9 6).toNat := by have q := hcov9 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6206 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6207 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6208 : 1 ≤ (x 15 10).toNat + (x 14 1 && x 14 11).toNat + (x 13 2 && x 13 12).toNat + (x 12 3 && x 12 13).toNat + (x 11 4 && x 11 14).toNat + (x 10 5).toNat := by have q := hcov10 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6209 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6210 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6211 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
    have r6212 : (x 15 10).toNat ≤ (x 15 2).toNat := himp _ _ (hp10 15)
    have r6213 := hand1 (x 16 1) (x 16 7)
    have r6214 := hand2 (x 15 2) (x 15 8)
    have r6215 := hand2 (x 14 3) (x 14 9)
    have r6216 := hand1 (x 13 4) (x 13 10)
    have r6217 := hand1 (x 12 5) (x 12 11)
    have r6218 := hand1 (x 11 6) (x 11 12)
    have r6219 := hand1 (x 10 7) (x 10 13)
    have r6220 := hand1 (x 9 8) (x 9 14)
    have r6221 := hand1 (x 3 5) (x 3 12)
    have r6222 := hand1 (x 1 7) (x 1 14)
    have r6223 := hand2 (x 15 1) (x 15 8)
    have r6224 := hand2 (x 14 2) (x 14 9)
    have r6225 := hand2 (x 13 3) (x 13 10)
    have r6226 := hand1 (x 12 4) (x 12 11)
    have r6227 := hand1 (x 11 5) (x 11 12)
    have r6228 := hand1 (x 10 6) (x 10 13)
    have r6229 := hand1 (x 9 7) (x 9 14)
    have r6230 := hand2 (x 6 1) (x 6 10)
    have r6231 := hand2 (x 5 2) (x 5 11)
    have r6232 := hand2 (x 4 3) (x 4 12)
    have r6233 := hand2 (x 14 1) (x 14 10)
    have r6234 := hand2 (x 13 2) (x 13 11)
    have r6235 := hand1 (x 12 3) (x 12 12)
    have r6236 := hand1 (x 11 4) (x 11 13)
    have r6237 := hand1 (x 10 5) (x 10 14)
    have r6238 := hand1 (x 3 2) (x 3 12)
    have r6239 := hand2 (x 3 2) (x 3 12)
    have r6240 := hand2 (x 2 3) (x 2 13)
    have r6241 := hand2 (x 6 1) (x 6 11)
    have r6242 := hand2 (x 5 2) (x 5 12)
    have r6243 := hand2 (x 4 3) (x 4 13)
    have r6244 := hand1 (x 14 1) (x 14 11)
    have r6245 := hand1 (x 13 2) (x 13 12)
    have r6246 := hand1 (x 12 3) (x 12 13)
    have r6247 := hand1 (x 11 4) (x 11 14)
    have r6248 := hand2 (x 3 1) (x 3 12)
    have r6249 := hand1 (x 1 3) (x 1 14)
    linarith only [r6165, r6166, r6167, e6168, e6169, e6170, e6171, e6172, e6173, r6174, e6175, e6176, e6177, e6178, e6179, e6180, r6181, e6182, e6183, e6184, e6185, e6186, e6187, r6188, e6189, e6190, e6191, e6192, e6193, e6194, r6195, e6196, e6197, r6198, e6199, e6200, r6201, r6202, r6203, r6204, r6205, r6206, r6207, r6208, r6209, r6210, r6211, r6212, r6213, r6214, r6215, r6216, r6217, r6218, r6219, r6220, r6221, r6222, r6223, r6224, r6225, r6226, r6227, r6228, r6229, r6230, r6231, r6232, r6233, r6234, r6235, r6236, r6237, r6238, r6239, r6240, r6241, r6242, r6243, r6244, r6245, r6246, r6247, r6248, r6249, g1, g2, g3, g6, g14, g15, d2688, g16, d2676, g18, g19, g20, g21, g46, g47, g48, g49, d2680, g54, g55, g57, d6161, g58, d2692, d2672]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b000001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 2).toNat = 0)
    (g1 : (x 0 3).toNat = 0)
    (g2 : (x 0 5).toNat = 0)
    (g3 : (x 0 10).toNat = 0)
    (g4 : (x 0 11).toNat = 0)
    (g5 : (x 0 12).toNat = 1)
    (g6 : (x 0 13).toNat = 0)
    (g7 : (x 5 10).toNat = 0)
    (g8 : (x 0 1 && x 0 11).toNat = 0)
    (g9 : (x 0 4 && x 0 14).toNat = 0)
    (g10 : (x 4 1 && x 4 11).toNat = 0)
    (g11 : (x 0 3 && x 0 14).toNat = 0)
    (g12 : (x 0 1 && x 0 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d6368 : (x (-1) 13).toNat = 0 := by
    have r6369 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6370 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e6371 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b6372 := hb (x (-3) 3)
    have b6373 := hb (x (-2) 2)
    have b6374 := hb (x (-1) 13)
    have b6375 := hb (x 0 12)
    clear * - r6369 e6370 e6371 b6372 b6373 b6374 b6375 g5
    omega
  have d6376 : (x (-1) 5).toNat = 0 := by
    have r6377 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
    have b6378 := hb (x (-1) 5)
    have b6379 := hb (x (-1) 13)
    clear * - r6377 b6378 b6379 d6368
    omega
  have d6380 : (x (-2) 2).toNat = 0 := by
    have r6381 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6382 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e6383 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b6384 := hb (x (-3) 3)
    have b6385 := hb (x (-2) 2)
    have b6386 := hb (x (-1) 13)
    have b6387 := hb (x 0 12)
    clear * - r6381 e6382 e6383 b6384 b6385 b6386 b6387 g5 d6368
    omega
  have d6388 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
    have r6389 := hand1 (x (-2) 2) (x (-2) 13)
    have b6390 := hb (x (-2) 2)
    have b6391 := hb (x (-2) 2 && x (-2) 13)
    clear * - r6389 b6390 b6391 d6380
    omega
  have d6392 : (x (-2) 2 && x (-2) 12).toNat = 0 := by
    have r6393 := hand1 (x (-2) 2) (x (-2) 12)
    have b6394 := hb (x (-2) 2)
    have b6395 := hb (x (-2) 2 && x (-2) 12)
    clear * - r6393 b6394 b6395 d6380
    omega
  have d6396 : (x (-1) 1 && x (-1) 14).toNat = 1 := by
    have r6397 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6398 := hb (x (-2) 2)
    have b6399 := hb (x 0 13)
    have b6400 := hb (x (-1) 1 && x (-1) 14)
    clear * - r6397 b6398 b6399 b6400 g6 d6380
    omega
  have d6401 : (x (-1) 14).toNat = 1 := by
    have r6402 := hand2 (x (-1) 1) (x (-1) 14)
    have b6403 := hb (x (-1) 14)
    have b6404 := hb (x (-1) 1 && x (-1) 14)
    clear * - r6402 b6403 b6404 d6396
    omega
  have d6405 : (x (-2) 1).toNat = 0 := by
    have r6406 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6407 := hb (x (-2) 1)
    have b6408 := hb (x (-1) 14)
    clear * - r6406 b6407 b6408 d6401
    omega
  have d6409 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
    have r6410 := hand1 (x (-2) 1) (x (-2) 14)
    have b6411 := hb (x (-2) 1)
    have b6412 := hb (x (-2) 1 && x (-2) 14)
    clear * - r6410 b6411 b6412 d6405
    omega
  have d6413 : (x (-3) 2).toNat = 1 := by
    have r6414 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6415 := hb (x (-3) 2)
    have b6416 := hb (x (-1) 13)
    have b6417 := hb (x (-2) 1 && x (-2) 14)
    clear * - r6414 b6415 b6416 b6417 d6368 d6409
    omega
  have d6418 : (x (-3) 14).toNat = 1 := by
    have r6419 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
    have b6420 := hb (x (-3) 2)
    have b6421 := hb (x (-3) 14)
    clear * - r6419 b6420 b6421 d6413
    omega
  have d6422 : (x (-4) 1).toNat = 0 := by
    have r6423 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6424 := hb (x (-4) 1)
    have b6425 := hb (x (-3) 14)
    clear * - r6423 b6424 b6425 d6418
    omega
  have d6426 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
    have r6427 := hand1 (x (-4) 1) (x (-4) 14)
    have b6428 := hb (x (-4) 1)
    have b6429 := hb (x (-4) 1 && x (-4) 14)
    clear * - r6427 b6428 b6429 d6422
    omega
  have d6430 : (x (-4) 13).toNat = 0 := by
    have r6431 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
    have b6432 := hb (x (-4) 1)
    have b6433 := hb (x (-4) 13)
    clear * - r6431 b6432 b6433 d6422
    omega
  have d6434 : (x (-4) 5).toNat = 0 := by
    have r6435 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
    have b6436 := hb (x (-4) 5)
    have b6437 := hb (x (-4) 13)
    clear * - r6435 b6436 b6437 d6430
    omega
  have d6438 : (x (-2) 13).toNat = 0 := by
    have r6439 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
    have b6440 := hb (x (-2) 1)
    have b6441 := hb (x (-2) 13)
    clear * - r6439 b6440 b6441 d6405
    omega
  have d6442 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
    have r6443 := hand2 (x (-2) 3) (x (-2) 13)
    have b6444 := hb (x (-2) 13)
    have b6445 := hb (x (-2) 3 && x (-2) 13)
    clear * - r6443 b6444 b6445 d6438
    omega
  have d6446 : (x (-3) 3).toNat = 0 := by
    have r6447 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6448 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e6449 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b6450 := hb (x (-3) 3)
    have b6451 := hb (x (-2) 2)
    have b6452 := hb (x (-1) 13)
    have b6453 := hb (x 0 12)
    clear * - r6447 e6448 e6449 b6450 b6451 b6452 b6453 g5 d6368 d6380
    omega
  have d6454 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
    have r6455 := hand1 (x (-3) 3) (x (-3) 14)
    have b6456 := hb (x (-3) 3)
    have b6457 := hb (x (-3) 3 && x (-3) 14)
    clear * - r6455 b6456 b6457 d6446
    omega
  have d6458 : (x (-3) 3 && x (-3) 13).toNat = 0 := by
    have r6459 := hand1 (x (-3) 3) (x (-3) 13)
    have b6460 := hb (x (-3) 3)
    have b6461 := hb (x (-3) 3 && x (-3) 13)
    clear * - r6459 b6460 b6461 d6446
    omega
  have d6462 : (x (-1) 12).toNat = 0 := by
    have r6463 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6464 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e6465 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b6466 := hb (x (-4) 3)
    have b6467 := hb (x (-3) 2)
    have b6468 := hb (x (-2) 13)
    have b6469 := hb (x (-1) 12)
    clear * - r6463 e6464 e6465 b6466 b6467 b6468 b6469 d6438 d6413
    omega
  have d6470 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
    have r6471 := hand2 (x (-1) 1) (x (-1) 12)
    have b6472 := hb (x (-1) 12)
    have b6473 := hb (x (-1) 1 && x (-1) 12)
    clear * - r6471 b6472 b6473 d6462
    omega
  have d6474 : (x (-1) 2 && x (-1) 12).toNat = 0 := by
    have r6475 := hand2 (x (-1) 2) (x (-1) 12)
    have b6476 := hb (x (-1) 12)
    have b6477 := hb (x (-1) 2 && x (-1) 12)
    clear * - r6475 b6476 b6477 d6462
    omega
  have d6478 : (x (-1) 4).toNat = 0 := by
    have r6479 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
    have b6480 := hb (x (-1) 4)
    have b6481 := hb (x (-1) 12)
    clear * - r6479 b6480 b6481 d6462
    omega
  have d6482 : (x (-4) 3).toNat = 0 := by
    have r6483 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6484 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e6485 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b6486 := hb (x (-4) 3)
    have b6487 := hb (x (-3) 2)
    have b6488 := hb (x (-2) 13)
    have b6489 := hb (x (-1) 12)
    clear * - r6483 e6484 e6485 b6486 b6487 b6488 b6489 d6462 d6438 d6413
    omega
  have d6490 : (x (-4) 11).toNat = 0 := by
    have r6491 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
    have b6492 := hb (x (-4) 3)
    have b6493 := hb (x (-4) 11)
    clear * - r6491 b6492 b6493 d6482
    omega
  have d6494 : (x (-4) 4).toNat = 1 := by
    have r6495 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6496 := hb (x (-4) 4)
    have b6497 := hb (x 0 11)
    have b6498 := hb (x (-1) 1 && x (-1) 12)
    have b6499 := hb (x (-2) 2 && x (-2) 13)
    have b6500 := hb (x (-3) 3 && x (-3) 14)
    clear * - r6495 b6496 b6497 b6498 b6499 b6500 g4 d6470 d6388 d6454
    omega
  have d6501 : (x (-4) 12).toNat = 1 := by
    have r6502 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
    have b6503 := hb (x (-4) 4)
    have b6504 := hb (x (-4) 12)
    clear * - r6502 b6503 b6504 d6494
    omega
  have d6505 : (x (-5) 13).toNat = 0 := by
    have r6506 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6507 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e6508 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b6509 := hb (x (-7) 3)
    have b6510 := hb (x (-6) 2)
    have b6511 := hb (x (-5) 13)
    have b6512 := hb (x (-4) 12)
    clear * - r6506 e6507 e6508 b6509 b6510 b6511 b6512 d6501
    omega
  have d6513 : (x (-5) 5).toNat = 0 := by
    have r6514 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
    have b6515 := hb (x (-5) 5)
    have b6516 := hb (x (-5) 13)
    clear * - r6514 b6515 b6516 d6505
    omega
  have d6517 : (x (-6) 2).toNat = 0 := by
    have r6518 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6519 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e6520 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b6521 := hb (x (-7) 3)
    have b6522 := hb (x (-6) 2)
    have b6523 := hb (x (-5) 13)
    have b6524 := hb (x (-4) 12)
    clear * - r6518 e6519 e6520 b6521 b6522 b6523 b6524 d6501 d6505
    omega
  have d6525 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
    have r6526 := hand1 (x (-6) 2) (x (-6) 13)
    have b6527 := hb (x (-6) 2)
    have b6528 := hb (x (-6) 2 && x (-6) 13)
    clear * - r6526 b6527 b6528 d6517
    omega
  have d6529 : (x (-6) 2 && x (-6) 12).toNat = 0 := by
    have r6530 := hand1 (x (-6) 2) (x (-6) 12)
    have b6531 := hb (x (-6) 2)
    have b6532 := hb (x (-6) 2 && x (-6) 12)
    clear * - r6530 b6531 b6532 d6517
    omega
  have d6533 : (x (-5) 1 && x (-5) 14).toNat = 1 := by
    have r6534 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6535 := hb (x (-6) 2)
    have b6536 := hb (x (-4) 13)
    have b6537 := hb (x (-5) 1 && x (-5) 14)
    clear * - r6534 b6535 b6536 b6537 d6430 d6517
    omega
  have d6538 : (x (-5) 14).toNat = 1 := by
    have r6539 := hand2 (x (-5) 1) (x (-5) 14)
    have b6540 := hb (x (-5) 14)
    have b6541 := hb (x (-5) 1 && x (-5) 14)
    clear * - r6539 b6540 b6541 d6533
    omega
  have d6542 : (x (-6) 1).toNat = 0 := by
    have r6543 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6544 := hb (x (-6) 1)
    have b6545 := hb (x (-5) 14)
    clear * - r6543 b6544 b6545 d6538
    omega
  have d6546 : (x (-6) 1 && x (-6) 14).toNat = 0 := by
    have r6547 := hand1 (x (-6) 1) (x (-6) 14)
    have b6548 := hb (x (-6) 1)
    have b6549 := hb (x (-6) 1 && x (-6) 14)
    clear * - r6547 b6548 b6549 d6542
    omega
  have d6550 : (x (-7) 2).toNat = 1 := by
    have r6551 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6552 := hb (x (-7) 2)
    have b6553 := hb (x (-5) 13)
    have b6554 := hb (x (-6) 1 && x (-6) 14)
    clear * - r6551 b6552 b6553 b6554 d6505 d6546
    omega
  have d6555 : (x (-7) 14).toNat = 1 := by
    have r6556 : (x (-7) 2).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp2 (-7))
    have b6557 := hb (x (-7) 2)
    have b6558 := hb (x (-7) 14)
    clear * - r6556 b6557 b6558 d6550
    omega
  have d6559 : (x (-8) 1).toNat = 0 := by
    have r6560 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6561 := hb (x (-8) 1)
    have b6562 := hb (x (-7) 14)
    clear * - r6560 b6561 b6562 d6555
    omega
  have d6563 : (x (-8) 13).toNat = 0 := by
    have r6564 : (x (-8) 13).toNat ≤ (x (-8) 1).toNat := himp _ _ (hp13 (-8))
    have b6565 := hb (x (-8) 1)
    have b6566 := hb (x (-8) 13)
    clear * - r6564 b6565 b6566 d6559
    omega
  have d6567 : (x (-5) 12).toNat = 0 := by
    have r6568 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6569 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
    have e6570 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
    have b6571 := hb (x (-8) 3)
    have b6572 := hb (x (-7) 2)
    have b6573 := hb (x (-6) 13)
    have b6574 := hb (x (-5) 12)
    clear * - r6568 e6569 e6570 b6571 b6572 b6573 b6574 d6550
    omega
  have d6575 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
    have r6576 := hand2 (x (-5) 1) (x (-5) 12)
    have b6577 := hb (x (-5) 12)
    have b6578 := hb (x (-5) 1 && x (-5) 12)
    clear * - r6576 b6577 b6578 d6567
    omega
  have d6579 : (x (-5) 1).toNat = 1 := by
    have r6580 := hand1 (x (-5) 1) (x (-5) 14)
    have b6581 := hb (x (-5) 1)
    have b6582 := hb (x (-5) 1 && x (-5) 14)
    clear * - r6580 b6581 b6582 d6533
    omega
  have d6583 : (x (-4) 14).toNat = 0 := by
    have r6584 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6585 := hb (x (-5) 1)
    have b6586 := hb (x (-4) 14)
    clear * - r6584 b6585 b6586 d6579
    omega
  have d6587 : (x (-4) 4 && x (-4) 14).toNat = 0 := by
    have r6588 := hand2 (x (-4) 4) (x (-4) 14)
    have b6589 := hb (x (-4) 14)
    have b6590 := hb (x (-4) 4 && x (-4) 14)
    clear * - r6588 b6589 b6590 d6583
    omega
  have d6591 : (x (-4) 2).toNat = 0 := by
    have r6592 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
    have b6593 := hb (x (-4) 2)
    have b6594 := hb (x (-4) 14)
    clear * - r6592 b6593 b6594 d6583
    omega
  have d6595 : (x (-4) 10).toNat = 0 := by
    have r6596 : (x (-4) 10).toNat ≤ (x (-4) 2).toNat := himp _ _ (hp10 (-4))
    have b6597 := hb (x (-4) 2)
    have b6598 := hb (x (-4) 10)
    clear * - r6596 b6597 b6598 d6591
    omega
  have d6599 : (x (-7) 3).toNat = 0 := by
    have r6600 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6601 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e6602 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b6603 := hb (x (-7) 3)
    have b6604 := hb (x (-6) 2)
    have b6605 := hb (x (-5) 13)
    have b6606 := hb (x (-4) 12)
    clear * - r6600 e6601 e6602 b6603 b6604 b6605 b6606 d6501 d6505 d6517
    omega
  have d6607 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
    have r6608 := hand1 (x (-7) 3) (x (-7) 14)
    have b6609 := hb (x (-7) 3)
    have b6610 := hb (x (-7) 3 && x (-7) 14)
    clear * - r6608 b6609 b6610 d6599
    omega
  have d6611 : (x (-7) 3 && x (-7) 13).toNat = 0 := by
    have r6612 := hand1 (x (-7) 3) (x (-7) 13)
    have b6613 := hb (x (-7) 3)
    have b6614 := hb (x (-7) 3 && x (-7) 13)
    clear * - r6612 b6613 b6614 d6599
    omega
  have d6615 : (x (-8) 4).toNat = 1 := by
    have r6616 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6617 := hb (x (-8) 4)
    have b6618 := hb (x (-4) 11)
    have b6619 := hb (x (-5) 1 && x (-5) 12)
    have b6620 := hb (x (-6) 2 && x (-6) 13)
    have b6621 := hb (x (-7) 3 && x (-7) 14)
    clear * - r6616 b6617 b6618 b6619 b6620 b6621 d6490 d6575 d6525 d6607
    omega
  have d6622 : (x (-8) 12).toNat = 1 := by
    have r6623 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
    have b6624 := hb (x (-8) 4)
    have b6625 := hb (x (-8) 12)
    clear * - r6623 b6624 b6625 d6615
    omega
  have d6626 : (x (-9) 13).toNat = 0 := by
    have r6627 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6628 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
    have e6629 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
    have b6630 := hb (x (-11) 3)
    have b6631 := hb (x (-10) 2)
    have b6632 := hb (x (-9) 13)
    have b6633 := hb (x (-8) 12)
    clear * - r6627 e6628 e6629 b6630 b6631 b6632 b6633 d6622
    omega
  have d6634 : (x (-9) 5).toNat = 0 := by
    have r6635 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
    have b6636 := hb (x (-9) 5)
    have b6637 := hb (x (-9) 13)
    clear * - r6635 b6636 b6637 d6626
    omega
  have d6638 : (x (-10) 2).toNat = 0 := by
    have r6639 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6640 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
    have e6641 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
    have b6642 := hb (x (-11) 3)
    have b6643 := hb (x (-10) 2)
    have b6644 := hb (x (-9) 13)
    have b6645 := hb (x (-8) 12)
    clear * - r6639 e6640 e6641 b6642 b6643 b6644 b6645 d6622 d6626
    omega
  have d6646 : (x (-9) 1 && x (-9) 14).toNat = 1 := by
    have r6647 : 1 ≤ (x (-8) 13).toNat + (x (-9) 1 && x (-9) 14).toNat + (x (-10) 2).toNat := by have q := hcov13 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6648 := hb (x (-10) 2)
    have b6649 := hb (x (-8) 13)
    have b6650 := hb (x (-9) 1 && x (-9) 14)
    clear * - r6647 b6648 b6649 b6650 d6563 d6638
    omega
  have d6651 : (x (-9) 1).toNat = 1 := by
    have r6652 := hand1 (x (-9) 1) (x (-9) 14)
    have b6653 := hb (x (-9) 1)
    have b6654 := hb (x (-9) 1 && x (-9) 14)
    clear * - r6652 b6653 b6654 d6646
    omega
  have d6655 : (x (-8) 14).toNat = 0 := by
    have r6656 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6657 := hb (x (-9) 1)
    have b6658 := hb (x (-8) 14)
    clear * - r6656 b6657 b6658 d6651
    omega
  have d6659 : (x (-8) 4 && x (-8) 14).toNat = 0 := by
    have r6660 := hand2 (x (-8) 4) (x (-8) 14)
    have b6661 := hb (x (-8) 14)
    have b6662 := hb (x (-8) 4 && x (-8) 14)
    clear * - r6660 b6661 b6662 d6655
    omega
  have d6663 : (x (-1) 1 && x (-1) 11).toNat = 1 := by
    have r6664 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6665 := hb (x (-5) 5)
    have b6666 := hb (x 0 10)
    have b6667 := hb (x (-1) 1 && x (-1) 11)
    have b6668 := hb (x (-2) 2 && x (-2) 12)
    have b6669 := hb (x (-3) 3 && x (-3) 13)
    have b6670 := hb (x (-4) 4 && x (-4) 14)
    clear * - r6664 b6665 b6666 b6667 b6668 b6669 b6670 g3 d6392 d6458 d6587 d6513
    omega
  have d6671 : (x (-1) 11).toNat = 1 := by
    have r6672 := hand2 (x (-1) 1) (x (-1) 11)
    have b6673 := hb (x (-1) 11)
    have b6674 := hb (x (-1) 1 && x (-1) 11)
    clear * - r6672 b6673 b6674 d6663
    omega
  have d6675 : (x (-1) 3).toNat = 1 := by
    have r6676 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
    have b6677 := hb (x (-1) 3)
    have b6678 := hb (x (-1) 11)
    clear * - r6676 b6677 b6678 d6671
    omega
  have d6679 : (x 2 12).toNat = 0 := by
    have r6680 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6681 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e6682 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b6683 := hb (x (-1) 3)
    have b6684 := hb (x 0 2)
    have b6685 := hb (x 1 13)
    have b6686 := hb (x 2 12)
    clear * - r6680 e6681 e6682 b6683 b6684 b6685 b6686 g0 d6675
    omega
  have d6687 : (x 2 1 && x 2 12).toNat = 0 := by
    have r6688 := hand2 (x 2 1) (x 2 12)
    have b6689 := hb (x 2 12)
    have b6690 := hb (x 2 1 && x 2 12)
    clear * - r6688 b6689 b6690 d6679
    omega
  have d6691 : (x 2 2 && x 2 12).toNat = 0 := by
    have r6692 := hand2 (x 2 2) (x 2 12)
    have b6693 := hb (x 2 12)
    have b6694 := hb (x 2 2 && x 2 12)
    clear * - r6692 b6693 b6694 d6679
    omega
  have d6695 : (x 1 13).toNat = 0 := by
    have r6696 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6697 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e6698 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b6699 := hb (x (-1) 3)
    have b6700 := hb (x 0 2)
    have b6701 := hb (x 1 13)
    have b6702 := hb (x 2 12)
    clear * - r6696 e6697 e6698 b6699 b6700 b6701 b6702 d6679 g0 d6675
    omega
  have d6703 : (x 1 2 && x 1 13).toNat = 0 := by
    have r6704 := hand2 (x 1 2) (x 1 13)
    have b6705 := hb (x 1 13)
    have b6706 := hb (x 1 2 && x 1 13)
    clear * - r6704 b6705 b6706 d6695
    omega
  have d6707 : (x 3 11).toNat = 1 := by
    have r6708 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6709 := hb (x (-1) 4)
    have b6710 := hb (x 3 11)
    have b6711 := hb (x 2 1 && x 2 12)
    have b6712 := hb (x 1 2 && x 1 13)
    have b6713 := hb (x 0 3 && x 0 14)
    clear * - r6708 b6709 b6710 b6711 b6712 b6713 d6687 d6703 g11 d6478
    omega
  have d6714 : (x 3 3).toNat = 1 := by
    have r6715 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
    have b6716 := hb (x 3 3)
    have b6717 := hb (x 3 11)
    clear * - r6715 b6716 b6717 d6707
    omega
  have d6718 : (x 6 12).toNat = 0 := by
    have r6719 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6720 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e6721 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b6722 := hb (x 3 3)
    have b6723 := hb (x 4 2)
    have b6724 := hb (x 5 13)
    have b6725 := hb (x 6 12)
    clear * - r6719 e6720 e6721 b6722 b6723 b6724 b6725 d6714
    omega
  have d6726 : (x 5 13).toNat = 0 := by
    have r6727 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6728 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e6729 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b6730 := hb (x 3 3)
    have b6731 := hb (x 4 2)
    have b6732 := hb (x 5 13)
    have b6733 := hb (x 6 12)
    clear * - r6727 e6728 e6729 b6730 b6731 b6732 b6733 d6718 d6714
    omega
  have d6734 : (x 4 2).toNat = 0 := by
    have r6735 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6736 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e6737 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b6738 := hb (x 3 3)
    have b6739 := hb (x 4 2)
    have b6740 := hb (x 5 13)
    have b6741 := hb (x 6 12)
    clear * - r6735 e6736 e6737 b6738 b6739 b6740 b6741 d6718 d6726 d6714
    omega
  have d6742 : (x 4 10).toNat = 0 := by
    have r6743 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
    have b6744 := hb (x 4 2)
    have b6745 := hb (x 4 10)
    clear * - r6743 b6744 b6745 d6734
    omega
  have d6746 : (x 1 3 && x 1 13).toNat = 0 := by
    have r6747 := hand2 (x 1 3) (x 1 13)
    have b6748 := hb (x 1 13)
    have b6749 := hb (x 1 3 && x 1 13)
    clear * - r6747 b6748 b6749 d6695
    omega
  have d6750 : (x 3 1 && x 3 11).toNat = 1 := by
    have r6751 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6752 := hb (x (-1) 5)
    have b6753 := hb (x 4 10)
    have b6754 := hb (x 3 1 && x 3 11)
    have b6755 := hb (x 2 2 && x 2 12)
    have b6756 := hb (x 1 3 && x 1 13)
    have b6757 := hb (x 0 4 && x 0 14)
    clear * - r6751 b6752 b6753 b6754 b6755 b6756 b6757 d6742 d6691 d6746 g9 d6376
    omega
  have d6758 : (x 3 1).toNat = 1 := by
    have r6759 := hand1 (x 3 1) (x 3 11)
    have b6760 := hb (x 3 1)
    have b6761 := hb (x 3 1 && x 3 11)
    clear * - r6759 b6760 b6761 d6750
    omega
  have d6762 : (x 4 14).toNat = 0 := by
    have r6763 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6764 := hb (x 3 1)
    have b6765 := hb (x 4 14)
    clear * - r6763 b6764 b6765 d6758
    omega
  have d6766 : (x 4 1 && x 4 14).toNat = 0 := by
    have r6767 := hand2 (x 4 1) (x 4 14)
    have b6768 := hb (x 4 14)
    have b6769 := hb (x 4 1 && x 4 14)
    clear * - r6767 b6768 b6769 d6762
    omega
  have d6770 : (x 3 2).toNat = 1 := by
    have r6771 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6772 := hb (x 3 2)
    have b6773 := hb (x 5 13)
    have b6774 := hb (x 4 1 && x 4 14)
    clear * - r6771 b6772 b6773 b6774 d6726 d6766
    omega
  have d6775 : (x 3 14).toNat = 1 := by
    have r6776 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
    have b6777 := hb (x 3 2)
    have b6778 := hb (x 3 14)
    clear * - r6776 b6777 b6778 d6770
    omega
  have d6779 : (x 2 1).toNat = 0 := by
    have r6780 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6781 := hb (x 2 1)
    have b6782 := hb (x 3 14)
    clear * - r6780 b6781 b6782 d6775
    omega
  have d6783 : (x 2 13).toNat = 0 := by
    have r6784 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
    have b6785 := hb (x 2 1)
    have b6786 := hb (x 2 13)
    clear * - r6784 b6785 b6786 d6779
    omega
  have d6787 : (x 2 3 && x 2 13).toNat = 0 := by
    have r6788 := hand2 (x 2 3) (x 2 13)
    have b6789 := hb (x 2 13)
    have b6790 := hb (x 2 3 && x 2 13)
    clear * - r6788 b6789 b6790 d6783
    omega
  have d6791 : (x (-1) 2).toNat = 1 := by
    have r6792 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6793 := hb (x (-1) 2)
    have b6794 := hb (x 1 13)
    have b6795 := hb (x 0 1 && x 0 14)
    clear * - r6792 b6793 b6794 b6795 d6695 g12
    omega
  have d6796 : (x 1 12).toNat = 0 := by
    have r6797 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6798 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e6799 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b6800 := hb (x (-2) 3)
    have b6801 := hb (x (-1) 2)
    have b6802 := hb (x 0 13)
    have b6803 := hb (x 1 12)
    clear * - r6797 e6798 e6799 b6800 b6801 b6802 b6803 g6 d6791
    omega
  have d6804 : (x 1 4).toNat = 0 := by
    have r6805 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
    have b6806 := hb (x 1 4)
    have b6807 := hb (x 1 12)
    clear * - r6805 b6806 b6807 d6796
    omega
  have d6808 : (x 1 4 && x 1 14).toNat = 0 := by
    have r6809 := hand1 (x 1 4) (x 1 14)
    have b6810 := hb (x 1 4)
    have b6811 := hb (x 1 4 && x 1 14)
    clear * - r6809 b6810 b6811 d6804
    omega
  have d6812 : (x 3 2 && x 3 12).toNat = 1 := by
    have r6813 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6814 := hb (x 0 5)
    have b6815 := hb (x 5 10)
    have b6816 := hb (x 4 1 && x 4 11)
    have b6817 := hb (x 3 2 && x 3 12)
    have b6818 := hb (x 2 3 && x 2 13)
    have b6819 := hb (x 1 4 && x 1 14)
    clear * - r6813 b6814 b6815 b6816 b6817 b6818 b6819 g7 g10 d6787 d6808 g2
    omega
  have d6820 : (x 3 12).toNat = 1 := by
    have r6821 := hand2 (x 3 2) (x 3 12)
    have b6822 := hb (x 3 12)
    have b6823 := hb (x 3 2 && x 3 12)
    clear * - r6821 b6822 b6823 d6812
    omega
  have d6824 : (x 1 2).toNat = 0 := by
    have r6825 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6826 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e6827 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b6828 := hb (x 0 3)
    have b6829 := hb (x 1 2)
    have b6830 := hb (x 2 13)
    have b6831 := hb (x 3 12)
    clear * - r6825 e6826 e6827 b6828 b6829 b6830 b6831 d6820 d6783 g1
    omega
  have d6832 : (x 1 10).toNat = 0 := by
    have r6833 : (x 1 10).toNat ≤ (x 1 2).toNat := himp _ _ (hp10 1)
    have b6834 := hb (x 1 2)
    have b6835 := hb (x 1 10)
    clear * - r6833 b6834 b6835 d6824
    omega
  have d6836 : (x (-3) 4 && x (-3) 14).toNat = 1 := by
    have r6837 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6838 := hb (x (-4) 5)
    have b6839 := hb (x 1 10)
    have b6840 := hb (x 0 1 && x 0 11)
    have b6841 := hb (x (-1) 2 && x (-1) 12)
    have b6842 := hb (x (-2) 3 && x (-2) 13)
    have b6843 := hb (x (-3) 4 && x (-3) 14)
    clear * - r6837 b6838 b6839 b6840 b6841 b6842 b6843 d6832 g8 d6474 d6442 d6434
    omega
  have d6844 : (x (-3) 4).toNat = 1 := by
    have r6845 := hand1 (x (-3) 4) (x (-3) 14)
    have b6846 := hb (x (-3) 4)
    have b6847 := hb (x (-3) 4 && x (-3) 14)
    clear * - r6845 b6846 b6847 d6836
    omega
  have d6848 : (x (-3) 12).toNat = 1 := by
    have r6849 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
    have b6850 := hb (x (-3) 4)
    have b6851 := hb (x (-3) 12)
    clear * - r6849 b6850 b6851 d6844
    omega
  have d6852 : (x (-5) 2).toNat = 0 := by
    have r6853 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6854 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
    have e6855 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
    have b6856 := hb (x (-6) 3)
    have b6857 := hb (x (-5) 2)
    have b6858 := hb (x (-4) 13)
    have b6859 := hb (x (-3) 12)
    clear * - r6853 e6854 e6855 b6856 b6857 b6858 b6859 d6848 d6430
    omega
  have d6860 : (x (-3) 13).toNat = 1 := by
    have r6861 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6862 := hb (x (-5) 2)
    have b6863 := hb (x (-3) 13)
    have b6864 := hb (x (-4) 1 && x (-4) 14)
    clear * - r6861 b6862 b6863 b6864 d6426 d6852
    omega
  have d6865 : (x (-2) 12).toNat = 0 := by
    have r6866 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6867 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
    have e6868 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
    have b6869 := hb (x (-5) 3)
    have b6870 := hb (x (-4) 2)
    have b6871 := hb (x (-3) 13)
    have b6872 := hb (x (-2) 12)
    clear * - r6866 e6867 e6868 b6869 b6870 b6871 b6872 d6860 d6591
    omega
  have d6873 : (x (-5) 3).toNat = 0 := by
    have r6874 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6875 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
    have e6876 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
    have b6877 := hb (x (-5) 3)
    have b6878 := hb (x (-4) 2)
    have b6879 := hb (x (-3) 13)
    have b6880 := hb (x (-2) 12)
    clear * - r6874 e6875 e6876 b6877 b6878 b6879 b6880 d6865 d6860 d6591
    omega
  have d6881 : (x (-5) 11).toNat = 0 := by
    have r6882 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
    have b6883 := hb (x (-5) 3)
    have b6884 := hb (x (-5) 11)
    clear * - r6882 b6883 b6884 d6873
    omega
  have d6885 : (x (-5) 1 && x (-5) 11).toNat = 0 := by
    have r6886 := hand2 (x (-5) 1) (x (-5) 11)
    have b6887 := hb (x (-5) 11)
    have b6888 := hb (x (-5) 1 && x (-5) 11)
    clear * - r6886 b6887 b6888 d6881
    omega
  have r6889 : 1 ≤ (x (-4) 10).toNat + (x (-5) 1 && x (-5) 11).toNat + (x (-6) 2 && x (-6) 12).toNat + (x (-7) 3 && x (-7) 13).toNat + (x (-8) 4 && x (-8) 14).toNat + (x (-9) 5).toNat := by have q := hcov10 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have b6890 := hb (x (-9) 5)
  have b6891 := hb (x (-4) 10)
  have b6892 := hb (x (-5) 1 && x (-5) 11)
  have b6893 := hb (x (-6) 2 && x (-6) 12)
  have b6894 := hb (x (-7) 3 && x (-7) 13)
  have b6895 := hb (x (-8) 4 && x (-8) 14)
  linarith only [r6889, b6890, b6891, b6892, b6893, b6894, b6895, d6595, d6885, d6529, d6611, d6659, d6634]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b00001_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 2).toNat = 0)
    (g1 : (x 0 3).toNat = 1)
    (g2 : (x 0 4).toNat = 0)
    (g3 : (x 4 11).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d6897 : (x 3 12).toNat = 0 := by
    have r6898 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6899 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e6900 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b6901 := hb (x 0 3)
    have b6902 := hb (x 1 2)
    have b6903 := hb (x 2 13)
    have b6904 := hb (x 3 12)
    clear * - r6898 e6899 e6900 b6901 b6902 b6903 b6904 g1
    omega
  have d6905 : (x 3 1 && x 3 12).toNat = 0 := by
    have r6906 := hand2 (x 3 1) (x 3 12)
    have b6907 := hb (x 3 12)
    have b6908 := hb (x 3 1 && x 3 12)
    clear * - r6906 b6907 b6908 d6897
    omega
  have d6909 : (x 2 13).toNat = 0 := by
    have r6910 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6911 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e6912 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b6913 := hb (x 0 3)
    have b6914 := hb (x 1 2)
    have b6915 := hb (x 2 13)
    have b6916 := hb (x 3 12)
    clear * - r6910 e6911 e6912 b6913 b6914 b6915 b6916 d6897 g1
    omega
  have d6917 : (x 2 2 && x 2 13).toNat = 0 := by
    have r6918 := hand2 (x 2 2) (x 2 13)
    have b6919 := hb (x 2 13)
    have b6920 := hb (x 2 2 && x 2 13)
    clear * - r6918 b6919 b6920 d6909
    omega
  have d6921 : (x 1 1 && x 1 14).toNat = 1 := by
    have r6922 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6923 := hb (x 0 2)
    have b6924 := hb (x 2 13)
    have b6925 := hb (x 1 1 && x 1 14)
    clear * - r6922 b6923 b6924 b6925 d6909 g0
    omega
  have d6926 : (x 1 1).toNat = 1 := by
    have r6927 := hand1 (x 1 1) (x 1 14)
    have b6928 := hb (x 1 1)
    have b6929 := hb (x 1 1 && x 1 14)
    clear * - r6927 b6928 b6929 d6921
    omega
  have d6930 : (x 2 14).toNat = 0 := by
    have r6931 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6932 := hb (x 1 1)
    have b6933 := hb (x 2 14)
    clear * - r6931 b6932 b6933 d6926
    omega
  have d6934 : (x 2 1 && x 2 14).toNat = 0 := by
    have r6935 := hand2 (x 2 1) (x 2 14)
    have b6936 := hb (x 2 14)
    have b6937 := hb (x 2 1 && x 2 14)
    clear * - r6935 b6936 b6937 d6930
    omega
  have d6938 : (x 2 2).toNat = 0 := by
    have r6939 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
    have b6940 := hb (x 2 2)
    have b6941 := hb (x 2 14)
    clear * - r6939 b6940 b6941 d6930
    omega
  have d6942 : (x 1 2).toNat = 0 := by
    have r6943 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6944 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e6945 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b6946 := hb (x 0 3)
    have b6947 := hb (x 1 2)
    have b6948 := hb (x 2 13)
    have b6949 := hb (x 3 12)
    clear * - r6943 e6944 e6945 b6946 b6947 b6948 b6949 d6897 d6909 g1
    omega
  have d6950 : (x 3 13).toNat = 1 := by
    have r6951 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6952 := hb (x 1 2)
    have b6953 := hb (x 3 13)
    have b6954 := hb (x 2 1 && x 2 14)
    clear * - r6951 b6952 b6953 b6954 d6934 d6942
    omega
  have d6955 : (x 4 12).toNat = 0 := by
    have r6956 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6957 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e6958 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b6959 := hb (x 1 3)
    have b6960 := hb (x 2 2)
    have b6961 := hb (x 3 13)
    have b6962 := hb (x 4 12)
    clear * - r6956 e6957 e6958 b6959 b6960 b6961 b6962 d6950 d6938
    omega
  have d6963 : (x 1 3).toNat = 0 := by
    have r6964 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6965 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e6966 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b6967 := hb (x 1 3)
    have b6968 := hb (x 2 2)
    have b6969 := hb (x 3 13)
    have b6970 := hb (x 4 12)
    clear * - r6964 e6965 e6966 b6967 b6968 b6969 b6970 d6955 d6950 d6938
    omega
  have d6971 : (x 1 3 && x 1 14).toNat = 0 := by
    have r6972 := hand1 (x 1 3) (x 1 14)
    have b6973 := hb (x 1 3)
    have b6974 := hb (x 1 3 && x 1 14)
    clear * - r6972 b6973 b6974 d6963
    omega
  have r6975 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have b6976 := hb (x 0 4)
  have b6977 := hb (x 4 11)
  have b6978 := hb (x 3 1 && x 3 12)
  have b6979 := hb (x 2 2 && x 2 13)
  have b6980 := hb (x 1 3 && x 1 14)
  linarith only [r6975, b6976, b6977, b6978, b6979, b6980, g3, d6905, d6917, d6971, g2]

theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b00001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 2).toNat = 0)
    (g1 : (x 0 3).toNat = 1)
    (g2 : (x 0 4).toNat = 0)
    (g3 : (x 4 11).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b00001_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3
