import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b110

Topic: combinatorics   Node: 015f7c1a550d

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_six_iff_seven_core: under the layer-free tight-cover constraints for k = 15 and 58 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b110_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-2) 11).toNat = 0)
    (g1 : (x (-1) 2).toNat = 0)
    (g2 : (x (-1) 10).toNat = 0)
    (g3 : (x 0 2).toNat = 0)
    (g4 : (x 0 6).toNat = 0)
    (g5 : (x 0 13).toNat = 1)
    (g6 : (x 1 2).toNat = 0)
    (g7 : (x 1 4).toNat = 0)
    (g8 : (x 1 6).toNat = 0)
    (g9 : (x 1 10).toNat = 0)
    (g10 : (x 1 12).toNat = 0)
    (g11 : (x 2 5).toNat = 0)
    (g12 : (x 4 11).toNat = 0)
    (g13 : (x 5 10).toNat = 0)
    (g14 : (x 6 9).toNat = 0)
    (g15 : (x 1 4 && x 1 8).toNat = 0)
    (g16 : (x (-1) 6 && x (-1) 10).toNat = 0)
    (g17 : (x (-2) 7 && x (-2) 11).toNat = 0)
    (g18 : (x 1 8 && x 1 12).toNat = 0)
    (g19 : (x 0 6 && x 0 12).toNat = 0)
    (g20 : (x 7 2 && x 7 8).toNat = 0)
    (g21 : (x 6 3 && x 6 9).toNat = 0)
    (g22 : (x 5 4 && x 5 10).toNat = 0)
    (g23 : (x 4 5 && x 4 11).toNat = 0)
    (g24 : (x 1 8 && x 1 14).toNat = 0)
    (g25 : (x (-1) 3 && x (-1) 10).toNat = 0)
    (g26 : (x (-2) 4 && x (-2) 11).toNat = 0)
    (g27 : (x 1 3 && x 1 10).toNat = 0)
    (g28 : (x 1 5 && x 1 12).toNat = 0)
    (g29 : (x 0 6 && x 0 13).toNat = 0)
    (g30 : (x 7 1 && x 7 8).toNat = 0)
    (g31 : (x 6 2 && x 6 9).toNat = 0)
    (g32 : (x 5 3 && x 5 10).toNat = 0)
    (g33 : (x 4 4 && x 4 11).toNat = 0)
    (g34 : (x 1 7 && x 1 14).toNat = 0)
    (g35 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g36 : (x (-2) 2 && x (-2) 11).toNat = 0)
    (g37 : (x (-1) 2 && x (-1) 11).toNat = 0)
    (g38 : (x (-2) 3 && x (-2) 12).toNat = 0)
    (g39 : (x 1 2 && x 1 11).toNat = 0)
    (g40 : (x 1 3 && x 1 12).toNat = 0)
    (g41 : (x 1 4 && x 1 13).toNat = 0)
    (g42 : (x 5 1 && x 5 10).toNat = 0)
    (g43 : (x 4 2 && x 4 11).toNat = 0)
    (g44 : (x 1 5 && x 1 14).toNat = 0)
    (g45 : (x 3 4 && x 3 13).toNat = 0)
    (g46 : (x 2 5 && x 2 14).toNat = 0)
    (g47 : (x (-1) 2 && x (-1) 12).toNat = 0)
    (g48 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g49 : (x 1 2 && x 1 12).toNat = 0)
    (g50 : (x 4 1 && x 4 11).toNat = 0)
    (g51 : (x 1 4 && x 1 14).toNat = 0)
    (g52 : (x 3 4 && x 3 14).toNat = 0)
    (g53 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g54 : (x (-2) 3 && x (-2) 14).toNat = 0)
    (g55 : (x 1 1 && x 1 12).toNat = 0)
    (g56 : (x 1 3 && x 1 14).toNat = 0)
    (g57 : (x 1 1 && x 1 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d22624 : (x 0 2 && x 0 13).toNat = 0 := by
    have r22625 := hand1 (x 0 2) (x 0 13)
    have b22626 := hb (x 0 2)
    have b22627 := hb (x 0 2 && x 0 13)
    clear * - r22625 b22626 b22627 g3
    omega
  have d22628 : (x 0 2 && x 0 12).toNat = 0 := by
    have r22629 := hand1 (x 0 2) (x 0 12)
    have b22630 := hb (x 0 2)
    have b22631 := hb (x 0 2 && x 0 12)
    clear * - r22629 b22630 b22631 g3
    omega
  have d22632 : (x 0 2 && x 0 9).toNat = 0 := by
    have r22633 := hand1 (x 0 2) (x 0 9)
    have b22634 := hb (x 0 2)
    have b22635 := hb (x 0 2 && x 0 9)
    clear * - r22633 b22634 b22635 g3
    omega
  have d22636 : (x 0 10).toNat = 0 := by
    have r22637 : (x 0 10).toNat ≤ (x 0 2).toNat := himp _ _ (hp10 0)
    have b22638 := hb (x 0 2)
    have b22639 := hb (x 0 10)
    clear * - r22637 b22638 b22639 g3
    omega
  have d22640 : (x 0 1 && x 0 10).toNat = 0 := by
    have r22641 := hand2 (x 0 1) (x 0 10)
    have b22642 := hb (x 0 10)
    have b22643 := hb (x 0 1 && x 0 10)
    clear * - r22641 b22642 b22643 d22636
    omega
  have d22644 : (x 2 13).toNat = 1 := by
    have r22645 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b22646 := hb (x 0 2)
    have b22647 := hb (x 2 13)
    have b22648 := hb (x 1 1 && x 1 14)
    clear * - r22645 b22646 b22647 b22648 g57 g3
    omega
  have d22649 : (x 2 1).toNat = 1 := by
    have r22650 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
    have b22651 := hb (x 2 1)
    have b22652 := hb (x 2 13)
    clear * - r22650 b22651 b22652 d22644
    omega
  have d22653 : (x 3 14).toNat = 0 := by
    have r22654 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b22655 := hb (x 2 1)
    have b22656 := hb (x 3 14)
    clear * - r22654 b22655 b22656 d22649
    omega
  have d22657 : (x 3 5 && x 3 14).toNat = 0 := by
    have r22658 := hand2 (x 3 5) (x 3 14)
    have b22659 := hb (x 3 14)
    have b22660 := hb (x 3 5 && x 3 14)
    clear * - r22658 b22659 b22660 d22653
    omega
  have d22661 : (x 3 6).toNat = 0 := by
    have r22662 : (x 3 6).toNat ≤ (x 3 14).toNat := himp _ _ (hp6 3)
    have b22663 := hb (x 3 6)
    have b22664 := hb (x 3 14)
    clear * - r22662 b22663 b22664 d22653
    omega
  have d22665 : (x 3 6 && x 3 12).toNat = 0 := by
    have r22666 := hand1 (x 3 6) (x 3 12)
    have b22667 := hb (x 3 6)
    have b22668 := hb (x 3 6 && x 3 12)
    clear * - r22666 b22667 b22668 d22661
    omega
  have d22669 : (x 3 6 && x 3 10).toNat = 0 := by
    have r22670 := hand1 (x 3 6) (x 3 10)
    have b22671 := hb (x 3 6)
    have b22672 := hb (x 3 6 && x 3 10)
    clear * - r22670 b22671 b22672 d22661
    omega
  have d22673 : (x 3 2 && x 3 6).toNat = 0 := by
    have r22674 := hand2 (x 3 2) (x 3 6)
    have b22675 := hb (x 3 6)
    have b22676 := hb (x 3 2 && x 3 6)
    clear * - r22674 b22675 b22676 d22661
    omega
  have d22677 : (x 3 2).toNat = 0 := by
    have r22678 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
    have b22679 := hb (x 3 2)
    have b22680 := hb (x 3 14)
    clear * - r22678 b22679 b22680 d22653
    omega
  have d22681 : (x 3 2 && x 3 12).toNat = 0 := by
    have r22682 := hand1 (x 3 2) (x 3 12)
    have b22683 := hb (x 3 2)
    have b22684 := hb (x 3 2 && x 3 12)
    clear * - r22682 b22683 b22684 d22677
    omega
  have d22685 : (x 3 2 && x 3 11).toNat = 0 := by
    have r22686 := hand1 (x 3 2) (x 3 11)
    have b22687 := hb (x 3 2)
    have b22688 := hb (x 3 2 && x 3 11)
    clear * - r22686 b22687 b22688 d22677
    omega
  have d22689 : (x 3 10).toNat = 0 := by
    have r22690 : (x 3 10).toNat ≤ (x 3 2).toNat := himp _ _ (hp10 3)
    have b22691 := hb (x 3 2)
    have b22692 := hb (x 3 10)
    clear * - r22690 b22691 b22692 d22677
    omega
  have d22693 : (x 3 1 && x 3 10).toNat = 0 := by
    have r22694 := hand2 (x 3 1) (x 3 10)
    have b22695 := hb (x 3 10)
    have b22696 := hb (x 3 1 && x 3 10)
    clear * - r22694 b22695 b22696 d22689
    omega
  have d22697 : (x 3 3 && x 3 10).toNat = 0 := by
    have r22698 := hand2 (x 3 3) (x 3 10)
    have b22699 := hb (x 3 10)
    have b22700 := hb (x 3 3 && x 3 10)
    clear * - r22698 b22699 b22700 d22689
    omega
  have d22701 : (x 3 12).toNat = 0 := by
    have r22702 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e22703 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e22704 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b22705 := hb (x 0 3)
    have b22706 := hb (x 1 2)
    have b22707 := hb (x 2 13)
    have b22708 := hb (x 3 12)
    clear * - r22702 e22703 e22704 b22705 b22706 b22707 b22708 d22644 g6
    omega
  have d22709 : (x 3 1 && x 3 12).toNat = 0 := by
    have r22710 := hand2 (x 3 1) (x 3 12)
    have b22711 := hb (x 3 12)
    have b22712 := hb (x 3 1 && x 3 12)
    clear * - r22710 b22711 b22712 d22701
    omega
  have d22713 : (x 3 3 && x 3 12).toNat = 0 := by
    have r22714 := hand2 (x 3 3) (x 3 12)
    have b22715 := hb (x 3 12)
    have b22716 := hb (x 3 3 && x 3 12)
    clear * - r22714 b22715 b22716 d22701
    omega
  have d22717 : (x 3 5 && x 3 12).toNat = 0 := by
    have r22718 := hand2 (x 3 5) (x 3 12)
    have b22719 := hb (x 3 12)
    have b22720 := hb (x 3 5 && x 3 12)
    clear * - r22718 b22719 b22720 d22701
    omega
  have d22721 : (x 0 3).toNat = 0 := by
    have r22722 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e22723 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e22724 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b22725 := hb (x 0 3)
    have b22726 := hb (x 1 2)
    have b22727 := hb (x 2 13)
    have b22728 := hb (x 3 12)
    clear * - r22722 e22723 e22724 b22725 b22726 b22727 b22728 d22701 d22644 g6
    omega
  have d22729 : (x 0 3 && x 0 13).toNat = 0 := by
    have r22730 := hand1 (x 0 3) (x 0 13)
    have b22731 := hb (x 0 3)
    have b22732 := hb (x 0 3 && x 0 13)
    clear * - r22730 b22731 b22732 d22721
    omega
  have d22733 : (x 0 3 && x 0 12).toNat = 0 := by
    have r22734 := hand1 (x 0 3) (x 0 12)
    have b22735 := hb (x 0 3)
    have b22736 := hb (x 0 3 && x 0 12)
    clear * - r22734 b22735 b22736 d22721
    omega
  have d22737 : (x 0 11).toNat = 0 := by
    have r22738 : (x 0 11).toNat ≤ (x 0 3).toNat := himp _ _ (hp11 0)
    have b22739 := hb (x 0 3)
    have b22740 := hb (x 0 11)
    clear * - r22738 b22739 b22740 d22721
    omega
  have d22741 : (x 0 1 && x 0 11).toNat = 0 := by
    have r22742 := hand2 (x 0 1) (x 0 11)
    have b22743 := hb (x 0 11)
    have b22744 := hb (x 0 1 && x 0 11)
    clear * - r22742 b22743 b22744 d22737
    omega
  have d22745 : (x 0 4 && x 0 11).toNat = 0 := by
    have r22746 := hand2 (x 0 4) (x 0 11)
    have b22747 := hb (x 0 11)
    have b22748 := hb (x 0 4 && x 0 11)
    clear * - r22746 b22747 b22748 d22737
    omega
  have d22749 : (x 2 4 && x 2 13).toNat = 1 := by
    have r22750 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b22751 := hb (x 0 6)
    have b22752 := hb (x 6 9)
    have b22753 := hb (x 5 1 && x 5 10)
    have b22754 := hb (x 4 2 && x 4 11)
    have b22755 := hb (x 3 3 && x 3 12)
    have b22756 := hb (x 2 4 && x 2 13)
    have b22757 := hb (x 1 5 && x 1 14)
    clear * - r22750 b22751 b22752 b22753 b22754 b22755 b22756 b22757 g14 g42 g43 d22713 g44 g4
    omega
  have d22758 : (x 2 4).toNat = 1 := by
    have r22759 := hand1 (x 2 4) (x 2 13)
    have b22760 := hb (x 2 4)
    have b22761 := hb (x 2 4 && x 2 13)
    clear * - r22759 b22760 b22761 d22749
    omega
  have d22762 : (x 2 12).toNat = 1 := by
    have r22763 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
    have b22764 := hb (x 2 4)
    have b22765 := hb (x 2 12)
    clear * - r22763 b22764 b22765 d22758
    omega
  have d22766 : (x 1 13).toNat = 0 := by
    have r22767 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e22768 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e22769 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b22770 := hb (x (-1) 3)
    have b22771 := hb (x 0 2)
    have b22772 := hb (x 1 13)
    have b22773 := hb (x 2 12)
    clear * - r22767 e22768 e22769 b22770 b22771 b22772 b22773 d22762 g3
    omega
  have d22774 : (x 1 7 && x 1 13).toNat = 0 := by
    have r22775 := hand2 (x 1 7) (x 1 13)
    have b22776 := hb (x 1 13)
    have b22777 := hb (x 1 7 && x 1 13)
    clear * - r22775 b22776 b22777 d22766
    omega
  have d22778 : (x 1 5).toNat = 0 := by
    have r22779 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
    have b22780 := hb (x 1 5)
    have b22781 := hb (x 1 13)
    clear * - r22779 b22780 b22781 d22766
    omega
  have d22782 : (x 1 5 && x 1 11).toNat = 0 := by
    have r22783 := hand1 (x 1 5) (x 1 11)
    have b22784 := hb (x 1 5)
    have b22785 := hb (x 1 5 && x 1 11)
    clear * - r22783 b22784 b22785 d22778
    omega
  have d22786 : (x 0 1 && x 0 14).toNat = 1 := by
    have r22787 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b22788 := hb (x (-1) 2)
    have b22789 := hb (x 1 13)
    have b22790 := hb (x 0 1 && x 0 14)
    clear * - r22787 b22788 b22789 b22790 d22766 g1
    omega
  have d22791 : (x 0 14).toNat = 1 := by
    have r22792 := hand2 (x 0 1) (x 0 14)
    have b22793 := hb (x 0 14)
    have b22794 := hb (x 0 1 && x 0 14)
    clear * - r22792 b22793 b22794 d22786
    omega
  have d22795 : (x (-1) 1).toNat = 0 := by
    have r22796 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b22797 := hb (x (-1) 1)
    have b22798 := hb (x 0 14)
    clear * - r22796 b22797 b22798 d22791
    omega
  have d22799 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
    have r22800 := hand1 (x (-1) 1) (x (-1) 12)
    have b22801 := hb (x (-1) 1)
    have b22802 := hb (x (-1) 1 && x (-1) 12)
    clear * - r22800 b22801 b22802 d22795
    omega
  have d22803 : (x (-1) 1 && x (-1) 11).toNat = 0 := by
    have r22804 := hand1 (x (-1) 1) (x (-1) 11)
    have b22805 := hb (x (-1) 1)
    have b22806 := hb (x (-1) 1 && x (-1) 11)
    clear * - r22804 b22805 b22806 d22795
    omega
  have d22807 : (x (-1) 13).toNat = 0 := by
    have r22808 : (x (-1) 13).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp13 (-1))
    have b22809 := hb (x (-1) 1)
    have b22810 := hb (x (-1) 13)
    clear * - r22808 b22809 b22810 d22795
    omega
  have d22811 : (x (-1) 3 && x (-1) 13).toNat = 0 := by
    have r22812 := hand2 (x (-1) 3) (x (-1) 13)
    have b22813 := hb (x (-1) 13)
    have b22814 := hb (x (-1) 3 && x (-1) 13)
    clear * - r22812 b22813 b22814 d22807
    omega
  have d22815 : (x (-1) 4 && x (-1) 13).toNat = 0 := by
    have r22816 := hand2 (x (-1) 4) (x (-1) 13)
    have b22817 := hb (x (-1) 13)
    have b22818 := hb (x (-1) 4 && x (-1) 13)
    clear * - r22816 b22817 b22818 d22807
    omega
  have d22819 : (x (-1) 7 && x (-1) 13).toNat = 0 := by
    have r22820 := hand2 (x (-1) 7) (x (-1) 13)
    have b22821 := hb (x (-1) 13)
    have b22822 := hb (x (-1) 7 && x (-1) 13)
    clear * - r22820 b22821 b22822 d22807
    omega
  have d22823 : (x (-1) 5).toNat = 0 := by
    have r22824 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
    have b22825 := hb (x (-1) 5)
    have b22826 := hb (x (-1) 13)
    clear * - r22824 b22825 b22826 d22807
    omega
  have d22827 : (x (-1) 5 && x (-1) 14).toNat = 0 := by
    have r22828 := hand1 (x (-1) 5) (x (-1) 14)
    have b22829 := hb (x (-1) 5)
    have b22830 := hb (x (-1) 5 && x (-1) 14)
    clear * - r22828 b22829 b22830 d22823
    omega
  have d22831 : (x (-1) 5 && x (-1) 12).toNat = 0 := by
    have r22832 := hand1 (x (-1) 5) (x (-1) 12)
    have b22833 := hb (x (-1) 5)
    have b22834 := hb (x (-1) 5 && x (-1) 12)
    clear * - r22832 b22833 b22834 d22823
    omega
  have d22835 : (x (-1) 9).toNat = 0 := by
    have r22836 : (x (-1) 9).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp9 (-1))
    have b22837 := hb (x (-1) 1)
    have b22838 := hb (x (-1) 9)
    clear * - r22836 b22837 b22838 d22795
    omega
  have d22839 : (x (-1) 3).toNat = 0 := by
    have r22840 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e22841 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e22842 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b22843 := hb (x (-1) 3)
    have b22844 := hb (x 0 2)
    have b22845 := hb (x 1 13)
    have b22846 := hb (x 2 12)
    clear * - r22840 e22841 e22842 b22843 b22844 b22845 b22846 d22762 d22766 g3
    omega
  have d22847 : (x (-1) 3 && x (-1) 14).toNat = 0 := by
    have r22848 := hand1 (x (-1) 3) (x (-1) 14)
    have b22849 := hb (x (-1) 3)
    have b22850 := hb (x (-1) 3 && x (-1) 14)
    clear * - r22848 b22849 b22850 d22839
    omega
  have d22851 : (x (-1) 11).toNat = 0 := by
    have r22852 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
    have b22853 := hb (x (-1) 3)
    have b22854 := hb (x (-1) 11)
    clear * - r22852 b22853 b22854 d22839
    omega
  have d22855 : (x 6 8).toNat = 0 := by
    have r22856 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e22857 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e22858 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e22859 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e22860 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e22861 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e22862 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b22863 := hb (x (-1) 7)
    have b22864 := hb (x 0 6)
    have b22865 := hb (x 1 5)
    have b22866 := hb (x 2 4)
    have b22867 := hb (x 3 11)
    have b22868 := hb (x 4 10)
    have b22869 := hb (x 5 9)
    have b22870 := hb (x 6 8)
    clear * - r22856 e22857 e22858 e22859 e22860 e22861 e22862 b22863 b22864 b22865 b22866 b22867 b22868 b22869 b22870 d22758 d22778 g4
    omega
  have d22871 : (x 6 2 && x 6 8).toNat = 0 := by
    have r22872 := hand2 (x 6 2) (x 6 8)
    have b22873 := hb (x 6 8)
    have b22874 := hb (x 6 2 && x 6 8)
    clear * - r22872 b22873 b22874 d22855
    omega
  have d22875 : (x 5 9).toNat = 0 := by
    have r22876 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e22877 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e22878 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e22879 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e22880 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e22881 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e22882 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b22883 := hb (x (-1) 7)
    have b22884 := hb (x 0 6)
    have b22885 := hb (x 1 5)
    have b22886 := hb (x 2 4)
    have b22887 := hb (x 3 11)
    have b22888 := hb (x 4 10)
    have b22889 := hb (x 5 9)
    have b22890 := hb (x 6 8)
    clear * - r22876 e22877 e22878 e22879 e22880 e22881 e22882 b22883 b22884 b22885 b22886 b22887 b22888 b22889 b22890 d22855 d22758 d22778 g4
    omega
  have d22891 : (x 5 3 && x 5 9).toNat = 0 := by
    have r22892 := hand2 (x 5 3) (x 5 9)
    have b22893 := hb (x 5 9)
    have b22894 := hb (x 5 3 && x 5 9)
    clear * - r22892 b22893 b22894 d22875
    omega
  have d22895 : (x 4 10).toNat = 0 := by
    have r22896 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e22897 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e22898 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e22899 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e22900 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e22901 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e22902 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b22903 := hb (x (-1) 7)
    have b22904 := hb (x 0 6)
    have b22905 := hb (x 1 5)
    have b22906 := hb (x 2 4)
    have b22907 := hb (x 3 11)
    have b22908 := hb (x 4 10)
    have b22909 := hb (x 5 9)
    have b22910 := hb (x 6 8)
    clear * - r22896 e22897 e22898 e22899 e22900 e22901 e22902 b22903 b22904 b22905 b22906 b22907 b22908 b22909 b22910 d22855 d22875 d22758 d22778 g4
    omega
  have d22911 : (x 4 1 && x 4 10).toNat = 0 := by
    have r22912 := hand2 (x 4 1) (x 4 10)
    have b22913 := hb (x 4 10)
    have b22914 := hb (x 4 1 && x 4 10)
    clear * - r22912 b22913 b22914 d22895
    omega
  have d22915 : (x 4 4 && x 4 10).toNat = 0 := by
    have r22916 := hand2 (x 4 4) (x 4 10)
    have b22917 := hb (x 4 10)
    have b22918 := hb (x 4 4 && x 4 10)
    clear * - r22916 b22917 b22918 d22895
    omega
  have d22919 : (x 3 11).toNat = 0 := by
    have r22920 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e22921 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e22922 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e22923 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e22924 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e22925 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e22926 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b22927 := hb (x (-1) 7)
    have b22928 := hb (x 0 6)
    have b22929 := hb (x 1 5)
    have b22930 := hb (x 2 4)
    have b22931 := hb (x 3 11)
    have b22932 := hb (x 4 10)
    have b22933 := hb (x 5 9)
    have b22934 := hb (x 6 8)
    clear * - r22920 e22921 e22922 e22923 e22924 e22925 e22926 b22927 b22928 b22929 b22930 b22931 b22932 b22933 b22934 d22855 d22875 d22895 d22758 d22778 g4
    omega
  have d22935 : (x 3 5 && x 3 11).toNat = 0 := by
    have r22936 := hand2 (x 3 5) (x 3 11)
    have b22937 := hb (x 3 11)
    have b22938 := hb (x 3 5 && x 3 11)
    clear * - r22936 b22937 b22938 d22919
    omega
  have d22939 : (x (-1) 7).toNat = 0 := by
    have r22940 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e22941 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e22942 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e22943 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e22944 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e22945 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e22946 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b22947 := hb (x (-1) 7)
    have b22948 := hb (x 0 6)
    have b22949 := hb (x 1 5)
    have b22950 := hb (x 2 4)
    have b22951 := hb (x 3 11)
    have b22952 := hb (x 4 10)
    have b22953 := hb (x 5 9)
    have b22954 := hb (x 6 8)
    clear * - r22940 e22941 e22942 e22943 e22944 e22945 e22946 b22947 b22948 b22949 b22950 b22951 b22952 b22953 b22954 d22855 d22875 d22895 d22919 d22758 d22778 g4
    omega
  have d22955 : (x (-1) 7 && x (-1) 14).toNat = 0 := by
    have r22956 := hand1 (x (-1) 7) (x (-1) 14)
    have b22957 := hb (x (-1) 7)
    have b22958 := hb (x (-1) 7 && x (-1) 14)
    clear * - r22956 b22957 b22958 d22939
    omega
  cases h22959 : x 0 4
  · have f22960 : (x 0 4).toNat = 0 := by rw [h22959]; rfl
    have d22961 : (x 0 4 && x 0 13).toNat = 0 := by
      have r22962 := hand1 (x 0 4) (x 0 13)
      have b22963 := hb (x 0 4)
      have b22964 := hb (x 0 4 && x 0 13)
      clear * - r22962 b22963 b22964 f22960
      omega
    have d22965 : (x 2 2 && x 2 13).toNat = 1 := by
      have r22966 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b22967 := hb (x 0 4)
      have b22968 := hb (x 4 11)
      have b22969 := hb (x 3 1 && x 3 12)
      have b22970 := hb (x 2 2 && x 2 13)
      have b22971 := hb (x 1 3 && x 1 14)
      clear * - r22966 b22967 b22968 b22969 b22970 b22971 g12 d22709 g56 f22960
      omega
    have d22972 : (x 2 2).toNat = 1 := by
      have r22973 := hand1 (x 2 2) (x 2 13)
      have b22974 := hb (x 2 2)
      have b22975 := hb (x 2 2 && x 2 13)
      clear * - r22973 b22974 b22975 d22965
      omega
    have d22976 : (x 2 14).toNat = 1 := by
      have r22977 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
      have b22978 := hb (x 2 2)
      have b22979 := hb (x 2 14)
      clear * - r22977 b22978 b22979 d22972
      omega
    have d22980 : (x 1 1).toNat = 0 := by
      have r22981 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b22982 := hb (x 1 1)
      have b22983 := hb (x 2 14)
      clear * - r22981 b22982 b22983 d22976
      omega
    have d22984 : (x 1 9).toNat = 0 := by
      have r22985 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
      have b22986 := hb (x 1 1)
      have b22987 := hb (x 1 9)
      clear * - r22985 b22986 b22987 d22980
      omega
    have d22988 : (x 4 12).toNat = 0 := by
      have r22989 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22990 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e22991 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b22992 := hb (x 1 3)
      have b22993 := hb (x 2 2)
      have b22994 := hb (x 3 13)
      have b22995 := hb (x 4 12)
      clear * - r22989 e22990 e22991 b22992 b22993 b22994 b22995 d22972
      omega
    have d22996 : (x 4 3 && x 4 12).toNat = 0 := by
      have r22997 := hand2 (x 4 3) (x 4 12)
      have b22998 := hb (x 4 12)
      have b22999 := hb (x 4 3 && x 4 12)
      clear * - r22997 b22998 b22999 d22988
      omega
    have d23000 : (x 4 4).toNat = 0 := by
      have r23001 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
      have b23002 := hb (x 4 4)
      have b23003 := hb (x 4 12)
      clear * - r23001 b23002 b23003 d22988
      omega
    have d23004 : (x 4 4 && x 4 13).toNat = 0 := by
      have r23005 := hand1 (x 4 4) (x 4 13)
      have b23006 := hb (x 4 4)
      have b23007 := hb (x 4 4 && x 4 13)
      clear * - r23005 b23006 b23007 d23000
      omega
    have d23008 : (x 3 13).toNat = 0 := by
      have r23009 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23010 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e23011 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b23012 := hb (x 1 3)
      have b23013 := hb (x 2 2)
      have b23014 := hb (x 3 13)
      have b23015 := hb (x 4 12)
      clear * - r23009 e23010 e23011 b23012 b23013 b23014 b23015 d22988 d22972
      omega
    have d23016 : (x 3 5).toNat = 0 := by
      have r23017 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
      have b23018 := hb (x 3 5)
      have b23019 := hb (x 3 13)
      clear * - r23017 b23018 b23019 d23008
      omega
    have d23020 : (x 1 3).toNat = 0 := by
      have r23021 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23022 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e23023 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b23024 := hb (x 1 3)
      have b23025 := hb (x 2 2)
      have b23026 := hb (x 3 13)
      have b23027 := hb (x 4 12)
      clear * - r23021 e23022 e23023 b23024 b23025 b23026 b23027 d22988 d23008 d22972
      omega
    have d23028 : (x 1 11).toNat = 0 := by
      have r23029 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
      have b23030 := hb (x 1 3)
      have b23031 := hb (x 1 11)
      clear * - r23029 b23030 b23031 d23020
      omega
    cases h23032 : x 0 8
    · have f23033 : (x 0 8).toNat = 0 := by rw [h23032]; rfl
      have d23034 : (x 0 8 && x 0 14).toNat = 0 := by
        have r23035 := hand1 (x 0 8) (x 0 14)
        have b23036 := hb (x 0 8)
        have b23037 := hb (x 0 8 && x 0 14)
        clear * - r23035 b23036 b23037 f23033
        omega
      cases h23038 : x 0 5
      · have f23039 : (x 0 5).toNat = 0 := by rw [h23038]; rfl
        have d23040 : (x 2 3 && x 2 13).toNat = 1 := by
          have r23041 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23042 := hb (x 0 5)
          have b23043 := hb (x 5 10)
          have b23044 := hb (x 4 1 && x 4 11)
          have b23045 := hb (x 3 2 && x 3 12)
          have b23046 := hb (x 2 3 && x 2 13)
          have b23047 := hb (x 1 4 && x 1 14)
          clear * - r23041 b23042 b23043 b23044 b23045 b23046 b23047 g13 g50 d22681 g51 f23039
          omega
        have d23048 : (x 2 3).toNat = 1 := by
          have r23049 := hand1 (x 2 3) (x 2 13)
          have b23050 := hb (x 2 3)
          have b23051 := hb (x 2 3 && x 2 13)
          clear * - r23049 b23050 b23051 d23040
          omega
        have d23052 : (x 5 12).toNat = 0 := by
          have r23053 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23054 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e23055 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b23056 := hb (x 2 3)
          have b23057 := hb (x 3 2)
          have b23058 := hb (x 4 13)
          have b23059 := hb (x 5 12)
          clear * - r23053 e23054 e23055 b23056 b23057 b23058 b23059 d22677 d23048
          omega
        have d23060 : (x 5 2 && x 5 12).toNat = 0 := by
          have r23061 := hand2 (x 5 2) (x 5 12)
          have b23062 := hb (x 5 12)
          have b23063 := hb (x 5 2 && x 5 12)
          clear * - r23061 b23062 b23063 d23052
          omega
        have d23064 : (x 5 3 && x 5 12).toNat = 0 := by
          have r23065 := hand2 (x 5 3) (x 5 12)
          have b23066 := hb (x 5 12)
          have b23067 := hb (x 5 3 && x 5 12)
          clear * - r23065 b23066 b23067 d23052
          omega
        have d23068 : (x 5 4).toNat = 0 := by
          have r23069 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
          have b23070 := hb (x 5 4)
          have b23071 := hb (x 5 12)
          clear * - r23069 b23070 b23071 d23052
          omega
        have d23072 : (x 5 4 && x 5 8).toNat = 0 := by
          have r23073 := hand1 (x 5 4) (x 5 8)
          have b23074 := hb (x 5 4)
          have b23075 := hb (x 5 4 && x 5 8)
          clear * - r23073 b23074 b23075 d23068
          omega
        have d23076 : (x 4 13).toNat = 0 := by
          have r23077 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23078 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e23079 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b23080 := hb (x 2 3)
          have b23081 := hb (x 3 2)
          have b23082 := hb (x 4 13)
          have b23083 := hb (x 5 12)
          clear * - r23077 e23078 e23079 b23080 b23081 b23082 b23083 d23052 d22677 d23048
          omega
        have d23084 : (x 4 3 && x 4 13).toNat = 0 := by
          have r23085 := hand2 (x 4 3) (x 4 13)
          have b23086 := hb (x 4 13)
          have b23087 := hb (x 4 3 && x 4 13)
          clear * - r23085 b23086 b23087 d23076
          omega
        have d23088 : (x 4 5).toNat = 0 := by
          have r23089 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
          have b23090 := hb (x 4 5)
          have b23091 := hb (x 4 13)
          clear * - r23089 b23090 b23091 d23076
          omega
        have d23092 : (x 4 5 && x 4 9).toNat = 0 := by
          have r23093 := hand1 (x 4 5) (x 4 9)
          have b23094 := hb (x 4 5)
          have b23095 := hb (x 4 5 && x 4 9)
          clear * - r23093 b23094 b23095 d23088
          omega
        cases h23096 : x 0 9
        · have f23097 : (x 0 9).toNat = 0 := by rw [h23096]; rfl
          have d23098 : (x 0 9 && x 0 13).toNat = 0 := by
            have r23099 := hand1 (x 0 9) (x 0 13)
            have b23100 := hb (x 0 9)
            have b23101 := hb (x 0 9 && x 0 13)
            clear * - r23099 b23100 b23101 f23097
            omega
          cases h23102 : x 1 7
          · have f23103 : (x 1 7).toNat = 0 := by rw [h23102]; rfl
            cases h23104 : x (-1) 14
            · have f23105 : (x (-1) 14).toNat = 0 := by rw [h23104]; rfl
              cases h23106 : x 2 6
              · have f23107 : (x 2 6).toNat = 0 := by rw [h23106]; rfl
                have d23108 : (x 2 6 && x 2 13).toNat = 0 := by
                  have r23109 := hand1 (x 2 6) (x 2 13)
                  have b23110 := hb (x 2 6)
                  have b23111 := hb (x 2 6 && x 2 13)
                  clear * - r23109 b23110 b23111 f23107
                  omega
                have d23112 : (x 2 6 && x 2 12).toNat = 0 := by
                  have r23113 := hand1 (x 2 6) (x 2 12)
                  have b23114 := hb (x 2 6)
                  have b23115 := hb (x 2 6 && x 2 12)
                  clear * - r23113 b23114 b23115 f23107
                  omega
                have d23116 : (x 8 7).toNat = 1 := by
                  have r23117 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := by have q := hcov7 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b23118 := hb (x 0 8)
                  have b23119 := hb (x 8 7)
                  have b23120 := hb (x 7 1 && x 7 8)
                  have b23121 := hb (x 6 2 && x 6 9)
                  have b23122 := hb (x 5 3 && x 5 10)
                  have b23123 := hb (x 4 4 && x 4 11)
                  have b23124 := hb (x 3 5 && x 3 12)
                  have b23125 := hb (x 2 6 && x 2 13)
                  have b23126 := hb (x 1 7 && x 1 14)
                  clear * - r23117 b23118 b23119 b23120 b23121 b23122 b23123 b23124 b23125 b23126 g30 g31 g32 g33 d22717 d23108 g34 f23033
                  omega
                have d23127 : (x 15 8).toNat = 0 := by
                  have r23128 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e23129 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                  have e23130 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                  have e23131 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                  have e23132 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                  have e23133 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                  have e23134 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                  have b23135 := hb (x 8 7)
                  have b23136 := hb (x 9 6)
                  have b23137 := hb (x 10 5)
                  have b23138 := hb (x 11 4)
                  have b23139 := hb (x 12 11)
                  have b23140 := hb (x 13 10)
                  have b23141 := hb (x 14 9)
                  have b23142 := hb (x 15 8)
                  clear * - r23128 e23129 e23130 e23131 e23132 e23133 e23134 b23135 b23136 b23137 b23138 b23139 b23140 b23141 b23142 d23116
                  omega
                have d23143 : (x 14 9).toNat = 0 := by
                  have r23144 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e23145 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                  have e23146 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                  have e23147 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                  have e23148 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                  have e23149 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                  have e23150 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                  have b23151 := hb (x 8 7)
                  have b23152 := hb (x 9 6)
                  have b23153 := hb (x 10 5)
                  have b23154 := hb (x 11 4)
                  have b23155 := hb (x 12 11)
                  have b23156 := hb (x 13 10)
                  have b23157 := hb (x 14 9)
                  have b23158 := hb (x 15 8)
                  clear * - r23144 e23145 e23146 e23147 e23148 e23149 e23150 b23151 b23152 b23153 b23154 b23155 b23156 b23157 b23158 d23127 d23116
                  omega
                have d23159 : (x 13 10).toNat = 0 := by
                  have r23160 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e23161 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                  have e23162 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                  have e23163 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                  have e23164 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                  have e23165 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                  have e23166 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                  have b23167 := hb (x 8 7)
                  have b23168 := hb (x 9 6)
                  have b23169 := hb (x 10 5)
                  have b23170 := hb (x 11 4)
                  have b23171 := hb (x 12 11)
                  have b23172 := hb (x 13 10)
                  have b23173 := hb (x 14 9)
                  have b23174 := hb (x 15 8)
                  clear * - r23160 e23161 e23162 e23163 e23164 e23165 e23166 b23167 b23168 b23169 b23170 b23171 b23172 b23173 b23174 d23127 d23143 d23116
                  omega
                have d23175 : (x 13 1 && x 13 10).toNat = 0 := by
                  have r23176 := hand2 (x 13 1) (x 13 10)
                  have b23177 := hb (x 13 10)
                  have b23178 := hb (x 13 1 && x 13 10)
                  clear * - r23176 b23177 b23178 d23159
                  omega
                have d23179 : (x 12 11).toNat = 0 := by
                  have r23180 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e23181 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                  have e23182 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                  have e23183 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                  have e23184 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                  have e23185 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                  have e23186 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                  have b23187 := hb (x 8 7)
                  have b23188 := hb (x 9 6)
                  have b23189 := hb (x 10 5)
                  have b23190 := hb (x 11 4)
                  have b23191 := hb (x 12 11)
                  have b23192 := hb (x 13 10)
                  have b23193 := hb (x 14 9)
                  have b23194 := hb (x 15 8)
                  clear * - r23180 e23181 e23182 e23183 e23184 e23185 e23186 b23187 b23188 b23189 b23190 b23191 b23192 b23193 b23194 d23127 d23143 d23159 d23116
                  omega
                have d23195 : (x 12 2 && x 12 11).toNat = 0 := by
                  have r23196 := hand2 (x 12 2) (x 12 11)
                  have b23197 := hb (x 12 11)
                  have b23198 := hb (x 12 2 && x 12 11)
                  clear * - r23196 b23197 b23198 d23179
                  omega
                have r23199 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r23200 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r23201 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23202 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                have e23203 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                have e23204 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                have e23205 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                have e23206 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                have e23207 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                have r23208 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23209 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                have e23210 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                have e23211 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                have e23212 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                have e23213 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                have e23214 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                have r23215 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23216 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                have e23217 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                have r23218 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r23219 : 1 ≤ (x 9 4).toNat + (x 8 1 && x 8 5).toNat + (x 7 2 && x 7 6).toNat + (x 6 3 && x 6 7).toNat + (x 5 4 && x 5 8).toNat + (x 4 5 && x 4 9).toNat + (x 3 6 && x 3 10).toNat + (x 2 7 && x 2 11).toNat + (x 1 8 && x 1 12).toNat + (x 0 9 && x 0 13).toNat + (x (-1) 10 && x (-1) 14).toNat + (x (-2) 11).toNat := by have q := hcov4 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23220 : (x 8 1 && x 8 5).toNat = (x 8 5).toNat := handr _ _ (fun h => hp13 8 (hp5 8 (h)))
                have e23221 : (x (-1) 10 && x (-1) 14).toNat = (x (-1) 10).toNat := handl _ _ (fun h => hp2 (-1) (hp10 (-1) (h)))
                have r23222 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r23223 : 1 ≤ (x 8 9).toNat + (x 7 1 && x 7 10).toNat + (x 6 2 && x 6 11).toNat + (x 5 3 && x 5 12).toNat + (x 4 4 && x 4 13).toNat + (x 3 5 && x 3 14).toNat + (x 2 6).toNat := by have q := hcov9 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r23224 : 1 ≤ (x 13 9).toNat + (x 12 1 && x 12 10).toNat + (x 11 2 && x 11 11).toNat + (x 10 3 && x 10 12).toNat + (x 9 4 && x 9 13).toNat + (x 8 5 && x 8 14).toNat + (x 7 6).toNat := by have q := hcov9 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r23225 : 1 ≤ (x 14 9).toNat + (x 13 1 && x 13 10).toNat + (x 12 2 && x 12 11).toNat + (x 11 3 && x 11 12).toNat + (x 10 4 && x 10 13).toNat + (x 9 5 && x 9 14).toNat + (x 8 6).toNat := by have q := hcov9 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r23226 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r23227 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r23228 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
                have r23229 : (x 8 5).toNat ≤ (x 8 13).toNat := himp _ _ (hp5 8)
                have r23230 : (x 8 6).toNat ≤ (x 8 14).toNat := himp _ _ (hp6 8)
                have r23231 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
                have r23232 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
                have r23233 := hand1 (x 7 2) (x 7 6)
                have r23234 := hand2 (x 6 3) (x 6 7)
                have r23235 := hand1 (x 2 7) (x 2 11)
                have r23236 := hand2 (x 7 1) (x 7 7)
                have r23237 := hand1 (x 7 1) (x 7 10)
                have r23238 := hand2 (x 6 2) (x 6 11)
                have r23239 := hand2 (x 12 1) (x 12 10)
                have r23240 := hand2 (x 11 2) (x 11 11)
                have r23241 := hand1 (x 10 3) (x 10 12)
                have r23242 := hand1 (x 9 4) (x 9 13)
                have r23243 := hand1 (x 8 5) (x 8 14)
                have r23244 := hand1 (x 11 3) (x 11 12)
                have r23245 := hand1 (x 10 4) (x 10 13)
                have r23246 := hand1 (x 9 5) (x 9 14)
                have r23247 := hand2 (x 6 1) (x 6 11)
                have r23248 := hand1 (x 12 1) (x 12 14)
                linarith only [r23199, r23200, r23201, e23202, e23203, e23204, e23205, e23206, e23207, r23208, e23209, e23210, e23211, e23212, e23213, e23214, r23215, e23216, e23217, r23218, r23219, e23220, e23221, r23222, r23223, r23224, r23225, r23226, r23227, r23228, r23229, r23230, r23231, r23232, r23233, r23234, r23235, r23236, r23237, r23238, r23239, r23240, r23241, r23242, r23243, r23244, r23245, r23246, r23247, r23248, g0, d22835, g2, f23105, g5, d22791, g10, d22766, g11, f23107, d22762, d22661, d22689, d22919, d23088, d22895, d23068, d22875, d22855, d23143, d23072, d23092, d22669, g18, d23098, d22871, d22891, d22915, d22935, d23112, d22774, d23034, d23064, d23004, d22657, d23175, d23195, d23060, d23084, g52]
              · have f23338 : (x 2 6).toNat = 1 := by rw [h23106]; rfl
                have d23339 : (x 8 8).toNat = 0 := by
                  have r23340 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e23341 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                  have e23342 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                  have e23343 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                  have e23344 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                  have e23345 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                  have e23346 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                  have b23347 := hb (x 1 7)
                  have b23348 := hb (x 2 6)
                  have b23349 := hb (x 3 5)
                  have b23350 := hb (x 4 4)
                  have b23351 := hb (x 5 11)
                  have b23352 := hb (x 6 10)
                  have b23353 := hb (x 7 9)
                  have b23354 := hb (x 8 8)
                  clear * - r23340 e23341 e23342 e23343 e23344 e23345 e23346 b23347 b23348 b23349 b23350 b23351 b23352 b23353 b23354 d23000 d23016 f23338 f23103
                  omega
                have d23355 : (x 7 9).toNat = 0 := by
                  have r23356 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e23357 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                  have e23358 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                  have e23359 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                  have e23360 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                  have e23361 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                  have e23362 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                  have b23363 := hb (x 1 7)
                  have b23364 := hb (x 2 6)
                  have b23365 := hb (x 3 5)
                  have b23366 := hb (x 4 4)
                  have b23367 := hb (x 5 11)
                  have b23368 := hb (x 6 10)
                  have b23369 := hb (x 7 9)
                  have b23370 := hb (x 8 8)
                  clear * - r23356 e23357 e23358 e23359 e23360 e23361 e23362 b23363 b23364 b23365 b23366 b23367 b23368 b23369 b23370 d23339 d23000 d23016 f23338 f23103
                  omega
                have d23371 : (x 6 10).toNat = 0 := by
                  have r23372 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e23373 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                  have e23374 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                  have e23375 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                  have e23376 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                  have e23377 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                  have e23378 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                  have b23379 := hb (x 1 7)
                  have b23380 := hb (x 2 6)
                  have b23381 := hb (x 3 5)
                  have b23382 := hb (x 4 4)
                  have b23383 := hb (x 5 11)
                  have b23384 := hb (x 6 10)
                  have b23385 := hb (x 7 9)
                  have b23386 := hb (x 8 8)
                  clear * - r23372 e23373 e23374 e23375 e23376 e23377 e23378 b23379 b23380 b23381 b23382 b23383 b23384 b23385 b23386 d23339 d23355 d23000 d23016 f23338 f23103
                  omega
                have d23387 : (x 6 1 && x 6 10).toNat = 0 := by
                  have r23388 := hand2 (x 6 1) (x 6 10)
                  have b23389 := hb (x 6 10)
                  have b23390 := hb (x 6 1 && x 6 10)
                  clear * - r23388 b23389 b23390 d23371
                  omega
                have d23391 : (x 5 2 && x 5 11).toNat = 1 := by
                  have r23392 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b23393 := hb (x 1 6)
                  have b23394 := hb (x 7 9)
                  have b23395 := hb (x 6 1 && x 6 10)
                  have b23396 := hb (x 5 2 && x 5 11)
                  have b23397 := hb (x 4 3 && x 4 12)
                  have b23398 := hb (x 3 4 && x 3 13)
                  have b23399 := hb (x 2 5 && x 2 14)
                  clear * - r23392 b23393 b23394 b23395 b23396 b23397 b23398 b23399 d23355 d23387 d22996 g45 g46 g8
                  omega
                have d23400 : (x 5 11).toNat = 1 := by
                  have r23401 := hand2 (x 5 2) (x 5 11)
                  have b23402 := hb (x 5 11)
                  have b23403 := hb (x 5 2 && x 5 11)
                  clear * - r23401 b23402 b23403 d23391
                  omega
                have r23404 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23405 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e23406 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e23407 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e23408 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e23409 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e23410 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b23411 := hb (x 1 7)
                have b23412 := hb (x 2 6)
                have b23413 := hb (x 3 5)
                have b23414 := hb (x 4 4)
                have b23415 := hb (x 5 11)
                have b23416 := hb (x 6 10)
                have b23417 := hb (x 7 9)
                have b23418 := hb (x 8 8)
                linarith only [r23404, e23405, e23406, e23407, e23408, e23409, e23410, b23411, b23412, b23413, b23414, b23415, b23416, b23417, b23418, d23339, d23355, d23371, d23400, d23000, d23016, f23338, f23103]
            · have f23419 : (x (-1) 14).toNat = 1 := by rw [h23104]; rfl
              have d23420 : (x (-2) 1).toNat = 0 := by
                have r23421 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23422 := hb (x (-2) 1)
                have b23423 := hb (x (-1) 14)
                clear * - r23421 b23422 b23423 f23419
                omega
              have d23424 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
                have r23425 := hand1 (x (-2) 1) (x (-2) 14)
                have b23426 := hb (x (-2) 1)
                have b23427 := hb (x (-2) 1 && x (-2) 14)
                clear * - r23425 b23426 b23427 d23420
                omega
              have d23428 : (x (-2) 13).toNat = 0 := by
                have r23429 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
                have b23430 := hb (x (-2) 1)
                have b23431 := hb (x (-2) 13)
                clear * - r23429 b23430 b23431 d23420
                omega
              have d23432 : (x (-2) 5).toNat = 0 := by
                have r23433 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
                have b23434 := hb (x (-2) 5)
                have b23435 := hb (x (-2) 13)
                clear * - r23433 b23434 b23435 d23428
                omega
              have d23436 : (x (-3) 2).toNat = 1 := by
                have r23437 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23438 := hb (x (-3) 2)
                have b23439 := hb (x (-1) 13)
                have b23440 := hb (x (-2) 1 && x (-2) 14)
                clear * - r23437 b23438 b23439 b23440 d22807 d23424
                omega
              have d23441 : (x (-1) 12).toNat = 0 := by
                have r23442 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23443 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                have e23444 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                have b23445 := hb (x (-4) 3)
                have b23446 := hb (x (-3) 2)
                have b23447 := hb (x (-2) 13)
                have b23448 := hb (x (-1) 12)
                clear * - r23442 e23443 e23444 b23445 b23446 b23447 b23448 d23428 d23436
                omega
              have d23449 : (x (-1) 4).toNat = 0 := by
                have r23450 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
                have b23451 := hb (x (-1) 4)
                have b23452 := hb (x (-1) 12)
                clear * - r23450 b23451 b23452 d23441
                omega
              have d23453 : (x (-1) 4 && x (-1) 14).toNat = 0 := by
                have r23454 := hand1 (x (-1) 4) (x (-1) 14)
                have b23455 := hb (x (-1) 4)
                have b23456 := hb (x (-1) 4 && x (-1) 14)
                clear * - r23454 b23455 b23456 d23449
                omega
              have d23457 : (x 2 1 && x 2 11).toNat = 1 := by
                have r23458 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23459 := hb (x (-2) 5)
                have b23460 := hb (x 3 10)
                have b23461 := hb (x 2 1 && x 2 11)
                have b23462 := hb (x 1 2 && x 1 12)
                have b23463 := hb (x 0 3 && x 0 13)
                have b23464 := hb (x (-1) 4 && x (-1) 14)
                clear * - r23458 b23459 b23460 b23461 b23462 b23463 b23464 d22689 g49 d22729 d23453 d23432
                omega
              have d23465 : (x 2 11).toNat = 1 := by
                have r23466 := hand2 (x 2 1) (x 2 11)
                have b23467 := hb (x 2 11)
                have b23468 := hb (x 2 1 && x 2 11)
                clear * - r23466 b23467 b23468 d23457
                omega
              have d23469 : (x 5 8).toNat = 0 := by
                have r23470 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23471 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                have e23472 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                have e23473 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                have e23474 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                have e23475 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                have e23476 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                have b23477 := hb (x (-2) 7)
                have b23478 := hb (x (-1) 6)
                have b23479 := hb (x 0 5)
                have b23480 := hb (x 1 4)
                have b23481 := hb (x 2 11)
                have b23482 := hb (x 3 10)
                have b23483 := hb (x 4 9)
                have b23484 := hb (x 5 8)
                clear * - r23470 e23471 e23472 e23473 e23474 e23475 e23476 b23477 b23478 b23479 b23480 b23481 b23482 b23483 b23484 d22689 d23465 g7 f23039
                omega
              have d23485 : (x 4 9).toNat = 0 := by
                have r23486 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23487 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                have e23488 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                have e23489 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                have e23490 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                have e23491 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                have e23492 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                have b23493 := hb (x (-2) 7)
                have b23494 := hb (x (-1) 6)
                have b23495 := hb (x 0 5)
                have b23496 := hb (x 1 4)
                have b23497 := hb (x 2 11)
                have b23498 := hb (x 3 10)
                have b23499 := hb (x 4 9)
                have b23500 := hb (x 5 8)
                clear * - r23486 e23487 e23488 e23489 e23490 e23491 e23492 b23493 b23494 b23495 b23496 b23497 b23498 b23499 b23500 d23469 d22689 d23465 g7 f23039
                omega
              have d23501 : (x 12 1).toNat = 0 := by
                have r23502 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23503 := hb (x (-1) 14)
                have b23504 := hb (x 0 13)
                have b23505 := hb (x 1 12)
                have b23506 := hb (x 2 11)
                have b23507 := hb (x 3 10)
                have b23508 := hb (x 4 9)
                have b23509 := hb (x 5 8)
                have b23510 := hb (x 6 7)
                have b23511 := hb (x 7 6)
                have b23512 := hb (x 8 5)
                have b23513 := hb (x 9 4)
                have b23514 := hb (x 10 3)
                have b23515 := hb (x 11 2)
                have b23516 := hb (x 12 1)
                clear * - r23502 b23503 b23504 b23505 b23506 b23507 b23508 b23509 b23510 b23511 b23512 b23513 b23514 b23515 b23516 d23469 d23485 d22689 d23465 g10 g5 f23419
                omega
              have d23517 : (x 12 1 && x 12 14).toNat = 0 := by
                have r23518 := hand1 (x 12 1) (x 12 14)
                have b23519 := hb (x 12 1)
                have b23520 := hb (x 12 1 && x 12 14)
                clear * - r23518 b23519 b23520 d23501
                omega
              have d23521 : (x 11 2).toNat = 0 := by
                have r23522 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23523 := hb (x (-1) 14)
                have b23524 := hb (x 0 13)
                have b23525 := hb (x 1 12)
                have b23526 := hb (x 2 11)
                have b23527 := hb (x 3 10)
                have b23528 := hb (x 4 9)
                have b23529 := hb (x 5 8)
                have b23530 := hb (x 6 7)
                have b23531 := hb (x 7 6)
                have b23532 := hb (x 8 5)
                have b23533 := hb (x 9 4)
                have b23534 := hb (x 10 3)
                have b23535 := hb (x 11 2)
                have b23536 := hb (x 12 1)
                clear * - r23522 b23523 b23524 b23525 b23526 b23527 b23528 b23529 b23530 b23531 b23532 b23533 b23534 b23535 b23536 d23501 d23469 d23485 d22689 d23465 g10 g5 f23419
                omega
              have d23537 : (x 13 13).toNat = 1 := by
                have r23538 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23539 := hb (x 11 2)
                have b23540 := hb (x 13 13)
                have b23541 := hb (x 12 1 && x 12 14)
                clear * - r23538 b23539 b23540 b23541 d23517 d23521
                omega
              have d23542 : (x 13 1).toNat = 1 := by
                have r23543 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
                have b23544 := hb (x 13 1)
                have b23545 := hb (x 13 13)
                clear * - r23543 b23544 b23545 d23537
                omega
              have d23546 : (x 14 14).toNat = 0 := by
                have r23547 : (x 14 14).toNat + (x 13 1).toNat = 1 := by have q := hd14 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23548 := hb (x 13 1)
                have b23549 := hb (x 14 14)
                clear * - r23547 b23548 b23549 d23542
                omega
              have d23550 : (x 14 1 && x 14 14).toNat = 0 := by
                have r23551 := hand2 (x 14 1) (x 14 14)
                have b23552 := hb (x 14 14)
                have b23553 := hb (x 14 1 && x 14 14)
                clear * - r23551 b23552 b23553 d23546
                omega
              have d23554 : (x 14 2).toNat = 0 := by
                have r23555 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
                have b23556 := hb (x 14 2)
                have b23557 := hb (x 14 14)
                clear * - r23555 b23556 b23557 d23546
                omega
              have d23558 : (x 14 10).toNat = 0 := by
                have r23559 : (x 14 10).toNat ≤ (x 14 2).toNat := himp _ _ (hp10 14)
                have b23560 := hb (x 14 2)
                have b23561 := hb (x 14 10)
                clear * - r23559 b23560 b23561 d23554
                omega
              have d23562 : (x 12 2).toNat = 0 := by
                have r23563 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23564 := hb (x 0 14)
                have b23565 := hb (x 1 13)
                have b23566 := hb (x 2 12)
                have b23567 := hb (x 3 11)
                have b23568 := hb (x 4 10)
                have b23569 := hb (x 5 9)
                have b23570 := hb (x 6 8)
                have b23571 := hb (x 7 7)
                have b23572 := hb (x 8 6)
                have b23573 := hb (x 9 5)
                have b23574 := hb (x 10 4)
                have b23575 := hb (x 11 3)
                have b23576 := hb (x 12 2)
                have b23577 := hb (x 13 1)
                clear * - r23563 b23564 b23565 b23566 b23567 b23568 b23569 b23570 b23571 b23572 b23573 b23574 b23575 b23576 b23577 d23542 d22855 d22875 d22895 d22919 d22762 d22766 d22791
                omega
              have d23578 : (x 12 2 && x 12 12).toNat = 0 := by
                have r23579 := hand1 (x 12 2) (x 12 12)
                have b23580 := hb (x 12 2)
                have b23581 := hb (x 12 2 && x 12 12)
                clear * - r23579 b23580 b23581 d23562
                omega
              have d23582 : (x 12 2 && x 12 11).toNat = 0 := by
                have r23583 := hand1 (x 12 2) (x 12 11)
                have b23584 := hb (x 12 2)
                have b23585 := hb (x 12 2 && x 12 11)
                clear * - r23583 b23584 b23585 d23562
                omega
              have d23586 : (x 12 10).toNat = 0 := by
                have r23587 : (x 12 10).toNat ≤ (x 12 2).toNat := himp _ _ (hp10 12)
                have b23588 := hb (x 12 2)
                have b23589 := hb (x 12 10)
                clear * - r23587 b23588 b23589 d23562
                omega
              have d23590 : (x 11 3).toNat = 0 := by
                have r23591 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23592 := hb (x 0 14)
                have b23593 := hb (x 1 13)
                have b23594 := hb (x 2 12)
                have b23595 := hb (x 3 11)
                have b23596 := hb (x 4 10)
                have b23597 := hb (x 5 9)
                have b23598 := hb (x 6 8)
                have b23599 := hb (x 7 7)
                have b23600 := hb (x 8 6)
                have b23601 := hb (x 9 5)
                have b23602 := hb (x 10 4)
                have b23603 := hb (x 11 3)
                have b23604 := hb (x 12 2)
                have b23605 := hb (x 13 1)
                clear * - r23591 b23592 b23593 b23594 b23595 b23596 b23597 b23598 b23599 b23600 b23601 b23602 b23603 b23604 b23605 d23542 d23562 d22855 d22875 d22895 d22919 d22762 d22766 d22791
                omega
              have d23606 : (x 11 3 && x 11 13).toNat = 0 := by
                have r23607 := hand1 (x 11 3) (x 11 13)
                have b23608 := hb (x 11 3)
                have b23609 := hb (x 11 3 && x 11 13)
                clear * - r23607 b23608 b23609 d23590
                omega
              have d23610 : (x 11 3 && x 11 12).toNat = 0 := by
                have r23611 := hand1 (x 11 3) (x 11 12)
                have b23612 := hb (x 11 3)
                have b23613 := hb (x 11 3 && x 11 12)
                clear * - r23611 b23612 b23613 d23590
                omega
              have d23614 : (x 11 11).toNat = 0 := by
                have r23615 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
                have b23616 := hb (x 11 3)
                have b23617 := hb (x 11 11)
                clear * - r23615 b23616 b23617 d23590
                omega
              have d23618 : (x 11 1 && x 11 11).toNat = 0 := by
                have r23619 := hand2 (x 11 1) (x 11 11)
                have b23620 := hb (x 11 11)
                have b23621 := hb (x 11 1 && x 11 11)
                clear * - r23619 b23620 b23621 d23614
                omega
              have d23622 : (x 10 4).toNat = 0 := by
                have r23623 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23624 := hb (x 0 14)
                have b23625 := hb (x 1 13)
                have b23626 := hb (x 2 12)
                have b23627 := hb (x 3 11)
                have b23628 := hb (x 4 10)
                have b23629 := hb (x 5 9)
                have b23630 := hb (x 6 8)
                have b23631 := hb (x 7 7)
                have b23632 := hb (x 8 6)
                have b23633 := hb (x 9 5)
                have b23634 := hb (x 10 4)
                have b23635 := hb (x 11 3)
                have b23636 := hb (x 12 2)
                have b23637 := hb (x 13 1)
                clear * - r23623 b23624 b23625 b23626 b23627 b23628 b23629 b23630 b23631 b23632 b23633 b23634 b23635 b23636 b23637 d23542 d23562 d23590 d22855 d22875 d22895 d22919 d22762 d22766 d22791
                omega
              have d23638 : (x 10 4 && x 10 14).toNat = 0 := by
                have r23639 := hand1 (x 10 4) (x 10 14)
                have b23640 := hb (x 10 4)
                have b23641 := hb (x 10 4 && x 10 14)
                clear * - r23639 b23640 b23641 d23622
                omega
              have d23642 : (x 10 4 && x 10 13).toNat = 0 := by
                have r23643 := hand1 (x 10 4) (x 10 13)
                have b23644 := hb (x 10 4)
                have b23645 := hb (x 10 4 && x 10 13)
                clear * - r23643 b23644 b23645 d23622
                omega
              have d23646 : (x 9 5).toNat = 0 := by
                have r23647 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23648 := hb (x 0 14)
                have b23649 := hb (x 1 13)
                have b23650 := hb (x 2 12)
                have b23651 := hb (x 3 11)
                have b23652 := hb (x 4 10)
                have b23653 := hb (x 5 9)
                have b23654 := hb (x 6 8)
                have b23655 := hb (x 7 7)
                have b23656 := hb (x 8 6)
                have b23657 := hb (x 9 5)
                have b23658 := hb (x 10 4)
                have b23659 := hb (x 11 3)
                have b23660 := hb (x 12 2)
                have b23661 := hb (x 13 1)
                clear * - r23647 b23648 b23649 b23650 b23651 b23652 b23653 b23654 b23655 b23656 b23657 b23658 b23659 b23660 b23661 d23542 d23562 d23590 d23622 d22855 d22875 d22895 d22919 d22762 d22766 d22791
                omega
              have d23662 : (x 9 5 && x 9 14).toNat = 0 := by
                have r23663 := hand1 (x 9 5) (x 9 14)
                have b23664 := hb (x 9 5)
                have b23665 := hb (x 9 5 && x 9 14)
                clear * - r23663 b23664 b23665 d23646
                omega
              have d23666 : (x 13 1 && x 13 11).toNat = 1 := by
                have r23667 : 1 ≤ (x 14 10).toNat + (x 13 1 && x 13 11).toNat + (x 12 2 && x 12 12).toNat + (x 11 3 && x 11 13).toNat + (x 10 4 && x 10 14).toNat + (x 9 5).toNat := by have q := hcov10 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23668 := hb (x 9 5)
                have b23669 := hb (x 14 10)
                have b23670 := hb (x 13 1 && x 13 11)
                have b23671 := hb (x 12 2 && x 12 12)
                have b23672 := hb (x 11 3 && x 11 13)
                have b23673 := hb (x 10 4 && x 10 14)
                clear * - r23667 b23668 b23669 b23670 b23671 b23672 b23673 d23558 d23578 d23606 d23638 d23646
                omega
              have d23674 : (x 13 11).toNat = 1 := by
                have r23675 := hand2 (x 13 1) (x 13 11)
                have b23676 := hb (x 13 11)
                have b23677 := hb (x 13 1 && x 13 11)
                clear * - r23675 b23676 b23677 d23666
                omega
              have d23678 : (x 13 3).toNat = 1 := by
                have r23679 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
                have b23680 := hb (x 13 3)
                have b23681 := hb (x 13 11)
                clear * - r23679 b23680 b23681 d23674
                omega
              have d23682 : (x 16 12).toNat = 0 := by
                have r23683 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23684 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                have e23685 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                have b23686 := hb (x 13 3)
                have b23687 := hb (x 14 2)
                have b23688 := hb (x 15 13)
                have b23689 := hb (x 16 12)
                clear * - r23683 e23684 e23685 b23686 b23687 b23688 b23689 d23554 d23678
                omega
              have d23690 : (x 15 13).toNat = 0 := by
                have r23691 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23692 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                have e23693 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                have b23694 := hb (x 13 3)
                have b23695 := hb (x 14 2)
                have b23696 := hb (x 15 13)
                have b23697 := hb (x 16 12)
                clear * - r23691 e23692 e23693 b23694 b23695 b23696 b23697 d23682 d23554 d23678
                omega
              have d23698 : (x 13 2).toNat = 1 := by
                have r23699 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23700 := hb (x 13 2)
                have b23701 := hb (x 15 13)
                have b23702 := hb (x 14 1 && x 14 14)
                clear * - r23699 b23700 b23701 b23702 d23690 d23550
                omega
              have d23703 : (x 15 12).toNat = 0 := by
                have r23704 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23705 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
                have e23706 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
                have b23707 := hb (x 12 3)
                have b23708 := hb (x 13 2)
                have b23709 := hb (x 14 13)
                have b23710 := hb (x 15 12)
                clear * - r23704 e23705 e23706 b23707 b23708 b23709 b23710 d23698
                omega
              have d23711 : (x 14 13).toNat = 0 := by
                have r23712 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23713 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
                have e23714 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
                have b23715 := hb (x 12 3)
                have b23716 := hb (x 13 2)
                have b23717 := hb (x 14 13)
                have b23718 := hb (x 15 12)
                clear * - r23712 e23713 e23714 b23715 b23716 b23717 b23718 d23703 d23698
                omega
              have d23719 : (x 12 3).toNat = 0 := by
                have r23720 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23721 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
                have e23722 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
                have b23723 := hb (x 12 3)
                have b23724 := hb (x 13 2)
                have b23725 := hb (x 14 13)
                have b23726 := hb (x 15 12)
                clear * - r23720 e23721 e23722 b23723 b23724 b23725 b23726 d23703 d23711 d23698
                omega
              have d23727 : (x 12 11).toNat = 0 := by
                have r23728 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
                have b23729 := hb (x 12 3)
                have b23730 := hb (x 12 11)
                clear * - r23728 b23729 b23730 d23719
                omega
              have d23731 : (x 8 6).toNat = 0 := by
                have r23732 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23733 := hb (x 0 14)
                have b23734 := hb (x 1 13)
                have b23735 := hb (x 2 12)
                have b23736 := hb (x 3 11)
                have b23737 := hb (x 4 10)
                have b23738 := hb (x 5 9)
                have b23739 := hb (x 6 8)
                have b23740 := hb (x 7 7)
                have b23741 := hb (x 8 6)
                have b23742 := hb (x 9 5)
                have b23743 := hb (x 10 4)
                have b23744 := hb (x 11 3)
                have b23745 := hb (x 12 2)
                have b23746 := hb (x 13 1)
                clear * - r23732 b23733 b23734 b23735 b23736 b23737 b23738 b23739 b23740 b23741 b23742 b23743 b23744 b23745 b23746 d23542 d23562 d23590 d23622 d23646 d22855 d22875 d22895 d22919 d22762 d22766 d22791
                omega
              have d23747 : (x 7 7).toNat = 0 := by
                have r23748 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23749 := hb (x 0 14)
                have b23750 := hb (x 1 13)
                have b23751 := hb (x 2 12)
                have b23752 := hb (x 3 11)
                have b23753 := hb (x 4 10)
                have b23754 := hb (x 5 9)
                have b23755 := hb (x 6 8)
                have b23756 := hb (x 7 7)
                have b23757 := hb (x 8 6)
                have b23758 := hb (x 9 5)
                have b23759 := hb (x 10 4)
                have b23760 := hb (x 11 3)
                have b23761 := hb (x 12 2)
                have b23762 := hb (x 13 1)
                clear * - r23748 b23749 b23750 b23751 b23752 b23753 b23754 b23755 b23756 b23757 b23758 b23759 b23760 b23761 b23762 d23542 d23562 d23590 d23622 d23646 d23731 d22855 d22875 d22895 d22919 d22762 d22766 d22791
                omega
              have d23763 : (x 7 1 && x 7 7).toNat = 0 := by
                have r23764 := hand2 (x 7 1) (x 7 7)
                have b23765 := hb (x 7 7)
                have b23766 := hb (x 7 1 && x 7 7)
                clear * - r23764 b23765 b23766 d23747
                omega
              have d23767 : (x 2 6 && x 2 12).toNat = 1 := by
                have r23768 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23769 := hb (x (-1) 9)
                have b23770 := hb (x 8 6)
                have b23771 := hb (x 7 1 && x 7 7)
                have b23772 := hb (x 6 2 && x 6 8)
                have b23773 := hb (x 5 3 && x 5 9)
                have b23774 := hb (x 4 4 && x 4 10)
                have b23775 := hb (x 3 5 && x 3 11)
                have b23776 := hb (x 2 6 && x 2 12)
                have b23777 := hb (x 1 7 && x 1 13)
                have b23778 := hb (x 0 8 && x 0 14)
                clear * - r23768 b23769 b23770 b23771 b23772 b23773 b23774 b23775 b23776 b23777 b23778 d23731 d23763 d22871 d22891 d22915 d22935 d22774 d23034 d22835
                omega
              have d23779 : (x 2 6).toNat = 1 := by
                have r23780 := hand1 (x 2 6) (x 2 12)
                have b23781 := hb (x 2 6)
                have b23782 := hb (x 2 6 && x 2 12)
                clear * - r23780 b23781 b23782 d23767
                omega
              have d23783 : (x 8 8).toNat = 0 := by
                have r23784 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23785 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e23786 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e23787 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e23788 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e23789 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e23790 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b23791 := hb (x 1 7)
                have b23792 := hb (x 2 6)
                have b23793 := hb (x 3 5)
                have b23794 := hb (x 4 4)
                have b23795 := hb (x 5 11)
                have b23796 := hb (x 6 10)
                have b23797 := hb (x 7 9)
                have b23798 := hb (x 8 8)
                clear * - r23784 e23785 e23786 e23787 e23788 e23789 e23790 b23791 b23792 b23793 b23794 b23795 b23796 b23797 b23798 d23000 d23016 d23779 f23103
                omega
              have d23799 : (x 7 9).toNat = 0 := by
                have r23800 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23801 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e23802 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e23803 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e23804 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e23805 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e23806 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b23807 := hb (x 1 7)
                have b23808 := hb (x 2 6)
                have b23809 := hb (x 3 5)
                have b23810 := hb (x 4 4)
                have b23811 := hb (x 5 11)
                have b23812 := hb (x 6 10)
                have b23813 := hb (x 7 9)
                have b23814 := hb (x 8 8)
                clear * - r23800 e23801 e23802 e23803 e23804 e23805 e23806 b23807 b23808 b23809 b23810 b23811 b23812 b23813 b23814 d23783 d23000 d23016 d23779 f23103
                omega
              have d23815 : (x 6 10).toNat = 0 := by
                have r23816 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23817 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e23818 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e23819 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e23820 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e23821 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e23822 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b23823 := hb (x 1 7)
                have b23824 := hb (x 2 6)
                have b23825 := hb (x 3 5)
                have b23826 := hb (x 4 4)
                have b23827 := hb (x 5 11)
                have b23828 := hb (x 6 10)
                have b23829 := hb (x 7 9)
                have b23830 := hb (x 8 8)
                clear * - r23816 e23817 e23818 e23819 e23820 e23821 e23822 b23823 b23824 b23825 b23826 b23827 b23828 b23829 b23830 d23783 d23799 d23000 d23016 d23779 f23103
                omega
              have d23831 : (x 6 1 && x 6 10).toNat = 0 := by
                have r23832 := hand2 (x 6 1) (x 6 10)
                have b23833 := hb (x 6 10)
                have b23834 := hb (x 6 1 && x 6 10)
                clear * - r23832 b23833 b23834 d23815
                omega
              have d23835 : (x 5 2 && x 5 11).toNat = 1 := by
                have r23836 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23837 := hb (x 1 6)
                have b23838 := hb (x 7 9)
                have b23839 := hb (x 6 1 && x 6 10)
                have b23840 := hb (x 5 2 && x 5 11)
                have b23841 := hb (x 4 3 && x 4 12)
                have b23842 := hb (x 3 4 && x 3 13)
                have b23843 := hb (x 2 5 && x 2 14)
                clear * - r23836 b23837 b23838 b23839 b23840 b23841 b23842 b23843 d23799 d23831 d22996 g45 g46 g8
                omega
              have d23844 : (x 5 11).toNat = 1 := by
                have r23845 := hand2 (x 5 2) (x 5 11)
                have b23846 := hb (x 5 11)
                have b23847 := hb (x 5 2 && x 5 11)
                clear * - r23845 b23846 b23847 d23835
                omega
              have d23848 : (x 5 3).toNat = 1 := by
                have r23849 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
                have b23850 := hb (x 5 3)
                have b23851 := hb (x 5 11)
                clear * - r23849 b23850 b23851 d23844
                omega
              have d23852 : (x 8 12).toNat = 0 := by
                have r23853 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23854 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                have e23855 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                have b23856 := hb (x 5 3)
                have b23857 := hb (x 6 2)
                have b23858 := hb (x 7 13)
                have b23859 := hb (x 8 12)
                clear * - r23853 e23854 e23855 b23856 b23857 b23858 b23859 d23848
                omega
              have d23860 : (x 8 1 && x 8 12).toNat = 0 := by
                have r23861 := hand2 (x 8 1) (x 8 12)
                have b23862 := hb (x 8 12)
                have b23863 := hb (x 8 1 && x 8 12)
                clear * - r23861 b23862 b23863 d23852
                omega
              have d23864 : (x 8 4).toNat = 0 := by
                have r23865 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
                have b23866 := hb (x 8 4)
                have b23867 := hb (x 8 12)
                clear * - r23865 b23866 b23867 d23852
                omega
              have d23868 : (x 8 4 && x 8 14).toNat = 0 := by
                have r23869 := hand1 (x 8 4) (x 8 14)
                have b23870 := hb (x 8 4)
                have b23871 := hb (x 8 4 && x 8 14)
                clear * - r23869 b23870 b23871 d23864
                omega
              have d23872 : (x 7 13).toNat = 0 := by
                have r23873 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23874 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                have e23875 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                have b23876 := hb (x 5 3)
                have b23877 := hb (x 6 2)
                have b23878 := hb (x 7 13)
                have b23879 := hb (x 8 12)
                clear * - r23873 e23874 e23875 b23876 b23877 b23878 b23879 d23852 d23848
                omega
              have d23880 : (x 7 2 && x 7 13).toNat = 0 := by
                have r23881 := hand2 (x 7 2) (x 7 13)
                have b23882 := hb (x 7 13)
                have b23883 := hb (x 7 2 && x 7 13)
                clear * - r23881 b23882 b23883 d23872
                omega
              have d23884 : (x 7 5).toNat = 0 := by
                have r23885 : (x 7 5).toNat ≤ (x 7 13).toNat := himp _ _ (hp5 7)
                have b23886 := hb (x 7 5)
                have b23887 := hb (x 7 13)
                clear * - r23885 b23886 b23887 d23872
                omega
              have d23888 : (x 6 2).toNat = 0 := by
                have r23889 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23890 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                have e23891 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                have b23892 := hb (x 5 3)
                have b23893 := hb (x 6 2)
                have b23894 := hb (x 7 13)
                have b23895 := hb (x 8 12)
                clear * - r23889 e23890 e23891 b23892 b23893 b23894 b23895 d23852 d23872 d23848
                omega
              have d23896 : (x 5 2).toNat = 1 := by
                have r23897 := hand1 (x 5 2) (x 5 11)
                have b23898 := hb (x 5 2)
                have b23899 := hb (x 5 2 && x 5 11)
                clear * - r23897 b23898 b23899 d23835
                omega
              have d23900 : (x 5 14).toNat = 1 := by
                have r23901 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
                have b23902 := hb (x 5 2)
                have b23903 := hb (x 5 14)
                clear * - r23901 b23902 b23903 d23896
                omega
              have d23904 : (x 4 1).toNat = 0 := by
                have r23905 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23906 := hb (x 4 1)
                have b23907 := hb (x 5 14)
                clear * - r23905 b23906 b23907 d23900
                omega
              have d23908 : (x 4 1 && x 4 14).toNat = 0 := by
                have r23909 := hand1 (x 4 1) (x 4 14)
                have b23910 := hb (x 4 1)
                have b23911 := hb (x 4 1 && x 4 14)
                clear * - r23909 b23910 b23911 d23904
                omega
              have d23912 : (x 5 13).toNat = 1 := by
                have r23913 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23914 := hb (x 3 2)
                have b23915 := hb (x 5 13)
                have b23916 := hb (x 4 1 && x 4 14)
                clear * - r23913 b23914 b23915 b23916 d23908 d22677
                omega
              have d23917 : (x 5 1).toNat = 1 := by
                have r23918 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
                have b23919 := hb (x 5 1)
                have b23920 := hb (x 5 13)
                clear * - r23918 b23919 b23920 d23912
                omega
              have d23921 : (x 6 14).toNat = 0 := by
                have r23922 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23923 := hb (x 5 1)
                have b23924 := hb (x 6 14)
                clear * - r23922 b23923 b23924 d23917
                omega
              have d23925 : (x 6 3 && x 6 14).toNat = 0 := by
                have r23926 := hand2 (x 6 3) (x 6 14)
                have b23927 := hb (x 6 14)
                have b23928 := hb (x 6 3 && x 6 14)
                clear * - r23926 b23927 b23928 d23921
                omega
              have d23929 : (x 9 11).toNat = 1 := by
                have r23930 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23931 := hb (x 5 4)
                have b23932 := hb (x 9 11)
                have b23933 := hb (x 8 1 && x 8 12)
                have b23934 := hb (x 7 2 && x 7 13)
                have b23935 := hb (x 6 3 && x 6 14)
                clear * - r23930 b23931 b23932 b23933 b23934 b23935 d23860 d23880 d23925 d23068
                omega
              have d23936 : (x 9 3).toNat = 1 := by
                have r23937 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
                have b23938 := hb (x 9 3)
                have b23939 := hb (x 9 11)
                clear * - r23937 b23938 b23939 d23929
                omega
              have d23940 : (x 12 12).toNat = 0 := by
                have r23941 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23942 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
                have e23943 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
                have b23944 := hb (x 9 3)
                have b23945 := hb (x 10 2)
                have b23946 := hb (x 11 13)
                have b23947 := hb (x 12 12)
                clear * - r23941 e23942 e23943 b23944 b23945 b23946 b23947 d23936
                omega
              have d23948 : (x 11 13).toNat = 0 := by
                have r23949 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23950 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
                have e23951 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
                have b23952 := hb (x 9 3)
                have b23953 := hb (x 10 2)
                have b23954 := hb (x 11 13)
                have b23955 := hb (x 12 12)
                clear * - r23949 e23950 e23951 b23952 b23953 b23954 b23955 d23940 d23936
                omega
              have d23956 : (x 10 2).toNat = 0 := by
                have r23957 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23958 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
                have e23959 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
                have b23960 := hb (x 9 3)
                have b23961 := hb (x 10 2)
                have b23962 := hb (x 11 13)
                have b23963 := hb (x 12 12)
                clear * - r23957 e23958 e23959 b23960 b23961 b23962 b23963 d23940 d23948 d23936
                omega
              have d23964 : (x 10 2 && x 10 12).toNat = 0 := by
                have r23965 := hand1 (x 10 2) (x 10 12)
                have b23966 := hb (x 10 2)
                have b23967 := hb (x 10 2 && x 10 12)
                clear * - r23965 b23966 b23967 d23956
                omega
              have d23968 : (x 9 3 && x 9 13).toNat = 1 := by
                have r23969 : 1 ≤ (x 12 10).toNat + (x 11 1 && x 11 11).toNat + (x 10 2 && x 10 12).toNat + (x 9 3 && x 9 13).toNat + (x 8 4 && x 8 14).toNat + (x 7 5).toNat := by have q := hcov10 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23970 := hb (x 7 5)
                have b23971 := hb (x 12 10)
                have b23972 := hb (x 11 1 && x 11 11)
                have b23973 := hb (x 10 2 && x 10 12)
                have b23974 := hb (x 9 3 && x 9 13)
                have b23975 := hb (x 8 4 && x 8 14)
                clear * - r23969 b23970 b23971 b23972 b23973 b23974 b23975 d23586 d23618 d23964 d23868 d23884
                omega
              have d23976 : (x 9 13).toNat = 1 := by
                have r23977 := hand2 (x 9 3) (x 9 13)
                have b23978 := hb (x 9 13)
                have b23979 := hb (x 9 3 && x 9 13)
                clear * - r23977 b23978 b23979 d23968
                omega
              have d23980 : (x 9 1).toNat = 1 := by
                have r23981 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
                have b23982 := hb (x 9 1)
                have b23983 := hb (x 9 13)
                clear * - r23981 b23982 b23983 d23976
                omega
              have d23984 : (x 10 14).toNat = 0 := by
                have r23985 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23986 := hb (x 9 1)
                have b23987 := hb (x 10 14)
                clear * - r23985 b23986 b23987 d23980
                omega
              have d23988 : (x 10 1 && x 10 14).toNat = 0 := by
                have r23989 := hand2 (x 10 1) (x 10 14)
                have b23990 := hb (x 10 14)
                have b23991 := hb (x 10 1 && x 10 14)
                clear * - r23989 b23990 b23991 d23984
                omega
              have d23992 : (x 9 2).toNat = 1 := by
                have r23993 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23994 := hb (x 9 2)
                have b23995 := hb (x 11 13)
                have b23996 := hb (x 10 1 && x 10 14)
                clear * - r23993 b23994 b23995 b23996 d23948 d23988
                omega
              have d23997 : (x 9 14).toNat = 1 := by
                have r23998 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
                have b23999 := hb (x 9 2)
                have b24000 := hb (x 9 14)
                clear * - r23998 b23999 b24000 d23992
                omega
              have d24001 : (x 8 1).toNat = 0 := by
                have r24002 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24003 := hb (x 8 1)
                have b24004 := hb (x 9 14)
                clear * - r24002 b24003 b24004 d23997
                omega
              have d24005 : (x 8 1 && x 8 7).toNat = 0 := by
                have r24006 := hand1 (x 8 1) (x 8 7)
                have b24007 := hb (x 8 1)
                have b24008 := hb (x 8 1 && x 8 7)
                clear * - r24006 b24007 b24008 d24001
                omega
              have d24009 : (x 8 13).toNat = 0 := by
                have r24010 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
                have b24011 := hb (x 8 1)
                have b24012 := hb (x 8 13)
                clear * - r24010 b24011 b24012 d24001
                omega
              have d24013 : (x 7 1 && x 7 14).toNat = 1 := by
                have r24014 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24015 := hb (x 6 2)
                have b24016 := hb (x 8 13)
                have b24017 := hb (x 7 1 && x 7 14)
                clear * - r24014 b24015 b24016 b24017 d24009 d23888
                omega
              have d24018 : (x 7 14).toNat = 1 := by
                have r24019 := hand2 (x 7 1) (x 7 14)
                have b24020 := hb (x 7 14)
                have b24021 := hb (x 7 1 && x 7 14)
                clear * - r24019 b24020 b24021 d24013
                omega
              have d24022 : (x 6 1).toNat = 0 := by
                have r24023 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24024 := hb (x 6 1)
                have b24025 := hb (x 7 14)
                clear * - r24023 b24024 b24025 d24018
                omega
              have d24026 : (x 6 1 && x 6 11).toNat = 0 := by
                have r24027 := hand1 (x 6 1) (x 6 11)
                have b24028 := hb (x 6 1)
                have b24029 := hb (x 6 1 && x 6 11)
                clear * - r24027 b24028 b24029 d24022
                omega
              have d24030 : (x 7 10).toNat = 1 := by
                have r24031 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24032 := hb (x 2 5)
                have b24033 := hb (x 7 10)
                have b24034 := hb (x 6 1 && x 6 11)
                have b24035 := hb (x 5 2 && x 5 12)
                have b24036 := hb (x 4 3 && x 4 13)
                have b24037 := hb (x 3 4 && x 3 14)
                clear * - r24031 b24032 b24033 b24034 b24035 b24036 b24037 d24026 d23060 d23084 g52 g11
                omega
              have d24038 : (x 9 8).toNat = 0 := by
                have r24039 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24040 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                have e24041 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                have e24042 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                have e24043 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                have e24044 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                have e24045 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                have b24046 := hb (x 2 7)
                have b24047 := hb (x 3 6)
                have b24048 := hb (x 4 5)
                have b24049 := hb (x 5 4)
                have b24050 := hb (x 6 11)
                have b24051 := hb (x 7 10)
                have b24052 := hb (x 8 9)
                have b24053 := hb (x 9 8)
                clear * - r24039 e24040 e24041 e24042 e24043 e24044 e24045 b24046 b24047 b24048 b24049 b24050 b24051 b24052 b24053 d24030 d23068 d23088 d22661
                omega
              have d24054 : (x 8 9).toNat = 0 := by
                have r24055 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24056 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                have e24057 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                have e24058 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                have e24059 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                have e24060 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                have e24061 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                have b24062 := hb (x 2 7)
                have b24063 := hb (x 3 6)
                have b24064 := hb (x 4 5)
                have b24065 := hb (x 5 4)
                have b24066 := hb (x 6 11)
                have b24067 := hb (x 7 10)
                have b24068 := hb (x 8 9)
                have b24069 := hb (x 9 8)
                clear * - r24055 e24056 e24057 e24058 e24059 e24060 e24061 b24062 b24063 b24064 b24065 b24066 b24067 b24068 b24069 d24038 d24030 d23068 d23088 d22661
                omega
              have d24070 : (x 6 11).toNat = 0 := by
                have r24071 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24072 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                have e24073 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                have e24074 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                have e24075 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                have e24076 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                have e24077 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                have b24078 := hb (x 2 7)
                have b24079 := hb (x 3 6)
                have b24080 := hb (x 4 5)
                have b24081 := hb (x 5 4)
                have b24082 := hb (x 6 11)
                have b24083 := hb (x 7 10)
                have b24084 := hb (x 8 9)
                have b24085 := hb (x 9 8)
                clear * - r24071 e24072 e24073 e24074 e24075 e24076 e24077 b24078 b24079 b24080 b24081 b24082 b24083 b24084 b24085 d24038 d24054 d24030 d23068 d23088 d22661
                omega
              have d24086 : (x 2 7).toNat = 0 := by
                have r24087 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24088 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                have e24089 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                have e24090 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                have e24091 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                have e24092 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                have e24093 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                have b24094 := hb (x 2 7)
                have b24095 := hb (x 3 6)
                have b24096 := hb (x 4 5)
                have b24097 := hb (x 5 4)
                have b24098 := hb (x 6 11)
                have b24099 := hb (x 7 10)
                have b24100 := hb (x 8 9)
                have b24101 := hb (x 9 8)
                clear * - r24087 e24088 e24089 e24090 e24091 e24092 e24093 b24094 b24095 b24096 b24097 b24098 b24099 b24100 b24101 d24038 d24054 d24030 d24070 d23068 d23088 d22661
                omega
              have d24102 : (x 2 7 && x 2 13).toNat = 0 := by
                have r24103 := hand1 (x 2 7) (x 2 13)
                have b24104 := hb (x 2 7)
                have b24105 := hb (x 2 7 && x 2 13)
                clear * - r24103 b24104 b24105 d24086
                omega
              have d24106 : (x 9 6).toNat = 1 := by
                have r24107 : 1 ≤ (x 9 6).toNat + (x 8 1 && x 8 7).toNat + (x 7 2 && x 7 8).toNat + (x 6 3 && x 6 9).toNat + (x 5 4 && x 5 10).toNat + (x 4 5 && x 4 11).toNat + (x 3 6 && x 3 12).toNat + (x 2 7 && x 2 13).toNat + (x 1 8 && x 1 14).toNat + (x 0 9).toNat := by have q := hcov6 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24108 := hb (x 0 9)
                have b24109 := hb (x 9 6)
                have b24110 := hb (x 8 1 && x 8 7)
                have b24111 := hb (x 7 2 && x 7 8)
                have b24112 := hb (x 6 3 && x 6 9)
                have b24113 := hb (x 5 4 && x 5 10)
                have b24114 := hb (x 4 5 && x 4 11)
                have b24115 := hb (x 3 6 && x 3 12)
                have b24116 := hb (x 2 7 && x 2 13)
                have b24117 := hb (x 1 8 && x 1 14)
                clear * - r24107 b24108 b24109 b24110 b24111 b24112 b24113 b24114 b24115 b24116 b24117 d24005 g20 g21 g22 g23 d22665 d24102 g24 f23097
                omega
              have d24118 : (x 15 8).toNat = 0 := by
                have r24119 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24120 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                have e24121 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                have e24122 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                have e24123 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                have e24124 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                have e24125 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                have b24126 := hb (x 8 7)
                have b24127 := hb (x 9 6)
                have b24128 := hb (x 10 5)
                have b24129 := hb (x 11 4)
                have b24130 := hb (x 12 11)
                have b24131 := hb (x 13 10)
                have b24132 := hb (x 14 9)
                have b24133 := hb (x 15 8)
                clear * - r24119 e24120 e24121 e24122 e24123 e24124 e24125 b24126 b24127 b24128 b24129 b24130 b24131 b24132 b24133 d23727 d24106
                omega
              have d24134 : (x 14 9).toNat = 0 := by
                have r24135 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24136 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                have e24137 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                have e24138 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                have e24139 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                have e24140 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                have e24141 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                have b24142 := hb (x 8 7)
                have b24143 := hb (x 9 6)
                have b24144 := hb (x 10 5)
                have b24145 := hb (x 11 4)
                have b24146 := hb (x 12 11)
                have b24147 := hb (x 13 10)
                have b24148 := hb (x 14 9)
                have b24149 := hb (x 15 8)
                clear * - r24135 e24136 e24137 e24138 e24139 e24140 e24141 b24142 b24143 b24144 b24145 b24146 b24147 b24148 b24149 d24118 d23727 d24106
                omega
              have d24150 : (x 13 1 && x 13 10).toNat = 1 := by
                have r24151 : 1 ≤ (x 14 9).toNat + (x 13 1 && x 13 10).toNat + (x 12 2 && x 12 11).toNat + (x 11 3 && x 11 12).toNat + (x 10 4 && x 10 13).toNat + (x 9 5 && x 9 14).toNat + (x 8 6).toNat := by have q := hcov9 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24152 := hb (x 8 6)
                have b24153 := hb (x 14 9)
                have b24154 := hb (x 13 1 && x 13 10)
                have b24155 := hb (x 12 2 && x 12 11)
                have b24156 := hb (x 11 3 && x 11 12)
                have b24157 := hb (x 10 4 && x 10 13)
                have b24158 := hb (x 9 5 && x 9 14)
                clear * - r24151 b24152 b24153 b24154 b24155 b24156 b24157 b24158 d24134 d23582 d23610 d23642 d23662 d23731
                omega
              have d24159 : (x 13 10).toNat = 1 := by
                have r24160 := hand2 (x 13 1) (x 13 10)
                have b24161 := hb (x 13 10)
                have b24162 := hb (x 13 1 && x 13 10)
                clear * - r24160 b24161 b24162 d24150
                omega
              have r24163 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e24164 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
              have e24165 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
              have e24166 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
              have e24167 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
              have e24168 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
              have e24169 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
              have b24170 := hb (x 8 7)
              have b24171 := hb (x 9 6)
              have b24172 := hb (x 10 5)
              have b24173 := hb (x 11 4)
              have b24174 := hb (x 12 11)
              have b24175 := hb (x 13 10)
              have b24176 := hb (x 14 9)
              have b24177 := hb (x 15 8)
              linarith only [r24163, e24164, e24165, e24166, e24167, e24168, e24169, b24170, b24171, b24172, b24173, b24174, b24175, b24176, b24177, d24118, d24134, d24159, d23727, d24106]
          · have f24178 : (x 1 7).toNat = 1 := by rw [h23102]; rfl
            have d24179 : (x 8 8).toNat = 0 := by
              have r24180 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e24181 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e24182 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e24183 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e24184 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e24185 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e24186 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b24187 := hb (x 1 7)
              have b24188 := hb (x 2 6)
              have b24189 := hb (x 3 5)
              have b24190 := hb (x 4 4)
              have b24191 := hb (x 5 11)
              have b24192 := hb (x 6 10)
              have b24193 := hb (x 7 9)
              have b24194 := hb (x 8 8)
              clear * - r24180 e24181 e24182 e24183 e24184 e24185 e24186 b24187 b24188 b24189 b24190 b24191 b24192 b24193 b24194 d23000 d23016 f24178
              omega
            have d24195 : (x 7 9).toNat = 0 := by
              have r24196 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e24197 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e24198 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e24199 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e24200 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e24201 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e24202 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b24203 := hb (x 1 7)
              have b24204 := hb (x 2 6)
              have b24205 := hb (x 3 5)
              have b24206 := hb (x 4 4)
              have b24207 := hb (x 5 11)
              have b24208 := hb (x 6 10)
              have b24209 := hb (x 7 9)
              have b24210 := hb (x 8 8)
              clear * - r24196 e24197 e24198 e24199 e24200 e24201 e24202 b24203 b24204 b24205 b24206 b24207 b24208 b24209 b24210 d24179 d23000 d23016 f24178
              omega
            have d24211 : (x 6 10).toNat = 0 := by
              have r24212 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e24213 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e24214 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e24215 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e24216 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e24217 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e24218 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b24219 := hb (x 1 7)
              have b24220 := hb (x 2 6)
              have b24221 := hb (x 3 5)
              have b24222 := hb (x 4 4)
              have b24223 := hb (x 5 11)
              have b24224 := hb (x 6 10)
              have b24225 := hb (x 7 9)
              have b24226 := hb (x 8 8)
              clear * - r24212 e24213 e24214 e24215 e24216 e24217 e24218 b24219 b24220 b24221 b24222 b24223 b24224 b24225 b24226 d24179 d24195 d23000 d23016 f24178
              omega
            have d24227 : (x 6 1 && x 6 10).toNat = 0 := by
              have r24228 := hand2 (x 6 1) (x 6 10)
              have b24229 := hb (x 6 10)
              have b24230 := hb (x 6 1 && x 6 10)
              clear * - r24228 b24229 b24230 d24211
              omega
            have d24231 : (x 5 2 && x 5 11).toNat = 1 := by
              have r24232 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b24233 := hb (x 1 6)
              have b24234 := hb (x 7 9)
              have b24235 := hb (x 6 1 && x 6 10)
              have b24236 := hb (x 5 2 && x 5 11)
              have b24237 := hb (x 4 3 && x 4 12)
              have b24238 := hb (x 3 4 && x 3 13)
              have b24239 := hb (x 2 5 && x 2 14)
              clear * - r24232 b24233 b24234 b24235 b24236 b24237 b24238 b24239 d24195 d24227 d22996 g45 g46 g8
              omega
            have d24240 : (x 5 11).toNat = 1 := by
              have r24241 := hand2 (x 5 2) (x 5 11)
              have b24242 := hb (x 5 11)
              have b24243 := hb (x 5 2 && x 5 11)
              clear * - r24241 b24242 b24243 d24231
              omega
            have r24244 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24245 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e24246 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e24247 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e24248 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e24249 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e24250 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have b24251 := hb (x 1 7)
            have b24252 := hb (x 2 6)
            have b24253 := hb (x 3 5)
            have b24254 := hb (x 4 4)
            have b24255 := hb (x 5 11)
            have b24256 := hb (x 6 10)
            have b24257 := hb (x 7 9)
            have b24258 := hb (x 8 8)
            linarith only [r24244, e24245, e24246, e24247, e24248, e24249, e24250, b24251, b24252, b24253, b24254, b24255, b24256, b24257, b24258, d24179, d24195, d24211, d24240, d23000, d23016, f24178]
        · have f24259 : (x 0 9).toNat = 1 := by rw [h23096]; rfl
          have d24260 : (x 1 8).toNat = 0 := by
            have r24261 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24262 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
            have e24263 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
            have e24264 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
            have e24265 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
            have e24266 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
            have e24267 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
            have b24268 := hb (x (-6) 7)
            have b24269 := hb (x (-5) 6)
            have b24270 := hb (x (-4) 5)
            have b24271 := hb (x (-3) 4)
            have b24272 := hb (x (-2) 11)
            have b24273 := hb (x (-1) 10)
            have b24274 := hb (x 0 9)
            have b24275 := hb (x 1 8)
            clear * - r24261 e24262 e24263 e24264 e24265 e24266 e24267 b24268 b24269 b24270 b24271 b24272 b24273 b24274 b24275 f24259 g2 g0
            omega
          have d24276 : (x (-3) 4).toNat = 0 := by
            have r24277 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24278 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
            have e24279 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
            have e24280 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
            have e24281 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
            have e24282 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
            have e24283 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
            have b24284 := hb (x (-6) 7)
            have b24285 := hb (x (-5) 6)
            have b24286 := hb (x (-4) 5)
            have b24287 := hb (x (-3) 4)
            have b24288 := hb (x (-2) 11)
            have b24289 := hb (x (-1) 10)
            have b24290 := hb (x 0 9)
            have b24291 := hb (x 1 8)
            clear * - r24277 e24278 e24279 e24280 e24281 e24282 e24283 b24284 b24285 b24286 b24287 b24288 b24289 b24290 b24291 d24260 f24259 g2 g0
            omega
          have d24292 : (x (-3) 4 && x (-3) 14).toNat = 0 := by
            have r24293 := hand1 (x (-3) 4) (x (-3) 14)
            have b24294 := hb (x (-3) 4)
            have b24295 := hb (x (-3) 4 && x (-3) 14)
            clear * - r24293 b24294 b24295 d24276
            omega
          have d24296 : (x (-4) 5).toNat = 1 := by
            have r24297 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b24298 := hb (x (-4) 5)
            have b24299 := hb (x 1 10)
            have b24300 := hb (x 0 1 && x 0 11)
            have b24301 := hb (x (-1) 2 && x (-1) 12)
            have b24302 := hb (x (-2) 3 && x (-2) 13)
            have b24303 := hb (x (-3) 4 && x (-3) 14)
            clear * - r24297 b24298 b24299 b24300 b24301 b24302 b24303 g9 d22741 g47 g48 d24292
            omega
          have r24304 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e24305 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e24306 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e24307 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e24308 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e24309 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e24310 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b24311 := hb (x (-6) 7)
          have b24312 := hb (x (-5) 6)
          have b24313 := hb (x (-4) 5)
          have b24314 := hb (x (-3) 4)
          have b24315 := hb (x (-2) 11)
          have b24316 := hb (x (-1) 10)
          have b24317 := hb (x 0 9)
          have b24318 := hb (x 1 8)
          linarith only [r24304, e24305, e24306, e24307, e24308, e24309, e24310, b24311, b24312, b24313, b24314, b24315, b24316, b24317, b24318, d24260, f24259, g2, g0, d24276, d24296]
      · have f24319 : (x 0 5).toNat = 1 := by rw [h23038]; rfl
        have d24320 : (x 5 8).toNat = 0 := by
          have r24321 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e24322 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
          have e24323 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
          have e24324 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
          have e24325 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
          have e24326 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
          have e24327 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
          have b24328 := hb (x (-2) 7)
          have b24329 := hb (x (-1) 6)
          have b24330 := hb (x 0 5)
          have b24331 := hb (x 1 4)
          have b24332 := hb (x 2 11)
          have b24333 := hb (x 3 10)
          have b24334 := hb (x 4 9)
          have b24335 := hb (x 5 8)
          clear * - r24321 e24322 e24323 e24324 e24325 e24326 e24327 b24328 b24329 b24330 b24331 b24332 b24333 b24334 b24335 d22689 g7 f24319
          omega
        have d24336 : (x 4 9).toNat = 0 := by
          have r24337 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e24338 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
          have e24339 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
          have e24340 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
          have e24341 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
          have e24342 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
          have e24343 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
          have b24344 := hb (x (-2) 7)
          have b24345 := hb (x (-1) 6)
          have b24346 := hb (x 0 5)
          have b24347 := hb (x 1 4)
          have b24348 := hb (x 2 11)
          have b24349 := hb (x 3 10)
          have b24350 := hb (x 4 9)
          have b24351 := hb (x 5 8)
          clear * - r24337 e24338 e24339 e24340 e24341 e24342 e24343 b24344 b24345 b24346 b24347 b24348 b24349 b24350 b24351 d24320 d22689 g7 f24319
          omega
        have d24352 : (x 2 11).toNat = 0 := by
          have r24353 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e24354 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
          have e24355 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
          have e24356 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
          have e24357 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
          have e24358 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
          have e24359 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
          have b24360 := hb (x (-2) 7)
          have b24361 := hb (x (-1) 6)
          have b24362 := hb (x 0 5)
          have b24363 := hb (x 1 4)
          have b24364 := hb (x 2 11)
          have b24365 := hb (x 3 10)
          have b24366 := hb (x 4 9)
          have b24367 := hb (x 5 8)
          clear * - r24353 e24354 e24355 e24356 e24357 e24358 e24359 b24360 b24361 b24362 b24363 b24364 b24365 b24366 b24367 d24320 d24336 d22689 g7 f24319
          omega
        have d24368 : (x 2 2 && x 2 11).toNat = 0 := by
          have r24369 := hand2 (x 2 2) (x 2 11)
          have b24370 := hb (x 2 11)
          have b24371 := hb (x 2 2 && x 2 11)
          clear * - r24369 b24370 b24371 d24352
          omega
        have d24372 : (x (-2) 6).toNat = 1 := by
          have r24373 : 1 ≤ (x 4 9).toNat + (x 3 1 && x 3 10).toNat + (x 2 2 && x 2 11).toNat + (x 1 3 && x 1 12).toNat + (x 0 4 && x 0 13).toNat + (x (-1) 5 && x (-1) 14).toNat + (x (-2) 6).toNat := by have q := hcov9 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b24374 := hb (x (-2) 6)
          have b24375 := hb (x 4 9)
          have b24376 := hb (x 3 1 && x 3 10)
          have b24377 := hb (x 2 2 && x 2 11)
          have b24378 := hb (x 1 3 && x 1 12)
          have b24379 := hb (x 0 4 && x 0 13)
          have b24380 := hb (x (-1) 5 && x (-1) 14)
          clear * - r24373 b24374 b24375 b24376 b24377 b24378 b24379 b24380 d24336 d22693 d24368 g40 d22961 d22827
          omega
        have d24381 : (x (-2) 14).toNat = 1 := by
          have r24382 : (x (-2) 6).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp6 (-2))
          have b24383 := hb (x (-2) 6)
          have b24384 := hb (x (-2) 14)
          clear * - r24382 b24383 b24384 d24372
          omega
        have d24385 : (x (-3) 1).toNat = 0 := by
          have r24386 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b24387 := hb (x (-3) 1)
          have b24388 := hb (x (-2) 14)
          clear * - r24386 b24387 b24388 d24381
          omega
        have d24389 : (x (-3) 1 && x (-3) 12).toNat = 0 := by
          have r24390 := hand1 (x (-3) 1) (x (-3) 12)
          have b24391 := hb (x (-3) 1)
          have b24392 := hb (x (-3) 1 && x (-3) 12)
          clear * - r24390 b24391 b24392 d24385
          omega
        have d24393 : (x (-3) 13).toNat = 0 := by
          have r24394 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
          have b24395 := hb (x (-3) 1)
          have b24396 := hb (x (-3) 13)
          clear * - r24394 b24395 b24396 d24385
          omega
        have d24397 : (x (-3) 4 && x (-3) 13).toNat = 0 := by
          have r24398 := hand2 (x (-3) 4) (x (-3) 13)
          have b24399 := hb (x (-3) 13)
          have b24400 := hb (x (-3) 4 && x (-3) 13)
          clear * - r24398 b24399 b24400 d24393
          omega
        have d24401 : (x (-3) 9).toNat = 0 := by
          have r24402 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
          have b24403 := hb (x (-3) 1)
          have b24404 := hb (x (-3) 9)
          clear * - r24402 b24403 b24404 d24385
          omega
        have d24405 : (x (-2) 4).toNat = 1 := by
          have r24406 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := by have q := hcov11 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b24407 := hb (x (-2) 4)
          have b24408 := hb (x 2 11)
          have b24409 := hb (x 1 1 && x 1 12)
          have b24410 := hb (x 0 2 && x 0 13)
          have b24411 := hb (x (-1) 3 && x (-1) 14)
          clear * - r24406 b24407 b24408 b24409 b24410 b24411 d24352 g55 d22624 d22847
          omega
        have d24412 : (x (-2) 12).toNat = 1 := by
          have r24413 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
          have b24414 := hb (x (-2) 4)
          have b24415 := hb (x (-2) 12)
          clear * - r24413 b24414 b24415 d24405
          omega
        have d24416 : (x (-4) 2).toNat = 0 := by
          have r24417 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e24418 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
          have e24419 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
          have b24420 := hb (x (-5) 3)
          have b24421 := hb (x (-4) 2)
          have b24422 := hb (x (-3) 13)
          have b24423 := hb (x (-2) 12)
          clear * - r24417 e24418 e24419 b24420 b24421 b24422 b24423 d24412 d24393
          omega
        have d24424 : (x (-4) 2 && x (-4) 13).toNat = 0 := by
          have r24425 := hand1 (x (-4) 2) (x (-4) 13)
          have b24426 := hb (x (-4) 2)
          have b24427 := hb (x (-4) 2 && x (-4) 13)
          clear * - r24425 b24426 b24427 d24416
          omega
        have d24428 : (x (-4) 10).toNat = 0 := by
          have r24429 : (x (-4) 10).toNat ≤ (x (-4) 2).toNat := himp _ _ (hp10 (-4))
          have b24430 := hb (x (-4) 2)
          have b24431 := hb (x (-4) 10)
          clear * - r24429 b24430 b24431 d24416
          omega
        have d24432 : (x (-5) 3).toNat = 0 := by
          have r24433 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e24434 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
          have e24435 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
          have b24436 := hb (x (-5) 3)
          have b24437 := hb (x (-4) 2)
          have b24438 := hb (x (-3) 13)
          have b24439 := hb (x (-2) 12)
          clear * - r24433 e24434 e24435 b24436 b24437 b24438 b24439 d24412 d24393 d24416
          omega
        have d24440 : (x (-5) 3 && x (-5) 14).toNat = 0 := by
          have r24441 := hand1 (x (-5) 3) (x (-5) 14)
          have b24442 := hb (x (-5) 3)
          have b24443 := hb (x (-5) 3 && x (-5) 14)
          clear * - r24441 b24442 b24443 d24432
          omega
        have d24444 : (x (-6) 4).toNat = 1 := by
          have r24445 : 1 ≤ (x (-2) 11).toNat + (x (-3) 1 && x (-3) 12).toNat + (x (-4) 2 && x (-4) 13).toNat + (x (-5) 3 && x (-5) 14).toNat + (x (-6) 4).toNat := by have q := hcov11 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b24446 := hb (x (-6) 4)
          have b24447 := hb (x (-2) 11)
          have b24448 := hb (x (-3) 1 && x (-3) 12)
          have b24449 := hb (x (-4) 2 && x (-4) 13)
          have b24450 := hb (x (-5) 3 && x (-5) 14)
          clear * - r24445 b24446 b24447 b24448 b24449 b24450 g0 d24389 d24424 d24440
          omega
        have d24451 : (x (-6) 12).toNat = 1 := by
          have r24452 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
          have b24453 := hb (x (-6) 4)
          have b24454 := hb (x (-6) 12)
          clear * - r24452 b24453 b24454 d24444
          omega
        have d24455 : (x (-7) 13).toNat = 0 := by
          have r24456 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e24457 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
          have e24458 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
          have b24459 := hb (x (-9) 3)
          have b24460 := hb (x (-8) 2)
          have b24461 := hb (x (-7) 13)
          have b24462 := hb (x (-6) 12)
          clear * - r24456 e24457 e24458 b24459 b24460 b24461 b24462 d24451
          omega
        have d24463 : (x (-7) 5).toNat = 0 := by
          have r24464 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
          have b24465 := hb (x (-7) 5)
          have b24466 := hb (x (-7) 13)
          clear * - r24464 b24465 b24466 d24455
          omega
        have d24467 : (x (-5) 11).toNat = 0 := by
          have r24468 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
          have b24469 := hb (x (-5) 3)
          have b24470 := hb (x (-5) 11)
          clear * - r24468 b24469 b24470 d24432
          omega
        have d24471 : (x 4 8).toNat = 0 := by
          have r24472 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e24473 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
          have e24474 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
          have e24475 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
          have e24476 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
          have e24477 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
          have e24478 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
          have b24479 := hb (x (-3) 7)
          have b24480 := hb (x (-2) 6)
          have b24481 := hb (x (-1) 5)
          have b24482 := hb (x 0 4)
          have b24483 := hb (x 1 11)
          have b24484 := hb (x 2 10)
          have b24485 := hb (x 3 9)
          have b24486 := hb (x 4 8)
          clear * - r24472 e24473 e24474 e24475 e24476 e24477 e24478 b24479 b24480 b24481 b24482 b24483 b24484 b24485 b24486 d23028 f22960 d22823 d24372
          omega
        have d24487 : (x 4 2 && x 4 8).toNat = 0 := by
          have r24488 := hand2 (x 4 2) (x 4 8)
          have b24489 := hb (x 4 8)
          have b24490 := hb (x 4 2 && x 4 8)
          clear * - r24488 b24489 b24490 d24471
          omega
        have d24491 : (x 3 9).toNat = 0 := by
          have r24492 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e24493 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
          have e24494 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
          have e24495 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
          have e24496 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
          have e24497 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
          have e24498 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
          have b24499 := hb (x (-3) 7)
          have b24500 := hb (x (-2) 6)
          have b24501 := hb (x (-1) 5)
          have b24502 := hb (x 0 4)
          have b24503 := hb (x 1 11)
          have b24504 := hb (x 2 10)
          have b24505 := hb (x 3 9)
          have b24506 := hb (x 4 8)
          clear * - r24492 e24493 e24494 e24495 e24496 e24497 e24498 b24499 b24500 b24501 b24502 b24503 b24504 b24505 b24506 d24471 d23028 f22960 d22823 d24372
          omega
        have d24507 : (x 3 3 && x 3 9).toNat = 0 := by
          have r24508 := hand2 (x 3 3) (x 3 9)
          have b24509 := hb (x 3 9)
          have b24510 := hb (x 3 3 && x 3 9)
          clear * - r24508 b24509 b24510 d24491
          omega
        have d24511 : (x 2 10).toNat = 0 := by
          have r24512 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e24513 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
          have e24514 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
          have e24515 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
          have e24516 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
          have e24517 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
          have e24518 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
          have b24519 := hb (x (-3) 7)
          have b24520 := hb (x (-2) 6)
          have b24521 := hb (x (-1) 5)
          have b24522 := hb (x 0 4)
          have b24523 := hb (x 1 11)
          have b24524 := hb (x 2 10)
          have b24525 := hb (x 3 9)
          have b24526 := hb (x 4 8)
          clear * - r24512 e24513 e24514 e24515 e24516 e24517 e24518 b24519 b24520 b24521 b24522 b24523 b24524 b24525 b24526 d24471 d24491 d23028 f22960 d22823 d24372
          omega
        have d24527 : (x 2 4 && x 2 10).toNat = 0 := by
          have r24528 := hand2 (x 2 4) (x 2 10)
          have b24529 := hb (x 2 10)
          have b24530 := hb (x 2 4 && x 2 10)
          clear * - r24528 b24529 b24530 d24511
          omega
        have d24531 : (x (-2) 8).toNat = 0 := by
          have r24532 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e24533 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
          have e24534 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
          have e24535 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
          have e24536 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
          have e24537 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
          have e24538 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
          have b24539 := hb (x (-9) 7)
          have b24540 := hb (x (-8) 6)
          have b24541 := hb (x (-7) 5)
          have b24542 := hb (x (-6) 4)
          have b24543 := hb (x (-5) 11)
          have b24544 := hb (x (-4) 10)
          have b24545 := hb (x (-3) 9)
          have b24546 := hb (x (-2) 8)
          clear * - r24532 e24533 e24534 e24535 e24536 e24537 e24538 b24539 b24540 b24541 b24542 b24543 b24544 b24545 b24546 d24401 d24428 d24467 d24444 d24463
          omega
        have d24547 : (x (-2) 8 && x (-2) 14).toNat = 0 := by
          have r24548 := hand1 (x (-2) 8) (x (-2) 14)
          have b24549 := hb (x (-2) 8)
          have b24550 := hb (x (-2) 8 && x (-2) 14)
          clear * - r24548 b24549 b24550 d24531
          omega
        have r24551 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r24552 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e24553 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
        have e24554 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
        have e24555 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
        have e24556 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
        have e24557 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
        have e24558 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
        have r24559 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e24560 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e24561 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e24562 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e24563 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e24564 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e24565 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have r24566 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e24567 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
        have e24568 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
        have e24569 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
        have e24570 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
        have e24571 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
        have e24572 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
        have r24573 : 1 ≤ (x 6 6).toNat + (x 5 1 && x 5 7).toNat + (x 4 2 && x 4 8).toNat + (x 3 3 && x 3 9).toNat + (x 2 4 && x 2 10).toNat + (x 1 5 && x 1 11).toNat + (x 0 6 && x 0 12).toNat + (x (-1) 7 && x (-1) 13).toNat + (x (-2) 8 && x (-2) 14).toNat + (x (-3) 9).toNat := by have q := hcov6 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r24574 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := by have q := hcov7 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r24575 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r24576 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r24577 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r24578 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r24579 := hand2 (x 5 1) (x 5 7)
        have r24580 := hand1 (x 2 6) (x 2 13)
        have r24581 := hand1 (x (-4) 5) (x (-4) 14)
        have r24582 := hand2 (x 6 1) (x 6 10)
        have r24583 := hand2 (x 5 2) (x 5 11)
        have r24584 := hand2 (x 0 1) (x 0 12)
        have r24585 := hand1 (x 11 1) (x 11 12)
        have r24586 := hand1 (x 10 2) (x 10 13)
        have r24587 := hand1 (x 9 3) (x 9 14)
        linarith only [r24551, r24552, e24553, e24554, e24555, e24556, e24557, e24558, r24559, e24560, e24561, e24562, e24563, e24564, e24565, r24566, e24567, e24568, e24569, e24570, e24571, e24572, r24573, r24574, r24575, r24576, r24577, r24578, r24579, r24580, r24581, r24582, r24583, r24584, r24585, r24586, r24587, d24401, g0, d24381, g2, d22807, f23033, g8, d22984, d23028, d24511, d23016, d24491, d23000, d24471, d24487, d24507, d24527, d22782, g19, d22819, d24547, g30, g31, g32, g33, d22717, g34, d22640, g37, g38, d24397, d22996, g45, g46, g53, g54]
    · have f24661 : (x 0 8).toNat = 1 := by rw [h23032]; rfl
      have d24662 : (x (-2) 10).toNat = 0 := by
        have r24663 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e24664 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
        have e24665 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
        have e24666 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
        have e24667 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
        have e24668 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
        have e24669 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
        have b24670 := hb (x (-7) 7)
        have b24671 := hb (x (-6) 6)
        have b24672 := hb (x (-5) 5)
        have b24673 := hb (x (-4) 4)
        have b24674 := hb (x (-3) 11)
        have b24675 := hb (x (-2) 10)
        have b24676 := hb (x (-1) 9)
        have b24677 := hb (x 0 8)
        clear * - r24663 e24664 e24665 e24666 e24667 e24668 e24669 b24670 b24671 b24672 b24673 b24674 b24675 b24676 b24677 f24661 d22835
        omega
      have d24678 : (x (-3) 11).toNat = 0 := by
        have r24679 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e24680 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
        have e24681 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
        have e24682 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
        have e24683 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
        have e24684 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
        have e24685 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
        have b24686 := hb (x (-7) 7)
        have b24687 := hb (x (-6) 6)
        have b24688 := hb (x (-5) 5)
        have b24689 := hb (x (-4) 4)
        have b24690 := hb (x (-3) 11)
        have b24691 := hb (x (-2) 10)
        have b24692 := hb (x (-1) 9)
        have b24693 := hb (x 0 8)
        clear * - r24679 e24680 e24681 e24682 e24683 e24684 e24685 b24686 b24687 b24688 b24689 b24690 b24691 b24692 b24693 f24661 d22835 d24662
        omega
      have d24694 : (x (-4) 4).toNat = 0 := by
        have r24695 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e24696 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
        have e24697 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
        have e24698 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
        have e24699 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
        have e24700 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
        have e24701 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
        have b24702 := hb (x (-7) 7)
        have b24703 := hb (x (-6) 6)
        have b24704 := hb (x (-5) 5)
        have b24705 := hb (x (-4) 4)
        have b24706 := hb (x (-3) 11)
        have b24707 := hb (x (-2) 10)
        have b24708 := hb (x (-1) 9)
        have b24709 := hb (x 0 8)
        clear * - r24695 e24696 e24697 e24698 e24699 e24700 e24701 b24702 b24703 b24704 b24705 b24706 b24707 b24708 b24709 f24661 d22835 d24662 d24678
        omega
      have d24710 : (x (-4) 4 && x (-4) 13).toNat = 0 := by
        have r24711 := hand1 (x (-4) 4) (x (-4) 13)
        have b24712 := hb (x (-4) 4)
        have b24713 := hb (x (-4) 4 && x (-4) 13)
        clear * - r24711 b24712 b24713 d24694
        omega
      have d24714 : (x (-5) 5).toNat = 0 := by
        have r24715 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e24716 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
        have e24717 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
        have e24718 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
        have e24719 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
        have e24720 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
        have e24721 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
        have b24722 := hb (x (-7) 7)
        have b24723 := hb (x (-6) 6)
        have b24724 := hb (x (-5) 5)
        have b24725 := hb (x (-4) 4)
        have b24726 := hb (x (-3) 11)
        have b24727 := hb (x (-2) 10)
        have b24728 := hb (x (-1) 9)
        have b24729 := hb (x 0 8)
        clear * - r24715 e24716 e24717 e24718 e24719 e24720 e24721 b24722 b24723 b24724 b24725 b24726 b24727 b24728 b24729 f24661 d22835 d24662 d24678 d24694
        omega
      have d24730 : (x (-5) 5 && x (-5) 14).toNat = 0 := by
        have r24731 := hand1 (x (-5) 5) (x (-5) 14)
        have b24732 := hb (x (-5) 5)
        have b24733 := hb (x (-5) 5 && x (-5) 14)
        clear * - r24731 b24732 b24733 d24714
        omega
      have d24734 : (x (-6) 6).toNat = 0 := by
        have r24735 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e24736 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
        have e24737 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
        have e24738 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
        have e24739 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
        have e24740 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
        have e24741 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
        have b24742 := hb (x (-7) 7)
        have b24743 := hb (x (-6) 6)
        have b24744 := hb (x (-5) 5)
        have b24745 := hb (x (-4) 4)
        have b24746 := hb (x (-3) 11)
        have b24747 := hb (x (-2) 10)
        have b24748 := hb (x (-1) 9)
        have b24749 := hb (x 0 8)
        clear * - r24735 e24736 e24737 e24738 e24739 e24740 e24741 b24742 b24743 b24744 b24745 b24746 b24747 b24748 b24749 f24661 d22835 d24662 d24678 d24694 d24714
        omega
      have r24750 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24751 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
      have e24752 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
      have e24753 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
      have e24754 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
      have e24755 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
      have e24756 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
      have r24757 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24758 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e24759 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e24760 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e24761 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e24762 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e24763 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have r24764 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24765 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
      have e24766 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
      have e24767 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
      have e24768 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
      have e24769 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
      have e24770 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
      have r24771 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24772 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e24773 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have r24774 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24775 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e24776 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have r24777 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24778 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e24779 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have r24780 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r24781 : 1 ≤ (x 5 4).toNat + (x 4 1 && x 4 5).toNat + (x 3 2 && x 3 6).toNat + (x 2 3 && x 2 7).toNat + (x 1 4 && x 1 8).toNat + (x 0 5 && x 0 9).toNat + (x (-1) 6 && x (-1) 10).toNat + (x (-2) 7 && x (-2) 11).toNat + (x (-3) 8 && x (-3) 12).toNat + (x (-4) 9 && x (-4) 13).toNat + (x (-5) 10 && x (-5) 14).toNat + (x (-6) 11).toNat := by have q := hcov4 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24782 : (x 4 1 && x 4 5).toNat = (x 4 5).toNat := handr _ _ (fun h => hp13 4 (hp5 4 (h)))
      have e24783 : (x (-5) 10 && x (-5) 14).toNat = (x (-5) 10).toNat := handl _ _ (fun h => hp2 (-5) (hp10 (-5) (h)))
      have r24784 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r24785 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r24786 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r24787 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r24788 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := by have q := hcov11 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r24789 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := by have q := hcov11 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r24790 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
      have r24791 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
      have r24792 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
      have r24793 := hand2 (x 2 3) (x 2 7)
      have r24794 := hand2 (x 0 5) (x 0 9)
      have r24795 := hand1 (x (-3) 8) (x (-3) 12)
      have r24796 := hand1 (x (-4) 9) (x (-4) 13)
      have r24797 := hand2 (x (-3) 3) (x (-3) 12)
      have r24798 := hand2 (x (-3) 4) (x (-3) 13)
      have r24799 := hand1 (x (-4) 5) (x (-4) 14)
      have r24800 := hand1 (x (-3) 4) (x (-3) 14)
      have r24801 := hand2 (x (-3) 4) (x (-3) 14)
      have r24802 := hand2 (x 6 1) (x 6 11)
      have r24803 := hand2 (x 5 2) (x 5 12)
      have r24804 := hand2 (x 4 3) (x 4 13)
      have r24805 := hand1 (x (-4) 1) (x (-4) 12)
      have r24806 := hand1 (x (-5) 2) (x (-5) 13)
      have r24807 := hand1 (x (-6) 3) (x (-6) 14)
      linarith only [r24750, e24751, e24752, e24753, e24754, e24755, e24756, r24757, e24758, e24759, e24760, e24761, e24762, e24763, r24764, e24765, e24766, e24767, e24768, e24769, e24770, r24771, e24772, e24773, r24774, e24775, e24776, r24777, e24778, e24779, r24780, r24781, e24782, e24783, r24784, r24785, r24786, r24787, r24788, r24789, r24790, r24791, r24792, r24793, r24794, r24795, r24796, r24797, r24798, r24799, r24800, r24801, r24802, r24803, r24804, r24805, r24806, r24807, d24734, d24678, g0, g2, d22984, g9, g11, d22677, d22661, d22673, g15, g16, g17, g35, g36, d24710, d24730, d22640, g37, g38, d22741, g47, g48, g52, g55, d22624, d22847]
  · have f24885 : (x 0 4).toNat = 1 := by rw [h22959]; rfl
    have d24886 : (x 0 12).toNat = 1 := by
      have r24887 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
      have b24888 := hb (x 0 4)
      have b24889 := hb (x 0 12)
      clear * - r24887 b24888 b24889 f24885
      omega
    have d24890 : (x (-2) 2).toNat = 0 := by
      have r24891 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24892 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e24893 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have b24894 := hb (x (-3) 3)
      have b24895 := hb (x (-2) 2)
      have b24896 := hb (x (-1) 13)
      have b24897 := hb (x 0 12)
      clear * - r24891 e24892 e24893 b24894 b24895 b24896 b24897 d24886 d22807
      omega
    have d24898 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
      have r24899 := hand1 (x (-2) 2) (x (-2) 13)
      have b24900 := hb (x (-2) 2)
      have b24901 := hb (x (-2) 2 && x (-2) 13)
      clear * - r24899 b24900 b24901 d24890
      omega
    have d24902 : (x (-2) 2 && x (-2) 12).toNat = 0 := by
      have r24903 := hand1 (x (-2) 2) (x (-2) 12)
      have b24904 := hb (x (-2) 2)
      have b24905 := hb (x (-2) 2 && x (-2) 12)
      clear * - r24903 b24904 b24905 d24890
      omega
    have d24906 : (x (-2) 10).toNat = 0 := by
      have r24907 : (x (-2) 10).toNat ≤ (x (-2) 2).toNat := himp _ _ (hp10 (-2))
      have b24908 := hb (x (-2) 2)
      have b24909 := hb (x (-2) 10)
      clear * - r24907 b24908 b24909 d24890
      omega
    have d24910 : (x (-2) 1 && x (-2) 10).toNat = 0 := by
      have r24911 := hand2 (x (-2) 1) (x (-2) 10)
      have b24912 := hb (x (-2) 10)
      have b24913 := hb (x (-2) 1 && x (-2) 10)
      clear * - r24911 b24912 b24913 d24906
      omega
    have d24914 : (x (-3) 3).toNat = 0 := by
      have r24915 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24916 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e24917 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have b24918 := hb (x (-3) 3)
      have b24919 := hb (x (-2) 2)
      have b24920 := hb (x (-1) 13)
      have b24921 := hb (x 0 12)
      clear * - r24915 e24916 e24917 b24918 b24919 b24920 b24921 d24886 d22807 d24890
      omega
    have d24922 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
      have r24923 := hand1 (x (-3) 3) (x (-3) 14)
      have b24924 := hb (x (-3) 3)
      have b24925 := hb (x (-3) 3 && x (-3) 14)
      clear * - r24923 b24924 b24925 d24914
      omega
    have d24926 : (x (-3) 3 && x (-3) 13).toNat = 0 := by
      have r24927 := hand1 (x (-3) 3) (x (-3) 13)
      have b24928 := hb (x (-3) 3)
      have b24929 := hb (x (-3) 3 && x (-3) 13)
      clear * - r24927 b24928 b24929 d24914
      omega
    have d24930 : (x (-3) 11).toNat = 0 := by
      have r24931 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
      have b24932 := hb (x (-3) 3)
      have b24933 := hb (x (-3) 11)
      clear * - r24931 b24932 b24933 d24914
      omega
    have d24934 : (x (-3) 1 && x (-3) 11).toNat = 0 := by
      have r24935 := hand2 (x (-3) 1) (x (-3) 11)
      have b24936 := hb (x (-3) 11)
      have b24937 := hb (x (-3) 1 && x (-3) 11)
      clear * - r24935 b24936 b24937 d24930
      omega
    have d24938 : (x (-3) 2 && x (-3) 11).toNat = 0 := by
      have r24939 := hand2 (x (-3) 2) (x (-3) 11)
      have b24940 := hb (x (-3) 11)
      have b24941 := hb (x (-3) 2 && x (-3) 11)
      clear * - r24939 b24940 b24941 d24930
      omega
    have d24942 : (x (-4) 4).toNat = 1 := by
      have r24943 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24944 := hb (x (-4) 4)
      have b24945 := hb (x 0 11)
      have b24946 := hb (x (-1) 1 && x (-1) 12)
      have b24947 := hb (x (-2) 2 && x (-2) 13)
      have b24948 := hb (x (-3) 3 && x (-3) 14)
      clear * - r24943 b24944 b24945 b24946 b24947 b24948 d22737 d22799 d24898 d24922
      omega
    have d24949 : (x (-4) 12).toNat = 1 := by
      have r24950 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
      have b24951 := hb (x (-4) 4)
      have b24952 := hb (x (-4) 12)
      clear * - r24950 b24951 b24952 d24942
      omega
    have d24953 : (x (-5) 13).toNat = 0 := by
      have r24954 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24955 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e24956 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have b24957 := hb (x (-7) 3)
      have b24958 := hb (x (-6) 2)
      have b24959 := hb (x (-5) 13)
      have b24960 := hb (x (-4) 12)
      clear * - r24954 e24955 e24956 b24957 b24958 b24959 b24960 d24949
      omega
    have d24961 : (x (-5) 3 && x (-5) 13).toNat = 0 := by
      have r24962 := hand2 (x (-5) 3) (x (-5) 13)
      have b24963 := hb (x (-5) 13)
      have b24964 := hb (x (-5) 3 && x (-5) 13)
      clear * - r24962 b24963 b24964 d24953
      omega
    have d24965 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
      have r24966 := hand2 (x (-5) 4) (x (-5) 13)
      have b24967 := hb (x (-5) 13)
      have b24968 := hb (x (-5) 4 && x (-5) 13)
      clear * - r24966 b24967 b24968 d24953
      omega
    have d24969 : (x (-5) 5).toNat = 0 := by
      have r24970 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
      have b24971 := hb (x (-5) 5)
      have b24972 := hb (x (-5) 13)
      clear * - r24970 b24971 b24972 d24953
      omega
    have d24973 : (x (-6) 2).toNat = 0 := by
      have r24974 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24975 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e24976 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have b24977 := hb (x (-7) 3)
      have b24978 := hb (x (-6) 2)
      have b24979 := hb (x (-5) 13)
      have b24980 := hb (x (-4) 12)
      clear * - r24974 e24975 e24976 b24977 b24978 b24979 b24980 d24949 d24953
      omega
    have d24981 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
      have r24982 := hand1 (x (-6) 2) (x (-6) 13)
      have b24983 := hb (x (-6) 2)
      have b24984 := hb (x (-6) 2 && x (-6) 13)
      clear * - r24982 b24983 b24984 d24973
      omega
    have d24985 : (x (-6) 2 && x (-6) 12).toNat = 0 := by
      have r24986 := hand1 (x (-6) 2) (x (-6) 12)
      have b24987 := hb (x (-6) 2)
      have b24988 := hb (x (-6) 2 && x (-6) 12)
      clear * - r24986 b24987 b24988 d24973
      omega
    have d24989 : (x (-6) 10).toNat = 0 := by
      have r24990 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
      have b24991 := hb (x (-6) 2)
      have b24992 := hb (x (-6) 10)
      clear * - r24990 b24991 b24992 d24973
      omega
    have d24993 : (x (-7) 3).toNat = 0 := by
      have r24994 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24995 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e24996 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have b24997 := hb (x (-7) 3)
      have b24998 := hb (x (-6) 2)
      have b24999 := hb (x (-5) 13)
      have b25000 := hb (x (-4) 12)
      clear * - r24994 e24995 e24996 b24997 b24998 b24999 b25000 d24949 d24953 d24973
      omega
    have d25001 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
      have r25002 := hand1 (x (-7) 3) (x (-7) 14)
      have b25003 := hb (x (-7) 3)
      have b25004 := hb (x (-7) 3 && x (-7) 14)
      clear * - r25002 b25003 b25004 d24993
      omega
    have d25005 : (x (-7) 3 && x (-7) 13).toNat = 0 := by
      have r25006 := hand1 (x (-7) 3) (x (-7) 13)
      have b25007 := hb (x (-7) 3)
      have b25008 := hb (x (-7) 3 && x (-7) 13)
      clear * - r25006 b25007 b25008 d24993
      omega
    have d25009 : (x (-7) 11).toNat = 0 := by
      have r25010 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
      have b25011 := hb (x (-7) 3)
      have b25012 := hb (x (-7) 11)
      clear * - r25010 b25011 b25012 d24993
      omega
    have d25013 : (x (-7) 1 && x (-7) 11).toNat = 0 := by
      have r25014 := hand2 (x (-7) 1) (x (-7) 11)
      have b25015 := hb (x (-7) 11)
      have b25016 := hb (x (-7) 1 && x (-7) 11)
      clear * - r25014 b25015 b25016 d25009
      omega
    have d25017 : (x (-4) 4 && x (-4) 14).toNat = 1 := by
      have r25018 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25019 := hb (x (-5) 5)
      have b25020 := hb (x 0 10)
      have b25021 := hb (x (-1) 1 && x (-1) 11)
      have b25022 := hb (x (-2) 2 && x (-2) 12)
      have b25023 := hb (x (-3) 3 && x (-3) 13)
      have b25024 := hb (x (-4) 4 && x (-4) 14)
      clear * - r25018 b25019 b25020 b25021 b25022 b25023 b25024 d22636 d22803 d24902 d24926 d24969
      omega
    have d25025 : (x (-4) 14).toNat = 1 := by
      have r25026 := hand2 (x (-4) 4) (x (-4) 14)
      have b25027 := hb (x (-4) 14)
      have b25028 := hb (x (-4) 4 && x (-4) 14)
      clear * - r25026 b25027 b25028 d25017
      omega
    have d25029 : (x (-5) 1).toNat = 0 := by
      have r25030 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25031 := hb (x (-5) 1)
      have b25032 := hb (x (-4) 14)
      clear * - r25030 b25031 b25032 d25025
      omega
    have d25033 : (x (-5) 1 && x (-5) 14).toNat = 0 := by
      have r25034 := hand1 (x (-5) 1) (x (-5) 14)
      have b25035 := hb (x (-5) 1)
      have b25036 := hb (x (-5) 1 && x (-5) 14)
      clear * - r25034 b25035 b25036 d25029
      omega
    have d25037 : (x (-4) 13).toNat = 1 := by
      have r25038 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25039 := hb (x (-6) 2)
      have b25040 := hb (x (-4) 13)
      have b25041 := hb (x (-5) 1 && x (-5) 14)
      clear * - r25038 b25039 b25040 b25041 d25033 d24973
      omega
    have d25042 : (x (-4) 1).toNat = 1 := by
      have r25043 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
      have b25044 := hb (x (-4) 1)
      have b25045 := hb (x (-4) 13)
      clear * - r25043 b25044 b25045 d25037
      omega
    have d25046 : (x (-3) 14).toNat = 0 := by
      have r25047 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25048 := hb (x (-4) 1)
      have b25049 := hb (x (-3) 14)
      clear * - r25047 b25048 b25049 d25042
      omega
    have d25050 : (x (-3) 4 && x (-3) 14).toNat = 0 := by
      have r25051 := hand2 (x (-3) 4) (x (-3) 14)
      have b25052 := hb (x (-3) 14)
      have b25053 := hb (x (-3) 4 && x (-3) 14)
      clear * - r25051 b25052 b25053 d25046
      omega
    have d25054 : (x (-4) 5).toNat = 1 := by
      have r25055 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25056 := hb (x (-4) 5)
      have b25057 := hb (x 1 10)
      have b25058 := hb (x 0 1 && x 0 11)
      have b25059 := hb (x (-1) 2 && x (-1) 12)
      have b25060 := hb (x (-2) 3 && x (-2) 13)
      have b25061 := hb (x (-3) 4 && x (-3) 14)
      clear * - r25055 b25056 b25057 b25058 b25059 b25060 b25061 g9 d22741 g47 g48 d25050
      omega
    have d25062 : (x (-3) 7 && x (-3) 14).toNat = 0 := by
      have r25063 := hand2 (x (-3) 7) (x (-3) 14)
      have b25064 := hb (x (-3) 14)
      have b25065 := hb (x (-3) 7 && x (-3) 14)
      clear * - r25063 b25064 b25065 d25046
      omega
    have d25066 : (x (-3) 6).toNat = 0 := by
      have r25067 : (x (-3) 6).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp6 (-3))
      have b25068 := hb (x (-3) 6)
      have b25069 := hb (x (-3) 14)
      clear * - r25067 b25068 b25069 d25046
      omega
    have d25070 : (x (-3) 2).toNat = 0 := by
      have r25071 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
      have b25072 := hb (x (-3) 2)
      have b25073 := hb (x (-3) 14)
      clear * - r25071 b25072 b25073 d25046
      omega
    have d25074 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
      have r25075 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25076 := hb (x (-3) 2)
      have b25077 := hb (x (-1) 13)
      have b25078 := hb (x (-2) 1 && x (-2) 14)
      clear * - r25075 b25076 b25077 b25078 d22807 d25070
      omega
    have d25079 : (x (-2) 14).toNat = 1 := by
      have r25080 := hand2 (x (-2) 1) (x (-2) 14)
      have b25081 := hb (x (-2) 14)
      have b25082 := hb (x (-2) 1 && x (-2) 14)
      clear * - r25080 b25081 b25082 d25074
      omega
    have d25083 : (x (-3) 1).toNat = 0 := by
      have r25084 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25085 := hb (x (-3) 1)
      have b25086 := hb (x (-2) 14)
      clear * - r25084 b25085 b25086 d25079
      omega
    have d25087 : (x (-3) 1 && x (-3) 8).toNat = 0 := by
      have r25088 := hand1 (x (-3) 1) (x (-3) 8)
      have b25089 := hb (x (-3) 1)
      have b25090 := hb (x (-3) 1 && x (-3) 8)
      clear * - r25088 b25089 b25090 d25083
      omega
    have d25091 : (x (-3) 13).toNat = 0 := by
      have r25092 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
      have b25093 := hb (x (-3) 1)
      have b25094 := hb (x (-3) 13)
      clear * - r25092 b25093 b25094 d25083
      omega
    have d25095 : (x (-3) 5).toNat = 0 := by
      have r25096 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
      have b25097 := hb (x (-3) 5)
      have b25098 := hb (x (-3) 13)
      clear * - r25096 b25097 b25098 d25091
      omega
    have d25099 : (x (-3) 5 && x (-3) 12).toNat = 0 := by
      have r25100 := hand1 (x (-3) 5) (x (-3) 12)
      have b25101 := hb (x (-3) 5)
      have b25102 := hb (x (-3) 5 && x (-3) 12)
      clear * - r25100 b25101 b25102 d25095
      omega
    have d25103 : (x (-3) 9).toNat = 0 := by
      have r25104 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
      have b25105 := hb (x (-3) 1)
      have b25106 := hb (x (-3) 9)
      clear * - r25104 b25105 b25106 d25083
      omega
    have d25107 : (x (-2) 1).toNat = 1 := by
      have r25108 := hand1 (x (-2) 1) (x (-2) 14)
      have b25109 := hb (x (-2) 1)
      have b25110 := hb (x (-2) 1 && x (-2) 14)
      clear * - r25108 b25109 b25110 d25074
      omega
    have d25111 : (x (-1) 14).toNat = 0 := by
      have r25112 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25113 := hb (x (-2) 1)
      have b25114 := hb (x (-1) 14)
      clear * - r25112 b25113 b25114 d25107
      omega
    have d25115 : (x (-1) 6).toNat = 0 := by
      have r25116 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
      have b25117 := hb (x (-1) 6)
      have b25118 := hb (x (-1) 14)
      clear * - r25116 b25117 b25118 d25111
      omega
    have d25119 : (x (-3) 12).toNat = 0 := by
      have r25120 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25121 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e25122 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b25123 := hb (x (-6) 3)
      have b25124 := hb (x (-5) 2)
      have b25125 := hb (x (-4) 13)
      have b25126 := hb (x (-3) 12)
      clear * - r25120 e25121 e25122 b25123 b25124 b25125 b25126 d25037
      omega
    have d25127 : (x (-3) 4).toNat = 0 := by
      have r25128 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
      have b25129 := hb (x (-3) 4)
      have b25130 := hb (x (-3) 12)
      clear * - r25128 b25129 b25130 d25119
      omega
    have d25131 : (x (-5) 2).toNat = 0 := by
      have r25132 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25133 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e25134 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b25135 := hb (x (-6) 3)
      have b25136 := hb (x (-5) 2)
      have b25137 := hb (x (-4) 13)
      have b25138 := hb (x (-3) 12)
      clear * - r25132 e25133 e25134 b25135 b25136 b25137 b25138 d25119 d25037
      omega
    have d25139 : (x (-5) 10).toNat = 0 := by
      have r25140 : (x (-5) 10).toNat ≤ (x (-5) 2).toNat := himp _ _ (hp10 (-5))
      have b25141 := hb (x (-5) 2)
      have b25142 := hb (x (-5) 10)
      clear * - r25140 b25141 b25142 d25131
      omega
    have d25143 : (x (-5) 3 && x (-5) 10).toNat = 0 := by
      have r25144 := hand2 (x (-5) 3) (x (-5) 10)
      have b25145 := hb (x (-5) 10)
      have b25146 := hb (x (-5) 3 && x (-5) 10)
      clear * - r25144 b25145 b25146 d25139
      omega
    have d25147 : (x (-6) 3).toNat = 0 := by
      have r25148 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25149 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e25150 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b25151 := hb (x (-6) 3)
      have b25152 := hb (x (-5) 2)
      have b25153 := hb (x (-4) 13)
      have b25154 := hb (x (-3) 12)
      clear * - r25148 e25149 e25150 b25151 b25152 b25153 b25154 d25119 d25037 d25131
      omega
    have d25155 : (x (-6) 11).toNat = 0 := by
      have r25156 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
      have b25157 := hb (x (-6) 3)
      have b25158 := hb (x (-6) 11)
      clear * - r25156 b25157 b25158 d25147
      omega
    have d25159 : (x (-6) 4 && x (-6) 11).toNat = 0 := by
      have r25160 := hand2 (x (-6) 4) (x (-6) 11)
      have b25161 := hb (x (-6) 11)
      have b25162 := hb (x (-6) 4 && x (-6) 11)
      clear * - r25160 b25161 b25162 d25155
      omega
    have d25163 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
      have r25164 := hand1 (x (-5) 1) (x (-5) 12)
      have b25165 := hb (x (-5) 1)
      have b25166 := hb (x (-5) 1 && x (-5) 12)
      clear * - r25164 b25165 b25166 d25029
      omega
    have d25167 : (x (-5) 1 && x (-5) 11).toNat = 0 := by
      have r25168 := hand1 (x (-5) 1) (x (-5) 11)
      have b25169 := hb (x (-5) 1)
      have b25170 := hb (x (-5) 1 && x (-5) 11)
      clear * - r25168 b25169 b25170 d25029
      omega
    have d25171 : (x (-5) 9).toNat = 0 := by
      have r25172 : (x (-5) 9).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp9 (-5))
      have b25173 := hb (x (-5) 1)
      have b25174 := hb (x (-5) 9)
      clear * - r25172 b25173 b25174 d25029
      omega
    have d25175 : (x 4 8).toNat = 0 := by
      have r25176 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25177 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
      have e25178 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
      have e25179 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
      have e25180 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
      have e25181 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
      have e25182 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
      have b25183 := hb (x (-3) 7)
      have b25184 := hb (x (-2) 6)
      have b25185 := hb (x (-1) 5)
      have b25186 := hb (x 0 4)
      have b25187 := hb (x 1 11)
      have b25188 := hb (x 2 10)
      have b25189 := hb (x 3 9)
      have b25190 := hb (x 4 8)
      clear * - r25176 e25177 e25178 e25179 e25180 e25181 e25182 b25183 b25184 b25185 b25186 b25187 b25188 b25189 b25190 f24885 d22823
      omega
    have d25191 : (x 3 9).toNat = 0 := by
      have r25192 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25193 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
      have e25194 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
      have e25195 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
      have e25196 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
      have e25197 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
      have e25198 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
      have b25199 := hb (x (-3) 7)
      have b25200 := hb (x (-2) 6)
      have b25201 := hb (x (-1) 5)
      have b25202 := hb (x 0 4)
      have b25203 := hb (x 1 11)
      have b25204 := hb (x 2 10)
      have b25205 := hb (x 3 9)
      have b25206 := hb (x 4 8)
      clear * - r25192 e25193 e25194 e25195 e25196 e25197 e25198 b25199 b25200 b25201 b25202 b25203 b25204 b25205 b25206 d25175 f24885 d22823
      omega
    have d25207 : (x 2 10).toNat = 0 := by
      have r25208 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25209 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
      have e25210 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
      have e25211 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
      have e25212 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
      have e25213 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
      have e25214 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
      have b25215 := hb (x (-3) 7)
      have b25216 := hb (x (-2) 6)
      have b25217 := hb (x (-1) 5)
      have b25218 := hb (x 0 4)
      have b25219 := hb (x 1 11)
      have b25220 := hb (x 2 10)
      have b25221 := hb (x 3 9)
      have b25222 := hb (x 4 8)
      clear * - r25208 e25209 e25210 e25211 e25212 e25213 e25214 b25215 b25216 b25217 b25218 b25219 b25220 b25221 b25222 d25175 d25191 f24885 d22823
      omega
    have d25223 : (x 2 1 && x 2 10).toNat = 0 := by
      have r25224 := hand2 (x 2 1) (x 2 10)
      have b25225 := hb (x 2 10)
      have b25226 := hb (x 2 1 && x 2 10)
      clear * - r25224 b25225 b25226 d25207
      omega
    have d25227 : (x (-2) 5 && x (-2) 14).toNat = 1 := by
      have r25228 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25229 := hb (x (-3) 6)
      have b25230 := hb (x 3 9)
      have b25231 := hb (x 2 1 && x 2 10)
      have b25232 := hb (x 1 2 && x 1 11)
      have b25233 := hb (x 0 3 && x 0 12)
      have b25234 := hb (x (-1) 4 && x (-1) 13)
      have b25235 := hb (x (-2) 5 && x (-2) 14)
      clear * - r25228 b25229 b25230 b25231 b25232 b25233 b25234 b25235 d25191 d25223 g39 d22733 d22815 d25066
      omega
    have d25236 : (x (-2) 5).toNat = 1 := by
      have r25237 := hand1 (x (-2) 5) (x (-2) 14)
      have b25238 := hb (x (-2) 5)
      have b25239 := hb (x (-2) 5 && x (-2) 14)
      clear * - r25237 b25238 b25239 d25227
      omega
    have d25240 : (x (-2) 13).toNat = 1 := by
      have r25241 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
      have b25242 := hb (x (-2) 5)
      have b25243 := hb (x (-2) 13)
      clear * - r25241 b25242 b25243 d25236
      omega
    have d25244 : (x (-1) 12).toNat = 0 := by
      have r25245 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25246 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e25247 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b25248 := hb (x (-4) 3)
      have b25249 := hb (x (-3) 2)
      have b25250 := hb (x (-2) 13)
      have b25251 := hb (x (-1) 12)
      clear * - r25245 e25246 e25247 b25248 b25249 b25250 b25251 d25240 d25070
      omega
    have d25252 : (x (-1) 4).toNat = 0 := by
      have r25253 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
      have b25254 := hb (x (-1) 4)
      have b25255 := hb (x (-1) 12)
      clear * - r25253 b25254 b25255 d25244
      omega
    have d25256 : (x (-4) 3).toNat = 0 := by
      have r25257 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25258 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e25259 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b25260 := hb (x (-4) 3)
      have b25261 := hb (x (-3) 2)
      have b25262 := hb (x (-2) 13)
      have b25263 := hb (x (-1) 12)
      clear * - r25257 e25258 e25259 b25260 b25261 b25262 b25263 d25244 d25240 d25070
      omega
    have d25264 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
      have r25265 := hand1 (x (-4) 3) (x (-4) 12)
      have b25266 := hb (x (-4) 3)
      have b25267 := hb (x (-4) 3 && x (-4) 12)
      clear * - r25265 b25266 b25267 d25256
      omega
    have d25268 : (x (-4) 11).toNat = 0 := by
      have r25269 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
      have b25270 := hb (x (-4) 3)
      have b25271 := hb (x (-4) 11)
      clear * - r25269 b25270 b25271 d25256
      omega
    have d25272 : (x (-8) 4).toNat = 1 := by
      have r25273 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25274 := hb (x (-8) 4)
      have b25275 := hb (x (-4) 11)
      have b25276 := hb (x (-5) 1 && x (-5) 12)
      have b25277 := hb (x (-6) 2 && x (-6) 13)
      have b25278 := hb (x (-7) 3 && x (-7) 14)
      clear * - r25273 b25274 b25275 b25276 b25277 b25278 d25268 d25163 d24981 d25001
      omega
    have d25279 : (x (-8) 12).toNat = 1 := by
      have r25280 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
      have b25281 := hb (x (-8) 4)
      have b25282 := hb (x (-8) 12)
      clear * - r25280 b25281 b25282 d25272
      omega
    have d25283 : (x (-9) 13).toNat = 0 := by
      have r25284 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25285 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
      have e25286 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
      have b25287 := hb (x (-11) 3)
      have b25288 := hb (x (-10) 2)
      have b25289 := hb (x (-9) 13)
      have b25290 := hb (x (-8) 12)
      clear * - r25284 e25285 e25286 b25287 b25288 b25289 b25290 d25279
      omega
    have d25291 : (x (-9) 3 && x (-9) 13).toNat = 0 := by
      have r25292 := hand2 (x (-9) 3) (x (-9) 13)
      have b25293 := hb (x (-9) 13)
      have b25294 := hb (x (-9) 3 && x (-9) 13)
      clear * - r25292 b25293 b25294 d25283
      omega
    have d25295 : (x (-9) 5).toNat = 0 := by
      have r25296 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
      have b25297 := hb (x (-9) 5)
      have b25298 := hb (x (-9) 13)
      clear * - r25296 b25297 b25298 d25283
      omega
    have d25299 : (x (-10) 2).toNat = 0 := by
      have r25300 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25301 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
      have e25302 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
      have b25303 := hb (x (-11) 3)
      have b25304 := hb (x (-10) 2)
      have b25305 := hb (x (-9) 13)
      have b25306 := hb (x (-8) 12)
      clear * - r25300 e25301 e25302 b25303 b25304 b25305 b25306 d25279 d25283
      omega
    have d25307 : (x (-10) 2 && x (-10) 13).toNat = 0 := by
      have r25308 := hand1 (x (-10) 2) (x (-10) 13)
      have b25309 := hb (x (-10) 2)
      have b25310 := hb (x (-10) 2 && x (-10) 13)
      clear * - r25308 b25309 b25310 d25299
      omega
    have d25311 : (x (-10) 2 && x (-10) 12).toNat = 0 := by
      have r25312 := hand1 (x (-10) 2) (x (-10) 12)
      have b25313 := hb (x (-10) 2)
      have b25314 := hb (x (-10) 2 && x (-10) 12)
      clear * - r25312 b25313 b25314 d25299
      omega
    have d25315 : (x (-10) 10).toNat = 0 := by
      have r25316 : (x (-10) 10).toNat ≤ (x (-10) 2).toNat := himp _ _ (hp10 (-10))
      have b25317 := hb (x (-10) 2)
      have b25318 := hb (x (-10) 10)
      clear * - r25316 b25317 b25318 d25299
      omega
    have d25319 : (x (-11) 3).toNat = 0 := by
      have r25320 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25321 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
      have e25322 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
      have b25323 := hb (x (-11) 3)
      have b25324 := hb (x (-10) 2)
      have b25325 := hb (x (-9) 13)
      have b25326 := hb (x (-8) 12)
      clear * - r25320 e25321 e25322 b25323 b25324 b25325 b25326 d25279 d25283 d25299
      omega
    have d25327 : (x (-11) 3 && x (-11) 14).toNat = 0 := by
      have r25328 := hand1 (x (-11) 3) (x (-11) 14)
      have b25329 := hb (x (-11) 3)
      have b25330 := hb (x (-11) 3 && x (-11) 14)
      clear * - r25328 b25329 b25330 d25319
      omega
    have d25331 : (x (-11) 3 && x (-11) 13).toNat = 0 := by
      have r25332 := hand1 (x (-11) 3) (x (-11) 13)
      have b25333 := hb (x (-11) 3)
      have b25334 := hb (x (-11) 3 && x (-11) 13)
      clear * - r25332 b25333 b25334 d25319
      omega
    have d25335 : (x (-11) 11).toNat = 0 := by
      have r25336 : (x (-11) 11).toNat ≤ (x (-11) 3).toNat := himp _ _ (hp11 (-11))
      have b25337 := hb (x (-11) 3)
      have b25338 := hb (x (-11) 11)
      clear * - r25336 b25337 b25338 d25319
      omega
    have d25339 : (x (-11) 1 && x (-11) 11).toNat = 0 := by
      have r25340 := hand2 (x (-11) 1) (x (-11) 11)
      have b25341 := hb (x (-11) 11)
      have b25342 := hb (x (-11) 1 && x (-11) 11)
      clear * - r25340 b25341 b25342 d25335
      omega
    have d25343 : (x 1 11).toNat = 0 := by
      have r25344 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25345 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
      have e25346 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
      have e25347 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
      have e25348 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
      have e25349 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
      have e25350 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
      have b25351 := hb (x (-3) 7)
      have b25352 := hb (x (-2) 6)
      have b25353 := hb (x (-1) 5)
      have b25354 := hb (x 0 4)
      have b25355 := hb (x 1 11)
      have b25356 := hb (x 2 10)
      have b25357 := hb (x 3 9)
      have b25358 := hb (x 4 8)
      clear * - r25344 e25345 e25346 e25347 e25348 e25349 e25350 b25351 b25352 b25353 b25354 b25355 b25356 b25357 b25358 d25175 d25191 d25207 f24885 d22823
      omega
    have d25359 : (x 1 1 && x 1 11).toNat = 0 := by
      have r25360 := hand2 (x 1 1) (x 1 11)
      have b25361 := hb (x 1 11)
      have b25362 := hb (x 1 1 && x 1 11)
      clear * - r25360 b25361 b25362 d25343
      omega
    have d25363 : (x (-2) 4 && x (-2) 14).toNat = 1 := by
      have r25364 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25365 := hb (x (-3) 5)
      have b25366 := hb (x 2 10)
      have b25367 := hb (x 1 1 && x 1 11)
      have b25368 := hb (x 0 2 && x 0 12)
      have b25369 := hb (x (-1) 3 && x (-1) 13)
      have b25370 := hb (x (-2) 4 && x (-2) 14)
      clear * - r25364 b25365 b25366 b25367 b25368 b25369 b25370 d25207 d25359 d22628 d22811 d25095
      omega
    have d25371 : (x (-2) 4).toNat = 1 := by
      have r25372 := hand1 (x (-2) 4) (x (-2) 14)
      have b25373 := hb (x (-2) 4)
      have b25374 := hb (x (-2) 4 && x (-2) 14)
      clear * - r25372 b25373 b25374 d25363
      omega
    have d25375 : (x (-2) 12).toNat = 1 := by
      have r25376 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
      have b25377 := hb (x (-2) 4)
      have b25378 := hb (x (-2) 12)
      clear * - r25376 b25377 b25378 d25371
      omega
    have d25379 : (x (-4) 2).toNat = 0 := by
      have r25380 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25381 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e25382 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have b25383 := hb (x (-5) 3)
      have b25384 := hb (x (-4) 2)
      have b25385 := hb (x (-3) 13)
      have b25386 := hb (x (-2) 12)
      clear * - r25380 e25381 e25382 b25383 b25384 b25385 b25386 d25375 d25091
      omega
    have d25387 : (x (-4) 2 && x (-4) 12).toNat = 0 := by
      have r25388 := hand1 (x (-4) 2) (x (-4) 12)
      have b25389 := hb (x (-4) 2)
      have b25390 := hb (x (-4) 2 && x (-4) 12)
      clear * - r25388 b25389 b25390 d25379
      omega
    have d25391 : (x (-4) 2 && x (-4) 9).toNat = 0 := by
      have r25392 := hand1 (x (-4) 2) (x (-4) 9)
      have b25393 := hb (x (-4) 2)
      have b25394 := hb (x (-4) 2 && x (-4) 9)
      clear * - r25392 b25393 b25394 d25379
      omega
    have d25395 : (x (-4) 10).toNat = 0 := by
      have r25396 : (x (-4) 10).toNat ≤ (x (-4) 2).toNat := himp _ _ (hp10 (-4))
      have b25397 := hb (x (-4) 2)
      have b25398 := hb (x (-4) 10)
      clear * - r25396 b25397 b25398 d25379
      omega
    have d25399 : (x (-8) 4 && x (-8) 14).toNat = 1 := by
      have r25400 : 1 ≤ (x (-4) 10).toNat + (x (-5) 1 && x (-5) 11).toNat + (x (-6) 2 && x (-6) 12).toNat + (x (-7) 3 && x (-7) 13).toNat + (x (-8) 4 && x (-8) 14).toNat + (x (-9) 5).toNat := by have q := hcov10 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25401 := hb (x (-9) 5)
      have b25402 := hb (x (-4) 10)
      have b25403 := hb (x (-5) 1 && x (-5) 11)
      have b25404 := hb (x (-6) 2 && x (-6) 12)
      have b25405 := hb (x (-7) 3 && x (-7) 13)
      have b25406 := hb (x (-8) 4 && x (-8) 14)
      clear * - r25400 b25401 b25402 b25403 b25404 b25405 b25406 d25395 d25167 d24985 d25005 d25295
      omega
    have d25407 : (x (-8) 14).toNat = 1 := by
      have r25408 := hand2 (x (-8) 4) (x (-8) 14)
      have b25409 := hb (x (-8) 14)
      have b25410 := hb (x (-8) 4 && x (-8) 14)
      clear * - r25408 b25409 b25410 d25399
      omega
    have d25411 : (x (-9) 1).toNat = 0 := by
      have r25412 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25413 := hb (x (-9) 1)
      have b25414 := hb (x (-8) 14)
      clear * - r25412 b25413 b25414 d25407
      omega
    have d25415 : (x (-9) 1 && x (-9) 14).toNat = 0 := by
      have r25416 := hand1 (x (-9) 1) (x (-9) 14)
      have b25417 := hb (x (-9) 1)
      have b25418 := hb (x (-9) 1 && x (-9) 14)
      clear * - r25416 b25417 b25418 d25411
      omega
    have d25419 : (x (-8) 13).toNat = 1 := by
      have r25420 : 1 ≤ (x (-8) 13).toNat + (x (-9) 1 && x (-9) 14).toNat + (x (-10) 2).toNat := by have q := hcov13 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25421 := hb (x (-10) 2)
      have b25422 := hb (x (-8) 13)
      have b25423 := hb (x (-9) 1 && x (-9) 14)
      clear * - r25420 b25421 b25422 b25423 d25415 d25299
      omega
    have d25424 : (x (-8) 1).toNat = 1 := by
      have r25425 : (x (-8) 13).toNat ≤ (x (-8) 1).toNat := himp _ _ (hp13 (-8))
      have b25426 := hb (x (-8) 1)
      have b25427 := hb (x (-8) 13)
      clear * - r25425 b25426 b25427 d25419
      omega
    have d25428 : (x (-7) 14).toNat = 0 := by
      have r25429 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25430 := hb (x (-8) 1)
      have b25431 := hb (x (-7) 14)
      clear * - r25429 b25430 b25431 d25424
      omega
    have d25432 : (x (-7) 1 && x (-7) 14).toNat = 0 := by
      have r25433 := hand2 (x (-7) 1) (x (-7) 14)
      have b25434 := hb (x (-7) 14)
      have b25435 := hb (x (-7) 1 && x (-7) 14)
      clear * - r25433 b25434 b25435 d25428
      omega
    have d25436 : (x (-7) 6).toNat = 0 := by
      have r25437 : (x (-7) 6).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp6 (-7))
      have b25438 := hb (x (-7) 6)
      have b25439 := hb (x (-7) 14)
      clear * - r25437 b25438 b25439 d25428
      omega
    have d25440 : (x (-6) 5 && x (-6) 14).toNat = 1 := by
      have r25441 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25442 := hb (x (-7) 6)
      have b25443 := hb (x (-1) 9)
      have b25444 := hb (x (-2) 1 && x (-2) 10)
      have b25445 := hb (x (-3) 2 && x (-3) 11)
      have b25446 := hb (x (-4) 3 && x (-4) 12)
      have b25447 := hb (x (-5) 4 && x (-5) 13)
      have b25448 := hb (x (-6) 5 && x (-6) 14)
      clear * - r25441 b25442 b25443 b25444 b25445 b25446 b25447 b25448 d22835 d24910 d24938 d25264 d24965 d25436
      omega
    have d25449 : (x (-6) 14).toNat = 1 := by
      have r25450 := hand2 (x (-6) 5) (x (-6) 14)
      have b25451 := hb (x (-6) 14)
      have b25452 := hb (x (-6) 5 && x (-6) 14)
      clear * - r25450 b25451 b25452 d25440
      omega
    have d25453 : (x (-7) 1).toNat = 0 := by
      have r25454 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25455 := hb (x (-7) 1)
      have b25456 := hb (x (-6) 14)
      clear * - r25454 b25455 b25456 d25449
      omega
    have d25457 : (x (-7) 1 && x (-7) 12).toNat = 0 := by
      have r25458 := hand1 (x (-7) 1) (x (-7) 12)
      have b25459 := hb (x (-7) 1)
      have b25460 := hb (x (-7) 1 && x (-7) 12)
      clear * - r25458 b25459 b25460 d25453
      omega
    have d25461 : (x (-7) 13).toNat = 0 := by
      have r25462 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
      have b25463 := hb (x (-7) 1)
      have b25464 := hb (x (-7) 13)
      clear * - r25462 b25463 b25464 d25453
      omega
    have d25465 : (x (-7) 5).toNat = 0 := by
      have r25466 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
      have b25467 := hb (x (-7) 5)
      have b25468 := hb (x (-7) 13)
      clear * - r25466 b25467 b25468 d25461
      omega
    have d25469 : (x (-7) 5 && x (-7) 12).toNat = 0 := by
      have r25470 := hand1 (x (-7) 5) (x (-7) 12)
      have b25471 := hb (x (-7) 5)
      have b25472 := hb (x (-7) 5 && x (-7) 12)
      clear * - r25470 b25471 b25472 d25465
      omega
    have d25473 : (x (-6) 4 && x (-6) 14).toNat = 1 := by
      have r25474 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25475 := hb (x (-7) 5)
      have b25476 := hb (x (-2) 10)
      have b25477 := hb (x (-3) 1 && x (-3) 11)
      have b25478 := hb (x (-4) 2 && x (-4) 12)
      have b25479 := hb (x (-5) 3 && x (-5) 13)
      have b25480 := hb (x (-6) 4 && x (-6) 14)
      clear * - r25474 b25475 b25476 b25477 b25478 b25479 b25480 d24906 d24934 d25387 d24961 d25465
      omega
    have d25481 : (x (-6) 4).toNat = 1 := by
      have r25482 := hand1 (x (-6) 4) (x (-6) 14)
      have b25483 := hb (x (-6) 4)
      have b25484 := hb (x (-6) 4 && x (-6) 14)
      clear * - r25482 b25483 b25484 d25473
      omega
    have d25485 : (x (-6) 12).toNat = 1 := by
      have r25486 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
      have b25487 := hb (x (-6) 4)
      have b25488 := hb (x (-6) 12)
      clear * - r25486 b25487 b25488 d25481
      omega
    have d25489 : (x (-8) 2).toNat = 0 := by
      have r25490 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25491 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
      have e25492 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
      have b25493 := hb (x (-9) 3)
      have b25494 := hb (x (-8) 2)
      have b25495 := hb (x (-7) 13)
      have b25496 := hb (x (-6) 12)
      clear * - r25490 e25491 e25492 b25493 b25494 b25495 b25496 d25485 d25461
      omega
    have d25497 : (x (-8) 2 && x (-8) 13).toNat = 0 := by
      have r25498 := hand1 (x (-8) 2) (x (-8) 13)
      have b25499 := hb (x (-8) 2)
      have b25500 := hb (x (-8) 2 && x (-8) 13)
      clear * - r25498 b25499 b25500 d25489
      omega
    have d25501 : (x (-8) 2 && x (-8) 12).toNat = 0 := by
      have r25502 := hand1 (x (-8) 2) (x (-8) 12)
      have b25503 := hb (x (-8) 2)
      have b25504 := hb (x (-8) 2 && x (-8) 12)
      clear * - r25502 b25503 b25504 d25489
      omega
    have d25505 : (x (-8) 10).toNat = 0 := by
      have r25506 : (x (-8) 10).toNat ≤ (x (-8) 2).toNat := himp _ _ (hp10 (-8))
      have b25507 := hb (x (-8) 2)
      have b25508 := hb (x (-8) 10)
      clear * - r25506 b25507 b25508 d25489
      omega
    have d25509 : (x (-6) 13).toNat = 1 := by
      have r25510 : 1 ≤ (x (-6) 13).toNat + (x (-7) 1 && x (-7) 14).toNat + (x (-8) 2).toNat := by have q := hcov13 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25511 := hb (x (-8) 2)
      have b25512 := hb (x (-6) 13)
      have b25513 := hb (x (-7) 1 && x (-7) 14)
      clear * - r25510 b25511 b25512 b25513 d25432 d25489
      omega
    have d25514 : (x (-6) 1).toNat = 1 := by
      have r25515 : (x (-6) 13).toNat ≤ (x (-6) 1).toNat := himp _ _ (hp13 (-6))
      have b25516 := hb (x (-6) 1)
      have b25517 := hb (x (-6) 13)
      clear * - r25515 b25516 b25517 d25509
      omega
    have d25518 : (x (-5) 14).toNat = 0 := by
      have r25519 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25520 := hb (x (-6) 1)
      have b25521 := hb (x (-5) 14)
      clear * - r25519 b25520 b25521 d25514
      omega
    have d25522 : (x (-5) 7 && x (-5) 14).toNat = 0 := by
      have r25523 := hand2 (x (-5) 7) (x (-5) 14)
      have b25524 := hb (x (-5) 14)
      have b25525 := hb (x (-5) 7 && x (-5) 14)
      clear * - r25523 b25524 b25525 d25518
      omega
    have d25526 : (x (-5) 6).toNat = 0 := by
      have r25527 : (x (-5) 6).toNat ≤ (x (-5) 14).toNat := himp _ _ (hp6 (-5))
      have b25528 := hb (x (-5) 6)
      have b25529 := hb (x (-5) 14)
      clear * - r25527 b25528 b25529 d25518
      omega
    have d25530 : (x (-5) 12).toNat = 0 := by
      have r25531 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25532 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
      have e25533 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
      have b25534 := hb (x (-8) 3)
      have b25535 := hb (x (-7) 2)
      have b25536 := hb (x (-6) 13)
      have b25537 := hb (x (-5) 12)
      clear * - r25531 e25532 e25533 b25534 b25535 b25536 b25537 d25509
      omega
    have d25538 : (x (-7) 2).toNat = 0 := by
      have r25539 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25540 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
      have e25541 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
      have b25542 := hb (x (-8) 3)
      have b25543 := hb (x (-7) 2)
      have b25544 := hb (x (-6) 13)
      have b25545 := hb (x (-5) 12)
      clear * - r25539 e25540 e25541 b25542 b25543 b25544 b25545 d25530 d25509
      omega
    have d25546 : (x (-8) 3).toNat = 0 := by
      have r25547 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25548 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
      have e25549 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
      have b25550 := hb (x (-8) 3)
      have b25551 := hb (x (-7) 2)
      have b25552 := hb (x (-6) 13)
      have b25553 := hb (x (-5) 12)
      clear * - r25547 e25548 e25549 b25550 b25551 b25552 b25553 d25530 d25509 d25538
      omega
    have d25554 : (x (-8) 11).toNat = 0 := by
      have r25555 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
      have b25556 := hb (x (-8) 3)
      have b25557 := hb (x (-8) 11)
      clear * - r25555 b25556 b25557 d25546
      omega
    have d25558 : (x (-9) 3).toNat = 0 := by
      have r25559 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25560 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
      have e25561 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
      have b25562 := hb (x (-9) 3)
      have b25563 := hb (x (-8) 2)
      have b25564 := hb (x (-7) 13)
      have b25565 := hb (x (-6) 12)
      clear * - r25559 e25560 e25561 b25562 b25563 b25564 b25565 d25485 d25461 d25489
      omega
    have d25566 : (x (-9) 3 && x (-9) 14).toNat = 0 := by
      have r25567 := hand1 (x (-9) 3) (x (-9) 14)
      have b25568 := hb (x (-9) 3)
      have b25569 := hb (x (-9) 3 && x (-9) 14)
      clear * - r25567 b25568 b25569 d25558
      omega
    have d25570 : (x (-10) 4).toNat = 1 := by
      have r25571 : 1 ≤ (x (-6) 11).toNat + (x (-7) 1 && x (-7) 12).toNat + (x (-8) 2 && x (-8) 13).toNat + (x (-9) 3 && x (-9) 14).toNat + (x (-10) 4).toNat := by have q := hcov11 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25572 := hb (x (-10) 4)
      have b25573 := hb (x (-6) 11)
      have b25574 := hb (x (-7) 1 && x (-7) 12)
      have b25575 := hb (x (-8) 2 && x (-8) 13)
      have b25576 := hb (x (-9) 3 && x (-9) 14)
      clear * - r25571 b25572 b25573 b25574 b25575 b25576 d25155 d25457 d25497 d25566
      omega
    have d25577 : (x (-10) 12).toNat = 1 := by
      have r25578 : (x (-10) 4).toNat ≤ (x (-10) 12).toNat := himp _ _ (hp4 (-10))
      have b25579 := hb (x (-10) 4)
      have b25580 := hb (x (-10) 12)
      clear * - r25578 b25579 b25580 d25570
      omega
    have d25581 : (x (-11) 13).toNat = 0 := by
      have r25582 : (x (-10) 12).toNat + (x (-11) 1 && x (-11) 13).toNat + (x (-12) 2 && x (-12) 14).toNat + (x (-13) 3).toNat = 1 := by have q := hd12 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25583 : (x (-11) 1 && x (-11) 13).toNat = (x (-11) 13).toNat := handr _ _ (fun h => hp13 (-11) (h))
      have e25584 : (x (-12) 2 && x (-12) 14).toNat = (x (-12) 2).toNat := handl _ _ (fun h => hp2 (-12) (h))
      have b25585 := hb (x (-13) 3)
      have b25586 := hb (x (-12) 2)
      have b25587 := hb (x (-11) 13)
      have b25588 := hb (x (-10) 12)
      clear * - r25582 e25583 e25584 b25585 b25586 b25587 b25588 d25577
      omega
    have d25589 : (x (-11) 5).toNat = 0 := by
      have r25590 : (x (-11) 5).toNat ≤ (x (-11) 13).toNat := himp _ _ (hp5 (-11))
      have b25591 := hb (x (-11) 5)
      have b25592 := hb (x (-11) 13)
      clear * - r25590 b25591 b25592 d25581
      omega
    have d25593 : (x (-10) 4 && x (-10) 14).toNat = 1 := by
      have r25594 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25595 := hb (x (-11) 5)
      have b25596 := hb (x (-6) 10)
      have b25597 := hb (x (-7) 1 && x (-7) 11)
      have b25598 := hb (x (-8) 2 && x (-8) 12)
      have b25599 := hb (x (-9) 3 && x (-9) 13)
      have b25600 := hb (x (-10) 4 && x (-10) 14)
      clear * - r25594 b25595 b25596 b25597 b25598 b25599 b25600 d24989 d25013 d25501 d25291 d25589
      omega
    have d25601 : (x (-10) 14).toNat = 1 := by
      have r25602 := hand2 (x (-10) 4) (x (-10) 14)
      have b25603 := hb (x (-10) 14)
      have b25604 := hb (x (-10) 4 && x (-10) 14)
      clear * - r25602 b25603 b25604 d25593
      omega
    have d25605 : (x (-11) 1).toNat = 0 := by
      have r25606 : (x (-10) 14).toNat + (x (-11) 1).toNat = 1 := by have q := hd14 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25607 := hb (x (-11) 1)
      have b25608 := hb (x (-10) 14)
      clear * - r25606 b25607 b25608 d25601
      omega
    have d25609 : (x (-11) 1 && x (-11) 14).toNat = 0 := by
      have r25610 := hand1 (x (-11) 1) (x (-11) 14)
      have b25611 := hb (x (-11) 1)
      have b25612 := hb (x (-11) 1 && x (-11) 14)
      clear * - r25610 b25611 b25612 d25605
      omega
    have d25613 : (x (-11) 9).toNat = 0 := by
      have r25614 : (x (-11) 9).toNat ≤ (x (-11) 1).toNat := himp _ _ (hp9 (-11))
      have b25615 := hb (x (-11) 1)
      have b25616 := hb (x (-11) 9)
      clear * - r25614 b25615 b25616 d25605
      omega
    have d25617 : (x (-12) 2).toNat = 0 := by
      have r25618 : (x (-10) 12).toNat + (x (-11) 1 && x (-11) 13).toNat + (x (-12) 2 && x (-12) 14).toNat + (x (-13) 3).toNat = 1 := by have q := hd12 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25619 : (x (-11) 1 && x (-11) 13).toNat = (x (-11) 13).toNat := handr _ _ (fun h => hp13 (-11) (h))
      have e25620 : (x (-12) 2 && x (-12) 14).toNat = (x (-12) 2).toNat := handl _ _ (fun h => hp2 (-12) (h))
      have b25621 := hb (x (-13) 3)
      have b25622 := hb (x (-12) 2)
      have b25623 := hb (x (-11) 13)
      have b25624 := hb (x (-10) 12)
      clear * - r25618 e25619 e25620 b25621 b25622 b25623 b25624 d25577 d25581
      omega
    have d25625 : (x (-12) 2 && x (-12) 12).toNat = 0 := by
      have r25626 := hand1 (x (-12) 2) (x (-12) 12)
      have b25627 := hb (x (-12) 2)
      have b25628 := hb (x (-12) 2 && x (-12) 12)
      clear * - r25626 b25627 b25628 d25617
      omega
    have d25629 : (x (-12) 10).toNat = 0 := by
      have r25630 : (x (-12) 10).toNat ≤ (x (-12) 2).toNat := himp _ _ (hp10 (-12))
      have b25631 := hb (x (-12) 2)
      have b25632 := hb (x (-12) 10)
      clear * - r25630 b25631 b25632 d25617
      omega
    have d25633 : (x (-10) 13).toNat = 1 := by
      have r25634 : 1 ≤ (x (-10) 13).toNat + (x (-11) 1 && x (-11) 14).toNat + (x (-12) 2).toNat := by have q := hcov13 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25635 := hb (x (-12) 2)
      have b25636 := hb (x (-10) 13)
      have b25637 := hb (x (-11) 1 && x (-11) 14)
      clear * - r25634 b25635 b25636 b25637 d25609 d25617
      omega
    have d25638 : (x (-10) 1).toNat = 1 := by
      have r25639 : (x (-10) 13).toNat ≤ (x (-10) 1).toNat := himp _ _ (hp13 (-10))
      have b25640 := hb (x (-10) 1)
      have b25641 := hb (x (-10) 13)
      clear * - r25639 b25640 b25641 d25633
      omega
    have d25642 : (x (-9) 14).toNat = 0 := by
      have r25643 : (x (-9) 14).toNat + (x (-10) 1).toNat = 1 := by have q := hd14 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25644 := hb (x (-10) 1)
      have b25645 := hb (x (-9) 14)
      clear * - r25643 b25644 b25645 d25638
      omega
    have d25646 : (x (-9) 7 && x (-9) 14).toNat = 0 := by
      have r25647 := hand2 (x (-9) 7) (x (-9) 14)
      have b25648 := hb (x (-9) 14)
      have b25649 := hb (x (-9) 7 && x (-9) 14)
      clear * - r25647 b25648 b25649 d25642
      omega
    have d25650 : (x (-9) 12).toNat = 0 := by
      have r25651 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25652 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
      have e25653 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
      have b25654 := hb (x (-12) 3)
      have b25655 := hb (x (-11) 2)
      have b25656 := hb (x (-10) 13)
      have b25657 := hb (x (-9) 12)
      clear * - r25651 e25652 e25653 b25654 b25655 b25656 b25657 d25633
      omega
    have d25658 : (x (-9) 1 && x (-9) 12).toNat = 0 := by
      have r25659 := hand2 (x (-9) 1) (x (-9) 12)
      have b25660 := hb (x (-9) 12)
      have b25661 := hb (x (-9) 1 && x (-9) 12)
      clear * - r25659 b25660 b25661 d25650
      omega
    have d25662 : (x (-12) 4).toNat = 1 := by
      have r25663 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := by have q := hcov11 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25664 := hb (x (-12) 4)
      have b25665 := hb (x (-8) 11)
      have b25666 := hb (x (-9) 1 && x (-9) 12)
      have b25667 := hb (x (-10) 2 && x (-10) 13)
      have b25668 := hb (x (-11) 3 && x (-11) 14)
      clear * - r25663 b25664 b25665 b25666 b25667 b25668 d25554 d25658 d25307 d25327
      omega
    have d25669 : (x (-12) 12).toNat = 1 := by
      have r25670 : (x (-12) 4).toNat ≤ (x (-12) 12).toNat := himp _ _ (hp4 (-12))
      have b25671 := hb (x (-12) 4)
      have b25672 := hb (x (-12) 12)
      clear * - r25670 b25671 b25672 d25662
      omega
    have d25673 : (x (-13) 13).toNat = 0 := by
      have r25674 : (x (-12) 12).toNat + (x (-13) 1 && x (-13) 13).toNat + (x (-14) 2 && x (-14) 14).toNat + (x (-15) 3).toNat = 1 := by have q := hd12 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25675 : (x (-13) 1 && x (-13) 13).toNat = (x (-13) 13).toNat := handr _ _ (fun h => hp13 (-13) (h))
      have e25676 : (x (-14) 2 && x (-14) 14).toNat = (x (-14) 2).toNat := handl _ _ (fun h => hp2 (-14) (h))
      have b25677 := hb (x (-15) 3)
      have b25678 := hb (x (-14) 2)
      have b25679 := hb (x (-13) 13)
      have b25680 := hb (x (-12) 12)
      clear * - r25674 e25675 e25676 b25677 b25678 b25679 b25680 d25669
      omega
    have d25681 : (x (-13) 3 && x (-13) 13).toNat = 0 := by
      have r25682 := hand2 (x (-13) 3) (x (-13) 13)
      have b25683 := hb (x (-13) 13)
      have b25684 := hb (x (-13) 3 && x (-13) 13)
      clear * - r25682 b25683 b25684 d25673
      omega
    have d25685 : (x (-13) 5).toNat = 0 := by
      have r25686 : (x (-13) 5).toNat ≤ (x (-13) 13).toNat := himp _ _ (hp5 (-13))
      have b25687 := hb (x (-13) 5)
      have b25688 := hb (x (-13) 13)
      clear * - r25686 b25687 b25688 d25673
      omega
    have d25689 : (x (-14) 2).toNat = 0 := by
      have r25690 : (x (-12) 12).toNat + (x (-13) 1 && x (-13) 13).toNat + (x (-14) 2 && x (-14) 14).toNat + (x (-15) 3).toNat = 1 := by have q := hd12 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25691 : (x (-13) 1 && x (-13) 13).toNat = (x (-13) 13).toNat := handr _ _ (fun h => hp13 (-13) (h))
      have e25692 : (x (-14) 2 && x (-14) 14).toNat = (x (-14) 2).toNat := handl _ _ (fun h => hp2 (-14) (h))
      have b25693 := hb (x (-15) 3)
      have b25694 := hb (x (-14) 2)
      have b25695 := hb (x (-13) 13)
      have b25696 := hb (x (-12) 12)
      clear * - r25690 e25691 e25692 b25693 b25694 b25695 b25696 d25669 d25673
      omega
    have d25697 : (x (-14) 2 && x (-14) 13).toNat = 0 := by
      have r25698 := hand1 (x (-14) 2) (x (-14) 13)
      have b25699 := hb (x (-14) 2)
      have b25700 := hb (x (-14) 2 && x (-14) 13)
      clear * - r25698 b25699 b25700 d25689
      omega
    have d25701 : (x (-14) 2 && x (-14) 12).toNat = 0 := by
      have r25702 := hand1 (x (-14) 2) (x (-14) 12)
      have b25703 := hb (x (-14) 2)
      have b25704 := hb (x (-14) 2 && x (-14) 12)
      clear * - r25702 b25703 b25704 d25689
      omega
    have d25705 : (x (-15) 3).toNat = 0 := by
      have r25706 : (x (-12) 12).toNat + (x (-13) 1 && x (-13) 13).toNat + (x (-14) 2 && x (-14) 14).toNat + (x (-15) 3).toNat = 1 := by have q := hd12 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25707 : (x (-13) 1 && x (-13) 13).toNat = (x (-13) 13).toNat := handr _ _ (fun h => hp13 (-13) (h))
      have e25708 : (x (-14) 2 && x (-14) 14).toNat = (x (-14) 2).toNat := handl _ _ (fun h => hp2 (-14) (h))
      have b25709 := hb (x (-15) 3)
      have b25710 := hb (x (-14) 2)
      have b25711 := hb (x (-13) 13)
      have b25712 := hb (x (-12) 12)
      clear * - r25706 e25707 e25708 b25709 b25710 b25711 b25712 d25669 d25673 d25689
      omega
    have d25713 : (x (-15) 3 && x (-15) 14).toNat = 0 := by
      have r25714 := hand1 (x (-15) 3) (x (-15) 14)
      have b25715 := hb (x (-15) 3)
      have b25716 := hb (x (-15) 3 && x (-15) 14)
      clear * - r25714 b25715 b25716 d25705
      omega
    have d25717 : (x (-15) 3 && x (-15) 13).toNat = 0 := by
      have r25718 := hand1 (x (-15) 3) (x (-15) 13)
      have b25719 := hb (x (-15) 3)
      have b25720 := hb (x (-15) 3 && x (-15) 13)
      clear * - r25718 b25719 b25720 d25705
      omega
    have d25721 : (x (-11) 2).toNat = 0 := by
      have r25722 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25723 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
      have e25724 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
      have b25725 := hb (x (-12) 3)
      have b25726 := hb (x (-11) 2)
      have b25727 := hb (x (-10) 13)
      have b25728 := hb (x (-9) 12)
      clear * - r25722 e25723 e25724 b25725 b25726 b25727 b25728 d25650 d25633
      omega
    have d25729 : (x (-12) 3).toNat = 0 := by
      have r25730 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25731 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
      have e25732 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
      have b25733 := hb (x (-12) 3)
      have b25734 := hb (x (-11) 2)
      have b25735 := hb (x (-10) 13)
      have b25736 := hb (x (-9) 12)
      clear * - r25730 e25731 e25732 b25733 b25734 b25735 b25736 d25650 d25633 d25721
      omega
    have d25737 : (x (-12) 11).toNat = 0 := by
      have r25738 : (x (-12) 11).toNat ≤ (x (-12) 3).toNat := himp _ _ (hp11 (-12))
      have b25739 := hb (x (-12) 3)
      have b25740 := hb (x (-12) 11)
      clear * - r25738 b25739 b25740 d25729
      omega
    have d25741 : (x (-13) 3).toNat = 0 := by
      have r25742 : (x (-10) 12).toNat + (x (-11) 1 && x (-11) 13).toNat + (x (-12) 2 && x (-12) 14).toNat + (x (-13) 3).toNat = 1 := by have q := hd12 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25743 : (x (-11) 1 && x (-11) 13).toNat = (x (-11) 13).toNat := handr _ _ (fun h => hp13 (-11) (h))
      have e25744 : (x (-12) 2 && x (-12) 14).toNat = (x (-12) 2).toNat := handl _ _ (fun h => hp2 (-12) (h))
      have b25745 := hb (x (-13) 3)
      have b25746 := hb (x (-12) 2)
      have b25747 := hb (x (-11) 13)
      have b25748 := hb (x (-10) 12)
      clear * - r25742 e25743 e25744 b25745 b25746 b25747 b25748 d25577 d25581 d25617
      omega
    have d25749 : (x (-13) 11).toNat = 0 := by
      have r25750 : (x (-13) 11).toNat ≤ (x (-13) 3).toNat := himp _ _ (hp11 (-13))
      have b25751 := hb (x (-13) 3)
      have b25752 := hb (x (-13) 11)
      clear * - r25750 b25751 b25752 d25741
      omega
    have d25753 : (x (-13) 1 && x (-13) 11).toNat = 0 := by
      have r25754 := hand2 (x (-13) 1) (x (-13) 11)
      have b25755 := hb (x (-13) 11)
      have b25756 := hb (x (-13) 1 && x (-13) 11)
      clear * - r25754 b25755 b25756 d25749
      omega
    have d25757 : (x (-9) 11).toNat = 0 := by
      have r25758 : (x (-9) 11).toNat ≤ (x (-9) 3).toNat := himp _ _ (hp11 (-9))
      have b25759 := hb (x (-9) 3)
      have b25760 := hb (x (-9) 11)
      clear * - r25758 b25759 b25760 d25558
      omega
    have d25761 : (x (-9) 1 && x (-9) 11).toNat = 0 := by
      have r25762 := hand2 (x (-9) 1) (x (-9) 11)
      have b25763 := hb (x (-9) 11)
      have b25764 := hb (x (-9) 1 && x (-9) 11)
      clear * - r25762 b25763 b25764 d25757
      omega
    have d25765 : (x (-12) 4 && x (-12) 14).toNat = 1 := by
      have r25766 : 1 ≤ (x (-8) 10).toNat + (x (-9) 1 && x (-9) 11).toNat + (x (-10) 2 && x (-10) 12).toNat + (x (-11) 3 && x (-11) 13).toNat + (x (-12) 4 && x (-12) 14).toNat + (x (-13) 5).toNat := by have q := hcov10 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25767 := hb (x (-13) 5)
      have b25768 := hb (x (-8) 10)
      have b25769 := hb (x (-9) 1 && x (-9) 11)
      have b25770 := hb (x (-10) 2 && x (-10) 12)
      have b25771 := hb (x (-11) 3 && x (-11) 13)
      have b25772 := hb (x (-12) 4 && x (-12) 14)
      clear * - r25766 b25767 b25768 b25769 b25770 b25771 b25772 d25505 d25761 d25311 d25331 d25685
      omega
    have d25773 : (x (-12) 14).toNat = 1 := by
      have r25774 := hand2 (x (-12) 4) (x (-12) 14)
      have b25775 := hb (x (-12) 14)
      have b25776 := hb (x (-12) 4 && x (-12) 14)
      clear * - r25774 b25775 b25776 d25765
      omega
    have d25777 : (x (-13) 1).toNat = 0 := by
      have r25778 : (x (-12) 14).toNat + (x (-13) 1).toNat = 1 := by have q := hd14 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25779 := hb (x (-13) 1)
      have b25780 := hb (x (-12) 14)
      clear * - r25778 b25779 b25780 d25773
      omega
    have d25781 : (x (-13) 1 && x (-13) 12).toNat = 0 := by
      have r25782 := hand1 (x (-13) 1) (x (-13) 12)
      have b25783 := hb (x (-13) 1)
      have b25784 := hb (x (-13) 1 && x (-13) 12)
      clear * - r25782 b25783 b25784 d25777
      omega
    have d25785 : (x (-16) 4).toNat = 1 := by
      have r25786 : 1 ≤ (x (-12) 11).toNat + (x (-13) 1 && x (-13) 12).toNat + (x (-14) 2 && x (-14) 13).toNat + (x (-15) 3 && x (-15) 14).toNat + (x (-16) 4).toNat := by have q := hcov11 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25787 := hb (x (-16) 4)
      have b25788 := hb (x (-12) 11)
      have b25789 := hb (x (-13) 1 && x (-13) 12)
      have b25790 := hb (x (-14) 2 && x (-14) 13)
      have b25791 := hb (x (-15) 3 && x (-15) 14)
      clear * - r25786 b25787 b25788 b25789 b25790 b25791 d25737 d25781 d25697 d25713
      omega
    have d25792 : (x (-16) 12).toNat = 1 := by
      have r25793 : (x (-16) 4).toNat ≤ (x (-16) 12).toNat := himp _ _ (hp4 (-16))
      have b25794 := hb (x (-16) 4)
      have b25795 := hb (x (-16) 12)
      clear * - r25793 b25794 b25795 d25785
      omega
    have d25796 : (x (-17) 13).toNat = 0 := by
      have r25797 : (x (-16) 12).toNat + (x (-17) 1 && x (-17) 13).toNat + (x (-18) 2 && x (-18) 14).toNat + (x (-19) 3).toNat = 1 := by have q := hd12 (-16); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25798 : (x (-17) 1 && x (-17) 13).toNat = (x (-17) 13).toNat := handr _ _ (fun h => hp13 (-17) (h))
      have e25799 : (x (-18) 2 && x (-18) 14).toNat = (x (-18) 2).toNat := handl _ _ (fun h => hp2 (-18) (h))
      have b25800 := hb (x (-19) 3)
      have b25801 := hb (x (-18) 2)
      have b25802 := hb (x (-17) 13)
      have b25803 := hb (x (-16) 12)
      clear * - r25797 e25798 e25799 b25800 b25801 b25802 b25803 d25792
      omega
    have d25804 : (x (-17) 5).toNat = 0 := by
      have r25805 : (x (-17) 5).toNat ≤ (x (-17) 13).toNat := himp _ _ (hp5 (-17))
      have b25806 := hb (x (-17) 5)
      have b25807 := hb (x (-17) 13)
      clear * - r25805 b25806 b25807 d25796
      omega
    have d25808 : (x (-16) 4 && x (-16) 14).toNat = 1 := by
      have r25809 : 1 ≤ (x (-12) 10).toNat + (x (-13) 1 && x (-13) 11).toNat + (x (-14) 2 && x (-14) 12).toNat + (x (-15) 3 && x (-15) 13).toNat + (x (-16) 4 && x (-16) 14).toNat + (x (-17) 5).toNat := by have q := hcov10 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25810 := hb (x (-17) 5)
      have b25811 := hb (x (-12) 10)
      have b25812 := hb (x (-13) 1 && x (-13) 11)
      have b25813 := hb (x (-14) 2 && x (-14) 12)
      have b25814 := hb (x (-15) 3 && x (-15) 13)
      have b25815 := hb (x (-16) 4 && x (-16) 14)
      clear * - r25809 b25810 b25811 b25812 b25813 b25814 b25815 d25629 d25753 d25701 d25717 d25804
      omega
    have d25816 : (x (-16) 14).toNat = 1 := by
      have r25817 := hand2 (x (-16) 4) (x (-16) 14)
      have b25818 := hb (x (-16) 14)
      have b25819 := hb (x (-16) 4 && x (-16) 14)
      clear * - r25817 b25818 b25819 d25808
      omega
    have d25820 : (x (-17) 1).toNat = 0 := by
      have r25821 : (x (-16) 14).toNat + (x (-17) 1).toNat = 1 := by have q := hd14 (-16); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25822 := hb (x (-17) 1)
      have b25823 := hb (x (-16) 14)
      clear * - r25821 b25822 b25823 d25816
      omega
    have d25824 : (x (-17) 1 && x (-17) 14).toNat = 0 := by
      have r25825 := hand1 (x (-17) 1) (x (-17) 14)
      have b25826 := hb (x (-17) 1)
      have b25827 := hb (x (-17) 1 && x (-17) 14)
      clear * - r25825 b25826 b25827 d25820
      omega
    have d25828 : (x (-18) 2).toNat = 0 := by
      have r25829 : (x (-16) 12).toNat + (x (-17) 1 && x (-17) 13).toNat + (x (-18) 2 && x (-18) 14).toNat + (x (-19) 3).toNat = 1 := by have q := hd12 (-16); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25830 : (x (-17) 1 && x (-17) 13).toNat = (x (-17) 13).toNat := handr _ _ (fun h => hp13 (-17) (h))
      have e25831 : (x (-18) 2 && x (-18) 14).toNat = (x (-18) 2).toNat := handl _ _ (fun h => hp2 (-18) (h))
      have b25832 := hb (x (-19) 3)
      have b25833 := hb (x (-18) 2)
      have b25834 := hb (x (-17) 13)
      have b25835 := hb (x (-16) 12)
      clear * - r25829 e25830 e25831 b25832 b25833 b25834 b25835 d25792 d25796
      omega
    have d25836 : (x (-16) 13).toNat = 1 := by
      have r25837 : 1 ≤ (x (-16) 13).toNat + (x (-17) 1 && x (-17) 14).toNat + (x (-18) 2).toNat := by have q := hcov13 (-16); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25838 := hb (x (-18) 2)
      have b25839 := hb (x (-16) 13)
      have b25840 := hb (x (-17) 1 && x (-17) 14)
      clear * - r25837 b25838 b25839 b25840 d25824 d25828
      omega
    have d25841 : (x (-16) 1).toNat = 1 := by
      have r25842 : (x (-16) 13).toNat ≤ (x (-16) 1).toNat := himp _ _ (hp13 (-16))
      have b25843 := hb (x (-16) 1)
      have b25844 := hb (x (-16) 13)
      clear * - r25842 b25843 b25844 d25836
      omega
    have d25845 : (x (-15) 14).toNat = 0 := by
      have r25846 : (x (-15) 14).toNat + (x (-16) 1).toNat = 1 := by have q := hd14 (-15); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25847 := hb (x (-16) 1)
      have b25848 := hb (x (-15) 14)
      clear * - r25846 b25847 b25848 d25841
      omega
    have d25849 : (x (-15) 2).toNat = 0 := by
      have r25850 : (x (-15) 2).toNat ≤ (x (-15) 14).toNat := himp _ _ (hp2 (-15))
      have b25851 := hb (x (-15) 2)
      have b25852 := hb (x (-15) 14)
      clear * - r25850 b25851 b25852 d25845
      omega
    have d25853 : (x (-14) 1 && x (-14) 14).toNat = 1 := by
      have r25854 : 1 ≤ (x (-13) 13).toNat + (x (-14) 1 && x (-14) 14).toNat + (x (-15) 2).toNat := by have q := hcov13 (-13); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25855 := hb (x (-15) 2)
      have b25856 := hb (x (-13) 13)
      have b25857 := hb (x (-14) 1 && x (-14) 14)
      clear * - r25854 b25855 b25856 b25857 d25673 d25849
      omega
    have d25858 : (x (-14) 14).toNat = 1 := by
      have r25859 := hand2 (x (-14) 1) (x (-14) 14)
      have b25860 := hb (x (-14) 14)
      have b25861 := hb (x (-14) 1 && x (-14) 14)
      clear * - r25859 b25860 b25861 d25853
      omega
    have d25862 : (x (-15) 1).toNat = 0 := by
      have r25863 : (x (-14) 14).toNat + (x (-15) 1).toNat = 1 := by have q := hd14 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25864 := hb (x (-15) 1)
      have b25865 := hb (x (-14) 14)
      clear * - r25863 b25864 b25865 d25858
      omega
    have d25866 : (x (-15) 13).toNat = 0 := by
      have r25867 : (x (-15) 13).toNat ≤ (x (-15) 1).toNat := himp _ _ (hp13 (-15))
      have b25868 := hb (x (-15) 1)
      have b25869 := hb (x (-15) 13)
      clear * - r25867 b25868 b25869 d25862
      omega
    have d25870 : (x (-15) 5).toNat = 0 := by
      have r25871 : (x (-15) 5).toNat ≤ (x (-15) 13).toNat := himp _ _ (hp5 (-15))
      have b25872 := hb (x (-15) 5)
      have b25873 := hb (x (-15) 13)
      clear * - r25871 b25872 b25873 d25866
      omega
    have d25874 : (x (-14) 4 && x (-14) 14).toNat = 1 := by
      have r25875 : 1 ≤ (x (-10) 10).toNat + (x (-11) 1 && x (-11) 11).toNat + (x (-12) 2 && x (-12) 12).toNat + (x (-13) 3 && x (-13) 13).toNat + (x (-14) 4 && x (-14) 14).toNat + (x (-15) 5).toNat := by have q := hcov10 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25876 := hb (x (-15) 5)
      have b25877 := hb (x (-10) 10)
      have b25878 := hb (x (-11) 1 && x (-11) 11)
      have b25879 := hb (x (-12) 2 && x (-12) 12)
      have b25880 := hb (x (-13) 3 && x (-13) 13)
      have b25881 := hb (x (-14) 4 && x (-14) 14)
      clear * - r25875 b25876 b25877 b25878 b25879 b25880 b25881 d25315 d25339 d25625 d25681 d25870
      omega
    have d25882 : (x (-14) 4).toNat = 1 := by
      have r25883 := hand1 (x (-14) 4) (x (-14) 14)
      have b25884 := hb (x (-14) 4)
      have b25885 := hb (x (-14) 4 && x (-14) 14)
      clear * - r25883 b25884 b25885 d25874
      omega
    have d25886 : (x (-7) 9).toNat = 0 := by
      have r25887 : (x (-7) 9).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp9 (-7))
      have b25888 := hb (x (-7) 1)
      have b25889 := hb (x (-7) 9)
      clear * - r25887 b25888 b25889 d25453
      omega
    have d25890 : (x (-5) 3).toNat = 0 := by
      have r25891 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25892 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e25893 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have b25894 := hb (x (-5) 3)
      have b25895 := hb (x (-4) 2)
      have b25896 := hb (x (-3) 13)
      have b25897 := hb (x (-2) 12)
      clear * - r25891 e25892 e25893 b25894 b25895 b25896 b25897 d25375 d25091 d25379
      omega
    have d25898 : (x (-5) 11).toNat = 0 := by
      have r25899 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
      have b25900 := hb (x (-5) 3)
      have b25901 := hb (x (-5) 11)
      clear * - r25899 b25900 b25901 d25890
      omega
    have d25902 : (x (-2) 6).toNat = 0 := by
      have r25903 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25904 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
      have e25905 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
      have e25906 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
      have e25907 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
      have e25908 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
      have e25909 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
      have b25910 := hb (x (-3) 7)
      have b25911 := hb (x (-2) 6)
      have b25912 := hb (x (-1) 5)
      have b25913 := hb (x 0 4)
      have b25914 := hb (x 1 11)
      have b25915 := hb (x 2 10)
      have b25916 := hb (x 3 9)
      have b25917 := hb (x 4 8)
      clear * - r25903 e25904 e25905 e25906 e25907 e25908 e25909 b25910 b25911 b25912 b25913 b25914 b25915 b25916 b25917 d25175 d25191 d25207 d25343 f24885 d22823
      omega
    have d25918 : (x (-2) 6 && x (-2) 13).toNat = 0 := by
      have r25919 := hand1 (x (-2) 6) (x (-2) 13)
      have b25920 := hb (x (-2) 6)
      have b25921 := hb (x (-2) 6 && x (-2) 13)
      clear * - r25919 b25920 b25921 d25902
      omega
    have d25922 : (x 3 8).toNat = 0 := by
      have r25923 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25924 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
      have e25925 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
      have e25926 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
      have e25927 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
      have e25928 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
      have e25929 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
      have b25930 := hb (x (-4) 7)
      have b25931 := hb (x (-3) 6)
      have b25932 := hb (x (-2) 5)
      have b25933 := hb (x (-1) 4)
      have b25934 := hb (x 0 11)
      have b25935 := hb (x 1 10)
      have b25936 := hb (x 2 9)
      have b25937 := hb (x 3 8)
      clear * - r25923 e25924 e25925 e25926 e25927 e25928 e25929 b25930 b25931 b25932 b25933 b25934 b25935 b25936 b25937 g9 d22737 d25252 d25236 d25066
      omega
    have d25938 : (x 3 1 && x 3 8).toNat = 0 := by
      have r25939 := hand2 (x 3 1) (x 3 8)
      have b25940 := hb (x 3 8)
      have b25941 := hb (x 3 1 && x 3 8)
      clear * - r25939 b25940 b25941 d25922
      omega
    have d25942 : (x 2 9).toNat = 0 := by
      have r25943 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25944 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
      have e25945 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
      have e25946 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
      have e25947 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
      have e25948 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
      have e25949 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
      have b25950 := hb (x (-4) 7)
      have b25951 := hb (x (-3) 6)
      have b25952 := hb (x (-2) 5)
      have b25953 := hb (x (-1) 4)
      have b25954 := hb (x 0 11)
      have b25955 := hb (x 1 10)
      have b25956 := hb (x 2 9)
      have b25957 := hb (x 3 8)
      clear * - r25943 e25944 e25945 e25946 e25947 e25948 e25949 b25950 b25951 b25952 b25953 b25954 b25955 b25956 b25957 d25922 g9 d22737 d25252 d25236 d25066
      omega
    have d25958 : (x 2 2 && x 2 9).toNat = 0 := by
      have r25959 := hand2 (x 2 2) (x 2 9)
      have b25960 := hb (x 2 9)
      have b25961 := hb (x 2 2 && x 2 9)
      clear * - r25959 b25960 b25961 d25942
      omega
    have d25962 : (x 2 8).toNat = 0 := by
      have r25963 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25964 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e25965 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e25966 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e25967 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e25968 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e25969 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b25970 := hb (x (-5) 7)
      have b25971 := hb (x (-4) 6)
      have b25972 := hb (x (-3) 5)
      have b25973 := hb (x (-2) 4)
      have b25974 := hb (x (-1) 11)
      have b25975 := hb (x 0 10)
      have b25976 := hb (x 1 9)
      have b25977 := hb (x 2 8)
      clear * - r25963 e25964 e25965 e25966 e25967 e25968 e25969 b25970 b25971 b25972 b25973 b25974 b25975 b25976 b25977 d22636 d22851 d25371 d25095
      omega
    have d25978 : (x 1 9).toNat = 0 := by
      have r25979 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25980 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e25981 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e25982 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e25983 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e25984 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e25985 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b25986 := hb (x (-5) 7)
      have b25987 := hb (x (-4) 6)
      have b25988 := hb (x (-3) 5)
      have b25989 := hb (x (-2) 4)
      have b25990 := hb (x (-1) 11)
      have b25991 := hb (x 0 10)
      have b25992 := hb (x 1 9)
      have b25993 := hb (x 2 8)
      clear * - r25979 e25980 e25981 e25982 e25983 e25984 e25985 b25986 b25987 b25988 b25989 b25990 b25991 b25992 b25993 d25962 d22636 d22851 d25371 d25095
      omega
    have d25994 : (x (-4) 6).toNat = 0 := by
      have r25995 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25996 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e25997 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e25998 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e25999 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e26000 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e26001 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b26002 := hb (x (-5) 7)
      have b26003 := hb (x (-4) 6)
      have b26004 := hb (x (-3) 5)
      have b26005 := hb (x (-2) 4)
      have b26006 := hb (x (-1) 11)
      have b26007 := hb (x 0 10)
      have b26008 := hb (x 1 9)
      have b26009 := hb (x 2 8)
      clear * - r25995 e25996 e25997 e25998 e25999 e26000 e26001 b26002 b26003 b26004 b26005 b26006 b26007 b26008 b26009 d25962 d25978 d22636 d22851 d25371 d25095
      omega
    have d26010 : (x (-4) 6 && x (-4) 13).toNat = 0 := by
      have r26011 := hand1 (x (-4) 6) (x (-4) 13)
      have b26012 := hb (x (-4) 6)
      have b26013 := hb (x (-4) 6 && x (-4) 13)
      clear * - r26011 b26012 b26013 d25994
      omega
    have d26014 : (x 1 8).toNat = 0 := by
      have r26015 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26016 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e26017 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e26018 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e26019 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e26020 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e26021 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b26022 := hb (x (-6) 7)
      have b26023 := hb (x (-5) 6)
      have b26024 := hb (x (-4) 5)
      have b26025 := hb (x (-3) 4)
      have b26026 := hb (x (-2) 11)
      have b26027 := hb (x (-1) 10)
      have b26028 := hb (x 0 9)
      have b26029 := hb (x 1 8)
      clear * - r26015 e26016 e26017 e26018 e26019 e26020 e26021 b26022 b26023 b26024 b26025 b26026 b26027 b26028 b26029 g2 g0 d25127 d25054 d25526
      omega
    have d26030 : (x 1 1 && x 1 8).toNat = 0 := by
      have r26031 := hand2 (x 1 1) (x 1 8)
      have b26032 := hb (x 1 8)
      have b26033 := hb (x 1 1 && x 1 8)
      clear * - r26031 b26032 b26033 d26014
      omega
    have d26034 : (x (-2) 8).toNat = 0 := by
      have r26035 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26036 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
      have e26037 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
      have e26038 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
      have e26039 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
      have e26040 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
      have e26041 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
      have b26042 := hb (x (-9) 7)
      have b26043 := hb (x (-8) 6)
      have b26044 := hb (x (-7) 5)
      have b26045 := hb (x (-6) 4)
      have b26046 := hb (x (-5) 11)
      have b26047 := hb (x (-4) 10)
      have b26048 := hb (x (-3) 9)
      have b26049 := hb (x (-2) 8)
      clear * - r26035 e26036 e26037 e26038 e26039 e26040 e26041 b26042 b26043 b26044 b26045 b26046 b26047 b26048 b26049 d25103 d25395 d25898 d25481 d25465
      omega
    have d26050 : (x (-8) 6).toNat = 0 := by
      have r26051 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26052 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
      have e26053 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
      have e26054 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
      have e26055 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
      have e26056 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
      have e26057 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
      have b26058 := hb (x (-9) 7)
      have b26059 := hb (x (-8) 6)
      have b26060 := hb (x (-7) 5)
      have b26061 := hb (x (-6) 4)
      have b26062 := hb (x (-5) 11)
      have b26063 := hb (x (-4) 10)
      have b26064 := hb (x (-3) 9)
      have b26065 := hb (x (-2) 8)
      clear * - r26051 e26052 e26053 e26054 e26055 e26056 e26057 b26058 b26059 b26060 b26061 b26062 b26063 b26064 b26065 d26034 d25103 d25395 d25898 d25481 d25465
      omega
    have d26066 : (x (-8) 6 && x (-8) 13).toNat = 0 := by
      have r26067 := hand1 (x (-8) 6) (x (-8) 13)
      have b26068 := hb (x (-8) 6)
      have b26069 := hb (x (-8) 6 && x (-8) 13)
      clear * - r26067 b26068 b26069 d26050
      omega
    have d26070 : (x (-4) 8).toNat = 0 := by
      have r26071 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26072 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
      have e26073 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
      have e26074 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
      have e26075 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
      have e26076 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
      have e26077 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
      have b26078 := hb (x (-11) 7)
      have b26079 := hb (x (-10) 6)
      have b26080 := hb (x (-9) 5)
      have b26081 := hb (x (-8) 4)
      have b26082 := hb (x (-7) 11)
      have b26083 := hb (x (-6) 10)
      have b26084 := hb (x (-5) 9)
      have b26085 := hb (x (-4) 8)
      clear * - r26071 e26072 e26073 e26074 e26075 e26076 e26077 b26078 b26079 b26080 b26081 b26082 b26083 b26084 b26085 d25171 d24989 d25009 d25272 d25295
      omega
    have d26086 : (x (-6) 8).toNat = 0 := by
      have r26087 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26088 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
      have e26089 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
      have e26090 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
      have e26091 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
      have e26092 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
      have e26093 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
      have b26094 := hb (x (-13) 7)
      have b26095 := hb (x (-12) 6)
      have b26096 := hb (x (-11) 5)
      have b26097 := hb (x (-10) 4)
      have b26098 := hb (x (-9) 11)
      have b26099 := hb (x (-8) 10)
      have b26100 := hb (x (-7) 9)
      have b26101 := hb (x (-6) 8)
      clear * - r26087 e26088 e26089 e26090 e26091 e26092 e26093 b26094 b26095 b26096 b26097 b26098 b26099 b26100 b26101 d25886 d25505 d25757 d25570 d25589
      omega
    have d26102 : (x (-10) 8).toNat = 0 := by
      have r26103 : (x (-10) 8).toNat + (x (-11) 1 && x (-11) 9).toNat + (x (-12) 2 && x (-12) 10).toNat + (x (-13) 3 && x (-13) 11).toNat + (x (-14) 4 && x (-14) 12).toNat + (x (-15) 5 && x (-15) 13).toNat + (x (-16) 6 && x (-16) 14).toNat + (x (-17) 7).toNat = 1 := by have q := hd8 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26104 : (x (-11) 1 && x (-11) 9).toNat = (x (-11) 9).toNat := handr _ _ (fun h => hp9 (-11) (h))
      have e26105 : (x (-12) 2 && x (-12) 10).toNat = (x (-12) 10).toNat := handr _ _ (fun h => hp10 (-12) (h))
      have e26106 : (x (-13) 3 && x (-13) 11).toNat = (x (-13) 11).toNat := handr _ _ (fun h => hp11 (-13) (h))
      have e26107 : (x (-14) 4 && x (-14) 12).toNat = (x (-14) 4).toNat := handl _ _ (fun h => hp4 (-14) (h))
      have e26108 : (x (-15) 5 && x (-15) 13).toNat = (x (-15) 5).toNat := handl _ _ (fun h => hp5 (-15) (h))
      have e26109 : (x (-16) 6 && x (-16) 14).toNat = (x (-16) 6).toNat := handl _ _ (fun h => hp6 (-16) (h))
      have b26110 := hb (x (-17) 7)
      have b26111 := hb (x (-16) 6)
      have b26112 := hb (x (-15) 5)
      have b26113 := hb (x (-14) 4)
      have b26114 := hb (x (-13) 11)
      have b26115 := hb (x (-12) 10)
      have b26116 := hb (x (-11) 9)
      have b26117 := hb (x (-10) 8)
      clear * - r26103 e26104 e26105 e26106 e26107 e26108 e26109 b26110 b26111 b26112 b26113 b26114 b26115 b26116 b26117 d25613 d25629 d25749 d25882 d25870
      omega
    have d26118 : (x 4 7).toNat = 1 := by
      have r26119 : 1 ≤ (x 4 7).toNat + (x 3 1 && x 3 8).toNat + (x 2 2 && x 2 9).toNat + (x 1 3 && x 1 10).toNat + (x 0 4 && x 0 11).toNat + (x (-1) 5 && x (-1) 12).toNat + (x (-2) 6 && x (-2) 13).toNat + (x (-3) 7 && x (-3) 14).toNat + (x (-4) 8).toNat := by have q := hcov7 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26120 := hb (x (-4) 8)
      have b26121 := hb (x 4 7)
      have b26122 := hb (x 3 1 && x 3 8)
      have b26123 := hb (x 2 2 && x 2 9)
      have b26124 := hb (x 1 3 && x 1 10)
      have b26125 := hb (x 0 4 && x 0 11)
      have b26126 := hb (x (-1) 5 && x (-1) 12)
      have b26127 := hb (x (-2) 6 && x (-2) 13)
      have b26128 := hb (x (-3) 7 && x (-3) 14)
      clear * - r26119 b26120 b26121 b26122 b26123 b26124 b26125 b26126 b26127 b26128 d25938 d25958 g27 d22745 d22831 d25918 d25062 d26070
      omega
    have d26129 : (x 11 8).toNat = 0 := by
      have r26130 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26131 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
      have e26132 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
      have e26133 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
      have e26134 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
      have e26135 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
      have e26136 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
      have b26137 := hb (x 4 7)
      have b26138 := hb (x 5 6)
      have b26139 := hb (x 6 5)
      have b26140 := hb (x 7 4)
      have b26141 := hb (x 8 11)
      have b26142 := hb (x 9 10)
      have b26143 := hb (x 10 9)
      have b26144 := hb (x 11 8)
      clear * - r26130 e26131 e26132 e26133 e26134 e26135 e26136 b26137 b26138 b26139 b26140 b26141 b26142 b26143 b26144 d26118
      omega
    have d26145 : (x 10 9).toNat = 0 := by
      have r26146 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26147 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
      have e26148 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
      have e26149 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
      have e26150 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
      have e26151 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
      have e26152 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
      have b26153 := hb (x 4 7)
      have b26154 := hb (x 5 6)
      have b26155 := hb (x 6 5)
      have b26156 := hb (x 7 4)
      have b26157 := hb (x 8 11)
      have b26158 := hb (x 9 10)
      have b26159 := hb (x 10 9)
      have b26160 := hb (x 11 8)
      clear * - r26146 e26147 e26148 e26149 e26150 e26151 e26152 b26153 b26154 b26155 b26156 b26157 b26158 b26159 b26160 d26129 d26118
      omega
    have d26161 : (x 9 10).toNat = 0 := by
      have r26162 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26163 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
      have e26164 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
      have e26165 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
      have e26166 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
      have e26167 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
      have e26168 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
      have b26169 := hb (x 4 7)
      have b26170 := hb (x 5 6)
      have b26171 := hb (x 6 5)
      have b26172 := hb (x 7 4)
      have b26173 := hb (x 8 11)
      have b26174 := hb (x 9 10)
      have b26175 := hb (x 10 9)
      have b26176 := hb (x 11 8)
      clear * - r26162 e26163 e26164 e26165 e26166 e26167 e26168 b26169 b26170 b26171 b26172 b26173 b26174 b26175 b26176 d26129 d26145 d26118
      omega
    have d26177 : (x 8 11).toNat = 0 := by
      have r26178 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26179 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
      have e26180 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
      have e26181 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
      have e26182 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
      have e26183 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
      have e26184 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
      have b26185 := hb (x 4 7)
      have b26186 := hb (x 5 6)
      have b26187 := hb (x 6 5)
      have b26188 := hb (x 7 4)
      have b26189 := hb (x 8 11)
      have b26190 := hb (x 9 10)
      have b26191 := hb (x 10 9)
      have b26192 := hb (x 11 8)
      clear * - r26178 e26179 e26180 e26181 e26182 e26183 e26184 b26185 b26186 b26187 b26188 b26189 b26190 b26191 b26192 d26129 d26145 d26161 d26118
      omega
    have d26193 : (x 8 1 && x 8 11).toNat = 0 := by
      have r26194 := hand2 (x 8 1) (x 8 11)
      have b26195 := hb (x 8 11)
      have b26196 := hb (x 8 1 && x 8 11)
      clear * - r26194 b26195 b26196 d26177
      omega
    have d26197 : (x 7 4).toNat = 0 := by
      have r26198 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26199 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
      have e26200 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
      have e26201 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
      have e26202 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
      have e26203 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
      have e26204 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
      have b26205 := hb (x 4 7)
      have b26206 := hb (x 5 6)
      have b26207 := hb (x 6 5)
      have b26208 := hb (x 7 4)
      have b26209 := hb (x 8 11)
      have b26210 := hb (x 9 10)
      have b26211 := hb (x 10 9)
      have b26212 := hb (x 11 8)
      clear * - r26198 e26199 e26200 e26201 e26202 e26203 e26204 b26205 b26206 b26207 b26208 b26209 b26210 b26211 b26212 d26129 d26145 d26161 d26177 d26118
      omega
    have d26213 : (x 7 4 && x 7 14).toNat = 0 := by
      have r26214 := hand1 (x 7 4) (x 7 14)
      have b26215 := hb (x 7 4)
      have b26216 := hb (x 7 4 && x 7 14)
      clear * - r26214 b26215 b26216 d26197
      omega
    have d26217 : (x 6 5).toNat = 0 := by
      have r26218 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26219 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
      have e26220 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
      have e26221 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
      have e26222 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
      have e26223 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
      have e26224 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
      have b26225 := hb (x 4 7)
      have b26226 := hb (x 5 6)
      have b26227 := hb (x 6 5)
      have b26228 := hb (x 7 4)
      have b26229 := hb (x 8 11)
      have b26230 := hb (x 9 10)
      have b26231 := hb (x 10 9)
      have b26232 := hb (x 11 8)
      clear * - r26218 e26219 e26220 e26221 e26222 e26223 e26224 b26225 b26226 b26227 b26228 b26229 b26230 b26231 b26232 d26129 d26145 d26161 d26177 d26197 d26118
      omega
    have d26233 : (x 2 7).toNat = 1 := by
      have r26234 : 1 ≤ (x 2 7).toNat + (x 1 1 && x 1 8).toNat + (x 0 2 && x 0 9).toNat + (x (-1) 3 && x (-1) 10).toNat + (x (-2) 4 && x (-2) 11).toNat + (x (-3) 5 && x (-3) 12).toNat + (x (-4) 6 && x (-4) 13).toNat + (x (-5) 7 && x (-5) 14).toNat + (x (-6) 8).toNat := by have q := hcov7 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26235 := hb (x (-6) 8)
      have b26236 := hb (x 2 7)
      have b26237 := hb (x 1 1 && x 1 8)
      have b26238 := hb (x 0 2 && x 0 9)
      have b26239 := hb (x (-1) 3 && x (-1) 10)
      have b26240 := hb (x (-2) 4 && x (-2) 11)
      have b26241 := hb (x (-3) 5 && x (-3) 12)
      have b26242 := hb (x (-4) 6 && x (-4) 13)
      have b26243 := hb (x (-5) 7 && x (-5) 14)
      clear * - r26234 b26235 b26236 b26237 b26238 b26239 b26240 b26241 b26242 b26243 d26030 d22632 g25 g26 d25099 d26010 d25522 d26086
      omega
    have d26244 : (x 9 8).toNat = 0 := by
      have r26245 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26246 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
      have e26247 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
      have e26248 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
      have e26249 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
      have e26250 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
      have e26251 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
      have b26252 := hb (x 2 7)
      have b26253 := hb (x 3 6)
      have b26254 := hb (x 4 5)
      have b26255 := hb (x 5 4)
      have b26256 := hb (x 6 11)
      have b26257 := hb (x 7 10)
      have b26258 := hb (x 8 9)
      have b26259 := hb (x 9 8)
      clear * - r26245 e26246 e26247 e26248 e26249 e26250 e26251 b26252 b26253 b26254 b26255 b26256 b26257 b26258 b26259 d22661 d26233
      omega
    have d26260 : (x 8 9).toNat = 0 := by
      have r26261 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26262 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
      have e26263 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
      have e26264 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
      have e26265 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
      have e26266 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
      have e26267 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
      have b26268 := hb (x 2 7)
      have b26269 := hb (x 3 6)
      have b26270 := hb (x 4 5)
      have b26271 := hb (x 5 4)
      have b26272 := hb (x 6 11)
      have b26273 := hb (x 7 10)
      have b26274 := hb (x 8 9)
      have b26275 := hb (x 9 8)
      clear * - r26261 e26262 e26263 e26264 e26265 e26266 e26267 b26268 b26269 b26270 b26271 b26272 b26273 b26274 b26275 d26244 d22661 d26233
      omega
    have d26276 : (x 7 10).toNat = 0 := by
      have r26277 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26278 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
      have e26279 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
      have e26280 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
      have e26281 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
      have e26282 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
      have e26283 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
      have b26284 := hb (x 2 7)
      have b26285 := hb (x 3 6)
      have b26286 := hb (x 4 5)
      have b26287 := hb (x 5 4)
      have b26288 := hb (x 6 11)
      have b26289 := hb (x 7 10)
      have b26290 := hb (x 8 9)
      have b26291 := hb (x 9 8)
      clear * - r26277 e26278 e26279 e26280 e26281 e26282 e26283 b26284 b26285 b26286 b26287 b26288 b26289 b26290 b26291 d26244 d26260 d22661 d26233
      omega
    have d26292 : (x 6 11).toNat = 0 := by
      have r26293 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26294 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
      have e26295 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
      have e26296 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
      have e26297 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
      have e26298 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
      have e26299 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
      have b26300 := hb (x 2 7)
      have b26301 := hb (x 3 6)
      have b26302 := hb (x 4 5)
      have b26303 := hb (x 5 4)
      have b26304 := hb (x 6 11)
      have b26305 := hb (x 7 10)
      have b26306 := hb (x 8 9)
      have b26307 := hb (x 9 8)
      clear * - r26293 e26294 e26295 e26296 e26297 e26298 e26299 b26300 b26301 b26302 b26303 b26304 b26305 b26306 b26307 d26244 d26260 d26276 d22661 d26233
      omega
    have d26308 : (x 6 1 && x 6 11).toNat = 0 := by
      have r26309 := hand2 (x 6 1) (x 6 11)
      have b26310 := hb (x 6 11)
      have b26311 := hb (x 6 1 && x 6 11)
      clear * - r26309 b26310 b26311 d26292
      omega
    have d26312 : (x 5 4).toNat = 0 := by
      have r26313 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26314 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
      have e26315 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
      have e26316 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
      have e26317 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
      have e26318 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
      have e26319 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
      have b26320 := hb (x 2 7)
      have b26321 := hb (x 3 6)
      have b26322 := hb (x 4 5)
      have b26323 := hb (x 5 4)
      have b26324 := hb (x 6 11)
      have b26325 := hb (x 7 10)
      have b26326 := hb (x 8 9)
      have b26327 := hb (x 9 8)
      clear * - r26313 e26314 e26315 e26316 e26317 e26318 e26319 b26320 b26321 b26322 b26323 b26324 b26325 b26326 b26327 d26244 d26260 d26276 d26292 d22661 d26233
      omega
    have d26328 : (x 5 4 && x 5 14).toNat = 0 := by
      have r26329 := hand1 (x 5 4) (x 5 14)
      have b26330 := hb (x 5 4)
      have b26331 := hb (x 5 4 && x 5 14)
      clear * - r26329 b26330 b26331 d26312
      omega
    have d26332 : (x 4 5).toNat = 0 := by
      have r26333 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26334 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
      have e26335 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
      have e26336 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
      have e26337 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
      have e26338 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
      have e26339 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
      have b26340 := hb (x 2 7)
      have b26341 := hb (x 3 6)
      have b26342 := hb (x 4 5)
      have b26343 := hb (x 5 4)
      have b26344 := hb (x 6 11)
      have b26345 := hb (x 7 10)
      have b26346 := hb (x 8 9)
      have b26347 := hb (x 9 8)
      clear * - r26333 e26334 e26335 e26336 e26337 e26338 e26339 b26340 b26341 b26342 b26343 b26344 b26345 b26346 b26347 d26244 d26260 d26276 d26292 d26312 d22661 d26233
      omega
    have d26348 : (x (-2) 7).toNat = 1 := by
      have r26349 : 1 ≤ (x (-2) 7).toNat + (x (-3) 1 && x (-3) 8).toNat + (x (-4) 2 && x (-4) 9).toNat + (x (-5) 3 && x (-5) 10).toNat + (x (-6) 4 && x (-6) 11).toNat + (x (-7) 5 && x (-7) 12).toNat + (x (-8) 6 && x (-8) 13).toNat + (x (-9) 7 && x (-9) 14).toNat + (x (-10) 8).toNat := by have q := hcov7 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26350 := hb (x (-10) 8)
      have b26351 := hb (x (-2) 7)
      have b26352 := hb (x (-3) 1 && x (-3) 8)
      have b26353 := hb (x (-4) 2 && x (-4) 9)
      have b26354 := hb (x (-5) 3 && x (-5) 10)
      have b26355 := hb (x (-6) 4 && x (-6) 11)
      have b26356 := hb (x (-7) 5 && x (-7) 12)
      have b26357 := hb (x (-8) 6 && x (-8) 13)
      have b26358 := hb (x (-9) 7 && x (-9) 14)
      clear * - r26349 b26350 b26351 b26352 b26353 b26354 b26355 b26356 b26357 b26358 d25087 d25391 d25143 d25159 d25469 d26066 d25646 d26102
      omega
    have d26359 : (x 5 8).toNat = 0 := by
      have r26360 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26361 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
      have e26362 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
      have e26363 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
      have e26364 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
      have e26365 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
      have e26366 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
      have b26367 := hb (x (-2) 7)
      have b26368 := hb (x (-1) 6)
      have b26369 := hb (x 0 5)
      have b26370 := hb (x 1 4)
      have b26371 := hb (x 2 11)
      have b26372 := hb (x 3 10)
      have b26373 := hb (x 4 9)
      have b26374 := hb (x 5 8)
      clear * - r26360 e26361 e26362 e26363 e26364 e26365 e26366 b26367 b26368 b26369 b26370 b26371 b26372 b26373 b26374 d22689 g7 d25115 d26348
      omega
    have d26375 : (x 5 1 && x 5 8).toNat = 0 := by
      have r26376 := hand2 (x 5 1) (x 5 8)
      have b26377 := hb (x 5 8)
      have b26378 := hb (x 5 1 && x 5 8)
      clear * - r26376 b26377 b26378 d26359
      omega
    have d26379 : (x 4 9).toNat = 0 := by
      have r26380 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26381 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
      have e26382 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
      have e26383 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
      have e26384 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
      have e26385 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
      have e26386 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
      have b26387 := hb (x (-2) 7)
      have b26388 := hb (x (-1) 6)
      have b26389 := hb (x 0 5)
      have b26390 := hb (x 1 4)
      have b26391 := hb (x 2 11)
      have b26392 := hb (x 3 10)
      have b26393 := hb (x 4 9)
      have b26394 := hb (x 5 8)
      clear * - r26380 e26381 e26382 e26383 e26384 e26385 e26386 b26387 b26388 b26389 b26390 b26391 b26392 b26393 b26394 d26359 d22689 g7 d25115 d26348
      omega
    have d26395 : (x 4 2 && x 4 9).toNat = 0 := by
      have r26396 := hand2 (x 4 2) (x 4 9)
      have b26397 := hb (x 4 9)
      have b26398 := hb (x 4 2 && x 4 9)
      clear * - r26396 b26397 b26398 d26379
      omega
    have d26399 : (x 2 11).toNat = 0 := by
      have r26400 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26401 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
      have e26402 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
      have e26403 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
      have e26404 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
      have e26405 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
      have e26406 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
      have b26407 := hb (x (-2) 7)
      have b26408 := hb (x (-1) 6)
      have b26409 := hb (x 0 5)
      have b26410 := hb (x 1 4)
      have b26411 := hb (x 2 11)
      have b26412 := hb (x 3 10)
      have b26413 := hb (x 4 9)
      have b26414 := hb (x 5 8)
      clear * - r26400 e26401 e26402 e26403 e26404 e26405 e26406 b26407 b26408 b26409 b26410 b26411 b26412 b26413 b26414 d26359 d26379 d22689 g7 d25115 d26348
      omega
    have d26415 : (x 2 4 && x 2 11).toNat = 0 := by
      have r26416 := hand2 (x 2 4) (x 2 11)
      have b26417 := hb (x 2 11)
      have b26418 := hb (x 2 4 && x 2 11)
      clear * - r26416 b26417 b26418 d26399
      omega
    have d26419 : (x 6 7).toNat = 1 := by
      have r26420 : 1 ≤ (x 6 7).toNat + (x 5 1 && x 5 8).toNat + (x 4 2 && x 4 9).toNat + (x 3 3 && x 3 10).toNat + (x 2 4 && x 2 11).toNat + (x 1 5 && x 1 12).toNat + (x 0 6 && x 0 13).toNat + (x (-1) 7 && x (-1) 14).toNat + (x (-2) 8).toNat := by have q := hcov7 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26421 := hb (x (-2) 8)
      have b26422 := hb (x 6 7)
      have b26423 := hb (x 5 1 && x 5 8)
      have b26424 := hb (x 4 2 && x 4 9)
      have b26425 := hb (x 3 3 && x 3 10)
      have b26426 := hb (x 2 4 && x 2 11)
      have b26427 := hb (x 1 5 && x 1 12)
      have b26428 := hb (x 0 6 && x 0 13)
      have b26429 := hb (x (-1) 7 && x (-1) 14)
      clear * - r26420 b26421 b26422 b26423 b26424 b26425 b26426 b26427 b26428 b26429 d26375 d26395 d22697 d26415 g28 g29 d22955 d26034
      omega
    have d26430 : (x 13 8).toNat = 0 := by
      have r26431 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26432 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
      have e26433 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
      have e26434 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
      have e26435 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
      have e26436 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
      have e26437 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
      have b26438 := hb (x 6 7)
      have b26439 := hb (x 7 6)
      have b26440 := hb (x 8 5)
      have b26441 := hb (x 9 4)
      have b26442 := hb (x 10 11)
      have b26443 := hb (x 11 10)
      have b26444 := hb (x 12 9)
      have b26445 := hb (x 13 8)
      clear * - r26431 e26432 e26433 e26434 e26435 e26436 e26437 b26438 b26439 b26440 b26441 b26442 b26443 b26444 b26445 d26419
      omega
    have d26446 : (x 12 9).toNat = 0 := by
      have r26447 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26448 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
      have e26449 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
      have e26450 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
      have e26451 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
      have e26452 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
      have e26453 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
      have b26454 := hb (x 6 7)
      have b26455 := hb (x 7 6)
      have b26456 := hb (x 8 5)
      have b26457 := hb (x 9 4)
      have b26458 := hb (x 10 11)
      have b26459 := hb (x 11 10)
      have b26460 := hb (x 12 9)
      have b26461 := hb (x 13 8)
      clear * - r26447 e26448 e26449 e26450 e26451 e26452 e26453 b26454 b26455 b26456 b26457 b26458 b26459 b26460 b26461 d26430 d26419
      omega
    have d26462 : (x 11 10).toNat = 0 := by
      have r26463 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26464 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
      have e26465 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
      have e26466 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
      have e26467 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
      have e26468 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
      have e26469 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
      have b26470 := hb (x 6 7)
      have b26471 := hb (x 7 6)
      have b26472 := hb (x 8 5)
      have b26473 := hb (x 9 4)
      have b26474 := hb (x 10 11)
      have b26475 := hb (x 11 10)
      have b26476 := hb (x 12 9)
      have b26477 := hb (x 13 8)
      clear * - r26463 e26464 e26465 e26466 e26467 e26468 e26469 b26470 b26471 b26472 b26473 b26474 b26475 b26476 b26477 d26430 d26446 d26419
      omega
    have d26478 : (x 10 11).toNat = 0 := by
      have r26479 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26480 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
      have e26481 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
      have e26482 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
      have e26483 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
      have e26484 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
      have e26485 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
      have b26486 := hb (x 6 7)
      have b26487 := hb (x 7 6)
      have b26488 := hb (x 8 5)
      have b26489 := hb (x 9 4)
      have b26490 := hb (x 10 11)
      have b26491 := hb (x 11 10)
      have b26492 := hb (x 12 9)
      have b26493 := hb (x 13 8)
      clear * - r26479 e26480 e26481 e26482 e26483 e26484 e26485 b26486 b26487 b26488 b26489 b26490 b26491 b26492 b26493 d26430 d26446 d26462 d26419
      omega
    have d26494 : (x 10 1 && x 10 11).toNat = 0 := by
      have r26495 := hand2 (x 10 1) (x 10 11)
      have b26496 := hb (x 10 11)
      have b26497 := hb (x 10 1 && x 10 11)
      clear * - r26495 b26496 b26497 d26478
      omega
    have d26498 : (x 0 5).toNat = 0 := by
      have r26499 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26500 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
      have e26501 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
      have e26502 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
      have e26503 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
      have e26504 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
      have e26505 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
      have b26506 := hb (x (-2) 7)
      have b26507 := hb (x (-1) 6)
      have b26508 := hb (x 0 5)
      have b26509 := hb (x 1 4)
      have b26510 := hb (x 2 11)
      have b26511 := hb (x 3 10)
      have b26512 := hb (x 4 9)
      have b26513 := hb (x 5 8)
      clear * - r26499 e26500 e26501 e26502 e26503 e26504 e26505 b26506 b26507 b26508 b26509 b26510 b26511 b26512 b26513 d26359 d26379 d22689 d26399 g7 d25115 d26348
      omega
    have d26514 : (x 0 5 && x 0 14).toNat = 0 := by
      have r26515 := hand1 (x 0 5) (x 0 14)
      have b26516 := hb (x 0 5)
      have b26517 := hb (x 0 5 && x 0 14)
      clear * - r26515 b26516 b26517 d26498
      omega
    have d26518 : (x 2 3 && x 2 12).toNat = 1 := by
      have r26519 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26520 := hb (x (-1) 6)
      have b26521 := hb (x 5 9)
      have b26522 := hb (x 4 1 && x 4 10)
      have b26523 := hb (x 3 2 && x 3 11)
      have b26524 := hb (x 2 3 && x 2 12)
      have b26525 := hb (x 1 4 && x 1 13)
      have b26526 := hb (x 0 5 && x 0 14)
      clear * - r26519 b26520 b26521 b26522 b26523 b26524 b26525 b26526 d22875 d22911 d22685 g41 d26514 d25115
      omega
    have d26527 : (x 2 3).toNat = 1 := by
      have r26528 := hand1 (x 2 3) (x 2 12)
      have b26529 := hb (x 2 3)
      have b26530 := hb (x 2 3 && x 2 12)
      clear * - r26528 b26529 b26530 d26518
      omega
    have d26531 : (x 5 12).toNat = 0 := by
      have r26532 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26533 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e26534 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b26535 := hb (x 2 3)
      have b26536 := hb (x 3 2)
      have b26537 := hb (x 4 13)
      have b26538 := hb (x 5 12)
      clear * - r26532 e26533 e26534 b26535 b26536 b26537 b26538 d22677 d26527
      omega
    have d26539 : (x 5 2 && x 5 12).toNat = 0 := by
      have r26540 := hand2 (x 5 2) (x 5 12)
      have b26541 := hb (x 5 12)
      have b26542 := hb (x 5 2 && x 5 12)
      clear * - r26540 b26541 b26542 d26531
      omega
    have d26543 : (x 4 3 && x 4 13).toNat = 1 := by
      have r26544 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26545 := hb (x 2 5)
      have b26546 := hb (x 7 10)
      have b26547 := hb (x 6 1 && x 6 11)
      have b26548 := hb (x 5 2 && x 5 12)
      have b26549 := hb (x 4 3 && x 4 13)
      have b26550 := hb (x 3 4 && x 3 14)
      clear * - r26544 b26545 b26546 b26547 b26548 b26549 b26550 d26276 d26308 d26539 g52 g11
      omega
    have d26551 : (x 4 13).toNat = 1 := by
      have r26552 := hand2 (x 4 3) (x 4 13)
      have b26553 := hb (x 4 13)
      have b26554 := hb (x 4 3 && x 4 13)
      clear * - r26552 b26553 b26554 d26543
      omega
    have d26555 : (x 4 1).toNat = 1 := by
      have r26556 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
      have b26557 := hb (x 4 1)
      have b26558 := hb (x 4 13)
      clear * - r26556 b26557 b26558 d26551
      omega
    have d26559 : (x 5 14).toNat = 0 := by
      have r26560 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26561 := hb (x 4 1)
      have b26562 := hb (x 5 14)
      clear * - r26560 b26561 b26562 d26555
      omega
    have d26563 : (x 5 2).toNat = 0 := by
      have r26564 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
      have b26565 := hb (x 5 2)
      have b26566 := hb (x 5 14)
      clear * - r26564 b26565 b26566 d26559
      omega
    have d26567 : (x 4 3).toNat = 1 := by
      have r26568 := hand1 (x 4 3) (x 4 13)
      have b26569 := hb (x 4 3)
      have b26570 := hb (x 4 3 && x 4 13)
      clear * - r26568 b26569 b26570 d26543
      omega
    have d26571 : (x 7 12).toNat = 0 := by
      have r26572 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26573 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
      have e26574 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
      have b26575 := hb (x 4 3)
      have b26576 := hb (x 5 2)
      have b26577 := hb (x 6 13)
      have b26578 := hb (x 7 12)
      clear * - r26572 e26573 e26574 b26575 b26576 b26577 b26578 d26563 d26567
      omega
    have d26579 : (x 7 2 && x 7 12).toNat = 0 := by
      have r26580 := hand2 (x 7 2) (x 7 12)
      have b26581 := hb (x 7 12)
      have b26582 := hb (x 7 2 && x 7 12)
      clear * - r26580 b26581 b26582 d26571
      omega
    have d26583 : (x 6 3 && x 6 13).toNat = 1 := by
      have r26584 : 1 ≤ (x 9 10).toNat + (x 8 1 && x 8 11).toNat + (x 7 2 && x 7 12).toNat + (x 6 3 && x 6 13).toNat + (x 5 4 && x 5 14).toNat + (x 4 5).toNat := by have q := hcov10 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26585 := hb (x 4 5)
      have b26586 := hb (x 9 10)
      have b26587 := hb (x 8 1 && x 8 11)
      have b26588 := hb (x 7 2 && x 7 12)
      have b26589 := hb (x 6 3 && x 6 13)
      have b26590 := hb (x 5 4 && x 5 14)
      clear * - r26584 b26585 b26586 b26587 b26588 b26589 b26590 d26161 d26193 d26579 d26328 d26332
      omega
    have d26591 : (x 6 13).toNat = 1 := by
      have r26592 := hand2 (x 6 3) (x 6 13)
      have b26593 := hb (x 6 13)
      have b26594 := hb (x 6 3 && x 6 13)
      clear * - r26592 b26593 b26594 d26583
      omega
    have d26595 : (x 6 1).toNat = 1 := by
      have r26596 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
      have b26597 := hb (x 6 1)
      have b26598 := hb (x 6 13)
      clear * - r26596 b26597 b26598 d26591
      omega
    have d26599 : (x 7 14).toNat = 0 := by
      have r26600 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26601 := hb (x 6 1)
      have b26602 := hb (x 7 14)
      clear * - r26600 b26601 b26602 d26595
      omega
    have d26603 : (x 7 2).toNat = 0 := by
      have r26604 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
      have b26605 := hb (x 7 2)
      have b26606 := hb (x 7 14)
      clear * - r26604 b26605 b26606 d26599
      omega
    have d26607 : (x 6 3).toNat = 1 := by
      have r26608 := hand1 (x 6 3) (x 6 13)
      have b26609 := hb (x 6 3)
      have b26610 := hb (x 6 3 && x 6 13)
      clear * - r26608 b26609 b26610 d26583
      omega
    have d26611 : (x 9 12).toNat = 0 := by
      have r26612 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26613 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
      have e26614 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
      have b26615 := hb (x 6 3)
      have b26616 := hb (x 7 2)
      have b26617 := hb (x 8 13)
      have b26618 := hb (x 9 12)
      clear * - r26612 e26613 e26614 b26615 b26616 b26617 b26618 d26603 d26607
      omega
    have d26619 : (x 9 2 && x 9 12).toNat = 0 := by
      have r26620 := hand2 (x 9 2) (x 9 12)
      have b26621 := hb (x 9 12)
      have b26622 := hb (x 9 2 && x 9 12)
      clear * - r26620 b26621 b26622 d26611
      omega
    have d26623 : (x 8 3 && x 8 13).toNat = 1 := by
      have r26624 : 1 ≤ (x 11 10).toNat + (x 10 1 && x 10 11).toNat + (x 9 2 && x 9 12).toNat + (x 8 3 && x 8 13).toNat + (x 7 4 && x 7 14).toNat + (x 6 5).toNat := by have q := hcov10 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26625 := hb (x 6 5)
      have b26626 := hb (x 11 10)
      have b26627 := hb (x 10 1 && x 10 11)
      have b26628 := hb (x 9 2 && x 9 12)
      have b26629 := hb (x 8 3 && x 8 13)
      have b26630 := hb (x 7 4 && x 7 14)
      clear * - r26624 b26625 b26626 b26627 b26628 b26629 b26630 d26462 d26494 d26619 d26213 d26217
      omega
    have d26631 : (x 8 13).toNat = 1 := by
      have r26632 := hand2 (x 8 3) (x 8 13)
      have b26633 := hb (x 8 13)
      have b26634 := hb (x 8 3 && x 8 13)
      clear * - r26632 b26633 b26634 d26623
      omega
    have r26635 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26636 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e26637 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b26638 := hb (x 6 3)
    have b26639 := hb (x 7 2)
    have b26640 := hb (x 8 13)
    have b26641 := hb (x 9 12)
    linarith only [r26635, e26636, e26637, b26638, b26639, b26640, b26641, d26611, d26631, d26603, d26607]

theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b110 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-2) 11).toNat = 0)
    (g1 : (x (-1) 2).toNat = 0)
    (g2 : (x (-1) 10).toNat = 0)
    (g3 : (x 0 2).toNat = 0)
    (g4 : (x 0 6).toNat = 0)
    (g5 : (x 0 13).toNat = 1)
    (g6 : (x 1 2).toNat = 0)
    (g7 : (x 1 4).toNat = 0)
    (g8 : (x 1 6).toNat = 0)
    (g9 : (x 1 10).toNat = 0)
    (g10 : (x 1 12).toNat = 0)
    (g11 : (x 2 5).toNat = 0)
    (g12 : (x 4 11).toNat = 0)
    (g13 : (x 5 10).toNat = 0)
    (g14 : (x 6 9).toNat = 0)
    (g15 : (x 1 4 && x 1 8).toNat = 0)
    (g16 : (x (-1) 6 && x (-1) 10).toNat = 0)
    (g17 : (x (-2) 7 && x (-2) 11).toNat = 0)
    (g18 : (x 1 8 && x 1 12).toNat = 0)
    (g19 : (x 0 6 && x 0 12).toNat = 0)
    (g20 : (x 7 2 && x 7 8).toNat = 0)
    (g21 : (x 6 3 && x 6 9).toNat = 0)
    (g22 : (x 5 4 && x 5 10).toNat = 0)
    (g23 : (x 4 5 && x 4 11).toNat = 0)
    (g24 : (x 1 8 && x 1 14).toNat = 0)
    (g25 : (x (-1) 3 && x (-1) 10).toNat = 0)
    (g26 : (x (-2) 4 && x (-2) 11).toNat = 0)
    (g27 : (x 1 3 && x 1 10).toNat = 0)
    (g28 : (x 1 5 && x 1 12).toNat = 0)
    (g29 : (x 0 6 && x 0 13).toNat = 0)
    (g30 : (x 7 1 && x 7 8).toNat = 0)
    (g31 : (x 6 2 && x 6 9).toNat = 0)
    (g32 : (x 5 3 && x 5 10).toNat = 0)
    (g33 : (x 4 4 && x 4 11).toNat = 0)
    (g34 : (x 1 7 && x 1 14).toNat = 0)
    (g35 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g36 : (x (-2) 2 && x (-2) 11).toNat = 0)
    (g37 : (x (-1) 2 && x (-1) 11).toNat = 0)
    (g38 : (x (-2) 3 && x (-2) 12).toNat = 0)
    (g39 : (x 1 2 && x 1 11).toNat = 0)
    (g40 : (x 1 3 && x 1 12).toNat = 0)
    (g41 : (x 1 4 && x 1 13).toNat = 0)
    (g42 : (x 5 1 && x 5 10).toNat = 0)
    (g43 : (x 4 2 && x 4 11).toNat = 0)
    (g44 : (x 1 5 && x 1 14).toNat = 0)
    (g45 : (x 3 4 && x 3 13).toNat = 0)
    (g46 : (x 2 5 && x 2 14).toNat = 0)
    (g47 : (x (-1) 2 && x (-1) 12).toNat = 0)
    (g48 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g49 : (x 1 2 && x 1 12).toNat = 0)
    (g50 : (x 4 1 && x 4 11).toNat = 0)
    (g51 : (x 1 4 && x 1 14).toNat = 0)
    (g52 : (x 3 4 && x 3 14).toNat = 0)
    (g53 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g54 : (x (-2) 3 && x (-2) 14).toNat = 0)
    (g55 : (x 1 1 && x 1 12).toNat = 0)
    (g56 : (x 1 3 && x 1 14).toNat = 0)
    (g57 : (x 1 1 && x 1 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b110_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57
