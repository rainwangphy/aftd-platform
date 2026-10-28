import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b111

Topic: combinatorics   Node: 1c06e375f195

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_six_iff_seven_core: under the layer-free tight-cover constraints for k = 15 and 16 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b111_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 2).toNat = 1)
    (g1 : (x 0 6).toNat = 0)
    (g2 : (x 1 2).toNat = 0)
    (g3 : (x 1 14).toNat = 0)
    (g4 : (x 3 4).toNat = 0)
    (g5 : (x 4 11).toNat = 0)
    (g6 : (x 5 10).toNat = 0)
    (g7 : (x 6 9).toNat = 0)
    (g8 : (x 7 8).toNat = 0)
    (g9 : (x 0 6 && x 0 10).toNat = 0)
    (g10 : (x 0 6 && x 0 12).toNat = 0)
    (g11 : (x 1 1 && x 1 10).toNat = 0)
    (g12 : (x 5 1 && x 5 10).toNat = 0)
    (g13 : (x 4 2 && x 4 11).toNat = 0)
    (g14 : (x 1 5 && x 1 14).toNat = 0)
    (g15 : (x 1 3 && x 1 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d26643 : (x 0 14).toNat = 1 := by
    have r26644 : (x 0 2).toNat ≤ (x 0 14).toNat := himp _ _ (hp2 0)
    have b26645 := hb (x 0 2)
    have b26646 := hb (x 0 14)
    clear * - r26644 b26645 b26646 g0
    omega
  have d26647 : (x (-1) 1).toNat = 0 := by
    have r26648 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26649 := hb (x (-1) 1)
    have b26650 := hb (x 0 14)
    clear * - r26648 b26649 b26650 d26643
    omega
  have d26651 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
    have r26652 := hand1 (x (-1) 1) (x (-1) 12)
    have b26653 := hb (x (-1) 1)
    have b26654 := hb (x (-1) 1 && x (-1) 12)
    clear * - r26652 b26653 b26654 d26647
    omega
  have d26655 : (x (-1) 13).toNat = 0 := by
    have r26656 : (x (-1) 13).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp13 (-1))
    have b26657 := hb (x (-1) 1)
    have b26658 := hb (x (-1) 13)
    clear * - r26656 b26657 b26658 d26647
    omega
  have d26659 : (x (-1) 7 && x (-1) 13).toNat = 0 := by
    have r26660 := hand2 (x (-1) 7) (x (-1) 13)
    have b26661 := hb (x (-1) 13)
    have b26662 := hb (x (-1) 7 && x (-1) 13)
    clear * - r26660 b26661 b26662 d26655
    omega
  have d26663 : (x (-1) 9 && x (-1) 13).toNat = 0 := by
    have r26664 := hand2 (x (-1) 9) (x (-1) 13)
    have b26665 := hb (x (-1) 13)
    have b26666 := hb (x (-1) 9 && x (-1) 13)
    clear * - r26664 b26665 b26666 d26655
    omega
  have d26667 : (x (-1) 5).toNat = 0 := by
    have r26668 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
    have b26669 := hb (x (-1) 5)
    have b26670 := hb (x (-1) 13)
    clear * - r26668 b26669 b26670 d26655
    omega
  have d26671 : (x (-1) 9).toNat = 0 := by
    have r26672 : (x (-1) 9).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp9 (-1))
    have b26673 := hb (x (-1) 1)
    have b26674 := hb (x (-1) 9)
    clear * - r26672 b26673 b26674 d26647
    omega
  have d26675 : (x 2 12).toNat = 0 := by
    have r26676 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26677 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e26678 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b26679 := hb (x (-1) 3)
    have b26680 := hb (x 0 2)
    have b26681 := hb (x 1 13)
    have b26682 := hb (x 2 12)
    clear * - r26676 e26677 e26678 b26679 b26680 b26681 b26682 g0
    omega
  have d26683 : (x 2 2 && x 2 12).toNat = 0 := by
    have r26684 := hand2 (x 2 2) (x 2 12)
    have b26685 := hb (x 2 12)
    have b26686 := hb (x 2 2 && x 2 12)
    clear * - r26684 b26685 b26686 d26675
    omega
  have d26687 : (x 2 8 && x 2 12).toNat = 0 := by
    have r26688 := hand2 (x 2 8) (x 2 12)
    have b26689 := hb (x 2 12)
    have b26690 := hb (x 2 8 && x 2 12)
    clear * - r26688 b26689 b26690 d26675
    omega
  have d26691 : (x 2 4).toNat = 0 := by
    have r26692 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
    have b26693 := hb (x 2 4)
    have b26694 := hb (x 2 12)
    clear * - r26692 b26693 b26694 d26675
    omega
  have d26695 : (x 2 4 && x 2 13).toNat = 0 := by
    have r26696 := hand1 (x 2 4) (x 2 13)
    have b26697 := hb (x 2 4)
    have b26698 := hb (x 2 4 && x 2 13)
    clear * - r26696 b26697 b26698 d26691
    omega
  have d26699 : (x 2 4 && x 2 10).toNat = 0 := by
    have r26700 := hand1 (x 2 4) (x 2 10)
    have b26701 := hb (x 2 4)
    have b26702 := hb (x 2 4 && x 2 10)
    clear * - r26700 b26701 b26702 d26691
    omega
  have d26703 : (x 2 4 && x 2 8).toNat = 0 := by
    have r26704 := hand1 (x 2 4) (x 2 8)
    have b26705 := hb (x 2 4)
    have b26706 := hb (x 2 4 && x 2 8)
    clear * - r26704 b26705 b26706 d26691
    omega
  have d26707 : (x 1 13).toNat = 0 := by
    have r26708 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26709 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e26710 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b26711 := hb (x (-1) 3)
    have b26712 := hb (x 0 2)
    have b26713 := hb (x 1 13)
    have b26714 := hb (x 2 12)
    clear * - r26708 e26709 e26710 b26711 b26712 b26713 b26714 d26675 g0
    omega
  have d26715 : (x 1 3 && x 1 13).toNat = 0 := by
    have r26716 := hand2 (x 1 3) (x 1 13)
    have b26717 := hb (x 1 13)
    have b26718 := hb (x 1 3 && x 1 13)
    clear * - r26716 b26717 b26718 d26707
    omega
  have d26719 : (x 1 9 && x 1 13).toNat = 0 := by
    have r26720 := hand2 (x 1 9) (x 1 13)
    have b26721 := hb (x 1 13)
    have b26722 := hb (x 1 9 && x 1 13)
    clear * - r26720 b26721 b26722 d26707
    omega
  have d26723 : (x 1 5).toNat = 0 := by
    have r26724 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
    have b26725 := hb (x 1 5)
    have b26726 := hb (x 1 13)
    clear * - r26724 b26725 b26726 d26707
    omega
  have d26727 : (x 1 5 && x 1 11).toNat = 0 := by
    have r26728 := hand1 (x 1 5) (x 1 11)
    have b26729 := hb (x 1 5)
    have b26730 := hb (x 1 5 && x 1 11)
    clear * - r26728 b26729 b26730 d26723
    omega
  have d26731 : (x 1 5 && x 1 9).toNat = 0 := by
    have r26732 := hand1 (x 1 5) (x 1 9)
    have b26733 := hb (x 1 5)
    have b26734 := hb (x 1 5 && x 1 9)
    clear * - r26732 b26733 b26734 d26723
    omega
  have d26735 : (x (-1) 3).toNat = 0 := by
    have r26736 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26737 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e26738 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b26739 := hb (x (-1) 3)
    have b26740 := hb (x 0 2)
    have b26741 := hb (x 1 13)
    have b26742 := hb (x 2 12)
    clear * - r26736 e26737 e26738 b26739 b26740 b26741 b26742 d26675 d26707 g0
    omega
  have d26743 : (x (-1) 3 && x (-1) 12).toNat = 0 := by
    have r26744 := hand1 (x (-1) 3) (x (-1) 12)
    have b26745 := hb (x (-1) 3)
    have b26746 := hb (x (-1) 3 && x (-1) 12)
    clear * - r26744 b26745 b26746 d26735
    omega
  have d26747 : (x (-1) 11).toNat = 0 := by
    have r26748 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
    have b26749 := hb (x (-1) 3)
    have b26750 := hb (x (-1) 11)
    clear * - r26748 b26749 b26750 d26735
    omega
  have d26751 : (x (-1) 7 && x (-1) 11).toNat = 0 := by
    have r26752 := hand2 (x (-1) 7) (x (-1) 11)
    have b26753 := hb (x (-1) 11)
    have b26754 := hb (x (-1) 7 && x (-1) 11)
    clear * - r26752 b26753 b26754 d26747
    omega
  have d26755 : (x 3 3 && x 3 12).toNat = 1 := by
    have r26756 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26757 := hb (x 0 6)
    have b26758 := hb (x 6 9)
    have b26759 := hb (x 5 1 && x 5 10)
    have b26760 := hb (x 4 2 && x 4 11)
    have b26761 := hb (x 3 3 && x 3 12)
    have b26762 := hb (x 2 4 && x 2 13)
    have b26763 := hb (x 1 5 && x 1 14)
    clear * - r26756 b26757 b26758 b26759 b26760 b26761 b26762 b26763 g7 g12 g13 d26695 g14 g1
    omega
  have d26764 : (x 3 12).toNat = 1 := by
    have r26765 := hand2 (x 3 3) (x 3 12)
    have b26766 := hb (x 3 12)
    have b26767 := hb (x 3 3 && x 3 12)
    clear * - r26765 b26766 b26767 d26755
    omega
  have d26768 : (x 2 13).toNat = 0 := by
    have r26769 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26770 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e26771 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b26772 := hb (x 0 3)
    have b26773 := hb (x 1 2)
    have b26774 := hb (x 2 13)
    have b26775 := hb (x 3 12)
    clear * - r26769 e26770 e26771 b26772 b26773 b26774 b26775 d26764 g2
    omega
  have d26776 : (x 2 2 && x 2 13).toNat = 0 := by
    have r26777 := hand2 (x 2 2) (x 2 13)
    have b26778 := hb (x 2 13)
    have b26779 := hb (x 2 2 && x 2 13)
    clear * - r26777 b26778 b26779 d26768
    omega
  have d26780 : (x 0 3).toNat = 0 := by
    have r26781 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26782 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e26783 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b26784 := hb (x 0 3)
    have b26785 := hb (x 1 2)
    have b26786 := hb (x 2 13)
    have b26787 := hb (x 3 12)
    clear * - r26781 e26782 e26783 b26784 b26785 b26786 b26787 d26764 d26768 g2
    omega
  have d26788 : (x 0 11).toNat = 0 := by
    have r26789 : (x 0 11).toNat ≤ (x 0 3).toNat := himp _ _ (hp11 0)
    have b26790 := hb (x 0 3)
    have b26791 := hb (x 0 11)
    clear * - r26789 b26790 b26791 d26780
    omega
  have d26792 : (x 0 2 && x 0 11).toNat = 0 := by
    have r26793 := hand2 (x 0 2) (x 0 11)
    have b26794 := hb (x 0 11)
    have b26795 := hb (x 0 2 && x 0 11)
    clear * - r26793 b26794 b26795 d26788
    omega
  have d26796 : (x 3 3).toNat = 1 := by
    have r26797 := hand1 (x 3 3) (x 3 12)
    have b26798 := hb (x 3 3)
    have b26799 := hb (x 3 3 && x 3 12)
    clear * - r26797 b26798 b26799 d26755
    omega
  have d26800 : (x 6 12).toNat = 0 := by
    have r26801 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26802 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e26803 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b26804 := hb (x 3 3)
    have b26805 := hb (x 4 2)
    have b26806 := hb (x 5 13)
    have b26807 := hb (x 6 12)
    clear * - r26801 e26802 e26803 b26804 b26805 b26806 b26807 d26796
    omega
  have d26808 : (x 6 1 && x 6 12).toNat = 0 := by
    have r26809 := hand2 (x 6 1) (x 6 12)
    have b26810 := hb (x 6 12)
    have b26811 := hb (x 6 1 && x 6 12)
    clear * - r26809 b26810 b26811 d26800
    omega
  have d26812 : (x 6 4).toNat = 0 := by
    have r26813 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
    have b26814 := hb (x 6 4)
    have b26815 := hb (x 6 12)
    clear * - r26813 b26814 b26815 d26800
    omega
  have d26816 : (x 6 4 && x 6 13).toNat = 0 := by
    have r26817 := hand1 (x 6 4) (x 6 13)
    have b26818 := hb (x 6 4)
    have b26819 := hb (x 6 4 && x 6 13)
    clear * - r26817 b26818 b26819 d26812
    omega
  have d26820 : (x 6 4 && x 6 8).toNat = 0 := by
    have r26821 := hand1 (x 6 4) (x 6 8)
    have b26822 := hb (x 6 4)
    have b26823 := hb (x 6 4 && x 6 8)
    clear * - r26821 b26822 b26823 d26812
    omega
  have d26824 : (x 5 13).toNat = 0 := by
    have r26825 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26826 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e26827 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b26828 := hb (x 3 3)
    have b26829 := hb (x 4 2)
    have b26830 := hb (x 5 13)
    have b26831 := hb (x 6 12)
    clear * - r26825 e26826 e26827 b26828 b26829 b26830 b26831 d26800 d26796
    omega
  have d26832 : (x 5 2 && x 5 13).toNat = 0 := by
    have r26833 := hand2 (x 5 2) (x 5 13)
    have b26834 := hb (x 5 13)
    have b26835 := hb (x 5 2 && x 5 13)
    clear * - r26833 b26834 b26835 d26824
    omega
  have d26836 : (x 5 5).toNat = 0 := by
    have r26837 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
    have b26838 := hb (x 5 5)
    have b26839 := hb (x 5 13)
    clear * - r26837 b26838 b26839 d26824
    omega
  have d26840 : (x 5 5 && x 5 14).toNat = 0 := by
    have r26841 := hand1 (x 5 5) (x 5 14)
    have b26842 := hb (x 5 5)
    have b26843 := hb (x 5 5 && x 5 14)
    clear * - r26841 b26842 b26843 d26836
    omega
  have d26844 : (x 5 5 && x 5 9).toNat = 0 := by
    have r26845 := hand1 (x 5 5) (x 5 9)
    have b26846 := hb (x 5 5)
    have b26847 := hb (x 5 5 && x 5 9)
    clear * - r26845 b26846 b26847 d26836
    omega
  have d26848 : (x 4 2).toNat = 0 := by
    have r26849 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26850 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e26851 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b26852 := hb (x 3 3)
    have b26853 := hb (x 4 2)
    have b26854 := hb (x 5 13)
    have b26855 := hb (x 6 12)
    clear * - r26849 e26850 e26851 b26852 b26853 b26854 b26855 d26800 d26824 d26796
    omega
  have d26856 : (x 4 2 && x 4 8).toNat = 0 := by
    have r26857 := hand1 (x 4 2) (x 4 8)
    have b26858 := hb (x 4 2)
    have b26859 := hb (x 4 2 && x 4 8)
    clear * - r26857 b26858 b26859 d26848
    omega
  have d26860 : (x 4 2 && x 4 6).toNat = 0 := by
    have r26861 := hand1 (x 4 2) (x 4 6)
    have b26862 := hb (x 4 2)
    have b26863 := hb (x 4 2 && x 4 6)
    clear * - r26861 b26862 b26863 d26848
    omega
  have d26864 : (x 4 10).toNat = 0 := by
    have r26865 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
    have b26866 := hb (x 4 2)
    have b26867 := hb (x 4 10)
    clear * - r26865 b26866 b26867 d26848
    omega
  have d26868 : (x 4 6 && x 4 10).toNat = 0 := by
    have r26869 := hand2 (x 4 6) (x 4 10)
    have b26870 := hb (x 4 10)
    have b26871 := hb (x 4 6 && x 4 10)
    clear * - r26869 b26870 b26871 d26864
    omega
  cases h26872 : x 0 4
  · have f26873 : (x 0 4).toNat = 0 := by rw [h26872]; rfl
    have d26874 : (x 0 4 && x 0 14).toNat = 0 := by
      have r26875 := hand1 (x 0 4) (x 0 14)
      have b26876 := hb (x 0 4)
      have b26877 := hb (x 0 4 && x 0 14)
      clear * - r26875 b26876 b26877 f26873
      omega
    have d26878 : (x 3 1 && x 3 12).toNat = 1 := by
      have r26879 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26880 := hb (x 0 4)
      have b26881 := hb (x 4 11)
      have b26882 := hb (x 3 1 && x 3 12)
      have b26883 := hb (x 2 2 && x 2 13)
      have b26884 := hb (x 1 3 && x 1 14)
      clear * - r26879 b26880 b26881 b26882 b26883 b26884 g5 d26776 g15 f26873
      omega
    have d26885 : (x 3 1).toNat = 1 := by
      have r26886 := hand1 (x 3 1) (x 3 12)
      have b26887 := hb (x 3 1)
      have b26888 := hb (x 3 1 && x 3 12)
      clear * - r26886 b26887 b26888 d26878
      omega
    have d26889 : (x 4 14).toNat = 0 := by
      have r26890 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26891 := hb (x 3 1)
      have b26892 := hb (x 4 14)
      clear * - r26890 b26891 b26892 d26885
      omega
    have d26893 : (x 4 1 && x 4 14).toNat = 0 := by
      have r26894 := hand2 (x 4 1) (x 4 14)
      have b26895 := hb (x 4 14)
      have b26896 := hb (x 4 1 && x 4 14)
      clear * - r26894 b26895 b26896 d26889
      omega
    have d26897 : (x 3 2).toNat = 1 := by
      have r26898 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26899 := hb (x 3 2)
      have b26900 := hb (x 5 13)
      have b26901 := hb (x 4 1 && x 4 14)
      clear * - r26898 b26899 b26900 b26901 d26824 d26893
      omega
    have d26902 : (x 3 14).toNat = 1 := by
      have r26903 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
      have b26904 := hb (x 3 2)
      have b26905 := hb (x 3 14)
      clear * - r26903 b26904 b26905 d26897
      omega
    have d26906 : (x 2 1).toNat = 0 := by
      have r26907 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26908 := hb (x 2 1)
      have b26909 := hb (x 3 14)
      clear * - r26907 b26908 b26909 d26902
      omega
    have d26910 : (x 2 9).toNat = 0 := by
      have r26911 : (x 2 9).toNat ≤ (x 2 1).toNat := himp _ _ (hp9 2)
      have b26912 := hb (x 2 1)
      have b26913 := hb (x 2 9)
      clear * - r26911 b26912 b26913 d26906
      omega
    have d26914 : (x 4 3 && x 4 14).toNat = 0 := by
      have r26915 := hand2 (x 4 3) (x 4 14)
      have b26916 := hb (x 4 14)
      have b26917 := hb (x 4 3 && x 4 14)
      clear * - r26915 b26916 b26917 d26889
      omega
    have d26918 : (x 7 11).toNat = 1 := by
      have r26919 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26920 := hb (x 3 4)
      have b26921 := hb (x 7 11)
      have b26922 := hb (x 6 1 && x 6 12)
      have b26923 := hb (x 5 2 && x 5 13)
      have b26924 := hb (x 4 3 && x 4 14)
      clear * - r26919 b26920 b26921 b26922 b26923 b26924 d26808 d26832 d26914 g4
      omega
    have d26925 : (x 7 3).toNat = 1 := by
      have r26926 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
      have b26927 := hb (x 7 3)
      have b26928 := hb (x 7 11)
      clear * - r26926 b26927 b26928 d26918
      omega
    have d26929 : (x 10 12).toNat = 0 := by
      have r26930 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26931 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e26932 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b26933 := hb (x 7 3)
      have b26934 := hb (x 8 2)
      have b26935 := hb (x 9 13)
      have b26936 := hb (x 10 12)
      clear * - r26930 e26931 e26932 b26933 b26934 b26935 b26936 d26925
      omega
    have d26937 : (x 10 4).toNat = 0 := by
      have r26938 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
      have b26939 := hb (x 10 4)
      have b26940 := hb (x 10 12)
      clear * - r26938 b26939 b26940 d26929
      omega
    have d26941 : (x 10 4 && x 10 13).toNat = 0 := by
      have r26942 := hand1 (x 10 4) (x 10 13)
      have b26943 := hb (x 10 4)
      have b26944 := hb (x 10 4 && x 10 13)
      clear * - r26942 b26943 b26944 d26937
      omega
    have d26945 : (x 9 13).toNat = 0 := by
      have r26946 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26947 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e26948 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b26949 := hb (x 7 3)
      have b26950 := hb (x 8 2)
      have b26951 := hb (x 9 13)
      have b26952 := hb (x 10 12)
      clear * - r26946 e26947 e26948 b26949 b26950 b26951 b26952 d26929 d26925
      omega
    have d26953 : (x 9 5).toNat = 0 := by
      have r26954 : (x 9 5).toNat ≤ (x 9 13).toNat := himp _ _ (hp5 9)
      have b26955 := hb (x 9 5)
      have b26956 := hb (x 9 13)
      clear * - r26954 b26955 b26956 d26945
      omega
    have d26957 : (x 9 5 && x 9 14).toNat = 0 := by
      have r26958 := hand1 (x 9 5) (x 9 14)
      have b26959 := hb (x 9 5)
      have b26960 := hb (x 9 5 && x 9 14)
      clear * - r26958 b26959 b26960 d26953
      omega
    have d26961 : (x 8 2).toNat = 0 := by
      have r26962 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26963 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e26964 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b26965 := hb (x 7 3)
      have b26966 := hb (x 8 2)
      have b26967 := hb (x 9 13)
      have b26968 := hb (x 10 12)
      clear * - r26962 e26963 e26964 b26965 b26966 b26967 b26968 d26929 d26945 d26925
      omega
    have d26969 : (x 8 2 && x 8 6).toNat = 0 := by
      have r26970 := hand1 (x 8 2) (x 8 6)
      have b26971 := hb (x 8 2)
      have b26972 := hb (x 8 2 && x 8 6)
      clear * - r26970 b26971 b26972 d26961
      omega
    have d26973 : (x 8 10).toNat = 0 := by
      have r26974 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
      have b26975 := hb (x 8 2)
      have b26976 := hb (x 8 10)
      clear * - r26974 b26975 b26976 d26961
      omega
    have d26977 : (x 4 6).toNat = 0 := by
      have r26978 : (x 4 6).toNat ≤ (x 4 14).toNat := himp _ _ (hp6 4)
      have b26979 := hb (x 4 6)
      have b26980 := hb (x 4 14)
      clear * - r26978 b26979 b26980 d26889
      omega
    have d26981 : (x 3 1 && x 3 11).toNat = 1 := by
      have r26982 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26983 := hb (x (-1) 5)
      have b26984 := hb (x 4 10)
      have b26985 := hb (x 3 1 && x 3 11)
      have b26986 := hb (x 2 2 && x 2 12)
      have b26987 := hb (x 1 3 && x 1 13)
      have b26988 := hb (x 0 4 && x 0 14)
      clear * - r26982 b26983 b26984 b26985 b26986 b26987 b26988 d26864 d26683 d26715 d26874 d26667
      omega
    have d26989 : (x 3 11).toNat = 1 := by
      have r26990 := hand2 (x 3 1) (x 3 11)
      have b26991 := hb (x 3 11)
      have b26992 := hb (x 3 1 && x 3 11)
      clear * - r26990 b26991 b26992 d26981
      omega
    have d26993 : (x 10 8).toNat = 0 := by
      have r26994 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26995 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
      have e26996 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
      have e26997 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
      have e26998 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
      have e26999 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
      have e27000 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
      have b27001 := hb (x 3 7)
      have b27002 := hb (x 4 6)
      have b27003 := hb (x 5 5)
      have b27004 := hb (x 6 4)
      have b27005 := hb (x 7 11)
      have b27006 := hb (x 8 10)
      have b27007 := hb (x 9 9)
      have b27008 := hb (x 10 8)
      clear * - r26994 e26995 e26996 e26997 e26998 e26999 e27000 b27001 b27002 b27003 b27004 b27005 b27006 b27007 b27008 d26973 d26918 d26812 d26836 d26977
      omega
    have d27009 : (x 9 9).toNat = 0 := by
      have r27010 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27011 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
      have e27012 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
      have e27013 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
      have e27014 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
      have e27015 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
      have e27016 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
      have b27017 := hb (x 3 7)
      have b27018 := hb (x 4 6)
      have b27019 := hb (x 5 5)
      have b27020 := hb (x 6 4)
      have b27021 := hb (x 7 11)
      have b27022 := hb (x 8 10)
      have b27023 := hb (x 9 9)
      have b27024 := hb (x 10 8)
      clear * - r27010 e27011 e27012 e27013 e27014 e27015 e27016 b27017 b27018 b27019 b27020 b27021 b27022 b27023 b27024 d26993 d26973 d26918 d26812 d26836 d26977
      omega
    have d27025 : (x 3 7).toNat = 0 := by
      have r27026 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27027 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
      have e27028 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
      have e27029 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
      have e27030 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
      have e27031 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
      have e27032 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
      have b27033 := hb (x 3 7)
      have b27034 := hb (x 4 6)
      have b27035 := hb (x 5 5)
      have b27036 := hb (x 6 4)
      have b27037 := hb (x 7 11)
      have b27038 := hb (x 8 10)
      have b27039 := hb (x 9 9)
      have b27040 := hb (x 10 8)
      clear * - r27026 e27027 e27028 e27029 e27030 e27031 e27032 b27033 b27034 b27035 b27036 b27037 b27038 b27039 b27040 d26993 d27009 d26973 d26918 d26812 d26836 d26977
      omega
    have d27041 : (x 3 7 && x 3 11).toNat = 0 := by
      have r27042 := hand1 (x 3 7) (x 3 11)
      have b27043 := hb (x 3 7)
      have b27044 := hb (x 3 7 && x 3 11)
      clear * - r27042 b27043 b27044 d27025
      omega
    have d27045 : (x 6 8).toNat = 0 := by
      have r27046 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27047 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e27048 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e27049 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e27050 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e27051 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e27052 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b27053 := hb (x (-1) 7)
      have b27054 := hb (x 0 6)
      have b27055 := hb (x 1 5)
      have b27056 := hb (x 2 4)
      have b27057 := hb (x 3 11)
      have b27058 := hb (x 4 10)
      have b27059 := hb (x 5 9)
      have b27060 := hb (x 6 8)
      clear * - r27046 e27047 e27048 e27049 e27050 e27051 e27052 b27053 b27054 b27055 b27056 b27057 b27058 b27059 b27060 d26864 d26989 d26691 d26723 g1
      omega
    have d27061 : (x 5 9).toNat = 0 := by
      have r27062 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27063 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e27064 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e27065 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e27066 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e27067 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e27068 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b27069 := hb (x (-1) 7)
      have b27070 := hb (x 0 6)
      have b27071 := hb (x 1 5)
      have b27072 := hb (x 2 4)
      have b27073 := hb (x 3 11)
      have b27074 := hb (x 4 10)
      have b27075 := hb (x 5 9)
      have b27076 := hb (x 6 8)
      clear * - r27062 e27063 e27064 e27065 e27066 e27067 e27068 b27069 b27070 b27071 b27072 b27073 b27074 b27075 b27076 d27045 d26864 d26989 d26691 d26723 g1
      omega
    have r27077 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r27078 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r27079 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27080 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
    have e27081 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
    have e27082 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
    have e27083 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
    have e27084 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
    have e27085 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
    have r27086 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27087 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
    have e27088 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
    have e27089 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
    have e27090 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
    have e27091 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
    have e27092 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
    have r27093 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27094 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e27095 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have r27096 : 1 ≤ (x 10 4).toNat + (x 9 1 && x 9 5).toNat + (x 8 2 && x 8 6).toNat + (x 7 3 && x 7 7).toNat + (x 6 4 && x 6 8).toNat + (x 5 5 && x 5 9).toNat + (x 4 6 && x 4 10).toNat + (x 3 7 && x 3 11).toNat + (x 2 8 && x 2 12).toNat + (x 1 9 && x 1 13).toNat + (x 0 10 && x 0 14).toNat + (x (-1) 11).toNat := by have q := hcov4 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27097 : (x 9 1 && x 9 5).toNat = (x 9 5).toNat := handr _ _ (fun h => hp13 9 (hp5 9 (h)))
    have e27098 : (x 0 10 && x 0 14).toNat = (x 0 10).toNat := handl _ _ (fun h => hp2 0 (hp10 0 (h)))
    have r27099 : 1 ≤ (x 2 9).toNat + (x 1 1 && x 1 10).toNat + (x 0 2 && x 0 11).toNat + (x (-1) 3 && x (-1) 12).toNat + (x (-2) 4 && x (-2) 13).toNat + (x (-3) 5 && x (-3) 14).toNat + (x (-4) 6).toNat := by have q := hcov9 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r27100 : 1 ≤ (x 14 9).toNat + (x 13 1 && x 13 10).toNat + (x 12 2 && x 12 11).toNat + (x 11 3 && x 11 12).toNat + (x 10 4 && x 10 13).toNat + (x 9 5 && x 9 14).toNat + (x 8 6).toNat := by have q := hcov9 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r27101 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r27102 := hand2 (x 7 3) (x 7 7)
    have r27103 := hand1 (x (-2) 4) (x (-2) 13)
    have r27104 := hand1 (x (-3) 5) (x (-3) 14)
    have r27105 := hand2 (x 13 1) (x 13 10)
    have r27106 := hand2 (x 12 2) (x 12 11)
    have r27107 := hand1 (x 11 3) (x 11 12)
    have r27108 := hand1 (x 13 1) (x 13 14)
    have b27147 := hb (x 14 1)
    linarith only [r27077, r27078, r27079, e27080, e27081, e27082, e27083, e27084, e27085, r27086, e27087, e27088, e27089, e27090, e27091, e27092, r27093, e27094, e27095, r27096, e27097, e27098, r27099, r27100, r27101, r27102, r27103, r27104, r27105, r27106, r27107, r27108, b27147, d26747, d26643, d26707, g3, d26910, d26675, d26768, d26989, d26764, d26864, g5, d27061, g6, d27045, g7, g8, d26953, d26937, d26969, d26820, d26844, d26868, d27041, d26687, d26719, g11, d26792, d26743, d26941, d26957]
  · have f27171 : (x 0 4).toNat = 1 := by rw [h26872]; rfl
    have d27172 : (x 0 12).toNat = 1 := by
      have r27173 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
      have b27174 := hb (x 0 4)
      have b27175 := hb (x 0 12)
      clear * - r27173 b27174 b27175 f27171
      omega
    have d27176 : (x (-2) 2).toNat = 0 := by
      have r27177 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27178 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e27179 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have b27180 := hb (x (-3) 3)
      have b27181 := hb (x (-2) 2)
      have b27182 := hb (x (-1) 13)
      have b27183 := hb (x 0 12)
      clear * - r27177 e27178 e27179 b27180 b27181 b27182 b27183 d27172 d26655
      omega
    have d27184 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
      have r27185 := hand1 (x (-2) 2) (x (-2) 13)
      have b27186 := hb (x (-2) 2)
      have b27187 := hb (x (-2) 2 && x (-2) 13)
      clear * - r27185 b27186 b27187 d27176
      omega
    have d27188 : (x (-2) 10).toNat = 0 := by
      have r27189 : (x (-2) 10).toNat ≤ (x (-2) 2).toNat := himp _ _ (hp10 (-2))
      have b27190 := hb (x (-2) 2)
      have b27191 := hb (x (-2) 10)
      clear * - r27189 b27190 b27191 d27176
      omega
    have d27192 : (x (-3) 3).toNat = 0 := by
      have r27193 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27194 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e27195 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have b27196 := hb (x (-3) 3)
      have b27197 := hb (x (-2) 2)
      have b27198 := hb (x (-1) 13)
      have b27199 := hb (x 0 12)
      clear * - r27193 e27194 e27195 b27196 b27197 b27198 b27199 d27172 d26655 d27176
      omega
    have d27200 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
      have r27201 := hand1 (x (-3) 3) (x (-3) 14)
      have b27202 := hb (x (-3) 3)
      have b27203 := hb (x (-3) 3 && x (-3) 14)
      clear * - r27201 b27202 b27203 d27192
      omega
    have d27204 : (x (-3) 11).toNat = 0 := by
      have r27205 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
      have b27206 := hb (x (-3) 3)
      have b27207 := hb (x (-3) 11)
      clear * - r27205 b27206 b27207 d27192
      omega
    have d27208 : (x (-3) 1 && x (-3) 11).toNat = 0 := by
      have r27209 := hand2 (x (-3) 1) (x (-3) 11)
      have b27210 := hb (x (-3) 11)
      have b27211 := hb (x (-3) 1 && x (-3) 11)
      clear * - r27209 b27210 b27211 d27204
      omega
    have d27212 : (x (-4) 4).toNat = 1 := by
      have r27213 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b27214 := hb (x (-4) 4)
      have b27215 := hb (x 0 11)
      have b27216 := hb (x (-1) 1 && x (-1) 12)
      have b27217 := hb (x (-2) 2 && x (-2) 13)
      have b27218 := hb (x (-3) 3 && x (-3) 14)
      clear * - r27213 b27214 b27215 b27216 b27217 b27218 d26788 d26651 d27184 d27200
      omega
    have d27219 : (x (-4) 12).toNat = 1 := by
      have r27220 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
      have b27221 := hb (x (-4) 4)
      have b27222 := hb (x (-4) 12)
      clear * - r27220 b27221 b27222 d27212
      omega
    have d27223 : (x (-5) 13).toNat = 0 := by
      have r27224 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27225 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e27226 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have b27227 := hb (x (-7) 3)
      have b27228 := hb (x (-6) 2)
      have b27229 := hb (x (-5) 13)
      have b27230 := hb (x (-4) 12)
      clear * - r27224 e27225 e27226 b27227 b27228 b27229 b27230 d27219
      omega
    have d27231 : (x (-5) 3 && x (-5) 13).toNat = 0 := by
      have r27232 := hand2 (x (-5) 3) (x (-5) 13)
      have b27233 := hb (x (-5) 13)
      have b27234 := hb (x (-5) 3 && x (-5) 13)
      clear * - r27232 b27233 b27234 d27223
      omega
    have d27235 : (x (-5) 5).toNat = 0 := by
      have r27236 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
      have b27237 := hb (x (-5) 5)
      have b27238 := hb (x (-5) 13)
      clear * - r27236 b27237 b27238 d27223
      omega
    have d27239 : (x 4 8).toNat = 0 := by
      have r27240 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27241 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
      have e27242 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
      have e27243 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
      have e27244 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
      have e27245 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
      have e27246 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
      have b27247 := hb (x (-3) 7)
      have b27248 := hb (x (-2) 6)
      have b27249 := hb (x (-1) 5)
      have b27250 := hb (x 0 4)
      have b27251 := hb (x 1 11)
      have b27252 := hb (x 2 10)
      have b27253 := hb (x 3 9)
      have b27254 := hb (x 4 8)
      clear * - r27240 e27241 e27242 e27243 e27244 e27245 e27246 b27247 b27248 b27249 b27250 b27251 b27252 b27253 b27254 f27171 d26667
      omega
    have d27255 : (x 4 4 && x 4 8).toNat = 0 := by
      have r27256 := hand2 (x 4 4) (x 4 8)
      have b27257 := hb (x 4 8)
      have b27258 := hb (x 4 4 && x 4 8)
      clear * - r27256 b27257 b27258 d27239
      omega
    have d27259 : (x 3 9).toNat = 0 := by
      have r27260 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27261 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
      have e27262 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
      have e27263 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
      have e27264 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
      have e27265 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
      have e27266 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
      have b27267 := hb (x (-3) 7)
      have b27268 := hb (x (-2) 6)
      have b27269 := hb (x (-1) 5)
      have b27270 := hb (x 0 4)
      have b27271 := hb (x 1 11)
      have b27272 := hb (x 2 10)
      have b27273 := hb (x 3 9)
      have b27274 := hb (x 4 8)
      clear * - r27260 e27261 e27262 e27263 e27264 e27265 e27266 b27267 b27268 b27269 b27270 b27271 b27272 b27273 b27274 d27239 f27171 d26667
      omega
    have d27275 : (x 3 3 && x 3 9).toNat = 0 := by
      have r27276 := hand2 (x 3 3) (x 3 9)
      have b27277 := hb (x 3 9)
      have b27278 := hb (x 3 3 && x 3 9)
      clear * - r27276 b27277 b27278 d27259
      omega
    have d27279 : (x 3 5 && x 3 9).toNat = 0 := by
      have r27280 := hand2 (x 3 5) (x 3 9)
      have b27281 := hb (x 3 9)
      have b27282 := hb (x 3 5 && x 3 9)
      clear * - r27280 b27281 b27282 d27259
      omega
    have d27283 : (x 2 10).toNat = 0 := by
      have r27284 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27285 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
      have e27286 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
      have e27287 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
      have e27288 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
      have e27289 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
      have e27290 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
      have b27291 := hb (x (-3) 7)
      have b27292 := hb (x (-2) 6)
      have b27293 := hb (x (-1) 5)
      have b27294 := hb (x 0 4)
      have b27295 := hb (x 1 11)
      have b27296 := hb (x 2 10)
      have b27297 := hb (x 3 9)
      have b27298 := hb (x 4 8)
      clear * - r27284 e27285 e27286 e27287 e27288 e27289 e27290 b27291 b27292 b27293 b27294 b27295 b27296 b27297 b27298 d27239 d27259 f27171 d26667
      omega
    have d27299 : (x 2 6 && x 2 10).toNat = 0 := by
      have r27300 := hand2 (x 2 6) (x 2 10)
      have b27301 := hb (x 2 10)
      have b27302 := hb (x 2 6 && x 2 10)
      clear * - r27300 b27301 b27302 d27283
      omega
    have d27303 : (x 1 11).toNat = 0 := by
      have r27304 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27305 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
      have e27306 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
      have e27307 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
      have e27308 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
      have e27309 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
      have e27310 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
      have b27311 := hb (x (-3) 7)
      have b27312 := hb (x (-2) 6)
      have b27313 := hb (x (-1) 5)
      have b27314 := hb (x 0 4)
      have b27315 := hb (x 1 11)
      have b27316 := hb (x 2 10)
      have b27317 := hb (x 3 9)
      have b27318 := hb (x 4 8)
      clear * - r27304 e27305 e27306 e27307 e27308 e27309 e27310 b27311 b27312 b27313 b27314 b27315 b27316 b27317 b27318 d27239 d27259 d27283 f27171 d26667
      omega
    have d27319 : (x 1 7 && x 1 11).toNat = 0 := by
      have r27320 := hand2 (x 1 7) (x 1 11)
      have b27321 := hb (x 1 11)
      have b27322 := hb (x 1 7 && x 1 11)
      clear * - r27320 b27321 b27322 d27303
      omega
    have d27323 : (x 0 8).toNat = 0 := by
      have r27324 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27325 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
      have e27326 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
      have e27327 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
      have e27328 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
      have e27329 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
      have e27330 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
      have b27331 := hb (x (-7) 7)
      have b27332 := hb (x (-6) 6)
      have b27333 := hb (x (-5) 5)
      have b27334 := hb (x (-4) 4)
      have b27335 := hb (x (-3) 11)
      have b27336 := hb (x (-2) 10)
      have b27337 := hb (x (-1) 9)
      have b27338 := hb (x 0 8)
      clear * - r27324 e27325 e27326 e27327 e27328 e27329 e27330 b27331 b27332 b27333 b27334 b27335 b27336 b27337 b27338 d26671 d27188 d27204 d27212 d27235
      omega
    have d27339 : (x 0 8 && x 0 12).toNat = 0 := by
      have r27340 := hand1 (x 0 8) (x 0 12)
      have b27341 := hb (x 0 8)
      have b27342 := hb (x 0 8 && x 0 12)
      clear * - r27340 b27341 b27342 d27323
      omega
    have r27343 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27344 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
    have e27345 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
    have e27346 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
    have e27347 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
    have e27348 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
    have e27349 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
    have r27350 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27351 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
    have e27352 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
    have e27353 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
    have e27354 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
    have e27355 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
    have e27356 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
    have r27357 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27358 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e27359 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e27360 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e27361 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e27362 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e27363 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have r27364 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27365 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
    have e27366 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
    have e27367 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
    have e27368 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
    have e27369 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
    have e27370 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
    have r27371 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27372 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
    have e27373 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
    have r27374 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27375 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e27376 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have r27377 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27378 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e27379 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have r27380 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r27381 : 1 ≤ (x 6 4).toNat + (x 5 1 && x 5 5).toNat + (x 4 2 && x 4 6).toNat + (x 3 3 && x 3 7).toNat + (x 2 4 && x 2 8).toNat + (x 1 5 && x 1 9).toNat + (x 0 6 && x 0 10).toNat + (x (-1) 7 && x (-1) 11).toNat + (x (-2) 8 && x (-2) 12).toNat + (x (-3) 9 && x (-3) 13).toNat + (x (-4) 10 && x (-4) 14).toNat + (x (-5) 11).toNat := by have q := hcov4 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27382 : (x 5 1 && x 5 5).toNat = (x 5 5).toNat := handr _ _ (fun h => hp13 5 (hp5 5 (h)))
    have e27383 : (x (-4) 10 && x (-4) 14).toNat = (x (-4) 10).toNat := handl _ _ (fun h => hp2 (-4) (hp10 (-4) (h)))
    have r27384 : 1 ≤ (x 8 4).toNat + (x 7 1 && x 7 5).toNat + (x 6 2 && x 6 6).toNat + (x 5 3 && x 5 7).toNat + (x 4 4 && x 4 8).toNat + (x 3 5 && x 3 9).toNat + (x 2 6 && x 2 10).toNat + (x 1 7 && x 1 11).toNat + (x 0 8 && x 0 12).toNat + (x (-1) 9 && x (-1) 13).toNat + (x (-2) 10 && x (-2) 14).toNat + (x (-3) 11).toNat := by have q := hcov4 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27385 : (x 7 1 && x 7 5).toNat = (x 7 5).toNat := handr _ _ (fun h => hp13 7 (hp5 7 (h)))
    have e27386 : (x (-2) 10 && x (-2) 14).toNat = (x (-2) 10).toNat := handl _ _ (fun h => hp2 (-2) (hp10 (-2) (h)))
    have r27387 : 1 ≤ (x 6 6).toNat + (x 5 1 && x 5 7).toNat + (x 4 2 && x 4 8).toNat + (x 3 3 && x 3 9).toNat + (x 2 4 && x 2 10).toNat + (x 1 5 && x 1 11).toNat + (x 0 6 && x 0 12).toNat + (x (-1) 7 && x (-1) 13).toNat + (x (-2) 8 && x (-2) 14).toNat + (x (-3) 9).toNat := by have q := hcov6 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r27388 : 1 ≤ (x 10 9).toNat + (x 9 1 && x 9 10).toNat + (x 8 2 && x 8 11).toNat + (x 7 3 && x 7 12).toNat + (x 6 4 && x 6 13).toNat + (x 5 5 && x 5 14).toNat + (x 4 6).toNat := by have q := hcov9 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r27389 : 1 ≤ (x 11 9).toNat + (x 10 1 && x 10 10).toNat + (x 9 2 && x 9 11).toNat + (x 8 3 && x 8 12).toNat + (x 7 4 && x 7 13).toNat + (x 6 5 && x 6 14).toNat + (x 5 6).toNat := by have q := hcov9 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r27390 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r27391 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r27392 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r27393 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r27394 := hand2 (x 3 3) (x 3 7)
    have r27395 := hand2 (x (-2) 8) (x (-2) 12)
    have r27396 := hand2 (x (-3) 9) (x (-3) 13)
    have r27397 := hand1 (x 6 2) (x 6 6)
    have r27398 := hand1 (x 5 3) (x 5 7)
    have r27399 := hand2 (x 5 1) (x 5 7)
    have r27400 := hand1 (x (-2) 8) (x (-2) 14)
    have r27401 := hand2 (x 9 1) (x 9 10)
    have r27402 := hand2 (x 8 2) (x 8 11)
    have r27403 := hand2 (x 7 3) (x 7 12)
    have r27404 := hand2 (x 10 1) (x 10 10)
    have r27405 := hand2 (x 9 2) (x 9 11)
    have r27406 := hand2 (x 8 3) (x 8 12)
    have r27407 := hand1 (x 7 4) (x 7 13)
    have r27408 := hand1 (x 6 5) (x 6 14)
    have r27409 := hand1 (x (-4) 2) (x (-4) 12)
    have r27410 := hand1 (x (-6) 4) (x (-6) 14)
    have r27411 := hand1 (x 4 3) (x 4 14)
    have r27412 := hand1 (x 5 1) (x 5 14)
    have r27413 := hand2 (x 6 1) (x 6 14)
    linarith only [r27343, e27344, e27345, e27346, e27347, e27348, e27349, r27350, e27351, e27352, e27353, e27354, e27355, e27356, r27357, e27358, e27359, e27360, e27361, e27362, e27363, r27364, e27365, e27366, e27367, e27368, e27369, e27370, r27371, e27372, e27373, r27374, e27375, e27376, r27377, e27378, e27379, r27380, r27381, e27382, e27383, r27384, e27385, e27386, r27387, r27388, r27389, r27390, r27391, r27392, r27393, r27394, r27395, r27396, r27397, r27398, r27399, r27400, r27401, r27402, r27403, r27404, r27405, r27406, r27407, r27408, r27409, r27410, r27411, r27412, r27413, d27204, d27188, g4, d26848, d26836, d26812, d26860, d26703, d26731, g9, d26751, d27255, d27279, d27299, d27319, d27339, d26663, d26856, d27275, d26699, d26727, g10, d26659, d26816, d26840, d27208, d27231, d26808, d26832]

theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b111 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 2).toNat = 1)
    (g1 : (x 0 6).toNat = 0)
    (g2 : (x 1 2).toNat = 0)
    (g3 : (x 1 14).toNat = 0)
    (g4 : (x 3 4).toNat = 0)
    (g5 : (x 4 11).toNat = 0)
    (g6 : (x 5 10).toNat = 0)
    (g7 : (x 6 9).toNat = 0)
    (g8 : (x 7 8).toNat = 0)
    (g9 : (x 0 6 && x 0 10).toNat = 0)
    (g10 : (x 0 6 && x 0 12).toNat = 0)
    (g11 : (x 1 1 && x 1 10).toNat = 0)
    (g12 : (x 5 1 && x 5 10).toNat = 0)
    (g13 : (x 4 2 && x 4 11).toNat = 0)
    (g14 : (x 1 5 && x 1 14).toNat = 0)
    (g15 : (x 1 3 && x 1 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b111_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15
