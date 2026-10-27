import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_a1

Topic: combinatorics   Node: c3dda208b6ed

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core: under the layer-free tight-cover constraints for k = 15 and 50 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_a1_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-4) 6).toNat = 0)
    (g1 : (x (-1) 5).toNat = 0)
    (g2 : (x (-1) 9).toNat = 0)
    (g3 : (x (-1) 11).toNat = 0)
    (g4 : (x (-1) 13).toNat = 0)
    (g5 : (x 0 4).toNat = 1)
    (g6 : (x 0 10).toNat = 1)
    (g7 : (x 0 11).toNat = 0)
    (g8 : (x 1 5).toNat = 0)
    (g9 : (x 1 9).toNat = 0)
    (g10 : (x 2 4).toNat = 0)
    (g11 : (x 2 8).toNat = 0)
    (g12 : (x (-1) 3 && x (-1) 7).toNat = 0)
    (g13 : (x (-2) 4 && x (-2) 8).toNat = 0)
    (g14 : (x (-3) 5 && x (-3) 9).toNat = 0)
    (g15 : (x (-4) 6 && x (-4) 10).toNat = 0)
    (g16 : (x (-5) 7 && x (-5) 11).toNat = 0)
    (g17 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g18 : (x 2 4 && x 2 8).toNat = 0)
    (g19 : (x 1 5 && x 1 9).toNat = 0)
    (g20 : (x (-1) 7 && x (-1) 11).toNat = 0)
    (g21 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g22 : (x (-1) 4 && x (-1) 9).toNat = 0)
    (g23 : (x (-1) 9 && x (-1) 14).toNat = 0)
    (g24 : (x (-1) 3 && x (-1) 9).toNat = 0)
    (g25 : (x (-2) 4 && x (-2) 10).toNat = 0)
    (g26 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g27 : (x (-4) 6 && x (-4) 12).toNat = 0)
    (g28 : (x (-5) 7 && x (-5) 13).toNat = 0)
    (g29 : (x 2 6 && x 2 12).toNat = 0)
    (g30 : (x 1 7 && x 1 13).toNat = 0)
    (g31 : (x 2 8 && x 2 14).toNat = 0)
    (g32 : (x 2 4 && x 2 11).toNat = 0)
    (g33 : (x 1 5 && x 1 12).toNat = 0)
    (g34 : (x 2 5 && x 2 12).toNat = 0)
    (g35 : (x 1 6 && x 1 13).toNat = 0)
    (g36 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g37 : (x 0 2 && x 0 11).toNat = 0)
    (g38 : (x (-1) 3 && x (-1) 12).toNat = 0)
    (g39 : (x (-2) 4 && x (-2) 13).toNat = 0)
    (g40 : (x (-3) 5 && x (-3) 14).toNat = 0)
    (g41 : (x (-1) 4 && x (-1) 13).toNat = 0)
    (g42 : (x 2 3 && x 2 12).toNat = 0)
    (g43 : (x 1 4 && x 1 13).toNat = 0)
    (g44 : (x 2 4 && x 2 13).toNat = 0)
    (g45 : (x 1 5 && x 1 14).toNat = 0)
    (g46 : (x 0 1 && x 0 11).toNat = 0)
    (g47 : (x 2 4 && x 2 14).toNat = 0)
    (g48 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g49 : (x (-1) 1 && x (-1) 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d29722 : (x 0 12).toNat = 1 := by
    have r29723 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
    have b29724 := hb (x 0 4)
    have b29725 := hb (x 0 12)
    clear * - r29723 b29724 b29725 g5
    omega
  have d29726 : (x (-2) 2).toNat = 0 := by
    have r29727 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e29728 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e29729 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b29730 := hb (x (-3) 3)
    have b29731 := hb (x (-2) 2)
    have b29732 := hb (x (-1) 13)
    have b29733 := hb (x 0 12)
    clear * - r29727 e29728 e29729 b29730 b29731 b29732 b29733 d29722 g4
    omega
  have d29734 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
    have r29735 := hand1 (x (-2) 2) (x (-2) 13)
    have b29736 := hb (x (-2) 2)
    have b29737 := hb (x (-2) 2 && x (-2) 13)
    clear * - r29735 b29736 b29737 d29726
    omega
  have d29738 : (x (-2) 2 && x (-2) 11).toNat = 0 := by
    have r29739 := hand1 (x (-2) 2) (x (-2) 11)
    have b29740 := hb (x (-2) 2)
    have b29741 := hb (x (-2) 2 && x (-2) 11)
    clear * - r29739 b29740 b29741 d29726
    omega
  have d29742 : (x (-2) 10).toNat = 0 := by
    have r29743 : (x (-2) 10).toNat ≤ (x (-2) 2).toNat := himp _ _ (hp10 (-2))
    have b29744 := hb (x (-2) 2)
    have b29745 := hb (x (-2) 10)
    clear * - r29743 b29744 b29745 d29726
    omega
  have d29746 : (x (-2) 5 && x (-2) 10).toNat = 0 := by
    have r29747 := hand2 (x (-2) 5) (x (-2) 10)
    have b29748 := hb (x (-2) 10)
    have b29749 := hb (x (-2) 5 && x (-2) 10)
    clear * - r29747 b29748 b29749 d29742
    omega
  have d29750 : (x (-2) 6 && x (-2) 10).toNat = 0 := by
    have r29751 := hand2 (x (-2) 6) (x (-2) 10)
    have b29752 := hb (x (-2) 10)
    have b29753 := hb (x (-2) 6 && x (-2) 10)
    clear * - r29751 b29752 b29753 d29742
    omega
  have d29754 : (x 0 13).toNat = 1 := by
    have r29755 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b29756 := hb (x (-2) 2)
    have b29757 := hb (x 0 13)
    have b29758 := hb (x (-1) 1 && x (-1) 14)
    clear * - r29755 b29756 b29757 b29758 g49 d29726
    omega
  have d29759 : (x 0 1).toNat = 1 := by
    have r29760 : (x 0 13).toNat ≤ (x 0 1).toNat := himp _ _ (hp13 0)
    have b29761 := hb (x 0 1)
    have b29762 := hb (x 0 13)
    clear * - r29760 b29761 b29762 d29754
    omega
  have d29763 : (x 1 14).toNat = 0 := by
    have r29764 : (x 1 14).toNat + (x 0 1).toNat = 1 := by have q := hd14 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b29765 := hb (x 0 1)
    have b29766 := hb (x 1 14)
    clear * - r29764 b29765 b29766 d29759
    omega
  have d29767 : (x 1 7 && x 1 14).toNat = 0 := by
    have r29768 := hand2 (x 1 7) (x 1 14)
    have b29769 := hb (x 1 14)
    have b29770 := hb (x 1 7 && x 1 14)
    clear * - r29768 b29769 b29770 d29763
    omega
  have d29771 : (x 1 6).toNat = 0 := by
    have r29772 : (x 1 6).toNat ≤ (x 1 14).toNat := himp _ _ (hp6 1)
    have b29773 := hb (x 1 6)
    have b29774 := hb (x 1 14)
    clear * - r29772 b29773 b29774 d29763
    omega
  have d29775 : (x 1 6 && x 1 12).toNat = 0 := by
    have r29776 := hand1 (x 1 6) (x 1 12)
    have b29777 := hb (x 1 6)
    have b29778 := hb (x 1 6 && x 1 12)
    clear * - r29776 b29777 b29778 d29771
    omega
  have d29779 : (x 1 2 && x 1 6).toNat = 0 := by
    have r29780 := hand2 (x 1 2) (x 1 6)
    have b29781 := hb (x 1 6)
    have b29782 := hb (x 1 2 && x 1 6)
    clear * - r29780 b29781 b29782 d29771
    omega
  have d29783 : (x 1 2).toNat = 0 := by
    have r29784 : (x 1 2).toNat ≤ (x 1 14).toNat := himp _ _ (hp2 1)
    have b29785 := hb (x 1 2)
    have b29786 := hb (x 1 14)
    clear * - r29784 b29785 b29786 d29763
    omega
  have d29787 : (x 1 2 && x 1 11).toNat = 0 := by
    have r29788 := hand1 (x 1 2) (x 1 11)
    have b29789 := hb (x 1 2)
    have b29790 := hb (x 1 2 && x 1 11)
    clear * - r29788 b29789 b29790 d29783
    omega
  have d29791 : (x 1 2 && x 1 7).toNat = 0 := by
    have r29792 := hand1 (x 1 2) (x 1 7)
    have b29793 := hb (x 1 2)
    have b29794 := hb (x 1 2 && x 1 7)
    clear * - r29792 b29793 b29794 d29783
    omega
  have d29795 : (x 1 10).toNat = 0 := by
    have r29796 : (x 1 10).toNat ≤ (x 1 2).toNat := himp _ _ (hp10 1)
    have b29797 := hb (x 1 2)
    have b29798 := hb (x 1 10)
    clear * - r29796 b29797 b29798 d29783
    omega
  have d29799 : (x 1 1 && x 1 10).toNat = 0 := by
    have r29800 := hand2 (x 1 1) (x 1 10)
    have b29801 := hb (x 1 10)
    have b29802 := hb (x 1 1 && x 1 10)
    clear * - r29800 b29801 b29802 d29795
    omega
  have d29803 : (x 1 12).toNat = 0 := by
    have r29804 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e29805 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e29806 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b29807 := hb (x (-2) 3)
    have b29808 := hb (x (-1) 2)
    have b29809 := hb (x 0 13)
    have b29810 := hb (x 1 12)
    clear * - r29804 e29805 e29806 b29807 b29808 b29809 b29810 d29754
    omega
  have d29811 : (x 1 7 && x 1 12).toNat = 0 := by
    have r29812 := hand2 (x 1 7) (x 1 12)
    have b29813 := hb (x 1 12)
    have b29814 := hb (x 1 7 && x 1 12)
    clear * - r29812 b29813 b29814 d29803
    omega
  have d29815 : (x 1 8 && x 1 12).toNat = 0 := by
    have r29816 := hand2 (x 1 8) (x 1 12)
    have b29817 := hb (x 1 12)
    have b29818 := hb (x 1 8 && x 1 12)
    clear * - r29816 b29817 b29818 d29803
    omega
  have d29819 : (x 1 4).toNat = 0 := by
    have r29820 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
    have b29821 := hb (x 1 4)
    have b29822 := hb (x 1 12)
    clear * - r29820 b29821 b29822 d29803
    omega
  have d29823 : (x (-1) 2).toNat = 0 := by
    have r29824 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e29825 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e29826 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b29827 := hb (x (-2) 3)
    have b29828 := hb (x (-1) 2)
    have b29829 := hb (x 0 13)
    have b29830 := hb (x 1 12)
    clear * - r29824 e29825 e29826 b29827 b29828 b29829 b29830 d29803 d29754
    omega
  have d29831 : (x (-1) 2 && x (-1) 12).toNat = 0 := by
    have r29832 := hand1 (x (-1) 2) (x (-1) 12)
    have b29833 := hb (x (-1) 2)
    have b29834 := hb (x (-1) 2 && x (-1) 12)
    clear * - r29832 b29833 b29834 d29823
    omega
  have d29835 : (x (-1) 10).toNat = 0 := by
    have r29836 : (x (-1) 10).toNat ≤ (x (-1) 2).toNat := himp _ _ (hp10 (-1))
    have b29837 := hb (x (-1) 2)
    have b29838 := hb (x (-1) 10)
    clear * - r29836 b29837 b29838 d29823
    omega
  have d29839 : (x (-2) 3).toNat = 0 := by
    have r29840 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e29841 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e29842 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b29843 := hb (x (-2) 3)
    have b29844 := hb (x (-1) 2)
    have b29845 := hb (x 0 13)
    have b29846 := hb (x 1 12)
    clear * - r29840 e29841 e29842 b29843 b29844 b29845 b29846 d29803 d29754 d29823
    omega
  have d29847 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
    have r29848 := hand1 (x (-2) 3) (x (-2) 13)
    have b29849 := hb (x (-2) 3)
    have b29850 := hb (x (-2) 3 && x (-2) 13)
    clear * - r29848 b29849 b29850 d29839
    omega
  have d29851 : (x (-2) 11).toNat = 0 := by
    have r29852 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
    have b29853 := hb (x (-2) 3)
    have b29854 := hb (x (-2) 11)
    clear * - r29852 b29853 b29854 d29839
    omega
  have d29855 : (x (-3) 3).toNat = 0 := by
    have r29856 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e29857 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e29858 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b29859 := hb (x (-3) 3)
    have b29860 := hb (x (-2) 2)
    have b29861 := hb (x (-1) 13)
    have b29862 := hb (x 0 12)
    clear * - r29856 e29857 e29858 b29859 b29860 b29861 b29862 d29722 g4 d29726
    omega
  have d29863 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
    have r29864 := hand1 (x (-3) 3) (x (-3) 14)
    have b29865 := hb (x (-3) 3)
    have b29866 := hb (x (-3) 3 && x (-3) 14)
    clear * - r29864 b29865 b29866 d29855
    omega
  have d29867 : (x (-3) 3 && x (-3) 12).toNat = 0 := by
    have r29868 := hand1 (x (-3) 3) (x (-3) 12)
    have b29869 := hb (x (-3) 3)
    have b29870 := hb (x (-3) 3 && x (-3) 12)
    clear * - r29868 b29869 b29870 d29855
    omega
  have d29871 : (x (-3) 11).toNat = 0 := by
    have r29872 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
    have b29873 := hb (x (-3) 3)
    have b29874 := hb (x (-3) 11)
    clear * - r29872 b29873 b29874 d29855
    omega
  have d29875 : (x (-3) 6 && x (-3) 11).toNat = 0 := by
    have r29876 := hand2 (x (-3) 6) (x (-3) 11)
    have b29877 := hb (x (-3) 11)
    have b29878 := hb (x (-3) 6 && x (-3) 11)
    clear * - r29876 b29877 b29878 d29871
    omega
  have d29879 : (x (-3) 7 && x (-3) 11).toNat = 0 := by
    have r29880 := hand2 (x (-3) 7) (x (-3) 11)
    have b29881 := hb (x (-3) 11)
    have b29882 := hb (x (-3) 7 && x (-3) 11)
    clear * - r29880 b29881 b29882 d29871
    omega
  have d29883 : (x (-4) 4).toNat = 1 := by
    have r29884 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b29885 := hb (x (-4) 4)
    have b29886 := hb (x 0 11)
    have b29887 := hb (x (-1) 1 && x (-1) 12)
    have b29888 := hb (x (-2) 2 && x (-2) 13)
    have b29889 := hb (x (-3) 3 && x (-3) 14)
    clear * - r29884 b29885 b29886 b29887 b29888 b29889 g7 g48 d29734 d29863
    omega
  have d29890 : (x (-4) 12).toNat = 1 := by
    have r29891 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
    have b29892 := hb (x (-4) 4)
    have b29893 := hb (x (-4) 12)
    clear * - r29891 b29892 b29893 d29883
    omega
  have d29894 : (x (-5) 13).toNat = 0 := by
    have r29895 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e29896 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e29897 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b29898 := hb (x (-7) 3)
    have b29899 := hb (x (-6) 2)
    have b29900 := hb (x (-5) 13)
    have b29901 := hb (x (-4) 12)
    clear * - r29895 e29896 e29897 b29898 b29899 b29900 b29901 d29890
    omega
  have d29902 : (x (-5) 2 && x (-5) 13).toNat = 0 := by
    have r29903 := hand2 (x (-5) 2) (x (-5) 13)
    have b29904 := hb (x (-5) 13)
    have b29905 := hb (x (-5) 2 && x (-5) 13)
    clear * - r29903 b29904 b29905 d29894
    omega
  have d29906 : (x (-5) 8 && x (-5) 13).toNat = 0 := by
    have r29907 := hand2 (x (-5) 8) (x (-5) 13)
    have b29908 := hb (x (-5) 13)
    have b29909 := hb (x (-5) 8 && x (-5) 13)
    clear * - r29907 b29908 b29909 d29894
    omega
  have d29910 : (x (-5) 9 && x (-5) 13).toNat = 0 := by
    have r29911 := hand2 (x (-5) 9) (x (-5) 13)
    have b29912 := hb (x (-5) 13)
    have b29913 := hb (x (-5) 9 && x (-5) 13)
    clear * - r29911 b29912 b29913 d29894
    omega
  have d29914 : (x (-5) 5).toNat = 0 := by
    have r29915 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
    have b29916 := hb (x (-5) 5)
    have b29917 := hb (x (-5) 13)
    clear * - r29915 b29916 b29917 d29894
    omega
  have d29918 : (x (-5) 5 && x (-5) 14).toNat = 0 := by
    have r29919 := hand1 (x (-5) 5) (x (-5) 14)
    have b29920 := hb (x (-5) 5)
    have b29921 := hb (x (-5) 5 && x (-5) 14)
    clear * - r29919 b29920 b29921 d29914
    omega
  have d29922 : (x (-6) 2).toNat = 0 := by
    have r29923 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e29924 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e29925 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b29926 := hb (x (-7) 3)
    have b29927 := hb (x (-6) 2)
    have b29928 := hb (x (-5) 13)
    have b29929 := hb (x (-4) 12)
    clear * - r29923 e29924 e29925 b29926 b29927 b29928 b29929 d29890 d29894
    omega
  have d29930 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
    have r29931 := hand1 (x (-6) 2) (x (-6) 13)
    have b29932 := hb (x (-6) 2)
    have b29933 := hb (x (-6) 2 && x (-6) 13)
    clear * - r29931 b29932 b29933 d29922
    omega
  have d29934 : (x (-6) 2 && x (-6) 11).toNat = 0 := by
    have r29935 := hand1 (x (-6) 2) (x (-6) 11)
    have b29936 := hb (x (-6) 2)
    have b29937 := hb (x (-6) 2 && x (-6) 11)
    clear * - r29935 b29936 b29937 d29922
    omega
  have d29938 : (x (-6) 10).toNat = 0 := by
    have r29939 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
    have b29940 := hb (x (-6) 2)
    have b29941 := hb (x (-6) 10)
    clear * - r29939 b29940 b29941 d29922
    omega
  have d29942 : (x (-6) 1 && x (-6) 10).toNat = 0 := by
    have r29943 := hand2 (x (-6) 1) (x (-6) 10)
    have b29944 := hb (x (-6) 10)
    have b29945 := hb (x (-6) 1 && x (-6) 10)
    clear * - r29943 b29944 b29945 d29938
    omega
  have d29946 : (x (-7) 3).toNat = 0 := by
    have r29947 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e29948 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e29949 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b29950 := hb (x (-7) 3)
    have b29951 := hb (x (-6) 2)
    have b29952 := hb (x (-5) 13)
    have b29953 := hb (x (-4) 12)
    clear * - r29947 e29948 e29949 b29950 b29951 b29952 b29953 d29890 d29894 d29922
    omega
  have d29954 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
    have r29955 := hand1 (x (-7) 3) (x (-7) 14)
    have b29956 := hb (x (-7) 3)
    have b29957 := hb (x (-7) 3 && x (-7) 14)
    clear * - r29955 b29956 b29957 d29946
    omega
  have d29958 : (x (-7) 3 && x (-7) 12).toNat = 0 := by
    have r29959 := hand1 (x (-7) 3) (x (-7) 12)
    have b29960 := hb (x (-7) 3)
    have b29961 := hb (x (-7) 3 && x (-7) 12)
    clear * - r29959 b29960 b29961 d29946
    omega
  have d29962 : (x (-7) 11).toNat = 0 := by
    have r29963 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
    have b29964 := hb (x (-7) 3)
    have b29965 := hb (x (-7) 11)
    clear * - r29963 b29964 b29965 d29946
    omega
  have d29966 : (x (-7) 1 && x (-7) 11).toNat = 0 := by
    have r29967 := hand2 (x (-7) 1) (x (-7) 11)
    have b29968 := hb (x (-7) 11)
    have b29969 := hb (x (-7) 1 && x (-7) 11)
    clear * - r29967 b29968 b29969 d29962
    omega
  have d29970 : (x (-7) 2 && x (-7) 11).toNat = 0 := by
    have r29971 := hand2 (x (-7) 2) (x (-7) 11)
    have b29972 := hb (x (-7) 11)
    have b29973 := hb (x (-7) 2 && x (-7) 11)
    clear * - r29971 b29972 b29973 d29962
    omega
  have d29974 : (x 2 9).toNat = 1 := by
    have r29975 : 1 ≤ (x 2 9).toNat + (x 1 1 && x 1 10).toNat + (x 0 2 && x 0 11).toNat + (x (-1) 3 && x (-1) 12).toNat + (x (-2) 4 && x (-2) 13).toNat + (x (-3) 5 && x (-3) 14).toNat + (x (-4) 6).toNat := by have q := hcov9 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b29976 := hb (x (-4) 6)
    have b29977 := hb (x 2 9)
    have b29978 := hb (x 1 1 && x 1 10)
    have b29979 := hb (x 0 2 && x 0 11)
    have b29980 := hb (x (-1) 3 && x (-1) 12)
    have b29981 := hb (x (-2) 4 && x (-2) 13)
    have b29982 := hb (x (-3) 5 && x (-3) 14)
    clear * - r29975 b29976 b29977 b29978 b29979 b29980 b29981 b29982 d29799 g37 g38 g39 g40 g0
    omega
  have d29983 : (x 2 1).toNat = 1 := by
    have r29984 : (x 2 9).toNat ≤ (x 2 1).toNat := himp _ _ (hp9 2)
    have b29985 := hb (x 2 1)
    have b29986 := hb (x 2 9)
    clear * - r29984 b29985 b29986 d29974
    omega
  have d29987 : (x 3 14).toNat = 0 := by
    have r29988 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b29989 := hb (x 2 1)
    have b29990 := hb (x 3 14)
    clear * - r29988 b29989 b29990 d29983
    omega
  have d29991 : (x 3 6).toNat = 0 := by
    have r29992 : (x 3 6).toNat ≤ (x 3 14).toNat := himp _ _ (hp6 3)
    have b29993 := hb (x 3 6)
    have b29994 := hb (x 3 14)
    clear * - r29992 b29993 b29994 d29987
    omega
  have d29995 : (x 3 6 && x 3 10).toNat = 0 := by
    have r29996 := hand1 (x 3 6) (x 3 10)
    have b29997 := hb (x 3 6)
    have b29998 := hb (x 3 6 && x 3 10)
    clear * - r29996 b29997 b29998 d29991
    omega
  have d29999 : (x 3 2).toNat = 0 := by
    have r30000 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
    have b30001 := hb (x 3 2)
    have b30002 := hb (x 3 14)
    clear * - r30000 b30001 b30002 d29987
    omega
  have d30003 : (x 3 2 && x 3 11).toNat = 0 := by
    have r30004 := hand1 (x 3 2) (x 3 11)
    have b30005 := hb (x 3 2)
    have b30006 := hb (x 3 2 && x 3 11)
    clear * - r30004 b30005 b30006 d29999
    omega
  have d30007 : (x 3 10).toNat = 0 := by
    have r30008 : (x 3 10).toNat ≤ (x 3 2).toNat := himp _ _ (hp10 3)
    have b30009 := hb (x 3 2)
    have b30010 := hb (x 3 10)
    clear * - r30008 b30009 b30010 d29999
    omega
  have d30011 : (x 3 3 && x 3 10).toNat = 0 := by
    have r30012 := hand2 (x 3 3) (x 3 10)
    have b30013 := hb (x 3 10)
    have b30014 := hb (x 3 3 && x 3 10)
    clear * - r30012 b30013 b30014 d30007
    omega
  have d30015 : (x 3 4 && x 3 10).toNat = 0 := by
    have r30016 := hand2 (x 3 4) (x 3 10)
    have b30017 := hb (x 3 10)
    have b30018 := hb (x 3 4 && x 3 10)
    clear * - r30016 b30017 b30018 d30007
    omega
  have d30019 : (x 3 5 && x 3 10).toNat = 0 := by
    have r30020 := hand2 (x 3 5) (x 3 10)
    have b30021 := hb (x 3 10)
    have b30022 := hb (x 3 5 && x 3 10)
    clear * - r30020 b30021 b30022 d30007
    omega
  have d30023 : (x 4 8).toNat = 0 := by
    have r30024 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e30025 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e30026 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e30027 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e30028 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e30029 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e30030 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b30031 := hb (x (-3) 7)
    have b30032 := hb (x (-2) 6)
    have b30033 := hb (x (-1) 5)
    have b30034 := hb (x 0 4)
    have b30035 := hb (x 1 11)
    have b30036 := hb (x 2 10)
    have b30037 := hb (x 3 9)
    have b30038 := hb (x 4 8)
    clear * - r30024 e30025 e30026 e30027 e30028 e30029 e30030 b30031 b30032 b30033 b30034 b30035 b30036 b30037 b30038 g5 g1
    omega
  have d30039 : (x 4 8 && x 4 12).toNat = 0 := by
    have r30040 := hand1 (x 4 8) (x 4 12)
    have b30041 := hb (x 4 8)
    have b30042 := hb (x 4 8 && x 4 12)
    clear * - r30040 b30041 b30042 d30023
    omega
  have d30043 : (x 4 4 && x 4 8).toNat = 0 := by
    have r30044 := hand2 (x 4 4) (x 4 8)
    have b30045 := hb (x 4 8)
    have b30046 := hb (x 4 4 && x 4 8)
    clear * - r30044 b30045 b30046 d30023
    omega
  have d30047 : (x 3 9).toNat = 0 := by
    have r30048 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e30049 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e30050 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e30051 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e30052 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e30053 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e30054 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b30055 := hb (x (-3) 7)
    have b30056 := hb (x (-2) 6)
    have b30057 := hb (x (-1) 5)
    have b30058 := hb (x 0 4)
    have b30059 := hb (x 1 11)
    have b30060 := hb (x 2 10)
    have b30061 := hb (x 3 9)
    have b30062 := hb (x 4 8)
    clear * - r30048 e30049 e30050 e30051 e30052 e30053 e30054 b30055 b30056 b30057 b30058 b30059 b30060 b30061 b30062 d30023 g5 g1
    omega
  have d30063 : (x 3 9 && x 3 13).toNat = 0 := by
    have r30064 := hand1 (x 3 9) (x 3 13)
    have b30065 := hb (x 3 9)
    have b30066 := hb (x 3 9 && x 3 13)
    clear * - r30064 b30065 b30066 d30047
    omega
  have d30067 : (x 3 5 && x 3 9).toNat = 0 := by
    have r30068 := hand2 (x 3 5) (x 3 9)
    have b30069 := hb (x 3 9)
    have b30070 := hb (x 3 5 && x 3 9)
    clear * - r30068 b30069 b30070 d30047
    omega
  have d30071 : (x 2 10).toNat = 0 := by
    have r30072 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e30073 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e30074 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e30075 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e30076 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e30077 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e30078 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b30079 := hb (x (-3) 7)
    have b30080 := hb (x (-2) 6)
    have b30081 := hb (x (-1) 5)
    have b30082 := hb (x 0 4)
    have b30083 := hb (x 1 11)
    have b30084 := hb (x 2 10)
    have b30085 := hb (x 3 9)
    have b30086 := hb (x 4 8)
    clear * - r30072 e30073 e30074 e30075 e30076 e30077 e30078 b30079 b30080 b30081 b30082 b30083 b30084 b30085 b30086 d30023 d30047 g5 g1
    omega
  have d30087 : (x 2 1 && x 2 10).toNat = 0 := by
    have r30088 := hand2 (x 2 1) (x 2 10)
    have b30089 := hb (x 2 10)
    have b30090 := hb (x 2 1 && x 2 10)
    clear * - r30088 b30089 b30090 d30071
    omega
  have d30091 : (x 2 6 && x 2 10).toNat = 0 := by
    have r30092 := hand2 (x 2 6) (x 2 10)
    have b30093 := hb (x 2 10)
    have b30094 := hb (x 2 6 && x 2 10)
    clear * - r30092 b30093 b30094 d30071
    omega
  have d30095 : (x 1 11).toNat = 0 := by
    have r30096 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e30097 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e30098 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e30099 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e30100 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e30101 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e30102 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b30103 := hb (x (-3) 7)
    have b30104 := hb (x (-2) 6)
    have b30105 := hb (x (-1) 5)
    have b30106 := hb (x 0 4)
    have b30107 := hb (x 1 11)
    have b30108 := hb (x 2 10)
    have b30109 := hb (x 3 9)
    have b30110 := hb (x 4 8)
    clear * - r30096 e30097 e30098 e30099 e30100 e30101 e30102 b30103 b30104 b30105 b30106 b30107 b30108 b30109 b30110 d30023 d30047 d30071 g5 g1
    omega
  have d30111 : (x 1 7 && x 1 11).toNat = 0 := by
    have r30112 := hand2 (x 1 7) (x 1 11)
    have b30113 := hb (x 1 11)
    have b30114 := hb (x 1 7 && x 1 11)
    clear * - r30112 b30113 b30114 d30095
    omega
  have d30115 : (x (-2) 6).toNat = 0 := by
    have r30116 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e30117 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e30118 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e30119 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e30120 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e30121 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e30122 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b30123 := hb (x (-3) 7)
    have b30124 := hb (x (-2) 6)
    have b30125 := hb (x (-1) 5)
    have b30126 := hb (x 0 4)
    have b30127 := hb (x 1 11)
    have b30128 := hb (x 2 10)
    have b30129 := hb (x 3 9)
    have b30130 := hb (x 4 8)
    clear * - r30116 e30117 e30118 e30119 e30120 e30121 e30122 b30123 b30124 b30125 b30126 b30127 b30128 b30129 b30130 d30023 d30047 d30071 d30095 g5 g1
    omega
  have d30131 : (x (-3) 7).toNat = 0 := by
    have r30132 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e30133 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e30134 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e30135 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e30136 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e30137 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e30138 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b30139 := hb (x (-3) 7)
    have b30140 := hb (x (-2) 6)
    have b30141 := hb (x (-1) 5)
    have b30142 := hb (x 0 4)
    have b30143 := hb (x 1 11)
    have b30144 := hb (x 2 10)
    have b30145 := hb (x 3 9)
    have b30146 := hb (x 4 8)
    clear * - r30132 e30133 e30134 e30135 e30136 e30137 e30138 b30139 b30140 b30141 b30142 b30143 b30144 b30145 b30146 d30023 d30047 d30071 d30095 g5 g1 d30115
    omega
  have d30147 : (x 3 8).toNat = 0 := by
    have r30148 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e30149 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
    have e30150 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
    have e30151 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
    have e30152 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
    have e30153 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
    have e30154 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
    have b30155 := hb (x (-4) 7)
    have b30156 := hb (x (-3) 6)
    have b30157 := hb (x (-2) 5)
    have b30158 := hb (x (-1) 4)
    have b30159 := hb (x 0 11)
    have b30160 := hb (x 1 10)
    have b30161 := hb (x 2 9)
    have b30162 := hb (x 3 8)
    clear * - r30148 e30149 e30150 e30151 e30152 e30153 e30154 b30155 b30156 b30157 b30158 b30159 b30160 b30161 b30162 d29974 d29795 g7
    omega
  have d30163 : (x 3 8 && x 3 12).toNat = 0 := by
    have r30164 := hand1 (x 3 8) (x 3 12)
    have b30165 := hb (x 3 8)
    have b30166 := hb (x 3 8 && x 3 12)
    clear * - r30164 b30165 b30166 d30147
    omega
  have d30167 : (x (-1) 4).toNat = 0 := by
    have r30168 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e30169 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
    have e30170 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
    have e30171 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
    have e30172 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
    have e30173 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
    have e30174 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
    have b30175 := hb (x (-4) 7)
    have b30176 := hb (x (-3) 6)
    have b30177 := hb (x (-2) 5)
    have b30178 := hb (x (-1) 4)
    have b30179 := hb (x 0 11)
    have b30180 := hb (x 1 10)
    have b30181 := hb (x 2 9)
    have b30182 := hb (x 3 8)
    clear * - r30168 e30169 e30170 e30171 e30172 e30173 e30174 b30175 b30176 b30177 b30178 b30179 b30180 b30181 b30182 d30147 d29974 d29795 g7
    omega
  have d30183 : (x (-1) 4 && x (-1) 8).toNat = 0 := by
    have r30184 := hand1 (x (-1) 4) (x (-1) 8)
    have b30185 := hb (x (-1) 4)
    have b30186 := hb (x (-1) 4 && x (-1) 8)
    clear * - r30184 b30185 b30186 d30167
    omega
  have d30187 : (x (-2) 5).toNat = 0 := by
    have r30188 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e30189 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
    have e30190 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
    have e30191 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
    have e30192 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
    have e30193 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
    have e30194 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
    have b30195 := hb (x (-4) 7)
    have b30196 := hb (x (-3) 6)
    have b30197 := hb (x (-2) 5)
    have b30198 := hb (x (-1) 4)
    have b30199 := hb (x 0 11)
    have b30200 := hb (x 1 10)
    have b30201 := hb (x 2 9)
    have b30202 := hb (x 3 8)
    clear * - r30188 e30189 e30190 e30191 e30192 e30193 e30194 b30195 b30196 b30197 b30198 b30199 b30200 b30201 b30202 d30147 d29974 d29795 g7 d30167
    omega
  have d30203 : (x (-2) 5 && x (-2) 14).toNat = 0 := by
    have r30204 := hand1 (x (-2) 5) (x (-2) 14)
    have b30205 := hb (x (-2) 5)
    have b30206 := hb (x (-2) 5 && x (-2) 14)
    clear * - r30204 b30205 b30206 d30187
    omega
  have d30207 : (x (-2) 5 && x (-2) 9).toNat = 0 := by
    have r30208 := hand1 (x (-2) 5) (x (-2) 9)
    have b30209 := hb (x (-2) 5)
    have b30210 := hb (x (-2) 5 && x (-2) 9)
    clear * - r30208 b30209 b30210 d30187
    omega
  have d30211 : (x (-3) 6).toNat = 0 := by
    have r30212 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e30213 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
    have e30214 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
    have e30215 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
    have e30216 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
    have e30217 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
    have e30218 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
    have b30219 := hb (x (-4) 7)
    have b30220 := hb (x (-3) 6)
    have b30221 := hb (x (-2) 5)
    have b30222 := hb (x (-1) 4)
    have b30223 := hb (x 0 11)
    have b30224 := hb (x 1 10)
    have b30225 := hb (x 2 9)
    have b30226 := hb (x 3 8)
    clear * - r30212 e30213 e30214 e30215 e30216 e30217 e30218 b30219 b30220 b30221 b30222 b30223 b30224 b30225 b30226 d30147 d29974 d29795 g7 d30167 d30187
    omega
  have d30227 : (x (-3) 6 && x (-3) 10).toNat = 0 := by
    have r30228 := hand1 (x (-3) 6) (x (-3) 10)
    have b30229 := hb (x (-3) 6)
    have b30230 := hb (x (-3) 6 && x (-3) 10)
    clear * - r30228 b30229 b30230 d30211
    omega
  have d30231 : (x 0 3 && x 0 12).toNat = 1 := by
    have r30232 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b30233 := hb (x (-3) 6)
    have b30234 := hb (x 3 9)
    have b30235 := hb (x 2 1 && x 2 10)
    have b30236 := hb (x 1 2 && x 1 11)
    have b30237 := hb (x 0 3 && x 0 12)
    have b30238 := hb (x (-1) 4 && x (-1) 13)
    have b30239 := hb (x (-2) 5 && x (-2) 14)
    clear * - r30232 b30233 b30234 b30235 b30236 b30237 b30238 b30239 d30047 d30087 d29787 g41 d30203 d30211
    omega
  have d30240 : (x 0 3).toNat = 1 := by
    have r30241 := hand1 (x 0 3) (x 0 12)
    have b30242 := hb (x 0 3)
    have b30243 := hb (x 0 3 && x 0 12)
    clear * - r30241 b30242 b30243 d30231
    omega
  have d30244 : (x 3 12).toNat = 0 := by
    have r30245 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e30246 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e30247 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b30248 := hb (x 0 3)
    have b30249 := hb (x 1 2)
    have b30250 := hb (x 2 13)
    have b30251 := hb (x 3 12)
    clear * - r30245 e30246 e30247 b30248 b30249 b30250 b30251 d29783 d30240
    omega
  have d30252 : (x 3 3 && x 3 12).toNat = 0 := by
    have r30253 := hand2 (x 3 3) (x 3 12)
    have b30254 := hb (x 3 12)
    have b30255 := hb (x 3 3 && x 3 12)
    clear * - r30253 b30254 b30255 d30244
    omega
  have d30256 : (x 3 5 && x 3 12).toNat = 0 := by
    have r30257 := hand2 (x 3 5) (x 3 12)
    have b30258 := hb (x 3 12)
    have b30259 := hb (x 3 5 && x 3 12)
    clear * - r30257 b30258 b30259 d30244
    omega
  have d30260 : (x 3 4).toNat = 0 := by
    have r30261 : (x 3 4).toNat ≤ (x 3 12).toNat := himp _ _ (hp4 3)
    have b30262 := hb (x 3 4)
    have b30263 := hb (x 3 12)
    clear * - r30261 b30262 b30263 d30244
    omega
  have d30264 : (x 3 4 && x 3 11).toNat = 0 := by
    have r30265 := hand1 (x 3 4) (x 3 11)
    have b30266 := hb (x 3 4)
    have b30267 := hb (x 3 4 && x 3 11)
    clear * - r30265 b30266 b30267 d30260
    omega
  have d30268 : (x 2 13).toNat = 0 := by
    have r30269 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e30270 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e30271 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b30272 := hb (x 0 3)
    have b30273 := hb (x 1 2)
    have b30274 := hb (x 2 13)
    have b30275 := hb (x 3 12)
    clear * - r30269 e30270 e30271 b30272 b30273 b30274 b30275 d30244 d29783 d30240
    omega
  have d30276 : (x 2 6 && x 2 13).toNat = 0 := by
    have r30277 := hand2 (x 2 6) (x 2 13)
    have b30278 := hb (x 2 13)
    have b30279 := hb (x 2 6 && x 2 13)
    clear * - r30277 b30278 b30279 d30268
    omega
  have d30280 : (x 2 9 && x 2 13).toNat = 0 := by
    have r30281 := hand2 (x 2 9) (x 2 13)
    have b30282 := hb (x 2 13)
    have b30283 := hb (x 2 9 && x 2 13)
    clear * - r30281 b30282 b30283 d30268
    omega
  have d30284 : (x 2 5).toNat = 0 := by
    have r30285 : (x 2 5).toNat ≤ (x 2 13).toNat := himp _ _ (hp5 2)
    have b30286 := hb (x 2 5)
    have b30287 := hb (x 2 13)
    clear * - r30285 b30286 b30287 d30268
    omega
  have d30288 : (x 2 5 && x 2 11).toNat = 0 := by
    have r30289 := hand1 (x 2 5) (x 2 11)
    have b30290 := hb (x 2 5)
    have b30291 := hb (x 2 5 && x 2 11)
    clear * - r30289 b30290 b30291 d30284
    omega
  have d30292 : (x (-4) 7).toNat = 0 := by
    have r30293 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e30294 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
    have e30295 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
    have e30296 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
    have e30297 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
    have e30298 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
    have e30299 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
    have b30300 := hb (x (-4) 7)
    have b30301 := hb (x (-3) 6)
    have b30302 := hb (x (-2) 5)
    have b30303 := hb (x (-1) 4)
    have b30304 := hb (x 0 11)
    have b30305 := hb (x 1 10)
    have b30306 := hb (x 2 9)
    have b30307 := hb (x 3 8)
    clear * - r30293 e30294 e30295 e30296 e30297 e30298 e30299 b30300 b30301 b30302 b30303 b30304 b30305 b30306 b30307 d30147 d29974 d29795 g7 d30167 d30187 d30211
    omega
  have d30308 : (x (-4) 7 && x (-4) 12).toNat = 0 := by
    have r30309 := hand1 (x (-4) 7) (x (-4) 12)
    have b30310 := hb (x (-4) 7)
    have b30311 := hb (x (-4) 7 && x (-4) 12)
    clear * - r30309 b30310 b30311 d30292
    omega
  have d30312 : (x (-4) 7 && x (-4) 11).toNat = 0 := by
    have r30313 := hand1 (x (-4) 7) (x (-4) 11)
    have b30314 := hb (x (-4) 7)
    have b30315 := hb (x (-4) 7 && x (-4) 11)
    clear * - r30313 b30314 b30315 d30292
    omega
  have d30316 : (x 0 8).toNat = 0 := by
    have r30317 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e30318 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e30319 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e30320 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e30321 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e30322 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e30323 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b30324 := hb (x (-7) 7)
    have b30325 := hb (x (-6) 6)
    have b30326 := hb (x (-5) 5)
    have b30327 := hb (x (-4) 4)
    have b30328 := hb (x (-3) 11)
    have b30329 := hb (x (-2) 10)
    have b30330 := hb (x (-1) 9)
    have b30331 := hb (x 0 8)
    clear * - r30317 e30318 e30319 e30320 e30321 e30322 e30323 b30324 b30325 b30326 b30327 b30328 b30329 b30330 b30331 g2 d29742 d29871 d29883 d29914
    omega
  have d30332 : (x 0 8 && x 0 14).toNat = 0 := by
    have r30333 := hand1 (x 0 8) (x 0 14)
    have b30334 := hb (x 0 8)
    have b30335 := hb (x 0 8 && x 0 14)
    clear * - r30333 b30334 b30335 d30316
    omega
  have d30336 : (x 0 2 && x 0 8).toNat = 0 := by
    have r30337 := hand2 (x 0 2) (x 0 8)
    have b30338 := hb (x 0 8)
    have b30339 := hb (x 0 2 && x 0 8)
    clear * - r30337 b30338 b30339 d30316
    omega
  have d30340 : (x 0 8 && x 0 13).toNat = 0 := by
    have r30341 := hand1 (x 0 8) (x 0 13)
    have b30342 := hb (x 0 8)
    have b30343 := hb (x 0 8 && x 0 13)
    clear * - r30341 b30342 b30343 d30316
    omega
  have d30344 : (x 0 3 && x 0 8).toNat = 0 := by
    have r30345 := hand2 (x 0 3) (x 0 8)
    have b30346 := hb (x 0 8)
    have b30347 := hb (x 0 3 && x 0 8)
    clear * - r30345 b30346 b30347 d30316
    omega
  have d30348 : (x 0 8 && x 0 12).toNat = 0 := by
    have r30349 := hand1 (x 0 8) (x 0 12)
    have b30350 := hb (x 0 8)
    have b30351 := hb (x 0 8 && x 0 12)
    clear * - r30349 b30350 b30351 d30316
    omega
  have d30352 : (x 0 4 && x 0 8).toNat = 0 := by
    have r30353 := hand2 (x 0 4) (x 0 8)
    have b30354 := hb (x 0 8)
    have b30355 := hb (x 0 4 && x 0 8)
    clear * - r30353 b30354 b30355 d30316
    omega
  have d30356 : (x (-6) 6).toNat = 0 := by
    have r30357 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e30358 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e30359 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e30360 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e30361 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e30362 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e30363 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b30364 := hb (x (-7) 7)
    have b30365 := hb (x (-6) 6)
    have b30366 := hb (x (-5) 5)
    have b30367 := hb (x (-4) 4)
    have b30368 := hb (x (-3) 11)
    have b30369 := hb (x (-2) 10)
    have b30370 := hb (x (-1) 9)
    have b30371 := hb (x 0 8)
    clear * - r30357 e30358 e30359 e30360 e30361 e30362 e30363 b30364 b30365 b30366 b30367 b30368 b30369 b30370 b30371 d30316 g2 d29742 d29871 d29883 d29914
    omega
  cases h30372 : x 0 5
  · have f30373 : (x 0 5).toNat = 0 := by rw [h30372]; rfl
    have d30374 : (x 0 5 && x 0 14).toNat = 0 := by
      have r30375 := hand1 (x 0 5) (x 0 14)
      have b30376 := hb (x 0 5)
      have b30377 := hb (x 0 5 && x 0 14)
      clear * - r30375 b30376 b30377 f30373
      omega
    cases h30378 : x 0 6
    · have f30379 : (x 0 6).toNat = 0 := by rw [h30378]; rfl
      have d30380 : (x 0 2 && x 0 6).toNat = 0 := by
        have r30381 := hand2 (x 0 2) (x 0 6)
        have b30382 := hb (x 0 6)
        have b30383 := hb (x 0 2 && x 0 6)
        clear * - r30381 b30382 b30383 f30379
        omega
      cases h30384 : x 0 7
      · have f30385 : (x 0 7).toNat = 0 := by rw [h30384]; rfl
        have d30386 : (x 0 3 && x 0 7).toNat = 0 := by
          have r30387 := hand2 (x 0 3) (x 0 7)
          have b30388 := hb (x 0 7)
          have b30389 := hb (x 0 3 && x 0 7)
          clear * - r30387 b30388 b30389 f30385
          omega
        have r30390 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r30391 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r30392 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30393 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
        have e30394 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
        have e30395 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
        have e30396 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
        have e30397 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
        have e30398 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
        have r30399 : (x (-5) 8).toNat + (x (-6) 1 && x (-6) 9).toNat + (x (-7) 2 && x (-7) 10).toNat + (x (-8) 3 && x (-8) 11).toNat + (x (-9) 4 && x (-9) 12).toNat + (x (-10) 5 && x (-10) 13).toNat + (x (-11) 6 && x (-11) 14).toNat + (x (-12) 7).toNat = 1 := by have q := hd8 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30400 : (x (-6) 1 && x (-6) 9).toNat = (x (-6) 9).toNat := handr _ _ (fun h => hp9 (-6) (h))
        have e30401 : (x (-7) 2 && x (-7) 10).toNat = (x (-7) 10).toNat := handr _ _ (fun h => hp10 (-7) (h))
        have e30402 : (x (-8) 3 && x (-8) 11).toNat = (x (-8) 11).toNat := handr _ _ (fun h => hp11 (-8) (h))
        have e30403 : (x (-9) 4 && x (-9) 12).toNat = (x (-9) 4).toNat := handl _ _ (fun h => hp4 (-9) (h))
        have e30404 : (x (-10) 5 && x (-10) 13).toNat = (x (-10) 5).toNat := handl _ _ (fun h => hp5 (-10) (h))
        have e30405 : (x (-11) 6 && x (-11) 14).toNat = (x (-11) 6).toNat := handl _ _ (fun h => hp6 (-11) (h))
        have r30406 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30407 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e30408 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e30409 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e30410 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e30411 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e30412 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have r30413 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30414 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
        have e30415 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
        have r30416 : 1 ≤ (x 2 4).toNat + (x 1 1 && x 1 5).toNat + (x 0 2 && x 0 6).toNat + (x (-1) 3 && x (-1) 7).toNat + (x (-2) 4 && x (-2) 8).toNat + (x (-3) 5 && x (-3) 9).toNat + (x (-4) 6 && x (-4) 10).toNat + (x (-5) 7 && x (-5) 11).toNat + (x (-6) 8 && x (-6) 12).toNat + (x (-7) 9 && x (-7) 13).toNat + (x (-8) 10 && x (-8) 14).toNat + (x (-9) 11).toNat := by have q := hcov4 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30417 : (x 1 1 && x 1 5).toNat = (x 1 5).toNat := handr _ _ (fun h => hp13 1 (hp5 1 (h)))
        have e30418 : (x (-8) 10 && x (-8) 14).toNat = (x (-8) 10).toNat := handl _ _ (fun h => hp2 (-8) (hp10 (-8) (h)))
        have r30419 : 1 ≤ (x 3 4).toNat + (x 2 1 && x 2 5).toNat + (x 1 2 && x 1 6).toNat + (x 0 3 && x 0 7).toNat + (x (-1) 4 && x (-1) 8).toNat + (x (-2) 5 && x (-2) 9).toNat + (x (-3) 6 && x (-3) 10).toNat + (x (-4) 7 && x (-4) 11).toNat + (x (-5) 8 && x (-5) 12).toNat + (x (-6) 9 && x (-6) 13).toNat + (x (-7) 10 && x (-7) 14).toNat + (x (-8) 11).toNat := by have q := hcov4 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30420 : (x 2 1 && x 2 5).toNat = (x 2 5).toNat := handr _ _ (fun h => hp13 2 (hp5 2 (h)))
        have e30421 : (x (-7) 10 && x (-7) 14).toNat = (x (-7) 10).toNat := handl _ _ (fun h => hp2 (-7) (hp10 (-7) (h)))
        have r30422 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30423 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
        have e30424 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
        have r30425 : 1 ≤ (x 2 6).toNat + (x 1 1 && x 1 7).toNat + (x 0 2 && x 0 8).toNat + (x (-1) 3 && x (-1) 9).toNat + (x (-2) 4 && x (-2) 10).toNat + (x (-3) 5 && x (-3) 11).toNat + (x (-4) 6 && x (-4) 12).toNat + (x (-5) 7 && x (-5) 13).toNat + (x (-6) 8 && x (-6) 14).toNat + (x (-7) 9).toNat := by have q := hcov6 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r30426 : 1 ≤ (x (-5) 9).toNat + (x (-6) 1 && x (-6) 10).toNat + (x (-7) 2 && x (-7) 11).toNat + (x (-8) 3 && x (-8) 12).toNat + (x (-9) 4 && x (-9) 13).toNat + (x (-10) 5 && x (-10) 14).toNat + (x (-11) 6).toNat := by have q := hcov9 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r30427 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r30428 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r30429 : (x (-11) 2).toNat ≤ (x (-11) 14).toNat := himp _ _ (hp2 (-11))
        have r30430 := hand2 (x (-6) 8) (x (-6) 12)
        have r30431 := hand2 (x (-7) 9) (x (-7) 13)
        have r30432 := hand1 (x (-5) 8) (x (-5) 12)
        have r30433 := hand1 (x (-6) 9) (x (-6) 13)
        have r30434 := hand1 (x 2 2) (x 2 6)
        have r30435 := hand1 (x 1 3) (x 1 7)
        have r30436 := hand1 (x (-4) 8) (x (-4) 12)
        have r30437 := hand2 (x 1 1) (x 1 7)
        have r30438 := hand1 (x (-6) 8) (x (-6) 14)
        have r30439 := hand2 (x (-8) 3) (x (-8) 12)
        have r30440 := hand1 (x (-9) 4) (x (-9) 13)
        have r30441 := hand1 (x (-10) 5) (x (-10) 14)
        have r30442 := hand1 (x (-8) 2) (x (-8) 12)
        have r30443 := hand1 (x (-9) 3) (x (-9) 13)
        have r30444 := hand1 (x (-10) 4) (x (-10) 14)
        have r30445 := hand2 (x (-10) 1) (x (-10) 14)
        linarith only [r30390, r30391, r30392, e30393, e30394, e30395, e30396, e30397, e30398, r30399, e30400, e30401, e30402, e30403, e30404, e30405, r30406, e30407, e30408, e30409, e30410, e30411, e30412, r30413, e30414, e30415, r30416, e30417, e30418, r30419, e30420, e30421, r30422, e30423, e30424, r30425, r30426, r30427, r30428, r30429, r30430, r30431, r30432, r30433, r30434, r30435, r30436, r30437, r30438, r30439, r30440, r30441, r30442, r30443, r30444, r30445, d29962, d29938, d30292, d30211, d30131, d30187, d30115, d30167, g1, d30240, g5, d29783, g8, d29983, g10, d30284, d30260, d30380, g12, g13, g14, g15, g16, d29779, d30386, d30183, d30207, d30227, d30312, d30352, g17, d29750, d29879, d29910, d30336, g24, g25, g26, g27, g28, d29942, d29970, d29966]
      · have f30545 : (x 0 7).toNat = 1 := by rw [h30384]; rfl
        have d30546 : (x 7 8).toNat = 0 := by
          have r30547 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30548 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e30549 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e30550 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e30551 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e30552 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e30553 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have b30554 := hb (x 0 7)
          have b30555 := hb (x 1 6)
          have b30556 := hb (x 2 5)
          have b30557 := hb (x 3 4)
          have b30558 := hb (x 4 11)
          have b30559 := hb (x 5 10)
          have b30560 := hb (x 6 9)
          have b30561 := hb (x 7 8)
          clear * - r30547 e30548 e30549 e30550 e30551 e30552 e30553 b30554 b30555 b30556 b30557 b30558 b30559 b30560 b30561 d30260 d30284 d29771 f30545
          omega
        have d30562 : (x 6 9).toNat = 0 := by
          have r30563 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30564 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e30565 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e30566 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e30567 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e30568 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e30569 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have b30570 := hb (x 0 7)
          have b30571 := hb (x 1 6)
          have b30572 := hb (x 2 5)
          have b30573 := hb (x 3 4)
          have b30574 := hb (x 4 11)
          have b30575 := hb (x 5 10)
          have b30576 := hb (x 6 9)
          have b30577 := hb (x 7 8)
          clear * - r30563 e30564 e30565 e30566 e30567 e30568 e30569 b30570 b30571 b30572 b30573 b30574 b30575 b30576 b30577 d30546 d30260 d30284 d29771 f30545
          omega
        have d30578 : (x 5 10).toNat = 0 := by
          have r30579 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30580 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e30581 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e30582 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e30583 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e30584 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e30585 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have b30586 := hb (x 0 7)
          have b30587 := hb (x 1 6)
          have b30588 := hb (x 2 5)
          have b30589 := hb (x 3 4)
          have b30590 := hb (x 4 11)
          have b30591 := hb (x 5 10)
          have b30592 := hb (x 6 9)
          have b30593 := hb (x 7 8)
          clear * - r30579 e30580 e30581 e30582 e30583 e30584 e30585 b30586 b30587 b30588 b30589 b30590 b30591 b30592 b30593 d30546 d30562 d30260 d30284 d29771 f30545
          omega
        have d30594 : (x 5 1 && x 5 10).toNat = 0 := by
          have r30595 := hand2 (x 5 1) (x 5 10)
          have b30596 := hb (x 5 10)
          have b30597 := hb (x 5 1 && x 5 10)
          clear * - r30595 b30596 b30597 d30578
          omega
        have d30598 : (x 4 2 && x 4 11).toNat = 1 := by
          have r30599 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b30600 := hb (x 0 6)
          have b30601 := hb (x 6 9)
          have b30602 := hb (x 5 1 && x 5 10)
          have b30603 := hb (x 4 2 && x 4 11)
          have b30604 := hb (x 3 3 && x 3 12)
          have b30605 := hb (x 2 4 && x 2 13)
          have b30606 := hb (x 1 5 && x 1 14)
          clear * - r30599 b30600 b30601 b30602 b30603 b30604 b30605 b30606 d30562 d30594 d30252 g44 g45 f30379
          omega
        have d30607 : (x 4 11).toNat = 1 := by
          have r30608 := hand2 (x 4 2) (x 4 11)
          have b30609 := hb (x 4 11)
          have b30610 := hb (x 4 2 && x 4 11)
          clear * - r30608 b30609 b30610 d30598
          omega
        have r30611 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30612 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e30613 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e30614 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e30615 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e30616 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e30617 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b30618 := hb (x 0 7)
        have b30619 := hb (x 1 6)
        have b30620 := hb (x 2 5)
        have b30621 := hb (x 3 4)
        have b30622 := hb (x 4 11)
        have b30623 := hb (x 5 10)
        have b30624 := hb (x 6 9)
        have b30625 := hb (x 7 8)
        linarith only [r30611, e30612, e30613, e30614, e30615, e30616, e30617, b30618, b30619, b30620, b30621, b30622, b30623, b30624, b30625, d30546, d30562, d30578, d30607, d30260, d30284, d29771, f30545]
    · have f30626 : (x 0 6).toNat = 1 := by rw [h30378]; rfl
      have d30627 : (x 6 8).toNat = 0 := by
        have r30628 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30629 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e30630 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e30631 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e30632 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e30633 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e30634 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b30635 := hb (x (-1) 7)
        have b30636 := hb (x 0 6)
        have b30637 := hb (x 1 5)
        have b30638 := hb (x 2 4)
        have b30639 := hb (x 3 11)
        have b30640 := hb (x 4 10)
        have b30641 := hb (x 5 9)
        have b30642 := hb (x 6 8)
        clear * - r30628 e30629 e30630 e30631 e30632 e30633 e30634 b30635 b30636 b30637 b30638 b30639 b30640 b30641 b30642 g10 g8 f30626
        omega
      have d30643 : (x 5 9).toNat = 0 := by
        have r30644 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30645 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e30646 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e30647 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e30648 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e30649 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e30650 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b30651 := hb (x (-1) 7)
        have b30652 := hb (x 0 6)
        have b30653 := hb (x 1 5)
        have b30654 := hb (x 2 4)
        have b30655 := hb (x 3 11)
        have b30656 := hb (x 4 10)
        have b30657 := hb (x 5 9)
        have b30658 := hb (x 6 8)
        clear * - r30644 e30645 e30646 e30647 e30648 e30649 e30650 b30651 b30652 b30653 b30654 b30655 b30656 b30657 b30658 d30627 g10 g8 f30626
        omega
      have d30659 : (x 4 10).toNat = 0 := by
        have r30660 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30661 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e30662 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e30663 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e30664 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e30665 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e30666 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b30667 := hb (x (-1) 7)
        have b30668 := hb (x 0 6)
        have b30669 := hb (x 1 5)
        have b30670 := hb (x 2 4)
        have b30671 := hb (x 3 11)
        have b30672 := hb (x 4 10)
        have b30673 := hb (x 5 9)
        have b30674 := hb (x 6 8)
        clear * - r30660 e30661 e30662 e30663 e30664 e30665 e30666 b30667 b30668 b30669 b30670 b30671 b30672 b30673 b30674 d30627 d30643 g10 g8 f30626
        omega
      have d30675 : (x 4 1 && x 4 10).toNat = 0 := by
        have r30676 := hand2 (x 4 1) (x 4 10)
        have b30677 := hb (x 4 10)
        have b30678 := hb (x 4 1 && x 4 10)
        clear * - r30676 b30677 b30678 d30659
        omega
      have d30679 : (x (-1) 6).toNat = 1 := by
        have r30680 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b30681 := hb (x (-1) 6)
        have b30682 := hb (x 5 9)
        have b30683 := hb (x 4 1 && x 4 10)
        have b30684 := hb (x 3 2 && x 3 11)
        have b30685 := hb (x 2 3 && x 2 12)
        have b30686 := hb (x 1 4 && x 1 13)
        have b30687 := hb (x 0 5 && x 0 14)
        clear * - r30680 b30681 b30682 b30683 b30684 b30685 b30686 b30687 d30643 d30675 d30003 g42 g43 d30374
        omega
      have d30688 : (x (-1) 14).toNat = 1 := by
        have r30689 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
        have b30690 := hb (x (-1) 6)
        have b30691 := hb (x (-1) 14)
        clear * - r30689 b30690 b30691 d30679
        omega
      have d30692 : (x (-2) 1).toNat = 0 := by
        have r30693 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b30694 := hb (x (-2) 1)
        have b30695 := hb (x (-1) 14)
        clear * - r30693 b30694 b30695 d30688
        omega
      have d30696 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
        have r30697 := hand1 (x (-2) 1) (x (-2) 14)
        have b30698 := hb (x (-2) 1)
        have b30699 := hb (x (-2) 1 && x (-2) 14)
        clear * - r30697 b30698 b30699 d30692
        omega
      have d30700 : (x (-3) 2).toNat = 1 := by
        have r30701 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b30702 := hb (x (-3) 2)
        have b30703 := hb (x (-1) 13)
        have b30704 := hb (x (-2) 1 && x (-2) 14)
        clear * - r30701 b30702 b30703 b30704 g4 d30696
        omega
      have d30705 : (x (-3) 14).toNat = 1 := by
        have r30706 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
        have b30707 := hb (x (-3) 2)
        have b30708 := hb (x (-3) 14)
        clear * - r30706 b30707 b30708 d30700
        omega
      have d30709 : (x (-4) 1).toNat = 0 := by
        have r30710 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b30711 := hb (x (-4) 1)
        have b30712 := hb (x (-3) 14)
        clear * - r30710 b30711 b30712 d30705
        omega
      have d30713 : (x (-4) 1 && x (-4) 12).toNat = 0 := by
        have r30714 := hand1 (x (-4) 1) (x (-4) 12)
        have b30715 := hb (x (-4) 1)
        have b30716 := hb (x (-4) 1 && x (-4) 12)
        clear * - r30714 b30715 b30716 d30709
        omega
      have d30717 : (x (-4) 13).toNat = 0 := by
        have r30718 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
        have b30719 := hb (x (-4) 1)
        have b30720 := hb (x (-4) 13)
        clear * - r30718 b30719 b30720 d30709
        omega
      have d30721 : (x (-4) 5).toNat = 0 := by
        have r30722 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
        have b30723 := hb (x (-4) 5)
        have b30724 := hb (x (-4) 13)
        clear * - r30722 b30723 b30724 d30717
        omega
      have d30725 : (x (-3) 4 && x (-3) 14).toNat = 1 := by
        have r30726 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b30727 := hb (x (-4) 5)
        have b30728 := hb (x 1 10)
        have b30729 := hb (x 0 1 && x 0 11)
        have b30730 := hb (x (-1) 2 && x (-1) 12)
        have b30731 := hb (x (-2) 3 && x (-2) 13)
        have b30732 := hb (x (-3) 4 && x (-3) 14)
        clear * - r30726 b30727 b30728 b30729 b30730 b30731 b30732 d29795 g46 d29831 d29847 d30721
        omega
      have d30733 : (x (-3) 4).toNat = 1 := by
        have r30734 := hand1 (x (-3) 4) (x (-3) 14)
        have b30735 := hb (x (-3) 4)
        have b30736 := hb (x (-3) 4 && x (-3) 14)
        clear * - r30734 b30735 b30736 d30725
        omega
      have d30737 : (x (-3) 12).toNat = 1 := by
        have r30738 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
        have b30739 := hb (x (-3) 4)
        have b30740 := hb (x (-3) 12)
        clear * - r30738 b30739 b30740 d30733
        omega
      have d30741 : (x (-5) 1 && x (-5) 14).toNat = 1 := by
        have r30742 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b30743 := hb (x (-6) 2)
        have b30744 := hb (x (-4) 13)
        have b30745 := hb (x (-5) 1 && x (-5) 14)
        clear * - r30742 b30743 b30744 b30745 d30717 d29922
        omega
      have d30746 : (x (-5) 14).toNat = 1 := by
        have r30747 := hand2 (x (-5) 1) (x (-5) 14)
        have b30748 := hb (x (-5) 14)
        have b30749 := hb (x (-5) 1 && x (-5) 14)
        clear * - r30747 b30748 b30749 d30741
        omega
      have d30750 : (x (-6) 1).toNat = 0 := by
        have r30751 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b30752 := hb (x (-6) 1)
        have b30753 := hb (x (-5) 14)
        clear * - r30751 b30752 b30753 d30746
        omega
      have d30754 : (x (-6) 1 && x (-6) 14).toNat = 0 := by
        have r30755 := hand1 (x (-6) 1) (x (-6) 14)
        have b30756 := hb (x (-6) 1)
        have b30757 := hb (x (-6) 1 && x (-6) 14)
        clear * - r30755 b30756 b30757 d30750
        omega
      have d30758 : (x (-7) 2).toNat = 1 := by
        have r30759 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b30760 := hb (x (-7) 2)
        have b30761 := hb (x (-5) 13)
        have b30762 := hb (x (-6) 1 && x (-6) 14)
        clear * - r30759 b30760 b30761 b30762 d29894 d30754
        omega
      have d30763 : (x (-7) 14).toNat = 1 := by
        have r30764 : (x (-7) 2).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp2 (-7))
        have b30765 := hb (x (-7) 2)
        have b30766 := hb (x (-7) 14)
        clear * - r30764 b30765 b30766 d30758
        omega
      have d30767 : (x (-8) 1).toNat = 0 := by
        have r30768 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b30769 := hb (x (-8) 1)
        have b30770 := hb (x (-7) 14)
        clear * - r30768 b30769 b30770 d30763
        omega
      have d30771 : (x (-8) 1 && x (-8) 14).toNat = 0 := by
        have r30772 := hand1 (x (-8) 1) (x (-8) 14)
        have b30773 := hb (x (-8) 1)
        have b30774 := hb (x (-8) 1 && x (-8) 14)
        clear * - r30772 b30773 b30774 d30767
        omega
      have d30775 : (x (-8) 1 && x (-8) 12).toNat = 0 := by
        have r30776 := hand1 (x (-8) 1) (x (-8) 12)
        have b30777 := hb (x (-8) 1)
        have b30778 := hb (x (-8) 1 && x (-8) 12)
        clear * - r30776 b30777 b30778 d30767
        omega
      have d30779 : (x (-8) 13).toNat = 0 := by
        have r30780 : (x (-8) 13).toNat ≤ (x (-8) 1).toNat := himp _ _ (hp13 (-8))
        have b30781 := hb (x (-8) 1)
        have b30782 := hb (x (-8) 13)
        clear * - r30780 b30781 b30782 d30767
        omega
      have d30783 : (x (-8) 4 && x (-8) 13).toNat = 0 := by
        have r30784 := hand2 (x (-8) 4) (x (-8) 13)
        have b30785 := hb (x (-8) 13)
        have b30786 := hb (x (-8) 4 && x (-8) 13)
        clear * - r30784 b30785 b30786 d30779
        omega
      have d30787 : (x (-5) 12).toNat = 0 := by
        have r30788 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30789 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
        have e30790 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
        have b30791 := hb (x (-8) 3)
        have b30792 := hb (x (-7) 2)
        have b30793 := hb (x (-6) 13)
        have b30794 := hb (x (-5) 12)
        clear * - r30788 e30789 e30790 b30791 b30792 b30793 b30794 d30758
        omega
      have d30795 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
        have r30796 := hand2 (x (-5) 1) (x (-5) 12)
        have b30797 := hb (x (-5) 12)
        have b30798 := hb (x (-5) 1 && x (-5) 12)
        clear * - r30796 b30797 b30798 d30787
        omega
      have d30799 : (x (-5) 2).toNat = 0 := by
        have r30800 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30801 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
        have e30802 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
        have b30803 := hb (x (-6) 3)
        have b30804 := hb (x (-5) 2)
        have b30805 := hb (x (-4) 13)
        have b30806 := hb (x (-3) 12)
        clear * - r30800 e30801 e30802 b30803 b30804 b30805 b30806 d30737 d30717
        omega
      have d30807 : (x (-5) 10).toNat = 0 := by
        have r30808 : (x (-5) 10).toNat ≤ (x (-5) 2).toNat := himp _ _ (hp10 (-5))
        have b30809 := hb (x (-5) 2)
        have b30810 := hb (x (-5) 10)
        clear * - r30808 b30809 b30810 d30799
        omega
      have d30811 : (x (-5) 1 && x (-5) 10).toNat = 0 := by
        have r30812 := hand2 (x (-5) 1) (x (-5) 10)
        have b30813 := hb (x (-5) 10)
        have b30814 := hb (x (-5) 1 && x (-5) 10)
        clear * - r30812 b30813 b30814 d30807
        omega
      have d30815 : (x (-6) 3).toNat = 0 := by
        have r30816 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30817 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
        have e30818 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
        have b30819 := hb (x (-6) 3)
        have b30820 := hb (x (-5) 2)
        have b30821 := hb (x (-4) 13)
        have b30822 := hb (x (-3) 12)
        clear * - r30816 e30817 e30818 b30819 b30820 b30821 b30822 d30737 d30717 d30799
        omega
      have d30823 : (x (-6) 3 && x (-6) 14).toNat = 0 := by
        have r30824 := hand1 (x (-6) 3) (x (-6) 14)
        have b30825 := hb (x (-6) 3)
        have b30826 := hb (x (-6) 3 && x (-6) 14)
        clear * - r30824 b30825 b30826 d30815
        omega
      have d30827 : (x (-7) 4).toNat = 1 := by
        have r30828 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := by have q := hcov11 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b30829 := hb (x (-7) 4)
        have b30830 := hb (x (-3) 11)
        have b30831 := hb (x (-4) 1 && x (-4) 12)
        have b30832 := hb (x (-5) 2 && x (-5) 13)
        have b30833 := hb (x (-6) 3 && x (-6) 14)
        clear * - r30828 b30829 b30830 b30831 b30832 b30833 d29871 d30713 d29902 d30823
        omega
      have d30834 : (x (-7) 12).toNat = 1 := by
        have r30835 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
        have b30836 := hb (x (-7) 4)
        have b30837 := hb (x (-7) 12)
        clear * - r30835 b30836 b30837 d30827
        omega
      have d30838 : (x (-9) 2).toNat = 0 := by
        have r30839 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30840 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
        have e30841 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
        have b30842 := hb (x (-10) 3)
        have b30843 := hb (x (-9) 2)
        have b30844 := hb (x (-8) 13)
        have b30845 := hb (x (-7) 12)
        clear * - r30839 e30840 e30841 b30842 b30843 b30844 b30845 d30834 d30779
        omega
      have d30846 : (x (-9) 2 && x (-9) 13).toNat = 0 := by
        have r30847 := hand1 (x (-9) 2) (x (-9) 13)
        have b30848 := hb (x (-9) 2)
        have b30849 := hb (x (-9) 2 && x (-9) 13)
        clear * - r30847 b30848 b30849 d30838
        omega
      have d30850 : (x (-7) 13).toNat = 1 := by
        have r30851 : 1 ≤ (x (-7) 13).toNat + (x (-8) 1 && x (-8) 14).toNat + (x (-9) 2).toNat := by have q := hcov13 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b30852 := hb (x (-9) 2)
        have b30853 := hb (x (-7) 13)
        have b30854 := hb (x (-8) 1 && x (-8) 14)
        clear * - r30851 b30852 b30853 b30854 d30771 d30838
        omega
      have d30855 : (x (-6) 12).toNat = 0 := by
        have r30856 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30857 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
        have e30858 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
        have b30859 := hb (x (-9) 3)
        have b30860 := hb (x (-8) 2)
        have b30861 := hb (x (-7) 13)
        have b30862 := hb (x (-6) 12)
        clear * - r30856 e30857 e30858 b30859 b30860 b30861 b30862 d30850
        omega
      have d30863 : (x (-8) 2).toNat = 0 := by
        have r30864 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30865 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
        have e30866 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
        have b30867 := hb (x (-9) 3)
        have b30868 := hb (x (-8) 2)
        have b30869 := hb (x (-7) 13)
        have b30870 := hb (x (-6) 12)
        clear * - r30864 e30865 e30866 b30867 b30868 b30869 b30870 d30855 d30850
        omega
      have d30871 : (x (-8) 10).toNat = 0 := by
        have r30872 : (x (-8) 10).toNat ≤ (x (-8) 2).toNat := himp _ _ (hp10 (-8))
        have b30873 := hb (x (-8) 2)
        have b30874 := hb (x (-8) 10)
        clear * - r30872 b30873 b30874 d30863
        omega
      have d30875 : (x (-9) 3).toNat = 0 := by
        have r30876 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30877 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
        have e30878 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
        have b30879 := hb (x (-9) 3)
        have b30880 := hb (x (-8) 2)
        have b30881 := hb (x (-7) 13)
        have b30882 := hb (x (-6) 12)
        clear * - r30876 e30877 e30878 b30879 b30880 b30881 b30882 d30855 d30850 d30863
        omega
      have d30883 : (x (-9) 11).toNat = 0 := by
        have r30884 : (x (-9) 11).toNat ≤ (x (-9) 3).toNat := himp _ _ (hp11 (-9))
        have b30885 := hb (x (-9) 3)
        have b30886 := hb (x (-9) 11)
        clear * - r30884 b30885 b30886 d30875
        omega
      have d30887 : (x (-9) 1 && x (-9) 11).toNat = 0 := by
        have r30888 := hand2 (x (-9) 1) (x (-9) 11)
        have b30889 := hb (x (-9) 11)
        have b30890 := hb (x (-9) 1 && x (-9) 11)
        clear * - r30888 b30889 b30890 d30883
        omega
      have d30891 : (x (-10) 3).toNat = 0 := by
        have r30892 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30893 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
        have e30894 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
        have b30895 := hb (x (-10) 3)
        have b30896 := hb (x (-9) 2)
        have b30897 := hb (x (-8) 13)
        have b30898 := hb (x (-7) 12)
        clear * - r30892 e30893 e30894 b30895 b30896 b30897 b30898 d30834 d30779 d30838
        omega
      have d30899 : (x (-10) 3 && x (-10) 14).toNat = 0 := by
        have r30900 := hand1 (x (-10) 3) (x (-10) 14)
        have b30901 := hb (x (-10) 3)
        have b30902 := hb (x (-10) 3 && x (-10) 14)
        clear * - r30900 b30901 b30902 d30891
        omega
      have d30903 : (x (-11) 4).toNat = 1 := by
        have r30904 : 1 ≤ (x (-7) 11).toNat + (x (-8) 1 && x (-8) 12).toNat + (x (-9) 2 && x (-9) 13).toNat + (x (-10) 3 && x (-10) 14).toNat + (x (-11) 4).toNat := by have q := hcov11 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b30905 := hb (x (-11) 4)
        have b30906 := hb (x (-7) 11)
        have b30907 := hb (x (-8) 1 && x (-8) 12)
        have b30908 := hb (x (-9) 2 && x (-9) 13)
        have b30909 := hb (x (-10) 3 && x (-10) 14)
        clear * - r30904 b30905 b30906 b30907 b30908 b30909 d29962 d30775 d30846 d30899
        omega
      have d30910 : (x (-11) 12).toNat = 1 := by
        have r30911 : (x (-11) 4).toNat ≤ (x (-11) 12).toNat := himp _ _ (hp4 (-11))
        have b30912 := hb (x (-11) 4)
        have b30913 := hb (x (-11) 12)
        clear * - r30911 b30912 b30913 d30903
        omega
      have d30914 : (x (-12) 13).toNat = 0 := by
        have r30915 : (x (-11) 12).toNat + (x (-12) 1 && x (-12) 13).toNat + (x (-13) 2 && x (-13) 14).toNat + (x (-14) 3).toNat = 1 := by have q := hd12 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30916 : (x (-12) 1 && x (-12) 13).toNat = (x (-12) 13).toNat := handr _ _ (fun h => hp13 (-12) (h))
        have e30917 : (x (-13) 2 && x (-13) 14).toNat = (x (-13) 2).toNat := handl _ _ (fun h => hp2 (-13) (h))
        have b30918 := hb (x (-14) 3)
        have b30919 := hb (x (-13) 2)
        have b30920 := hb (x (-12) 13)
        have b30921 := hb (x (-11) 12)
        clear * - r30915 e30916 e30917 b30918 b30919 b30920 b30921 d30910
        omega
      have d30922 : (x (-13) 2).toNat = 0 := by
        have r30923 : (x (-11) 12).toNat + (x (-12) 1 && x (-12) 13).toNat + (x (-13) 2 && x (-13) 14).toNat + (x (-14) 3).toNat = 1 := by have q := hd12 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30924 : (x (-12) 1 && x (-12) 13).toNat = (x (-12) 13).toNat := handr _ _ (fun h => hp13 (-12) (h))
        have e30925 : (x (-13) 2 && x (-13) 14).toNat = (x (-13) 2).toNat := handl _ _ (fun h => hp2 (-13) (h))
        have b30926 := hb (x (-14) 3)
        have b30927 := hb (x (-13) 2)
        have b30928 := hb (x (-12) 13)
        have b30929 := hb (x (-11) 12)
        clear * - r30923 e30924 e30925 b30926 b30927 b30928 b30929 d30910 d30914
        omega
      have d30930 : (x (-4) 9).toNat = 0 := by
        have r30931 : (x (-4) 9).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp9 (-4))
        have b30932 := hb (x (-4) 1)
        have b30933 := hb (x (-4) 9)
        clear * - r30931 b30932 b30933 d30709
        omega
      have d30934 : (x (-1) 12).toNat = 0 := by
        have r30935 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30936 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e30937 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b30938 := hb (x (-4) 3)
        have b30939 := hb (x (-3) 2)
        have b30940 := hb (x (-2) 13)
        have b30941 := hb (x (-1) 12)
        clear * - r30935 e30936 e30937 b30938 b30939 b30940 b30941 d30700
        omega
      have d30942 : (x (-2) 13).toNat = 0 := by
        have r30943 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30944 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e30945 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b30946 := hb (x (-4) 3)
        have b30947 := hb (x (-3) 2)
        have b30948 := hb (x (-2) 13)
        have b30949 := hb (x (-1) 12)
        clear * - r30943 e30944 e30945 b30946 b30947 b30948 b30949 d30934 d30700
        omega
      have d30950 : (x (-4) 3).toNat = 0 := by
        have r30951 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30952 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e30953 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b30954 := hb (x (-4) 3)
        have b30955 := hb (x (-3) 2)
        have b30956 := hb (x (-2) 13)
        have b30957 := hb (x (-1) 12)
        clear * - r30951 e30952 e30953 b30954 b30955 b30956 b30957 d30934 d30942 d30700
        omega
      have d30958 : (x (-4) 11).toNat = 0 := by
        have r30959 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
        have b30960 := hb (x (-4) 3)
        have b30961 := hb (x (-4) 11)
        clear * - r30959 b30960 b30961 d30950
        omega
      have d30962 : (x (-8) 4).toNat = 1 := by
        have r30963 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b30964 := hb (x (-8) 4)
        have b30965 := hb (x (-4) 11)
        have b30966 := hb (x (-5) 1 && x (-5) 12)
        have b30967 := hb (x (-6) 2 && x (-6) 13)
        have b30968 := hb (x (-7) 3 && x (-7) 14)
        clear * - r30963 b30964 b30965 b30966 b30967 b30968 d30958 d30795 d29930 d29954
        omega
      have d30969 : (x (-8) 12).toNat = 1 := by
        have r30970 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
        have b30971 := hb (x (-8) 4)
        have b30972 := hb (x (-8) 12)
        clear * - r30970 b30971 b30972 d30962
        omega
      have d30973 : (x (-9) 13).toNat = 0 := by
        have r30974 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30975 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
        have e30976 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
        have b30977 := hb (x (-11) 3)
        have b30978 := hb (x (-10) 2)
        have b30979 := hb (x (-9) 13)
        have b30980 := hb (x (-8) 12)
        clear * - r30974 e30975 e30976 b30977 b30978 b30979 b30980 d30969
        omega
      have d30981 : (x (-9) 5).toNat = 0 := by
        have r30982 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
        have b30983 := hb (x (-9) 5)
        have b30984 := hb (x (-9) 13)
        clear * - r30982 b30983 b30984 d30973
        omega
      have d30985 : (x (-9) 5 && x (-9) 14).toNat = 0 := by
        have r30986 := hand1 (x (-9) 5) (x (-9) 14)
        have b30987 := hb (x (-9) 5)
        have b30988 := hb (x (-9) 5 && x (-9) 14)
        clear * - r30986 b30987 b30988 d30981
        omega
      have d30989 : (x (-10) 6).toNat = 1 := by
        have r30990 : 1 ≤ (x (-4) 9).toNat + (x (-5) 1 && x (-5) 10).toNat + (x (-6) 2 && x (-6) 11).toNat + (x (-7) 3 && x (-7) 12).toNat + (x (-8) 4 && x (-8) 13).toNat + (x (-9) 5 && x (-9) 14).toNat + (x (-10) 6).toNat := by have q := hcov9 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b30991 := hb (x (-10) 6)
        have b30992 := hb (x (-4) 9)
        have b30993 := hb (x (-5) 1 && x (-5) 10)
        have b30994 := hb (x (-6) 2 && x (-6) 11)
        have b30995 := hb (x (-7) 3 && x (-7) 12)
        have b30996 := hb (x (-8) 4 && x (-8) 13)
        have b30997 := hb (x (-9) 5 && x (-9) 14)
        clear * - r30990 b30991 b30992 b30993 b30994 b30995 b30996 b30997 d30930 d30811 d29934 d29958 d30783 d30985
        omega
      have d30998 : (x (-10) 14).toNat = 1 := by
        have r30999 : (x (-10) 6).toNat ≤ (x (-10) 14).toNat := himp _ _ (hp6 (-10))
        have b31000 := hb (x (-10) 6)
        have b31001 := hb (x (-10) 14)
        clear * - r30999 b31000 b31001 d30989
        omega
      have d31002 : (x (-11) 1).toNat = 0 := by
        have r31003 : (x (-10) 14).toNat + (x (-11) 1).toNat = 1 := by have q := hd14 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31004 := hb (x (-11) 1)
        have b31005 := hb (x (-10) 14)
        clear * - r31003 b31004 b31005 d30998
        omega
      have d31006 : (x (-11) 13).toNat = 0 := by
        have r31007 : (x (-11) 13).toNat ≤ (x (-11) 1).toNat := himp _ _ (hp13 (-11))
        have b31008 := hb (x (-11) 1)
        have b31009 := hb (x (-11) 13)
        clear * - r31007 b31008 b31009 d31002
        omega
      have d31010 : (x (-11) 3 && x (-11) 13).toNat = 0 := by
        have r31011 := hand2 (x (-11) 3) (x (-11) 13)
        have b31012 := hb (x (-11) 13)
        have b31013 := hb (x (-11) 3 && x (-11) 13)
        clear * - r31011 b31012 b31013 d31006
        omega
      have d31014 : (x (-12) 1 && x (-12) 14).toNat = 1 := by
        have r31015 : 1 ≤ (x (-11) 13).toNat + (x (-12) 1 && x (-12) 14).toNat + (x (-13) 2).toNat := by have q := hcov13 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31016 := hb (x (-13) 2)
        have b31017 := hb (x (-11) 13)
        have b31018 := hb (x (-12) 1 && x (-12) 14)
        clear * - r31015 b31016 b31017 b31018 d31006 d30922
        omega
      have d31019 : (x (-12) 14).toNat = 1 := by
        have r31020 := hand2 (x (-12) 1) (x (-12) 14)
        have b31021 := hb (x (-12) 14)
        have b31022 := hb (x (-12) 1 && x (-12) 14)
        clear * - r31020 b31021 b31022 d31014
        omega
      have d31023 : (x (-13) 1).toNat = 0 := by
        have r31024 : (x (-12) 14).toNat + (x (-13) 1).toNat = 1 := by have q := hd14 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31025 := hb (x (-13) 1)
        have b31026 := hb (x (-12) 14)
        clear * - r31024 b31025 b31026 d31019
        omega
      have d31027 : (x (-13) 1 && x (-13) 14).toNat = 0 := by
        have r31028 := hand1 (x (-13) 1) (x (-13) 14)
        have b31029 := hb (x (-13) 1)
        have b31030 := hb (x (-13) 1 && x (-13) 14)
        clear * - r31028 b31029 b31030 d31023
        omega
      have d31031 : (x (-14) 2).toNat = 1 := by
        have r31032 : 1 ≤ (x (-12) 13).toNat + (x (-13) 1 && x (-13) 14).toNat + (x (-14) 2).toNat := by have q := hcov13 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31033 := hb (x (-14) 2)
        have b31034 := hb (x (-12) 13)
        have b31035 := hb (x (-13) 1 && x (-13) 14)
        clear * - r31032 b31033 b31034 b31035 d30914 d31027
        omega
      have d31036 : (x (-12) 12).toNat = 0 := by
        have r31037 : (x (-12) 12).toNat + (x (-13) 1 && x (-13) 13).toNat + (x (-14) 2 && x (-14) 14).toNat + (x (-15) 3).toNat = 1 := by have q := hd12 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31038 : (x (-13) 1 && x (-13) 13).toNat = (x (-13) 13).toNat := handr _ _ (fun h => hp13 (-13) (h))
        have e31039 : (x (-14) 2 && x (-14) 14).toNat = (x (-14) 2).toNat := handl _ _ (fun h => hp2 (-14) (h))
        have b31040 := hb (x (-15) 3)
        have b31041 := hb (x (-14) 2)
        have b31042 := hb (x (-13) 13)
        have b31043 := hb (x (-12) 12)
        clear * - r31037 e31038 e31039 b31040 b31041 b31042 b31043 d31031
        omega
      have d31044 : (x (-12) 4).toNat = 0 := by
        have r31045 : (x (-12) 4).toNat ≤ (x (-12) 12).toNat := himp _ _ (hp4 (-12))
        have b31046 := hb (x (-12) 4)
        have b31047 := hb (x (-12) 12)
        clear * - r31045 b31046 b31047 d31036
        omega
      have d31048 : (x (-12) 4 && x (-12) 14).toNat = 0 := by
        have r31049 := hand1 (x (-12) 4) (x (-12) 14)
        have b31050 := hb (x (-12) 4)
        have b31051 := hb (x (-12) 4 && x (-12) 14)
        clear * - r31049 b31050 b31051 d31044
        omega
      have d31052 : (x (-13) 13).toNat = 0 := by
        have r31053 : (x (-12) 12).toNat + (x (-13) 1 && x (-13) 13).toNat + (x (-14) 2 && x (-14) 14).toNat + (x (-15) 3).toNat = 1 := by have q := hd12 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31054 : (x (-13) 1 && x (-13) 13).toNat = (x (-13) 13).toNat := handr _ _ (fun h => hp13 (-13) (h))
        have e31055 : (x (-14) 2 && x (-14) 14).toNat = (x (-14) 2).toNat := handl _ _ (fun h => hp2 (-14) (h))
        have b31056 := hb (x (-15) 3)
        have b31057 := hb (x (-14) 2)
        have b31058 := hb (x (-13) 13)
        have b31059 := hb (x (-12) 12)
        clear * - r31053 e31054 e31055 b31056 b31057 b31058 b31059 d31036 d31031
        omega
      have d31060 : (x (-13) 5).toNat = 0 := by
        have r31061 : (x (-13) 5).toNat ≤ (x (-13) 13).toNat := himp _ _ (hp5 (-13))
        have b31062 := hb (x (-13) 5)
        have b31063 := hb (x (-13) 13)
        clear * - r31061 b31062 b31063 d31052
        omega
      have d31064 : (x (-10) 2 && x (-10) 12).toNat = 1 := by
        have r31065 : 1 ≤ (x (-8) 10).toNat + (x (-9) 1 && x (-9) 11).toNat + (x (-10) 2 && x (-10) 12).toNat + (x (-11) 3 && x (-11) 13).toNat + (x (-12) 4 && x (-12) 14).toNat + (x (-13) 5).toNat := by have q := hcov10 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31066 := hb (x (-13) 5)
        have b31067 := hb (x (-8) 10)
        have b31068 := hb (x (-9) 1 && x (-9) 11)
        have b31069 := hb (x (-10) 2 && x (-10) 12)
        have b31070 := hb (x (-11) 3 && x (-11) 13)
        have b31071 := hb (x (-12) 4 && x (-12) 14)
        clear * - r31065 b31066 b31067 b31068 b31069 b31070 b31071 d30871 d30887 d31010 d31048 d31060
        omega
      have d31072 : (x (-10) 2).toNat = 1 := by
        have r31073 := hand1 (x (-10) 2) (x (-10) 12)
        have b31074 := hb (x (-10) 2)
        have b31075 := hb (x (-10) 2 && x (-10) 12)
        clear * - r31073 b31074 b31075 d31064
        omega
      have r31076 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e31077 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
      have e31078 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
      have b31079 := hb (x (-11) 3)
      have b31080 := hb (x (-10) 2)
      have b31081 := hb (x (-9) 13)
      have b31082 := hb (x (-8) 12)
      linarith only [r31076, e31077, e31078, b31079, b31080, b31081, b31082, d30969, d30973, d31072]
  · have f31083 : (x 0 5).toNat = 1 := by rw [h30372]; rfl
    have d31084 : (x 5 8).toNat = 0 := by
      have r31085 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e31086 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
      have e31087 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
      have e31088 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
      have e31089 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
      have e31090 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
      have e31091 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
      have b31092 := hb (x (-2) 7)
      have b31093 := hb (x (-1) 6)
      have b31094 := hb (x 0 5)
      have b31095 := hb (x 1 4)
      have b31096 := hb (x 2 11)
      have b31097 := hb (x 3 10)
      have b31098 := hb (x 4 9)
      have b31099 := hb (x 5 8)
      clear * - r31085 e31086 e31087 e31088 e31089 e31090 e31091 b31092 b31093 b31094 b31095 b31096 b31097 b31098 b31099 d30007 d29819 f31083
      omega
    have d31100 : (x 5 1 && x 5 8).toNat = 0 := by
      have r31101 := hand2 (x 5 1) (x 5 8)
      have b31102 := hb (x 5 8)
      have b31103 := hb (x 5 1 && x 5 8)
      clear * - r31101 b31102 b31103 d31084
      omega
    have d31104 : (x 5 2 && x 5 8).toNat = 0 := by
      have r31105 := hand2 (x 5 2) (x 5 8)
      have b31106 := hb (x 5 8)
      have b31107 := hb (x 5 2 && x 5 8)
      clear * - r31105 b31106 b31107 d31084
      omega
    have d31108 : (x 5 3 && x 5 8).toNat = 0 := by
      have r31109 := hand2 (x 5 3) (x 5 8)
      have b31110 := hb (x 5 8)
      have b31111 := hb (x 5 3 && x 5 8)
      clear * - r31109 b31110 b31111 d31084
      omega
    have d31112 : (x 5 4 && x 5 8).toNat = 0 := by
      have r31113 := hand2 (x 5 4) (x 5 8)
      have b31114 := hb (x 5 8)
      have b31115 := hb (x 5 4 && x 5 8)
      clear * - r31113 b31114 b31115 d31084
      omega
    have d31116 : (x 4 9).toNat = 0 := by
      have r31117 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e31118 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
      have e31119 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
      have e31120 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
      have e31121 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
      have e31122 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
      have e31123 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
      have b31124 := hb (x (-2) 7)
      have b31125 := hb (x (-1) 6)
      have b31126 := hb (x 0 5)
      have b31127 := hb (x 1 4)
      have b31128 := hb (x 2 11)
      have b31129 := hb (x 3 10)
      have b31130 := hb (x 4 9)
      have b31131 := hb (x 5 8)
      clear * - r31117 e31118 e31119 e31120 e31121 e31122 e31123 b31124 b31125 b31126 b31127 b31128 b31129 b31130 b31131 d31084 d30007 d29819 f31083
      omega
    have d31132 : (x 4 2 && x 4 9).toNat = 0 := by
      have r31133 := hand2 (x 4 2) (x 4 9)
      have b31134 := hb (x 4 9)
      have b31135 := hb (x 4 2 && x 4 9)
      clear * - r31133 b31134 b31135 d31116
      omega
    have d31136 : (x 4 3 && x 4 9).toNat = 0 := by
      have r31137 := hand2 (x 4 3) (x 4 9)
      have b31138 := hb (x 4 9)
      have b31139 := hb (x 4 3 && x 4 9)
      clear * - r31137 b31138 b31139 d31116
      omega
    have d31140 : (x 4 4 && x 4 9).toNat = 0 := by
      have r31141 := hand2 (x 4 4) (x 4 9)
      have b31142 := hb (x 4 9)
      have b31143 := hb (x 4 4 && x 4 9)
      clear * - r31141 b31142 b31143 d31116
      omega
    have d31144 : (x 4 5 && x 4 9).toNat = 0 := by
      have r31145 := hand2 (x 4 5) (x 4 9)
      have b31146 := hb (x 4 9)
      have b31147 := hb (x 4 5 && x 4 9)
      clear * - r31145 b31146 b31147 d31116
      omega
    have d31148 : (x 2 11).toNat = 0 := by
      have r31149 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e31150 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
      have e31151 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
      have e31152 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
      have e31153 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
      have e31154 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
      have e31155 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
      have b31156 := hb (x (-2) 7)
      have b31157 := hb (x (-1) 6)
      have b31158 := hb (x 0 5)
      have b31159 := hb (x 1 4)
      have b31160 := hb (x 2 11)
      have b31161 := hb (x 3 10)
      have b31162 := hb (x 4 9)
      have b31163 := hb (x 5 8)
      clear * - r31149 e31150 e31151 e31152 e31153 e31154 e31155 b31156 b31157 b31158 b31159 b31160 b31161 b31162 b31163 d31084 d31116 d30007 d29819 f31083
      omega
    have d31164 : (x 2 6 && x 2 11).toNat = 0 := by
      have r31165 := hand2 (x 2 6) (x 2 11)
      have b31166 := hb (x 2 11)
      have b31167 := hb (x 2 6 && x 2 11)
      clear * - r31165 b31166 b31167 d31148
      omega
    have d31168 : (x 2 7 && x 2 11).toNat = 0 := by
      have r31169 := hand2 (x 2 7) (x 2 11)
      have b31170 := hb (x 2 11)
      have b31171 := hb (x 2 7 && x 2 11)
      clear * - r31169 b31170 b31171 d31148
      omega
    cases h31172 : x 0 6
    · have f31173 : (x 0 6).toNat = 0 := by rw [h31172]; rfl
      have d31174 : (x 0 6 && x 0 13).toNat = 0 := by
        have r31175 := hand1 (x 0 6) (x 0 13)
        have b31176 := hb (x 0 6)
        have b31177 := hb (x 0 6 && x 0 13)
        clear * - r31175 b31176 b31177 f31173
        omega
      have d31178 : (x 0 6 && x 0 10).toNat = 0 := by
        have r31179 := hand1 (x 0 6) (x 0 10)
        have b31180 := hb (x 0 6)
        have b31181 := hb (x 0 6 && x 0 10)
        clear * - r31179 b31180 b31181 f31173
        omega
      have d31182 : (x 0 2 && x 0 6).toNat = 0 := by
        have r31183 := hand2 (x 0 2) (x 0 6)
        have b31184 := hb (x 0 6)
        have b31185 := hb (x 0 2 && x 0 6)
        clear * - r31183 b31184 b31185 f31173
        omega
      cases h31186 : x 0 7
      · have f31187 : (x 0 7).toNat = 0 := by rw [h31186]; rfl
        have d31188 : (x 0 3 && x 0 7).toNat = 0 := by
          have r31189 := hand2 (x 0 3) (x 0 7)
          have b31190 := hb (x 0 7)
          have b31191 := hb (x 0 3 && x 0 7)
          clear * - r31189 b31190 b31191 f31187
          omega
        cases h31192 : x 0 9
        · have f31193 : (x 0 9).toNat = 0 := by rw [h31192]; rfl
          have d31194 : (x 0 9 && x 0 13).toNat = 0 := by
            have r31195 := hand1 (x 0 9) (x 0 13)
            have b31196 := hb (x 0 9)
            have b31197 := hb (x 0 9 && x 0 13)
            clear * - r31195 b31196 b31197 f31193
            omega
          have d31198 : (x (-4) 4 && x (-4) 13).toNat = 1 := by
            have r31199 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b31200 := hb (x (-6) 6)
            have b31201 := hb (x 0 9)
            have b31202 := hb (x (-1) 1 && x (-1) 10)
            have b31203 := hb (x (-2) 2 && x (-2) 11)
            have b31204 := hb (x (-3) 3 && x (-3) 12)
            have b31205 := hb (x (-4) 4 && x (-4) 13)
            have b31206 := hb (x (-5) 5 && x (-5) 14)
            clear * - r31199 b31200 b31201 b31202 b31203 b31204 b31205 b31206 f31193 g36 d29738 d29867 d29918 d30356
            omega
          have d31207 : (x (-4) 13).toNat = 1 := by
            have r31208 := hand2 (x (-4) 4) (x (-4) 13)
            have b31209 := hb (x (-4) 13)
            have b31210 := hb (x (-4) 4 && x (-4) 13)
            clear * - r31208 b31209 b31210 d31198
            omega
          have d31211 : (x (-4) 1).toNat = 1 := by
            have r31212 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
            have b31213 := hb (x (-4) 1)
            have b31214 := hb (x (-4) 13)
            clear * - r31212 b31213 b31214 d31207
            omega
          have d31215 : (x (-3) 14).toNat = 0 := by
            have r31216 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b31217 := hb (x (-4) 1)
            have b31218 := hb (x (-3) 14)
            clear * - r31216 b31217 b31218 d31211
            omega
          have d31219 : (x (-3) 2).toNat = 0 := by
            have r31220 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
            have b31221 := hb (x (-3) 2)
            have b31222 := hb (x (-3) 14)
            clear * - r31220 b31221 b31222 d31215
            omega
          have d31223 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
            have r31224 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b31225 := hb (x (-3) 2)
            have b31226 := hb (x (-1) 13)
            have b31227 := hb (x (-2) 1 && x (-2) 14)
            clear * - r31224 b31225 b31226 b31227 g4 d31219
            omega
          have d31228 : (x (-2) 14).toNat = 1 := by
            have r31229 := hand2 (x (-2) 1) (x (-2) 14)
            have b31230 := hb (x (-2) 14)
            have b31231 := hb (x (-2) 1 && x (-2) 14)
            clear * - r31229 b31230 b31231 d31223
            omega
          have d31232 : (x (-3) 1).toNat = 0 := by
            have r31233 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b31234 := hb (x (-3) 1)
            have b31235 := hb (x (-2) 14)
            clear * - r31233 b31234 b31235 d31228
            omega
          have d31236 : (x (-3) 13).toNat = 0 := by
            have r31237 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
            have b31238 := hb (x (-3) 1)
            have b31239 := hb (x (-3) 13)
            clear * - r31237 b31238 b31239 d31232
            omega
          have d31240 : (x (-3) 9 && x (-3) 13).toNat = 0 := by
            have r31241 := hand2 (x (-3) 9) (x (-3) 13)
            have b31242 := hb (x (-3) 13)
            have b31243 := hb (x (-3) 9 && x (-3) 13)
            clear * - r31241 b31242 b31243 d31236
            omega
          have d31244 : (x (-3) 9).toNat = 0 := by
            have r31245 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
            have b31246 := hb (x (-3) 1)
            have b31247 := hb (x (-3) 9)
            clear * - r31245 b31246 b31247 d31232
            omega
          have d31248 : (x (-2) 1).toNat = 1 := by
            have r31249 := hand1 (x (-2) 1) (x (-2) 14)
            have b31250 := hb (x (-2) 1)
            have b31251 := hb (x (-2) 1 && x (-2) 14)
            clear * - r31249 b31250 b31251 d31223
            omega
          have d31252 : (x (-1) 14).toNat = 0 := by
            have r31253 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b31254 := hb (x (-2) 1)
            have b31255 := hb (x (-1) 14)
            clear * - r31253 b31254 b31255 d31248
            omega
          have d31256 : (x (-1) 7 && x (-1) 14).toNat = 0 := by
            have r31257 := hand2 (x (-1) 7) (x (-1) 14)
            have b31258 := hb (x (-1) 14)
            have b31259 := hb (x (-1) 7 && x (-1) 14)
            clear * - r31257 b31258 b31259 d31252
            omega
          have d31260 : (x (-3) 12).toNat = 0 := by
            have r31261 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e31262 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
            have e31263 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
            have b31264 := hb (x (-6) 3)
            have b31265 := hb (x (-5) 2)
            have b31266 := hb (x (-4) 13)
            have b31267 := hb (x (-3) 12)
            clear * - r31261 e31262 e31263 b31264 b31265 b31266 b31267 d31207
            omega
          have d31268 : (x (-5) 2).toNat = 0 := by
            have r31269 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e31270 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
            have e31271 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
            have b31272 := hb (x (-6) 3)
            have b31273 := hb (x (-5) 2)
            have b31274 := hb (x (-4) 13)
            have b31275 := hb (x (-3) 12)
            clear * - r31269 e31270 e31271 b31272 b31273 b31274 b31275 d31260 d31207
            omega
          have d31276 : (x (-4) 1 && x (-4) 14).toNat = 1 := by
            have r31277 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b31278 := hb (x (-5) 2)
            have b31279 := hb (x (-3) 13)
            have b31280 := hb (x (-4) 1 && x (-4) 14)
            clear * - r31277 b31278 b31279 b31280 d31236 d31268
            omega
          have d31281 : (x (-4) 14).toNat = 1 := by
            have r31282 := hand2 (x (-4) 1) (x (-4) 14)
            have b31283 := hb (x (-4) 14)
            have b31284 := hb (x (-4) 1 && x (-4) 14)
            clear * - r31282 b31283 b31284 d31276
            omega
          have d31285 : (x (-5) 1).toNat = 0 := by
            have r31286 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b31287 := hb (x (-5) 1)
            have b31288 := hb (x (-4) 14)
            clear * - r31286 b31287 b31288 d31281
            omega
          have d31289 : (x (-5) 9).toNat = 0 := by
            have r31290 : (x (-5) 9).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp9 (-5))
            have b31291 := hb (x (-5) 1)
            have b31292 := hb (x (-5) 9)
            clear * - r31290 b31291 b31292 d31285
            omega
          have r31293 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r31294 : (x 9 1).toNat + (x 8 2).toNat + (x 7 3).toNat + (x 6 4).toNat + (x 5 5).toNat + (x 4 6).toNat + (x 3 7).toNat + (x 2 8).toNat + (x 1 9).toNat + (x 0 10).toNat + (x (-1) 11).toNat + (x (-2) 12).toNat + (x (-3) 13).toNat + (x (-4) 14).toNat = 3 := by have q := hcount 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r31295 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31296 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
          have e31297 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
          have e31298 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
          have e31299 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
          have e31300 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
          have e31301 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
          have r31302 : (x (-5) 8).toNat + (x (-6) 1 && x (-6) 9).toNat + (x (-7) 2 && x (-7) 10).toNat + (x (-8) 3 && x (-8) 11).toNat + (x (-9) 4 && x (-9) 12).toNat + (x (-10) 5 && x (-10) 13).toNat + (x (-11) 6 && x (-11) 14).toNat + (x (-12) 7).toNat = 1 := by have q := hd8 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31303 : (x (-6) 1 && x (-6) 9).toNat = (x (-6) 9).toNat := handr _ _ (fun h => hp9 (-6) (h))
          have e31304 : (x (-7) 2 && x (-7) 10).toNat = (x (-7) 10).toNat := handr _ _ (fun h => hp10 (-7) (h))
          have e31305 : (x (-8) 3 && x (-8) 11).toNat = (x (-8) 11).toNat := handr _ _ (fun h => hp11 (-8) (h))
          have e31306 : (x (-9) 4 && x (-9) 12).toNat = (x (-9) 4).toNat := handl _ _ (fun h => hp4 (-9) (h))
          have e31307 : (x (-10) 5 && x (-10) 13).toNat = (x (-10) 5).toNat := handl _ _ (fun h => hp5 (-10) (h))
          have e31308 : (x (-11) 6 && x (-11) 14).toNat = (x (-11) 6).toNat := handl _ _ (fun h => hp6 (-11) (h))
          have r31309 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31310 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
          have e31311 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
          have e31312 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
          have e31313 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
          have e31314 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
          have e31315 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
          have r31316 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31317 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e31318 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e31319 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e31320 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e31321 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e31322 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have r31323 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31324 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
          have e31325 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
          have e31326 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
          have e31327 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
          have e31328 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
          have e31329 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
          have r31330 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31331 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
          have e31332 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
          have r31333 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31334 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
          have e31335 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
          have r31336 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31337 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e31338 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have r31339 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31340 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
          have e31341 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
          have r31342 : 1 ≤ (x 2 4).toNat + (x 1 1 && x 1 5).toNat + (x 0 2 && x 0 6).toNat + (x (-1) 3 && x (-1) 7).toNat + (x (-2) 4 && x (-2) 8).toNat + (x (-3) 5 && x (-3) 9).toNat + (x (-4) 6 && x (-4) 10).toNat + (x (-5) 7 && x (-5) 11).toNat + (x (-6) 8 && x (-6) 12).toNat + (x (-7) 9 && x (-7) 13).toNat + (x (-8) 10 && x (-8) 14).toNat + (x (-9) 11).toNat := by have q := hcov4 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31343 : (x 1 1 && x 1 5).toNat = (x 1 5).toNat := handr _ _ (fun h => hp13 1 (hp5 1 (h)))
          have e31344 : (x (-8) 10 && x (-8) 14).toNat = (x (-8) 10).toNat := handl _ _ (fun h => hp2 (-8) (hp10 (-8) (h)))
          have r31345 : 1 ≤ (x 3 4).toNat + (x 2 1 && x 2 5).toNat + (x 1 2 && x 1 6).toNat + (x 0 3 && x 0 7).toNat + (x (-1) 4 && x (-1) 8).toNat + (x (-2) 5 && x (-2) 9).toNat + (x (-3) 6 && x (-3) 10).toNat + (x (-4) 7 && x (-4) 11).toNat + (x (-5) 8 && x (-5) 12).toNat + (x (-6) 9 && x (-6) 13).toNat + (x (-7) 10 && x (-7) 14).toNat + (x (-8) 11).toNat := by have q := hcov4 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31346 : (x 2 1 && x 2 5).toNat = (x 2 5).toNat := handr _ _ (fun h => hp13 2 (hp5 2 (h)))
          have e31347 : (x (-7) 10 && x (-7) 14).toNat = (x (-7) 10).toNat := handl _ _ (fun h => hp2 (-7) (hp10 (-7) (h)))
          have r31348 : 1 ≤ (x 6 4).toNat + (x 5 1 && x 5 5).toNat + (x 4 2 && x 4 6).toNat + (x 3 3 && x 3 7).toNat + (x 2 4 && x 2 8).toNat + (x 1 5 && x 1 9).toNat + (x 0 6 && x 0 10).toNat + (x (-1) 7 && x (-1) 11).toNat + (x (-2) 8 && x (-2) 12).toNat + (x (-3) 9 && x (-3) 13).toNat + (x (-4) 10 && x (-4) 14).toNat + (x (-5) 11).toNat := by have q := hcov4 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31349 : (x 5 1 && x 5 5).toNat = (x 5 5).toNat := handr _ _ (fun h => hp13 5 (hp5 5 (h)))
          have e31350 : (x (-4) 10 && x (-4) 14).toNat = (x (-4) 10).toNat := handl _ _ (fun h => hp2 (-4) (hp10 (-4) (h)))
          have r31351 : 1 ≤ (x 9 4).toNat + (x 8 1 && x 8 5).toNat + (x 7 2 && x 7 6).toNat + (x 6 3 && x 6 7).toNat + (x 5 4 && x 5 8).toNat + (x 4 5 && x 4 9).toNat + (x 3 6 && x 3 10).toNat + (x 2 7 && x 2 11).toNat + (x 1 8 && x 1 12).toNat + (x 0 9 && x 0 13).toNat + (x (-1) 10 && x (-1) 14).toNat + (x (-2) 11).toNat := by have q := hcov4 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31352 : (x 8 1 && x 8 5).toNat = (x 8 5).toNat := handr _ _ (fun h => hp13 8 (hp5 8 (h)))
          have e31353 : (x (-1) 10 && x (-1) 14).toNat = (x (-1) 10).toNat := handl _ _ (fun h => hp2 (-1) (hp10 (-1) (h)))
          have r31354 : 1 ≤ (x 2 6).toNat + (x 1 1 && x 1 7).toNat + (x 0 2 && x 0 8).toNat + (x (-1) 3 && x (-1) 9).toNat + (x (-2) 4 && x (-2) 10).toNat + (x (-3) 5 && x (-3) 11).toNat + (x (-4) 6 && x (-4) 12).toNat + (x (-5) 7 && x (-5) 13).toNat + (x (-6) 8 && x (-6) 14).toNat + (x (-7) 9).toNat := by have q := hcov6 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r31355 : 1 ≤ (x 6 7).toNat + (x 5 1 && x 5 8).toNat + (x 4 2 && x 4 9).toNat + (x 3 3 && x 3 10).toNat + (x 2 4 && x 2 11).toNat + (x 1 5 && x 1 12).toNat + (x 0 6 && x 0 13).toNat + (x (-1) 7 && x (-1) 14).toNat + (x (-2) 8).toNat := by have q := hcov7 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r31356 : 1 ≤ (x (-5) 9).toNat + (x (-6) 1 && x (-6) 10).toNat + (x (-7) 2 && x (-7) 11).toNat + (x (-8) 3 && x (-8) 12).toNat + (x (-9) 4 && x (-9) 13).toNat + (x (-10) 5 && x (-10) 14).toNat + (x (-11) 6).toNat := by have q := hcov9 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r31357 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r31358 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r31359 : 1 ≤ (x 10 11).toNat + (x 9 1 && x 9 12).toNat + (x 8 2 && x 8 13).toNat + (x 7 3 && x 7 14).toNat + (x 6 4).toNat := by have q := hcov11 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r31360 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r31361 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r31362 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
          have r31363 := hand2 (x (-6) 8) (x (-6) 12)
          have r31364 := hand2 (x (-7) 9) (x (-7) 13)
          have r31365 := hand2 (x (-5) 8) (x (-5) 12)
          have r31366 := hand1 (x (-6) 9) (x (-6) 13)
          have r31367 := hand2 (x 4 2) (x 4 6)
          have r31368 := hand2 (x 3 3) (x 3 7)
          have r31369 := hand2 (x (-2) 8) (x (-2) 12)
          have r31370 := hand2 (x 7 2) (x 7 6)
          have r31371 := hand1 (x 6 3) (x 6 7)
          have r31372 := hand2 (x 1 1) (x 1 7)
          have r31373 := hand1 (x (-6) 8) (x (-6) 14)
          have r31374 := hand1 (x (-8) 3) (x (-8) 12)
          have r31375 := hand1 (x (-9) 4) (x (-9) 13)
          have r31376 := hand1 (x (-10) 5) (x (-10) 14)
          have r31377 := hand1 (x (-8) 2) (x (-8) 12)
          have r31378 := hand1 (x (-9) 3) (x (-9) 13)
          have r31379 := hand1 (x (-10) 4) (x (-10) 14)
          have r31380 := hand2 (x 5 1) (x 5 11)
          have r31381 := hand1 (x 4 2) (x 4 12)
          have r31382 := hand1 (x 3 3) (x 3 13)
          have r31383 := hand2 (x 9 1) (x 9 12)
          have r31384 := hand1 (x 8 2) (x 8 13)
          have r31385 := hand1 (x 7 3) (x 7 14)
          have r31386 := hand2 (x (-6) 1) (x (-6) 14)
          have r31387 := hand1 (x 7 1) (x 7 14)
          linarith only [r31293, r31294, r31295, e31296, e31297, e31298, e31299, e31300, e31301, r31302, e31303, e31304, e31305, e31306, e31307, e31308, r31309, e31310, e31311, e31312, e31313, e31314, e31315, r31316, e31317, e31318, e31319, e31320, e31321, e31322, r31323, e31324, e31325, e31326, e31327, e31328, e31329, r31330, e31331, e31332, r31333, e31334, e31335, r31336, e31337, e31338, r31339, e31340, e31341, r31342, e31343, e31344, r31345, e31346, e31347, r31348, e31349, e31350, r31351, e31352, e31353, r31354, r31355, r31356, r31357, r31358, r31359, r31360, r31361, r31362, r31363, r31364, r31365, r31366, r31367, r31368, r31369, r31370, r31371, r31372, r31373, r31374, r31375, r31376, r31377, r31378, r31379, r31380, r31381, r31382, r31383, r31384, r31385, r31386, r31387, d29938, d31289, d29894, d29890, d31281, d31244, d29871, d31236, d29742, d29851, g2, d29835, g3, d30316, g6, g8, g9, g10, d30284, g11, d30260, d31182, g12, g13, g14, g15, g16, d29779, d31188, d30183, d30207, d30227, d30312, g18, g19, d31178, g20, d31240, d31112, d31144, d29995, d31168, d29815, d31194, d30336, g24, g25, g26, g27, g28, d31100, d31132, d30011, g32, g33, d31174, d31256, d29942, d29970, d29966, g47]
        · have f31541 : (x 0 9).toNat = 1 := by rw [h31192]; rfl
          have d31542 : (x 1 8).toNat = 0 := by
            have r31543 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e31544 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
            have e31545 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
            have e31546 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
            have e31547 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
            have e31548 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
            have e31549 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
            have b31550 := hb (x (-6) 7)
            have b31551 := hb (x (-5) 6)
            have b31552 := hb (x (-4) 5)
            have b31553 := hb (x (-3) 4)
            have b31554 := hb (x (-2) 11)
            have b31555 := hb (x (-1) 10)
            have b31556 := hb (x 0 9)
            have b31557 := hb (x 1 8)
            clear * - r31543 e31544 e31545 e31546 e31547 e31548 e31549 b31550 b31551 b31552 b31553 b31554 b31555 b31556 b31557 f31541 d29835 d29851
            omega
          have d31558 : (x (-3) 4).toNat = 0 := by
            have r31559 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e31560 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
            have e31561 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
            have e31562 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
            have e31563 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
            have e31564 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
            have e31565 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
            have b31566 := hb (x (-6) 7)
            have b31567 := hb (x (-5) 6)
            have b31568 := hb (x (-4) 5)
            have b31569 := hb (x (-3) 4)
            have b31570 := hb (x (-2) 11)
            have b31571 := hb (x (-1) 10)
            have b31572 := hb (x 0 9)
            have b31573 := hb (x 1 8)
            clear * - r31559 e31560 e31561 e31562 e31563 e31564 e31565 b31566 b31567 b31568 b31569 b31570 b31571 b31572 b31573 d31542 f31541 d29835 d29851
            omega
          have d31574 : (x (-3) 4 && x (-3) 14).toNat = 0 := by
            have r31575 := hand1 (x (-3) 4) (x (-3) 14)
            have b31576 := hb (x (-3) 4)
            have b31577 := hb (x (-3) 4 && x (-3) 14)
            clear * - r31575 b31576 b31577 d31558
            omega
          have d31578 : (x (-4) 5).toNat = 1 := by
            have r31579 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b31580 := hb (x (-4) 5)
            have b31581 := hb (x 1 10)
            have b31582 := hb (x 0 1 && x 0 11)
            have b31583 := hb (x (-1) 2 && x (-1) 12)
            have b31584 := hb (x (-2) 3 && x (-2) 13)
            have b31585 := hb (x (-3) 4 && x (-3) 14)
            clear * - r31579 b31580 b31581 b31582 b31583 b31584 b31585 d29795 g46 d29831 d29847 d31574
            omega
          have r31586 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31587 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e31588 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e31589 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e31590 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e31591 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e31592 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b31593 := hb (x (-6) 7)
          have b31594 := hb (x (-5) 6)
          have b31595 := hb (x (-4) 5)
          have b31596 := hb (x (-3) 4)
          have b31597 := hb (x (-2) 11)
          have b31598 := hb (x (-1) 10)
          have b31599 := hb (x 0 9)
          have b31600 := hb (x 1 8)
          linarith only [r31586, e31587, e31588, e31589, e31590, e31591, e31592, b31593, b31594, b31595, b31596, b31597, b31598, b31599, b31600, d31542, f31541, d29835, d29851, d31558, d31578]
      · have f31601 : (x 0 7).toNat = 1 := by rw [h31186]; rfl
        have d31602 : (x 7 8).toNat = 0 := by
          have r31603 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31604 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e31605 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e31606 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e31607 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e31608 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e31609 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have b31610 := hb (x 0 7)
          have b31611 := hb (x 1 6)
          have b31612 := hb (x 2 5)
          have b31613 := hb (x 3 4)
          have b31614 := hb (x 4 11)
          have b31615 := hb (x 5 10)
          have b31616 := hb (x 6 9)
          have b31617 := hb (x 7 8)
          clear * - r31603 e31604 e31605 e31606 e31607 e31608 e31609 b31610 b31611 b31612 b31613 b31614 b31615 b31616 b31617 d30260 d30284 d29771 f31601
          omega
        have d31618 : (x 6 9).toNat = 0 := by
          have r31619 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31620 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e31621 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e31622 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e31623 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e31624 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e31625 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have b31626 := hb (x 0 7)
          have b31627 := hb (x 1 6)
          have b31628 := hb (x 2 5)
          have b31629 := hb (x 3 4)
          have b31630 := hb (x 4 11)
          have b31631 := hb (x 5 10)
          have b31632 := hb (x 6 9)
          have b31633 := hb (x 7 8)
          clear * - r31619 e31620 e31621 e31622 e31623 e31624 e31625 b31626 b31627 b31628 b31629 b31630 b31631 b31632 b31633 d31602 d30260 d30284 d29771 f31601
          omega
        have d31634 : (x 5 10).toNat = 0 := by
          have r31635 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31636 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e31637 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e31638 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e31639 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e31640 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e31641 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have b31642 := hb (x 0 7)
          have b31643 := hb (x 1 6)
          have b31644 := hb (x 2 5)
          have b31645 := hb (x 3 4)
          have b31646 := hb (x 4 11)
          have b31647 := hb (x 5 10)
          have b31648 := hb (x 6 9)
          have b31649 := hb (x 7 8)
          clear * - r31635 e31636 e31637 e31638 e31639 e31640 e31641 b31642 b31643 b31644 b31645 b31646 b31647 b31648 b31649 d31602 d31618 d30260 d30284 d29771 f31601
          omega
        have d31650 : (x 5 1 && x 5 10).toNat = 0 := by
          have r31651 := hand2 (x 5 1) (x 5 10)
          have b31652 := hb (x 5 10)
          have b31653 := hb (x 5 1 && x 5 10)
          clear * - r31651 b31652 b31653 d31634
          omega
        have d31654 : (x 4 2 && x 4 11).toNat = 1 := by
          have r31655 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b31656 := hb (x 0 6)
          have b31657 := hb (x 6 9)
          have b31658 := hb (x 5 1 && x 5 10)
          have b31659 := hb (x 4 2 && x 4 11)
          have b31660 := hb (x 3 3 && x 3 12)
          have b31661 := hb (x 2 4 && x 2 13)
          have b31662 := hb (x 1 5 && x 1 14)
          clear * - r31655 b31656 b31657 b31658 b31659 b31660 b31661 b31662 d31618 d31650 d30252 g44 g45 f31173
          omega
        have d31663 : (x 4 11).toNat = 1 := by
          have r31664 := hand2 (x 4 2) (x 4 11)
          have b31665 := hb (x 4 11)
          have b31666 := hb (x 4 2 && x 4 11)
          clear * - r31664 b31665 b31666 d31654
          omega
        have r31667 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31668 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e31669 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e31670 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e31671 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e31672 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e31673 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b31674 := hb (x 0 7)
        have b31675 := hb (x 1 6)
        have b31676 := hb (x 2 5)
        have b31677 := hb (x 3 4)
        have b31678 := hb (x 4 11)
        have b31679 := hb (x 5 10)
        have b31680 := hb (x 6 9)
        have b31681 := hb (x 7 8)
        linarith only [r31667, e31668, e31669, e31670, e31671, e31672, e31673, b31674, b31675, b31676, b31677, b31678, b31679, b31680, b31681, d31602, d31618, d31634, d31663, d30260, d30284, d29771, f31601]
    · have f31682 : (x 0 6).toNat = 1 := by rw [h31172]; rfl
      have d31683 : (x 6 8).toNat = 0 := by
        have r31684 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31685 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e31686 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e31687 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e31688 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e31689 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e31690 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b31691 := hb (x (-1) 7)
        have b31692 := hb (x 0 6)
        have b31693 := hb (x 1 5)
        have b31694 := hb (x 2 4)
        have b31695 := hb (x 3 11)
        have b31696 := hb (x 4 10)
        have b31697 := hb (x 5 9)
        have b31698 := hb (x 6 8)
        clear * - r31684 e31685 e31686 e31687 e31688 e31689 e31690 b31691 b31692 b31693 b31694 b31695 b31696 b31697 b31698 g10 g8 f31682
        omega
      have d31699 : (x 6 1 && x 6 8).toNat = 0 := by
        have r31700 := hand2 (x 6 1) (x 6 8)
        have b31701 := hb (x 6 8)
        have b31702 := hb (x 6 1 && x 6 8)
        clear * - r31700 b31701 b31702 d31683
        omega
      have d31703 : (x 6 2 && x 6 8).toNat = 0 := by
        have r31704 := hand2 (x 6 2) (x 6 8)
        have b31705 := hb (x 6 8)
        have b31706 := hb (x 6 2 && x 6 8)
        clear * - r31704 b31705 b31706 d31683
        omega
      have d31707 : (x 5 9).toNat = 0 := by
        have r31708 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31709 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e31710 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e31711 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e31712 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e31713 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e31714 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b31715 := hb (x (-1) 7)
        have b31716 := hb (x 0 6)
        have b31717 := hb (x 1 5)
        have b31718 := hb (x 2 4)
        have b31719 := hb (x 3 11)
        have b31720 := hb (x 4 10)
        have b31721 := hb (x 5 9)
        have b31722 := hb (x 6 8)
        clear * - r31708 e31709 e31710 e31711 e31712 e31713 e31714 b31715 b31716 b31717 b31718 b31719 b31720 b31721 b31722 d31683 g10 g8 f31682
        omega
      have d31723 : (x 5 2 && x 5 9).toNat = 0 := by
        have r31724 := hand2 (x 5 2) (x 5 9)
        have b31725 := hb (x 5 9)
        have b31726 := hb (x 5 2 && x 5 9)
        clear * - r31724 b31725 b31726 d31707
        omega
      have d31727 : (x 5 3 && x 5 9).toNat = 0 := by
        have r31728 := hand2 (x 5 3) (x 5 9)
        have b31729 := hb (x 5 9)
        have b31730 := hb (x 5 3 && x 5 9)
        clear * - r31728 b31729 b31730 d31707
        omega
      have d31731 : (x 4 10).toNat = 0 := by
        have r31732 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31733 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e31734 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e31735 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e31736 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e31737 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e31738 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b31739 := hb (x (-1) 7)
        have b31740 := hb (x 0 6)
        have b31741 := hb (x 1 5)
        have b31742 := hb (x 2 4)
        have b31743 := hb (x 3 11)
        have b31744 := hb (x 4 10)
        have b31745 := hb (x 5 9)
        have b31746 := hb (x 6 8)
        clear * - r31732 e31733 e31734 e31735 e31736 e31737 e31738 b31739 b31740 b31741 b31742 b31743 b31744 b31745 b31746 d31683 d31707 g10 g8 f31682
        omega
      have d31747 : (x 4 3 && x 4 10).toNat = 0 := by
        have r31748 := hand2 (x 4 3) (x 4 10)
        have b31749 := hb (x 4 10)
        have b31750 := hb (x 4 3 && x 4 10)
        clear * - r31748 b31749 b31750 d31731
        omega
      have d31751 : (x 4 4 && x 4 10).toNat = 0 := by
        have r31752 := hand2 (x 4 4) (x 4 10)
        have b31753 := hb (x 4 10)
        have b31754 := hb (x 4 4 && x 4 10)
        clear * - r31752 b31753 b31754 d31731
        omega
      have d31755 : (x 3 11).toNat = 0 := by
        have r31756 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31757 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e31758 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e31759 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e31760 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e31761 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e31762 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b31763 := hb (x (-1) 7)
        have b31764 := hb (x 0 6)
        have b31765 := hb (x 1 5)
        have b31766 := hb (x 2 4)
        have b31767 := hb (x 3 11)
        have b31768 := hb (x 4 10)
        have b31769 := hb (x 5 9)
        have b31770 := hb (x 6 8)
        clear * - r31756 e31757 e31758 e31759 e31760 e31761 e31762 b31763 b31764 b31765 b31766 b31767 b31768 b31769 b31770 d31683 d31707 d31731 g10 g8 f31682
        omega
      have d31771 : (x 3 5 && x 3 11).toNat = 0 := by
        have r31772 := hand2 (x 3 5) (x 3 11)
        have b31773 := hb (x 3 11)
        have b31774 := hb (x 3 5 && x 3 11)
        clear * - r31772 b31773 b31774 d31755
        omega
      cases h31775 : x 0 7
      · have f31776 : (x 0 7).toNat = 0 := by rw [h31775]; rfl
        have d31777 : (x 0 7 && x 0 14).toNat = 0 := by
          have r31778 := hand1 (x 0 7) (x 0 14)
          have b31779 := hb (x 0 7)
          have b31780 := hb (x 0 7 && x 0 14)
          clear * - r31778 b31779 b31780 f31776
          omega
        have d31781 : (x 0 7 && x 0 13).toNat = 0 := by
          have r31782 := hand1 (x 0 7) (x 0 13)
          have b31783 := hb (x 0 7)
          have b31784 := hb (x 0 7 && x 0 13)
          clear * - r31782 b31783 b31784 f31776
          omega
        have d31785 : (x 0 3 && x 0 7).toNat = 0 := by
          have r31786 := hand2 (x 0 3) (x 0 7)
          have b31787 := hb (x 0 7)
          have b31788 := hb (x 0 3 && x 0 7)
          clear * - r31786 b31787 b31788 f31776
          omega
        cases h31789 : x 0 9
        · have f31790 : (x 0 9).toNat = 0 := by rw [h31789]; rfl
          have d31791 : (x (-4) 4 && x (-4) 13).toNat = 1 := by
            have r31792 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b31793 := hb (x (-6) 6)
            have b31794 := hb (x 0 9)
            have b31795 := hb (x (-1) 1 && x (-1) 10)
            have b31796 := hb (x (-2) 2 && x (-2) 11)
            have b31797 := hb (x (-3) 3 && x (-3) 12)
            have b31798 := hb (x (-4) 4 && x (-4) 13)
            have b31799 := hb (x (-5) 5 && x (-5) 14)
            clear * - r31792 b31793 b31794 b31795 b31796 b31797 b31798 b31799 f31790 g36 d29738 d29867 d29918 d30356
            omega
          have d31800 : (x (-4) 13).toNat = 1 := by
            have r31801 := hand2 (x (-4) 4) (x (-4) 13)
            have b31802 := hb (x (-4) 13)
            have b31803 := hb (x (-4) 4 && x (-4) 13)
            clear * - r31801 b31802 b31803 d31791
            omega
          have d31804 : (x (-4) 1).toNat = 1 := by
            have r31805 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
            have b31806 := hb (x (-4) 1)
            have b31807 := hb (x (-4) 13)
            clear * - r31805 b31806 b31807 d31800
            omega
          have d31808 : (x (-3) 14).toNat = 0 := by
            have r31809 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b31810 := hb (x (-4) 1)
            have b31811 := hb (x (-3) 14)
            clear * - r31809 b31810 b31811 d31804
            omega
          have d31812 : (x (-3) 2).toNat = 0 := by
            have r31813 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
            have b31814 := hb (x (-3) 2)
            have b31815 := hb (x (-3) 14)
            clear * - r31813 b31814 b31815 d31808
            omega
          have d31816 : (x (-3) 10).toNat = 0 := by
            have r31817 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
            have b31818 := hb (x (-3) 2)
            have b31819 := hb (x (-3) 10)
            clear * - r31817 b31818 b31819 d31812
            omega
          have d31820 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
            have r31821 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b31822 := hb (x (-3) 2)
            have b31823 := hb (x (-1) 13)
            have b31824 := hb (x (-2) 1 && x (-2) 14)
            clear * - r31821 b31822 b31823 b31824 g4 d31812
            omega
          have d31825 : (x (-2) 14).toNat = 1 := by
            have r31826 := hand2 (x (-2) 1) (x (-2) 14)
            have b31827 := hb (x (-2) 14)
            have b31828 := hb (x (-2) 1 && x (-2) 14)
            clear * - r31826 b31827 b31828 d31820
            omega
          have d31829 : (x (-3) 1).toNat = 0 := by
            have r31830 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b31831 := hb (x (-3) 1)
            have b31832 := hb (x (-2) 14)
            clear * - r31830 b31831 b31832 d31825
            omega
          have d31833 : (x (-3) 13).toNat = 0 := by
            have r31834 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
            have b31835 := hb (x (-3) 1)
            have b31836 := hb (x (-3) 13)
            clear * - r31834 b31835 b31836 d31829
            omega
          have d31837 : (x (-2) 1).toNat = 1 := by
            have r31838 := hand1 (x (-2) 1) (x (-2) 14)
            have b31839 := hb (x (-2) 1)
            have b31840 := hb (x (-2) 1 && x (-2) 14)
            clear * - r31838 b31839 b31840 d31820
            omega
          have d31841 : (x (-1) 14).toNat = 0 := by
            have r31842 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b31843 := hb (x (-2) 1)
            have b31844 := hb (x (-1) 14)
            clear * - r31842 b31843 b31844 d31837
            omega
          have d31845 : (x (-1) 8 && x (-1) 14).toNat = 0 := by
            have r31846 := hand2 (x (-1) 8) (x (-1) 14)
            have b31847 := hb (x (-1) 14)
            have b31848 := hb (x (-1) 8 && x (-1) 14)
            clear * - r31846 b31847 b31848 d31841
            omega
          have d31849 : (x (-3) 12).toNat = 0 := by
            have r31850 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e31851 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
            have e31852 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
            have b31853 := hb (x (-6) 3)
            have b31854 := hb (x (-5) 2)
            have b31855 := hb (x (-4) 13)
            have b31856 := hb (x (-3) 12)
            clear * - r31850 e31851 e31852 b31853 b31854 b31855 b31856 d31800
            omega
          have d31857 : (x (-5) 2).toNat = 0 := by
            have r31858 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e31859 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
            have e31860 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
            have b31861 := hb (x (-6) 3)
            have b31862 := hb (x (-5) 2)
            have b31863 := hb (x (-4) 13)
            have b31864 := hb (x (-3) 12)
            clear * - r31858 e31859 e31860 b31861 b31862 b31863 b31864 d31849 d31800
            omega
          have d31865 : (x (-4) 1 && x (-4) 14).toNat = 1 := by
            have r31866 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b31867 := hb (x (-5) 2)
            have b31868 := hb (x (-3) 13)
            have b31869 := hb (x (-4) 1 && x (-4) 14)
            clear * - r31866 b31867 b31868 b31869 d31833 d31857
            omega
          have d31870 : (x (-4) 14).toNat = 1 := by
            have r31871 := hand2 (x (-4) 1) (x (-4) 14)
            have b31872 := hb (x (-4) 14)
            have b31873 := hb (x (-4) 1 && x (-4) 14)
            clear * - r31871 b31872 b31873 d31865
            omega
          have d31874 : (x (-5) 1).toNat = 0 := by
            have r31875 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b31876 := hb (x (-5) 1)
            have b31877 := hb (x (-4) 14)
            clear * - r31875 b31876 b31877 d31870
            omega
          have d31878 : (x (-5) 9).toNat = 0 := by
            have r31879 : (x (-5) 9).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp9 (-5))
            have b31880 := hb (x (-5) 1)
            have b31881 := hb (x (-5) 9)
            clear * - r31879 b31880 b31881 d31874
            omega
          have r31882 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r31883 : (x (-5) 8).toNat + (x (-6) 1 && x (-6) 9).toNat + (x (-7) 2 && x (-7) 10).toNat + (x (-8) 3 && x (-8) 11).toNat + (x (-9) 4 && x (-9) 12).toNat + (x (-10) 5 && x (-10) 13).toNat + (x (-11) 6 && x (-11) 14).toNat + (x (-12) 7).toNat = 1 := by have q := hd8 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31884 : (x (-6) 1 && x (-6) 9).toNat = (x (-6) 9).toNat := handr _ _ (fun h => hp9 (-6) (h))
          have e31885 : (x (-7) 2 && x (-7) 10).toNat = (x (-7) 10).toNat := handr _ _ (fun h => hp10 (-7) (h))
          have e31886 : (x (-8) 3 && x (-8) 11).toNat = (x (-8) 11).toNat := handr _ _ (fun h => hp11 (-8) (h))
          have e31887 : (x (-9) 4 && x (-9) 12).toNat = (x (-9) 4).toNat := handl _ _ (fun h => hp4 (-9) (h))
          have e31888 : (x (-10) 5 && x (-10) 13).toNat = (x (-10) 5).toNat := handl _ _ (fun h => hp5 (-10) (h))
          have e31889 : (x (-11) 6 && x (-11) 14).toNat = (x (-11) 6).toNat := handl _ _ (fun h => hp6 (-11) (h))
          have r31890 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31891 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
          have e31892 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
          have e31893 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
          have e31894 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
          have e31895 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
          have e31896 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
          have r31897 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31898 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
          have e31899 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
          have e31900 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
          have e31901 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
          have e31902 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
          have e31903 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
          have r31904 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31905 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
          have e31906 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
          have e31907 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
          have e31908 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
          have e31909 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
          have e31910 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
          have r31911 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31912 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
          have e31913 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
          have r31914 : 1 ≤ (x 3 4).toNat + (x 2 1 && x 2 5).toNat + (x 1 2 && x 1 6).toNat + (x 0 3 && x 0 7).toNat + (x (-1) 4 && x (-1) 8).toNat + (x (-2) 5 && x (-2) 9).toNat + (x (-3) 6 && x (-3) 10).toNat + (x (-4) 7 && x (-4) 11).toNat + (x (-5) 8 && x (-5) 12).toNat + (x (-6) 9 && x (-6) 13).toNat + (x (-7) 10 && x (-7) 14).toNat + (x (-8) 11).toNat := by have q := hcov4 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31915 : (x 2 1 && x 2 5).toNat = (x 2 5).toNat := handr _ _ (fun h => hp13 2 (hp5 2 (h)))
          have e31916 : (x (-7) 10 && x (-7) 14).toNat = (x (-7) 10).toNat := handl _ _ (fun h => hp2 (-7) (hp10 (-7) (h)))
          have r31917 : 1 ≤ (x 3 5).toNat + (x 2 1 && x 2 6).toNat + (x 1 2 && x 1 7).toNat + (x 0 3 && x 0 8).toNat + (x (-1) 4 && x (-1) 9).toNat + (x (-2) 5 && x (-2) 10).toNat + (x (-3) 6 && x (-3) 11).toNat + (x (-4) 7 && x (-4) 12).toNat + (x (-5) 8 && x (-5) 13).toNat + (x (-6) 9 && x (-6) 14).toNat + (x (-7) 10).toNat := by have q := hcov5 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r31918 : 1 ≤ (x 8 5).toNat + (x 7 1 && x 7 6).toNat + (x 6 2 && x 6 7).toNat + (x 5 3 && x 5 8).toNat + (x 4 4 && x 4 9).toNat + (x 3 5 && x 3 10).toNat + (x 2 6 && x 2 11).toNat + (x 1 7 && x 1 12).toNat + (x 0 8 && x 0 13).toNat + (x (-1) 9 && x (-1) 14).toNat + (x (-2) 10).toNat := by have q := hcov5 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r31919 : 1 ≤ (x 7 6).toNat + (x 6 1 && x 6 7).toNat + (x 5 2 && x 5 8).toNat + (x 4 3 && x 4 9).toNat + (x 3 4 && x 3 10).toNat + (x 2 5 && x 2 11).toNat + (x 1 6 && x 1 12).toNat + (x 0 7 && x 0 13).toNat + (x (-1) 8 && x (-1) 14).toNat + (x (-2) 9).toNat := by have q := hcov6 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r31920 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r31921 : 1 ≤ (x 7 7).toNat + (x 6 1 && x 6 8).toNat + (x 5 2 && x 5 9).toNat + (x 4 3 && x 4 10).toNat + (x 3 4 && x 3 11).toNat + (x 2 5 && x 2 12).toNat + (x 1 6 && x 1 13).toNat + (x 0 7 && x 0 14).toNat + (x (-1) 8).toNat := by have q := hcov7 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r31922 : 1 ≤ (x (-5) 9).toNat + (x (-6) 1 && x (-6) 10).toNat + (x (-7) 2 && x (-7) 11).toNat + (x (-8) 3 && x (-8) 12).toNat + (x (-9) 4 && x (-9) 13).toNat + (x (-10) 5 && x (-10) 14).toNat + (x (-11) 6).toNat := by have q := hcov9 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r31923 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r31924 : (x (-7) 10).toNat ≤ (x (-7) 2).toNat := himp _ _ (hp10 (-7))
          have r31925 := hand2 (x (-5) 8) (x (-5) 12)
          have r31926 := hand2 (x (-6) 9) (x (-6) 13)
          have r31927 := hand2 (x 2 1) (x 2 6)
          have r31928 := hand1 (x (-6) 9) (x (-6) 14)
          have r31929 := hand1 (x 7 1) (x 7 6)
          have r31930 := hand1 (x 6 2) (x 6 7)
          have r31931 := hand2 (x 6 1) (x 6 7)
          have r31932 := hand1 (x 7 1) (x 7 7)
          have r31933 := hand1 (x (-8) 3) (x (-8) 12)
          have r31934 := hand1 (x (-9) 4) (x (-9) 13)
          have r31935 := hand1 (x (-10) 5) (x (-10) 14)
          have r31936 := hand2 (x (-6) 1) (x (-6) 14)
          linarith only [r31882, r31883, e31884, e31885, e31886, e31887, e31888, e31889, r31890, e31891, e31892, e31893, e31894, e31895, e31896, r31897, e31898, e31899, e31900, e31901, e31902, e31903, r31904, e31905, e31906, e31907, e31908, e31909, e31910, r31911, e31912, e31913, r31914, e31915, e31916, r31917, r31918, r31919, r31920, r31921, r31922, r31923, r31924, r31925, r31926, r31927, r31928, r31929, r31930, r31931, r31932, r31933, r31934, r31935, r31936, d31878, d29894, d29890, d31816, d29871, d29742, g2, d30316, d30284, d30260, d29779, d31785, d30183, d30207, d30227, d30312, d29791, d30344, g22, d29746, d29875, d30308, d29906, d31108, d31140, d30019, d31164, d29811, d30340, g23, d31104, d31136, d30015, d30288, d29775, d31781, d31845, d31703, d31727, d31751, d31771, g29, g30, d30332, d31699, d31723, d31747, d30264, g34, g35, d31777, d29942, d29970]
        · have f32045 : (x 0 9).toNat = 1 := by rw [h31789]; rfl
          have d32046 : (x 1 8).toNat = 0 := by
            have r32047 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e32048 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
            have e32049 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
            have e32050 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
            have e32051 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
            have e32052 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
            have e32053 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
            have b32054 := hb (x (-6) 7)
            have b32055 := hb (x (-5) 6)
            have b32056 := hb (x (-4) 5)
            have b32057 := hb (x (-3) 4)
            have b32058 := hb (x (-2) 11)
            have b32059 := hb (x (-1) 10)
            have b32060 := hb (x 0 9)
            have b32061 := hb (x 1 8)
            clear * - r32047 e32048 e32049 e32050 e32051 e32052 e32053 b32054 b32055 b32056 b32057 b32058 b32059 b32060 b32061 f32045 d29835 d29851
            omega
          have d32062 : (x (-3) 4).toNat = 0 := by
            have r32063 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e32064 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
            have e32065 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
            have e32066 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
            have e32067 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
            have e32068 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
            have e32069 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
            have b32070 := hb (x (-6) 7)
            have b32071 := hb (x (-5) 6)
            have b32072 := hb (x (-4) 5)
            have b32073 := hb (x (-3) 4)
            have b32074 := hb (x (-2) 11)
            have b32075 := hb (x (-1) 10)
            have b32076 := hb (x 0 9)
            have b32077 := hb (x 1 8)
            clear * - r32063 e32064 e32065 e32066 e32067 e32068 e32069 b32070 b32071 b32072 b32073 b32074 b32075 b32076 b32077 d32046 f32045 d29835 d29851
            omega
          have d32078 : (x (-3) 4 && x (-3) 14).toNat = 0 := by
            have r32079 := hand1 (x (-3) 4) (x (-3) 14)
            have b32080 := hb (x (-3) 4)
            have b32081 := hb (x (-3) 4 && x (-3) 14)
            clear * - r32079 b32080 b32081 d32062
            omega
          have d32082 : (x (-4) 5).toNat = 1 := by
            have r32083 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b32084 := hb (x (-4) 5)
            have b32085 := hb (x 1 10)
            have b32086 := hb (x 0 1 && x 0 11)
            have b32087 := hb (x (-1) 2 && x (-1) 12)
            have b32088 := hb (x (-2) 3 && x (-2) 13)
            have b32089 := hb (x (-3) 4 && x (-3) 14)
            clear * - r32083 b32084 b32085 b32086 b32087 b32088 b32089 d29795 g46 d29831 d29847 d32078
            omega
          have r32090 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e32091 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e32092 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e32093 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e32094 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e32095 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e32096 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b32097 := hb (x (-6) 7)
          have b32098 := hb (x (-5) 6)
          have b32099 := hb (x (-4) 5)
          have b32100 := hb (x (-3) 4)
          have b32101 := hb (x (-2) 11)
          have b32102 := hb (x (-1) 10)
          have b32103 := hb (x 0 9)
          have b32104 := hb (x 1 8)
          linarith only [r32090, e32091, e32092, e32093, e32094, e32095, e32096, b32097, b32098, b32099, b32100, b32101, b32102, b32103, b32104, d32046, f32045, d29835, d29851, d32062, d32082]
      · have f32105 : (x 0 7).toNat = 1 := by rw [h31775]; rfl
        have d32106 : (x 7 8).toNat = 0 := by
          have r32107 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e32108 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e32109 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e32110 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e32111 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e32112 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e32113 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have b32114 := hb (x 0 7)
          have b32115 := hb (x 1 6)
          have b32116 := hb (x 2 5)
          have b32117 := hb (x 3 4)
          have b32118 := hb (x 4 11)
          have b32119 := hb (x 5 10)
          have b32120 := hb (x 6 9)
          have b32121 := hb (x 7 8)
          clear * - r32107 e32108 e32109 e32110 e32111 e32112 e32113 b32114 b32115 b32116 b32117 b32118 b32119 b32120 b32121 d30260 d30284 d29771 f32105
          omega
        have d32122 : (x 7 1 && x 7 8).toNat = 0 := by
          have r32123 := hand2 (x 7 1) (x 7 8)
          have b32124 := hb (x 7 8)
          have b32125 := hb (x 7 1 && x 7 8)
          clear * - r32123 b32124 b32125 d32106
          omega
        have d32126 : (x 7 4 && x 7 8).toNat = 0 := by
          have r32127 := hand2 (x 7 4) (x 7 8)
          have b32128 := hb (x 7 8)
          have b32129 := hb (x 7 4 && x 7 8)
          clear * - r32127 b32128 b32129 d32106
          omega
        have d32130 : (x 6 9).toNat = 0 := by
          have r32131 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e32132 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e32133 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e32134 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e32135 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e32136 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e32137 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have b32138 := hb (x 0 7)
          have b32139 := hb (x 1 6)
          have b32140 := hb (x 2 5)
          have b32141 := hb (x 3 4)
          have b32142 := hb (x 4 11)
          have b32143 := hb (x 5 10)
          have b32144 := hb (x 6 9)
          have b32145 := hb (x 7 8)
          clear * - r32131 e32132 e32133 e32134 e32135 e32136 e32137 b32138 b32139 b32140 b32141 b32142 b32143 b32144 b32145 d32106 d30260 d30284 d29771 f32105
          omega
        have d32146 : (x 6 2 && x 6 9).toNat = 0 := by
          have r32147 := hand2 (x 6 2) (x 6 9)
          have b32148 := hb (x 6 9)
          have b32149 := hb (x 6 2 && x 6 9)
          clear * - r32147 b32148 b32149 d32130
          omega
        have d32150 : (x 6 5 && x 6 9).toNat = 0 := by
          have r32151 := hand2 (x 6 5) (x 6 9)
          have b32152 := hb (x 6 9)
          have b32153 := hb (x 6 5 && x 6 9)
          clear * - r32151 b32152 b32153 d32130
          omega
        have d32154 : (x 5 10).toNat = 0 := by
          have r32155 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e32156 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e32157 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e32158 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e32159 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e32160 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e32161 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have b32162 := hb (x 0 7)
          have b32163 := hb (x 1 6)
          have b32164 := hb (x 2 5)
          have b32165 := hb (x 3 4)
          have b32166 := hb (x 4 11)
          have b32167 := hb (x 5 10)
          have b32168 := hb (x 6 9)
          have b32169 := hb (x 7 8)
          clear * - r32155 e32156 e32157 e32158 e32159 e32160 e32161 b32162 b32163 b32164 b32165 b32166 b32167 b32168 b32169 d32106 d32130 d30260 d30284 d29771 f32105
          omega
        have d32170 : (x 5 3 && x 5 10).toNat = 0 := by
          have r32171 := hand2 (x 5 3) (x 5 10)
          have b32172 := hb (x 5 10)
          have b32173 := hb (x 5 3 && x 5 10)
          clear * - r32171 b32172 b32173 d32154
          omega
        have d32174 : (x 5 6 && x 5 10).toNat = 0 := by
          have r32175 := hand2 (x 5 6) (x 5 10)
          have b32176 := hb (x 5 10)
          have b32177 := hb (x 5 6 && x 5 10)
          clear * - r32175 b32176 b32177 d32154
          omega
        have d32178 : (x 4 11).toNat = 0 := by
          have r32179 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e32180 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e32181 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e32182 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e32183 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e32184 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e32185 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have b32186 := hb (x 0 7)
          have b32187 := hb (x 1 6)
          have b32188 := hb (x 2 5)
          have b32189 := hb (x 3 4)
          have b32190 := hb (x 4 11)
          have b32191 := hb (x 5 10)
          have b32192 := hb (x 6 9)
          have b32193 := hb (x 7 8)
          clear * - r32179 e32180 e32181 e32182 e32183 e32184 e32185 b32186 b32187 b32188 b32189 b32190 b32191 b32192 b32193 d32106 d32130 d32154 d30260 d30284 d29771 f32105
          omega
        have d32194 : (x 4 4 && x 4 11).toNat = 0 := by
          have r32195 := hand2 (x 4 4) (x 4 11)
          have b32196 := hb (x 4 11)
          have b32197 := hb (x 4 4 && x 4 11)
          clear * - r32195 b32196 b32197 d32178
          omega
        have d32198 : (x 4 7 && x 4 11).toNat = 0 := by
          have r32199 := hand2 (x 4 7) (x 4 11)
          have b32200 := hb (x 4 11)
          have b32201 := hb (x 4 7 && x 4 11)
          clear * - r32199 b32200 b32201 d32178
          omega
        have d32202 : (x 8 7).toNat = 1 := by
          have r32203 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := by have q := hcov7 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b32204 := hb (x 0 8)
          have b32205 := hb (x 8 7)
          have b32206 := hb (x 7 1 && x 7 8)
          have b32207 := hb (x 6 2 && x 6 9)
          have b32208 := hb (x 5 3 && x 5 10)
          have b32209 := hb (x 4 4 && x 4 11)
          have b32210 := hb (x 3 5 && x 3 12)
          have b32211 := hb (x 2 6 && x 2 13)
          have b32212 := hb (x 1 7 && x 1 14)
          clear * - r32203 b32204 b32205 b32206 b32207 b32208 b32209 b32210 b32211 b32212 d32122 d32146 d32170 d32194 d30256 d30276 d29767 d30316
          omega
        have d32213 : (x 15 8).toNat = 0 := by
          have r32214 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e32215 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
          have e32216 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
          have e32217 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
          have e32218 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
          have e32219 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
          have e32220 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
          have b32221 := hb (x 8 7)
          have b32222 := hb (x 9 6)
          have b32223 := hb (x 10 5)
          have b32224 := hb (x 11 4)
          have b32225 := hb (x 12 11)
          have b32226 := hb (x 13 10)
          have b32227 := hb (x 14 9)
          have b32228 := hb (x 15 8)
          clear * - r32214 e32215 e32216 e32217 e32218 e32219 e32220 b32221 b32222 b32223 b32224 b32225 b32226 b32227 b32228 d32202
          omega
        have d32229 : (x 14 9).toNat = 0 := by
          have r32230 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e32231 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
          have e32232 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
          have e32233 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
          have e32234 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
          have e32235 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
          have e32236 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
          have b32237 := hb (x 8 7)
          have b32238 := hb (x 9 6)
          have b32239 := hb (x 10 5)
          have b32240 := hb (x 11 4)
          have b32241 := hb (x 12 11)
          have b32242 := hb (x 13 10)
          have b32243 := hb (x 14 9)
          have b32244 := hb (x 15 8)
          clear * - r32230 e32231 e32232 e32233 e32234 e32235 e32236 b32237 b32238 b32239 b32240 b32241 b32242 b32243 b32244 d32213 d32202
          omega
        have d32245 : (x 13 10).toNat = 0 := by
          have r32246 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e32247 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
          have e32248 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
          have e32249 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
          have e32250 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
          have e32251 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
          have e32252 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
          have b32253 := hb (x 8 7)
          have b32254 := hb (x 9 6)
          have b32255 := hb (x 10 5)
          have b32256 := hb (x 11 4)
          have b32257 := hb (x 12 11)
          have b32258 := hb (x 13 10)
          have b32259 := hb (x 14 9)
          have b32260 := hb (x 15 8)
          clear * - r32246 e32247 e32248 e32249 e32250 e32251 e32252 b32253 b32254 b32255 b32256 b32257 b32258 b32259 b32260 d32213 d32229 d32202
          omega
        have d32261 : (x 13 1 && x 13 10).toNat = 0 := by
          have r32262 := hand2 (x 13 1) (x 13 10)
          have b32263 := hb (x 13 10)
          have b32264 := hb (x 13 1 && x 13 10)
          clear * - r32262 b32263 b32264 d32245
          omega
        have d32265 : (x 12 11).toNat = 0 := by
          have r32266 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e32267 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
          have e32268 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
          have e32269 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
          have e32270 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
          have e32271 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
          have e32272 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
          have b32273 := hb (x 8 7)
          have b32274 := hb (x 9 6)
          have b32275 := hb (x 10 5)
          have b32276 := hb (x 11 4)
          have b32277 := hb (x 12 11)
          have b32278 := hb (x 13 10)
          have b32279 := hb (x 14 9)
          have b32280 := hb (x 15 8)
          clear * - r32266 e32267 e32268 e32269 e32270 e32271 e32272 b32273 b32274 b32275 b32276 b32277 b32278 b32279 b32280 d32213 d32229 d32245 d32202
          omega
        have d32281 : (x 12 2 && x 12 11).toNat = 0 := by
          have r32282 := hand2 (x 12 2) (x 12 11)
          have b32283 := hb (x 12 11)
          have b32284 := hb (x 12 2 && x 12 11)
          clear * - r32282 b32283 b32284 d32265
          omega
        have d32285 : (x 11 4).toNat = 0 := by
          have r32286 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e32287 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
          have e32288 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
          have e32289 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
          have e32290 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
          have e32291 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
          have e32292 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
          have b32293 := hb (x 8 7)
          have b32294 := hb (x 9 6)
          have b32295 := hb (x 10 5)
          have b32296 := hb (x 11 4)
          have b32297 := hb (x 12 11)
          have b32298 := hb (x 13 10)
          have b32299 := hb (x 14 9)
          have b32300 := hb (x 15 8)
          clear * - r32286 e32287 e32288 e32289 e32290 e32291 e32292 b32293 b32294 b32295 b32296 b32297 b32298 b32299 b32300 d32213 d32229 d32245 d32265 d32202
          omega
        have d32301 : (x 11 4 && x 11 13).toNat = 0 := by
          have r32302 := hand1 (x 11 4) (x 11 13)
          have b32303 := hb (x 11 4)
          have b32304 := hb (x 11 4 && x 11 13)
          clear * - r32302 b32303 b32304 d32285
          omega
        have d32305 : (x 10 5).toNat = 0 := by
          have r32306 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e32307 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
          have e32308 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
          have e32309 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
          have e32310 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
          have e32311 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
          have e32312 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
          have b32313 := hb (x 8 7)
          have b32314 := hb (x 9 6)
          have b32315 := hb (x 10 5)
          have b32316 := hb (x 11 4)
          have b32317 := hb (x 12 11)
          have b32318 := hb (x 13 10)
          have b32319 := hb (x 14 9)
          have b32320 := hb (x 15 8)
          clear * - r32306 e32307 e32308 e32309 e32310 e32311 e32312 b32313 b32314 b32315 b32316 b32317 b32318 b32319 b32320 d32213 d32229 d32245 d32265 d32285 d32202
          omega
        have d32321 : (x 10 5 && x 10 14).toNat = 0 := by
          have r32322 := hand1 (x 10 5) (x 10 14)
          have b32323 := hb (x 10 5)
          have b32324 := hb (x 10 5 && x 10 14)
          clear * - r32322 b32323 b32324 d32305
          omega
        have d32325 : (x 9 6).toNat = 0 := by
          have r32326 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e32327 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
          have e32328 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
          have e32329 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
          have e32330 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
          have e32331 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
          have e32332 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
          have b32333 := hb (x 8 7)
          have b32334 := hb (x 9 6)
          have b32335 := hb (x 10 5)
          have b32336 := hb (x 11 4)
          have b32337 := hb (x 12 11)
          have b32338 := hb (x 13 10)
          have b32339 := hb (x 14 9)
          have b32340 := hb (x 15 8)
          clear * - r32326 e32327 e32328 e32329 e32330 e32331 e32332 b32333 b32334 b32335 b32336 b32337 b32338 b32339 b32340 d32213 d32229 d32245 d32265 d32285 d32305 d32202
          omega
        have d32341 : (x 9 2 && x 9 6).toNat = 0 := by
          have r32342 := hand2 (x 9 2) (x 9 6)
          have b32343 := hb (x 9 6)
          have b32344 := hb (x 9 2 && x 9 6)
          clear * - r32342 b32343 b32344 d32325
          omega
        have d32345 : (x 8 3 && x 8 7).toNat = 1 := by
          have r32346 : 1 ≤ (x 11 4).toNat + (x 10 1 && x 10 5).toNat + (x 9 2 && x 9 6).toNat + (x 8 3 && x 8 7).toNat + (x 7 4 && x 7 8).toNat + (x 6 5 && x 6 9).toNat + (x 5 6 && x 5 10).toNat + (x 4 7 && x 4 11).toNat + (x 3 8 && x 3 12).toNat + (x 2 9 && x 2 13).toNat + (x 1 10 && x 1 14).toNat + (x 0 11).toNat := by have q := hcov4 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e32347 : (x 10 1 && x 10 5).toNat = (x 10 5).toNat := handr _ _ (fun h => hp13 10 (hp5 10 (h)))
          have e32348 : (x 1 10 && x 1 14).toNat = (x 1 10).toNat := handl _ _ (fun h => hp2 1 (hp10 1 (h)))
          have b32349 := hb (x 0 11)
          have b32350 := hb (x 1 10)
          have b32351 := hb (x 10 5)
          have b32352 := hb (x 11 4)
          have b32353 := hb (x 9 2 && x 9 6)
          have b32354 := hb (x 8 3 && x 8 7)
          have b32355 := hb (x 7 4 && x 7 8)
          have b32356 := hb (x 6 5 && x 6 9)
          have b32357 := hb (x 5 6 && x 5 10)
          have b32358 := hb (x 4 7 && x 4 11)
          have b32359 := hb (x 3 8 && x 3 12)
          have b32360 := hb (x 2 9 && x 2 13)
          clear * - r32346 e32347 e32348 b32349 b32350 b32351 b32352 b32353 b32354 b32355 b32356 b32357 b32358 b32359 b32360 d32285 d32305 d32341 d32126 d32150 d32174 d32198 d30163 d30280 d29795 g7
          omega
        have d32361 : (x 8 3).toNat = 1 := by
          have r32362 := hand1 (x 8 3) (x 8 7)
          have b32363 := hb (x 8 3)
          have b32364 := hb (x 8 3 && x 8 7)
          clear * - r32362 b32363 b32364 d32345
          omega
        have d32365 : (x 11 12).toNat = 0 := by
          have r32366 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e32367 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e32368 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have b32369 := hb (x 8 3)
          have b32370 := hb (x 9 2)
          have b32371 := hb (x 10 13)
          have b32372 := hb (x 11 12)
          clear * - r32366 e32367 e32368 b32369 b32370 b32371 b32372 d32361
          omega
        have d32373 : (x 11 1 && x 11 12).toNat = 0 := by
          have r32374 := hand2 (x 11 1) (x 11 12)
          have b32375 := hb (x 11 12)
          have b32376 := hb (x 11 1 && x 11 12)
          clear * - r32374 b32375 b32376 d32365
          omega
        have d32377 : (x 11 3 && x 11 12).toNat = 0 := by
          have r32378 := hand2 (x 11 3) (x 11 12)
          have b32379 := hb (x 11 12)
          have b32380 := hb (x 11 3 && x 11 12)
          clear * - r32378 b32379 b32380 d32365
          omega
        have d32381 : (x 10 13).toNat = 0 := by
          have r32382 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e32383 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e32384 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have b32385 := hb (x 8 3)
          have b32386 := hb (x 9 2)
          have b32387 := hb (x 10 13)
          have b32388 := hb (x 11 12)
          clear * - r32382 e32383 e32384 b32385 b32386 b32387 b32388 d32365 d32361
          omega
        have d32389 : (x 10 2 && x 10 13).toNat = 0 := by
          have r32390 := hand2 (x 10 2) (x 10 13)
          have b32391 := hb (x 10 13)
          have b32392 := hb (x 10 2 && x 10 13)
          clear * - r32390 b32391 b32392 d32381
          omega
        have d32393 : (x 10 4 && x 10 13).toNat = 0 := by
          have r32394 := hand2 (x 10 4) (x 10 13)
          have b32395 := hb (x 10 13)
          have b32396 := hb (x 10 4 && x 10 13)
          clear * - r32394 b32395 b32396 d32381
          omega
        have d32397 : (x 9 2).toNat = 0 := by
          have r32398 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e32399 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e32400 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have b32401 := hb (x 8 3)
          have b32402 := hb (x 9 2)
          have b32403 := hb (x 10 13)
          have b32404 := hb (x 11 12)
          clear * - r32398 e32399 e32400 b32401 b32402 b32403 b32404 d32365 d32381 d32361
          omega
        have r32405 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r32406 : (x 9 1).toNat + (x 8 2).toNat + (x 7 3).toNat + (x 6 4).toNat + (x 5 5).toNat + (x 4 6).toNat + (x 3 7).toNat + (x 2 8).toNat + (x 1 9).toNat + (x 0 10).toNat + (x (-1) 11).toNat + (x (-2) 12).toNat + (x (-3) 13).toNat + (x (-4) 14).toNat = 3 := by have q := hcount 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r32407 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r32408 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r32409 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e32410 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e32411 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e32412 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e32413 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e32414 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e32415 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have r32416 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e32417 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
        have e32418 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
        have e32419 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
        have e32420 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
        have e32421 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
        have e32422 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
        have r32423 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e32424 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
        have e32425 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
        have e32426 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
        have e32427 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
        have e32428 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
        have e32429 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
        have r32430 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e32431 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e32432 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have r32433 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e32434 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
        have e32435 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
        have r32436 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r32437 : 1 ≤ (x 8 4).toNat + (x 7 1 && x 7 5).toNat + (x 6 2 && x 6 6).toNat + (x 5 3 && x 5 7).toNat + (x 4 4 && x 4 8).toNat + (x 3 5 && x 3 9).toNat + (x 2 6 && x 2 10).toNat + (x 1 7 && x 1 11).toNat + (x 0 8 && x 0 12).toNat + (x (-1) 9 && x (-1) 13).toNat + (x (-2) 10 && x (-2) 14).toNat + (x (-3) 11).toNat := by have q := hcov4 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e32438 : (x 7 1 && x 7 5).toNat = (x 7 5).toNat := handr _ _ (fun h => hp13 7 (hp5 7 (h)))
        have e32439 : (x (-2) 10 && x (-2) 14).toNat = (x (-2) 10).toNat := handl _ _ (fun h => hp2 (-2) (hp10 (-2) (h)))
        have r32440 : 1 ≤ (x 12 4).toNat + (x 11 1 && x 11 5).toNat + (x 10 2 && x 10 6).toNat + (x 9 3 && x 9 7).toNat + (x 8 4 && x 8 8).toNat + (x 7 5 && x 7 9).toNat + (x 6 6 && x 6 10).toNat + (x 5 7 && x 5 11).toNat + (x 4 8 && x 4 12).toNat + (x 3 9 && x 3 13).toNat + (x 2 10 && x 2 14).toNat + (x 1 11).toNat := by have q := hcov4 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e32441 : (x 11 1 && x 11 5).toNat = (x 11 5).toNat := handr _ _ (fun h => hp13 11 (hp5 11 (h)))
        have e32442 : (x 2 10 && x 2 14).toNat = (x 2 10).toNat := handl _ _ (fun h => hp2 2 (hp10 2 (h)))
        have r32443 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r32444 : 1 ≤ (x 10 6).toNat + (x 9 1 && x 9 7).toNat + (x 8 2 && x 8 8).toNat + (x 7 3 && x 7 9).toNat + (x 6 4 && x 6 10).toNat + (x 5 5 && x 5 11).toNat + (x 4 6 && x 4 12).toNat + (x 3 7 && x 3 13).toNat + (x 2 8 && x 2 14).toNat + (x 1 9).toNat := by have q := hcov6 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r32445 : 1 ≤ (x 14 9).toNat + (x 13 1 && x 13 10).toNat + (x 12 2 && x 12 11).toNat + (x 11 3 && x 11 12).toNat + (x 10 4 && x 10 13).toNat + (x 9 5 && x 9 14).toNat + (x 8 6).toNat := by have q := hcov9 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r32446 : 1 ≤ (x 15 9).toNat + (x 14 1 && x 14 10).toNat + (x 13 2 && x 13 11).toNat + (x 12 3 && x 12 12).toNat + (x 11 4 && x 11 13).toNat + (x 10 5 && x 10 14).toNat + (x 9 6).toNat := by have q := hcov9 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r32447 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r32448 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r32449 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r32450 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r32451 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r32452 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
        have r32453 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
        have r32454 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
        have r32455 : (x 8 6).toNat ≤ (x 8 14).toNat := himp _ _ (hp6 8)
        have r32456 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
        have r32457 := hand2 (x 6 2) (x 6 6)
        have r32458 := hand2 (x 5 3) (x 5 7)
        have r32459 := hand1 (x 10 2) (x 10 6)
        have r32460 := hand1 (x 9 3) (x 9 7)
        have r32461 := hand2 (x 8 4) (x 8 8)
        have r32462 := hand1 (x 7 5) (x 7 9)
        have r32463 := hand1 (x 6 6) (x 6 10)
        have r32464 := hand1 (x 5 7) (x 5 11)
        have r32465 := hand2 (x 7 1) (x 7 7)
        have r32466 := hand2 (x 9 1) (x 9 7)
        have r32467 := hand2 (x 8 2) (x 8 8)
        have r32468 := hand1 (x 7 3) (x 7 9)
        have r32469 := hand1 (x 6 4) (x 6 10)
        have r32470 := hand1 (x 5 5) (x 5 11)
        have r32471 := hand1 (x 4 6) (x 4 12)
        have r32472 := hand1 (x 3 7) (x 3 13)
        have r32473 := hand1 (x 9 5) (x 9 14)
        have r32474 := hand2 (x 14 1) (x 14 10)
        have r32475 := hand2 (x 13 2) (x 13 11)
        have r32476 := hand2 (x 12 3) (x 12 12)
        have r32477 := hand1 (x 9 3) (x 9 14)
        have r32478 := hand2 (x (-3) 1) (x (-3) 14)
        have r32479 := hand2 (x (-2) 1) (x (-2) 14)
        have r32480 := hand1 (x 9 1) (x 9 14)
        have r32481 := hand1 (x 10 1) (x 10 14)
        have b32482 := hb (x (-6) 14)
        linarith only [r32405, r32406, r32407, r32408, r32409, e32410, e32411, e32412, e32413, e32414, e32415, r32416, e32417, e32418, e32419, e32420, e32421, e32422, r32423, e32424, e32425, e32426, e32427, e32428, e32429, r32430, e32431, e32432, r32433, e32434, e32435, r32436, r32437, e32438, e32439, r32440, e32441, e32442, r32443, r32444, r32445, r32446, r32447, r32448, r32449, r32450, r32451, r32452, r32453, r32454, r32455, r32456, r32457, r32458, r32459, r32460, r32461, r32462, r32463, r32464, r32465, r32466, r32467, r32468, r32469, r32470, r32471, r32472, r32473, r32474, r32475, r32476, r32477, r32478, r32479, r32480, r32481, b32482, d29894, d29890, d29871, d29742, g2, g3, g4, d30316, g6, g7, d29722, g9, d29795, d30095, g11, d29974, d30071, d30147, d30047, d30023, d32361, d32397, d32325, d32381, d32265, d32229, d30043, d30067, d30091, d30111, d30348, g21, d30039, d30063, d31703, d31727, d31751, d31771, g29, g30, d30332, g31, d32261, d32281, d32377, d32393, d32301, d32321, d32373, d32389]

theorem cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_a1 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-4) 6).toNat = 0)
    (g1 : (x (-1) 5).toNat = 0)
    (g2 : (x (-1) 9).toNat = 0)
    (g3 : (x (-1) 11).toNat = 0)
    (g4 : (x (-1) 13).toNat = 0)
    (g5 : (x 0 4).toNat = 1)
    (g6 : (x 0 10).toNat = 1)
    (g7 : (x 0 11).toNat = 0)
    (g8 : (x 1 5).toNat = 0)
    (g9 : (x 1 9).toNat = 0)
    (g10 : (x 2 4).toNat = 0)
    (g11 : (x 2 8).toNat = 0)
    (g12 : (x (-1) 3 && x (-1) 7).toNat = 0)
    (g13 : (x (-2) 4 && x (-2) 8).toNat = 0)
    (g14 : (x (-3) 5 && x (-3) 9).toNat = 0)
    (g15 : (x (-4) 6 && x (-4) 10).toNat = 0)
    (g16 : (x (-5) 7 && x (-5) 11).toNat = 0)
    (g17 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g18 : (x 2 4 && x 2 8).toNat = 0)
    (g19 : (x 1 5 && x 1 9).toNat = 0)
    (g20 : (x (-1) 7 && x (-1) 11).toNat = 0)
    (g21 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g22 : (x (-1) 4 && x (-1) 9).toNat = 0)
    (g23 : (x (-1) 9 && x (-1) 14).toNat = 0)
    (g24 : (x (-1) 3 && x (-1) 9).toNat = 0)
    (g25 : (x (-2) 4 && x (-2) 10).toNat = 0)
    (g26 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g27 : (x (-4) 6 && x (-4) 12).toNat = 0)
    (g28 : (x (-5) 7 && x (-5) 13).toNat = 0)
    (g29 : (x 2 6 && x 2 12).toNat = 0)
    (g30 : (x 1 7 && x 1 13).toNat = 0)
    (g31 : (x 2 8 && x 2 14).toNat = 0)
    (g32 : (x 2 4 && x 2 11).toNat = 0)
    (g33 : (x 1 5 && x 1 12).toNat = 0)
    (g34 : (x 2 5 && x 2 12).toNat = 0)
    (g35 : (x 1 6 && x 1 13).toNat = 0)
    (g36 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g37 : (x 0 2 && x 0 11).toNat = 0)
    (g38 : (x (-1) 3 && x (-1) 12).toNat = 0)
    (g39 : (x (-2) 4 && x (-2) 13).toNat = 0)
    (g40 : (x (-3) 5 && x (-3) 14).toNat = 0)
    (g41 : (x (-1) 4 && x (-1) 13).toNat = 0)
    (g42 : (x 2 3 && x 2 12).toNat = 0)
    (g43 : (x 1 4 && x 1 13).toNat = 0)
    (g44 : (x 2 4 && x 2 13).toNat = 0)
    (g45 : (x 1 5 && x 1 14).toNat = 0)
    (g46 : (x 0 1 && x 0 11).toNat = 0)
    (g47 : (x 2 4 && x 2 14).toNat = 0)
    (g48 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g49 : (x (-1) 1 && x (-1) 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_a1_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49
