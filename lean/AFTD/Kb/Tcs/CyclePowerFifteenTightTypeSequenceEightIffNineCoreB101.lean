import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b101

Topic: combinatorics   Node: 37419d7ce4a4

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core: under the layer-free tight-cover constraints for k = 15 and 70 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b101_aux (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x (-4) 5).toNat = 0)
    (g2 : (x (-2) 11).toNat = 0)
    (g3 : (x (-1) 5).toNat = 0)
    (g4 : (x (-1) 9).toNat = 0)
    (g5 : (x (-1) 10).toNat = 0)
    (g6 : (x (-1) 11).toNat = 0)
    (g7 : (x (-1) 13).toNat = 0)
    (g8 : (x 0 4).toNat = 1)
    (g9 : (x 0 5).toNat = 0)
    (g10 : (x 0 8).toNat = 0)
    (g11 : (x 0 9).toNat = 1)
    (g12 : (x 1 2).toNat = 0)
    (g13 : (x 1 5).toNat = 0)
    (g14 : (x 1 6).toNat = 0)
    (g15 : (x 1 8).toNat = 0)
    (g16 : (x 1 10).toNat = 0)
    (g17 : (x 2 4).toNat = 0)
    (g18 : (x 2 5).toNat = 0)
    (g19 : (x 3 4).toNat = 0)
    (g20 : (x (-1) 3 && x (-1) 7).toNat = 0)
    (g21 : (x 0 4 && x 0 8).toNat = 0)
    (g22 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g23 : (x 1 4 && x 1 8).toNat = 0)
    (g24 : (x 0 5 && x 0 9).toNat = 0)
    (g25 : (x (-1) 6 && x (-1) 10).toNat = 0)
    (g26 : (x (-2) 7 && x (-2) 11).toNat = 0)
    (g27 : (x 2 4 && x 2 8).toNat = 0)
    (g28 : (x 1 5 && x 1 9).toNat = 0)
    (g29 : (x (-1) 7 && x (-1) 11).toNat = 0)
    (g30 : (x 3 4 && x 3 8).toNat = 0)
    (g31 : (x 2 5 && x 2 9).toNat = 0)
    (g32 : (x 1 6 && x 1 10).toNat = 0)
    (g33 : (x (-3) 4 && x (-3) 9).toNat = 0)
    (g34 : (x (-4) 5 && x (-4) 10).toNat = 0)
    (g35 : (x (-5) 6 && x (-5) 11).toNat = 0)
    (g36 : (x (-6) 7 && x (-6) 12).toNat = 0)
    (g37 : (x 0 8 && x 0 13).toNat = 0)
    (g38 : (x (-1) 9 && x (-1) 14).toNat = 0)
    (g39 : (x (-3) 4 && x (-3) 10).toNat = 0)
    (g40 : (x (-4) 5 && x (-4) 11).toNat = 0)
    (g41 : (x (-5) 6 && x (-5) 12).toNat = 0)
    (g42 : (x (-6) 7 && x (-6) 13).toNat = 0)
    (g43 : (x 2 6 && x 2 12).toNat = 0)
    (g44 : (x 1 7 && x 1 13).toNat = 0)
    (g45 : (x 0 8 && x 0 14).toNat = 0)
    (g46 : (x 0 1 && x 0 8).toNat = 0)
    (g47 : (x (-1) 2 && x (-1) 9).toNat = 0)
    (g48 : (x (-3) 4 && x (-3) 11).toNat = 0)
    (g49 : (x (-4) 5 && x (-4) 12).toNat = 0)
    (g50 : (x (-5) 6 && x (-5) 13).toNat = 0)
    (g51 : (x (-6) 7 && x (-6) 14).toNat = 0)
    (g52 : (x (-1) 2 && x (-1) 11).toNat = 0)
    (g53 : (x (-3) 4 && x (-3) 13).toNat = 0)
    (g54 : (x (-4) 5 && x (-4) 14).toNat = 0)
    (g55 : (x 2 3 && x 2 12).toNat = 0)
    (g56 : (x 1 4 && x 1 13).toNat = 0)
    (g57 : (x 0 5 && x 0 14).toNat = 0)
    (g58 : (x 3 3 && x 3 12).toNat = 0)
    (g59 : (x 2 4 && x 2 13).toNat = 0)
    (g60 : (x 1 5 && x 1 14).toNat = 0)
    (g61 : (x 3 4 && x 3 13).toNat = 0)
    (g62 : (x 2 5 && x 2 14).toNat = 0)
    (g63 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g64 : (x (-3) 4 && x (-3) 14).toNat = 0)
    (g65 : (x 3 2 && x 3 12).toNat = 0)
    (g66 : (x 2 3 && x 2 13).toNat = 0)
    (g67 : (x 1 4 && x 1 14).toNat = 0)
    (g68 : (x 2 4 && x 2 14).toNat = 0)
    (g69 : (x (-1) 1 && x (-1) 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d11796 : (x 0 12).toNat = 1 := by
    have r11797 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
    have b11798 := hb (x 0 4)
    have b11799 := hb (x 0 12)
    clear * - r11797 b11798 b11799 g8
    omega
  have d11800 : (x (-2) 2).toNat = 0 := by
    have r11801 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11802 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e11803 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b11804 := hb (x (-3) 3)
    have b11805 := hb (x (-2) 2)
    have b11806 := hb (x (-1) 13)
    have b11807 := hb (x 0 12)
    clear * - r11801 e11802 e11803 b11804 b11805 b11806 b11807 d11796 g7
    omega
  have d11808 : (x (-2) 2 && x (-2) 12).toNat = 0 := by
    have r11809 := hand1 (x (-2) 2) (x (-2) 12)
    have b11810 := hb (x (-2) 2)
    have b11811 := hb (x (-2) 2 && x (-2) 12)
    clear * - r11809 b11810 b11811 d11800
    omega
  have d11812 : (x (-2) 10).toNat = 0 := by
    have r11813 : (x (-2) 10).toNat ≤ (x (-2) 2).toNat := himp _ _ (hp10 (-2))
    have b11814 := hb (x (-2) 2)
    have b11815 := hb (x (-2) 10)
    clear * - r11813 b11814 b11815 d11800
    omega
  have d11816 : (x (-2) 1 && x (-2) 10).toNat = 0 := by
    have r11817 := hand2 (x (-2) 1) (x (-2) 10)
    have b11818 := hb (x (-2) 10)
    have b11819 := hb (x (-2) 1 && x (-2) 10)
    clear * - r11817 b11818 b11819 d11812
    omega
  have d11820 : (x (-2) 3 && x (-2) 10).toNat = 0 := by
    have r11821 := hand2 (x (-2) 3) (x (-2) 10)
    have b11822 := hb (x (-2) 10)
    have b11823 := hb (x (-2) 3 && x (-2) 10)
    clear * - r11821 b11822 b11823 d11812
    omega
  have d11824 : (x (-2) 6 && x (-2) 10).toNat = 0 := by
    have r11825 := hand2 (x (-2) 6) (x (-2) 10)
    have b11826 := hb (x (-2) 10)
    have b11827 := hb (x (-2) 6 && x (-2) 10)
    clear * - r11825 b11826 b11827 d11812
    omega
  have d11828 : (x 0 13).toNat = 1 := by
    have r11829 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11830 := hb (x (-2) 2)
    have b11831 := hb (x 0 13)
    have b11832 := hb (x (-1) 1 && x (-1) 14)
    clear * - r11829 b11830 b11831 b11832 g69 d11800
    omega
  have d11833 : (x 1 12).toNat = 0 := by
    have r11834 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11835 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e11836 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b11837 := hb (x (-2) 3)
    have b11838 := hb (x (-1) 2)
    have b11839 := hb (x 0 13)
    have b11840 := hb (x 1 12)
    clear * - r11834 e11835 e11836 b11837 b11838 b11839 b11840 d11828
    omega
  have d11841 : (x 1 7 && x 1 12).toNat = 0 := by
    have r11842 := hand2 (x 1 7) (x 1 12)
    have b11843 := hb (x 1 12)
    have b11844 := hb (x 1 7 && x 1 12)
    clear * - r11842 b11843 b11844 d11833
    omega
  have d11845 : (x 1 4).toNat = 0 := by
    have r11846 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
    have b11847 := hb (x 1 4)
    have b11848 := hb (x 1 12)
    clear * - r11846 b11847 b11848 d11833
    omega
  have d11849 : (x (-1) 2).toNat = 0 := by
    have r11850 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11851 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e11852 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b11853 := hb (x (-2) 3)
    have b11854 := hb (x (-1) 2)
    have b11855 := hb (x 0 13)
    have b11856 := hb (x 1 12)
    clear * - r11850 e11851 e11852 b11853 b11854 b11855 b11856 d11833 d11828
    omega
  have d11857 : (x (-1) 2 && x (-1) 12).toNat = 0 := by
    have r11858 := hand1 (x (-1) 2) (x (-1) 12)
    have b11859 := hb (x (-1) 2)
    have b11860 := hb (x (-1) 2 && x (-1) 12)
    clear * - r11858 b11859 b11860 d11849
    omega
  have d11861 : (x (-1) 2 && x (-1) 8).toNat = 0 := by
    have r11862 := hand1 (x (-1) 2) (x (-1) 8)
    have b11863 := hb (x (-1) 2)
    have b11864 := hb (x (-1) 2 && x (-1) 8)
    clear * - r11862 b11863 b11864 d11849
    omega
  have d11865 : (x (-1) 2 && x (-1) 7).toNat = 0 := by
    have r11866 := hand1 (x (-1) 2) (x (-1) 7)
    have b11867 := hb (x (-1) 2)
    have b11868 := hb (x (-1) 2 && x (-1) 7)
    clear * - r11866 b11867 b11868 d11849
    omega
  have d11869 : (x (-2) 3).toNat = 0 := by
    have r11870 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11871 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e11872 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b11873 := hb (x (-2) 3)
    have b11874 := hb (x (-1) 2)
    have b11875 := hb (x 0 13)
    have b11876 := hb (x 1 12)
    clear * - r11870 e11871 e11872 b11873 b11874 b11875 b11876 d11833 d11828 d11849
    omega
  have d11877 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
    have r11878 := hand1 (x (-2) 3) (x (-2) 13)
    have b11879 := hb (x (-2) 3)
    have b11880 := hb (x (-2) 3 && x (-2) 13)
    clear * - r11878 b11879 b11880 d11869
    omega
  have d11881 : (x (-2) 3 && x (-2) 12).toNat = 0 := by
    have r11882 := hand1 (x (-2) 3) (x (-2) 12)
    have b11883 := hb (x (-2) 3)
    have b11884 := hb (x (-2) 3 && x (-2) 12)
    clear * - r11882 b11883 b11884 d11869
    omega
  have d11885 : (x (-2) 3 && x (-2) 9).toNat = 0 := by
    have r11886 := hand1 (x (-2) 3) (x (-2) 9)
    have b11887 := hb (x (-2) 3)
    have b11888 := hb (x (-2) 3 && x (-2) 9)
    clear * - r11886 b11887 b11888 d11869
    omega
  have d11889 : (x (-2) 3 && x (-2) 8).toNat = 0 := by
    have r11890 := hand1 (x (-2) 3) (x (-2) 8)
    have b11891 := hb (x (-2) 3)
    have b11892 := hb (x (-2) 3 && x (-2) 8)
    clear * - r11890 b11891 b11892 d11869
    omega
  have d11893 : (x (-3) 3).toNat = 0 := by
    have r11894 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11895 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e11896 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b11897 := hb (x (-3) 3)
    have b11898 := hb (x (-2) 2)
    have b11899 := hb (x (-1) 13)
    have b11900 := hb (x 0 12)
    clear * - r11894 e11895 e11896 b11897 b11898 b11899 b11900 d11796 g7 d11800
    omega
  have d11901 : (x (-3) 3 && x (-3) 13).toNat = 0 := by
    have r11902 := hand1 (x (-3) 3) (x (-3) 13)
    have b11903 := hb (x (-3) 3)
    have b11904 := hb (x (-3) 3 && x (-3) 13)
    clear * - r11902 b11903 b11904 d11893
    omega
  have d11905 : (x (-3) 11).toNat = 0 := by
    have r11906 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
    have b11907 := hb (x (-3) 3)
    have b11908 := hb (x (-3) 11)
    clear * - r11906 b11907 b11908 d11893
    omega
  have d11909 : (x (-3) 1 && x (-3) 11).toNat = 0 := by
    have r11910 := hand2 (x (-3) 1) (x (-3) 11)
    have b11911 := hb (x (-3) 11)
    have b11912 := hb (x (-3) 1 && x (-3) 11)
    clear * - r11910 b11911 b11912 d11905
    omega
  have d11913 : (x (-3) 2 && x (-3) 11).toNat = 0 := by
    have r11914 := hand2 (x (-3) 2) (x (-3) 11)
    have b11915 := hb (x (-3) 11)
    have b11916 := hb (x (-3) 2 && x (-3) 11)
    clear * - r11914 b11915 b11916 d11905
    omega
  have d11917 : (x (-3) 7 && x (-3) 11).toNat = 0 := by
    have r11918 := hand2 (x (-3) 7) (x (-3) 11)
    have b11919 := hb (x (-3) 11)
    have b11920 := hb (x (-3) 7 && x (-3) 11)
    clear * - r11918 b11919 b11920 d11905
    omega
  have d11921 : (x 0 1 && x 0 11).toNat = 1 := by
    have r11922 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11923 := hb (x (-4) 5)
    have b11924 := hb (x 1 10)
    have b11925 := hb (x 0 1 && x 0 11)
    have b11926 := hb (x (-1) 2 && x (-1) 12)
    have b11927 := hb (x (-2) 3 && x (-2) 13)
    have b11928 := hb (x (-3) 4 && x (-3) 14)
    clear * - r11922 b11923 b11924 b11925 b11926 b11927 b11928 g16 d11857 d11877 g64 g1
    omega
  have d11929 : (x 0 11).toNat = 1 := by
    have r11930 := hand2 (x 0 1) (x 0 11)
    have b11931 := hb (x 0 11)
    have b11932 := hb (x 0 1 && x 0 11)
    clear * - r11930 b11931 b11932 d11921
    omega
  have d11933 : (x 4 8).toNat = 0 := by
    have r11934 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11935 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e11936 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e11937 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e11938 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e11939 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e11940 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b11941 := hb (x (-3) 7)
    have b11942 := hb (x (-2) 6)
    have b11943 := hb (x (-1) 5)
    have b11944 := hb (x 0 4)
    have b11945 := hb (x 1 11)
    have b11946 := hb (x 2 10)
    have b11947 := hb (x 3 9)
    have b11948 := hb (x 4 8)
    clear * - r11934 e11935 e11936 e11937 e11938 e11939 e11940 b11941 b11942 b11943 b11944 b11945 b11946 b11947 b11948 g8 g3
    omega
  have d11949 : (x 3 9).toNat = 0 := by
    have r11950 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11951 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e11952 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e11953 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e11954 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e11955 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e11956 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b11957 := hb (x (-3) 7)
    have b11958 := hb (x (-2) 6)
    have b11959 := hb (x (-1) 5)
    have b11960 := hb (x 0 4)
    have b11961 := hb (x 1 11)
    have b11962 := hb (x 2 10)
    have b11963 := hb (x 3 9)
    have b11964 := hb (x 4 8)
    clear * - r11950 e11951 e11952 e11953 e11954 e11955 e11956 b11957 b11958 b11959 b11960 b11961 b11962 b11963 b11964 d11933 g8 g3
    omega
  have d11965 : (x 2 10).toNat = 0 := by
    have r11966 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11967 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e11968 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e11969 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e11970 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e11971 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e11972 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b11973 := hb (x (-3) 7)
    have b11974 := hb (x (-2) 6)
    have b11975 := hb (x (-1) 5)
    have b11976 := hb (x 0 4)
    have b11977 := hb (x 1 11)
    have b11978 := hb (x 2 10)
    have b11979 := hb (x 3 9)
    have b11980 := hb (x 4 8)
    clear * - r11966 e11967 e11968 e11969 e11970 e11971 e11972 b11973 b11974 b11975 b11976 b11977 b11978 b11979 b11980 d11933 d11949 g8 g3
    omega
  have d11981 : (x 1 11).toNat = 0 := by
    have r11982 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11983 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e11984 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e11985 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e11986 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e11987 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e11988 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b11989 := hb (x (-3) 7)
    have b11990 := hb (x (-2) 6)
    have b11991 := hb (x (-1) 5)
    have b11992 := hb (x 0 4)
    have b11993 := hb (x 1 11)
    have b11994 := hb (x 2 10)
    have b11995 := hb (x 3 9)
    have b11996 := hb (x 4 8)
    clear * - r11982 e11983 e11984 e11985 e11986 e11987 e11988 b11989 b11990 b11991 b11992 b11993 b11994 b11995 b11996 d11933 d11949 d11965 g8 g3
    omega
  have d11997 : (x (-2) 6).toNat = 0 := by
    have r11998 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11999 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e12000 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e12001 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e12002 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e12003 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e12004 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b12005 := hb (x (-3) 7)
    have b12006 := hb (x (-2) 6)
    have b12007 := hb (x (-1) 5)
    have b12008 := hb (x 0 4)
    have b12009 := hb (x 1 11)
    have b12010 := hb (x 2 10)
    have b12011 := hb (x 3 9)
    have b12012 := hb (x 4 8)
    clear * - r11998 e11999 e12000 e12001 e12002 e12003 e12004 b12005 b12006 b12007 b12008 b12009 b12010 b12011 b12012 d11933 d11949 d11965 d11981 g8 g3
    omega
  have d12013 : (x (-3) 7).toNat = 0 := by
    have r12014 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12015 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e12016 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e12017 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e12018 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e12019 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e12020 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b12021 := hb (x (-3) 7)
    have b12022 := hb (x (-2) 6)
    have b12023 := hb (x (-1) 5)
    have b12024 := hb (x 0 4)
    have b12025 := hb (x 1 11)
    have b12026 := hb (x 2 10)
    have b12027 := hb (x 3 9)
    have b12028 := hb (x 4 8)
    clear * - r12014 e12015 e12016 e12017 e12018 e12019 e12020 b12021 b12022 b12023 b12024 b12025 b12026 b12027 b12028 d11933 d11949 d11965 d11981 g8 g3 d11997
    omega
  have d12029 : (x 3 8).toNat = 0 := by
    have r12030 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12031 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
    have e12032 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
    have e12033 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
    have e12034 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
    have e12035 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
    have e12036 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
    have b12037 := hb (x (-4) 7)
    have b12038 := hb (x (-3) 6)
    have b12039 := hb (x (-2) 5)
    have b12040 := hb (x (-1) 4)
    have b12041 := hb (x 0 11)
    have b12042 := hb (x 1 10)
    have b12043 := hb (x 2 9)
    have b12044 := hb (x 3 8)
    clear * - r12030 e12031 e12032 e12033 e12034 e12035 e12036 b12037 b12038 b12039 b12040 b12041 b12042 b12043 b12044 g16 d11929
    omega
  have d12045 : (x 3 8 && x 3 13).toNat = 0 := by
    have r12046 := hand1 (x 3 8) (x 3 13)
    have b12047 := hb (x 3 8)
    have b12048 := hb (x 3 8 && x 3 13)
    clear * - r12046 b12047 b12048 d12029
    omega
  have d12049 : (x 2 9).toNat = 0 := by
    have r12050 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12051 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
    have e12052 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
    have e12053 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
    have e12054 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
    have e12055 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
    have e12056 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
    have b12057 := hb (x (-4) 7)
    have b12058 := hb (x (-3) 6)
    have b12059 := hb (x (-2) 5)
    have b12060 := hb (x (-1) 4)
    have b12061 := hb (x 0 11)
    have b12062 := hb (x 1 10)
    have b12063 := hb (x 2 9)
    have b12064 := hb (x 3 8)
    clear * - r12050 e12051 e12052 e12053 e12054 e12055 e12056 b12057 b12058 b12059 b12060 b12061 b12062 b12063 b12064 d12029 g16 d11929
    omega
  have d12065 : (x 2 9 && x 2 14).toNat = 0 := by
    have r12066 := hand1 (x 2 9) (x 2 14)
    have b12067 := hb (x 2 9)
    have b12068 := hb (x 2 9 && x 2 14)
    clear * - r12066 b12067 b12068 d12049
    omega
  cases h12069 : x 0 6
  · have f12070 : (x 0 6).toNat = 0 := by rw [h12069]; rfl
    have d12071 : (x 0 1 && x 0 6).toNat = 0 := by
      have r12072 := hand2 (x 0 1) (x 0 6)
      have b12073 := hb (x 0 6)
      have b12074 := hb (x 0 1 && x 0 6)
      clear * - r12072 b12073 b12074 f12070
      omega
    have d12075 : (x 0 6 && x 0 10).toNat = 0 := by
      have r12076 := hand1 (x 0 6) (x 0 10)
      have b12077 := hb (x 0 6)
      have b12078 := hb (x 0 6 && x 0 10)
      clear * - r12076 b12077 b12078 f12070
      omega
    have d12079 : (x 0 2 && x 0 6).toNat = 0 := by
      have r12080 := hand2 (x 0 2) (x 0 6)
      have b12081 := hb (x 0 6)
      have b12082 := hb (x 0 2 && x 0 6)
      clear * - r12080 b12081 b12082 f12070
      omega
    cases h12083 : x 0 7
    · have f12084 : (x 0 7).toNat = 0 := by rw [h12083]; rfl
      have d12085 : (x 0 1 && x 0 7).toNat = 0 := by
        have r12086 := hand2 (x 0 1) (x 0 7)
        have b12087 := hb (x 0 7)
        have b12088 := hb (x 0 1 && x 0 7)
        clear * - r12086 b12087 b12088 f12084
        omega
      have d12089 : (x 0 7 && x 0 11).toNat = 0 := by
        have r12090 := hand1 (x 0 7) (x 0 11)
        have b12091 := hb (x 0 7)
        have b12092 := hb (x 0 7 && x 0 11)
        clear * - r12090 b12091 b12092 f12084
        omega
      cases h12093 : x 0 10
      · have f12094 : (x 0 10).toNat = 0 := by rw [h12093]; rfl
        have d12095 : (x 0 1 && x 0 10).toNat = 0 := by
          have r12096 := hand2 (x 0 1) (x 0 10)
          have b12097 := hb (x 0 10)
          have b12098 := hb (x 0 1 && x 0 10)
          clear * - r12096 b12097 b12098 f12094
          omega
        have d12099 : (x 1 9).toNat = 1 := by
          have r12100 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12101 := hb (x (-5) 6)
          have b12102 := hb (x 1 9)
          have b12103 := hb (x 0 1 && x 0 10)
          have b12104 := hb (x (-1) 2 && x (-1) 11)
          have b12105 := hb (x (-2) 3 && x (-2) 12)
          have b12106 := hb (x (-3) 4 && x (-3) 13)
          have b12107 := hb (x (-4) 5 && x (-4) 14)
          clear * - r12100 b12101 b12102 b12103 b12104 b12105 b12106 b12107 d12095 g52 d11881 g53 g54 g0
          omega
        have d12108 : (x 1 1).toNat = 1 := by
          have r12109 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
          have b12110 := hb (x 1 1)
          have b12111 := hb (x 1 9)
          clear * - r12109 b12110 b12111 d12099
          omega
        have d12112 : (x 2 14).toNat = 0 := by
          have r12113 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12114 := hb (x 1 1)
          have b12115 := hb (x 2 14)
          clear * - r12113 b12114 b12115 d12108
          omega
        have d12116 : (x 2 1 && x 2 14).toNat = 0 := by
          have r12117 := hand2 (x 2 1) (x 2 14)
          have b12118 := hb (x 2 14)
          have b12119 := hb (x 2 1 && x 2 14)
          clear * - r12117 b12118 b12119 d12112
          omega
        have d12120 : (x 3 13).toNat = 1 := by
          have r12121 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12122 := hb (x 1 2)
          have b12123 := hb (x 3 13)
          have b12124 := hb (x 2 1 && x 2 14)
          clear * - r12121 b12122 b12123 b12124 d12116 g12
          omega
        have d12125 : (x 4 12).toNat = 0 := by
          have r12126 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12127 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e12128 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b12129 := hb (x 1 3)
          have b12130 := hb (x 2 2)
          have b12131 := hb (x 3 13)
          have b12132 := hb (x 4 12)
          clear * - r12126 e12127 e12128 b12129 b12130 b12131 b12132 d12120
          omega
        have d12133 : (x 4 3 && x 4 12).toNat = 0 := by
          have r12134 := hand2 (x 4 3) (x 4 12)
          have b12135 := hb (x 4 12)
          have b12136 := hb (x 4 3 && x 4 12)
          clear * - r12134 b12135 b12136 d12125
          omega
        have d12137 : (x 4 4).toNat = 0 := by
          have r12138 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
          have b12139 := hb (x 4 4)
          have b12140 := hb (x 4 12)
          clear * - r12138 b12139 b12140 d12125
          omega
        have d12141 : (x 2 6).toNat = 0 := by
          have r12142 : (x 2 6).toNat ≤ (x 2 14).toNat := himp _ _ (hp6 2)
          have b12143 := hb (x 2 6)
          have b12144 := hb (x 2 14)
          clear * - r12142 b12143 b12144 d12112
          omega
        have d12145 : (x 2 8).toNat = 0 := by
          have r12146 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12147 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
          have e12148 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
          have e12149 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
          have e12150 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
          have e12151 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
          have e12152 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
          have b12153 := hb (x (-5) 7)
          have b12154 := hb (x (-4) 6)
          have b12155 := hb (x (-3) 5)
          have b12156 := hb (x (-2) 4)
          have b12157 := hb (x (-1) 11)
          have b12158 := hb (x 0 10)
          have b12159 := hb (x 1 9)
          have b12160 := hb (x 2 8)
          clear * - r12146 e12147 e12148 e12149 e12150 e12151 e12152 b12153 b12154 b12155 b12156 b12157 b12158 b12159 b12160 d12099 f12094 g6
          omega
        have d12161 : (x (-2) 4).toNat = 0 := by
          have r12162 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12163 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
          have e12164 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
          have e12165 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
          have e12166 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
          have e12167 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
          have e12168 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
          have b12169 := hb (x (-5) 7)
          have b12170 := hb (x (-4) 6)
          have b12171 := hb (x (-3) 5)
          have b12172 := hb (x (-2) 4)
          have b12173 := hb (x (-1) 11)
          have b12174 := hb (x 0 10)
          have b12175 := hb (x 1 9)
          have b12176 := hb (x 2 8)
          clear * - r12162 e12163 e12164 e12165 e12166 e12167 e12168 b12169 b12170 b12171 b12172 b12173 b12174 b12175 b12176 d12145 d12099 f12094 g6
          omega
        have d12177 : (x (-2) 4 && x (-2) 8).toNat = 0 := by
          have r12178 := hand1 (x (-2) 4) (x (-2) 8)
          have b12179 := hb (x (-2) 4)
          have b12180 := hb (x (-2) 4 && x (-2) 8)
          clear * - r12178 b12179 b12180 d12161
          omega
        have d12181 : (x (-3) 5).toNat = 0 := by
          have r12182 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12183 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
          have e12184 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
          have e12185 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
          have e12186 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
          have e12187 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
          have e12188 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
          have b12189 := hb (x (-5) 7)
          have b12190 := hb (x (-4) 6)
          have b12191 := hb (x (-3) 5)
          have b12192 := hb (x (-2) 4)
          have b12193 := hb (x (-1) 11)
          have b12194 := hb (x 0 10)
          have b12195 := hb (x 1 9)
          have b12196 := hb (x 2 8)
          clear * - r12182 e12183 e12184 e12185 e12186 e12187 e12188 b12189 b12190 b12191 b12192 b12193 b12194 b12195 b12196 d12145 d12099 f12094 g6 d12161
          omega
        have d12197 : (x (-3) 5 && x (-3) 9).toNat = 0 := by
          have r12198 := hand1 (x (-3) 5) (x (-3) 9)
          have b12199 := hb (x (-3) 5)
          have b12200 := hb (x (-3) 5 && x (-3) 9)
          clear * - r12198 b12199 b12200 d12181
          omega
        have d12201 : (x (-4) 6).toNat = 0 := by
          have r12202 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12203 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
          have e12204 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
          have e12205 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
          have e12206 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
          have e12207 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
          have e12208 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
          have b12209 := hb (x (-5) 7)
          have b12210 := hb (x (-4) 6)
          have b12211 := hb (x (-3) 5)
          have b12212 := hb (x (-2) 4)
          have b12213 := hb (x (-1) 11)
          have b12214 := hb (x 0 10)
          have b12215 := hb (x 1 9)
          have b12216 := hb (x 2 8)
          clear * - r12202 e12203 e12204 e12205 e12206 e12207 e12208 b12209 b12210 b12211 b12212 b12213 b12214 b12215 b12216 d12145 d12099 f12094 g6 d12161 d12181
          omega
        have d12217 : (x (-4) 6 && x (-4) 10).toNat = 0 := by
          have r12218 := hand1 (x (-4) 6) (x (-4) 10)
          have b12219 := hb (x (-4) 6)
          have b12220 := hb (x (-4) 6 && x (-4) 10)
          clear * - r12218 b12219 b12220 d12201
          omega
        have d12221 : (x (-5) 7).toNat = 0 := by
          have r12222 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12223 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
          have e12224 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
          have e12225 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
          have e12226 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
          have e12227 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
          have e12228 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
          have b12229 := hb (x (-5) 7)
          have b12230 := hb (x (-4) 6)
          have b12231 := hb (x (-3) 5)
          have b12232 := hb (x (-2) 4)
          have b12233 := hb (x (-1) 11)
          have b12234 := hb (x 0 10)
          have b12235 := hb (x 1 9)
          have b12236 := hb (x 2 8)
          clear * - r12222 e12223 e12224 e12225 e12226 e12227 e12228 b12229 b12230 b12231 b12232 b12233 b12234 b12235 b12236 d12145 d12099 f12094 g6 d12161 d12181 d12201
          omega
        have d12237 : (x (-5) 7 && x (-5) 11).toNat = 0 := by
          have r12238 := hand1 (x (-5) 7) (x (-5) 11)
          have b12239 := hb (x (-5) 7)
          have b12240 := hb (x (-5) 7 && x (-5) 11)
          clear * - r12238 b12239 b12240 d12221
          omega
        have r12241 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12242 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
        have e12243 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
        have e12244 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
        have e12245 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
        have e12246 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
        have e12247 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
        have r12248 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12249 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
        have e12250 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
        have e12251 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
        have e12252 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
        have e12253 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
        have e12254 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
        have r12255 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12256 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e12257 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e12258 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e12259 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e12260 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e12261 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have r12262 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12263 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
        have e12264 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
        have r12265 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12266 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e12267 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have r12268 : 1 ≤ (x 2 4).toNat + (x 1 1 && x 1 5).toNat + (x 0 2 && x 0 6).toNat + (x (-1) 3 && x (-1) 7).toNat + (x (-2) 4 && x (-2) 8).toNat + (x (-3) 5 && x (-3) 9).toNat + (x (-4) 6 && x (-4) 10).toNat + (x (-5) 7 && x (-5) 11).toNat + (x (-6) 8 && x (-6) 12).toNat + (x (-7) 9 && x (-7) 13).toNat + (x (-8) 10 && x (-8) 14).toNat + (x (-9) 11).toNat := by have q := hcov4 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12269 : (x 1 1 && x 1 5).toNat = (x 1 5).toNat := handr _ _ (fun h => hp13 1 (hp5 1 (h)))
        have e12270 : (x (-8) 10 && x (-8) 14).toNat = (x (-8) 10).toNat := handl _ _ (fun h => hp2 (-8) (hp10 (-8) (h)))
        have r12271 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := by have q := hcov5 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r12272 : 1 ≤ (x 1 7).toNat + (x 0 1 && x 0 8).toNat + (x (-1) 2 && x (-1) 9).toNat + (x (-2) 3 && x (-2) 10).toNat + (x (-3) 4 && x (-3) 11).toNat + (x (-4) 5 && x (-4) 12).toNat + (x (-5) 6 && x (-5) 13).toNat + (x (-6) 7 && x (-6) 14).toNat + (x (-7) 8).toNat := by have q := hcov7 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r12273 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r12274 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r12275 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r12276 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
        have r12277 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
        have r12278 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
        have r12279 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
        have r12280 := hand2 (x (-6) 8) (x (-6) 12)
        have r12281 := hand1 (x (-7) 9) (x (-7) 13)
        have r12282 := hand2 (x (-7) 8) (x (-7) 13)
        have r12283 := hand1 (x (-8) 9) (x (-8) 14)
        have r12284 := hand2 (x 6 1) (x 6 10)
        have r12285 := hand2 (x 5 2) (x 5 11)
        have r12286 := hand2 (x (-7) 1) (x (-7) 11)
        have r12287 := hand1 (x (-8) 2) (x (-8) 12)
        have r12288 := hand1 (x (-9) 3) (x (-9) 13)
        have r12289 := hand1 (x (-10) 4) (x (-10) 14)
        have r12290 := hand1 (x (-4) 4) (x (-4) 14)
        linarith only [r12241, e12242, e12243, e12244, e12245, e12246, e12247, r12248, e12249, e12250, e12251, e12252, e12253, e12254, r12255, e12256, e12257, e12258, e12259, e12260, e12261, r12262, e12263, e12264, r12265, e12266, e12267, r12268, e12269, e12270, r12271, r12272, r12273, r12274, r12275, r12276, r12277, r12278, r12279, r12280, r12281, r12282, r12283, r12284, r12285, r12286, r12287, r12288, r12289, r12290, f12094, g13, g14, g17, d12141, d12137, d12079, g20, d12177, d12197, d12217, d12237, d12071, d11865, d11889, g33, g34, g35, g36, g46, g47, d11820, g48, g49, g50, g51, d12133, g61, g62, g63, d11808, d11901]
      · have f12368 : (x 0 10).toNat = 1 := by rw [h12093]; rfl
        have d12369 : (x 2 8).toNat = 0 := by
          have r12370 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12371 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
          have e12372 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
          have e12373 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
          have e12374 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
          have e12375 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
          have e12376 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
          have b12377 := hb (x (-5) 7)
          have b12378 := hb (x (-4) 6)
          have b12379 := hb (x (-3) 5)
          have b12380 := hb (x (-2) 4)
          have b12381 := hb (x (-1) 11)
          have b12382 := hb (x 0 10)
          have b12383 := hb (x 1 9)
          have b12384 := hb (x 2 8)
          clear * - r12370 e12371 e12372 e12373 e12374 e12375 e12376 b12377 b12378 b12379 b12380 b12381 b12382 b12383 b12384 f12368 g6
          omega
        have d12385 : (x 1 9).toNat = 0 := by
          have r12386 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12387 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
          have e12388 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
          have e12389 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
          have e12390 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
          have e12391 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
          have e12392 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
          have b12393 := hb (x (-5) 7)
          have b12394 := hb (x (-4) 6)
          have b12395 := hb (x (-3) 5)
          have b12396 := hb (x (-2) 4)
          have b12397 := hb (x (-1) 11)
          have b12398 := hb (x 0 10)
          have b12399 := hb (x 1 9)
          have b12400 := hb (x 2 8)
          clear * - r12386 e12387 e12388 e12389 e12390 e12391 e12392 b12393 b12394 b12395 b12396 b12397 b12398 b12399 b12400 d12369 f12368 g6
          omega
        have d12401 : (x (-2) 4).toNat = 0 := by
          have r12402 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12403 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
          have e12404 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
          have e12405 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
          have e12406 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
          have e12407 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
          have e12408 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
          have b12409 := hb (x (-5) 7)
          have b12410 := hb (x (-4) 6)
          have b12411 := hb (x (-3) 5)
          have b12412 := hb (x (-2) 4)
          have b12413 := hb (x (-1) 11)
          have b12414 := hb (x 0 10)
          have b12415 := hb (x 1 9)
          have b12416 := hb (x 2 8)
          clear * - r12402 e12403 e12404 e12405 e12406 e12407 e12408 b12409 b12410 b12411 b12412 b12413 b12414 b12415 b12416 d12369 d12385 f12368 g6
          omega
        have d12417 : (x (-2) 4 && x (-2) 8).toNat = 0 := by
          have r12418 := hand1 (x (-2) 4) (x (-2) 8)
          have b12419 := hb (x (-2) 4)
          have b12420 := hb (x (-2) 4 && x (-2) 8)
          clear * - r12418 b12419 b12420 d12401
          omega
        have d12421 : (x (-3) 5).toNat = 0 := by
          have r12422 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12423 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
          have e12424 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
          have e12425 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
          have e12426 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
          have e12427 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
          have e12428 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
          have b12429 := hb (x (-5) 7)
          have b12430 := hb (x (-4) 6)
          have b12431 := hb (x (-3) 5)
          have b12432 := hb (x (-2) 4)
          have b12433 := hb (x (-1) 11)
          have b12434 := hb (x 0 10)
          have b12435 := hb (x 1 9)
          have b12436 := hb (x 2 8)
          clear * - r12422 e12423 e12424 e12425 e12426 e12427 e12428 b12429 b12430 b12431 b12432 b12433 b12434 b12435 b12436 d12369 d12385 f12368 g6 d12401
          omega
        have d12437 : (x (-3) 5 && x (-3) 9).toNat = 0 := by
          have r12438 := hand1 (x (-3) 5) (x (-3) 9)
          have b12439 := hb (x (-3) 5)
          have b12440 := hb (x (-3) 5 && x (-3) 9)
          clear * - r12438 b12439 b12440 d12421
          omega
        have d12441 : (x (-4) 6).toNat = 0 := by
          have r12442 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12443 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
          have e12444 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
          have e12445 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
          have e12446 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
          have e12447 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
          have e12448 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
          have b12449 := hb (x (-5) 7)
          have b12450 := hb (x (-4) 6)
          have b12451 := hb (x (-3) 5)
          have b12452 := hb (x (-2) 4)
          have b12453 := hb (x (-1) 11)
          have b12454 := hb (x 0 10)
          have b12455 := hb (x 1 9)
          have b12456 := hb (x 2 8)
          clear * - r12442 e12443 e12444 e12445 e12446 e12447 e12448 b12449 b12450 b12451 b12452 b12453 b12454 b12455 b12456 d12369 d12385 f12368 g6 d12401 d12421
          omega
        have d12457 : (x (-4) 6 && x (-4) 10).toNat = 0 := by
          have r12458 := hand1 (x (-4) 6) (x (-4) 10)
          have b12459 := hb (x (-4) 6)
          have b12460 := hb (x (-4) 6 && x (-4) 10)
          clear * - r12458 b12459 b12460 d12441
          omega
        have d12461 : (x (-5) 7).toNat = 0 := by
          have r12462 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12463 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
          have e12464 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
          have e12465 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
          have e12466 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
          have e12467 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
          have e12468 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
          have b12469 := hb (x (-5) 7)
          have b12470 := hb (x (-4) 6)
          have b12471 := hb (x (-3) 5)
          have b12472 := hb (x (-2) 4)
          have b12473 := hb (x (-1) 11)
          have b12474 := hb (x 0 10)
          have b12475 := hb (x 1 9)
          have b12476 := hb (x 2 8)
          clear * - r12462 e12463 e12464 e12465 e12466 e12467 e12468 b12469 b12470 b12471 b12472 b12473 b12474 b12475 b12476 d12369 d12385 f12368 g6 d12401 d12421 d12441
          omega
        have d12477 : (x (-5) 7 && x (-5) 11).toNat = 0 := by
          have r12478 := hand1 (x (-5) 7) (x (-5) 11)
          have b12479 := hb (x (-5) 7)
          have b12480 := hb (x (-5) 7 && x (-5) 11)
          clear * - r12478 b12479 b12480 d12461
          omega
        cases h12481 : x 1 1
        · have f12482 : (x 1 1).toNat = 0 := by rw [h12481]; rfl
          cases h12483 : x 1 3
          · have f12484 : (x 1 3).toNat = 0 := by rw [h12483]; rfl
            cases h12485 : x (-1) 6
            · have f12486 : (x (-1) 6).toNat = 0 := by rw [h12485]; rfl
              cases h12487 : x 1 7
              · have f12488 : (x 1 7).toNat = 0 := by rw [h12487]; rfl
                have d12489 : (x (-7) 8).toNat = 1 := by
                  have r12490 : 1 ≤ (x 1 7).toNat + (x 0 1 && x 0 8).toNat + (x (-1) 2 && x (-1) 9).toNat + (x (-2) 3 && x (-2) 10).toNat + (x (-3) 4 && x (-3) 11).toNat + (x (-4) 5 && x (-4) 12).toNat + (x (-5) 6 && x (-5) 13).toNat + (x (-6) 7 && x (-6) 14).toNat + (x (-7) 8).toNat := by have q := hcov7 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b12491 := hb (x (-7) 8)
                  have b12492 := hb (x 1 7)
                  have b12493 := hb (x 0 1 && x 0 8)
                  have b12494 := hb (x (-1) 2 && x (-1) 9)
                  have b12495 := hb (x (-2) 3 && x (-2) 10)
                  have b12496 := hb (x (-3) 4 && x (-3) 11)
                  have b12497 := hb (x (-4) 5 && x (-4) 12)
                  have b12498 := hb (x (-5) 6 && x (-5) 13)
                  have b12499 := hb (x (-6) 7 && x (-6) 14)
                  clear * - r12490 b12491 b12492 b12493 b12494 b12495 b12496 b12497 b12498 b12499 f12488 g46 g47 d11820 g48 g49 g50 g51
                  omega
                have d12500 : (x (-8) 9).toNat = 0 := by
                  have r12501 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e12502 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
                  have e12503 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
                  have e12504 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
                  have e12505 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
                  have e12506 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
                  have e12507 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
                  have b12508 := hb (x (-14) 7)
                  have b12509 := hb (x (-13) 6)
                  have b12510 := hb (x (-12) 5)
                  have b12511 := hb (x (-11) 4)
                  have b12512 := hb (x (-10) 11)
                  have b12513 := hb (x (-9) 10)
                  have b12514 := hb (x (-8) 9)
                  have b12515 := hb (x (-7) 8)
                  clear * - r12501 e12502 e12503 e12504 e12505 e12506 e12507 b12508 b12509 b12510 b12511 b12512 b12513 b12514 b12515 d12489
                  omega
                have d12516 : (x (-8) 9 && x (-8) 14).toNat = 0 := by
                  have r12517 := hand1 (x (-8) 9) (x (-8) 14)
                  have b12518 := hb (x (-8) 9)
                  have b12519 := hb (x (-8) 9 && x (-8) 14)
                  clear * - r12517 b12518 b12519 d12500
                  omega
                have d12520 : (x (-9) 10).toNat = 0 := by
                  have r12521 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e12522 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
                  have e12523 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
                  have e12524 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
                  have e12525 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
                  have e12526 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
                  have e12527 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
                  have b12528 := hb (x (-14) 7)
                  have b12529 := hb (x (-13) 6)
                  have b12530 := hb (x (-12) 5)
                  have b12531 := hb (x (-11) 4)
                  have b12532 := hb (x (-10) 11)
                  have b12533 := hb (x (-9) 10)
                  have b12534 := hb (x (-8) 9)
                  have b12535 := hb (x (-7) 8)
                  clear * - r12521 e12522 e12523 e12524 e12525 e12526 e12527 b12528 b12529 b12530 b12531 b12532 b12533 b12534 b12535 d12489 d12500
                  omega
                have d12536 : (x (-10) 11).toNat = 0 := by
                  have r12537 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e12538 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
                  have e12539 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
                  have e12540 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
                  have e12541 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
                  have e12542 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
                  have e12543 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
                  have b12544 := hb (x (-14) 7)
                  have b12545 := hb (x (-13) 6)
                  have b12546 := hb (x (-12) 5)
                  have b12547 := hb (x (-11) 4)
                  have b12548 := hb (x (-10) 11)
                  have b12549 := hb (x (-9) 10)
                  have b12550 := hb (x (-8) 9)
                  have b12551 := hb (x (-7) 8)
                  clear * - r12537 e12538 e12539 e12540 e12541 e12542 e12543 b12544 b12545 b12546 b12547 b12548 b12549 b12550 b12551 d12489 d12500 d12520
                  omega
                have d12552 : (x (-11) 4).toNat = 0 := by
                  have r12553 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e12554 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
                  have e12555 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
                  have e12556 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
                  have e12557 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
                  have e12558 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
                  have e12559 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
                  have b12560 := hb (x (-14) 7)
                  have b12561 := hb (x (-13) 6)
                  have b12562 := hb (x (-12) 5)
                  have b12563 := hb (x (-11) 4)
                  have b12564 := hb (x (-10) 11)
                  have b12565 := hb (x (-9) 10)
                  have b12566 := hb (x (-8) 9)
                  have b12567 := hb (x (-7) 8)
                  clear * - r12553 e12554 e12555 e12556 e12557 e12558 e12559 b12560 b12561 b12562 b12563 b12564 b12565 b12566 b12567 d12489 d12500 d12520 d12536
                  omega
                have d12568 : (x (-11) 4 && x (-11) 14).toNat = 0 := by
                  have r12569 := hand1 (x (-11) 4) (x (-11) 14)
                  have b12570 := hb (x (-11) 4)
                  have b12571 := hb (x (-11) 4 && x (-11) 14)
                  clear * - r12569 b12570 b12571 d12552
                  omega
                have d12572 : (x (-12) 5).toNat = 0 := by
                  have r12573 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e12574 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
                  have e12575 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
                  have e12576 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
                  have e12577 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
                  have e12578 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
                  have e12579 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
                  have b12580 := hb (x (-14) 7)
                  have b12581 := hb (x (-13) 6)
                  have b12582 := hb (x (-12) 5)
                  have b12583 := hb (x (-11) 4)
                  have b12584 := hb (x (-10) 11)
                  have b12585 := hb (x (-9) 10)
                  have b12586 := hb (x (-8) 9)
                  have b12587 := hb (x (-7) 8)
                  clear * - r12573 e12574 e12575 e12576 e12577 e12578 e12579 b12580 b12581 b12582 b12583 b12584 b12585 b12586 b12587 d12489 d12500 d12520 d12536 d12552
                  omega
                have d12588 : (x (-7) 8 && x (-7) 14).toNat = 1 := by
                  have r12589 : 1 ≤ (x 1 6).toNat + (x 0 1 && x 0 7).toNat + (x (-1) 2 && x (-1) 8).toNat + (x (-2) 3 && x (-2) 9).toNat + (x (-3) 4 && x (-3) 10).toNat + (x (-4) 5 && x (-4) 11).toNat + (x (-5) 6 && x (-5) 12).toNat + (x (-6) 7 && x (-6) 13).toNat + (x (-7) 8 && x (-7) 14).toNat + (x (-8) 9).toNat := by have q := hcov6 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b12590 := hb (x (-8) 9)
                  have b12591 := hb (x 1 6)
                  have b12592 := hb (x 0 1 && x 0 7)
                  have b12593 := hb (x (-1) 2 && x (-1) 8)
                  have b12594 := hb (x (-2) 3 && x (-2) 9)
                  have b12595 := hb (x (-3) 4 && x (-3) 10)
                  have b12596 := hb (x (-4) 5 && x (-4) 11)
                  have b12597 := hb (x (-5) 6 && x (-5) 12)
                  have b12598 := hb (x (-6) 7 && x (-6) 13)
                  have b12599 := hb (x (-7) 8 && x (-7) 14)
                  clear * - r12589 b12590 b12591 b12592 b12593 b12594 b12595 b12596 b12597 b12598 b12599 g14 d12085 d11861 d11885 g39 g40 g41 g42 d12500
                  omega
                have d12600 : (x (-7) 14).toNat = 1 := by
                  have r12601 := hand2 (x (-7) 8) (x (-7) 14)
                  have b12602 := hb (x (-7) 14)
                  have b12603 := hb (x (-7) 8 && x (-7) 14)
                  clear * - r12601 b12602 b12603 d12588
                  omega
                have d12604 : (x (-8) 1).toNat = 0 := by
                  have r12605 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b12606 := hb (x (-8) 1)
                  have b12607 := hb (x (-7) 14)
                  clear * - r12605 b12606 b12607 d12600
                  omega
                have d12608 : (x (-8) 1 && x (-8) 11).toNat = 0 := by
                  have r12609 := hand1 (x (-8) 1) (x (-8) 11)
                  have b12610 := hb (x (-8) 1)
                  have b12611 := hb (x (-8) 1 && x (-8) 11)
                  clear * - r12609 b12610 b12611 d12604
                  omega
                have d12612 : (x (-8) 13).toNat = 0 := by
                  have r12613 : (x (-8) 13).toNat ≤ (x (-8) 1).toNat := himp _ _ (hp13 (-8))
                  have b12614 := hb (x (-8) 1)
                  have b12615 := hb (x (-8) 13)
                  clear * - r12613 b12614 b12615 d12604
                  omega
                have d12616 : (x (-8) 5).toNat = 0 := by
                  have r12617 : (x (-8) 5).toNat ≤ (x (-8) 13).toNat := himp _ _ (hp5 (-8))
                  have b12618 := hb (x (-8) 5)
                  have b12619 := hb (x (-8) 13)
                  clear * - r12617 b12618 b12619 d12612
                  omega
                have d12620 : (x (-7) 8 && x (-7) 13).toNat = 1 := by
                  have r12621 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := by have q := hcov5 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b12622 := hb (x (-9) 10)
                  have b12623 := hb (x 1 5)
                  have b12624 := hb (x 0 1 && x 0 6)
                  have b12625 := hb (x (-1) 2 && x (-1) 7)
                  have b12626 := hb (x (-2) 3 && x (-2) 8)
                  have b12627 := hb (x (-3) 4 && x (-3) 9)
                  have b12628 := hb (x (-4) 5 && x (-4) 10)
                  have b12629 := hb (x (-5) 6 && x (-5) 11)
                  have b12630 := hb (x (-6) 7 && x (-6) 12)
                  have b12631 := hb (x (-7) 8 && x (-7) 13)
                  have b12632 := hb (x (-8) 9 && x (-8) 14)
                  clear * - r12621 b12622 b12623 b12624 b12625 b12626 b12627 b12628 b12629 b12630 b12631 b12632 g13 d12071 d11865 d11889 g33 g34 g35 g36 d12516 d12520
                  omega
                have d12633 : (x (-7) 13).toNat = 1 := by
                  have r12634 := hand2 (x (-7) 8) (x (-7) 13)
                  have b12635 := hb (x (-7) 13)
                  have b12636 := hb (x (-7) 8 && x (-7) 13)
                  clear * - r12634 b12635 b12636 d12620
                  omega
                have d12637 : (x (-7) 1).toNat = 1 := by
                  have r12638 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
                  have b12639 := hb (x (-7) 1)
                  have b12640 := hb (x (-7) 13)
                  clear * - r12638 b12639 b12640 d12633
                  omega
                have d12641 : (x (-6) 14).toNat = 0 := by
                  have r12642 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b12643 := hb (x (-7) 1)
                  have b12644 := hb (x (-6) 14)
                  clear * - r12642 b12643 b12644 d12637
                  omega
                have d12645 : (x (-6) 3 && x (-6) 14).toNat = 0 := by
                  have r12646 := hand2 (x (-6) 3) (x (-6) 14)
                  have b12647 := hb (x (-6) 14)
                  have b12648 := hb (x (-6) 3 && x (-6) 14)
                  clear * - r12646 b12647 b12648 d12641
                  omega
                have d12649 : (x (-6) 4 && x (-6) 14).toNat = 0 := by
                  have r12650 := hand2 (x (-6) 4) (x (-6) 14)
                  have b12651 := hb (x (-6) 14)
                  have b12652 := hb (x (-6) 4 && x (-6) 14)
                  clear * - r12650 b12651 b12652 d12641
                  omega
                have d12653 : (x (-6) 2).toNat = 0 := by
                  have r12654 : (x (-6) 2).toNat ≤ (x (-6) 14).toNat := himp _ _ (hp2 (-6))
                  have b12655 := hb (x (-6) 2)
                  have b12656 := hb (x (-6) 14)
                  clear * - r12654 b12655 b12656 d12641
                  omega
                have d12657 : (x (-6) 10).toNat = 0 := by
                  have r12658 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
                  have b12659 := hb (x (-6) 2)
                  have b12660 := hb (x (-6) 10)
                  clear * - r12658 b12659 b12660 d12653
                  omega
                have d12661 : (x (-6) 12).toNat = 0 := by
                  have r12662 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e12663 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
                  have e12664 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
                  have b12665 := hb (x (-9) 3)
                  have b12666 := hb (x (-8) 2)
                  have b12667 := hb (x (-7) 13)
                  have b12668 := hb (x (-6) 12)
                  clear * - r12662 e12663 e12664 b12665 b12666 b12667 b12668 d12633
                  omega
                have d12669 : (x (-6) 8 && x (-6) 12).toNat = 0 := by
                  have r12670 := hand2 (x (-6) 8) (x (-6) 12)
                  have b12671 := hb (x (-6) 12)
                  have b12672 := hb (x (-6) 8 && x (-6) 12)
                  clear * - r12670 b12671 b12672 d12661
                  omega
                have d12673 : (x (-6) 4).toNat = 0 := by
                  have r12674 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
                  have b12675 := hb (x (-6) 4)
                  have b12676 := hb (x (-6) 12)
                  clear * - r12674 b12675 b12676 d12661
                  omega
                have d12677 : (x (-8) 2).toNat = 0 := by
                  have r12678 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e12679 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
                  have e12680 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
                  have b12681 := hb (x (-9) 3)
                  have b12682 := hb (x (-8) 2)
                  have b12683 := hb (x (-7) 13)
                  have b12684 := hb (x (-6) 12)
                  clear * - r12678 e12679 e12680 b12681 b12682 b12683 b12684 d12661 d12633
                  omega
                have d12685 : (x (-8) 2 && x (-8) 12).toNat = 0 := by
                  have r12686 := hand1 (x (-8) 2) (x (-8) 12)
                  have b12687 := hb (x (-8) 2)
                  have b12688 := hb (x (-8) 2 && x (-8) 12)
                  clear * - r12686 b12687 b12688 d12677
                  omega
                have d12689 : (x (-8) 10).toNat = 0 := by
                  have r12690 : (x (-8) 10).toNat ≤ (x (-8) 2).toNat := himp _ _ (hp10 (-8))
                  have b12691 := hb (x (-8) 2)
                  have b12692 := hb (x (-8) 10)
                  clear * - r12690 b12691 b12692 d12677
                  omega
                have d12693 : (x (-9) 3).toNat = 0 := by
                  have r12694 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e12695 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
                  have e12696 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
                  have b12697 := hb (x (-9) 3)
                  have b12698 := hb (x (-8) 2)
                  have b12699 := hb (x (-7) 13)
                  have b12700 := hb (x (-6) 12)
                  clear * - r12694 e12695 e12696 b12697 b12698 b12699 b12700 d12661 d12633 d12677
                  omega
                have d12701 : (x (-9) 3 && x (-9) 13).toNat = 0 := by
                  have r12702 := hand1 (x (-9) 3) (x (-9) 13)
                  have b12703 := hb (x (-9) 3)
                  have b12704 := hb (x (-9) 3 && x (-9) 13)
                  clear * - r12702 b12703 b12704 d12693
                  omega
                have d12705 : (x (-9) 11).toNat = 0 := by
                  have r12706 : (x (-9) 11).toNat ≤ (x (-9) 3).toNat := himp _ _ (hp11 (-9))
                  have b12707 := hb (x (-9) 3)
                  have b12708 := hb (x (-9) 11)
                  clear * - r12706 b12707 b12708 d12693
                  omega
                have d12709 : (x (-7) 9 && x (-7) 13).toNat = 1 := by
                  have r12710 : 1 ≤ (x 2 4).toNat + (x 1 1 && x 1 5).toNat + (x 0 2 && x 0 6).toNat + (x (-1) 3 && x (-1) 7).toNat + (x (-2) 4 && x (-2) 8).toNat + (x (-3) 5 && x (-3) 9).toNat + (x (-4) 6 && x (-4) 10).toNat + (x (-5) 7 && x (-5) 11).toNat + (x (-6) 8 && x (-6) 12).toNat + (x (-7) 9 && x (-7) 13).toNat + (x (-8) 10 && x (-8) 14).toNat + (x (-9) 11).toNat := by have q := hcov4 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e12711 : (x 1 1 && x 1 5).toNat = (x 1 5).toNat := handr _ _ (fun h => hp13 1 (hp5 1 (h)))
                  have e12712 : (x (-8) 10 && x (-8) 14).toNat = (x (-8) 10).toNat := handl _ _ (fun h => hp2 (-8) (hp10 (-8) (h)))
                  have b12713 := hb (x (-9) 11)
                  have b12714 := hb (x (-8) 10)
                  have b12715 := hb (x 1 5)
                  have b12716 := hb (x 2 4)
                  have b12717 := hb (x 0 2 && x 0 6)
                  have b12718 := hb (x (-1) 3 && x (-1) 7)
                  have b12719 := hb (x (-2) 4 && x (-2) 8)
                  have b12720 := hb (x (-3) 5 && x (-3) 9)
                  have b12721 := hb (x (-4) 6 && x (-4) 10)
                  have b12722 := hb (x (-5) 7 && x (-5) 11)
                  have b12723 := hb (x (-6) 8 && x (-6) 12)
                  have b12724 := hb (x (-7) 9 && x (-7) 13)
                  clear * - r12710 e12711 e12712 b12713 b12714 b12715 b12716 b12717 b12718 b12719 b12720 b12721 b12722 b12723 b12724 g17 g13 d12079 g20 d12417 d12437 d12457 d12477 d12669 d12689 d12705
                  omega
                have d12725 : (x (-7) 9).toNat = 1 := by
                  have r12726 := hand1 (x (-7) 9) (x (-7) 13)
                  have b12727 := hb (x (-7) 9)
                  have b12728 := hb (x (-7) 9 && x (-7) 13)
                  clear * - r12726 b12727 b12728 d12709
                  omega
                have d12729 : (x (-6) 8).toNat = 0 := by
                  have r12730 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e12731 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
                  have e12732 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
                  have e12733 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
                  have e12734 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
                  have e12735 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
                  have e12736 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
                  have b12737 := hb (x (-13) 7)
                  have b12738 := hb (x (-12) 6)
                  have b12739 := hb (x (-11) 5)
                  have b12740 := hb (x (-10) 4)
                  have b12741 := hb (x (-9) 11)
                  have b12742 := hb (x (-8) 10)
                  have b12743 := hb (x (-7) 9)
                  have b12744 := hb (x (-6) 8)
                  clear * - r12730 e12731 e12732 e12733 e12734 e12735 e12736 b12737 b12738 b12739 b12740 b12741 b12742 b12743 b12744 d12725 d12689 d12705
                  omega
                have d12745 : (x (-10) 4).toNat = 0 := by
                  have r12746 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e12747 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
                  have e12748 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
                  have e12749 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
                  have e12750 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
                  have e12751 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
                  have e12752 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
                  have b12753 := hb (x (-13) 7)
                  have b12754 := hb (x (-12) 6)
                  have b12755 := hb (x (-11) 5)
                  have b12756 := hb (x (-10) 4)
                  have b12757 := hb (x (-9) 11)
                  have b12758 := hb (x (-8) 10)
                  have b12759 := hb (x (-7) 9)
                  have b12760 := hb (x (-6) 8)
                  clear * - r12746 e12747 e12748 e12749 e12750 e12751 e12752 b12753 b12754 b12755 b12756 b12757 b12758 b12759 b12760 d12729 d12725 d12689 d12705
                  omega
                have d12761 : (x (-10) 4 && x (-10) 14).toNat = 0 := by
                  have r12762 := hand1 (x (-10) 4) (x (-10) 14)
                  have b12763 := hb (x (-10) 4)
                  have b12764 := hb (x (-10) 4 && x (-10) 14)
                  clear * - r12762 b12763 b12764 d12745
                  omega
                have d12765 : (x (-11) 5).toNat = 0 := by
                  have r12766 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e12767 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
                  have e12768 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
                  have e12769 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
                  have e12770 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
                  have e12771 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
                  have e12772 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
                  have b12773 := hb (x (-13) 7)
                  have b12774 := hb (x (-12) 6)
                  have b12775 := hb (x (-11) 5)
                  have b12776 := hb (x (-10) 4)
                  have b12777 := hb (x (-9) 11)
                  have b12778 := hb (x (-8) 10)
                  have b12779 := hb (x (-7) 9)
                  have b12780 := hb (x (-6) 8)
                  clear * - r12766 e12767 e12768 e12769 e12770 e12771 e12772 b12773 b12774 b12775 b12776 b12777 b12778 b12779 b12780 d12729 d12725 d12689 d12705 d12745
                  omega
                have d12781 : (x (-7) 1 && x (-7) 11).toNat = 1 := by
                  have r12782 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b12783 := hb (x (-11) 5)
                  have b12784 := hb (x (-6) 10)
                  have b12785 := hb (x (-7) 1 && x (-7) 11)
                  have b12786 := hb (x (-8) 2 && x (-8) 12)
                  have b12787 := hb (x (-9) 3 && x (-9) 13)
                  have b12788 := hb (x (-10) 4 && x (-10) 14)
                  clear * - r12782 b12783 b12784 b12785 b12786 b12787 b12788 d12657 d12685 d12701 d12761 d12765
                  omega
                have d12789 : (x (-7) 11).toNat = 1 := by
                  have r12790 := hand2 (x (-7) 1) (x (-7) 11)
                  have b12791 := hb (x (-7) 11)
                  have b12792 := hb (x (-7) 1 && x (-7) 11)
                  clear * - r12790 b12791 b12792 d12781
                  omega
                have d12793 : (x (-7) 3).toNat = 1 := by
                  have r12794 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
                  have b12795 := hb (x (-7) 3)
                  have b12796 := hb (x (-7) 11)
                  clear * - r12794 b12795 b12796 d12789
                  omega
                have d12797 : (x (-4) 12).toNat = 0 := by
                  have r12798 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e12799 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                  have e12800 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                  have b12801 := hb (x (-7) 3)
                  have b12802 := hb (x (-6) 2)
                  have b12803 := hb (x (-5) 13)
                  have b12804 := hb (x (-4) 12)
                  clear * - r12798 e12799 e12800 b12801 b12802 b12803 b12804 d12653 d12793
                  omega
                have d12805 : (x (-4) 1 && x (-4) 12).toNat = 0 := by
                  have r12806 := hand2 (x (-4) 1) (x (-4) 12)
                  have b12807 := hb (x (-4) 12)
                  have b12808 := hb (x (-4) 1 && x (-4) 12)
                  clear * - r12806 b12807 b12808 d12797
                  omega
                have d12809 : (x (-4) 2 && x (-4) 12).toNat = 0 := by
                  have r12810 := hand2 (x (-4) 2) (x (-4) 12)
                  have b12811 := hb (x (-4) 12)
                  have b12812 := hb (x (-4) 2 && x (-4) 12)
                  clear * - r12810 b12811 b12812 d12797
                  omega
                have d12813 : (x (-5) 13).toNat = 0 := by
                  have r12814 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e12815 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                  have e12816 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                  have b12817 := hb (x (-7) 3)
                  have b12818 := hb (x (-6) 2)
                  have b12819 := hb (x (-5) 13)
                  have b12820 := hb (x (-4) 12)
                  clear * - r12814 e12815 e12816 b12817 b12818 b12819 b12820 d12797 d12653 d12793
                  omega
                have d12821 : (x (-5) 2 && x (-5) 13).toNat = 0 := by
                  have r12822 := hand2 (x (-5) 2) (x (-5) 13)
                  have b12823 := hb (x (-5) 13)
                  have b12824 := hb (x (-5) 2 && x (-5) 13)
                  clear * - r12822 b12823 b12824 d12813
                  omega
                have d12825 : (x (-7) 4).toNat = 1 := by
                  have r12826 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := by have q := hcov11 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b12827 := hb (x (-7) 4)
                  have b12828 := hb (x (-3) 11)
                  have b12829 := hb (x (-4) 1 && x (-4) 12)
                  have b12830 := hb (x (-5) 2 && x (-5) 13)
                  have b12831 := hb (x (-6) 3 && x (-6) 14)
                  clear * - r12826 b12827 b12828 b12829 b12830 b12831 d11905 d12805 d12821 d12645
                  omega
                have d12832 : (x (-7) 12).toNat = 1 := by
                  have r12833 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
                  have b12834 := hb (x (-7) 4)
                  have b12835 := hb (x (-7) 12)
                  clear * - r12833 b12834 b12835 d12825
                  omega
                have d12836 : (x (-9) 2).toNat = 0 := by
                  have r12837 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e12838 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
                  have e12839 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
                  have b12840 := hb (x (-10) 3)
                  have b12841 := hb (x (-9) 2)
                  have b12842 := hb (x (-8) 13)
                  have b12843 := hb (x (-7) 12)
                  clear * - r12837 e12838 e12839 b12840 b12841 b12842 b12843 d12832 d12612
                  omega
                have d12844 : (x (-9) 2 && x (-9) 12).toNat = 0 := by
                  have r12845 := hand1 (x (-9) 2) (x (-9) 12)
                  have b12846 := hb (x (-9) 2)
                  have b12847 := hb (x (-9) 2 && x (-9) 12)
                  clear * - r12845 b12846 b12847 d12836
                  omega
                have d12848 : (x (-10) 3).toNat = 0 := by
                  have r12849 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e12850 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
                  have e12851 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
                  have b12852 := hb (x (-10) 3)
                  have b12853 := hb (x (-9) 2)
                  have b12854 := hb (x (-8) 13)
                  have b12855 := hb (x (-7) 12)
                  clear * - r12849 e12850 e12851 b12852 b12853 b12854 b12855 d12832 d12612 d12836
                  omega
                have d12856 : (x (-10) 3 && x (-10) 13).toNat = 0 := by
                  have r12857 := hand1 (x (-10) 3) (x (-10) 13)
                  have b12858 := hb (x (-10) 3)
                  have b12859 := hb (x (-10) 3 && x (-10) 13)
                  clear * - r12857 b12858 b12859 d12848
                  omega
                have d12860 : (x (-7) 10).toNat = 1 := by
                  have r12861 : 1 ≤ (x (-7) 10).toNat + (x (-8) 1 && x (-8) 11).toNat + (x (-9) 2 && x (-9) 12).toNat + (x (-10) 3 && x (-10) 13).toNat + (x (-11) 4 && x (-11) 14).toNat + (x (-12) 5).toNat := by have q := hcov10 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b12862 := hb (x (-12) 5)
                  have b12863 := hb (x (-7) 10)
                  have b12864 := hb (x (-8) 1 && x (-8) 11)
                  have b12865 := hb (x (-9) 2 && x (-9) 12)
                  have b12866 := hb (x (-10) 3 && x (-10) 13)
                  have b12867 := hb (x (-11) 4 && x (-11) 14)
                  clear * - r12861 b12862 b12863 b12864 b12865 b12866 b12867 d12608 d12844 d12856 d12568 d12572
                  omega
                have d12868 : (x (-7) 2).toNat = 1 := by
                  have r12869 : (x (-7) 10).toNat ≤ (x (-7) 2).toNat := himp _ _ (hp10 (-7))
                  have b12870 := hb (x (-7) 2)
                  have b12871 := hb (x (-7) 10)
                  clear * - r12869 b12870 b12871 d12860
                  omega
                have d12872 : (x (-5) 12).toNat = 0 := by
                  have r12873 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e12874 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                  have e12875 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                  have b12876 := hb (x (-8) 3)
                  have b12877 := hb (x (-7) 2)
                  have b12878 := hb (x (-6) 13)
                  have b12879 := hb (x (-5) 12)
                  clear * - r12873 e12874 e12875 b12876 b12877 b12878 b12879 d12868
                  omega
                have d12880 : (x (-5) 4).toNat = 0 := by
                  have r12881 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
                  have b12882 := hb (x (-5) 4)
                  have b12883 := hb (x (-5) 12)
                  clear * - r12881 b12882 b12883 d12872
                  omega
                have d12884 : (x (-3) 8).toNat = 0 := by
                  have r12885 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e12886 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
                  have e12887 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
                  have e12888 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
                  have e12889 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
                  have e12890 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
                  have e12891 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
                  have b12892 := hb (x (-10) 7)
                  have b12893 := hb (x (-9) 6)
                  have b12894 := hb (x (-8) 5)
                  have b12895 := hb (x (-7) 4)
                  have b12896 := hb (x (-6) 11)
                  have b12897 := hb (x (-5) 10)
                  have b12898 := hb (x (-4) 9)
                  have b12899 := hb (x (-3) 8)
                  clear * - r12885 e12886 e12887 e12888 e12889 e12890 e12891 b12892 b12893 b12894 b12895 b12896 b12897 b12898 b12899 d12825 d12616
                  omega
                have d12900 : (x (-3) 8 && x (-3) 12).toNat = 0 := by
                  have r12901 := hand1 (x (-3) 8) (x (-3) 12)
                  have b12902 := hb (x (-3) 8)
                  have b12903 := hb (x (-3) 8 && x (-3) 12)
                  clear * - r12901 b12902 b12903 d12884
                  omega
                have d12904 : (x (-4) 9).toNat = 0 := by
                  have r12905 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e12906 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
                  have e12907 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
                  have e12908 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
                  have e12909 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
                  have e12910 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
                  have e12911 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
                  have b12912 := hb (x (-10) 7)
                  have b12913 := hb (x (-9) 6)
                  have b12914 := hb (x (-8) 5)
                  have b12915 := hb (x (-7) 4)
                  have b12916 := hb (x (-6) 11)
                  have b12917 := hb (x (-5) 10)
                  have b12918 := hb (x (-4) 9)
                  have b12919 := hb (x (-3) 8)
                  clear * - r12905 e12906 e12907 e12908 e12909 e12910 e12911 b12912 b12913 b12914 b12915 b12916 b12917 b12918 b12919 d12884 d12825 d12616
                  omega
                have d12920 : (x (-4) 9 && x (-4) 13).toNat = 0 := by
                  have r12921 := hand1 (x (-4) 9) (x (-4) 13)
                  have b12922 := hb (x (-4) 9)
                  have b12923 := hb (x (-4) 9 && x (-4) 13)
                  clear * - r12921 b12922 b12923 d12904
                  omega
                have d12924 : (x (-5) 10).toNat = 0 := by
                  have r12925 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e12926 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
                  have e12927 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
                  have e12928 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
                  have e12929 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
                  have e12930 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
                  have e12931 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
                  have b12932 := hb (x (-10) 7)
                  have b12933 := hb (x (-9) 6)
                  have b12934 := hb (x (-8) 5)
                  have b12935 := hb (x (-7) 4)
                  have b12936 := hb (x (-6) 11)
                  have b12937 := hb (x (-5) 10)
                  have b12938 := hb (x (-4) 9)
                  have b12939 := hb (x (-3) 8)
                  clear * - r12925 e12926 e12927 e12928 e12929 e12930 e12931 b12932 b12933 b12934 b12935 b12936 b12937 b12938 b12939 d12884 d12904 d12825 d12616
                  omega
                have d12940 : (x (-6) 11).toNat = 0 := by
                  have r12941 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e12942 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
                  have e12943 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
                  have e12944 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
                  have e12945 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
                  have e12946 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
                  have e12947 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
                  have b12948 := hb (x (-10) 7)
                  have b12949 := hb (x (-9) 6)
                  have b12950 := hb (x (-8) 5)
                  have b12951 := hb (x (-7) 4)
                  have b12952 := hb (x (-6) 11)
                  have b12953 := hb (x (-5) 10)
                  have b12954 := hb (x (-4) 9)
                  have b12955 := hb (x (-3) 8)
                  clear * - r12941 e12942 e12943 e12944 e12945 e12946 e12947 b12948 b12949 b12950 b12951 b12952 b12953 b12954 b12955 d12884 d12904 d12924 d12825 d12616
                  omega
                have d12956 : (x (-5) 3 && x (-5) 13).toNat = 0 := by
                  have r12957 := hand2 (x (-5) 3) (x (-5) 13)
                  have b12958 := hb (x (-5) 13)
                  have b12959 := hb (x (-5) 3 && x (-5) 13)
                  clear * - r12957 b12958 b12959 d12813
                  omega
                have d12960 : (x (-7) 5).toNat = 1 := by
                  have r12961 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b12962 := hb (x (-7) 5)
                  have b12963 := hb (x (-2) 10)
                  have b12964 := hb (x (-3) 1 && x (-3) 11)
                  have b12965 := hb (x (-4) 2 && x (-4) 12)
                  have b12966 := hb (x (-5) 3 && x (-5) 13)
                  have b12967 := hb (x (-6) 4 && x (-6) 14)
                  clear * - r12961 b12962 b12963 b12964 b12965 b12966 b12967 d11812 d11909 d12809 d12956 d12649
                  omega
                have d12968 : (x (-2) 8).toNat = 0 := by
                  have r12969 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e12970 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                  have e12971 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                  have e12972 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                  have e12973 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                  have e12974 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                  have e12975 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                  have b12976 := hb (x (-9) 7)
                  have b12977 := hb (x (-8) 6)
                  have b12978 := hb (x (-7) 5)
                  have b12979 := hb (x (-6) 4)
                  have b12980 := hb (x (-5) 11)
                  have b12981 := hb (x (-4) 10)
                  have b12982 := hb (x (-3) 9)
                  have b12983 := hb (x (-2) 8)
                  clear * - r12969 e12970 e12971 e12972 e12973 e12974 e12975 b12976 b12977 b12978 b12979 b12980 b12981 b12982 b12983 d12673 d12960
                  omega
                have d12984 : (x (-2) 8 && x (-2) 12).toNat = 0 := by
                  have r12985 := hand1 (x (-2) 8) (x (-2) 12)
                  have b12986 := hb (x (-2) 8)
                  have b12987 := hb (x (-2) 8 && x (-2) 12)
                  clear * - r12985 b12986 b12987 d12968
                  omega
                have d12988 : (x (-3) 9).toNat = 0 := by
                  have r12989 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e12990 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                  have e12991 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                  have e12992 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                  have e12993 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                  have e12994 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                  have e12995 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                  have b12996 := hb (x (-9) 7)
                  have b12997 := hb (x (-8) 6)
                  have b12998 := hb (x (-7) 5)
                  have b12999 := hb (x (-6) 4)
                  have b13000 := hb (x (-5) 11)
                  have b13001 := hb (x (-4) 10)
                  have b13002 := hb (x (-3) 9)
                  have b13003 := hb (x (-2) 8)
                  clear * - r12989 e12990 e12991 e12992 e12993 e12994 e12995 b12996 b12997 b12998 b12999 b13000 b13001 b13002 b13003 d12968 d12673 d12960
                  omega
                have d13004 : (x (-3) 9 && x (-3) 13).toNat = 0 := by
                  have r13005 := hand1 (x (-3) 9) (x (-3) 13)
                  have b13006 := hb (x (-3) 9)
                  have b13007 := hb (x (-3) 9 && x (-3) 13)
                  clear * - r13005 b13006 b13007 d12988
                  omega
                have d13008 : (x (-4) 10).toNat = 0 := by
                  have r13009 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e13010 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                  have e13011 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                  have e13012 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                  have e13013 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                  have e13014 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                  have e13015 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                  have b13016 := hb (x (-9) 7)
                  have b13017 := hb (x (-8) 6)
                  have b13018 := hb (x (-7) 5)
                  have b13019 := hb (x (-6) 4)
                  have b13020 := hb (x (-5) 11)
                  have b13021 := hb (x (-4) 10)
                  have b13022 := hb (x (-3) 9)
                  have b13023 := hb (x (-2) 8)
                  clear * - r13009 e13010 e13011 e13012 e13013 e13014 e13015 b13016 b13017 b13018 b13019 b13020 b13021 b13022 b13023 d12968 d12988 d12673 d12960
                  omega
                have d13024 : (x (-5) 11).toNat = 0 := by
                  have r13025 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e13026 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                  have e13027 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                  have e13028 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                  have e13029 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                  have e13030 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                  have e13031 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                  have b13032 := hb (x (-9) 7)
                  have b13033 := hb (x (-8) 6)
                  have b13034 := hb (x (-7) 5)
                  have b13035 := hb (x (-6) 4)
                  have b13036 := hb (x (-5) 11)
                  have b13037 := hb (x (-4) 10)
                  have b13038 := hb (x (-3) 9)
                  have b13039 := hb (x (-2) 8)
                  clear * - r13025 e13026 e13027 e13028 e13029 e13030 e13031 b13032 b13033 b13034 b13035 b13036 b13037 b13038 b13039 d12968 d12988 d13008 d12673 d12960
                  omega
                have r13040 : (x 8 1).toNat + (x 7 2).toNat + (x 6 3).toNat + (x 5 4).toNat + (x 4 5).toNat + (x 3 6).toNat + (x 2 7).toNat + (x 1 8).toNat + (x 0 9).toNat + (x (-1) 10).toNat + (x (-2) 11).toNat + (x (-3) 12).toNat + (x (-4) 13).toNat + (x (-5) 14).toNat = 3 := by have q := hcount 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r13041 : (x 9 1).toNat + (x 8 2).toNat + (x 7 3).toNat + (x 6 4).toNat + (x 5 5).toNat + (x 4 6).toNat + (x 3 7).toNat + (x 2 8).toNat + (x 1 9).toNat + (x 0 10).toNat + (x (-1) 11).toNat + (x (-2) 12).toNat + (x (-3) 13).toNat + (x (-4) 14).toNat = 3 := by have q := hcount 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r13042 : 1 ≤ (x 5 4).toNat + (x 4 1 && x 4 5).toNat + (x 3 2 && x 3 6).toNat + (x 2 3 && x 2 7).toNat + (x 1 4 && x 1 8).toNat + (x 0 5 && x 0 9).toNat + (x (-1) 6 && x (-1) 10).toNat + (x (-2) 7 && x (-2) 11).toNat + (x (-3) 8 && x (-3) 12).toNat + (x (-4) 9 && x (-4) 13).toNat + (x (-5) 10 && x (-5) 14).toNat + (x (-6) 11).toNat := by have q := hcov4 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e13043 : (x 4 1 && x 4 5).toNat = (x 4 5).toNat := handr _ _ (fun h => hp13 4 (hp5 4 (h)))
                have e13044 : (x (-5) 10 && x (-5) 14).toNat = (x (-5) 10).toNat := handl _ _ (fun h => hp2 (-5) (hp10 (-5) (h)))
                have r13045 : 1 ≤ (x 6 4).toNat + (x 5 1 && x 5 5).toNat + (x 4 2 && x 4 6).toNat + (x 3 3 && x 3 7).toNat + (x 2 4 && x 2 8).toNat + (x 1 5 && x 1 9).toNat + (x 0 6 && x 0 10).toNat + (x (-1) 7 && x (-1) 11).toNat + (x (-2) 8 && x (-2) 12).toNat + (x (-3) 9 && x (-3) 13).toNat + (x (-4) 10 && x (-4) 14).toNat + (x (-5) 11).toNat := by have q := hcov4 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e13046 : (x 5 1 && x 5 5).toNat = (x 5 5).toNat := handr _ _ (fun h => hp13 5 (hp5 5 (h)))
                have e13047 : (x (-4) 10 && x (-4) 14).toNat = (x (-4) 10).toNat := handl _ _ (fun h => hp2 (-4) (hp10 (-4) (h)))
                have r13048 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r13049 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r13050 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r13051 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
                have r13052 := hand2 (x 3 2) (x 3 6)
                have r13053 := hand2 (x 2 3) (x 2 7)
                have r13054 := hand2 (x 4 2) (x 4 6)
                have r13055 := hand2 (x 3 3) (x 3 7)
                have r13056 := hand2 (x (-2) 1) (x (-2) 12)
                have r13057 := hand2 (x (-3) 2) (x (-3) 13)
                have r13058 := hand2 (x (-4) 3) (x (-4) 14)
                have r13059 := hand2 (x (-5) 1) (x (-5) 14)
                have r13060 := hand1 (x 8 1) (x 8 14)
                linarith only [r13040, r13041, r13042, e13043, e13044, r13045, e13046, e13047, r13048, r13049, r13050, r13051, r13052, r13053, r13054, r13055, r13056, r13057, r13058, r13059, r13060, d12653, d12940, d12880, d12924, d13024, d13008, g2, g5, g6, g11, f12368, g15, d12385, d12369, g23, g24, g25, g26, d12900, d12920, g27, g28, d12075, g29, d12984, d13004]
              · have f13117 : (x 1 7).toNat = 1 := by rw [h12487]; rfl
                have d13118 : (x 8 8).toNat = 0 := by
                  have r13119 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e13120 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                  have e13121 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                  have e13122 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                  have e13123 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                  have e13124 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                  have e13125 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                  have b13126 := hb (x 1 7)
                  have b13127 := hb (x 2 6)
                  have b13128 := hb (x 3 5)
                  have b13129 := hb (x 4 4)
                  have b13130 := hb (x 5 11)
                  have b13131 := hb (x 6 10)
                  have b13132 := hb (x 7 9)
                  have b13133 := hb (x 8 8)
                  clear * - r13119 e13120 e13121 e13122 e13123 e13124 e13125 b13126 b13127 b13128 b13129 b13130 b13131 b13132 b13133 f13117
                  omega
                have d13134 : (x 8 1 && x 8 8).toNat = 0 := by
                  have r13135 := hand2 (x 8 1) (x 8 8)
                  have b13136 := hb (x 8 8)
                  have b13137 := hb (x 8 1 && x 8 8)
                  clear * - r13135 b13136 b13137 d13118
                  omega
                have d13138 : (x 8 3 && x 8 8).toNat = 0 := by
                  have r13139 := hand2 (x 8 3) (x 8 8)
                  have b13140 := hb (x 8 8)
                  have b13141 := hb (x 8 3 && x 8 8)
                  clear * - r13139 b13140 b13141 d13118
                  omega
                have d13142 : (x 7 9).toNat = 0 := by
                  have r13143 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e13144 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                  have e13145 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                  have e13146 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                  have e13147 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                  have e13148 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                  have e13149 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                  have b13150 := hb (x 1 7)
                  have b13151 := hb (x 2 6)
                  have b13152 := hb (x 3 5)
                  have b13153 := hb (x 4 4)
                  have b13154 := hb (x 5 11)
                  have b13155 := hb (x 6 10)
                  have b13156 := hb (x 7 9)
                  have b13157 := hb (x 8 8)
                  clear * - r13143 e13144 e13145 e13146 e13147 e13148 e13149 b13150 b13151 b13152 b13153 b13154 b13155 b13156 b13157 d13118 f13117
                  omega
                have d13158 : (x 7 2 && x 7 9).toNat = 0 := by
                  have r13159 := hand2 (x 7 2) (x 7 9)
                  have b13160 := hb (x 7 9)
                  have b13161 := hb (x 7 2 && x 7 9)
                  clear * - r13159 b13160 b13161 d13142
                  omega
                have d13162 : (x 7 4 && x 7 9).toNat = 0 := by
                  have r13163 := hand2 (x 7 4) (x 7 9)
                  have b13164 := hb (x 7 9)
                  have b13165 := hb (x 7 4 && x 7 9)
                  clear * - r13163 b13164 b13165 d13142
                  omega
                have d13166 : (x 6 10).toNat = 0 := by
                  have r13167 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e13168 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                  have e13169 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                  have e13170 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                  have e13171 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                  have e13172 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                  have e13173 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                  have b13174 := hb (x 1 7)
                  have b13175 := hb (x 2 6)
                  have b13176 := hb (x 3 5)
                  have b13177 := hb (x 4 4)
                  have b13178 := hb (x 5 11)
                  have b13179 := hb (x 6 10)
                  have b13180 := hb (x 7 9)
                  have b13181 := hb (x 8 8)
                  clear * - r13167 e13168 e13169 e13170 e13171 e13172 e13173 b13174 b13175 b13176 b13177 b13178 b13179 b13180 b13181 d13118 d13142 f13117
                  omega
                have d13182 : (x 6 1 && x 6 10).toNat = 0 := by
                  have r13183 := hand2 (x 6 1) (x 6 10)
                  have b13184 := hb (x 6 10)
                  have b13185 := hb (x 6 1 && x 6 10)
                  clear * - r13183 b13184 b13185 d13166
                  omega
                have d13186 : (x 6 3 && x 6 10).toNat = 0 := by
                  have r13187 := hand2 (x 6 3) (x 6 10)
                  have b13188 := hb (x 6 10)
                  have b13189 := hb (x 6 3 && x 6 10)
                  clear * - r13187 b13188 b13189 d13166
                  omega
                have d13190 : (x 6 5 && x 6 10).toNat = 0 := by
                  have r13191 := hand2 (x 6 5) (x 6 10)
                  have b13192 := hb (x 6 10)
                  have b13193 := hb (x 6 5 && x 6 10)
                  clear * - r13191 b13192 b13193 d13166
                  omega
                have d13194 : (x 5 11).toNat = 0 := by
                  have r13195 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e13196 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                  have e13197 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                  have e13198 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                  have e13199 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                  have e13200 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                  have e13201 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                  have b13202 := hb (x 1 7)
                  have b13203 := hb (x 2 6)
                  have b13204 := hb (x 3 5)
                  have b13205 := hb (x 4 4)
                  have b13206 := hb (x 5 11)
                  have b13207 := hb (x 6 10)
                  have b13208 := hb (x 7 9)
                  have b13209 := hb (x 8 8)
                  clear * - r13195 e13196 e13197 e13198 e13199 e13200 e13201 b13202 b13203 b13204 b13205 b13206 b13207 b13208 b13209 d13118 d13142 d13166 f13117
                  omega
                have d13210 : (x 5 1 && x 5 11).toNat = 0 := by
                  have r13211 := hand2 (x 5 1) (x 5 11)
                  have b13212 := hb (x 5 11)
                  have b13213 := hb (x 5 1 && x 5 11)
                  clear * - r13211 b13212 b13213 d13194
                  omega
                have d13214 : (x 5 2 && x 5 11).toNat = 0 := by
                  have r13215 := hand2 (x 5 2) (x 5 11)
                  have b13216 := hb (x 5 11)
                  have b13217 := hb (x 5 2 && x 5 11)
                  clear * - r13215 b13216 b13217 d13194
                  omega
                have d13218 : (x 4 3 && x 4 12).toNat = 1 := by
                  have r13219 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b13220 := hb (x 1 6)
                  have b13221 := hb (x 7 9)
                  have b13222 := hb (x 6 1 && x 6 10)
                  have b13223 := hb (x 5 2 && x 5 11)
                  have b13224 := hb (x 4 3 && x 4 12)
                  have b13225 := hb (x 3 4 && x 3 13)
                  have b13226 := hb (x 2 5 && x 2 14)
                  clear * - r13219 b13220 b13221 b13222 b13223 b13224 b13225 b13226 d13142 d13182 d13214 g61 g62 g14
                  omega
                have d13227 : (x 4 12).toNat = 1 := by
                  have r13228 := hand2 (x 4 3) (x 4 12)
                  have b13229 := hb (x 4 12)
                  have b13230 := hb (x 4 3 && x 4 12)
                  clear * - r13228 b13229 b13230 d13218
                  omega
                have d13231 : (x 3 13).toNat = 0 := by
                  have r13232 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e13233 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                  have e13234 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                  have b13235 := hb (x 1 3)
                  have b13236 := hb (x 2 2)
                  have b13237 := hb (x 3 13)
                  have b13238 := hb (x 4 12)
                  clear * - r13232 e13233 e13234 b13235 b13236 b13237 b13238 d13227 f12484
                  omega
                have d13239 : (x 3 3 && x 3 13).toNat = 0 := by
                  have r13240 := hand2 (x 3 3) (x 3 13)
                  have b13241 := hb (x 3 13)
                  have b13242 := hb (x 3 3 && x 3 13)
                  clear * - r13240 b13241 b13242 d13231
                  omega
                have d13243 : (x 4 2 && x 4 12).toNat = 1 := by
                  have r13244 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b13245 := hb (x 1 5)
                  have b13246 := hb (x 6 10)
                  have b13247 := hb (x 5 1 && x 5 11)
                  have b13248 := hb (x 4 2 && x 4 12)
                  have b13249 := hb (x 3 3 && x 3 13)
                  have b13250 := hb (x 2 4 && x 2 14)
                  clear * - r13244 b13245 b13246 b13247 b13248 b13249 b13250 d13166 d13210 d13239 g68 g13
                  omega
                have d13251 : (x 4 2).toNat = 1 := by
                  have r13252 := hand1 (x 4 2) (x 4 12)
                  have b13253 := hb (x 4 2)
                  have b13254 := hb (x 4 2 && x 4 12)
                  clear * - r13252 b13253 b13254 d13243
                  omega
                have d13255 : (x 4 14).toNat = 1 := by
                  have r13256 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
                  have b13257 := hb (x 4 2)
                  have b13258 := hb (x 4 14)
                  clear * - r13256 b13257 b13258 d13251
                  omega
                have d13259 : (x 3 1).toNat = 0 := by
                  have r13260 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b13261 := hb (x 3 1)
                  have b13262 := hb (x 4 14)
                  clear * - r13260 b13261 b13262 d13255
                  omega
                have d13263 : (x 3 1 && x 3 14).toNat = 0 := by
                  have r13264 := hand1 (x 3 1) (x 3 14)
                  have b13265 := hb (x 3 1)
                  have b13266 := hb (x 3 1 && x 3 14)
                  clear * - r13264 b13265 b13266 d13259
                  omega
                have d13267 : (x 6 12).toNat = 0 := by
                  have r13268 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e13269 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                  have e13270 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                  have b13271 := hb (x 3 3)
                  have b13272 := hb (x 4 2)
                  have b13273 := hb (x 5 13)
                  have b13274 := hb (x 6 12)
                  clear * - r13268 e13269 e13270 b13271 b13272 b13273 b13274 d13251
                  omega
                have d13275 : (x 5 13).toNat = 0 := by
                  have r13276 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e13277 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                  have e13278 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                  have b13279 := hb (x 3 3)
                  have b13280 := hb (x 4 2)
                  have b13281 := hb (x 5 13)
                  have b13282 := hb (x 6 12)
                  clear * - r13276 e13277 e13278 b13279 b13280 b13281 b13282 d13267 d13251
                  omega
                have d13283 : (x 3 6 && x 3 13).toNat = 0 := by
                  have r13284 := hand2 (x 3 6) (x 3 13)
                  have b13285 := hb (x 3 13)
                  have b13286 := hb (x 3 6 && x 3 13)
                  clear * - r13284 b13285 b13286 d13231
                  omega
                have d13287 : (x 3 5).toNat = 0 := by
                  have r13288 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
                  have b13289 := hb (x 3 5)
                  have b13290 := hb (x 3 13)
                  clear * - r13288 b13289 b13290 d13231
                  omega
                have d13291 : (x 3 5 && x 3 14).toNat = 0 := by
                  have r13292 := hand1 (x 3 5) (x 3 14)
                  have b13293 := hb (x 3 5)
                  have b13294 := hb (x 3 5 && x 3 14)
                  clear * - r13292 b13293 b13294 d13287
                  omega
                have d13295 : (x 2 1 && x 2 14).toNat = 1 := by
                  have r13296 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b13297 := hb (x 1 2)
                  have b13298 := hb (x 3 13)
                  have b13299 := hb (x 2 1 && x 2 14)
                  clear * - r13296 b13297 b13298 b13299 d13231 g12
                  omega
                have d13300 : (x 2 1).toNat = 1 := by
                  have r13301 := hand1 (x 2 1) (x 2 14)
                  have b13302 := hb (x 2 1)
                  have b13303 := hb (x 2 1 && x 2 14)
                  clear * - r13301 b13302 b13303 d13295
                  omega
                have d13304 : (x 3 14).toNat = 0 := by
                  have r13305 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b13306 := hb (x 2 1)
                  have b13307 := hb (x 3 14)
                  clear * - r13305 b13306 b13307 d13300
                  omega
                have d13308 : (x 3 6).toNat = 0 := by
                  have r13309 : (x 3 6).toNat ≤ (x 3 14).toNat := himp _ _ (hp6 3)
                  have b13310 := hb (x 3 6)
                  have b13311 := hb (x 3 14)
                  clear * - r13309 b13310 b13311 d13304
                  omega
                have d13312 : (x 3 2).toNat = 0 := by
                  have r13313 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
                  have b13314 := hb (x 3 2)
                  have b13315 := hb (x 3 14)
                  clear * - r13313 b13314 b13315 d13304
                  omega
                have d13316 : (x 4 1 && x 4 14).toNat = 1 := by
                  have r13317 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b13318 := hb (x 3 2)
                  have b13319 := hb (x 5 13)
                  have b13320 := hb (x 4 1 && x 4 14)
                  clear * - r13317 b13318 b13319 b13320 d13275 d13312
                  omega
                have d13321 : (x 4 1).toNat = 1 := by
                  have r13322 := hand1 (x 4 1) (x 4 14)
                  have b13323 := hb (x 4 1)
                  have b13324 := hb (x 4 1 && x 4 14)
                  clear * - r13322 b13323 b13324 d13316
                  omega
                have d13325 : (x 5 14).toNat = 0 := by
                  have r13326 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b13327 := hb (x 4 1)
                  have b13328 := hb (x 5 14)
                  clear * - r13326 b13327 b13328 d13321
                  omega
                have d13329 : (x 5 3 && x 5 14).toNat = 0 := by
                  have r13330 := hand2 (x 5 3) (x 5 14)
                  have b13331 := hb (x 5 14)
                  have b13332 := hb (x 5 3 && x 5 14)
                  clear * - r13330 b13331 b13332 d13325
                  omega
                have d13333 : (x 5 6).toNat = 0 := by
                  have r13334 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
                  have b13335 := hb (x 5 6)
                  have b13336 := hb (x 5 14)
                  clear * - r13334 b13335 b13336 d13325
                  omega
                have d13337 : (x 5 6 && x 5 11).toNat = 0 := by
                  have r13338 := hand1 (x 5 6) (x 5 11)
                  have b13339 := hb (x 5 6)
                  have b13340 := hb (x 5 6 && x 5 11)
                  clear * - r13338 b13339 b13340 d13333
                  omega
                have d13341 : (x 5 2).toNat = 0 := by
                  have r13342 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
                  have b13343 := hb (x 5 2)
                  have b13344 := hb (x 5 14)
                  clear * - r13342 b13343 b13344 d13325
                  omega
                have d13345 : (x 5 10).toNat = 0 := by
                  have r13346 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
                  have b13347 := hb (x 5 2)
                  have b13348 := hb (x 5 10)
                  clear * - r13346 b13347 b13348 d13341
                  omega
                have d13349 : (x 4 1 && x 4 11).toNat = 1 := by
                  have r13350 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b13351 := hb (x 0 5)
                  have b13352 := hb (x 5 10)
                  have b13353 := hb (x 4 1 && x 4 11)
                  have b13354 := hb (x 3 2 && x 3 12)
                  have b13355 := hb (x 2 3 && x 2 13)
                  have b13356 := hb (x 1 4 && x 1 14)
                  clear * - r13350 b13351 b13352 b13353 b13354 b13355 b13356 d13345 g65 g66 g67 g9
                  omega
                have d13357 : (x 4 11).toNat = 1 := by
                  have r13358 := hand2 (x 4 1) (x 4 11)
                  have b13359 := hb (x 4 11)
                  have b13360 := hb (x 4 1 && x 4 11)
                  clear * - r13358 b13359 b13360 d13349
                  omega
                have d13361 : (x 4 3).toNat = 1 := by
                  have r13362 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
                  have b13363 := hb (x 4 3)
                  have b13364 := hb (x 4 11)
                  clear * - r13362 b13363 b13364 d13357
                  omega
                have d13365 : (x 7 12).toNat = 0 := by
                  have r13366 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e13367 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                  have e13368 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                  have b13369 := hb (x 4 3)
                  have b13370 := hb (x 5 2)
                  have b13371 := hb (x 6 13)
                  have b13372 := hb (x 7 12)
                  clear * - r13366 e13367 e13368 b13369 b13370 b13371 b13372 d13341 d13361
                  omega
                have d13373 : (x 7 1 && x 7 12).toNat = 0 := by
                  have r13374 := hand2 (x 7 1) (x 7 12)
                  have b13375 := hb (x 7 12)
                  have b13376 := hb (x 7 1 && x 7 12)
                  clear * - r13374 b13375 b13376 d13365
                  omega
                have d13377 : (x 7 4).toNat = 0 := by
                  have r13378 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
                  have b13379 := hb (x 7 4)
                  have b13380 := hb (x 7 12)
                  clear * - r13378 b13379 b13380 d13365
                  omega
                have d13381 : (x 6 13).toNat = 0 := by
                  have r13382 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e13383 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                  have e13384 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                  have b13385 := hb (x 4 3)
                  have b13386 := hb (x 5 2)
                  have b13387 := hb (x 6 13)
                  have b13388 := hb (x 7 12)
                  clear * - r13382 e13383 e13384 b13385 b13386 b13387 b13388 d13365 d13341 d13361
                  omega
                have d13389 : (x 6 2 && x 6 13).toNat = 0 := by
                  have r13390 := hand2 (x 6 2) (x 6 13)
                  have b13391 := hb (x 6 13)
                  have b13392 := hb (x 6 2 && x 6 13)
                  clear * - r13390 b13391 b13392 d13381
                  omega
                have d13393 : (x 6 5).toNat = 0 := by
                  have r13394 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
                  have b13395 := hb (x 6 5)
                  have b13396 := hb (x 6 13)
                  clear * - r13394 b13395 b13396 d13381
                  omega
                have d13397 : (x 2 2).toNat = 0 := by
                  have r13398 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e13399 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                  have e13400 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                  have b13401 := hb (x 1 3)
                  have b13402 := hb (x 2 2)
                  have b13403 := hb (x 3 13)
                  have b13404 := hb (x 4 12)
                  clear * - r13398 e13399 e13400 b13401 b13402 b13403 b13404 d13227 d13231 f12484
                  omega
                have d13405 : (x 4 13).toNat = 1 := by
                  have r13406 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b13407 := hb (x 2 2)
                  have b13408 := hb (x 4 13)
                  have b13409 := hb (x 3 1 && x 3 14)
                  clear * - r13406 b13407 b13408 b13409 d13263 d13397
                  omega
                have d13410 : (x 5 12).toNat = 0 := by
                  have r13411 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e13412 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                  have e13413 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                  have b13414 := hb (x 2 3)
                  have b13415 := hb (x 3 2)
                  have b13416 := hb (x 4 13)
                  have b13417 := hb (x 5 12)
                  clear * - r13411 e13412 e13413 b13414 b13415 b13416 b13417 d13405 d13312
                  omega
                have d13418 : (x 5 3 && x 5 12).toNat = 0 := by
                  have r13419 := hand2 (x 5 3) (x 5 12)
                  have b13420 := hb (x 5 12)
                  have b13421 := hb (x 5 3 && x 5 12)
                  clear * - r13419 b13420 b13421 d13410
                  omega
                have d13422 : (x 5 4).toNat = 0 := by
                  have r13423 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
                  have b13424 := hb (x 5 4)
                  have b13425 := hb (x 5 12)
                  clear * - r13423 b13424 b13425 d13410
                  omega
                have d13426 : (x 5 4 && x 5 11).toNat = 0 := by
                  have r13427 := hand1 (x 5 4) (x 5 11)
                  have b13428 := hb (x 5 4)
                  have b13429 := hb (x 5 4 && x 5 11)
                  clear * - r13427 b13428 b13429 d13422
                  omega
                have d13430 : (x 4 4).toNat = 0 := by
                  have r13431 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e13432 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                  have e13433 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                  have e13434 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                  have e13435 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                  have e13436 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                  have e13437 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                  have b13438 := hb (x 1 7)
                  have b13439 := hb (x 2 6)
                  have b13440 := hb (x 3 5)
                  have b13441 := hb (x 4 4)
                  have b13442 := hb (x 5 11)
                  have b13443 := hb (x 6 10)
                  have b13444 := hb (x 7 9)
                  have b13445 := hb (x 8 8)
                  clear * - r13431 e13432 e13433 e13434 e13435 e13436 e13437 b13438 b13439 b13440 b13441 b13442 b13443 b13444 b13445 d13118 d13142 d13166 d13194 d13287 f13117
                  omega
                have d13446 : (x 4 4 && x 4 13).toNat = 0 := by
                  have r13447 := hand1 (x 4 4) (x 4 13)
                  have b13448 := hb (x 4 4)
                  have b13449 := hb (x 4 4 && x 4 13)
                  clear * - r13447 b13448 b13449 d13430
                  omega
                have d13450 : (x 8 11).toNat = 1 := by
                  have r13451 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b13452 := hb (x 4 4)
                  have b13453 := hb (x 8 11)
                  have b13454 := hb (x 7 1 && x 7 12)
                  have b13455 := hb (x 6 2 && x 6 13)
                  have b13456 := hb (x 5 3 && x 5 14)
                  clear * - r13451 b13452 b13453 b13454 b13455 b13456 d13373 d13389 d13329 d13430
                  omega
                have d13457 : (x 8 3).toNat = 1 := by
                  have r13458 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
                  have b13459 := hb (x 8 3)
                  have b13460 := hb (x 8 11)
                  clear * - r13458 b13459 b13460 d13450
                  omega
                have d13461 : (x 11 12).toNat = 0 := by
                  have r13462 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e13463 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                  have e13464 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                  have b13465 := hb (x 8 3)
                  have b13466 := hb (x 9 2)
                  have b13467 := hb (x 10 13)
                  have b13468 := hb (x 11 12)
                  clear * - r13462 e13463 e13464 b13465 b13466 b13467 b13468 d13457
                  omega
                have d13469 : (x 10 13).toNat = 0 := by
                  have r13470 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e13471 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                  have e13472 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                  have b13473 := hb (x 8 3)
                  have b13474 := hb (x 9 2)
                  have b13475 := hb (x 10 13)
                  have b13476 := hb (x 11 12)
                  clear * - r13470 e13471 e13472 b13473 b13474 b13475 b13476 d13461 d13457
                  omega
                have d13477 : (x 9 2).toNat = 0 := by
                  have r13478 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e13479 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                  have e13480 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                  have b13481 := hb (x 8 3)
                  have b13482 := hb (x 9 2)
                  have b13483 := hb (x 10 13)
                  have b13484 := hb (x 11 12)
                  clear * - r13478 e13479 e13480 b13481 b13482 b13483 b13484 d13461 d13469 d13457
                  omega
                have d13485 : (x 9 2 && x 9 7).toNat = 0 := by
                  have r13486 := hand1 (x 9 2) (x 9 7)
                  have b13487 := hb (x 9 2)
                  have b13488 := hb (x 9 2 && x 9 7)
                  clear * - r13486 b13487 b13488 d13477
                  omega
                have d13489 : (x 9 10).toNat = 0 := by
                  have r13490 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
                  have b13491 := hb (x 9 2)
                  have b13492 := hb (x 9 10)
                  clear * - r13490 b13491 b13492 d13477
                  omega
                have d13493 : (x 11 8).toNat = 0 := by
                  have r13494 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e13495 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
                  have e13496 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
                  have e13497 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
                  have e13498 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
                  have e13499 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
                  have e13500 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
                  have b13501 := hb (x 4 7)
                  have b13502 := hb (x 5 6)
                  have b13503 := hb (x 6 5)
                  have b13504 := hb (x 7 4)
                  have b13505 := hb (x 8 11)
                  have b13506 := hb (x 9 10)
                  have b13507 := hb (x 10 9)
                  have b13508 := hb (x 11 8)
                  clear * - r13494 e13495 e13496 e13497 e13498 e13499 e13500 b13501 b13502 b13503 b13504 b13505 b13506 b13507 b13508 d13489 d13450 d13377 d13393 d13333
                  omega
                have d13509 : (x 10 9).toNat = 0 := by
                  have r13510 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e13511 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
                  have e13512 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
                  have e13513 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
                  have e13514 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
                  have e13515 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
                  have e13516 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
                  have b13517 := hb (x 4 7)
                  have b13518 := hb (x 5 6)
                  have b13519 := hb (x 6 5)
                  have b13520 := hb (x 7 4)
                  have b13521 := hb (x 8 11)
                  have b13522 := hb (x 9 10)
                  have b13523 := hb (x 10 9)
                  have b13524 := hb (x 11 8)
                  clear * - r13510 e13511 e13512 e13513 e13514 e13515 e13516 b13517 b13518 b13519 b13520 b13521 b13522 b13523 b13524 d13493 d13489 d13450 d13377 d13393 d13333
                  omega
                have d13525 : (x 4 7).toNat = 0 := by
                  have r13526 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e13527 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
                  have e13528 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
                  have e13529 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
                  have e13530 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
                  have e13531 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
                  have e13532 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
                  have b13533 := hb (x 4 7)
                  have b13534 := hb (x 5 6)
                  have b13535 := hb (x 6 5)
                  have b13536 := hb (x 7 4)
                  have b13537 := hb (x 8 11)
                  have b13538 := hb (x 9 10)
                  have b13539 := hb (x 10 9)
                  have b13540 := hb (x 11 8)
                  clear * - r13526 e13527 e13528 e13529 e13530 e13531 e13532 b13533 b13534 b13535 b13536 b13537 b13538 b13539 b13540 d13493 d13509 d13489 d13450 d13377 d13393 d13333
                  omega
                have d13541 : (x 4 7 && x 4 12).toNat = 0 := by
                  have r13542 := hand1 (x 4 7) (x 4 12)
                  have b13543 := hb (x 4 7)
                  have b13544 := hb (x 4 7 && x 4 12)
                  clear * - r13542 b13543 b13544 d13525
                  omega
                have d13545 : (x 2 6).toNat = 0 := by
                  have r13546 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e13547 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                  have e13548 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                  have e13549 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                  have e13550 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                  have e13551 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                  have e13552 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                  have b13553 := hb (x 1 7)
                  have b13554 := hb (x 2 6)
                  have b13555 := hb (x 3 5)
                  have b13556 := hb (x 4 4)
                  have b13557 := hb (x 5 11)
                  have b13558 := hb (x 6 10)
                  have b13559 := hb (x 7 9)
                  have b13560 := hb (x 8 8)
                  clear * - r13546 e13547 e13548 e13549 e13550 e13551 e13552 b13553 b13554 b13555 b13556 b13557 b13558 b13559 b13560 d13118 d13142 d13166 d13194 d13430 d13287 f13117
                  omega
                have r13561 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e13562 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                have e13563 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                have e13564 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                have e13565 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                have e13566 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                have e13567 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                have r13568 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e13569 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
                have e13570 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
                have e13571 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
                have e13572 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
                have e13573 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
                have e13574 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
                have r13575 : 1 ≤ (x 11 5).toNat + (x 10 1 && x 10 6).toNat + (x 9 2 && x 9 7).toNat + (x 8 3 && x 8 8).toNat + (x 7 4 && x 7 9).toNat + (x 6 5 && x 6 10).toNat + (x 5 6 && x 5 11).toNat + (x 4 7 && x 4 12).toNat + (x 3 8 && x 3 13).toNat + (x 2 9 && x 2 14).toNat + (x 1 10).toNat := by have q := hcov5 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r13576 : 1 ≤ (x 9 7).toNat + (x 8 1 && x 8 8).toNat + (x 7 2 && x 7 9).toNat + (x 6 3 && x 6 10).toNat + (x 5 4 && x 5 11).toNat + (x 4 5 && x 4 12).toNat + (x 3 6 && x 3 13).toNat + (x 2 7 && x 2 14).toNat + (x 1 8).toNat := by have q := hcov7 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r13577 : 1 ≤ (x 8 9).toNat + (x 7 1 && x 7 10).toNat + (x 6 2 && x 6 11).toNat + (x 5 3 && x 5 12).toNat + (x 4 4 && x 4 13).toNat + (x 3 5 && x 3 14).toNat + (x 2 6).toNat := by have q := hcov9 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r13578 := hand2 (x 10 1) (x 10 6)
                have r13579 := hand1 (x 4 5) (x 4 12)
                have r13580 := hand1 (x 2 7) (x 2 14)
                have r13581 := hand2 (x 7 1) (x 7 10)
                have r13582 := hand2 (x 6 2) (x 6 11)
                linarith only [r13561, e13562, e13563, e13564, e13565, e13566, e13567, r13568, e13569, e13570, e13571, e13572, e13573, e13574, r13575, r13576, r13577, r13578, r13579, r13580, r13581, r13582, g15, g16, d13545, d13308, d13422, d13485, d13138, d13162, d13190, d13337, d13541, d12045, d12065, d13134, d13158, d13186, d13426, d13283, d13418, d13446, d13291]
            · have f13623 : (x (-1) 6).toNat = 1 := by rw [h12485]; rfl
              have d13624 : (x (-1) 14).toNat = 1 := by
                have r13625 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
                have b13626 := hb (x (-1) 6)
                have b13627 := hb (x (-1) 14)
                clear * - r13625 b13626 b13627 f13623
                omega
              have d13628 : (x (-2) 1).toNat = 0 := by
                have r13629 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b13630 := hb (x (-2) 1)
                have b13631 := hb (x (-1) 14)
                clear * - r13629 b13630 b13631 d13624
                omega
              have d13632 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
                have r13633 := hand1 (x (-2) 1) (x (-2) 14)
                have b13634 := hb (x (-2) 1)
                have b13635 := hb (x (-2) 1 && x (-2) 14)
                clear * - r13633 b13634 b13635 d13628
                omega
              have d13636 : (x (-2) 13).toNat = 0 := by
                have r13637 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
                have b13638 := hb (x (-2) 1)
                have b13639 := hb (x (-2) 13)
                clear * - r13637 b13638 b13639 d13628
                omega
              have d13640 : (x (-2) 9 && x (-2) 13).toNat = 0 := by
                have r13641 := hand2 (x (-2) 9) (x (-2) 13)
                have b13642 := hb (x (-2) 13)
                have b13643 := hb (x (-2) 9 && x (-2) 13)
                clear * - r13641 b13642 b13643 d13636
                omega
              have d13644 : (x (-2) 9).toNat = 0 := by
                have r13645 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
                have b13646 := hb (x (-2) 1)
                have b13647 := hb (x (-2) 9)
                clear * - r13645 b13646 b13647 d13628
                omega
              have d13648 : (x (-3) 2).toNat = 1 := by
                have r13649 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b13650 := hb (x (-3) 2)
                have b13651 := hb (x (-1) 13)
                have b13652 := hb (x (-2) 1 && x (-2) 14)
                clear * - r13649 b13650 b13651 b13652 g7 d13632
                omega
              have d13653 : (x (-3) 14).toNat = 1 := by
                have r13654 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
                have b13655 := hb (x (-3) 2)
                have b13656 := hb (x (-3) 14)
                clear * - r13654 b13655 b13656 d13648
                omega
              have d13657 : (x (-1) 12).toNat = 0 := by
                have r13658 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e13659 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                have e13660 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                have b13661 := hb (x (-4) 3)
                have b13662 := hb (x (-3) 2)
                have b13663 := hb (x (-2) 13)
                have b13664 := hb (x (-1) 12)
                clear * - r13658 e13659 e13660 b13661 b13662 b13663 b13664 d13636 d13648
                omega
              have d13665 : (x (-1) 8 && x (-1) 12).toNat = 0 := by
                have r13666 := hand2 (x (-1) 8) (x (-1) 12)
                have b13667 := hb (x (-1) 12)
                have b13668 := hb (x (-1) 8 && x (-1) 12)
                clear * - r13666 b13667 b13668 d13657
                omega
              have d13669 : (x (-4) 3).toNat = 0 := by
                have r13670 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e13671 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                have e13672 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                have b13673 := hb (x (-4) 3)
                have b13674 := hb (x (-3) 2)
                have b13675 := hb (x (-2) 13)
                have b13676 := hb (x (-1) 12)
                clear * - r13670 e13671 e13672 b13673 b13674 b13675 b13676 d13657 d13636 d13648
                omega
              have d13677 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
                have r13678 := hand1 (x (-4) 3) (x (-4) 12)
                have b13679 := hb (x (-4) 3)
                have b13680 := hb (x (-4) 3 && x (-4) 12)
                clear * - r13678 b13679 b13680 d13669
                omega
              have d13681 : (x (-4) 11).toNat = 0 := by
                have r13682 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
                have b13683 := hb (x (-4) 3)
                have b13684 := hb (x (-4) 11)
                clear * - r13682 b13683 b13684 d13669
                omega
              have d13685 : (x 5 8).toNat = 0 := by
                have r13686 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e13687 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                have e13688 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                have e13689 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                have e13690 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                have e13691 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                have e13692 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                have b13693 := hb (x (-2) 7)
                have b13694 := hb (x (-1) 6)
                have b13695 := hb (x 0 5)
                have b13696 := hb (x 1 4)
                have b13697 := hb (x 2 11)
                have b13698 := hb (x 3 10)
                have b13699 := hb (x 4 9)
                have b13700 := hb (x 5 8)
                clear * - r13686 e13687 e13688 e13689 e13690 e13691 e13692 b13693 b13694 b13695 b13696 b13697 b13698 b13699 b13700 d11845 g9 f13623
                omega
              have d13701 : (x 5 3 && x 5 8).toNat = 0 := by
                have r13702 := hand2 (x 5 3) (x 5 8)
                have b13703 := hb (x 5 8)
                have b13704 := hb (x 5 3 && x 5 8)
                clear * - r13702 b13703 b13704 d13685
                omega
              have d13705 : (x 4 9).toNat = 0 := by
                have r13706 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e13707 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                have e13708 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                have e13709 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                have e13710 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                have e13711 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                have e13712 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                have b13713 := hb (x (-2) 7)
                have b13714 := hb (x (-1) 6)
                have b13715 := hb (x 0 5)
                have b13716 := hb (x 1 4)
                have b13717 := hb (x 2 11)
                have b13718 := hb (x 3 10)
                have b13719 := hb (x 4 9)
                have b13720 := hb (x 5 8)
                clear * - r13706 e13707 e13708 e13709 e13710 e13711 e13712 b13713 b13714 b13715 b13716 b13717 b13718 b13719 b13720 d13685 d11845 g9 f13623
                omega
              have d13721 : (x 4 4 && x 4 9).toNat = 0 := by
                have r13722 := hand2 (x 4 4) (x 4 9)
                have b13723 := hb (x 4 9)
                have b13724 := hb (x 4 4 && x 4 9)
                clear * - r13722 b13723 b13724 d13705
                omega
              have d13725 : (x 3 10).toNat = 0 := by
                have r13726 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e13727 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                have e13728 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                have e13729 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                have e13730 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                have e13731 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                have e13732 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                have b13733 := hb (x (-2) 7)
                have b13734 := hb (x (-1) 6)
                have b13735 := hb (x 0 5)
                have b13736 := hb (x 1 4)
                have b13737 := hb (x 2 11)
                have b13738 := hb (x 3 10)
                have b13739 := hb (x 4 9)
                have b13740 := hb (x 5 8)
                clear * - r13726 e13727 e13728 e13729 e13730 e13731 e13732 b13733 b13734 b13735 b13736 b13737 b13738 b13739 b13740 d13685 d13705 d11845 g9 f13623
                omega
              have d13741 : (x 3 5 && x 3 10).toNat = 0 := by
                have r13742 := hand2 (x 3 5) (x 3 10)
                have b13743 := hb (x 3 10)
                have b13744 := hb (x 3 5 && x 3 10)
                clear * - r13742 b13743 b13744 d13725
                omega
              have d13745 : (x 2 11).toNat = 0 := by
                have r13746 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e13747 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                have e13748 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                have e13749 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                have e13750 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                have e13751 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                have e13752 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                have b13753 := hb (x (-2) 7)
                have b13754 := hb (x (-1) 6)
                have b13755 := hb (x 0 5)
                have b13756 := hb (x 1 4)
                have b13757 := hb (x 2 11)
                have b13758 := hb (x 3 10)
                have b13759 := hb (x 4 9)
                have b13760 := hb (x 5 8)
                clear * - r13746 e13747 e13748 e13749 e13750 e13751 e13752 b13753 b13754 b13755 b13756 b13757 b13758 b13759 b13760 d13685 d13705 d13725 d11845 g9 f13623
                omega
              have d13761 : (x 2 6 && x 2 11).toNat = 0 := by
                have r13762 := hand2 (x 2 6) (x 2 11)
                have b13763 := hb (x 2 11)
                have b13764 := hb (x 2 6 && x 2 11)
                clear * - r13762 b13763 b13764 d13745
                omega
              have r13765 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r13766 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e13767 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e13768 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e13769 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e13770 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e13771 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e13772 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have r13773 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e13774 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
              have e13775 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
              have e13776 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
              have e13777 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
              have e13778 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
              have e13779 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
              have r13780 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e13781 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
              have e13782 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
              have r13783 : 1 ≤ (x 7 4).toNat + (x 6 1 && x 6 5).toNat + (x 5 2 && x 5 6).toNat + (x 4 3 && x 4 7).toNat + (x 3 4 && x 3 8).toNat + (x 2 5 && x 2 9).toNat + (x 1 6 && x 1 10).toNat + (x 0 7 && x 0 11).toNat + (x (-1) 8 && x (-1) 12).toNat + (x (-2) 9 && x (-2) 13).toNat + (x (-3) 10 && x (-3) 14).toNat + (x (-4) 11).toNat := by have q := hcov4 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e13784 : (x 6 1 && x 6 5).toNat = (x 6 5).toNat := handr _ _ (fun h => hp13 6 (hp5 6 (h)))
              have e13785 : (x (-3) 10 && x (-3) 14).toNat = (x (-3) 10).toNat := handl _ _ (fun h => hp2 (-3) (hp10 (-3) (h)))
              have r13786 : 1 ≤ (x 8 5).toNat + (x 7 1 && x 7 6).toNat + (x 6 2 && x 6 7).toNat + (x 5 3 && x 5 8).toNat + (x 4 4 && x 4 9).toNat + (x 3 5 && x 3 10).toNat + (x 2 6 && x 2 11).toNat + (x 1 7 && x 1 12).toNat + (x 0 8 && x 0 13).toNat + (x (-1) 9 && x (-1) 14).toNat + (x (-2) 10).toNat := by have q := hcov5 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r13787 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r13788 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r13789 : 1 ≤ (x 11 10).toNat + (x 10 1 && x 10 11).toNat + (x 9 2 && x 9 12).toNat + (x 8 3 && x 8 13).toNat + (x 7 4 && x 7 14).toNat + (x 6 5).toNat := by have q := hcov10 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r13790 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
              have r13791 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
              have r13792 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
              have r13793 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
              have r13794 := hand2 (x 5 2) (x 5 6)
              have r13795 := hand2 (x 4 3) (x 4 7)
              have r13796 := hand2 (x 7 1) (x 7 6)
              have r13797 := hand2 (x 6 2) (x 6 7)
              have r13798 := hand1 (x (-5) 4) (x (-5) 13)
              have r13799 := hand1 (x (-6) 5) (x (-6) 14)
              have r13800 := hand2 (x 4 1) (x 4 11)
              have r13801 := hand1 (x 10 1) (x 10 11)
              have r13802 := hand1 (x 9 2) (x 9 12)
              have r13803 := hand1 (x 8 3) (x 8 13)
              have r13804 := hand1 (x 7 4) (x 7 14)
              linarith only [r13765, r13766, e13767, e13768, e13769, e13770, e13771, e13772, r13773, e13774, e13775, e13776, e13777, e13778, e13779, r13780, e13781, e13782, r13783, e13784, e13785, r13786, r13787, r13788, r13789, r13790, r13791, r13792, r13793, r13794, r13795, r13796, r13797, r13798, r13799, r13800, r13801, r13802, r13803, r13804, d13681, d13653, d13644, d11812, d13636, g4, d13657, g9, d11929, g16, d12049, d12029, g30, g31, g32, d12089, d13665, d13640, d13701, d13721, d13741, d13761, d11841, g37, g38, d11816, d11913, d13677, g65, g66, g67]
          · have f13874 : (x 1 3).toNat = 1 := by rw [h12483]; rfl
            have d13875 : (x 4 12).toNat = 0 := by
              have r13876 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e13877 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e13878 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b13879 := hb (x 1 3)
              have b13880 := hb (x 2 2)
              have b13881 := hb (x 3 13)
              have b13882 := hb (x 4 12)
              clear * - r13876 e13877 e13878 b13879 b13880 b13881 b13882 f13874
              omega
            have d13883 : (x 4 1 && x 4 12).toNat = 0 := by
              have r13884 := hand2 (x 4 1) (x 4 12)
              have b13885 := hb (x 4 12)
              have b13886 := hb (x 4 1 && x 4 12)
              clear * - r13884 b13885 b13886 d13875
              omega
            have d13887 : (x 4 4).toNat = 0 := by
              have r13888 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
              have b13889 := hb (x 4 4)
              have b13890 := hb (x 4 12)
              clear * - r13888 b13889 b13890 d13875
              omega
            have d13891 : (x 3 13).toNat = 0 := by
              have r13892 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e13893 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e13894 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b13895 := hb (x 1 3)
              have b13896 := hb (x 2 2)
              have b13897 := hb (x 3 13)
              have b13898 := hb (x 4 12)
              clear * - r13892 e13893 e13894 b13895 b13896 b13897 b13898 d13875 f13874
              omega
            have d13899 : (x 3 2 && x 3 13).toNat = 0 := by
              have r13900 := hand2 (x 3 2) (x 3 13)
              have b13901 := hb (x 3 13)
              have b13902 := hb (x 3 2 && x 3 13)
              clear * - r13900 b13901 b13902 d13891
              omega
            have d13903 : (x 2 1 && x 2 14).toNat = 1 := by
              have r13904 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b13905 := hb (x 1 2)
              have b13906 := hb (x 3 13)
              have b13907 := hb (x 2 1 && x 2 14)
              clear * - r13904 b13905 b13906 b13907 d13891 g12
              omega
            have d13908 : (x 2 1).toNat = 1 := by
              have r13909 := hand1 (x 2 1) (x 2 14)
              have b13910 := hb (x 2 1)
              have b13911 := hb (x 2 1 && x 2 14)
              clear * - r13909 b13910 b13911 d13903
              omega
            have d13912 : (x 3 14).toNat = 0 := by
              have r13913 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b13914 := hb (x 2 1)
              have b13915 := hb (x 3 14)
              clear * - r13913 b13914 b13915 d13908
              omega
            have d13916 : (x 3 1 && x 3 14).toNat = 0 := by
              have r13917 := hand2 (x 3 1) (x 3 14)
              have b13918 := hb (x 3 14)
              have b13919 := hb (x 3 1 && x 3 14)
              clear * - r13917 b13918 b13919 d13912
              omega
            have d13920 : (x 3 2).toNat = 0 := by
              have r13921 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
              have b13922 := hb (x 3 2)
              have b13923 := hb (x 3 14)
              clear * - r13921 b13922 b13923 d13912
              omega
            have d13924 : (x 2 2).toNat = 0 := by
              have r13925 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e13926 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e13927 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b13928 := hb (x 1 3)
              have b13929 := hb (x 2 2)
              have b13930 := hb (x 3 13)
              have b13931 := hb (x 4 12)
              clear * - r13925 e13926 e13927 b13928 b13929 b13930 b13931 d13875 d13891 f13874
              omega
            have d13932 : (x 4 13).toNat = 1 := by
              have r13933 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b13934 := hb (x 2 2)
              have b13935 := hb (x 4 13)
              have b13936 := hb (x 3 1 && x 3 14)
              clear * - r13933 b13934 b13935 b13936 d13916 d13924
              omega
            have d13937 : (x 4 1).toNat = 1 := by
              have r13938 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
              have b13939 := hb (x 4 1)
              have b13940 := hb (x 4 13)
              clear * - r13938 b13939 b13940 d13932
              omega
            have d13941 : (x 5 14).toNat = 0 := by
              have r13942 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b13943 := hb (x 4 1)
              have b13944 := hb (x 5 14)
              clear * - r13942 b13943 b13944 d13937
              omega
            have d13945 : (x 5 3 && x 5 14).toNat = 0 := by
              have r13946 := hand2 (x 5 3) (x 5 14)
              have b13947 := hb (x 5 14)
              have b13948 := hb (x 5 3 && x 5 14)
              clear * - r13946 b13947 b13948 d13941
              omega
            have d13949 : (x 5 2).toNat = 0 := by
              have r13950 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
              have b13951 := hb (x 5 2)
              have b13952 := hb (x 5 14)
              clear * - r13950 b13951 b13952 d13941
              omega
            have d13953 : (x 5 12).toNat = 0 := by
              have r13954 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e13955 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
              have e13956 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
              have b13957 := hb (x 2 3)
              have b13958 := hb (x 3 2)
              have b13959 := hb (x 4 13)
              have b13960 := hb (x 5 12)
              clear * - r13954 e13955 e13956 b13957 b13958 b13959 b13960 d13932 d13920
              omega
            have d13961 : (x 5 4).toNat = 0 := by
              have r13962 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
              have b13963 := hb (x 5 4)
              have b13964 := hb (x 5 12)
              clear * - r13962 b13963 b13964 d13953
              omega
            have d13965 : (x 2 3).toNat = 0 := by
              have r13966 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e13967 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
              have e13968 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
              have b13969 := hb (x 2 3)
              have b13970 := hb (x 3 2)
              have b13971 := hb (x 4 13)
              have b13972 := hb (x 5 12)
              clear * - r13966 e13967 e13968 b13969 b13970 b13971 b13972 d13953 d13932 d13920
              omega
            have d13973 : (x 2 3 && x 2 14).toNat = 0 := by
              have r13974 := hand1 (x 2 3) (x 2 14)
              have b13975 := hb (x 2 3)
              have b13976 := hb (x 2 3 && x 2 14)
              clear * - r13974 b13975 b13976 d13965
              omega
            have d13977 : (x 5 11).toNat = 1 := by
              have r13978 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b13979 := hb (x 1 4)
              have b13980 := hb (x 5 11)
              have b13981 := hb (x 4 1 && x 4 12)
              have b13982 := hb (x 3 2 && x 3 13)
              have b13983 := hb (x 2 3 && x 2 14)
              clear * - r13978 b13979 b13980 b13981 b13982 b13983 d13883 d13899 d13973 d11845
              omega
            have d13984 : (x 5 3).toNat = 1 := by
              have r13985 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
              have b13986 := hb (x 5 3)
              have b13987 := hb (x 5 11)
              clear * - r13985 b13986 b13987 d13977
              omega
            have d13988 : (x 8 12).toNat = 0 := by
              have r13989 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e13990 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
              have e13991 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
              have b13992 := hb (x 5 3)
              have b13993 := hb (x 6 2)
              have b13994 := hb (x 7 13)
              have b13995 := hb (x 8 12)
              clear * - r13989 e13990 e13991 b13992 b13993 b13994 b13995 d13984
              omega
            have d13996 : (x 8 1 && x 8 12).toNat = 0 := by
              have r13997 := hand2 (x 8 1) (x 8 12)
              have b13998 := hb (x 8 12)
              have b13999 := hb (x 8 1 && x 8 12)
              clear * - r13997 b13998 b13999 d13988
              omega
            have d14000 : (x 8 4).toNat = 0 := by
              have r14001 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
              have b14002 := hb (x 8 4)
              have b14003 := hb (x 8 12)
              clear * - r14001 b14002 b14003 d13988
              omega
            have d14004 : (x 7 13).toNat = 0 := by
              have r14005 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e14006 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
              have e14007 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
              have b14008 := hb (x 5 3)
              have b14009 := hb (x 6 2)
              have b14010 := hb (x 7 13)
              have b14011 := hb (x 8 12)
              clear * - r14005 e14006 e14007 b14008 b14009 b14010 b14011 d13988 d13984
              omega
            have d14012 : (x 7 2 && x 7 13).toNat = 0 := by
              have r14013 := hand2 (x 7 2) (x 7 13)
              have b14014 := hb (x 7 13)
              have b14015 := hb (x 7 2 && x 7 13)
              clear * - r14013 b14014 b14015 d14004
              omega
            have d14016 : (x 6 1 && x 6 14).toNat = 1 := by
              have r14017 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b14018 := hb (x 5 2)
              have b14019 := hb (x 7 13)
              have b14020 := hb (x 6 1 && x 6 14)
              clear * - r14017 b14018 b14019 b14020 d14004 d13949
              omega
            have d14021 : (x 6 1).toNat = 1 := by
              have r14022 := hand1 (x 6 1) (x 6 14)
              have b14023 := hb (x 6 1)
              have b14024 := hb (x 6 1 && x 6 14)
              clear * - r14022 b14023 b14024 d14016
              omega
            have d14025 : (x 7 14).toNat = 0 := by
              have r14026 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b14027 := hb (x 6 1)
              have b14028 := hb (x 7 14)
              clear * - r14026 b14027 b14028 d14021
              omega
            have d14029 : (x 7 1 && x 7 14).toNat = 0 := by
              have r14030 := hand2 (x 7 1) (x 7 14)
              have b14031 := hb (x 7 14)
              have b14032 := hb (x 7 1 && x 7 14)
              clear * - r14030 b14031 b14032 d14025
              omega
            have d14033 : (x 7 2).toNat = 0 := by
              have r14034 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
              have b14035 := hb (x 7 2)
              have b14036 := hb (x 7 14)
              clear * - r14034 b14035 b14036 d14025
              omega
            have d14037 : (x 6 2).toNat = 0 := by
              have r14038 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e14039 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
              have e14040 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
              have b14041 := hb (x 5 3)
              have b14042 := hb (x 6 2)
              have b14043 := hb (x 7 13)
              have b14044 := hb (x 8 12)
              clear * - r14038 e14039 e14040 b14041 b14042 b14043 b14044 d13988 d14004 d13984
              omega
            have d14045 : (x 6 2 && x 6 13).toNat = 0 := by
              have r14046 := hand1 (x 6 2) (x 6 13)
              have b14047 := hb (x 6 2)
              have b14048 := hb (x 6 2 && x 6 13)
              clear * - r14046 b14047 b14048 d14037
              omega
            have d14049 : (x 8 13).toNat = 1 := by
              have r14050 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b14051 := hb (x 6 2)
              have b14052 := hb (x 8 13)
              have b14053 := hb (x 7 1 && x 7 14)
              clear * - r14050 b14051 b14052 b14053 d14029 d14037
              omega
            have d14054 : (x 8 1).toNat = 1 := by
              have r14055 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
              have b14056 := hb (x 8 1)
              have b14057 := hb (x 8 13)
              clear * - r14055 b14056 b14057 d14049
              omega
            have d14058 : (x 9 14).toNat = 0 := by
              have r14059 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b14060 := hb (x 8 1)
              have b14061 := hb (x 9 14)
              clear * - r14059 b14060 b14061 d14054
              omega
            have d14062 : (x 9 3 && x 9 14).toNat = 0 := by
              have r14063 := hand2 (x 9 3) (x 9 14)
              have b14064 := hb (x 9 14)
              have b14065 := hb (x 9 3 && x 9 14)
              clear * - r14063 b14064 b14065 d14058
              omega
            have d14066 : (x 9 2).toNat = 0 := by
              have r14067 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
              have b14068 := hb (x 9 2)
              have b14069 := hb (x 9 14)
              clear * - r14067 b14068 b14069 d14058
              omega
            have d14070 : (x 9 12).toNat = 0 := by
              have r14071 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e14072 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
              have e14073 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
              have b14074 := hb (x 6 3)
              have b14075 := hb (x 7 2)
              have b14076 := hb (x 8 13)
              have b14077 := hb (x 9 12)
              clear * - r14071 e14072 e14073 b14074 b14075 b14076 b14077 d14049 d14033
              omega
            have d14078 : (x 9 4).toNat = 0 := by
              have r14079 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
              have b14080 := hb (x 9 4)
              have b14081 := hb (x 9 12)
              clear * - r14079 b14080 b14081 d14070
              omega
            have d14082 : (x 6 3).toNat = 0 := by
              have r14083 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e14084 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
              have e14085 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
              have b14086 := hb (x 6 3)
              have b14087 := hb (x 7 2)
              have b14088 := hb (x 8 13)
              have b14089 := hb (x 9 12)
              clear * - r14083 e14084 e14085 b14086 b14087 b14088 b14089 d14070 d14049 d14033
              omega
            have d14090 : (x 6 3 && x 6 14).toNat = 0 := by
              have r14091 := hand1 (x 6 3) (x 6 14)
              have b14092 := hb (x 6 3)
              have b14093 := hb (x 6 3 && x 6 14)
              clear * - r14091 b14092 b14093 d14082
              omega
            have d14094 : (x 9 11).toNat = 1 := by
              have r14095 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b14096 := hb (x 5 4)
              have b14097 := hb (x 9 11)
              have b14098 := hb (x 8 1 && x 8 12)
              have b14099 := hb (x 7 2 && x 7 13)
              have b14100 := hb (x 6 3 && x 6 14)
              clear * - r14095 b14096 b14097 b14098 b14099 b14100 d13996 d14012 d14090 d13961
              omega
            have d14101 : (x 9 3).toNat = 1 := by
              have r14102 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
              have b14103 := hb (x 9 3)
              have b14104 := hb (x 9 11)
              clear * - r14102 b14103 b14104 d14094
              omega
            have d14105 : (x 12 12).toNat = 0 := by
              have r14106 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e14107 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
              have e14108 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
              have b14109 := hb (x 9 3)
              have b14110 := hb (x 10 2)
              have b14111 := hb (x 11 13)
              have b14112 := hb (x 12 12)
              clear * - r14106 e14107 e14108 b14109 b14110 b14111 b14112 d14101
              omega
            have d14113 : (x 12 1 && x 12 12).toNat = 0 := by
              have r14114 := hand2 (x 12 1) (x 12 12)
              have b14115 := hb (x 12 12)
              have b14116 := hb (x 12 1 && x 12 12)
              clear * - r14114 b14115 b14116 d14105
              omega
            have d14117 : (x 12 4).toNat = 0 := by
              have r14118 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
              have b14119 := hb (x 12 4)
              have b14120 := hb (x 12 12)
              clear * - r14118 b14119 b14120 d14105
              omega
            have d14121 : (x 11 13).toNat = 0 := by
              have r14122 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e14123 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
              have e14124 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
              have b14125 := hb (x 9 3)
              have b14126 := hb (x 10 2)
              have b14127 := hb (x 11 13)
              have b14128 := hb (x 12 12)
              clear * - r14122 e14123 e14124 b14125 b14126 b14127 b14128 d14105 d14101
              omega
            have d14129 : (x 11 2 && x 11 13).toNat = 0 := by
              have r14130 := hand2 (x 11 2) (x 11 13)
              have b14131 := hb (x 11 13)
              have b14132 := hb (x 11 2 && x 11 13)
              clear * - r14130 b14131 b14132 d14121
              omega
            have d14133 : (x 10 1 && x 10 14).toNat = 1 := by
              have r14134 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b14135 := hb (x 9 2)
              have b14136 := hb (x 11 13)
              have b14137 := hb (x 10 1 && x 10 14)
              clear * - r14134 b14135 b14136 b14137 d14121 d14066
              omega
            have d14138 : (x 10 14).toNat = 1 := by
              have r14139 := hand2 (x 10 1) (x 10 14)
              have b14140 := hb (x 10 14)
              have b14141 := hb (x 10 1 && x 10 14)
              clear * - r14139 b14140 b14141 d14133
              omega
            have d14142 : (x 9 1).toNat = 0 := by
              have r14143 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b14144 := hb (x 9 1)
              have b14145 := hb (x 10 14)
              clear * - r14143 b14144 b14145 d14138
              omega
            have d14146 : (x 9 13).toNat = 0 := by
              have r14147 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
              have b14148 := hb (x 9 1)
              have b14149 := hb (x 9 13)
              clear * - r14147 b14148 b14149 d14142
              omega
            have d14150 : (x 8 1 && x 8 14).toNat = 1 := by
              have r14151 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b14152 := hb (x 7 2)
              have b14153 := hb (x 9 13)
              have b14154 := hb (x 8 1 && x 8 14)
              clear * - r14151 b14152 b14153 b14154 d14146 d14033
              omega
            have d14155 : (x 8 14).toNat = 1 := by
              have r14156 := hand2 (x 8 1) (x 8 14)
              have b14157 := hb (x 8 14)
              have b14158 := hb (x 8 1 && x 8 14)
              clear * - r14156 b14157 b14158 d14150
              omega
            have d14159 : (x 7 1).toNat = 0 := by
              have r14160 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b14161 := hb (x 7 1)
              have b14162 := hb (x 8 14)
              clear * - r14160 b14161 b14162 d14155
              omega
            have d14163 : (x 7 1 && x 7 12).toNat = 0 := by
              have r14164 := hand1 (x 7 1) (x 7 12)
              have b14165 := hb (x 7 1)
              have b14166 := hb (x 7 1 && x 7 12)
              clear * - r14164 b14165 b14166 d14159
              omega
            have d14167 : (x 8 11).toNat = 1 := by
              have r14168 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b14169 := hb (x 4 4)
              have b14170 := hb (x 8 11)
              have b14171 := hb (x 7 1 && x 7 12)
              have b14172 := hb (x 6 2 && x 6 13)
              have b14173 := hb (x 5 3 && x 5 14)
              clear * - r14168 b14169 b14170 b14171 b14172 b14173 d14163 d14045 d13945 d13887
              omega
            have d14174 : (x 8 3).toNat = 1 := by
              have r14175 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
              have b14176 := hb (x 8 3)
              have b14177 := hb (x 8 11)
              clear * - r14175 b14176 b14177 d14167
              omega
            have d14178 : (x 11 12).toNat = 0 := by
              have r14179 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e14180 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
              have e14181 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
              have b14182 := hb (x 8 3)
              have b14183 := hb (x 9 2)
              have b14184 := hb (x 10 13)
              have b14185 := hb (x 11 12)
              clear * - r14179 e14180 e14181 b14182 b14183 b14184 b14185 d14066 d14174
              omega
            have d14186 : (x 11 1 && x 11 12).toNat = 0 := by
              have r14187 := hand2 (x 11 1) (x 11 12)
              have b14188 := hb (x 11 12)
              have b14189 := hb (x 11 1 && x 11 12)
              clear * - r14187 b14188 b14189 d14178
              omega
            have d14190 : (x 10 13).toNat = 0 := by
              have r14191 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e14192 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
              have e14193 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
              have b14194 := hb (x 8 3)
              have b14195 := hb (x 9 2)
              have b14196 := hb (x 10 13)
              have b14197 := hb (x 11 12)
              clear * - r14191 e14192 e14193 b14194 b14195 b14196 b14197 d14178 d14066 d14174
              omega
            have d14198 : (x 10 2 && x 10 13).toNat = 0 := by
              have r14199 := hand2 (x 10 2) (x 10 13)
              have b14200 := hb (x 10 13)
              have b14201 := hb (x 10 2 && x 10 13)
              clear * - r14199 b14200 b14201 d14190
              omega
            have d14202 : (x 12 11).toNat = 1 := by
              have r14203 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b14204 := hb (x 8 4)
              have b14205 := hb (x 12 11)
              have b14206 := hb (x 11 1 && x 11 12)
              have b14207 := hb (x 10 2 && x 10 13)
              have b14208 := hb (x 9 3 && x 9 14)
              clear * - r14203 b14204 b14205 b14206 b14207 b14208 d14186 d14198 d14062 d14000
              omega
            have d14209 : (x 12 3).toNat = 1 := by
              have r14210 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
              have b14211 := hb (x 12 3)
              have b14212 := hb (x 12 11)
              clear * - r14210 b14211 b14212 d14202
              omega
            have d14213 : (x 15 12).toNat = 0 := by
              have r14214 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e14215 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
              have e14216 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
              have b14217 := hb (x 12 3)
              have b14218 := hb (x 13 2)
              have b14219 := hb (x 14 13)
              have b14220 := hb (x 15 12)
              clear * - r14214 e14215 e14216 b14217 b14218 b14219 b14220 d14209
              omega
            have d14221 : (x 15 1 && x 15 12).toNat = 0 := by
              have r14222 := hand2 (x 15 1) (x 15 12)
              have b14223 := hb (x 15 12)
              have b14224 := hb (x 15 1 && x 15 12)
              clear * - r14222 b14223 b14224 d14213
              omega
            have d14225 : (x 14 13).toNat = 0 := by
              have r14226 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e14227 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
              have e14228 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
              have b14229 := hb (x 12 3)
              have b14230 := hb (x 13 2)
              have b14231 := hb (x 14 13)
              have b14232 := hb (x 15 12)
              clear * - r14226 e14227 e14228 b14229 b14230 b14231 b14232 d14213 d14209
              omega
            have d14233 : (x 14 2 && x 14 13).toNat = 0 := by
              have r14234 := hand2 (x 14 2) (x 14 13)
              have b14235 := hb (x 14 13)
              have b14236 := hb (x 14 2 && x 14 13)
              clear * - r14234 b14235 b14236 d14225
              omega
            have d14237 : (x 13 2).toNat = 0 := by
              have r14238 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e14239 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
              have e14240 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
              have b14241 := hb (x 12 3)
              have b14242 := hb (x 13 2)
              have b14243 := hb (x 14 13)
              have b14244 := hb (x 15 12)
              clear * - r14238 e14239 e14240 b14241 b14242 b14243 b14244 d14213 d14225 d14209
              omega
            have d14245 : (x 10 1).toNat = 1 := by
              have r14246 := hand1 (x 10 1) (x 10 14)
              have b14247 := hb (x 10 1)
              have b14248 := hb (x 10 1 && x 10 14)
              clear * - r14246 b14247 b14248 d14133
              omega
            have d14249 : (x 11 14).toNat = 0 := by
              have r14250 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b14251 := hb (x 10 1)
              have b14252 := hb (x 11 14)
              clear * - r14250 b14251 b14252 d14245
              omega
            have d14253 : (x 11 1 && x 11 14).toNat = 0 := by
              have r14254 := hand2 (x 11 1) (x 11 14)
              have b14255 := hb (x 11 14)
              have b14256 := hb (x 11 1 && x 11 14)
              clear * - r14254 b14255 b14256 d14249
              omega
            have d14257 : (x 11 2).toNat = 0 := by
              have r14258 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
              have b14259 := hb (x 11 2)
              have b14260 := hb (x 11 14)
              clear * - r14258 b14259 b14260 d14249
              omega
            have d14261 : (x 10 2).toNat = 0 := by
              have r14262 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e14263 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
              have e14264 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
              have b14265 := hb (x 9 3)
              have b14266 := hb (x 10 2)
              have b14267 := hb (x 11 13)
              have b14268 := hb (x 12 12)
              clear * - r14262 e14263 e14264 b14265 b14266 b14267 b14268 d14105 d14121 d14101
              omega
            have d14269 : (x 12 13).toNat = 1 := by
              have r14270 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b14271 := hb (x 10 2)
              have b14272 := hb (x 12 13)
              have b14273 := hb (x 11 1 && x 11 14)
              clear * - r14270 b14271 b14272 b14273 d14253 d14261
              omega
            have d14274 : (x 12 1).toNat = 1 := by
              have r14275 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
              have b14276 := hb (x 12 1)
              have b14277 := hb (x 12 13)
              clear * - r14275 b14276 b14277 d14269
              omega
            have d14278 : (x 13 14).toNat = 0 := by
              have r14279 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b14280 := hb (x 12 1)
              have b14281 := hb (x 13 14)
              clear * - r14279 b14280 b14281 d14274
              omega
            have d14282 : (x 13 1 && x 13 14).toNat = 0 := by
              have r14283 := hand2 (x 13 1) (x 13 14)
              have b14284 := hb (x 13 14)
              have b14285 := hb (x 13 1 && x 13 14)
              clear * - r14283 b14284 b14285 d14278
              omega
            have d14286 : (x 12 2).toNat = 1 := by
              have r14287 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b14288 := hb (x 12 2)
              have b14289 := hb (x 14 13)
              have b14290 := hb (x 13 1 && x 13 14)
              clear * - r14287 b14288 b14289 b14290 d14225 d14282
              omega
            have d14291 : (x 14 12).toNat = 0 := by
              have r14292 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e14293 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
              have e14294 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
              have b14295 := hb (x 11 3)
              have b14296 := hb (x 12 2)
              have b14297 := hb (x 13 13)
              have b14298 := hb (x 14 12)
              clear * - r14292 e14293 e14294 b14295 b14296 b14297 b14298 d14286
              omega
            have d14299 : (x 14 4).toNat = 0 := by
              have r14300 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
              have b14301 := hb (x 14 4)
              have b14302 := hb (x 14 12)
              clear * - r14300 b14301 b14302 d14291
              omega
            have d14303 : (x 14 4 && x 14 14).toNat = 0 := by
              have r14304 := hand1 (x 14 4) (x 14 14)
              have b14305 := hb (x 14 4)
              have b14306 := hb (x 14 4 && x 14 14)
              clear * - r14304 b14305 b14306 d14299
              omega
            have d14307 : (x 13 13).toNat = 0 := by
              have r14308 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e14309 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
              have e14310 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
              have b14311 := hb (x 11 3)
              have b14312 := hb (x 12 2)
              have b14313 := hb (x 13 13)
              have b14314 := hb (x 14 12)
              clear * - r14308 e14309 e14310 b14311 b14312 b14313 b14314 d14291 d14286
              omega
            have d14315 : (x 13 5).toNat = 0 := by
              have r14316 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
              have b14317 := hb (x 13 5)
              have b14318 := hb (x 13 13)
              clear * - r14316 b14317 b14318 d14307
              omega
            have d14319 : (x 13 3 && x 13 14).toNat = 0 := by
              have r14320 := hand2 (x 13 3) (x 13 14)
              have b14321 := hb (x 13 14)
              have b14322 := hb (x 13 3 && x 13 14)
              clear * - r14320 b14321 b14322 d14278
              omega
            have d14323 : (x 16 11).toNat = 1 := by
              have r14324 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b14325 := hb (x 12 4)
              have b14326 := hb (x 16 11)
              have b14327 := hb (x 15 1 && x 15 12)
              have b14328 := hb (x 14 2 && x 14 13)
              have b14329 := hb (x 13 3 && x 13 14)
              clear * - r14324 b14325 b14326 b14327 b14328 b14329 d14221 d14233 d14319 d14117
              omega
            have d14330 : (x 16 3).toNat = 1 := by
              have r14331 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
              have b14332 := hb (x 16 3)
              have b14333 := hb (x 16 11)
              clear * - r14331 b14332 b14333 d14323
              omega
            have d14334 : (x 19 12).toNat = 0 := by
              have r14335 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e14336 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
              have e14337 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
              have b14338 := hb (x 16 3)
              have b14339 := hb (x 17 2)
              have b14340 := hb (x 18 13)
              have b14341 := hb (x 19 12)
              clear * - r14335 e14336 e14337 b14338 b14339 b14340 b14341 d14330
              omega
            have d14342 : (x 18 13).toNat = 0 := by
              have r14343 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e14344 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
              have e14345 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
              have b14346 := hb (x 16 3)
              have b14347 := hb (x 17 2)
              have b14348 := hb (x 18 13)
              have b14349 := hb (x 19 12)
              clear * - r14343 e14344 e14345 b14346 b14347 b14348 b14349 d14334 d14330
              omega
            have d14350 : (x 17 2).toNat = 0 := by
              have r14351 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e14352 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
              have e14353 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
              have b14354 := hb (x 16 3)
              have b14355 := hb (x 17 2)
              have b14356 := hb (x 18 13)
              have b14357 := hb (x 19 12)
              clear * - r14351 e14352 e14353 b14354 b14355 b14356 b14357 d14334 d14342 d14330
              omega
            have d14358 : (x 13 12).toNat = 0 := by
              have r14359 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e14360 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
              have e14361 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
              have b14362 := hb (x 10 3)
              have b14363 := hb (x 11 2)
              have b14364 := hb (x 12 13)
              have b14365 := hb (x 13 12)
              clear * - r14359 e14360 e14361 b14362 b14363 b14364 b14365 d14269 d14257
              omega
            have d14366 : (x 13 4).toNat = 0 := by
              have r14367 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
              have b14368 := hb (x 13 4)
              have b14369 := hb (x 13 12)
              clear * - r14367 b14368 b14369 d14358
              omega
            have d14370 : (x 10 3).toNat = 0 := by
              have r14371 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e14372 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
              have e14373 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
              have b14374 := hb (x 10 3)
              have b14375 := hb (x 11 2)
              have b14376 := hb (x 12 13)
              have b14377 := hb (x 13 12)
              clear * - r14371 e14372 e14373 b14374 b14375 b14376 b14377 d14358 d14269 d14257
              omega
            have d14378 : (x 10 3 && x 10 14).toNat = 0 := by
              have r14379 := hand1 (x 10 3) (x 10 14)
              have b14380 := hb (x 10 3)
              have b14381 := hb (x 10 3 && x 10 14)
              clear * - r14379 b14380 b14381 d14370
              omega
            have d14382 : (x 13 11).toNat = 1 := by
              have r14383 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b14384 := hb (x 9 4)
              have b14385 := hb (x 13 11)
              have b14386 := hb (x 12 1 && x 12 12)
              have b14387 := hb (x 11 2 && x 11 13)
              have b14388 := hb (x 10 3 && x 10 14)
              clear * - r14383 b14384 b14385 b14386 b14387 b14388 d14113 d14129 d14378 d14078
              omega
            have d14389 : (x 13 3).toNat = 1 := by
              have r14390 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
              have b14391 := hb (x 13 3)
              have b14392 := hb (x 13 11)
              clear * - r14390 b14391 b14392 d14382
              omega
            have d14393 : (x 16 12).toNat = 0 := by
              have r14394 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e14395 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
              have e14396 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
              have b14397 := hb (x 13 3)
              have b14398 := hb (x 14 2)
              have b14399 := hb (x 15 13)
              have b14400 := hb (x 16 12)
              clear * - r14394 e14395 e14396 b14397 b14398 b14399 b14400 d14389
              omega
            have d14401 : (x 16 1 && x 16 12).toNat = 0 := by
              have r14402 := hand2 (x 16 1) (x 16 12)
              have b14403 := hb (x 16 12)
              have b14404 := hb (x 16 1 && x 16 12)
              clear * - r14402 b14403 b14404 d14393
              omega
            have d14405 : (x 16 2 && x 16 12).toNat = 0 := by
              have r14406 := hand2 (x 16 2) (x 16 12)
              have b14407 := hb (x 16 12)
              have b14408 := hb (x 16 2 && x 16 12)
              clear * - r14406 b14407 b14408 d14393
              omega
            have d14409 : (x 15 13).toNat = 0 := by
              have r14410 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e14411 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
              have e14412 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
              have b14413 := hb (x 13 3)
              have b14414 := hb (x 14 2)
              have b14415 := hb (x 15 13)
              have b14416 := hb (x 16 12)
              clear * - r14410 e14411 e14412 b14413 b14414 b14415 b14416 d14393 d14389
              omega
            have d14417 : (x 15 2 && x 15 13).toNat = 0 := by
              have r14418 := hand2 (x 15 2) (x 15 13)
              have b14419 := hb (x 15 13)
              have b14420 := hb (x 15 2 && x 15 13)
              clear * - r14418 b14419 b14420 d14409
              omega
            have d14421 : (x 15 3 && x 15 13).toNat = 0 := by
              have r14422 := hand2 (x 15 3) (x 15 13)
              have b14423 := hb (x 15 13)
              have b14424 := hb (x 15 3 && x 15 13)
              clear * - r14422 b14423 b14424 d14409
              omega
            have d14425 : (x 14 1 && x 14 14).toNat = 1 := by
              have r14426 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b14427 := hb (x 13 2)
              have b14428 := hb (x 15 13)
              have b14429 := hb (x 14 1 && x 14 14)
              clear * - r14426 b14427 b14428 b14429 d14409 d14237
              omega
            have d14430 : (x 14 1).toNat = 1 := by
              have r14431 := hand1 (x 14 1) (x 14 14)
              have b14432 := hb (x 14 1)
              have b14433 := hb (x 14 1 && x 14 14)
              clear * - r14431 b14432 b14433 d14425
              omega
            have d14434 : (x 15 14).toNat = 0 := by
              have r14435 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b14436 := hb (x 14 1)
              have b14437 := hb (x 15 14)
              clear * - r14435 b14436 b14437 d14430
              omega
            have d14438 : (x 15 1 && x 15 14).toNat = 0 := by
              have r14439 := hand2 (x 15 1) (x 15 14)
              have b14440 := hb (x 15 14)
              have b14441 := hb (x 15 1 && x 15 14)
              clear * - r14439 b14440 b14441 d14434
              omega
            have d14442 : (x 15 2).toNat = 0 := by
              have r14443 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
              have b14444 := hb (x 15 2)
              have b14445 := hb (x 15 14)
              clear * - r14443 b14444 b14445 d14434
              omega
            have d14446 : (x 14 2).toNat = 0 := by
              have r14447 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e14448 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
              have e14449 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
              have b14450 := hb (x 13 3)
              have b14451 := hb (x 14 2)
              have b14452 := hb (x 15 13)
              have b14453 := hb (x 16 12)
              clear * - r14447 e14448 e14449 b14450 b14451 b14452 b14453 d14393 d14409 d14389
              omega
            have d14454 : (x 16 13).toNat = 1 := by
              have r14455 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b14456 := hb (x 14 2)
              have b14457 := hb (x 16 13)
              have b14458 := hb (x 15 1 && x 15 14)
              clear * - r14455 b14456 b14457 b14458 d14438 d14446
              omega
            have d14459 : (x 17 12).toNat = 0 := by
              have r14460 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e14461 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
              have e14462 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
              have b14463 := hb (x 14 3)
              have b14464 := hb (x 15 2)
              have b14465 := hb (x 16 13)
              have b14466 := hb (x 17 12)
              clear * - r14460 e14461 e14462 b14463 b14464 b14465 b14466 d14454 d14442
              omega
            have d14467 : (x 14 3).toNat = 0 := by
              have r14468 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e14469 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
              have e14470 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
              have b14471 := hb (x 14 3)
              have b14472 := hb (x 15 2)
              have b14473 := hb (x 16 13)
              have b14474 := hb (x 17 12)
              clear * - r14468 e14469 e14470 b14471 b14472 b14473 b14474 d14459 d14454 d14442
              omega
            have d14475 : (x 14 3 && x 14 14).toNat = 0 := by
              have r14476 := hand1 (x 14 3) (x 14 14)
              have b14477 := hb (x 14 3)
              have b14478 := hb (x 14 3 && x 14 14)
              clear * - r14476 b14477 b14478 d14467
              omega
            have d14479 : (x 17 11).toNat = 1 := by
              have r14480 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b14481 := hb (x 13 4)
              have b14482 := hb (x 17 11)
              have b14483 := hb (x 16 1 && x 16 12)
              have b14484 := hb (x 15 2 && x 15 13)
              have b14485 := hb (x 14 3 && x 14 14)
              clear * - r14480 b14481 b14482 b14483 b14484 b14485 d14401 d14417 d14475 d14366
              omega
            have d14486 : (x 17 3).toNat = 1 := by
              have r14487 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
              have b14488 := hb (x 17 3)
              have b14489 := hb (x 17 11)
              clear * - r14487 b14488 b14489 d14479
              omega
            have d14490 : (x 20 12).toNat = 0 := by
              have r14491 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e14492 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
              have e14493 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
              have b14494 := hb (x 17 3)
              have b14495 := hb (x 18 2)
              have b14496 := hb (x 19 13)
              have b14497 := hb (x 20 12)
              clear * - r14491 e14492 e14493 b14494 b14495 b14496 b14497 d14486
              omega
            have d14498 : (x 19 13).toNat = 0 := by
              have r14499 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e14500 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
              have e14501 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
              have b14502 := hb (x 17 3)
              have b14503 := hb (x 18 2)
              have b14504 := hb (x 19 13)
              have b14505 := hb (x 20 12)
              clear * - r14499 e14500 e14501 b14502 b14503 b14504 b14505 d14490 d14486
              omega
            have d14506 : (x 18 1 && x 18 14).toNat = 1 := by
              have r14507 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b14508 := hb (x 17 2)
              have b14509 := hb (x 19 13)
              have b14510 := hb (x 18 1 && x 18 14)
              clear * - r14507 b14508 b14509 b14510 d14498 d14350
              omega
            have d14511 : (x 18 14).toNat = 1 := by
              have r14512 := hand2 (x 18 1) (x 18 14)
              have b14513 := hb (x 18 14)
              have b14514 := hb (x 18 1 && x 18 14)
              clear * - r14512 b14513 b14514 d14506
              omega
            have d14515 : (x 17 1).toNat = 0 := by
              have r14516 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b14517 := hb (x 17 1)
              have b14518 := hb (x 18 14)
              clear * - r14516 b14517 b14518 d14511
              omega
            have d14519 : (x 17 1 && x 17 11).toNat = 0 := by
              have r14520 := hand1 (x 17 1) (x 17 11)
              have b14521 := hb (x 17 1)
              have b14522 := hb (x 17 1 && x 17 11)
              clear * - r14520 b14521 b14522 d14515
              omega
            have d14523 : (x 18 2).toNat = 0 := by
              have r14524 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e14525 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
              have e14526 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
              have b14527 := hb (x 17 3)
              have b14528 := hb (x 18 2)
              have b14529 := hb (x 19 13)
              have b14530 := hb (x 20 12)
              clear * - r14524 e14525 e14526 b14527 b14528 b14529 b14530 d14490 d14498 d14486
              omega
            have d14531 : (x 18 10).toNat = 0 := by
              have r14532 : (x 18 10).toNat ≤ (x 18 2).toNat := himp _ _ (hp10 18)
              have b14533 := hb (x 18 2)
              have b14534 := hb (x 18 10)
              clear * - r14532 b14533 b14534 d14523
              omega
            have r14535 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := by have q := hcov10 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b14536 := hb (x 13 5)
            have b14537 := hb (x 18 10)
            have b14538 := hb (x 17 1 && x 17 11)
            have b14539 := hb (x 16 2 && x 16 12)
            have b14540 := hb (x 15 3 && x 15 13)
            have b14541 := hb (x 14 4 && x 14 14)
            linarith only [r14535, b14536, b14537, b14538, b14539, b14540, b14541, d14531, d14519, d14405, d14421, d14303, d14315]
        · have f14542 : (x 1 1).toNat = 1 := by rw [h12481]; rfl
          have d14543 : (x 2 14).toNat = 0 := by
            have r14544 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b14545 := hb (x 1 1)
            have b14546 := hb (x 2 14)
            clear * - r14544 b14545 b14546 f14542
            omega
          have d14547 : (x 2 1 && x 2 14).toNat = 0 := by
            have r14548 := hand2 (x 2 1) (x 2 14)
            have b14549 := hb (x 2 14)
            have b14550 := hb (x 2 1 && x 2 14)
            clear * - r14548 b14549 b14550 d14543
            omega
          have d14551 : (x 2 6).toNat = 0 := by
            have r14552 : (x 2 6).toNat ≤ (x 2 14).toNat := himp _ _ (hp6 2)
            have b14553 := hb (x 2 6)
            have b14554 := hb (x 2 14)
            clear * - r14552 b14553 b14554 d14543
            omega
          have d14555 : (x 2 2 && x 2 6).toNat = 0 := by
            have r14556 := hand2 (x 2 2) (x 2 6)
            have b14557 := hb (x 2 6)
            have b14558 := hb (x 2 2 && x 2 6)
            clear * - r14556 b14557 b14558 d14551
            omega
          have d14559 : (x 2 2).toNat = 0 := by
            have r14560 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
            have b14561 := hb (x 2 2)
            have b14562 := hb (x 2 14)
            clear * - r14560 b14561 b14562 d14543
            omega
          have d14563 : (x 3 13).toNat = 1 := by
            have r14564 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b14565 := hb (x 1 2)
            have b14566 := hb (x 3 13)
            have b14567 := hb (x 2 1 && x 2 14)
            clear * - r14564 b14565 b14566 b14567 d14547 g12
            omega
          have d14568 : (x 3 1).toNat = 1 := by
            have r14569 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
            have b14570 := hb (x 3 1)
            have b14571 := hb (x 3 13)
            clear * - r14569 b14570 b14571 d14563
            omega
          have d14572 : (x 4 12).toNat = 0 := by
            have r14573 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e14574 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e14575 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b14576 := hb (x 1 3)
            have b14577 := hb (x 2 2)
            have b14578 := hb (x 3 13)
            have b14579 := hb (x 4 12)
            clear * - r14573 e14574 e14575 b14576 b14577 b14578 b14579 d14563 d14559
            omega
          have d14580 : (x 4 3 && x 4 12).toNat = 0 := by
            have r14581 := hand2 (x 4 3) (x 4 12)
            have b14582 := hb (x 4 12)
            have b14583 := hb (x 4 3 && x 4 12)
            clear * - r14581 b14582 b14583 d14572
            omega
          have d14584 : (x 4 4).toNat = 0 := by
            have r14585 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
            have b14586 := hb (x 4 4)
            have b14587 := hb (x 4 12)
            clear * - r14585 b14586 b14587 d14572
            omega
          have d14588 : (x 1 3).toNat = 0 := by
            have r14589 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e14590 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e14591 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b14592 := hb (x 1 3)
            have b14593 := hb (x 2 2)
            have b14594 := hb (x 3 13)
            have b14595 := hb (x 4 12)
            clear * - r14589 e14590 e14591 b14592 b14593 b14594 b14595 d14572 d14563 d14559
            omega
          have d14596 : (x 1 3 && x 1 7).toNat = 0 := by
            have r14597 := hand1 (x 1 3) (x 1 7)
            have b14598 := hb (x 1 3)
            have b14599 := hb (x 1 3 && x 1 7)
            clear * - r14597 b14598 b14599 d14588
            omega
          have r14600 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r14601 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r14602 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e14603 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
          have e14604 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
          have e14605 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
          have e14606 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
          have e14607 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
          have e14608 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
          have r14609 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e14610 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e14611 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e14612 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e14613 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e14614 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e14615 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have r14616 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e14617 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
          have e14618 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
          have r14619 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e14620 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
          have e14621 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
          have r14622 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r14623 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e14624 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
          have e14625 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
          have r14626 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := by have q := hcov5 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r14627 : 1 ≤ (x 1 7).toNat + (x 0 1 && x 0 8).toNat + (x (-1) 2 && x (-1) 9).toNat + (x (-2) 3 && x (-2) 10).toNat + (x (-3) 4 && x (-3) 11).toNat + (x (-4) 5 && x (-4) 12).toNat + (x (-5) 6 && x (-5) 13).toNat + (x (-6) 7 && x (-6) 14).toNat + (x (-7) 8).toNat := by have q := hcov7 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r14628 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r14629 : 1 ≤ (x (-7) 11).toNat + (x (-8) 1 && x (-8) 12).toNat + (x (-9) 2 && x (-9) 13).toNat + (x (-10) 3 && x (-10) 14).toNat + (x (-11) 4).toNat := by have q := hcov11 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r14630 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
          have r14631 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
          have r14632 := hand1 (x (-4) 8) (x (-4) 12)
          have r14633 := hand1 (x (-5) 9) (x (-5) 13)
          have r14634 := hand2 (x (-7) 8) (x (-7) 13)
          have r14635 := hand1 (x (-8) 9) (x (-8) 14)
          have r14636 := hand2 (x 6 1) (x 6 10)
          have r14637 := hand2 (x 5 2) (x 5 11)
          have r14638 := hand2 (x (-8) 1) (x (-8) 12)
          have r14639 := hand2 (x (-9) 2) (x (-9) 13)
          have r14640 := hand2 (x (-10) 3) (x (-10) 14)
          have b14684 := hb (x 7 1)
          linarith only [r14600, r14601, r14602, e14603, e14604, e14605, e14606, e14607, e14608, r14609, e14610, e14611, e14612, e14613, e14614, e14615, r14616, e14617, e14618, r14619, e14620, e14621, r14622, r14623, e14624, e14625, r14626, r14627, r14628, r14629, r14630, r14631, r14632, r14633, r14634, r14635, r14636, r14637, r14638, r14639, r14640, b14684, d12013, d11905, d11997, d11812, g3, g4, g8, g10, d14588, g13, g14, d14559, d14551, d14568, d14584, d14555, d14596, g21, g22, d11824, d11917, d12071, d11865, d11889, g33, g34, g35, g36, g46, g47, d11820, g48, g49, g50, g51, d14580, g61, g62]
    · have f14721 : (x 0 7).toNat = 1 := by rw [h12083]; rfl
      have d14722 : (x 7 8).toNat = 0 := by
        have r14723 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e14724 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e14725 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e14726 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e14727 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e14728 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e14729 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b14730 := hb (x 0 7)
        have b14731 := hb (x 1 6)
        have b14732 := hb (x 2 5)
        have b14733 := hb (x 3 4)
        have b14734 := hb (x 4 11)
        have b14735 := hb (x 5 10)
        have b14736 := hb (x 6 9)
        have b14737 := hb (x 7 8)
        clear * - r14723 e14724 e14725 e14726 e14727 e14728 e14729 b14730 b14731 b14732 b14733 b14734 b14735 b14736 b14737 g19 g18 g14 f14721
        omega
      have d14738 : (x 6 9).toNat = 0 := by
        have r14739 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e14740 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e14741 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e14742 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e14743 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e14744 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e14745 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b14746 := hb (x 0 7)
        have b14747 := hb (x 1 6)
        have b14748 := hb (x 2 5)
        have b14749 := hb (x 3 4)
        have b14750 := hb (x 4 11)
        have b14751 := hb (x 5 10)
        have b14752 := hb (x 6 9)
        have b14753 := hb (x 7 8)
        clear * - r14739 e14740 e14741 e14742 e14743 e14744 e14745 b14746 b14747 b14748 b14749 b14750 b14751 b14752 b14753 d14722 g19 g18 g14 f14721
        omega
      have d14754 : (x 5 10).toNat = 0 := by
        have r14755 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e14756 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e14757 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e14758 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e14759 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e14760 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e14761 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b14762 := hb (x 0 7)
        have b14763 := hb (x 1 6)
        have b14764 := hb (x 2 5)
        have b14765 := hb (x 3 4)
        have b14766 := hb (x 4 11)
        have b14767 := hb (x 5 10)
        have b14768 := hb (x 6 9)
        have b14769 := hb (x 7 8)
        clear * - r14755 e14756 e14757 e14758 e14759 e14760 e14761 b14762 b14763 b14764 b14765 b14766 b14767 b14768 b14769 d14722 d14738 g19 g18 g14 f14721
        omega
      have d14770 : (x 5 1 && x 5 10).toNat = 0 := by
        have r14771 := hand2 (x 5 1) (x 5 10)
        have b14772 := hb (x 5 10)
        have b14773 := hb (x 5 1 && x 5 10)
        clear * - r14771 b14772 b14773 d14754
        omega
      have d14774 : (x 4 2 && x 4 11).toNat = 1 := by
        have r14775 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b14776 := hb (x 0 6)
        have b14777 := hb (x 6 9)
        have b14778 := hb (x 5 1 && x 5 10)
        have b14779 := hb (x 4 2 && x 4 11)
        have b14780 := hb (x 3 3 && x 3 12)
        have b14781 := hb (x 2 4 && x 2 13)
        have b14782 := hb (x 1 5 && x 1 14)
        clear * - r14775 b14776 b14777 b14778 b14779 b14780 b14781 b14782 d14738 d14770 g58 g59 g60 f12070
        omega
      have d14783 : (x 4 11).toNat = 1 := by
        have r14784 := hand2 (x 4 2) (x 4 11)
        have b14785 := hb (x 4 11)
        have b14786 := hb (x 4 2 && x 4 11)
        clear * - r14784 b14785 b14786 d14774
        omega
      have r14787 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e14788 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e14789 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e14790 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e14791 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e14792 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e14793 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b14794 := hb (x 0 7)
      have b14795 := hb (x 1 6)
      have b14796 := hb (x 2 5)
      have b14797 := hb (x 3 4)
      have b14798 := hb (x 4 11)
      have b14799 := hb (x 5 10)
      have b14800 := hb (x 6 9)
      have b14801 := hb (x 7 8)
      linarith only [r14787, e14788, e14789, e14790, e14791, e14792, e14793, b14794, b14795, b14796, b14797, b14798, b14799, b14800, b14801, d14722, d14738, d14754, d14783, g19, g18, g14, f14721]
  · have f14802 : (x 0 6).toNat = 1 := by rw [h12069]; rfl
    have d14803 : (x 6 8).toNat = 0 := by
      have r14804 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e14805 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e14806 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e14807 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e14808 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e14809 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e14810 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b14811 := hb (x (-1) 7)
      have b14812 := hb (x 0 6)
      have b14813 := hb (x 1 5)
      have b14814 := hb (x 2 4)
      have b14815 := hb (x 3 11)
      have b14816 := hb (x 4 10)
      have b14817 := hb (x 5 9)
      have b14818 := hb (x 6 8)
      clear * - r14804 e14805 e14806 e14807 e14808 e14809 e14810 b14811 b14812 b14813 b14814 b14815 b14816 b14817 b14818 g17 g13 f14802
      omega
    have d14819 : (x 6 2 && x 6 8).toNat = 0 := by
      have r14820 := hand2 (x 6 2) (x 6 8)
      have b14821 := hb (x 6 8)
      have b14822 := hb (x 6 2 && x 6 8)
      clear * - r14820 b14821 b14822 d14803
      omega
    have d14823 : (x 5 9).toNat = 0 := by
      have r14824 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e14825 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e14826 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e14827 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e14828 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e14829 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e14830 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b14831 := hb (x (-1) 7)
      have b14832 := hb (x 0 6)
      have b14833 := hb (x 1 5)
      have b14834 := hb (x 2 4)
      have b14835 := hb (x 3 11)
      have b14836 := hb (x 4 10)
      have b14837 := hb (x 5 9)
      have b14838 := hb (x 6 8)
      clear * - r14824 e14825 e14826 e14827 e14828 e14829 e14830 b14831 b14832 b14833 b14834 b14835 b14836 b14837 b14838 d14803 g17 g13 f14802
      omega
    have d14839 : (x 5 3 && x 5 9).toNat = 0 := by
      have r14840 := hand2 (x 5 3) (x 5 9)
      have b14841 := hb (x 5 9)
      have b14842 := hb (x 5 3 && x 5 9)
      clear * - r14840 b14841 b14842 d14823
      omega
    have d14843 : (x 4 10).toNat = 0 := by
      have r14844 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e14845 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e14846 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e14847 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e14848 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e14849 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e14850 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b14851 := hb (x (-1) 7)
      have b14852 := hb (x 0 6)
      have b14853 := hb (x 1 5)
      have b14854 := hb (x 2 4)
      have b14855 := hb (x 3 11)
      have b14856 := hb (x 4 10)
      have b14857 := hb (x 5 9)
      have b14858 := hb (x 6 8)
      clear * - r14844 e14845 e14846 e14847 e14848 e14849 e14850 b14851 b14852 b14853 b14854 b14855 b14856 b14857 b14858 d14803 d14823 g17 g13 f14802
      omega
    have d14859 : (x 4 1 && x 4 10).toNat = 0 := by
      have r14860 := hand2 (x 4 1) (x 4 10)
      have b14861 := hb (x 4 10)
      have b14862 := hb (x 4 1 && x 4 10)
      clear * - r14860 b14861 b14862 d14843
      omega
    have d14863 : (x 4 4 && x 4 10).toNat = 0 := by
      have r14864 := hand2 (x 4 4) (x 4 10)
      have b14865 := hb (x 4 10)
      have b14866 := hb (x 4 4 && x 4 10)
      clear * - r14864 b14865 b14866 d14843
      omega
    have d14867 : (x 3 11).toNat = 0 := by
      have r14868 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e14869 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e14870 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e14871 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e14872 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e14873 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e14874 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b14875 := hb (x (-1) 7)
      have b14876 := hb (x 0 6)
      have b14877 := hb (x 1 5)
      have b14878 := hb (x 2 4)
      have b14879 := hb (x 3 11)
      have b14880 := hb (x 4 10)
      have b14881 := hb (x 5 9)
      have b14882 := hb (x 6 8)
      clear * - r14868 e14869 e14870 e14871 e14872 e14873 e14874 b14875 b14876 b14877 b14878 b14879 b14880 b14881 b14882 d14803 d14823 d14843 g17 g13 f14802
      omega
    have d14883 : (x 3 2 && x 3 11).toNat = 0 := by
      have r14884 := hand2 (x 3 2) (x 3 11)
      have b14885 := hb (x 3 11)
      have b14886 := hb (x 3 2 && x 3 11)
      clear * - r14884 b14885 b14886 d14867
      omega
    have d14887 : (x (-1) 6).toNat = 1 := by
      have r14888 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b14889 := hb (x (-1) 6)
      have b14890 := hb (x 5 9)
      have b14891 := hb (x 4 1 && x 4 10)
      have b14892 := hb (x 3 2 && x 3 11)
      have b14893 := hb (x 2 3 && x 2 12)
      have b14894 := hb (x 1 4 && x 1 13)
      have b14895 := hb (x 0 5 && x 0 14)
      clear * - r14888 b14889 b14890 b14891 b14892 b14893 b14894 b14895 d14823 d14859 d14883 g55 g56 g57
      omega
    have d14896 : (x (-1) 14).toNat = 1 := by
      have r14897 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
      have b14898 := hb (x (-1) 6)
      have b14899 := hb (x (-1) 14)
      clear * - r14897 b14898 b14899 d14887
      omega
    have d14900 : (x (-2) 1).toNat = 0 := by
      have r14901 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b14902 := hb (x (-2) 1)
      have b14903 := hb (x (-1) 14)
      clear * - r14901 b14902 b14903 d14896
      omega
    have d14904 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
      have r14905 := hand1 (x (-2) 1) (x (-2) 14)
      have b14906 := hb (x (-2) 1)
      have b14907 := hb (x (-2) 1 && x (-2) 14)
      clear * - r14905 b14906 b14907 d14900
      omega
    have d14908 : (x (-3) 2).toNat = 1 := by
      have r14909 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b14910 := hb (x (-3) 2)
      have b14911 := hb (x (-1) 13)
      have b14912 := hb (x (-2) 1 && x (-2) 14)
      clear * - r14909 b14910 b14911 b14912 g7 d14904
      omega
    have d14913 : (x (-3) 14).toNat = 1 := by
      have r14914 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
      have b14915 := hb (x (-3) 2)
      have b14916 := hb (x (-3) 14)
      clear * - r14914 b14915 b14916 d14908
      omega
    have d14917 : (x (-1) 12).toNat = 0 := by
      have r14918 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e14919 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e14920 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b14921 := hb (x (-4) 3)
      have b14922 := hb (x (-3) 2)
      have b14923 := hb (x (-2) 13)
      have b14924 := hb (x (-1) 12)
      clear * - r14918 e14919 e14920 b14921 b14922 b14923 b14924 d14908
      omega
    have d14925 : (x (-1) 8 && x (-1) 12).toNat = 0 := by
      have r14926 := hand2 (x (-1) 8) (x (-1) 12)
      have b14927 := hb (x (-1) 12)
      have b14928 := hb (x (-1) 8 && x (-1) 12)
      clear * - r14926 b14927 b14928 d14917
      omega
    have d14929 : (x (-2) 13).toNat = 0 := by
      have r14930 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e14931 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e14932 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b14933 := hb (x (-4) 3)
      have b14934 := hb (x (-3) 2)
      have b14935 := hb (x (-2) 13)
      have b14936 := hb (x (-1) 12)
      clear * - r14930 e14931 e14932 b14933 b14934 b14935 b14936 d14917 d14908
      omega
    have d14937 : (x (-2) 9 && x (-2) 13).toNat = 0 := by
      have r14938 := hand2 (x (-2) 9) (x (-2) 13)
      have b14939 := hb (x (-2) 13)
      have b14940 := hb (x (-2) 9 && x (-2) 13)
      clear * - r14938 b14939 b14940 d14929
      omega
    have d14941 : (x (-4) 3).toNat = 0 := by
      have r14942 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e14943 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e14944 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b14945 := hb (x (-4) 3)
      have b14946 := hb (x (-3) 2)
      have b14947 := hb (x (-2) 13)
      have b14948 := hb (x (-1) 12)
      clear * - r14942 e14943 e14944 b14945 b14946 b14947 b14948 d14917 d14929 d14908
      omega
    have d14949 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
      have r14950 := hand1 (x (-4) 3) (x (-4) 12)
      have b14951 := hb (x (-4) 3)
      have b14952 := hb (x (-4) 3 && x (-4) 12)
      clear * - r14950 b14951 b14952 d14941
      omega
    have d14953 : (x (-4) 11).toNat = 0 := by
      have r14954 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
      have b14955 := hb (x (-4) 3)
      have b14956 := hb (x (-4) 11)
      clear * - r14954 b14955 b14956 d14941
      omega
    have d14957 : (x (-2) 9).toNat = 0 := by
      have r14958 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
      have b14959 := hb (x (-2) 1)
      have b14960 := hb (x (-2) 9)
      clear * - r14958 b14959 b14960 d14900
      omega
    have d14961 : (x 3 5 && x 3 11).toNat = 0 := by
      have r14962 := hand2 (x 3 5) (x 3 11)
      have b14963 := hb (x 3 11)
      have b14964 := hb (x 3 5 && x 3 11)
      clear * - r14962 b14963 b14964 d14867
      omega
    have r14965 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r14966 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14967 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
    have e14968 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
    have e14969 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
    have e14970 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
    have e14971 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
    have e14972 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
    have r14973 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14974 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e14975 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e14976 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e14977 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e14978 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e14979 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have r14980 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14981 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e14982 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e14983 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e14984 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e14985 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e14986 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have r14987 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14988 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e14989 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have r14990 : 1 ≤ (x 7 4).toNat + (x 6 1 && x 6 5).toNat + (x 5 2 && x 5 6).toNat + (x 4 3 && x 4 7).toNat + (x 3 4 && x 3 8).toNat + (x 2 5 && x 2 9).toNat + (x 1 6 && x 1 10).toNat + (x 0 7 && x 0 11).toNat + (x (-1) 8 && x (-1) 12).toNat + (x (-2) 9 && x (-2) 13).toNat + (x (-3) 10 && x (-3) 14).toNat + (x (-4) 11).toNat := by have q := hcov4 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14991 : (x 6 1 && x 6 5).toNat = (x 6 5).toNat := handr _ _ (fun h => hp13 6 (hp5 6 (h)))
    have e14992 : (x (-3) 10 && x (-3) 14).toNat = (x (-3) 10).toNat := handl _ _ (fun h => hp2 (-3) (hp10 (-3) (h)))
    have r14993 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r14994 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r14995 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r14996 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r14997 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
    have r14998 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
    have r14999 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
    have r15000 := hand2 (x 5 2) (x 5 6)
    have r15001 := hand2 (x 4 3) (x 4 7)
    have r15002 := hand1 (x 0 7) (x 0 11)
    have r15003 := hand2 (x 7 1) (x 7 7)
    have r15004 := hand1 (x (-5) 4) (x (-5) 13)
    have r15005 := hand1 (x (-6) 5) (x (-6) 14)
    have r15006 := hand2 (x 4 1) (x 4 11)
    have r15007 := hand1 (x 10 1) (x 10 12)
    have r15008 := hand1 (x 9 2) (x 9 13)
    have r15009 := hand1 (x 8 3) (x 8 14)
    linarith only [r14965, r14966, e14967, e14968, e14969, e14970, e14971, e14972, r14973, e14974, e14975, e14976, e14977, e14978, e14979, r14980, e14981, e14982, e14983, e14984, e14985, e14986, r14987, e14988, e14989, r14990, e14991, e14992, r14993, r14994, r14995, r14996, r14997, r14998, r14999, r15000, r15001, r15002, r15003, r15004, r15005, r15006, r15007, r15008, r15009, d14953, d14913, d14957, d14929, g4, d14917, g9, d11929, g14, g16, g18, d12049, g19, d12029, g30, g31, g32, d14925, d14937, d14819, d14839, d14863, d14961, g43, g44, g45, d11816, d11913, d14949, g65, g66, g67]

theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b101 (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x (-4) 5).toNat = 0)
    (g2 : (x (-2) 11).toNat = 0)
    (g3 : (x (-1) 5).toNat = 0)
    (g4 : (x (-1) 9).toNat = 0)
    (g5 : (x (-1) 10).toNat = 0)
    (g6 : (x (-1) 11).toNat = 0)
    (g7 : (x (-1) 13).toNat = 0)
    (g8 : (x 0 4).toNat = 1)
    (g9 : (x 0 5).toNat = 0)
    (g10 : (x 0 8).toNat = 0)
    (g11 : (x 0 9).toNat = 1)
    (g12 : (x 1 2).toNat = 0)
    (g13 : (x 1 5).toNat = 0)
    (g14 : (x 1 6).toNat = 0)
    (g15 : (x 1 8).toNat = 0)
    (g16 : (x 1 10).toNat = 0)
    (g17 : (x 2 4).toNat = 0)
    (g18 : (x 2 5).toNat = 0)
    (g19 : (x 3 4).toNat = 0)
    (g20 : (x (-1) 3 && x (-1) 7).toNat = 0)
    (g21 : (x 0 4 && x 0 8).toNat = 0)
    (g22 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g23 : (x 1 4 && x 1 8).toNat = 0)
    (g24 : (x 0 5 && x 0 9).toNat = 0)
    (g25 : (x (-1) 6 && x (-1) 10).toNat = 0)
    (g26 : (x (-2) 7 && x (-2) 11).toNat = 0)
    (g27 : (x 2 4 && x 2 8).toNat = 0)
    (g28 : (x 1 5 && x 1 9).toNat = 0)
    (g29 : (x (-1) 7 && x (-1) 11).toNat = 0)
    (g30 : (x 3 4 && x 3 8).toNat = 0)
    (g31 : (x 2 5 && x 2 9).toNat = 0)
    (g32 : (x 1 6 && x 1 10).toNat = 0)
    (g33 : (x (-3) 4 && x (-3) 9).toNat = 0)
    (g34 : (x (-4) 5 && x (-4) 10).toNat = 0)
    (g35 : (x (-5) 6 && x (-5) 11).toNat = 0)
    (g36 : (x (-6) 7 && x (-6) 12).toNat = 0)
    (g37 : (x 0 8 && x 0 13).toNat = 0)
    (g38 : (x (-1) 9 && x (-1) 14).toNat = 0)
    (g39 : (x (-3) 4 && x (-3) 10).toNat = 0)
    (g40 : (x (-4) 5 && x (-4) 11).toNat = 0)
    (g41 : (x (-5) 6 && x (-5) 12).toNat = 0)
    (g42 : (x (-6) 7 && x (-6) 13).toNat = 0)
    (g43 : (x 2 6 && x 2 12).toNat = 0)
    (g44 : (x 1 7 && x 1 13).toNat = 0)
    (g45 : (x 0 8 && x 0 14).toNat = 0)
    (g46 : (x 0 1 && x 0 8).toNat = 0)
    (g47 : (x (-1) 2 && x (-1) 9).toNat = 0)
    (g48 : (x (-3) 4 && x (-3) 11).toNat = 0)
    (g49 : (x (-4) 5 && x (-4) 12).toNat = 0)
    (g50 : (x (-5) 6 && x (-5) 13).toNat = 0)
    (g51 : (x (-6) 7 && x (-6) 14).toNat = 0)
    (g52 : (x (-1) 2 && x (-1) 11).toNat = 0)
    (g53 : (x (-3) 4 && x (-3) 13).toNat = 0)
    (g54 : (x (-4) 5 && x (-4) 14).toNat = 0)
    (g55 : (x 2 3 && x 2 12).toNat = 0)
    (g56 : (x 1 4 && x 1 13).toNat = 0)
    (g57 : (x 0 5 && x 0 14).toNat = 0)
    (g58 : (x 3 3 && x 3 12).toNat = 0)
    (g59 : (x 2 4 && x 2 13).toNat = 0)
    (g60 : (x 1 5 && x 1 14).toNat = 0)
    (g61 : (x 3 4 && x 3 13).toNat = 0)
    (g62 : (x 2 5 && x 2 14).toNat = 0)
    (g63 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g64 : (x (-3) 4 && x (-3) 14).toNat = 0)
    (g65 : (x 3 2 && x 3 12).toNat = 0)
    (g66 : (x 2 3 && x 2 13).toNat = 0)
    (g67 : (x 1 4 && x 1 14).toNat = 0)
    (g68 : (x 2 4 && x 2 14).toNat = 0)
    (g69 : (x (-1) 1 && x (-1) 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b101_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69
