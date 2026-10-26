import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b000011

Topic: combinatorics   Node: 2002b530dbf4

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core: under the layer-free tight-cover constraints for k = 15 and 72 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b000011_aux (x : ℤ → Fin 16 → Bool)
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
    (g2 : (x (-3) 11).toNat = 0)
    (g3 : (x (-3) 13).toNat = 0)
    (g4 : (x (-2) 2).toNat = 1)
    (g5 : (x (-2) 14).toNat = 1)
    (g6 : (x (-1) 1).toNat = 0)
    (g7 : (x (-1) 5).toNat = 0)
    (g8 : (x (-1) 9).toNat = 0)
    (g9 : (x (-1) 13).toNat = 0)
    (g10 : (x 0 1).toNat = 0)
    (g11 : (x 0 2).toNat = 0)
    (g12 : (x 0 3).toNat = 0)
    (g13 : (x 0 4).toNat = 0)
    (g14 : (x 0 5).toNat = 0)
    (g15 : (x 0 7).toNat = 0)
    (g16 : (x 0 8).toNat = 0)
    (g17 : (x 0 9).toNat = 0)
    (g18 : (x 0 10).toNat = 0)
    (g19 : (x 0 11).toNat = 0)
    (g20 : (x 0 12).toNat = 0)
    (g21 : (x 0 13).toNat = 0)
    (g22 : (x 0 14).toNat = 1)
    (g23 : (x 1 3).toNat = 1)
    (g24 : (x 1 8).toNat = 1)
    (g25 : (x 2 2).toNat = 0)
    (g26 : (x 2 10).toNat = 0)
    (g27 : (x 3 5).toNat = 0)
    (g28 : (x 3 13).toNat = 0)
    (g29 : (x 4 4).toNat = 0)
    (g30 : (x 2 2 && x 2 6).toNat = 0)
    (g31 : (x 0 4 && x 0 8).toNat = 0)
    (g32 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g33 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g34 : (x 4 4 && x 4 8).toNat = 0)
    (g35 : (x 3 5 && x 3 9).toNat = 0)
    (g36 : (x 2 6 && x 2 10).toNat = 0)
    (g37 : (x 0 8 && x 0 12).toNat = 0)
    (g38 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g39 : (x (-1) 1 && x (-1) 6).toNat = 0)
    (g40 : (x (-3) 3 && x (-3) 8).toNat = 0)
    (g41 : (x 0 1 && x 0 6).toNat = 0)
    (g42 : (x (-3) 4 && x (-3) 9).toNat = 0)
    (g43 : (x 0 2 && x 0 8).toNat = 0)
    (g44 : (x (-1) 3 && x (-1) 9).toNat = 0)
    (g45 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g46 : (x 4 4 && x 4 10).toNat = 0)
    (g47 : (x 3 5 && x 3 11).toNat = 0)
    (g48 : (x 0 8 && x 0 14).toNat = 0)
    (g49 : (x 0 1 && x 0 8).toNat = 0)
    (g50 : (x (-1) 2 && x (-1) 9).toNat = 0)
    (g51 : (x (-3) 4 && x (-3) 11).toNat = 0)
    (g52 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g53 : (x (-3) 3 && x (-3) 12).toNat = 0)
    (g54 : (x 0 1 && x 0 10).toNat = 0)
    (g55 : (x (-3) 4 && x (-3) 13).toNat = 0)
    (g56 : (x 0 5 && x 0 14).toNat = 0)
    (g57 : (x 4 3 && x 4 12).toNat = 0)
    (g58 : (x 3 4 && x 3 13).toNat = 0)
    (g59 : (x 2 2 && x 2 12).toNat = 0)
    (g60 : (x 0 4 && x 0 14).toNat = 0)
    (g61 : (x 4 2 && x 4 12).toNat = 0)
    (g62 : (x 3 3 && x 3 13).toNat = 0)
    (g63 : (x (-3) 2 && x (-3) 13).toNat = 0)
    (g64 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g65 : (x (-3) 3 && x (-3) 14).toNat = 0)
    (g66 : (x 0 2 && x 0 13).toNat = 0)
    (g67 : (x 0 3 && x 0 14).toNat = 0)
    (g68 : (x 4 1 && x 4 12).toNat = 0)
    (g69 : (x 3 2 && x 3 13).toNat = 0)
    (g70 : (x (-3) 1 && x (-3) 14).toNat = 0)
    (g71 : (x 0 1 && x 0 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d11832 : (x (-1) 10).toNat = 0 := by
    have r11833 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11834 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e11835 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e11836 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e11837 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e11838 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e11839 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b11840 := hb (x (-6) 7)
    have b11841 := hb (x (-5) 6)
    have b11842 := hb (x (-4) 5)
    have b11843 := hb (x (-3) 4)
    have b11844 := hb (x (-2) 11)
    have b11845 := hb (x (-1) 10)
    have b11846 := hb (x 0 9)
    have b11847 := hb (x 1 8)
    clear * - r11833 e11834 e11835 e11836 e11837 e11838 e11839 b11840 b11841 b11842 b11843 b11844 b11845 b11846 b11847 g24 g17
    omega
  have d11848 : (x (-2) 11).toNat = 0 := by
    have r11849 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11850 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e11851 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e11852 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e11853 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e11854 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e11855 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b11856 := hb (x (-6) 7)
    have b11857 := hb (x (-5) 6)
    have b11858 := hb (x (-4) 5)
    have b11859 := hb (x (-3) 4)
    have b11860 := hb (x (-2) 11)
    have b11861 := hb (x (-1) 10)
    have b11862 := hb (x 0 9)
    have b11863 := hb (x 1 8)
    clear * - r11849 e11850 e11851 e11852 e11853 e11854 e11855 b11856 b11857 b11858 b11859 b11860 b11861 b11862 b11863 g24 g17 d11832
    omega
  have d11864 : (x (-2) 1 && x (-2) 11).toNat = 0 := by
    have r11865 := hand2 (x (-2) 1) (x (-2) 11)
    have b11866 := hb (x (-2) 11)
    have b11867 := hb (x (-2) 1 && x (-2) 11)
    clear * - r11865 b11866 b11867 d11848
    omega
  have d11868 : (x (-2) 2 && x (-2) 11).toNat = 0 := by
    have r11869 := hand2 (x (-2) 2) (x (-2) 11)
    have b11870 := hb (x (-2) 11)
    have b11871 := hb (x (-2) 2 && x (-2) 11)
    clear * - r11869 b11870 b11871 d11848
    omega
  have d11872 : (x (-3) 4).toNat = 0 := by
    have r11873 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11874 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e11875 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e11876 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e11877 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e11878 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e11879 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b11880 := hb (x (-6) 7)
    have b11881 := hb (x (-5) 6)
    have b11882 := hb (x (-4) 5)
    have b11883 := hb (x (-3) 4)
    have b11884 := hb (x (-2) 11)
    have b11885 := hb (x (-1) 10)
    have b11886 := hb (x 0 9)
    have b11887 := hb (x 1 8)
    clear * - r11873 e11874 e11875 e11876 e11877 e11878 e11879 b11880 b11881 b11882 b11883 b11884 b11885 b11886 b11887 g24 g17 d11832 d11848
    omega
  have d11888 : (x (-3) 2 && x (-3) 4).toNat = 0 := by
    have r11889 := hand2 (x (-3) 2) (x (-3) 4)
    have b11890 := hb (x (-3) 4)
    have b11891 := hb (x (-3) 2 && x (-3) 4)
    clear * - r11889 b11890 b11891 d11872
    omega
  have d11892 : (x (-4) 5).toNat = 0 := by
    have r11893 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11894 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e11895 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e11896 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e11897 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e11898 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e11899 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b11900 := hb (x (-6) 7)
    have b11901 := hb (x (-5) 6)
    have b11902 := hb (x (-4) 5)
    have b11903 := hb (x (-3) 4)
    have b11904 := hb (x (-2) 11)
    have b11905 := hb (x (-1) 10)
    have b11906 := hb (x 0 9)
    have b11907 := hb (x 1 8)
    clear * - r11893 e11894 e11895 e11896 e11897 e11898 e11899 b11900 b11901 b11902 b11903 b11904 b11905 b11906 b11907 g24 g17 d11832 d11848 d11872
    omega
  have d11908 : (x (-4) 5 && x (-4) 14).toNat = 0 := by
    have r11909 := hand1 (x (-4) 5) (x (-4) 14)
    have b11910 := hb (x (-4) 5)
    have b11911 := hb (x (-4) 5 && x (-4) 14)
    clear * - r11909 b11910 b11911 d11892
    omega
  have d11912 : (x (-4) 5 && x (-4) 12).toNat = 0 := by
    have r11913 := hand1 (x (-4) 5) (x (-4) 12)
    have b11914 := hb (x (-4) 5)
    have b11915 := hb (x (-4) 5 && x (-4) 12)
    clear * - r11913 b11914 b11915 d11892
    omega
  have d11916 : (x (-4) 5 && x (-4) 10).toNat = 0 := by
    have r11917 := hand1 (x (-4) 5) (x (-4) 10)
    have b11918 := hb (x (-4) 5)
    have b11919 := hb (x (-4) 5 && x (-4) 10)
    clear * - r11917 b11918 b11919 d11892
    omega
  have d11920 : (x (-4) 3 && x (-4) 5).toNat = 0 := by
    have r11921 := hand2 (x (-4) 3) (x (-4) 5)
    have b11922 := hb (x (-4) 5)
    have b11923 := hb (x (-4) 3 && x (-4) 5)
    clear * - r11921 b11922 b11923 d11892
    omega
  have d11924 : (x (-5) 6).toNat = 0 := by
    have r11925 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11926 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e11927 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e11928 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e11929 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e11930 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e11931 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b11932 := hb (x (-6) 7)
    have b11933 := hb (x (-5) 6)
    have b11934 := hb (x (-4) 5)
    have b11935 := hb (x (-3) 4)
    have b11936 := hb (x (-2) 11)
    have b11937 := hb (x (-1) 10)
    have b11938 := hb (x 0 9)
    have b11939 := hb (x 1 8)
    clear * - r11925 e11926 e11927 e11928 e11929 e11930 e11931 b11932 b11933 b11934 b11935 b11936 b11937 b11938 b11939 g24 g17 d11832 d11848 d11872 d11892
    omega
  have d11940 : (x (-5) 6 && x (-5) 13).toNat = 0 := by
    have r11941 := hand1 (x (-5) 6) (x (-5) 13)
    have b11942 := hb (x (-5) 6)
    have b11943 := hb (x (-5) 6 && x (-5) 13)
    clear * - r11941 b11942 b11943 d11924
    omega
  have d11944 : (x (-5) 6 && x (-5) 11).toNat = 0 := by
    have r11945 := hand1 (x (-5) 6) (x (-5) 11)
    have b11946 := hb (x (-5) 6)
    have b11947 := hb (x (-5) 6 && x (-5) 11)
    clear * - r11945 b11946 b11947 d11924
    omega
  have d11948 : (x (-5) 2 && x (-5) 6).toNat = 0 := by
    have r11949 := hand2 (x (-5) 2) (x (-5) 6)
    have b11950 := hb (x (-5) 6)
    have b11951 := hb (x (-5) 2 && x (-5) 6)
    clear * - r11949 b11950 b11951 d11924
    omega
  have d11952 : (x (-5) 4 && x (-5) 6).toNat = 0 := by
    have r11953 := hand2 (x (-5) 4) (x (-5) 6)
    have b11954 := hb (x (-5) 6)
    have b11955 := hb (x (-5) 4 && x (-5) 6)
    clear * - r11953 b11954 b11955 d11924
    omega
  have d11956 : (x (-6) 7).toNat = 0 := by
    have r11957 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11958 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e11959 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e11960 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e11961 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e11962 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e11963 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b11964 := hb (x (-6) 7)
    have b11965 := hb (x (-5) 6)
    have b11966 := hb (x (-4) 5)
    have b11967 := hb (x (-3) 4)
    have b11968 := hb (x (-2) 11)
    have b11969 := hb (x (-1) 10)
    have b11970 := hb (x 0 9)
    have b11971 := hb (x 1 8)
    clear * - r11957 e11958 e11959 e11960 e11961 e11962 e11963 b11964 b11965 b11966 b11967 b11968 b11969 b11970 b11971 g24 g17 d11832 d11848 d11872 d11892 d11924
    omega
  have d11972 : (x (-6) 7 && x (-6) 14).toNat = 0 := by
    have r11973 := hand1 (x (-6) 7) (x (-6) 14)
    have b11974 := hb (x (-6) 7)
    have b11975 := hb (x (-6) 7 && x (-6) 14)
    clear * - r11973 b11974 b11975 d11956
    omega
  have d11976 : (x (-6) 7 && x (-6) 12).toNat = 0 := by
    have r11977 := hand1 (x (-6) 7) (x (-6) 12)
    have b11978 := hb (x (-6) 7)
    have b11979 := hb (x (-6) 7 && x (-6) 12)
    clear * - r11977 b11978 b11979 d11956
    omega
  have d11980 : (x (-6) 3 && x (-6) 7).toNat = 0 := by
    have r11981 := hand2 (x (-6) 3) (x (-6) 7)
    have b11982 := hb (x (-6) 7)
    have b11983 := hb (x (-6) 3 && x (-6) 7)
    clear * - r11981 b11982 b11983 d11956
    omega
  have d11984 : (x (-6) 5 && x (-6) 7).toNat = 0 := by
    have r11985 := hand2 (x (-6) 5) (x (-6) 7)
    have b11986 := hb (x (-6) 7)
    have b11987 := hb (x (-6) 5 && x (-6) 7)
    clear * - r11985 b11986 b11987 d11956
    omega
  cases h11988 : x 0 6
  · have f11989 : (x 0 6).toNat = 0 := by rw [h11988]; rfl
    cases h11990 : x 1 1
    · have f11991 : (x 1 1).toNat = 0 := by rw [h11990]; rfl
      have d11992 : (x 1 1 && x 1 14).toNat = 0 := by
        have r11993 := hand1 (x 1 1) (x 1 14)
        have b11994 := hb (x 1 1)
        have b11995 := hb (x 1 1 && x 1 14)
        clear * - r11993 b11994 b11995 f11991
        omega
      have d11996 : (x 1 1 && x 1 12).toNat = 0 := by
        have r11997 := hand1 (x 1 1) (x 1 12)
        have b11998 := hb (x 1 1)
        have b11999 := hb (x 1 1 && x 1 12)
        clear * - r11997 b11998 b11999 f11991
        omega
      have d12000 : (x 1 13).toNat = 0 := by
        have r12001 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
        have b12002 := hb (x 1 1)
        have b12003 := hb (x 1 13)
        clear * - r12001 b12002 b12003 f11991
        omega
      have d12004 : (x 1 2 && x 1 13).toNat = 0 := by
        have r12005 := hand2 (x 1 2) (x 1 13)
        have b12006 := hb (x 1 13)
        have b12007 := hb (x 1 2 && x 1 13)
        clear * - r12005 b12006 b12007 d12000
        omega
      have d12008 : (x 2 13).toNat = 1 := by
        have r12009 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12010 := hb (x 0 2)
        have b12011 := hb (x 2 13)
        have b12012 := hb (x 1 1 && x 1 14)
        clear * - r12009 b12010 b12011 b12012 d11992 g11
        omega
      have d12013 : (x 2 1).toNat = 1 := by
        have r12014 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
        have b12015 := hb (x 2 1)
        have b12016 := hb (x 2 13)
        clear * - r12014 b12015 b12016 d12008
        omega
      have d12017 : (x 3 14).toNat = 0 := by
        have r12018 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12019 := hb (x 2 1)
        have b12020 := hb (x 3 14)
        clear * - r12018 b12019 b12020 d12013
        omega
      have d12021 : (x 3 1 && x 3 14).toNat = 0 := by
        have r12022 := hand2 (x 3 1) (x 3 14)
        have b12023 := hb (x 3 14)
        have b12024 := hb (x 3 1 && x 3 14)
        clear * - r12022 b12023 b12024 d12017
        omega
      have d12025 : (x 4 13).toNat = 1 := by
        have r12026 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12027 := hb (x 2 2)
        have b12028 := hb (x 4 13)
        have b12029 := hb (x 3 1 && x 3 14)
        clear * - r12026 b12027 b12028 b12029 d12021 g25
        omega
      have d12030 : (x 4 1).toNat = 1 := by
        have r12031 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
        have b12032 := hb (x 4 1)
        have b12033 := hb (x 4 13)
        clear * - r12031 b12032 b12033 d12025
        omega
      have d12034 : (x 5 14).toNat = 0 := by
        have r12035 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12036 := hb (x 4 1)
        have b12037 := hb (x 5 14)
        clear * - r12035 b12036 b12037 d12030
        omega
      have d12038 : (x 5 1 && x 5 14).toNat = 0 := by
        have r12039 := hand2 (x 5 1) (x 5 14)
        have b12040 := hb (x 5 14)
        have b12041 := hb (x 5 1 && x 5 14)
        clear * - r12039 b12040 b12041 d12034
        omega
      have d12042 : (x 5 3 && x 5 14).toNat = 0 := by
        have r12043 := hand2 (x 5 3) (x 5 14)
        have b12044 := hb (x 5 14)
        have b12045 := hb (x 5 3 && x 5 14)
        clear * - r12043 b12044 b12045 d12034
        omega
      have d12046 : (x 5 2).toNat = 0 := by
        have r12047 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
        have b12048 := hb (x 5 2)
        have b12049 := hb (x 5 14)
        clear * - r12047 b12048 b12049 d12034
        omega
      have d12050 : (x 5 2 && x 5 13).toNat = 0 := by
        have r12051 := hand1 (x 5 2) (x 5 13)
        have b12052 := hb (x 5 2)
        have b12053 := hb (x 5 2 && x 5 13)
        clear * - r12051 b12052 b12053 d12046
        omega
      have d12054 : (x 3 2).toNat = 0 := by
        have r12055 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
        have b12056 := hb (x 3 2)
        have b12057 := hb (x 3 14)
        clear * - r12055 b12056 b12057 d12017
        omega
      have d12058 : (x (-1) 2).toNat = 1 := by
        have r12059 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12060 := hb (x (-1) 2)
        have b12061 := hb (x 1 13)
        have b12062 := hb (x 0 1 && x 0 14)
        clear * - r12059 b12060 b12061 b12062 d12000 g71
        omega
      have d12063 : (x (-1) 14).toNat = 1 := by
        have r12064 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
        have b12065 := hb (x (-1) 2)
        have b12066 := hb (x (-1) 14)
        clear * - r12064 b12065 b12066 d12058
        omega
      have d12067 : (x (-2) 1).toNat = 0 := by
        have r12068 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12069 := hb (x (-2) 1)
        have b12070 := hb (x (-1) 14)
        clear * - r12068 b12069 b12070 d12063
        omega
      have d12071 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
        have r12072 := hand1 (x (-2) 1) (x (-2) 14)
        have b12073 := hb (x (-2) 1)
        have b12074 := hb (x (-2) 1 && x (-2) 14)
        clear * - r12072 b12073 b12074 d12067
        omega
      have d12075 : (x (-2) 13).toNat = 0 := by
        have r12076 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
        have b12077 := hb (x (-2) 1)
        have b12078 := hb (x (-2) 13)
        clear * - r12076 b12077 b12078 d12067
        omega
      have d12079 : (x (-3) 2).toNat = 1 := by
        have r12080 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12081 := hb (x (-3) 2)
        have b12082 := hb (x (-1) 13)
        have b12083 := hb (x (-2) 1 && x (-2) 14)
        clear * - r12080 b12081 b12082 b12083 g9 d12071
        omega
      have d12084 : (x (-4) 2).toNat = 1 := by
        have r12085 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12086 := hb (x (-4) 2)
        have b12087 := hb (x (-2) 13)
        have b12088 := hb (x (-3) 1 && x (-3) 14)
        clear * - r12085 b12086 b12087 b12088 d12075 g70
        omega
      have d12089 : (x 5 12).toNat = 0 := by
        have r12090 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12091 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e12092 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b12093 := hb (x 2 3)
        have b12094 := hb (x 3 2)
        have b12095 := hb (x 4 13)
        have b12096 := hb (x 5 12)
        clear * - r12090 e12091 e12092 b12093 b12094 b12095 b12096 d12025 d12054
        omega
      have d12097 : (x 5 4).toNat = 0 := by
        have r12098 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
        have b12099 := hb (x 5 4)
        have b12100 := hb (x 5 12)
        clear * - r12098 b12099 b12100 d12089
        omega
      have d12101 : (x 2 3).toNat = 0 := by
        have r12102 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12103 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e12104 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b12105 := hb (x 2 3)
        have b12106 := hb (x 3 2)
        have b12107 := hb (x 4 13)
        have b12108 := hb (x 5 12)
        clear * - r12102 e12103 e12104 b12105 b12106 b12107 b12108 d12089 d12025 d12054
        omega
      have d12109 : (x 2 3 && x 2 14).toNat = 0 := by
        have r12110 := hand1 (x 2 3) (x 2 14)
        have b12111 := hb (x 2 3)
        have b12112 := hb (x 2 3 && x 2 14)
        clear * - r12110 b12111 b12112 d12101
        omega
      have d12113 : (x 2 11).toNat = 0 := by
        have r12114 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
        have b12115 := hb (x 2 3)
        have b12116 := hb (x 2 11)
        clear * - r12114 b12115 b12116 d12101
        omega
      have d12117 : (x 3 12).toNat = 0 := by
        have r12118 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12119 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
        have e12120 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
        have b12121 := hb (x 0 3)
        have b12122 := hb (x 1 2)
        have b12123 := hb (x 2 13)
        have b12124 := hb (x 3 12)
        clear * - r12118 e12119 e12120 b12121 b12122 b12123 b12124 d12008 g12
        omega
      have d12125 : (x 3 4).toNat = 0 := by
        have r12126 : (x 3 4).toNat ≤ (x 3 12).toNat := himp _ _ (hp4 3)
        have b12127 := hb (x 3 4)
        have b12128 := hb (x 3 12)
        clear * - r12126 b12127 b12128 d12117
        omega
      have d12129 : (x 1 12).toNat = 0 := by
        have r12130 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12131 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e12132 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b12133 := hb (x (-2) 3)
        have b12134 := hb (x (-1) 2)
        have b12135 := hb (x 0 13)
        have b12136 := hb (x 1 12)
        clear * - r12130 e12131 e12132 b12133 b12134 b12135 b12136 g21 d12058
        omega
      have d12137 : (x 1 4).toNat = 0 := by
        have r12138 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
        have b12139 := hb (x 1 4)
        have b12140 := hb (x 1 12)
        clear * - r12138 b12139 b12140 d12129
        omega
      have d12141 : (x (-1) 12).toNat = 0 := by
        have r12142 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12143 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e12144 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b12145 := hb (x (-4) 3)
        have b12146 := hb (x (-3) 2)
        have b12147 := hb (x (-2) 13)
        have b12148 := hb (x (-1) 12)
        clear * - r12142 e12143 e12144 b12145 b12146 b12147 b12148 d12075 d12079
        omega
      have d12149 : (x (-1) 4).toNat = 0 := by
        have r12150 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
        have b12151 := hb (x (-1) 4)
        have b12152 := hb (x (-1) 12)
        clear * - r12150 b12151 b12152 d12141
        omega
      have d12153 : (x (-2) 12).toNat = 0 := by
        have r12154 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12155 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e12156 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have b12157 := hb (x (-5) 3)
        have b12158 := hb (x (-4) 2)
        have b12159 := hb (x (-3) 13)
        have b12160 := hb (x (-2) 12)
        clear * - r12154 e12155 e12156 b12157 b12158 b12159 b12160 g3 d12084
        omega
      have d12161 : (x (-2) 4).toNat = 0 := by
        have r12162 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
        have b12163 := hb (x (-2) 4)
        have b12164 := hb (x (-2) 12)
        clear * - r12162 b12163 b12164 d12153
        omega
      have d12165 : (x 5 11).toNat = 1 := by
        have r12166 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12167 := hb (x 1 4)
        have b12168 := hb (x 5 11)
        have b12169 := hb (x 4 1 && x 4 12)
        have b12170 := hb (x 3 2 && x 3 13)
        have b12171 := hb (x 2 3 && x 2 14)
        clear * - r12166 b12167 b12168 b12169 b12170 b12171 g68 g69 d12109 d12137
        omega
      have d12172 : (x 5 3).toNat = 1 := by
        have r12173 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
        have b12174 := hb (x 5 3)
        have b12175 := hb (x 5 11)
        clear * - r12173 b12174 b12175 d12165
        omega
      have d12176 : (x 8 12).toNat = 0 := by
        have r12177 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12178 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e12179 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have b12180 := hb (x 5 3)
        have b12181 := hb (x 6 2)
        have b12182 := hb (x 7 13)
        have b12183 := hb (x 8 12)
        clear * - r12177 e12178 e12179 b12180 b12181 b12182 b12183 d12172
        omega
      have d12184 : (x 8 1 && x 8 12).toNat = 0 := by
        have r12185 := hand2 (x 8 1) (x 8 12)
        have b12186 := hb (x 8 12)
        have b12187 := hb (x 8 1 && x 8 12)
        clear * - r12185 b12186 b12187 d12176
        omega
      have d12188 : (x 7 13).toNat = 0 := by
        have r12189 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12190 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e12191 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have b12192 := hb (x 5 3)
        have b12193 := hb (x 6 2)
        have b12194 := hb (x 7 13)
        have b12195 := hb (x 8 12)
        clear * - r12189 e12190 e12191 b12192 b12193 b12194 b12195 d12176 d12172
        omega
      have d12196 : (x 7 2 && x 7 13).toNat = 0 := by
        have r12197 := hand2 (x 7 2) (x 7 13)
        have b12198 := hb (x 7 13)
        have b12199 := hb (x 7 2 && x 7 13)
        clear * - r12197 b12198 b12199 d12188
        omega
      have d12200 : (x 6 1 && x 6 14).toNat = 1 := by
        have r12201 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12202 := hb (x 5 2)
        have b12203 := hb (x 7 13)
        have b12204 := hb (x 6 1 && x 6 14)
        clear * - r12201 b12202 b12203 b12204 d12188 d12046
        omega
      have d12205 : (x 6 14).toNat = 1 := by
        have r12206 := hand2 (x 6 1) (x 6 14)
        have b12207 := hb (x 6 14)
        have b12208 := hb (x 6 1 && x 6 14)
        clear * - r12206 b12207 b12208 d12200
        omega
      have d12209 : (x 5 1).toNat = 0 := by
        have r12210 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12211 := hb (x 5 1)
        have b12212 := hb (x 6 14)
        clear * - r12210 b12211 b12212 d12205
        omega
      have d12213 : (x 5 13).toNat = 0 := by
        have r12214 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
        have b12215 := hb (x 5 1)
        have b12216 := hb (x 5 13)
        clear * - r12214 b12215 b12216 d12209
        omega
      have d12217 : (x 6 1).toNat = 1 := by
        have r12218 := hand1 (x 6 1) (x 6 14)
        have b12219 := hb (x 6 1)
        have b12220 := hb (x 6 1 && x 6 14)
        clear * - r12218 b12219 b12220 d12200
        omega
      have d12221 : (x 7 14).toNat = 0 := by
        have r12222 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12223 := hb (x 6 1)
        have b12224 := hb (x 7 14)
        clear * - r12222 b12223 b12224 d12217
        omega
      have d12225 : (x 7 1 && x 7 14).toNat = 0 := by
        have r12226 := hand2 (x 7 1) (x 7 14)
        have b12227 := hb (x 7 14)
        have b12228 := hb (x 7 1 && x 7 14)
        clear * - r12226 b12227 b12228 d12221
        omega
      have d12229 : (x 7 2).toNat = 0 := by
        have r12230 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
        have b12231 := hb (x 7 2)
        have b12232 := hb (x 7 14)
        clear * - r12230 b12231 b12232 d12221
        omega
      have d12233 : (x 6 2).toNat = 0 := by
        have r12234 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12235 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e12236 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have b12237 := hb (x 5 3)
        have b12238 := hb (x 6 2)
        have b12239 := hb (x 7 13)
        have b12240 := hb (x 8 12)
        clear * - r12234 e12235 e12236 b12237 b12238 b12239 b12240 d12176 d12188 d12172
        omega
      have d12241 : (x 6 2 && x 6 13).toNat = 0 := by
        have r12242 := hand1 (x 6 2) (x 6 13)
        have b12243 := hb (x 6 2)
        have b12244 := hb (x 6 2 && x 6 13)
        clear * - r12242 b12243 b12244 d12233
        omega
      have d12245 : (x 8 13).toNat = 1 := by
        have r12246 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12247 := hb (x 6 2)
        have b12248 := hb (x 8 13)
        have b12249 := hb (x 7 1 && x 7 14)
        clear * - r12246 b12247 b12248 b12249 d12225 d12233
        omega
      have d12250 : (x 8 1).toNat = 1 := by
        have r12251 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
        have b12252 := hb (x 8 1)
        have b12253 := hb (x 8 13)
        clear * - r12251 b12252 b12253 d12245
        omega
      have d12254 : (x 9 14).toNat = 0 := by
        have r12255 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12256 := hb (x 8 1)
        have b12257 := hb (x 9 14)
        clear * - r12255 b12256 b12257 d12250
        omega
      have d12258 : (x 9 1 && x 9 14).toNat = 0 := by
        have r12259 := hand2 (x 9 1) (x 9 14)
        have b12260 := hb (x 9 14)
        have b12261 := hb (x 9 1 && x 9 14)
        clear * - r12259 b12260 b12261 d12254
        omega
      have d12262 : (x 9 2).toNat = 0 := by
        have r12263 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
        have b12264 := hb (x 9 2)
        have b12265 := hb (x 9 14)
        clear * - r12263 b12264 b12265 d12254
        omega
      have d12266 : (x 9 12).toNat = 0 := by
        have r12267 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12268 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
        have e12269 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
        have b12270 := hb (x 6 3)
        have b12271 := hb (x 7 2)
        have b12272 := hb (x 8 13)
        have b12273 := hb (x 9 12)
        clear * - r12267 e12268 e12269 b12270 b12271 b12272 b12273 d12245 d12229
        omega
      have d12274 : (x 6 3).toNat = 0 := by
        have r12275 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12276 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
        have e12277 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
        have b12278 := hb (x 6 3)
        have b12279 := hb (x 7 2)
        have b12280 := hb (x 8 13)
        have b12281 := hb (x 9 12)
        clear * - r12275 e12276 e12277 b12278 b12279 b12280 b12281 d12266 d12245 d12229
        omega
      have d12282 : (x 6 3 && x 6 14).toNat = 0 := by
        have r12283 := hand1 (x 6 3) (x 6 14)
        have b12284 := hb (x 6 3)
        have b12285 := hb (x 6 3 && x 6 14)
        clear * - r12283 b12284 b12285 d12274
        omega
      have d12286 : (x 9 11).toNat = 1 := by
        have r12287 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12288 := hb (x 5 4)
        have b12289 := hb (x 9 11)
        have b12290 := hb (x 8 1 && x 8 12)
        have b12291 := hb (x 7 2 && x 7 13)
        have b12292 := hb (x 6 3 && x 6 14)
        clear * - r12287 b12288 b12289 b12290 b12291 b12292 d12184 d12196 d12282 d12097
        omega
      have d12293 : (x 9 3).toNat = 1 := by
        have r12294 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
        have b12295 := hb (x 9 3)
        have b12296 := hb (x 9 11)
        clear * - r12294 b12295 b12296 d12286
        omega
      have d12297 : (x 12 12).toNat = 0 := by
        have r12298 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12299 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
        have e12300 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
        have b12301 := hb (x 9 3)
        have b12302 := hb (x 10 2)
        have b12303 := hb (x 11 13)
        have b12304 := hb (x 12 12)
        clear * - r12298 e12299 e12300 b12301 b12302 b12303 b12304 d12293
        omega
      have d12305 : (x 11 13).toNat = 0 := by
        have r12306 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12307 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
        have e12308 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
        have b12309 := hb (x 9 3)
        have b12310 := hb (x 10 2)
        have b12311 := hb (x 11 13)
        have b12312 := hb (x 12 12)
        clear * - r12306 e12307 e12308 b12309 b12310 b12311 b12312 d12297 d12293
        omega
      have d12313 : (x 10 1 && x 10 14).toNat = 1 := by
        have r12314 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12315 := hb (x 9 2)
        have b12316 := hb (x 11 13)
        have b12317 := hb (x 10 1 && x 10 14)
        clear * - r12314 b12315 b12316 b12317 d12305 d12262
        omega
      have d12318 : (x 10 14).toNat = 1 := by
        have r12319 := hand2 (x 10 1) (x 10 14)
        have b12320 := hb (x 10 14)
        have b12321 := hb (x 10 1 && x 10 14)
        clear * - r12319 b12320 b12321 d12313
        omega
      have d12322 : (x 9 1).toNat = 0 := by
        have r12323 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12324 := hb (x 9 1)
        have b12325 := hb (x 10 14)
        clear * - r12323 b12324 b12325 d12318
        omega
      have d12326 : (x 9 13).toNat = 0 := by
        have r12327 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
        have b12328 := hb (x 9 1)
        have b12329 := hb (x 9 13)
        clear * - r12327 b12328 b12329 d12322
        omega
      have d12330 : (x 8 1 && x 8 14).toNat = 1 := by
        have r12331 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12332 := hb (x 7 2)
        have b12333 := hb (x 9 13)
        have b12334 := hb (x 8 1 && x 8 14)
        clear * - r12331 b12332 b12333 b12334 d12326 d12229
        omega
      have d12335 : (x 8 14).toNat = 1 := by
        have r12336 := hand2 (x 8 1) (x 8 14)
        have b12337 := hb (x 8 14)
        have b12338 := hb (x 8 1 && x 8 14)
        clear * - r12336 b12337 b12338 d12330
        omega
      have d12339 : (x 7 1).toNat = 0 := by
        have r12340 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12341 := hb (x 7 1)
        have b12342 := hb (x 8 14)
        clear * - r12340 b12341 b12342 d12335
        omega
      have d12343 : (x 7 1 && x 7 12).toNat = 0 := by
        have r12344 := hand1 (x 7 1) (x 7 12)
        have b12345 := hb (x 7 1)
        have b12346 := hb (x 7 1 && x 7 12)
        clear * - r12344 b12345 b12346 d12339
        omega
      have d12347 : (x 8 11).toNat = 1 := by
        have r12348 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12349 := hb (x 4 4)
        have b12350 := hb (x 8 11)
        have b12351 := hb (x 7 1 && x 7 12)
        have b12352 := hb (x 6 2 && x 6 13)
        have b12353 := hb (x 5 3 && x 5 14)
        clear * - r12348 b12349 b12350 b12351 b12352 b12353 d12343 d12241 d12042 g29
        omega
      have d12354 : (x 8 3).toNat = 1 := by
        have r12355 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
        have b12356 := hb (x 8 3)
        have b12357 := hb (x 8 11)
        clear * - r12355 b12356 b12357 d12347
        omega
      have d12358 : (x 11 12).toNat = 0 := by
        have r12359 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12360 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e12361 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b12362 := hb (x 8 3)
        have b12363 := hb (x 9 2)
        have b12364 := hb (x 10 13)
        have b12365 := hb (x 11 12)
        clear * - r12359 e12360 e12361 b12362 b12363 b12364 b12365 d12262 d12354
        omega
      have d12366 : (x 10 13).toNat = 0 := by
        have r12367 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12368 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e12369 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b12370 := hb (x 8 3)
        have b12371 := hb (x 9 2)
        have b12372 := hb (x 10 13)
        have b12373 := hb (x 11 12)
        clear * - r12367 e12368 e12369 b12370 b12371 b12372 b12373 d12358 d12262 d12354
        omega
      have d12374 : (x 8 2).toNat = 1 := by
        have r12375 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12376 := hb (x 8 2)
        have b12377 := hb (x 10 13)
        have b12378 := hb (x 9 1 && x 9 14)
        clear * - r12375 b12376 b12377 b12378 d12366 d12258
        omega
      have d12379 : (x 10 12).toNat = 0 := by
        have r12380 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12381 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
        have e12382 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
        have b12383 := hb (x 7 3)
        have b12384 := hb (x 8 2)
        have b12385 := hb (x 9 13)
        have b12386 := hb (x 10 12)
        clear * - r12380 e12381 e12382 b12383 b12384 b12385 b12386 d12326 d12374
        omega
      have d12387 : (x 7 3).toNat = 0 := by
        have r12388 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12389 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
        have e12390 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
        have b12391 := hb (x 7 3)
        have b12392 := hb (x 8 2)
        have b12393 := hb (x 9 13)
        have b12394 := hb (x 10 12)
        clear * - r12388 e12389 e12390 b12391 b12392 b12393 b12394 d12379 d12326 d12374
        omega
      have d12395 : (x 7 11).toNat = 0 := by
        have r12396 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
        have b12397 := hb (x 7 3)
        have b12398 := hb (x 7 11)
        clear * - r12396 b12397 b12398 d12387
        omega
      have d12399 : (x (-1) 3 && x (-1) 14).toNat = 1 := by
        have r12400 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := by have q := hcov11 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12401 := hb (x (-2) 4)
        have b12402 := hb (x 2 11)
        have b12403 := hb (x 1 1 && x 1 12)
        have b12404 := hb (x 0 2 && x 0 13)
        have b12405 := hb (x (-1) 3 && x (-1) 14)
        clear * - r12400 b12401 b12402 b12403 b12404 b12405 d12113 d11996 g66 d12161
        omega
      have d12406 : (x (-1) 3).toNat = 1 := by
        have r12407 := hand1 (x (-1) 3) (x (-1) 14)
        have b12408 := hb (x (-1) 3)
        have b12409 := hb (x (-1) 3 && x (-1) 14)
        clear * - r12407 b12408 b12409 d12399
        omega
      have d12410 : (x 2 12).toNat = 0 := by
        have r12411 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12412 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
        have e12413 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
        have b12414 := hb (x (-1) 3)
        have b12415 := hb (x 0 2)
        have b12416 := hb (x 1 13)
        have b12417 := hb (x 2 12)
        clear * - r12411 e12412 e12413 b12414 b12415 b12416 b12417 d12000 g11 d12406
        omega
      have d12418 : (x 2 1 && x 2 12).toNat = 0 := by
        have r12419 := hand2 (x 2 1) (x 2 12)
        have b12420 := hb (x 2 12)
        have b12421 := hb (x 2 1 && x 2 12)
        clear * - r12419 b12420 b12421 d12410
        omega
      have d12422 : (x 3 11).toNat = 1 := by
        have r12423 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12424 := hb (x (-1) 4)
        have b12425 := hb (x 3 11)
        have b12426 := hb (x 2 1 && x 2 12)
        have b12427 := hb (x 1 2 && x 1 13)
        have b12428 := hb (x 0 3 && x 0 14)
        clear * - r12423 b12424 b12425 b12426 b12427 b12428 d12418 d12004 g67 d12149
        omega
      have d12429 : (x 3 3).toNat = 1 := by
        have r12430 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
        have b12431 := hb (x 3 3)
        have b12432 := hb (x 3 11)
        clear * - r12430 b12431 b12432 d12422
        omega
      have d12433 : (x 6 12).toNat = 0 := by
        have r12434 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12435 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
        have e12436 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
        have b12437 := hb (x 3 3)
        have b12438 := hb (x 4 2)
        have b12439 := hb (x 5 13)
        have b12440 := hb (x 6 12)
        clear * - r12434 e12435 e12436 b12437 b12438 b12439 b12440 d12213 d12429
        omega
      have d12441 : (x 6 1 && x 6 12).toNat = 0 := by
        have r12442 := hand2 (x 6 1) (x 6 12)
        have b12443 := hb (x 6 12)
        have b12444 := hb (x 6 1 && x 6 12)
        clear * - r12442 b12443 b12444 d12433
        omega
      have d12445 : (x 4 3 && x 4 14).toNat = 1 := by
        have r12446 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12447 := hb (x 3 4)
        have b12448 := hb (x 7 11)
        have b12449 := hb (x 6 1 && x 6 12)
        have b12450 := hb (x 5 2 && x 5 13)
        have b12451 := hb (x 4 3 && x 4 14)
        clear * - r12446 b12447 b12448 b12449 b12450 b12451 d12395 d12441 d12050 d12125
        omega
      have d12452 : (x 4 3).toNat = 1 := by
        have r12453 := hand1 (x 4 3) (x 4 14)
        have b12454 := hb (x 4 3)
        have b12455 := hb (x 4 3 && x 4 14)
        clear * - r12453 b12454 b12455 d12445
        omega
      have d12456 : (x 7 12).toNat = 0 := by
        have r12457 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12458 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
        have e12459 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
        have b12460 := hb (x 4 3)
        have b12461 := hb (x 5 2)
        have b12462 := hb (x 6 13)
        have b12463 := hb (x 7 12)
        clear * - r12457 e12458 e12459 b12460 b12461 b12462 b12463 d12046 d12452
        omega
      have d12464 : (x 6 13).toNat = 0 := by
        have r12465 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12466 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
        have e12467 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
        have b12468 := hb (x 4 3)
        have b12469 := hb (x 5 2)
        have b12470 := hb (x 6 13)
        have b12471 := hb (x 7 12)
        clear * - r12465 e12466 e12467 b12468 b12469 b12470 b12471 d12456 d12046 d12452
        omega
      have d12472 : (x 4 2).toNat = 1 := by
        have r12473 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12474 := hb (x 4 2)
        have b12475 := hb (x 6 13)
        have b12476 := hb (x 5 1 && x 5 14)
        clear * - r12473 b12474 b12475 b12476 d12464 d12038
        omega
      have r12477 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e12478 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e12479 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b12480 := hb (x 3 3)
      have b12481 := hb (x 4 2)
      have b12482 := hb (x 5 13)
      have b12483 := hb (x 6 12)
      linarith only [r12477, e12478, e12479, b12480, b12481, b12482, b12483, d12433, d12213, d12472, d12429]
    · have f12484 : (x 1 1).toNat = 1 := by rw [h11990]; rfl
      have d12485 : (x 2 14).toNat = 0 := by
        have r12486 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12487 := hb (x 1 1)
        have b12488 := hb (x 2 14)
        clear * - r12486 b12487 b12488 f12484
        omega
      have d12489 : (x 2 1 && x 2 14).toNat = 0 := by
        have r12490 := hand2 (x 2 1) (x 2 14)
        have b12491 := hb (x 2 14)
        have b12492 := hb (x 2 1 && x 2 14)
        clear * - r12490 b12491 b12492 d12485
        omega
      have d12493 : (x 2 3 && x 2 14).toNat = 0 := by
        have r12494 := hand2 (x 2 3) (x 2 14)
        have b12495 := hb (x 2 14)
        have b12496 := hb (x 2 3 && x 2 14)
        clear * - r12494 b12495 b12496 d12485
        omega
      have d12497 : (x 2 5 && x 2 14).toNat = 0 := by
        have r12498 := hand2 (x 2 5) (x 2 14)
        have b12499 := hb (x 2 14)
        have b12500 := hb (x 2 5 && x 2 14)
        clear * - r12498 b12499 b12500 d12485
        omega
      have d12501 : (x 2 6).toNat = 0 := by
        have r12502 : (x 2 6).toNat ≤ (x 2 14).toNat := himp _ _ (hp6 2)
        have b12503 := hb (x 2 6)
        have b12504 := hb (x 2 14)
        clear * - r12502 b12503 b12504 d12485
        omega
      have d12505 : (x 2 6 && x 2 12).toNat = 0 := by
        have r12506 := hand1 (x 2 6) (x 2 12)
        have b12507 := hb (x 2 6)
        have b12508 := hb (x 2 6 && x 2 12)
        clear * - r12506 b12507 b12508 d12501
        omega
      have d12509 : (x 1 2).toNat = 1 := by
        have r12510 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12511 := hb (x 1 2)
        have b12512 := hb (x 3 13)
        have b12513 := hb (x 2 1 && x 2 14)
        clear * - r12510 b12511 b12512 b12513 g28 d12489
        omega
      have d12514 : (x 3 12).toNat = 0 := by
        have r12515 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12516 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
        have e12517 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
        have b12518 := hb (x 0 3)
        have b12519 := hb (x 1 2)
        have b12520 := hb (x 2 13)
        have b12521 := hb (x 3 12)
        clear * - r12515 e12516 e12517 b12518 b12519 b12520 b12521 d12509 g12
        omega
      have d12522 : (x 3 2 && x 3 12).toNat = 0 := by
        have r12523 := hand2 (x 3 2) (x 3 12)
        have b12524 := hb (x 3 12)
        have b12525 := hb (x 3 2 && x 3 12)
        clear * - r12523 b12524 b12525 d12514
        omega
      have d12526 : (x 3 4).toNat = 0 := by
        have r12527 : (x 3 4).toNat ≤ (x 3 12).toNat := himp _ _ (hp4 3)
        have b12528 := hb (x 3 4)
        have b12529 := hb (x 3 12)
        clear * - r12527 b12528 b12529 d12514
        omega
      have d12530 : (x 2 13).toNat = 0 := by
        have r12531 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12532 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
        have e12533 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
        have b12534 := hb (x 0 3)
        have b12535 := hb (x 1 2)
        have b12536 := hb (x 2 13)
        have b12537 := hb (x 3 12)
        clear * - r12531 e12532 e12533 b12534 b12535 b12536 b12537 d12514 d12509 g12
        omega
      have d12538 : (x 2 3 && x 2 13).toNat = 0 := by
        have r12539 := hand2 (x 2 3) (x 2 13)
        have b12540 := hb (x 2 13)
        have b12541 := hb (x 2 3 && x 2 13)
        clear * - r12539 b12540 b12541 d12530
        omega
      have d12542 : (x 2 5).toNat = 0 := by
        have r12543 : (x 2 5).toNat ≤ (x 2 13).toNat := himp _ _ (hp5 2)
        have b12544 := hb (x 2 5)
        have b12545 := hb (x 2 13)
        clear * - r12543 b12544 b12545 d12530
        omega
      cases h12546 : x (-1) 2
      · have f12547 : (x (-1) 2).toNat = 0 := by rw [h12546]; rfl
        have d12548 : (x 1 13).toNat = 1 := by
          have r12549 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12550 := hb (x (-1) 2)
          have b12551 := hb (x 1 13)
          have b12552 := hb (x 0 1 && x 0 14)
          clear * - r12549 b12550 b12551 b12552 g71 f12547
          omega
        have d12553 : (x 2 12).toNat = 0 := by
          have r12554 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12555 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
          have e12556 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
          have b12557 := hb (x (-1) 3)
          have b12558 := hb (x 0 2)
          have b12559 := hb (x 1 13)
          have b12560 := hb (x 2 12)
          clear * - r12554 e12555 e12556 b12557 b12558 b12559 b12560 d12548 g11
          omega
        have d12561 : (x (-1) 3).toNat = 0 := by
          have r12562 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12563 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
          have e12564 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
          have b12565 := hb (x (-1) 3)
          have b12566 := hb (x 0 2)
          have b12567 := hb (x 1 13)
          have b12568 := hb (x 2 12)
          clear * - r12562 e12563 e12564 b12565 b12566 b12567 b12568 d12553 d12548 g11
          omega
        have d12569 : (x (-1) 11).toNat = 0 := by
          have r12570 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
          have b12571 := hb (x (-1) 3)
          have b12572 := hb (x (-1) 11)
          clear * - r12570 b12571 b12572 d12561
          omega
        cases h12573 : x (-1) 4
        · have f12574 : (x (-1) 4).toNat = 0 := by rw [h12573]; rfl
          cases h12575 : x 1 4
          · have f12576 : (x 1 4).toNat = 0 := by rw [h12575]; rfl
            have d12577 : (x 1 4 && x 1 14).toNat = 0 := by
              have r12578 := hand1 (x 1 4) (x 1 14)
              have b12579 := hb (x 1 4)
              have b12580 := hb (x 1 4 && x 1 14)
              clear * - r12578 b12579 b12580 f12576
              omega
            have d12581 : (x 5 11).toNat = 1 := by
              have r12582 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b12583 := hb (x 1 4)
              have b12584 := hb (x 5 11)
              have b12585 := hb (x 4 1 && x 4 12)
              have b12586 := hb (x 3 2 && x 3 13)
              have b12587 := hb (x 2 3 && x 2 14)
              clear * - r12582 b12583 b12584 b12585 b12586 b12587 g68 g69 d12493 f12576
              omega
            have d12588 : (x 5 3).toNat = 1 := by
              have r12589 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
              have b12590 := hb (x 5 3)
              have b12591 := hb (x 5 11)
              clear * - r12589 b12590 b12591 d12581
              omega
            have d12592 : (x 8 12).toNat = 0 := by
              have r12593 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e12594 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
              have e12595 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
              have b12596 := hb (x 5 3)
              have b12597 := hb (x 6 2)
              have b12598 := hb (x 7 13)
              have b12599 := hb (x 8 12)
              clear * - r12593 e12594 e12595 b12596 b12597 b12598 b12599 d12588
              omega
            have d12600 : (x 8 4).toNat = 0 := by
              have r12601 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
              have b12602 := hb (x 8 4)
              have b12603 := hb (x 8 12)
              clear * - r12601 b12602 b12603 d12592
              omega
            have d12604 : (x 8 4 && x 8 14).toNat = 0 := by
              have r12605 := hand1 (x 8 4) (x 8 14)
              have b12606 := hb (x 8 4)
              have b12607 := hb (x 8 4 && x 8 14)
              clear * - r12605 b12606 b12607 d12600
              omega
            have d12608 : (x 7 13).toNat = 0 := by
              have r12609 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e12610 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
              have e12611 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
              have b12612 := hb (x 5 3)
              have b12613 := hb (x 6 2)
              have b12614 := hb (x 7 13)
              have b12615 := hb (x 8 12)
              clear * - r12609 e12610 e12611 b12612 b12613 b12614 b12615 d12592 d12588
              omega
            have d12616 : (x 7 5).toNat = 0 := by
              have r12617 : (x 7 5).toNat ≤ (x 7 13).toNat := himp _ _ (hp5 7)
              have b12618 := hb (x 7 5)
              have b12619 := hb (x 7 13)
              clear * - r12617 b12618 b12619 d12608
              omega
            have d12620 : (x 6 2).toNat = 0 := by
              have r12621 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e12622 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
              have e12623 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
              have b12624 := hb (x 5 3)
              have b12625 := hb (x 6 2)
              have b12626 := hb (x 7 13)
              have b12627 := hb (x 8 12)
              clear * - r12621 e12622 e12623 b12624 b12625 b12626 b12627 d12592 d12608 d12588
              omega
            have d12628 : (x 6 2 && x 6 8).toNat = 0 := by
              have r12629 := hand1 (x 6 2) (x 6 8)
              have b12630 := hb (x 6 2)
              have b12631 := hb (x 6 2 && x 6 8)
              clear * - r12629 b12630 b12631 d12620
              omega
            have d12632 : (x 6 2 && x 6 6).toNat = 0 := by
              have r12633 := hand1 (x 6 2) (x 6 6)
              have b12634 := hb (x 6 2)
              have b12635 := hb (x 6 2 && x 6 6)
              clear * - r12633 b12634 b12635 d12620
              omega
            have d12636 : (x 6 10).toNat = 0 := by
              have r12637 : (x 6 10).toNat ≤ (x 6 2).toNat := himp _ _ (hp10 6)
              have b12638 := hb (x 6 2)
              have b12639 := hb (x 6 10)
              clear * - r12637 b12638 b12639 d12620
              omega
            have d12640 : (x 6 1 && x 6 10).toNat = 0 := by
              have r12641 := hand2 (x 6 1) (x 6 10)
              have b12642 := hb (x 6 10)
              have b12643 := hb (x 6 1 && x 6 10)
              clear * - r12641 b12642 b12643 d12636
              omega
            have d12644 : (x 8 8).toNat = 0 := by
              have r12645 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e12646 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e12647 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e12648 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e12649 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e12650 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e12651 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b12652 := hb (x 1 7)
              have b12653 := hb (x 2 6)
              have b12654 := hb (x 3 5)
              have b12655 := hb (x 4 4)
              have b12656 := hb (x 5 11)
              have b12657 := hb (x 6 10)
              have b12658 := hb (x 7 9)
              have b12659 := hb (x 8 8)
              clear * - r12645 e12646 e12647 e12648 e12649 e12650 e12651 b12652 b12653 b12654 b12655 b12656 b12657 b12658 b12659 d12636 d12581 g29 g27 d12501
              omega
            have d12660 : (x 7 9).toNat = 0 := by
              have r12661 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e12662 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e12663 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e12664 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e12665 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e12666 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e12667 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b12668 := hb (x 1 7)
              have b12669 := hb (x 2 6)
              have b12670 := hb (x 3 5)
              have b12671 := hb (x 4 4)
              have b12672 := hb (x 5 11)
              have b12673 := hb (x 6 10)
              have b12674 := hb (x 7 9)
              have b12675 := hb (x 8 8)
              clear * - r12661 e12662 e12663 e12664 e12665 e12666 e12667 b12668 b12669 b12670 b12671 b12672 b12673 b12674 b12675 d12644 d12636 d12581 g29 g27 d12501
              omega
            have d12676 : (x 1 7).toNat = 0 := by
              have r12677 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e12678 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e12679 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e12680 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e12681 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e12682 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e12683 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b12684 := hb (x 1 7)
              have b12685 := hb (x 2 6)
              have b12686 := hb (x 3 5)
              have b12687 := hb (x 4 4)
              have b12688 := hb (x 5 11)
              have b12689 := hb (x 6 10)
              have b12690 := hb (x 7 9)
              have b12691 := hb (x 8 8)
              clear * - r12677 e12678 e12679 e12680 e12681 e12682 e12683 b12684 b12685 b12686 b12687 b12688 b12689 b12690 b12691 d12644 d12660 d12636 d12581 g29 g27 d12501
              omega
            have d12692 : (x 1 7 && x 1 13).toNat = 0 := by
              have r12693 := hand1 (x 1 7) (x 1 13)
              have b12694 := hb (x 1 7)
              have b12695 := hb (x 1 7 && x 1 13)
              clear * - r12693 b12694 b12695 d12676
              omega
            have d12696 : (x 1 7 && x 1 11).toNat = 0 := by
              have r12697 := hand1 (x 1 7) (x 1 11)
              have b12698 := hb (x 1 7)
              have b12699 := hb (x 1 7 && x 1 11)
              clear * - r12697 b12698 b12699 d12676
              omega
            have d12700 : (x 1 3 && x 1 7).toNat = 0 := by
              have r12701 := hand2 (x 1 3) (x 1 7)
              have b12702 := hb (x 1 7)
              have b12703 := hb (x 1 3 && x 1 7)
              clear * - r12701 b12702 b12703 d12676
              omega
            have r12704 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r12705 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r12706 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r12707 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e12708 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
            have e12709 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
            have e12710 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
            have e12711 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
            have e12712 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
            have e12713 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
            have r12714 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e12715 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
            have e12716 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
            have e12717 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
            have e12718 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
            have e12719 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
            have e12720 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
            have r12721 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e12722 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
            have e12723 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
            have e12724 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
            have e12725 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
            have e12726 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
            have e12727 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
            have r12728 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r12729 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e12730 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
            have e12731 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
            have r12732 : 1 ≤ (x 8 4).toNat + (x 7 1 && x 7 5).toNat + (x 6 2 && x 6 6).toNat + (x 5 3 && x 5 7).toNat + (x 4 4 && x 4 8).toNat + (x 3 5 && x 3 9).toNat + (x 2 6 && x 2 10).toNat + (x 1 7 && x 1 11).toNat + (x 0 8 && x 0 12).toNat + (x (-1) 9 && x (-1) 13).toNat + (x (-2) 10 && x (-2) 14).toNat + (x (-3) 11).toNat := by have q := hcov4 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e12733 : (x 7 1 && x 7 5).toNat = (x 7 5).toNat := handr _ _ (fun h => hp13 7 (hp5 7 (h)))
            have e12734 : (x (-2) 10 && x (-2) 14).toNat = (x (-2) 10).toNat := handl _ _ (fun h => hp2 (-2) (hp10 (-2) (h)))
            have r12735 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r12736 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r12737 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r12738 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r12739 : 1 ≤ (x 12 10).toNat + (x 11 1 && x 11 11).toNat + (x 10 2 && x 10 12).toNat + (x 9 3 && x 9 13).toNat + (x 8 4 && x 8 14).toNat + (x 7 5).toNat := by have q := hcov10 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r12740 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r12741 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
            have r12742 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
            have r12743 : (x 12 10).toNat ≤ (x 12 2).toNat := himp _ _ (hp10 12)
            have r12744 := hand2 (x (-2) 6) (x (-2) 10)
            have r12745 := hand1 (x (-4) 8) (x (-4) 12)
            have r12746 := hand1 (x (-5) 9) (x (-5) 13)
            have r12747 := hand2 (x 5 3) (x 5 7)
            have r12748 := hand2 (x 7 1) (x 7 7)
            have r12749 := hand2 (x 5 3) (x 5 9)
            have r12750 := hand1 (x (-4) 4) (x (-4) 13)
            have r12751 := hand1 (x (-5) 5) (x (-5) 14)
            have r12752 := hand1 (x 5 2) (x 5 11)
            have r12753 := hand2 (x 4 1) (x 4 11)
            have r12754 := hand1 (x 11 1) (x 11 11)
            have r12755 := hand1 (x 10 2) (x 10 12)
            have r12756 := hand1 (x 9 3) (x 9 13)
            have r12757 := hand1 (x 3 1) (x 3 14)
            linarith only [r12704, r12705, r12706, r12707, e12708, e12709, e12710, e12711, e12712, e12713, r12714, e12715, e12716, e12717, e12718, e12719, e12720, r12721, e12722, e12723, e12724, e12725, e12726, e12727, r12728, r12729, e12730, e12731, r12732, e12733, e12734, r12735, r12736, r12737, r12738, r12739, r12740, r12741, r12742, r12743, r12744, r12745, r12746, r12747, r12748, r12749, r12750, r12751, r12752, r12753, r12754, r12755, r12756, r12757, g2, g5, g7, g8, g9, g13, g14, g15, g16, g17, g20, g22, g23, d12548, g25, d12542, g26, d12553, d12526, g27, g29, d12616, d12660, d12600, g30, d12700, g31, g32, g33, d12632, g34, g35, g36, d12696, g37, g38, d12628, g46, g47, d12505, d12692, g48, g52, d11868, g53, d12640, g57, g58, d12497, d12522, d12538, d12577, d12604]
          · have f12869 : (x 1 4).toNat = 1 := by rw [h12575]; rfl
            have d12870 : (x 1 12).toNat = 1 := by
              have r12871 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
              have b12872 := hb (x 1 4)
              have b12873 := hb (x 1 12)
              clear * - r12871 b12872 b12873 f12869
              omega
            have d12874 : (x (-2) 3).toNat = 0 := by
              have r12875 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e12876 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
              have e12877 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
              have b12878 := hb (x (-2) 3)
              have b12879 := hb (x (-1) 2)
              have b12880 := hb (x 0 13)
              have b12881 := hb (x 1 12)
              clear * - r12875 e12876 e12877 b12878 b12879 b12880 b12881 d12870 g21 f12547
              omega
            have d12882 : (x (-2) 1 && x (-2) 3).toNat = 0 := by
              have r12883 := hand2 (x (-2) 1) (x (-2) 3)
              have b12884 := hb (x (-2) 3)
              have b12885 := hb (x (-2) 1 && x (-2) 3)
              clear * - r12883 b12884 b12885 d12874
              omega
            have d12886 : (x 5 8).toNat = 0 := by
              have r12887 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e12888 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
              have e12889 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
              have e12890 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
              have e12891 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
              have e12892 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
              have e12893 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
              have b12894 := hb (x (-2) 7)
              have b12895 := hb (x (-1) 6)
              have b12896 := hb (x 0 5)
              have b12897 := hb (x 1 4)
              have b12898 := hb (x 2 11)
              have b12899 := hb (x 3 10)
              have b12900 := hb (x 4 9)
              have b12901 := hb (x 5 8)
              clear * - r12887 e12888 e12889 e12890 e12891 e12892 e12893 b12894 b12895 b12896 b12897 b12898 b12899 b12900 b12901 f12869 g14
              omega
            have d12902 : (x 4 9).toNat = 0 := by
              have r12903 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e12904 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
              have e12905 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
              have e12906 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
              have e12907 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
              have e12908 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
              have e12909 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
              have b12910 := hb (x (-2) 7)
              have b12911 := hb (x (-1) 6)
              have b12912 := hb (x 0 5)
              have b12913 := hb (x 1 4)
              have b12914 := hb (x 2 11)
              have b12915 := hb (x 3 10)
              have b12916 := hb (x 4 9)
              have b12917 := hb (x 5 8)
              clear * - r12903 e12904 e12905 e12906 e12907 e12908 e12909 b12910 b12911 b12912 b12913 b12914 b12915 b12916 b12917 d12886 f12869 g14
              omega
            have d12918 : (x 3 10).toNat = 0 := by
              have r12919 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e12920 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
              have e12921 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
              have e12922 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
              have e12923 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
              have e12924 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
              have e12925 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
              have b12926 := hb (x (-2) 7)
              have b12927 := hb (x (-1) 6)
              have b12928 := hb (x 0 5)
              have b12929 := hb (x 1 4)
              have b12930 := hb (x 2 11)
              have b12931 := hb (x 3 10)
              have b12932 := hb (x 4 9)
              have b12933 := hb (x 5 8)
              clear * - r12919 e12920 e12921 e12922 e12923 e12924 e12925 b12926 b12927 b12928 b12929 b12930 b12931 b12932 b12933 d12886 d12902 f12869 g14
              omega
            have d12934 : (x 2 11).toNat = 0 := by
              have r12935 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e12936 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
              have e12937 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
              have e12938 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
              have e12939 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
              have e12940 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
              have e12941 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
              have b12942 := hb (x (-2) 7)
              have b12943 := hb (x (-1) 6)
              have b12944 := hb (x 0 5)
              have b12945 := hb (x 1 4)
              have b12946 := hb (x 2 11)
              have b12947 := hb (x 3 10)
              have b12948 := hb (x 4 9)
              have b12949 := hb (x 5 8)
              clear * - r12935 e12936 e12937 e12938 e12939 e12940 e12941 b12942 b12943 b12944 b12945 b12946 b12947 b12948 b12949 d12886 d12902 d12918 f12869 g14
              omega
            have d12950 : (x (-1) 6).toNat = 0 := by
              have r12951 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e12952 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
              have e12953 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
              have e12954 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
              have e12955 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
              have e12956 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
              have e12957 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
              have b12958 := hb (x (-2) 7)
              have b12959 := hb (x (-1) 6)
              have b12960 := hb (x 0 5)
              have b12961 := hb (x 1 4)
              have b12962 := hb (x 2 11)
              have b12963 := hb (x 3 10)
              have b12964 := hb (x 4 9)
              have b12965 := hb (x 5 8)
              clear * - r12951 e12952 e12953 e12954 e12955 e12956 e12957 b12958 b12959 b12960 b12961 b12962 b12963 b12964 b12965 d12886 d12902 d12918 d12934 f12869 g14
              omega
            have d12966 : (x (-2) 7).toNat = 0 := by
              have r12967 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e12968 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
              have e12969 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
              have e12970 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
              have e12971 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
              have e12972 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
              have e12973 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
              have b12974 := hb (x (-2) 7)
              have b12975 := hb (x (-1) 6)
              have b12976 := hb (x 0 5)
              have b12977 := hb (x 1 4)
              have b12978 := hb (x 2 11)
              have b12979 := hb (x 3 10)
              have b12980 := hb (x 4 9)
              have b12981 := hb (x 5 8)
              clear * - r12967 e12968 e12969 e12970 e12971 e12972 e12973 b12974 b12975 b12976 b12977 b12978 b12979 b12980 b12981 d12886 d12902 d12918 d12934 f12869 g14 d12950
              omega
            have d12982 : (x (-2) 2 && x (-2) 7).toNat = 0 := by
              have r12983 := hand2 (x (-2) 2) (x (-2) 7)
              have b12984 := hb (x (-2) 7)
              have b12985 := hb (x (-2) 2 && x (-2) 7)
              clear * - r12983 b12984 b12985 d12966
              omega
            have r12986 : (x (-2) 1).toNat + (x (-3) 2).toNat + (x (-4) 3).toNat + (x (-5) 4).toNat + (x (-6) 5).toNat + (x (-7) 6).toNat + (x (-8) 7).toNat + (x (-9) 8).toNat + (x (-10) 9).toNat + (x (-11) 10).toNat + (x (-12) 11).toNat + (x (-13) 12).toNat + (x (-14) 13).toNat + (x (-15) 14).toNat = 3 := by have q := hcount (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r12987 : (x (-1) 1).toNat + (x (-2) 2).toNat + (x (-3) 3).toNat + (x (-4) 4).toNat + (x (-5) 5).toNat + (x (-6) 6).toNat + (x (-7) 7).toNat + (x (-8) 8).toNat + (x (-9) 9).toNat + (x (-10) 10).toNat + (x (-11) 11).toNat + (x (-12) 12).toNat + (x (-13) 13).toNat + (x (-14) 14).toNat = 3 := by have q := hcount 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r12988 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r12989 : (x (-11) 8).toNat + (x (-12) 1 && x (-12) 9).toNat + (x (-13) 2 && x (-13) 10).toNat + (x (-14) 3 && x (-14) 11).toNat + (x (-15) 4 && x (-15) 12).toNat + (x (-16) 5 && x (-16) 13).toNat + (x (-17) 6 && x (-17) 14).toNat + (x (-18) 7).toNat = 1 := by have q := hd8 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e12990 : (x (-12) 1 && x (-12) 9).toNat = (x (-12) 9).toNat := handr _ _ (fun h => hp9 (-12) (h))
            have e12991 : (x (-13) 2 && x (-13) 10).toNat = (x (-13) 10).toNat := handr _ _ (fun h => hp10 (-13) (h))
            have e12992 : (x (-14) 3 && x (-14) 11).toNat = (x (-14) 11).toNat := handr _ _ (fun h => hp11 (-14) (h))
            have e12993 : (x (-15) 4 && x (-15) 12).toNat = (x (-15) 4).toNat := handl _ _ (fun h => hp4 (-15) (h))
            have e12994 : (x (-16) 5 && x (-16) 13).toNat = (x (-16) 5).toNat := handl _ _ (fun h => hp5 (-16) (h))
            have e12995 : (x (-17) 6 && x (-17) 14).toNat = (x (-17) 6).toNat := handl _ _ (fun h => hp6 (-17) (h))
            have r12996 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e12997 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
            have e12998 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
            have e12999 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
            have e13000 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
            have e13001 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
            have e13002 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
            have r13003 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e13004 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
            have e13005 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
            have e13006 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
            have e13007 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
            have e13008 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
            have e13009 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
            have r13010 : (x (-11) 12).toNat + (x (-12) 1 && x (-12) 13).toNat + (x (-13) 2 && x (-13) 14).toNat + (x (-14) 3).toNat = 1 := by have q := hd12 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e13011 : (x (-12) 1 && x (-12) 13).toNat = (x (-12) 13).toNat := handr _ _ (fun h => hp13 (-12) (h))
            have e13012 : (x (-13) 2 && x (-13) 14).toNat = (x (-13) 2).toNat := handl _ _ (fun h => hp2 (-13) (h))
            have r13013 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e13014 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
            have e13015 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
            have r13016 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e13017 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e13018 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have r13019 : 1 ≤ (x (-1) 2).toNat + (x (-2) 1 && x (-2) 3).toNat + (x (-3) 2 && x (-3) 4).toNat + (x (-4) 3 && x (-4) 5).toNat + (x (-5) 4 && x (-5) 6).toNat + (x (-6) 5 && x (-6) 7).toNat + (x (-7) 6 && x (-7) 8).toNat + (x (-8) 7 && x (-8) 9).toNat + (x (-9) 8 && x (-9) 10).toNat + (x (-10) 9 && x (-10) 11).toNat + (x (-11) 10 && x (-11) 12).toNat + (x (-12) 11 && x (-12) 13).toNat + (x (-13) 12 && x (-13) 14).toNat + (x (-14) 13).toNat := by have q := hcov2 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r13020 : 1 ≤ (x (-3) 4).toNat + (x (-4) 1 && x (-4) 5).toNat + (x (-5) 2 && x (-5) 6).toNat + (x (-6) 3 && x (-6) 7).toNat + (x (-7) 4 && x (-7) 8).toNat + (x (-8) 5 && x (-8) 9).toNat + (x (-9) 6 && x (-9) 10).toNat + (x (-10) 7 && x (-10) 11).toNat + (x (-11) 8 && x (-11) 12).toNat + (x (-12) 9 && x (-12) 13).toNat + (x (-13) 10 && x (-13) 14).toNat + (x (-14) 11).toNat := by have q := hcov4 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e13021 : (x (-4) 1 && x (-4) 5).toNat = (x (-4) 5).toNat := handr _ _ (fun h => hp13 (-4) (hp5 (-4) (h)))
            have e13022 : (x (-13) 10 && x (-13) 14).toNat = (x (-13) 10).toNat := handl _ _ (fun h => hp2 (-13) (hp10 (-13) (h)))
            have r13023 : 1 ≤ (x 0 5).toNat + (x (-1) 1 && x (-1) 6).toNat + (x (-2) 2 && x (-2) 7).toNat + (x (-3) 3 && x (-3) 8).toNat + (x (-4) 4 && x (-4) 9).toNat + (x (-5) 5 && x (-5) 10).toNat + (x (-6) 6 && x (-6) 11).toNat + (x (-7) 7 && x (-7) 12).toNat + (x (-8) 8 && x (-8) 13).toNat + (x (-9) 9 && x (-9) 14).toNat + (x (-10) 10).toNat := by have q := hcov5 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r13024 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r13025 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r13026 : 1 ≤ (x (-11) 11).toNat + (x (-12) 1 && x (-12) 12).toNat + (x (-13) 2 && x (-13) 13).toNat + (x (-14) 3 && x (-14) 14).toNat + (x (-15) 4).toNat := by have q := hcov11 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r13027 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r13028 : 1 ≤ (x (-13) 13).toNat + (x (-14) 1 && x (-14) 14).toNat + (x (-15) 2).toNat := by have q := hcov13 (-13); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r13029 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r13030 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r13031 : (x (-15) 2).toNat ≤ (x (-15) 14).toNat := himp _ _ (hp2 (-15))
            have r13032 := hand1 (x (-7) 6) (x (-7) 8)
            have r13033 := hand1 (x (-8) 7) (x (-8) 9)
            have r13034 := hand1 (x (-9) 8) (x (-9) 10)
            have r13035 := hand1 (x (-10) 9) (x (-10) 11)
            have r13036 := hand1 (x (-11) 10) (x (-11) 12)
            have r13037 := hand1 (x (-12) 11) (x (-12) 13)
            have r13038 := hand1 (x (-13) 12) (x (-13) 14)
            have r13039 := hand1 (x (-7) 4) (x (-7) 8)
            have r13040 := hand1 (x (-8) 5) (x (-8) 9)
            have r13041 := hand1 (x (-9) 6) (x (-9) 10)
            have r13042 := hand1 (x (-10) 7) (x (-10) 11)
            have r13043 := hand1 (x (-11) 8) (x (-11) 12)
            have r13044 := hand1 (x (-12) 9) (x (-12) 13)
            have r13045 := hand2 (x (-4) 4) (x (-4) 9)
            have r13046 := hand2 (x (-5) 5) (x (-5) 10)
            have r13047 := hand2 (x (-6) 6) (x (-6) 11)
            have r13048 := hand1 (x (-7) 7) (x (-7) 12)
            have r13049 := hand1 (x (-8) 8) (x (-8) 13)
            have r13050 := hand1 (x (-9) 9) (x (-9) 14)
            have r13051 := hand1 (x (-4) 4) (x (-4) 13)
            have r13052 := hand1 (x (-5) 5) (x (-5) 14)
            have r13053 := hand1 (x (-3) 2) (x (-3) 12)
            have r13054 := hand1 (x (-4) 3) (x (-4) 13)
            have r13055 := hand1 (x (-5) 4) (x (-5) 14)
            have r13056 := hand2 (x (-12) 1) (x (-12) 12)
            have r13057 := hand1 (x (-13) 2) (x (-13) 13)
            have r13058 := hand1 (x (-14) 3) (x (-14) 14)
            have r13059 := hand2 (x (-2) 1) (x (-2) 12)
            have r13060 := hand1 (x (-4) 3) (x (-4) 14)
            have r13061 := hand2 (x (-14) 1) (x (-14) 14)
            have r13062 := hand1 (x (-2) 1) (x (-2) 14)
            have b13079 := hb (x (-13) 14)
            linarith only [r12986, r12987, r12988, r12989, e12990, e12991, e12992, e12993, e12994, e12995, r12996, e12997, e12998, e12999, e13000, e13001, e13002, r13003, e13004, e13005, e13006, e13007, e13008, e13009, r13010, e13011, e13012, r13013, e13014, e13015, r13016, e13017, e13018, r13019, r13020, e13021, e13022, r13023, r13024, r13025, r13026, r13027, r13028, r13029, r13030, r13031, r13032, r13033, r13034, r13035, r13036, r13037, r13038, r13039, r13040, r13041, r13042, r13043, r13044, r13045, r13046, r13047, r13048, r13049, r13050, r13051, r13052, r13053, r13054, r13055, r13056, r13057, r13058, r13059, r13060, r13061, r13062, b13079, d11956, d11924, d11892, g0, d11872, g3, g4, d12874, g6, f12547, d11832, d12569, g9, g10, g14, g17, d12882, d11888, d11920, d11952, d11984, d11948, d11980, g39, d12982, g40, g52, d11868, g53, d11864, g63, g70]
        · have f13186 : (x (-1) 4).toNat = 1 := by rw [h12573]; rfl
          have d13187 : (x (-1) 12).toNat = 1 := by
            have r13188 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
            have b13189 := hb (x (-1) 4)
            have b13190 := hb (x (-1) 12)
            clear * - r13188 b13189 b13190 f13186
            omega
          have d13191 : (x (-2) 13).toNat = 0 := by
            have r13192 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e13193 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e13194 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b13195 := hb (x (-4) 3)
            have b13196 := hb (x (-3) 2)
            have b13197 := hb (x (-2) 13)
            have b13198 := hb (x (-1) 12)
            clear * - r13192 e13193 e13194 b13195 b13196 b13197 b13198 d13187
            omega
          have d13199 : (x (-4) 2).toNat = 1 := by
            have r13200 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b13201 := hb (x (-4) 2)
            have b13202 := hb (x (-2) 13)
            have b13203 := hb (x (-3) 1 && x (-3) 14)
            clear * - r13200 b13201 b13202 b13203 d13191 g70
            omega
          have d13204 : (x (-4) 14).toNat = 1 := by
            have r13205 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
            have b13206 := hb (x (-4) 2)
            have b13207 := hb (x (-4) 14)
            clear * - r13205 b13206 b13207 d13199
            omega
          have d13208 : (x (-5) 1).toNat = 0 := by
            have r13209 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b13210 := hb (x (-5) 1)
            have b13211 := hb (x (-4) 14)
            clear * - r13209 b13210 b13211 d13204
            omega
          have d13212 : (x (-5) 13).toNat = 0 := by
            have r13213 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
            have b13214 := hb (x (-5) 1)
            have b13215 := hb (x (-5) 13)
            clear * - r13213 b13214 b13215 d13208
            omega
          have d13216 : (x (-3) 2).toNat = 0 := by
            have r13217 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e13218 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e13219 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b13220 := hb (x (-4) 3)
            have b13221 := hb (x (-3) 2)
            have b13222 := hb (x (-2) 13)
            have b13223 := hb (x (-1) 12)
            clear * - r13217 e13218 e13219 b13220 b13221 b13222 b13223 d13187 d13191
            omega
          have d13224 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
            have r13225 := hand1 (x (-3) 2) (x (-3) 12)
            have b13226 := hb (x (-3) 2)
            have b13227 := hb (x (-3) 2 && x (-3) 12)
            clear * - r13225 b13226 b13227 d13216
            omega
          have d13228 : (x (-4) 3).toNat = 0 := by
            have r13229 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e13230 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e13231 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b13232 := hb (x (-4) 3)
            have b13233 := hb (x (-3) 2)
            have b13234 := hb (x (-2) 13)
            have b13235 := hb (x (-1) 12)
            clear * - r13229 e13230 e13231 b13232 b13233 b13234 b13235 d13187 d13191 d13216
            omega
          have d13236 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
            have r13237 := hand1 (x (-4) 3) (x (-4) 14)
            have b13238 := hb (x (-4) 3)
            have b13239 := hb (x (-4) 3 && x (-4) 14)
            clear * - r13237 b13238 b13239 d13228
            omega
          have d13240 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
            have r13241 := hand1 (x (-4) 3) (x (-4) 13)
            have b13242 := hb (x (-4) 3)
            have b13243 := hb (x (-4) 3 && x (-4) 13)
            clear * - r13241 b13242 b13243 d13228
            omega
          have d13244 : (x (-2) 12).toNat = 0 := by
            have r13245 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e13246 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
            have e13247 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
            have b13248 := hb (x (-5) 3)
            have b13249 := hb (x (-4) 2)
            have b13250 := hb (x (-3) 13)
            have b13251 := hb (x (-2) 12)
            clear * - r13245 e13246 e13247 b13248 b13249 b13250 b13251 g3 d13199
            omega
          have d13252 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
            have r13253 := hand2 (x (-2) 1) (x (-2) 12)
            have b13254 := hb (x (-2) 12)
            have b13255 := hb (x (-2) 1 && x (-2) 12)
            clear * - r13253 b13254 b13255 d13244
            omega
          have d13256 : (x (-5) 4).toNat = 1 := by
            have r13257 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b13258 := hb (x (-5) 4)
            have b13259 := hb (x (-1) 11)
            have b13260 := hb (x (-2) 1 && x (-2) 12)
            have b13261 := hb (x (-3) 2 && x (-3) 13)
            have b13262 := hb (x (-4) 3 && x (-4) 14)
            clear * - r13257 b13258 b13259 b13260 b13261 b13262 d12569 d13252 g63 d13236
            omega
          have d13263 : (x (-5) 12).toNat = 1 := by
            have r13264 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
            have b13265 := hb (x (-5) 4)
            have b13266 := hb (x (-5) 12)
            clear * - r13264 b13265 b13266 d13256
            omega
          have d13267 : (x (-6) 13).toNat = 0 := by
            have r13268 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e13269 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
            have e13270 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
            have b13271 := hb (x (-8) 3)
            have b13272 := hb (x (-7) 2)
            have b13273 := hb (x (-6) 13)
            have b13274 := hb (x (-5) 12)
            clear * - r13268 e13269 e13270 b13271 b13272 b13273 b13274 d13263
            omega
          have d13275 : (x (-6) 5).toNat = 0 := by
            have r13276 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
            have b13277 := hb (x (-6) 5)
            have b13278 := hb (x (-6) 13)
            clear * - r13276 b13277 b13278 d13267
            omega
          have d13279 : (x (-7) 2).toNat = 0 := by
            have r13280 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e13281 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
            have e13282 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
            have b13283 := hb (x (-8) 3)
            have b13284 := hb (x (-7) 2)
            have b13285 := hb (x (-6) 13)
            have b13286 := hb (x (-5) 12)
            clear * - r13280 e13281 e13282 b13283 b13284 b13285 b13286 d13263 d13267
            omega
          have d13287 : (x (-6) 1 && x (-6) 14).toNat = 1 := by
            have r13288 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b13289 := hb (x (-7) 2)
            have b13290 := hb (x (-5) 13)
            have b13291 := hb (x (-6) 1 && x (-6) 14)
            clear * - r13288 b13289 b13290 b13291 d13212 d13279
            omega
          have d13292 : (x (-6) 1).toNat = 1 := by
            have r13293 := hand1 (x (-6) 1) (x (-6) 14)
            have b13294 := hb (x (-6) 1)
            have b13295 := hb (x (-6) 1 && x (-6) 14)
            clear * - r13293 b13294 b13295 d13287
            omega
          have d13296 : (x (-5) 14).toNat = 0 := by
            have r13297 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b13298 := hb (x (-6) 1)
            have b13299 := hb (x (-5) 14)
            clear * - r13297 b13298 b13299 d13292
            omega
          have d13300 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
            have r13301 := hand2 (x (-5) 4) (x (-5) 14)
            have b13302 := hb (x (-5) 14)
            have b13303 := hb (x (-5) 4 && x (-5) 14)
            clear * - r13301 b13302 b13303 d13296
            omega
          have r13304 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b13305 := hb (x (-6) 5)
          have b13306 := hb (x (-1) 10)
          have b13307 := hb (x (-2) 1 && x (-2) 11)
          have b13308 := hb (x (-3) 2 && x (-3) 12)
          have b13309 := hb (x (-4) 3 && x (-4) 13)
          have b13310 := hb (x (-5) 4 && x (-5) 14)
          linarith only [r13304, b13305, b13306, b13307, b13308, b13309, b13310, d11832, d11864, d13224, d13240, d13300, d13275]
      · have f13311 : (x (-1) 2).toNat = 1 := by rw [h12546]; rfl
        have d13312 : (x (-1) 14).toNat = 1 := by
          have r13313 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
          have b13314 := hb (x (-1) 2)
          have b13315 := hb (x (-1) 14)
          clear * - r13313 b13314 b13315 f13311
          omega
        have d13316 : (x (-2) 1).toNat = 0 := by
          have r13317 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b13318 := hb (x (-2) 1)
          have b13319 := hb (x (-1) 14)
          clear * - r13317 b13318 b13319 d13312
          omega
        have d13320 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
          have r13321 := hand1 (x (-2) 1) (x (-2) 14)
          have b13322 := hb (x (-2) 1)
          have b13323 := hb (x (-2) 1 && x (-2) 14)
          clear * - r13321 b13322 b13323 d13316
          omega
        have d13324 : (x (-2) 13).toNat = 0 := by
          have r13325 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
          have b13326 := hb (x (-2) 1)
          have b13327 := hb (x (-2) 13)
          clear * - r13325 b13326 b13327 d13316
          omega
        have d13328 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
          have r13329 := hand2 (x (-2) 2) (x (-2) 13)
          have b13330 := hb (x (-2) 13)
          have b13331 := hb (x (-2) 2 && x (-2) 13)
          clear * - r13329 b13330 b13331 d13324
          omega
        have d13332 : (x (-3) 2).toNat = 1 := by
          have r13333 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b13334 := hb (x (-3) 2)
          have b13335 := hb (x (-1) 13)
          have b13336 := hb (x (-2) 1 && x (-2) 14)
          clear * - r13333 b13334 b13335 b13336 g9 d13320
          omega
        have d13337 : (x (-3) 14).toNat = 1 := by
          have r13338 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
          have b13339 := hb (x (-3) 2)
          have b13340 := hb (x (-3) 14)
          clear * - r13338 b13339 b13340 d13332
          omega
        have d13341 : (x (-4) 1).toNat = 0 := by
          have r13342 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b13343 := hb (x (-4) 1)
          have b13344 := hb (x (-3) 14)
          clear * - r13342 b13343 b13344 d13337
          omega
        have d13345 : (x (-4) 13).toNat = 0 := by
          have r13346 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
          have b13347 := hb (x (-4) 1)
          have b13348 := hb (x (-4) 13)
          clear * - r13346 b13347 b13348 d13341
          omega
        have d13349 : (x (-4) 2).toNat = 1 := by
          have r13350 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b13351 := hb (x (-4) 2)
          have b13352 := hb (x (-2) 13)
          have b13353 := hb (x (-3) 1 && x (-3) 14)
          clear * - r13350 b13351 b13352 b13353 d13324 g70
          omega
        have d13354 : (x (-4) 14).toNat = 1 := by
          have r13355 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
          have b13356 := hb (x (-4) 2)
          have b13357 := hb (x (-4) 14)
          clear * - r13355 b13356 b13357 d13349
          omega
        have d13358 : (x (-5) 1).toNat = 0 := by
          have r13359 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b13360 := hb (x (-5) 1)
          have b13361 := hb (x (-4) 14)
          clear * - r13359 b13360 b13361 d13354
          omega
        have d13362 : (x (-5) 1 && x (-5) 14).toNat = 0 := by
          have r13363 := hand1 (x (-5) 1) (x (-5) 14)
          have b13364 := hb (x (-5) 1)
          have b13365 := hb (x (-5) 1 && x (-5) 14)
          clear * - r13363 b13364 b13365 d13358
          omega
        have d13366 : (x (-5) 13).toNat = 0 := by
          have r13367 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
          have b13368 := hb (x (-5) 1)
          have b13369 := hb (x (-5) 13)
          clear * - r13367 b13368 b13369 d13358
          omega
        have d13370 : (x (-6) 2).toNat = 1 := by
          have r13371 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b13372 := hb (x (-6) 2)
          have b13373 := hb (x (-4) 13)
          have b13374 := hb (x (-5) 1 && x (-5) 14)
          clear * - r13371 b13372 b13373 b13374 d13345 d13362
          omega
        have d13375 : (x (-4) 12).toNat = 0 := by
          have r13376 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e13377 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
          have e13378 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
          have b13379 := hb (x (-7) 3)
          have b13380 := hb (x (-6) 2)
          have b13381 := hb (x (-5) 13)
          have b13382 := hb (x (-4) 12)
          clear * - r13376 e13377 e13378 b13379 b13380 b13381 b13382 d13366 d13370
          omega
        have d13383 : (x (-4) 4).toNat = 0 := by
          have r13384 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
          have b13385 := hb (x (-4) 4)
          have b13386 := hb (x (-4) 12)
          clear * - r13384 b13385 b13386 d13375
          omega
        have r13387 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b13388 := hb (x (-4) 4)
        have b13389 := hb (x 0 11)
        have b13390 := hb (x (-1) 1 && x (-1) 12)
        have b13391 := hb (x (-2) 2 && x (-2) 13)
        have b13392 := hb (x (-3) 3 && x (-3) 14)
        linarith only [r13387, b13388, b13389, b13390, b13391, b13392, g19, g64, d13328, g65, d13383]
  · have f13393 : (x 0 6).toNat = 1 := by rw [h11988]; rfl
    have d13394 : (x 6 8).toNat = 0 := by
      have r13395 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13396 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e13397 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e13398 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e13399 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e13400 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e13401 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b13402 := hb (x (-1) 7)
      have b13403 := hb (x 0 6)
      have b13404 := hb (x 1 5)
      have b13405 := hb (x 2 4)
      have b13406 := hb (x 3 11)
      have b13407 := hb (x 4 10)
      have b13408 := hb (x 5 9)
      have b13409 := hb (x 6 8)
      clear * - r13395 e13396 e13397 e13398 e13399 e13400 e13401 b13402 b13403 b13404 b13405 b13406 b13407 b13408 b13409 f13393
      omega
    have d13410 : (x 5 9).toNat = 0 := by
      have r13411 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13412 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e13413 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e13414 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e13415 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e13416 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e13417 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b13418 := hb (x (-1) 7)
      have b13419 := hb (x 0 6)
      have b13420 := hb (x 1 5)
      have b13421 := hb (x 2 4)
      have b13422 := hb (x 3 11)
      have b13423 := hb (x 4 10)
      have b13424 := hb (x 5 9)
      have b13425 := hb (x 6 8)
      clear * - r13411 e13412 e13413 e13414 e13415 e13416 e13417 b13418 b13419 b13420 b13421 b13422 b13423 b13424 b13425 d13394 f13393
      omega
    have d13426 : (x 4 10).toNat = 0 := by
      have r13427 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13428 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e13429 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e13430 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e13431 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e13432 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e13433 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b13434 := hb (x (-1) 7)
      have b13435 := hb (x 0 6)
      have b13436 := hb (x 1 5)
      have b13437 := hb (x 2 4)
      have b13438 := hb (x 3 11)
      have b13439 := hb (x 4 10)
      have b13440 := hb (x 5 9)
      have b13441 := hb (x 6 8)
      clear * - r13427 e13428 e13429 e13430 e13431 e13432 e13433 b13434 b13435 b13436 b13437 b13438 b13439 b13440 b13441 d13394 d13410 f13393
      omega
    have d13442 : (x 4 1 && x 4 10).toNat = 0 := by
      have r13443 := hand2 (x 4 1) (x 4 10)
      have b13444 := hb (x 4 10)
      have b13445 := hb (x 4 1 && x 4 10)
      clear * - r13443 b13444 b13445 d13426
      omega
    have d13446 : (x 3 11).toNat = 0 := by
      have r13447 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13448 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e13449 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e13450 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e13451 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e13452 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e13453 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b13454 := hb (x (-1) 7)
      have b13455 := hb (x 0 6)
      have b13456 := hb (x 1 5)
      have b13457 := hb (x 2 4)
      have b13458 := hb (x 3 11)
      have b13459 := hb (x 4 10)
      have b13460 := hb (x 5 9)
      have b13461 := hb (x 6 8)
      clear * - r13447 e13448 e13449 e13450 e13451 e13452 e13453 b13454 b13455 b13456 b13457 b13458 b13459 b13460 b13461 d13394 d13410 d13426 f13393
      omega
    have d13462 : (x 3 1 && x 3 11).toNat = 0 := by
      have r13463 := hand2 (x 3 1) (x 3 11)
      have b13464 := hb (x 3 11)
      have b13465 := hb (x 3 1 && x 3 11)
      clear * - r13463 b13464 b13465 d13446
      omega
    have d13466 : (x 1 3 && x 1 13).toNat = 1 := by
      have r13467 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b13468 := hb (x (-1) 5)
      have b13469 := hb (x 4 10)
      have b13470 := hb (x 3 1 && x 3 11)
      have b13471 := hb (x 2 2 && x 2 12)
      have b13472 := hb (x 1 3 && x 1 13)
      have b13473 := hb (x 0 4 && x 0 14)
      clear * - r13467 b13468 b13469 b13470 b13471 b13472 b13473 d13426 d13462 g59 g60 g7
      omega
    have d13474 : (x 1 13).toNat = 1 := by
      have r13475 := hand2 (x 1 3) (x 1 13)
      have b13476 := hb (x 1 13)
      have b13477 := hb (x 1 3 && x 1 13)
      clear * - r13475 b13476 b13477 d13466
      omega
    have d13478 : (x 1 1).toNat = 1 := by
      have r13479 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
      have b13480 := hb (x 1 1)
      have b13481 := hb (x 1 13)
      clear * - r13479 b13480 b13481 d13474
      omega
    have d13482 : (x 2 14).toNat = 0 := by
      have r13483 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b13484 := hb (x 1 1)
      have b13485 := hb (x 2 14)
      clear * - r13483 b13484 b13485 d13478
      omega
    have d13486 : (x 2 4 && x 2 14).toNat = 0 := by
      have r13487 := hand2 (x 2 4) (x 2 14)
      have b13488 := hb (x 2 14)
      have b13489 := hb (x 2 4 && x 2 14)
      clear * - r13487 b13488 b13489 d13482
      omega
    have d13490 : (x 2 6).toNat = 0 := by
      have r13491 : (x 2 6).toNat ≤ (x 2 14).toNat := himp _ _ (hp6 2)
      have b13492 := hb (x 2 6)
      have b13493 := hb (x 2 14)
      clear * - r13491 b13492 b13493 d13482
      omega
    have d13494 : (x 2 12).toNat = 0 := by
      have r13495 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13496 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e13497 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b13498 := hb (x (-1) 3)
      have b13499 := hb (x 0 2)
      have b13500 := hb (x 1 13)
      have b13501 := hb (x 2 12)
      clear * - r13495 e13496 e13497 b13498 b13499 b13500 b13501 d13474 g11
      omega
    have d13502 : (x 2 3 && x 2 12).toNat = 0 := by
      have r13503 := hand2 (x 2 3) (x 2 12)
      have b13504 := hb (x 2 12)
      have b13505 := hb (x 2 3 && x 2 12)
      clear * - r13503 b13504 b13505 d13494
      omega
    have d13506 : (x 2 4).toNat = 0 := by
      have r13507 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
      have b13508 := hb (x 2 4)
      have b13509 := hb (x 2 12)
      clear * - r13507 b13508 b13509 d13494
      omega
    have d13510 : (x (-1) 3).toNat = 0 := by
      have r13511 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13512 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e13513 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b13514 := hb (x (-1) 3)
      have b13515 := hb (x 0 2)
      have b13516 := hb (x 1 13)
      have b13517 := hb (x 2 12)
      clear * - r13511 e13512 e13513 b13514 b13515 b13516 b13517 d13494 d13474 g11
      omega
    have d13518 : (x (-1) 11).toNat = 0 := by
      have r13519 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
      have b13520 := hb (x (-1) 3)
      have b13521 := hb (x (-1) 11)
      clear * - r13519 b13520 b13521 d13510
      omega
    have d13522 : (x (-1) 2 && x (-1) 11).toNat = 0 := by
      have r13523 := hand2 (x (-1) 2) (x (-1) 11)
      have b13524 := hb (x (-1) 11)
      have b13525 := hb (x (-1) 2 && x (-1) 11)
      clear * - r13523 b13524 b13525 d13518
      omega
    have d13526 : (x 3 2 && x 3 11).toNat = 0 := by
      have r13527 := hand2 (x 3 2) (x 3 11)
      have b13528 := hb (x 3 11)
      have b13529 := hb (x 3 2 && x 3 11)
      clear * - r13527 b13528 b13529 d13446
      omega
    have d13530 : (x 1 5).toNat = 0 := by
      have r13531 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13532 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e13533 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e13534 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e13535 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e13536 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e13537 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b13538 := hb (x (-1) 7)
      have b13539 := hb (x 0 6)
      have b13540 := hb (x 1 5)
      have b13541 := hb (x 2 4)
      have b13542 := hb (x 3 11)
      have b13543 := hb (x 4 10)
      have b13544 := hb (x 5 9)
      have b13545 := hb (x 6 8)
      clear * - r13531 e13532 e13533 e13534 e13535 e13536 e13537 b13538 b13539 b13540 b13541 b13542 b13543 b13544 b13545 d13394 d13410 d13426 d13446 d13506 f13393
      omega
    have d13546 : (x (-1) 7).toNat = 0 := by
      have r13547 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13548 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e13549 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e13550 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e13551 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e13552 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e13553 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b13554 := hb (x (-1) 7)
      have b13555 := hb (x 0 6)
      have b13556 := hb (x 1 5)
      have b13557 := hb (x 2 4)
      have b13558 := hb (x 3 11)
      have b13559 := hb (x 4 10)
      have b13560 := hb (x 5 9)
      have b13561 := hb (x 6 8)
      clear * - r13547 e13548 e13549 e13550 e13551 e13552 e13553 b13554 b13555 b13556 b13557 b13558 b13559 b13560 b13561 d13394 d13410 d13426 d13446 d13506 d13530 f13393
      omega
    have d13562 : (x (-1) 2 && x (-1) 7).toNat = 0 := by
      have r13563 := hand2 (x (-1) 2) (x (-1) 7)
      have b13564 := hb (x (-1) 7)
      have b13565 := hb (x (-1) 2 && x (-1) 7)
      clear * - r13563 b13564 b13565 d13546
      omega
    cases h13566 : x (-1) 2
    · have f13567 : (x (-1) 2).toNat = 0 := by rw [h13566]; rfl
      cases h13568 : x (-1) 4
      · have f13569 : (x (-1) 4).toNat = 0 := by rw [h13568]; rfl
        cases h13570 : x 1 4
        · have f13571 : (x 1 4).toNat = 0 := by rw [h13570]; rfl
          have d13572 : (x 1 4 && x 1 13).toNat = 0 := by
            have r13573 := hand1 (x 1 4) (x 1 13)
            have b13574 := hb (x 1 4)
            have b13575 := hb (x 1 4 && x 1 13)
            clear * - r13573 b13574 b13575 f13571
            omega
          have d13576 : (x (-1) 6).toNat = 1 := by
            have r13577 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b13578 := hb (x (-1) 6)
            have b13579 := hb (x 5 9)
            have b13580 := hb (x 4 1 && x 4 10)
            have b13581 := hb (x 3 2 && x 3 11)
            have b13582 := hb (x 2 3 && x 2 12)
            have b13583 := hb (x 1 4 && x 1 13)
            have b13584 := hb (x 0 5 && x 0 14)
            clear * - r13577 b13578 b13579 b13580 b13581 b13582 b13583 b13584 d13410 d13442 d13526 d13502 d13572 g56
            omega
          have d13585 : (x (-1) 14).toNat = 1 := by
            have r13586 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
            have b13587 := hb (x (-1) 6)
            have b13588 := hb (x (-1) 14)
            clear * - r13586 b13587 b13588 d13576
            omega
          have d13589 : (x (-2) 1).toNat = 0 := by
            have r13590 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b13591 := hb (x (-2) 1)
            have b13592 := hb (x (-1) 14)
            clear * - r13590 b13591 b13592 d13585
            omega
          have d13593 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
            have r13594 := hand1 (x (-2) 1) (x (-2) 14)
            have b13595 := hb (x (-2) 1)
            have b13596 := hb (x (-2) 1 && x (-2) 14)
            clear * - r13594 b13595 b13596 d13589
            omega
          have d13597 : (x (-3) 2).toNat = 1 := by
            have r13598 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b13599 := hb (x (-3) 2)
            have b13600 := hb (x (-1) 13)
            have b13601 := hb (x (-2) 1 && x (-2) 14)
            clear * - r13598 b13599 b13600 b13601 g9 d13593
            omega
          have d13602 : (x (-3) 14).toNat = 1 := by
            have r13603 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
            have b13604 := hb (x (-3) 2)
            have b13605 := hb (x (-3) 14)
            clear * - r13603 b13604 b13605 d13597
            omega
          have d13606 : (x (-4) 1).toNat = 0 := by
            have r13607 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b13608 := hb (x (-4) 1)
            have b13609 := hb (x (-3) 14)
            clear * - r13607 b13608 b13609 d13602
            omega
          have d13610 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
            have r13611 := hand1 (x (-4) 1) (x (-4) 14)
            have b13612 := hb (x (-4) 1)
            have b13613 := hb (x (-4) 1 && x (-4) 14)
            clear * - r13611 b13612 b13613 d13606
            omega
          have d13614 : (x (-5) 2).toNat = 1 := by
            have r13615 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b13616 := hb (x (-5) 2)
            have b13617 := hb (x (-3) 13)
            have b13618 := hb (x (-4) 1 && x (-4) 14)
            clear * - r13615 b13616 b13617 b13618 g3 d13610
            omega
          have d13619 : (x (-5) 14).toNat = 1 := by
            have r13620 : (x (-5) 2).toNat ≤ (x (-5) 14).toNat := himp _ _ (hp2 (-5))
            have b13621 := hb (x (-5) 2)
            have b13622 := hb (x (-5) 14)
            clear * - r13620 b13621 b13622 d13614
            omega
          have d13623 : (x (-6) 1).toNat = 0 := by
            have r13624 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b13625 := hb (x (-6) 1)
            have b13626 := hb (x (-5) 14)
            clear * - r13624 b13625 b13626 d13619
            omega
          have d13627 : (x (-6) 1 && x (-6) 14).toNat = 0 := by
            have r13628 := hand1 (x (-6) 1) (x (-6) 14)
            have b13629 := hb (x (-6) 1)
            have b13630 := hb (x (-6) 1 && x (-6) 14)
            clear * - r13628 b13629 b13630 d13623
            omega
          have d13631 : (x (-6) 13).toNat = 0 := by
            have r13632 : (x (-6) 13).toNat ≤ (x (-6) 1).toNat := himp _ _ (hp13 (-6))
            have b13633 := hb (x (-6) 1)
            have b13634 := hb (x (-6) 13)
            clear * - r13632 b13633 b13634 d13623
            omega
          have d13635 : (x (-6) 5).toNat = 0 := by
            have r13636 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
            have b13637 := hb (x (-6) 5)
            have b13638 := hb (x (-6) 13)
            clear * - r13636 b13637 b13638 d13631
            omega
          have d13639 : (x (-3) 12).toNat = 0 := by
            have r13640 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e13641 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
            have e13642 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
            have b13643 := hb (x (-6) 3)
            have b13644 := hb (x (-5) 2)
            have b13645 := hb (x (-4) 13)
            have b13646 := hb (x (-3) 12)
            clear * - r13640 e13641 e13642 b13643 b13644 b13645 b13646 d13614
            omega
          have d13647 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
            have r13648 := hand2 (x (-3) 2) (x (-3) 12)
            have b13649 := hb (x (-3) 12)
            have b13650 := hb (x (-3) 2 && x (-3) 12)
            clear * - r13648 b13649 b13650 d13639
            omega
          have d13651 : (x (-4) 13).toNat = 0 := by
            have r13652 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e13653 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
            have e13654 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
            have b13655 := hb (x (-6) 3)
            have b13656 := hb (x (-5) 2)
            have b13657 := hb (x (-4) 13)
            have b13658 := hb (x (-3) 12)
            clear * - r13652 e13653 e13654 b13655 b13656 b13657 b13658 d13639 d13614
            omega
          have d13659 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
            have r13660 := hand2 (x (-4) 3) (x (-4) 13)
            have b13661 := hb (x (-4) 13)
            have b13662 := hb (x (-4) 3 && x (-4) 13)
            clear * - r13660 b13661 b13662 d13651
            omega
          have d13663 : (x (-5) 4 && x (-5) 14).toNat = 1 := by
            have r13664 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b13665 := hb (x (-6) 5)
            have b13666 := hb (x (-1) 10)
            have b13667 := hb (x (-2) 1 && x (-2) 11)
            have b13668 := hb (x (-3) 2 && x (-3) 12)
            have b13669 := hb (x (-4) 3 && x (-4) 13)
            have b13670 := hb (x (-5) 4 && x (-5) 14)
            clear * - r13664 b13665 b13666 b13667 b13668 b13669 b13670 d11832 d11864 d13647 d13659 d13635
            omega
          have d13671 : (x (-5) 4).toNat = 1 := by
            have r13672 := hand1 (x (-5) 4) (x (-5) 14)
            have b13673 := hb (x (-5) 4)
            have b13674 := hb (x (-5) 4 && x (-5) 14)
            clear * - r13672 b13673 b13674 d13663
            omega
          have d13675 : (x (-5) 12).toNat = 1 := by
            have r13676 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
            have b13677 := hb (x (-5) 4)
            have b13678 := hb (x (-5) 12)
            clear * - r13676 b13677 b13678 d13671
            omega
          have d13679 : (x (-7) 2).toNat = 0 := by
            have r13680 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e13681 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
            have e13682 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
            have b13683 := hb (x (-8) 3)
            have b13684 := hb (x (-7) 2)
            have b13685 := hb (x (-6) 13)
            have b13686 := hb (x (-5) 12)
            clear * - r13680 e13681 e13682 b13683 b13684 b13685 b13686 d13675 d13631
            omega
          have d13687 : (x (-5) 13).toNat = 1 := by
            have r13688 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b13689 := hb (x (-7) 2)
            have b13690 := hb (x (-5) 13)
            have b13691 := hb (x (-6) 1 && x (-6) 14)
            clear * - r13688 b13689 b13690 b13691 d13627 d13679
            omega
          have d13692 : (x (-5) 1).toNat = 1 := by
            have r13693 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
            have b13694 := hb (x (-5) 1)
            have b13695 := hb (x (-5) 13)
            clear * - r13693 b13694 b13695 d13687
            omega
          have d13696 : (x (-4) 14).toNat = 0 := by
            have r13697 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b13698 := hb (x (-5) 1)
            have b13699 := hb (x (-4) 14)
            clear * - r13697 b13698 b13699 d13692
            omega
          have d13700 : (x (-4) 2).toNat = 0 := by
            have r13701 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
            have b13702 := hb (x (-4) 2)
            have b13703 := hb (x (-4) 14)
            clear * - r13701 b13702 b13703 d13696
            omega
          have d13704 : (x (-2) 13).toNat = 1 := by
            have r13705 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b13706 := hb (x (-4) 2)
            have b13707 := hb (x (-2) 13)
            have b13708 := hb (x (-3) 1 && x (-3) 14)
            clear * - r13705 b13706 b13707 b13708 g70 d13700
            omega
          have r13709 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e13710 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e13711 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b13712 := hb (x (-4) 3)
          have b13713 := hb (x (-3) 2)
          have b13714 := hb (x (-2) 13)
          have b13715 := hb (x (-1) 12)
          linarith only [r13709, e13710, e13711, b13712, b13713, b13714, b13715, d13704, d13597]
        · have f13716 : (x 1 4).toNat = 1 := by rw [h13570]; rfl
          have d13717 : (x 1 12).toNat = 1 := by
            have r13718 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
            have b13719 := hb (x 1 4)
            have b13720 := hb (x 1 12)
            clear * - r13718 b13719 b13720 f13716
            omega
          have d13721 : (x (-2) 3).toNat = 0 := by
            have r13722 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e13723 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
            have e13724 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
            have b13725 := hb (x (-2) 3)
            have b13726 := hb (x (-1) 2)
            have b13727 := hb (x 0 13)
            have b13728 := hb (x 1 12)
            clear * - r13722 e13723 e13724 b13725 b13726 b13727 b13728 d13717 g21 f13567
            omega
          have d13729 : (x (-2) 3 && x (-2) 12).toNat = 0 := by
            have r13730 := hand1 (x (-2) 3) (x (-2) 12)
            have b13731 := hb (x (-2) 3)
            have b13732 := hb (x (-2) 3 && x (-2) 12)
            clear * - r13730 b13731 b13732 d13721
            omega
          have d13733 : (x (-2) 3 && x (-2) 10).toNat = 0 := by
            have r13734 := hand1 (x (-2) 3) (x (-2) 10)
            have b13735 := hb (x (-2) 3)
            have b13736 := hb (x (-2) 3 && x (-2) 10)
            clear * - r13734 b13735 b13736 d13721
            omega
          have d13737 : (x (-2) 3 && x (-2) 8).toNat = 0 := by
            have r13738 := hand1 (x (-2) 3) (x (-2) 8)
            have b13739 := hb (x (-2) 3)
            have b13740 := hb (x (-2) 3 && x (-2) 8)
            clear * - r13738 b13739 b13740 d13721
            omega
          have d13741 : (x 1 9).toNat = 1 := by
            have r13742 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b13743 := hb (x (-5) 6)
            have b13744 := hb (x 1 9)
            have b13745 := hb (x 0 1 && x 0 10)
            have b13746 := hb (x (-1) 2 && x (-1) 11)
            have b13747 := hb (x (-2) 3 && x (-2) 12)
            have b13748 := hb (x (-3) 4 && x (-3) 13)
            have b13749 := hb (x (-4) 5 && x (-4) 14)
            clear * - r13742 b13743 b13744 b13745 b13746 b13747 b13748 b13749 g54 d13522 d13729 g55 d11908 d11924
            omega
          have d13750 : (x 2 8).toNat = 0 := by
            have r13751 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e13752 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
            have e13753 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
            have e13754 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
            have e13755 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
            have e13756 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
            have e13757 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
            have b13758 := hb (x (-5) 7)
            have b13759 := hb (x (-4) 6)
            have b13760 := hb (x (-3) 5)
            have b13761 := hb (x (-2) 4)
            have b13762 := hb (x (-1) 11)
            have b13763 := hb (x 0 10)
            have b13764 := hb (x 1 9)
            have b13765 := hb (x 2 8)
            clear * - r13751 e13752 e13753 e13754 e13755 e13756 e13757 b13758 b13759 b13760 b13761 b13762 b13763 b13764 b13765 d13741 g18 d13518 g1
            omega
          have d13766 : (x (-2) 4).toNat = 0 := by
            have r13767 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e13768 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
            have e13769 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
            have e13770 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
            have e13771 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
            have e13772 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
            have e13773 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
            have b13774 := hb (x (-5) 7)
            have b13775 := hb (x (-4) 6)
            have b13776 := hb (x (-3) 5)
            have b13777 := hb (x (-2) 4)
            have b13778 := hb (x (-1) 11)
            have b13779 := hb (x 0 10)
            have b13780 := hb (x 1 9)
            have b13781 := hb (x 2 8)
            clear * - r13767 e13768 e13769 e13770 e13771 e13772 e13773 b13774 b13775 b13776 b13777 b13778 b13779 b13780 b13781 d13750 d13741 g18 d13518 g1
            omega
          have d13782 : (x (-2) 4 && x (-2) 10).toNat = 0 := by
            have r13783 := hand1 (x (-2) 4) (x (-2) 10)
            have b13784 := hb (x (-2) 4)
            have b13785 := hb (x (-2) 4 && x (-2) 10)
            clear * - r13783 b13784 b13785 d13766
            omega
          have d13786 : (x (-4) 6).toNat = 0 := by
            have r13787 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e13788 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
            have e13789 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
            have e13790 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
            have e13791 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
            have e13792 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
            have e13793 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
            have b13794 := hb (x (-5) 7)
            have b13795 := hb (x (-4) 6)
            have b13796 := hb (x (-3) 5)
            have b13797 := hb (x (-2) 4)
            have b13798 := hb (x (-1) 11)
            have b13799 := hb (x 0 10)
            have b13800 := hb (x 1 9)
            have b13801 := hb (x 2 8)
            clear * - r13787 e13788 e13789 e13790 e13791 e13792 e13793 b13794 b13795 b13796 b13797 b13798 b13799 b13800 b13801 d13750 d13741 g18 d13518 d13766 g1
            omega
          have d13802 : (x (-4) 6 && x (-4) 12).toNat = 0 := by
            have r13803 := hand1 (x (-4) 6) (x (-4) 12)
            have b13804 := hb (x (-4) 6)
            have b13805 := hb (x (-4) 6 && x (-4) 12)
            clear * - r13803 b13804 b13805 d13786
            omega
          have d13806 : (x (-5) 7).toNat = 0 := by
            have r13807 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e13808 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
            have e13809 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
            have e13810 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
            have e13811 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
            have e13812 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
            have e13813 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
            have b13814 := hb (x (-5) 7)
            have b13815 := hb (x (-4) 6)
            have b13816 := hb (x (-3) 5)
            have b13817 := hb (x (-2) 4)
            have b13818 := hb (x (-1) 11)
            have b13819 := hb (x 0 10)
            have b13820 := hb (x 1 9)
            have b13821 := hb (x 2 8)
            clear * - r13807 e13808 e13809 e13810 e13811 e13812 e13813 b13814 b13815 b13816 b13817 b13818 b13819 b13820 b13821 d13750 d13741 g18 d13518 d13766 g1 d13786
            omega
          have d13822 : (x (-5) 7 && x (-5) 13).toNat = 0 := by
            have r13823 := hand1 (x (-5) 7) (x (-5) 13)
            have b13824 := hb (x (-5) 7)
            have b13825 := hb (x (-5) 7 && x (-5) 13)
            clear * - r13823 b13824 b13825 d13806
            omega
          have r13826 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r13827 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e13828 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
          have e13829 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
          have e13830 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
          have e13831 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
          have e13832 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
          have e13833 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
          have r13834 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e13835 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
          have e13836 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
          have e13837 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
          have e13838 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
          have e13839 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
          have e13840 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
          have r13841 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e13842 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e13843 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e13844 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e13845 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e13846 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e13847 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have r13848 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e13849 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e13850 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e13851 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e13852 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e13853 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e13854 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have r13855 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e13856 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
          have e13857 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
          have r13858 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e13859 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
          have e13860 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
          have r13861 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e13862 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
          have e13863 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
          have r13864 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r13865 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := by have q := hcov5 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r13866 : 1 ≤ (x 2 6).toNat + (x 1 1 && x 1 7).toNat + (x 0 2 && x 0 8).toNat + (x (-1) 3 && x (-1) 9).toNat + (x (-2) 4 && x (-2) 10).toNat + (x (-3) 5 && x (-3) 11).toNat + (x (-4) 6 && x (-4) 12).toNat + (x (-5) 7 && x (-5) 13).toNat + (x (-6) 8 && x (-6) 14).toNat + (x (-7) 9).toNat := by have q := hcov6 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r13867 : 1 ≤ (x 1 7).toNat + (x 0 1 && x 0 8).toNat + (x (-1) 2 && x (-1) 9).toNat + (x (-2) 3 && x (-2) 10).toNat + (x (-3) 4 && x (-3) 11).toNat + (x (-4) 5 && x (-4) 12).toNat + (x (-5) 6 && x (-5) 13).toNat + (x (-6) 7 && x (-6) 14).toNat + (x (-7) 8).toNat := by have q := hcov7 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r13868 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r13869 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r13870 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r13871 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
          have r13872 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
          have r13873 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
          have r13874 := hand2 (x (-7) 8) (x (-7) 13)
          have r13875 := hand1 (x (-8) 9) (x (-8) 14)
          have r13876 := hand2 (x 1 1) (x 1 7)
          have r13877 := hand1 (x (-6) 8) (x (-6) 14)
          have r13878 := hand1 (x (-4) 4) (x (-4) 13)
          have r13879 := hand1 (x (-5) 5) (x (-5) 14)
          have r13880 := hand2 (x (-7) 1) (x (-7) 11)
          have r13881 := hand1 (x (-8) 2) (x (-8) 12)
          have r13882 := hand1 (x (-9) 3) (x (-9) 13)
          have r13883 := hand1 (x (-10) 4) (x (-10) 14)
          have r13884 := hand2 (x 5 1) (x 5 11)
          have b13931 := hb (x 7 1)
          linarith only [r13826, r13827, e13828, e13829, e13830, e13831, e13832, e13833, r13834, e13835, e13836, e13837, e13838, e13839, e13840, r13841, e13842, e13843, e13844, e13845, e13846, e13847, r13848, e13849, e13850, e13851, e13852, e13853, e13854, r13855, e13856, e13857, r13858, e13859, e13860, r13861, e13862, e13863, r13864, r13865, r13866, r13867, r13868, r13869, r13870, r13871, r13872, r13873, r13874, r13875, r13876, r13877, r13878, r13879, r13880, r13881, r13882, r13883, r13884, b13931, g2, g8, g16, g17, d13530, d13490, g27, g29, g41, d13562, d13737, g42, d11916, d11944, d11976, g43, g44, d13782, g45, d13802, d13822, g49, g50, d13733, g51, d11912, d11940, d11972, g52, d11868, g53, g61, g62, d13486]
      · have f13973 : (x (-1) 4).toNat = 1 := by rw [h13568]; rfl
        have d13974 : (x (-1) 12).toNat = 1 := by
          have r13975 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
          have b13976 := hb (x (-1) 4)
          have b13977 := hb (x (-1) 12)
          clear * - r13975 b13976 b13977 f13973
          omega
        have d13978 : (x (-2) 13).toNat = 0 := by
          have r13979 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e13980 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e13981 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b13982 := hb (x (-4) 3)
          have b13983 := hb (x (-3) 2)
          have b13984 := hb (x (-2) 13)
          have b13985 := hb (x (-1) 12)
          clear * - r13979 e13980 e13981 b13982 b13983 b13984 b13985 d13974
          omega
        have d13986 : (x (-4) 2).toNat = 1 := by
          have r13987 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b13988 := hb (x (-4) 2)
          have b13989 := hb (x (-2) 13)
          have b13990 := hb (x (-3) 1 && x (-3) 14)
          clear * - r13987 b13988 b13989 b13990 d13978 g70
          omega
        have d13991 : (x (-4) 14).toNat = 1 := by
          have r13992 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
          have b13993 := hb (x (-4) 2)
          have b13994 := hb (x (-4) 14)
          clear * - r13992 b13993 b13994 d13986
          omega
        have d13995 : (x (-5) 1).toNat = 0 := by
          have r13996 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b13997 := hb (x (-5) 1)
          have b13998 := hb (x (-4) 14)
          clear * - r13996 b13997 b13998 d13991
          omega
        have d13999 : (x (-5) 13).toNat = 0 := by
          have r14000 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
          have b14001 := hb (x (-5) 1)
          have b14002 := hb (x (-5) 13)
          clear * - r14000 b14001 b14002 d13995
          omega
        have d14003 : (x (-3) 2).toNat = 0 := by
          have r14004 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e14005 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e14006 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b14007 := hb (x (-4) 3)
          have b14008 := hb (x (-3) 2)
          have b14009 := hb (x (-2) 13)
          have b14010 := hb (x (-1) 12)
          clear * - r14004 e14005 e14006 b14007 b14008 b14009 b14010 d13974 d13978
          omega
        have d14011 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
          have r14012 := hand1 (x (-3) 2) (x (-3) 12)
          have b14013 := hb (x (-3) 2)
          have b14014 := hb (x (-3) 2 && x (-3) 12)
          clear * - r14012 b14013 b14014 d14003
          omega
        have d14015 : (x (-4) 3).toNat = 0 := by
          have r14016 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e14017 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e14018 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b14019 := hb (x (-4) 3)
          have b14020 := hb (x (-3) 2)
          have b14021 := hb (x (-2) 13)
          have b14022 := hb (x (-1) 12)
          clear * - r14016 e14017 e14018 b14019 b14020 b14021 b14022 d13974 d13978 d14003
          omega
        have d14023 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
          have r14024 := hand1 (x (-4) 3) (x (-4) 14)
          have b14025 := hb (x (-4) 3)
          have b14026 := hb (x (-4) 3 && x (-4) 14)
          clear * - r14024 b14025 b14026 d14015
          omega
        have d14027 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
          have r14028 := hand1 (x (-4) 3) (x (-4) 13)
          have b14029 := hb (x (-4) 3)
          have b14030 := hb (x (-4) 3 && x (-4) 13)
          clear * - r14028 b14029 b14030 d14015
          omega
        have d14031 : (x (-2) 12).toNat = 0 := by
          have r14032 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e14033 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
          have e14034 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
          have b14035 := hb (x (-5) 3)
          have b14036 := hb (x (-4) 2)
          have b14037 := hb (x (-3) 13)
          have b14038 := hb (x (-2) 12)
          clear * - r14032 e14033 e14034 b14035 b14036 b14037 b14038 g3 d13986
          omega
        have d14039 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
          have r14040 := hand2 (x (-2) 1) (x (-2) 12)
          have b14041 := hb (x (-2) 12)
          have b14042 := hb (x (-2) 1 && x (-2) 12)
          clear * - r14040 b14041 b14042 d14031
          omega
        have d14043 : (x (-5) 4).toNat = 1 := by
          have r14044 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b14045 := hb (x (-5) 4)
          have b14046 := hb (x (-1) 11)
          have b14047 := hb (x (-2) 1 && x (-2) 12)
          have b14048 := hb (x (-3) 2 && x (-3) 13)
          have b14049 := hb (x (-4) 3 && x (-4) 14)
          clear * - r14044 b14045 b14046 b14047 b14048 b14049 d13518 d14039 g63 d14023
          omega
        have d14050 : (x (-5) 12).toNat = 1 := by
          have r14051 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
          have b14052 := hb (x (-5) 4)
          have b14053 := hb (x (-5) 12)
          clear * - r14051 b14052 b14053 d14043
          omega
        have d14054 : (x (-6) 13).toNat = 0 := by
          have r14055 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e14056 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
          have e14057 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
          have b14058 := hb (x (-8) 3)
          have b14059 := hb (x (-7) 2)
          have b14060 := hb (x (-6) 13)
          have b14061 := hb (x (-5) 12)
          clear * - r14055 e14056 e14057 b14058 b14059 b14060 b14061 d14050
          omega
        have d14062 : (x (-6) 5).toNat = 0 := by
          have r14063 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
          have b14064 := hb (x (-6) 5)
          have b14065 := hb (x (-6) 13)
          clear * - r14063 b14064 b14065 d14054
          omega
        have d14066 : (x (-7) 2).toNat = 0 := by
          have r14067 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e14068 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
          have e14069 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
          have b14070 := hb (x (-8) 3)
          have b14071 := hb (x (-7) 2)
          have b14072 := hb (x (-6) 13)
          have b14073 := hb (x (-5) 12)
          clear * - r14067 e14068 e14069 b14070 b14071 b14072 b14073 d14050 d14054
          omega
        have d14074 : (x (-6) 1 && x (-6) 14).toNat = 1 := by
          have r14075 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b14076 := hb (x (-7) 2)
          have b14077 := hb (x (-5) 13)
          have b14078 := hb (x (-6) 1 && x (-6) 14)
          clear * - r14075 b14076 b14077 b14078 d13999 d14066
          omega
        have d14079 : (x (-6) 1).toNat = 1 := by
          have r14080 := hand1 (x (-6) 1) (x (-6) 14)
          have b14081 := hb (x (-6) 1)
          have b14082 := hb (x (-6) 1 && x (-6) 14)
          clear * - r14080 b14081 b14082 d14074
          omega
        have d14083 : (x (-5) 14).toNat = 0 := by
          have r14084 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b14085 := hb (x (-6) 1)
          have b14086 := hb (x (-5) 14)
          clear * - r14084 b14085 b14086 d14079
          omega
        have d14087 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
          have r14088 := hand2 (x (-5) 4) (x (-5) 14)
          have b14089 := hb (x (-5) 14)
          have b14090 := hb (x (-5) 4 && x (-5) 14)
          clear * - r14088 b14089 b14090 d14083
          omega
        have r14091 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b14092 := hb (x (-6) 5)
        have b14093 := hb (x (-1) 10)
        have b14094 := hb (x (-2) 1 && x (-2) 11)
        have b14095 := hb (x (-3) 2 && x (-3) 12)
        have b14096 := hb (x (-4) 3 && x (-4) 13)
        have b14097 := hb (x (-5) 4 && x (-5) 14)
        linarith only [r14091, b14092, b14093, b14094, b14095, b14096, b14097, d11832, d11864, d14011, d14027, d14087, d14062]
    · have f14098 : (x (-1) 2).toNat = 1 := by rw [h13566]; rfl
      have d14099 : (x (-1) 14).toNat = 1 := by
        have r14100 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
        have b14101 := hb (x (-1) 2)
        have b14102 := hb (x (-1) 14)
        clear * - r14100 b14101 b14102 f14098
        omega
      have d14103 : (x (-2) 1).toNat = 0 := by
        have r14104 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b14105 := hb (x (-2) 1)
        have b14106 := hb (x (-1) 14)
        clear * - r14104 b14105 b14106 d14099
        omega
      have d14107 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
        have r14108 := hand1 (x (-2) 1) (x (-2) 14)
        have b14109 := hb (x (-2) 1)
        have b14110 := hb (x (-2) 1 && x (-2) 14)
        clear * - r14108 b14109 b14110 d14103
        omega
      have d14111 : (x (-2) 13).toNat = 0 := by
        have r14112 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
        have b14113 := hb (x (-2) 1)
        have b14114 := hb (x (-2) 13)
        clear * - r14112 b14113 b14114 d14103
        omega
      have d14115 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
        have r14116 := hand2 (x (-2) 2) (x (-2) 13)
        have b14117 := hb (x (-2) 13)
        have b14118 := hb (x (-2) 2 && x (-2) 13)
        clear * - r14116 b14117 b14118 d14111
        omega
      have d14119 : (x (-3) 2).toNat = 1 := by
        have r14120 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b14121 := hb (x (-3) 2)
        have b14122 := hb (x (-1) 13)
        have b14123 := hb (x (-2) 1 && x (-2) 14)
        clear * - r14120 b14121 b14122 b14123 g9 d14107
        omega
      have d14124 : (x (-3) 14).toNat = 1 := by
        have r14125 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
        have b14126 := hb (x (-3) 2)
        have b14127 := hb (x (-3) 14)
        clear * - r14125 b14126 b14127 d14119
        omega
      have d14128 : (x (-4) 1).toNat = 0 := by
        have r14129 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b14130 := hb (x (-4) 1)
        have b14131 := hb (x (-3) 14)
        clear * - r14129 b14130 b14131 d14124
        omega
      have d14132 : (x (-4) 13).toNat = 0 := by
        have r14133 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
        have b14134 := hb (x (-4) 1)
        have b14135 := hb (x (-4) 13)
        clear * - r14133 b14134 b14135 d14128
        omega
      have d14136 : (x (-4) 2).toNat = 1 := by
        have r14137 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b14138 := hb (x (-4) 2)
        have b14139 := hb (x (-2) 13)
        have b14140 := hb (x (-3) 1 && x (-3) 14)
        clear * - r14137 b14138 b14139 b14140 d14111 g70
        omega
      have d14141 : (x (-4) 14).toNat = 1 := by
        have r14142 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
        have b14143 := hb (x (-4) 2)
        have b14144 := hb (x (-4) 14)
        clear * - r14142 b14143 b14144 d14136
        omega
      have d14145 : (x (-5) 1).toNat = 0 := by
        have r14146 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b14147 := hb (x (-5) 1)
        have b14148 := hb (x (-4) 14)
        clear * - r14146 b14147 b14148 d14141
        omega
      have d14149 : (x (-5) 1 && x (-5) 14).toNat = 0 := by
        have r14150 := hand1 (x (-5) 1) (x (-5) 14)
        have b14151 := hb (x (-5) 1)
        have b14152 := hb (x (-5) 1 && x (-5) 14)
        clear * - r14150 b14151 b14152 d14145
        omega
      have d14153 : (x (-5) 13).toNat = 0 := by
        have r14154 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
        have b14155 := hb (x (-5) 1)
        have b14156 := hb (x (-5) 13)
        clear * - r14154 b14155 b14156 d14145
        omega
      have d14157 : (x (-6) 2).toNat = 1 := by
        have r14158 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b14159 := hb (x (-6) 2)
        have b14160 := hb (x (-4) 13)
        have b14161 := hb (x (-5) 1 && x (-5) 14)
        clear * - r14158 b14159 b14160 b14161 d14132 d14149
        omega
      have d14162 : (x (-4) 12).toNat = 0 := by
        have r14163 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e14164 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e14165 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have b14166 := hb (x (-7) 3)
        have b14167 := hb (x (-6) 2)
        have b14168 := hb (x (-5) 13)
        have b14169 := hb (x (-4) 12)
        clear * - r14163 e14164 e14165 b14166 b14167 b14168 b14169 d14153 d14157
        omega
      have d14170 : (x (-4) 4).toNat = 0 := by
        have r14171 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
        have b14172 := hb (x (-4) 4)
        have b14173 := hb (x (-4) 12)
        clear * - r14171 b14172 b14173 d14162
        omega
      have r14174 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b14175 := hb (x (-4) 4)
      have b14176 := hb (x 0 11)
      have b14177 := hb (x (-1) 1 && x (-1) 12)
      have b14178 := hb (x (-2) 2 && x (-2) 13)
      have b14179 := hb (x (-3) 3 && x (-3) 14)
      linarith only [r14174, b14175, b14176, b14177, b14178, b14179, g19, g64, d14115, g65, d14170]

theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b000011 (x : ℤ → Fin 16 → Bool)
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
    (g2 : (x (-3) 11).toNat = 0)
    (g3 : (x (-3) 13).toNat = 0)
    (g4 : (x (-2) 2).toNat = 1)
    (g5 : (x (-2) 14).toNat = 1)
    (g6 : (x (-1) 1).toNat = 0)
    (g7 : (x (-1) 5).toNat = 0)
    (g8 : (x (-1) 9).toNat = 0)
    (g9 : (x (-1) 13).toNat = 0)
    (g10 : (x 0 1).toNat = 0)
    (g11 : (x 0 2).toNat = 0)
    (g12 : (x 0 3).toNat = 0)
    (g13 : (x 0 4).toNat = 0)
    (g14 : (x 0 5).toNat = 0)
    (g15 : (x 0 7).toNat = 0)
    (g16 : (x 0 8).toNat = 0)
    (g17 : (x 0 9).toNat = 0)
    (g18 : (x 0 10).toNat = 0)
    (g19 : (x 0 11).toNat = 0)
    (g20 : (x 0 12).toNat = 0)
    (g21 : (x 0 13).toNat = 0)
    (g22 : (x 0 14).toNat = 1)
    (g23 : (x 1 3).toNat = 1)
    (g24 : (x 1 8).toNat = 1)
    (g25 : (x 2 2).toNat = 0)
    (g26 : (x 2 10).toNat = 0)
    (g27 : (x 3 5).toNat = 0)
    (g28 : (x 3 13).toNat = 0)
    (g29 : (x 4 4).toNat = 0)
    (g30 : (x 2 2 && x 2 6).toNat = 0)
    (g31 : (x 0 4 && x 0 8).toNat = 0)
    (g32 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g33 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g34 : (x 4 4 && x 4 8).toNat = 0)
    (g35 : (x 3 5 && x 3 9).toNat = 0)
    (g36 : (x 2 6 && x 2 10).toNat = 0)
    (g37 : (x 0 8 && x 0 12).toNat = 0)
    (g38 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g39 : (x (-1) 1 && x (-1) 6).toNat = 0)
    (g40 : (x (-3) 3 && x (-3) 8).toNat = 0)
    (g41 : (x 0 1 && x 0 6).toNat = 0)
    (g42 : (x (-3) 4 && x (-3) 9).toNat = 0)
    (g43 : (x 0 2 && x 0 8).toNat = 0)
    (g44 : (x (-1) 3 && x (-1) 9).toNat = 0)
    (g45 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g46 : (x 4 4 && x 4 10).toNat = 0)
    (g47 : (x 3 5 && x 3 11).toNat = 0)
    (g48 : (x 0 8 && x 0 14).toNat = 0)
    (g49 : (x 0 1 && x 0 8).toNat = 0)
    (g50 : (x (-1) 2 && x (-1) 9).toNat = 0)
    (g51 : (x (-3) 4 && x (-3) 11).toNat = 0)
    (g52 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g53 : (x (-3) 3 && x (-3) 12).toNat = 0)
    (g54 : (x 0 1 && x 0 10).toNat = 0)
    (g55 : (x (-3) 4 && x (-3) 13).toNat = 0)
    (g56 : (x 0 5 && x 0 14).toNat = 0)
    (g57 : (x 4 3 && x 4 12).toNat = 0)
    (g58 : (x 3 4 && x 3 13).toNat = 0)
    (g59 : (x 2 2 && x 2 12).toNat = 0)
    (g60 : (x 0 4 && x 0 14).toNat = 0)
    (g61 : (x 4 2 && x 4 12).toNat = 0)
    (g62 : (x 3 3 && x 3 13).toNat = 0)
    (g63 : (x (-3) 2 && x (-3) 13).toNat = 0)
    (g64 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g65 : (x (-3) 3 && x (-3) 14).toNat = 0)
    (g66 : (x 0 2 && x 0 13).toNat = 0)
    (g67 : (x 0 3 && x 0 14).toNat = 0)
    (g68 : (x 4 1 && x 4 12).toNat = 0)
    (g69 : (x 3 2 && x 3 13).toNat = 0)
    (g70 : (x (-3) 1 && x (-3) 14).toNat = 0)
    (g71 : (x 0 1 && x 0 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b000011_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71
