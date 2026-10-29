import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000100_p1

Topic: combinatorics   Node: 93b3b9ebbcd0

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

Sub-branch of the window refutation cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000100 (one subtree of its case split, cut out so each piece fits the build limit): under the same layer-free tight-cover constraints for k = 15, its fixed bits and the case bits of this subtree, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000100_p1_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-4) 11).toNat = 0)
    (g1 : (x (-3) 10).toNat = 0)
    (g2 : (x (-3) 11).toNat = 0)
    (g3 : (x (-2) 5).toNat = 0)
    (g4 : (x (-2) 9).toNat = 0)
    (g5 : (x (-2) 10).toNat = 0)
    (g6 : (x (-2) 11).toNat = 0)
    (g7 : (x (-2) 13).toNat = 0)
    (g8 : (x (-1) 3).toNat = 0)
    (g9 : (x (-1) 5).toNat = 0)
    (g10 : (x (-1) 12).toNat = 1)
    (g11 : (x (-1) 13).toNat = 1)
    (g12 : (x (-1) 14).toNat = 1)
    (g13 : (x 0 3).toNat = 0)
    (g14 : (x 0 4).toNat = 0)
    (g15 : (x 0 5).toNat = 0)
    (g16 : (x 0 6).toNat = 0)
    (g17 : (x 0 7).toNat = 0)
    (g18 : (x 0 8).toNat = 0)
    (g19 : (x 0 9).toNat = 0)
    (g20 : (x 0 10).toNat = 0)
    (g21 : (x 0 11).toNat = 0)
    (g22 : (x 0 12).toNat = 0)
    (g23 : (x 0 13).toNat = 0)
    (g24 : (x 1 2).toNat = 0)
    (g25 : (x 1 4).toNat = 0)
    (g26 : (x 1 5).toNat = 0)
    (g27 : (x 1 9).toNat = 0)
    (g28 : (x 1 10).toNat = 0)
    (g29 : (x 1 12).toNat = 0)
    (g30 : (x 1 14).toNat = 1)
    (g31 : (x 2 1).toNat = 1)
    (g32 : (x 2 13).toNat = 1)
    (g33 : (x 3 2).toNat = 0)
    (g34 : (x 3 4).toNat = 0)
    (g35 : (x 3 6).toNat = 0)
    (g36 : (x 3 10).toNat = 0)
    (g37 : (x 3 12).toNat = 0)
    (g38 : (x 1 2 && x 1 6).toNat = 0)
    (g39 : (x 0 3 && x 0 7).toNat = 0)
    (g40 : (x (-2) 5 && x (-2) 9).toNat = 0)
    (g41 : (x (-3) 6 && x (-3) 10).toNat = 0)
    (g42 : (x (-4) 7 && x (-4) 11).toNat = 0)
    (g43 : (x 1 5 && x 1 9).toNat = 0)
    (g44 : (x 0 6 && x 0 10).toNat = 0)
    (g45 : (x 3 4 && x 3 8).toNat = 0)
    (g46 : (x 1 6 && x 1 10).toNat = 0)
    (g47 : (x 0 7 && x 0 11).toNat = 0)
    (g48 : (x (-2) 9 && x (-2) 13).toNat = 0)
    (g49 : (x 1 9 && x 1 13).toNat = 0)
    (g50 : (x 3 8 && x 3 12).toNat = 0)
    (g51 : (x 3 6 && x 3 11).toNat = 0)
    (g52 : (x 1 8 && x 1 13).toNat = 0)
    (g53 : (x 0 9 && x 0 14).toNat = 0)
    (g54 : (x 3 7 && x 3 12).toNat = 0)
    (g55 : (x 1 9 && x 1 14).toNat = 0)
    (g56 : (x 3 4 && x 3 10).toNat = 0)
    (g57 : (x 1 6 && x 1 12).toNat = 0)
    (g58 : (x 0 7 && x 0 13).toNat = 0)
    (g59 : (x 3 6 && x 3 12).toNat = 0)
    (g60 : (x 1 2 && x 1 9).toNat = 0)
    (g61 : (x 0 3 && x 0 10).toNat = 0)
    (g62 : (x (-2) 5 && x (-2) 12).toNat = 0)
    (g63 : (x 3 4 && x 3 11).toNat = 0)
    (g64 : (x 1 6 && x 1 13).toNat = 0)
    (g65 : (x 0 7 && x 0 14).toNat = 0)
    (g66 : (x (-3) 1 && x (-3) 10).toNat = 0)
    (g67 : (x (-4) 2 && x (-4) 11).toNat = 0)
    (g68 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g69 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g70 : (x (-4) 3 && x (-4) 12).toNat = 0)
    (g71 : (x 0 1 && x 0 10).toNat = 0)
    (g72 : (x (-2) 3 && x (-2) 12).toNat = 0)
    (g73 : (x 1 1 && x 1 10).toNat = 0)
    (g74 : (x 0 2 && x 0 11).toNat = 0)
    (g75 : (x (-2) 4 && x (-2) 13).toNat = 0)
    (g76 : (x 3 3 && x 3 12).toNat = 0)
    (g77 : (x 1 5 && x 1 14).toNat = 0)
    (g78 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g79 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g80 : (x (-3) 2 && x (-3) 12).toNat = 0)
    (g81 : (x (-4) 3 && x (-4) 13).toNat = 0)
    (g82 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g83 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g84 : (x 1 1 && x 1 11).toNat = 0)
    (g85 : (x 0 2 && x 0 12).toNat = 0)
    (g86 : (x 1 2 && x 1 12).toNat = 0)
    (g87 : (x 0 3 && x 0 13).toNat = 0)
    (g88 : (x 3 4 && x 3 14).toNat = 0)
    (g89 : (x (-2) 1 && x (-2) 12).toNat = 0)
    (g90 : (x (-3) 2 && x (-3) 13).toNat = 0)
    (g91 : (x (-4) 3 && x (-4) 14).toNat = 0)
    (g92 : (x 3 2 && x 3 13).toNat = 0)
    (g93 : (x 3 3 && x 3 14).toNat = 0)
    (g94 : (x 3 1 && x 3 14).toNat = 0)
    (h14164 : x 1 3 = true)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d14017 : (x (-1) 3 && x (-1) 13).toNat = 0 := by
    have r14018 := hand1 (x (-1) 3) (x (-1) 13)
    have b14019 := hb (x (-1) 3)
    have b14020 := hb (x (-1) 3 && x (-1) 13)
    clear * - r14018 b14019 b14020 g8
    omega
  have d14021 : (x (-1) 3 && x (-1) 12).toNat = 0 := by
    have r14022 := hand1 (x (-1) 3) (x (-1) 12)
    have b14023 := hb (x (-1) 3)
    have b14024 := hb (x (-1) 3 && x (-1) 12)
    clear * - r14022 b14023 b14024 g8
    omega
  have d14025 : (x (-1) 11).toNat = 0 := by
    have r14026 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
    have b14027 := hb (x (-1) 3)
    have b14028 := hb (x (-1) 11)
    clear * - r14026 b14027 b14028 g8
    omega
  have d14029 : (x (-1) 1 && x (-1) 11).toNat = 0 := by
    have r14030 := hand2 (x (-1) 1) (x (-1) 11)
    have b14031 := hb (x (-1) 11)
    have b14032 := hb (x (-1) 1 && x (-1) 11)
    clear * - r14030 b14031 b14032 d14025
    omega
  have d14033 : (x (-1) 2 && x (-1) 11).toNat = 0 := by
    have r14034 := hand2 (x (-1) 2) (x (-1) 11)
    have b14035 := hb (x (-1) 11)
    have b14036 := hb (x (-1) 2 && x (-1) 11)
    clear * - r14034 b14035 b14036 d14025
    omega
  have d14037 : (x (-1) 4 && x (-1) 11).toNat = 0 := by
    have r14038 := hand2 (x (-1) 4) (x (-1) 11)
    have b14039 := hb (x (-1) 11)
    have b14040 := hb (x (-1) 4 && x (-1) 11)
    clear * - r14038 b14039 b14040 d14025
    omega
  have d14041 : (x (-1) 7 && x (-1) 11).toNat = 0 := by
    have r14042 := hand2 (x (-1) 7) (x (-1) 11)
    have b14043 := hb (x (-1) 11)
    have b14044 := hb (x (-1) 7 && x (-1) 11)
    clear * - r14042 b14043 b14044 d14025
    omega
  have d14045 : (x (-5) 4).toNat = 1 := by
    have r14046 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14047 := hb (x (-5) 4)
    have b14048 := hb (x (-1) 11)
    have b14049 := hb (x (-2) 1 && x (-2) 12)
    have b14050 := hb (x (-3) 2 && x (-3) 13)
    have b14051 := hb (x (-4) 3 && x (-4) 14)
    clear * - r14046 b14047 b14048 b14049 b14050 b14051 d14025 g89 g90 g91
    omega
  have d14052 : (x (-5) 12).toNat = 1 := by
    have r14053 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
    have b14054 := hb (x (-5) 4)
    have b14055 := hb (x (-5) 12)
    clear * - r14053 b14054 b14055 d14045
    omega
  have d14056 : (x (-6) 13).toNat = 0 := by
    have r14057 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14058 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
    have e14059 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
    have b14060 := hb (x (-8) 3)
    have b14061 := hb (x (-7) 2)
    have b14062 := hb (x (-6) 13)
    have b14063 := hb (x (-5) 12)
    clear * - r14057 e14058 e14059 b14060 b14061 b14062 b14063 d14052
    omega
  have d14064 : (x (-6) 4 && x (-6) 13).toNat = 0 := by
    have r14065 := hand2 (x (-6) 4) (x (-6) 13)
    have b14066 := hb (x (-6) 13)
    have b14067 := hb (x (-6) 4 && x (-6) 13)
    clear * - r14065 b14066 b14067 d14056
    omega
  have d14068 : (x (-6) 9 && x (-6) 13).toNat = 0 := by
    have r14069 := hand2 (x (-6) 9) (x (-6) 13)
    have b14070 := hb (x (-6) 13)
    have b14071 := hb (x (-6) 9 && x (-6) 13)
    clear * - r14069 b14070 b14071 d14056
    omega
  have d14072 : (x (-6) 5).toNat = 0 := by
    have r14073 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
    have b14074 := hb (x (-6) 5)
    have b14075 := hb (x (-6) 13)
    clear * - r14073 b14074 b14075 d14056
    omega
  have d14076 : (x (-6) 5 && x (-6) 14).toNat = 0 := by
    have r14077 := hand1 (x (-6) 5) (x (-6) 14)
    have b14078 := hb (x (-6) 5)
    have b14079 := hb (x (-6) 5 && x (-6) 14)
    clear * - r14077 b14078 b14079 d14072
    omega
  have d14080 : (x (-7) 2).toNat = 0 := by
    have r14081 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14082 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
    have e14083 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
    have b14084 := hb (x (-8) 3)
    have b14085 := hb (x (-7) 2)
    have b14086 := hb (x (-6) 13)
    have b14087 := hb (x (-5) 12)
    clear * - r14081 e14082 e14083 b14084 b14085 b14086 b14087 d14052 d14056
    omega
  have d14088 : (x (-7) 2 && x (-7) 13).toNat = 0 := by
    have r14089 := hand1 (x (-7) 2) (x (-7) 13)
    have b14090 := hb (x (-7) 2)
    have b14091 := hb (x (-7) 2 && x (-7) 13)
    clear * - r14089 b14090 b14091 d14080
    omega
  have d14092 : (x (-7) 10).toNat = 0 := by
    have r14093 : (x (-7) 10).toNat ≤ (x (-7) 2).toNat := himp _ _ (hp10 (-7))
    have b14094 := hb (x (-7) 2)
    have b14095 := hb (x (-7) 10)
    clear * - r14093 b14094 b14095 d14080
    omega
  have d14096 : (x (-7) 5 && x (-7) 10).toNat = 0 := by
    have r14097 := hand2 (x (-7) 5) (x (-7) 10)
    have b14098 := hb (x (-7) 10)
    have b14099 := hb (x (-7) 5 && x (-7) 10)
    clear * - r14097 b14098 b14099 d14092
    omega
  have d14100 : (x (-8) 3).toNat = 0 := by
    have r14101 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14102 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
    have e14103 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
    have b14104 := hb (x (-8) 3)
    have b14105 := hb (x (-7) 2)
    have b14106 := hb (x (-6) 13)
    have b14107 := hb (x (-5) 12)
    clear * - r14101 e14102 e14103 b14104 b14105 b14106 b14107 d14052 d14056 d14080
    omega
  have d14108 : (x (-8) 3 && x (-8) 14).toNat = 0 := by
    have r14109 := hand1 (x (-8) 3) (x (-8) 14)
    have b14110 := hb (x (-8) 3)
    have b14111 := hb (x (-8) 3 && x (-8) 14)
    clear * - r14109 b14110 b14111 d14100
    omega
  have d14112 : (x (-8) 11).toNat = 0 := by
    have r14113 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
    have b14114 := hb (x (-8) 3)
    have b14115 := hb (x (-8) 11)
    clear * - r14113 b14114 b14115 d14100
    omega
  have d14116 : (x (-8) 6 && x (-8) 11).toNat = 0 := by
    have r14117 := hand2 (x (-8) 6) (x (-8) 11)
    have b14118 := hb (x (-8) 11)
    have b14119 := hb (x (-8) 6 && x (-8) 11)
    clear * - r14117 b14118 b14119 d14112
    omega
  have d14120 : (x (-1) 8).toNat = 0 := by
    have r14121 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14122 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
    have e14123 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
    have e14124 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
    have e14125 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
    have e14126 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
    have e14127 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
    have b14128 := hb (x (-8) 7)
    have b14129 := hb (x (-7) 6)
    have b14130 := hb (x (-6) 5)
    have b14131 := hb (x (-5) 4)
    have b14132 := hb (x (-4) 11)
    have b14133 := hb (x (-3) 10)
    have b14134 := hb (x (-2) 9)
    have b14135 := hb (x (-1) 8)
    clear * - r14121 e14122 e14123 e14124 e14125 e14126 e14127 b14128 b14129 b14130 b14131 b14132 b14133 b14134 b14135 g4 g1 g0 d14045 d14072
    omega
  have d14136 : (x (-1) 8 && x (-1) 14).toNat = 0 := by
    have r14137 := hand1 (x (-1) 8) (x (-1) 14)
    have b14138 := hb (x (-1) 8)
    have b14139 := hb (x (-1) 8 && x (-1) 14)
    clear * - r14137 b14138 b14139 d14120
    omega
  have d14140 : (x (-1) 8 && x (-1) 12).toNat = 0 := by
    have r14141 := hand1 (x (-1) 8) (x (-1) 12)
    have b14142 := hb (x (-1) 8)
    have b14143 := hb (x (-1) 8 && x (-1) 12)
    clear * - r14141 b14142 b14143 d14120
    omega
  have d14144 : (x (-1) 4 && x (-1) 8).toNat = 0 := by
    have r14145 := hand2 (x (-1) 4) (x (-1) 8)
    have b14146 := hb (x (-1) 8)
    have b14147 := hb (x (-1) 4 && x (-1) 8)
    clear * - r14145 b14146 b14147 d14120
    omega
  have d14148 : (x (-7) 6).toNat = 0 := by
    have r14149 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14150 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
    have e14151 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
    have e14152 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
    have e14153 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
    have e14154 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
    have e14155 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
    have b14156 := hb (x (-8) 7)
    have b14157 := hb (x (-7) 6)
    have b14158 := hb (x (-6) 5)
    have b14159 := hb (x (-5) 4)
    have b14160 := hb (x (-4) 11)
    have b14161 := hb (x (-3) 10)
    have b14162 := hb (x (-2) 9)
    have b14163 := hb (x (-1) 8)
    clear * - r14149 e14150 e14151 e14152 e14153 e14154 e14155 b14156 b14157 b14158 b14159 b14160 b14161 b14162 b14163 d14120 g4 g1 g0 d14045 d14072
    omega
  have f17509 : (x 1 3).toNat = 1 := by rw [h14164]; rfl
  have d17510 : (x 4 12).toNat = 0 := by
    have r17511 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17512 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e17513 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b17514 := hb (x 1 3)
    have b17515 := hb (x 2 2)
    have b17516 := hb (x 3 13)
    have b17517 := hb (x 4 12)
    clear * - r17511 e17512 e17513 b17514 b17515 b17516 b17517 f17509
    omega
  have d17518 : (x 4 1 && x 4 12).toNat = 0 := by
    have r17519 := hand2 (x 4 1) (x 4 12)
    have b17520 := hb (x 4 12)
    have b17521 := hb (x 4 1 && x 4 12)
    clear * - r17519 b17520 b17521 d17510
    omega
  have d17522 : (x 4 4).toNat = 0 := by
    have r17523 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
    have b17524 := hb (x 4 4)
    have b17525 := hb (x 4 12)
    clear * - r17523 b17524 b17525 d17510
    omega
  have d17526 : (x 3 13).toNat = 0 := by
    have r17527 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17528 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e17529 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b17530 := hb (x 1 3)
    have b17531 := hb (x 2 2)
    have b17532 := hb (x 3 13)
    have b17533 := hb (x 4 12)
    clear * - r17527 e17528 e17529 b17530 b17531 b17532 b17533 d17510 f17509
    omega
  have d17534 : (x 2 2).toNat = 0 := by
    have r17535 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17536 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e17537 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b17538 := hb (x 1 3)
    have b17539 := hb (x 2 2)
    have b17540 := hb (x 3 13)
    have b17541 := hb (x 4 12)
    clear * - r17535 e17536 e17537 b17538 b17539 b17540 b17541 d17510 d17526 f17509
    omega
  have d17542 : (x 4 13).toNat = 1 := by
    have r17543 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17544 := hb (x 2 2)
    have b17545 := hb (x 4 13)
    have b17546 := hb (x 3 1 && x 3 14)
    clear * - r17543 b17544 b17545 b17546 g94 d17534
    omega
  have d17547 : (x 4 1).toNat = 1 := by
    have r17548 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
    have b17549 := hb (x 4 1)
    have b17550 := hb (x 4 13)
    clear * - r17548 b17549 b17550 d17542
    omega
  have d17551 : (x 5 14).toNat = 0 := by
    have r17552 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17553 := hb (x 4 1)
    have b17554 := hb (x 5 14)
    clear * - r17552 b17553 b17554 d17547
    omega
  have d17555 : (x 5 3 && x 5 14).toNat = 0 := by
    have r17556 := hand2 (x 5 3) (x 5 14)
    have b17557 := hb (x 5 14)
    have b17558 := hb (x 5 3 && x 5 14)
    clear * - r17556 b17557 b17558 d17551
    omega
  have d17559 : (x 5 2).toNat = 0 := by
    have r17560 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
    have b17561 := hb (x 5 2)
    have b17562 := hb (x 5 14)
    clear * - r17560 b17561 b17562 d17551
    omega
  have d17563 : (x 5 12).toNat = 0 := by
    have r17564 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17565 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e17566 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b17567 := hb (x 2 3)
    have b17568 := hb (x 3 2)
    have b17569 := hb (x 4 13)
    have b17570 := hb (x 5 12)
    clear * - r17564 e17565 e17566 b17567 b17568 b17569 b17570 d17542 g33
    omega
  have d17571 : (x 5 4).toNat = 0 := by
    have r17572 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
    have b17573 := hb (x 5 4)
    have b17574 := hb (x 5 12)
    clear * - r17572 b17573 b17574 d17563
    omega
  have d17575 : (x 2 3).toNat = 0 := by
    have r17576 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17577 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e17578 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b17579 := hb (x 2 3)
    have b17580 := hb (x 3 2)
    have b17581 := hb (x 4 13)
    have b17582 := hb (x 5 12)
    clear * - r17576 e17577 e17578 b17579 b17580 b17581 b17582 d17563 d17542 g33
    omega
  have d17583 : (x 2 3 && x 2 14).toNat = 0 := by
    have r17584 := hand1 (x 2 3) (x 2 14)
    have b17585 := hb (x 2 3)
    have b17586 := hb (x 2 3 && x 2 14)
    clear * - r17584 b17585 b17586 d17575
    omega
  have d17587 : (x 5 11).toNat = 1 := by
    have r17588 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17589 := hb (x 1 4)
    have b17590 := hb (x 5 11)
    have b17591 := hb (x 4 1 && x 4 12)
    have b17592 := hb (x 3 2 && x 3 13)
    have b17593 := hb (x 2 3 && x 2 14)
    clear * - r17588 b17589 b17590 b17591 b17592 b17593 d17518 g92 d17583 g25
    omega
  have d17594 : (x 5 3).toNat = 1 := by
    have r17595 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
    have b17596 := hb (x 5 3)
    have b17597 := hb (x 5 11)
    clear * - r17595 b17596 b17597 d17587
    omega
  have d17598 : (x 8 12).toNat = 0 := by
    have r17599 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17600 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e17601 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b17602 := hb (x 5 3)
    have b17603 := hb (x 6 2)
    have b17604 := hb (x 7 13)
    have b17605 := hb (x 8 12)
    clear * - r17599 e17600 e17601 b17602 b17603 b17604 b17605 d17594
    omega
  have d17606 : (x 8 1 && x 8 12).toNat = 0 := by
    have r17607 := hand2 (x 8 1) (x 8 12)
    have b17608 := hb (x 8 12)
    have b17609 := hb (x 8 1 && x 8 12)
    clear * - r17607 b17608 b17609 d17598
    omega
  have d17610 : (x 8 4).toNat = 0 := by
    have r17611 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
    have b17612 := hb (x 8 4)
    have b17613 := hb (x 8 12)
    clear * - r17611 b17612 b17613 d17598
    omega
  have d17614 : (x 7 13).toNat = 0 := by
    have r17615 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17616 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e17617 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b17618 := hb (x 5 3)
    have b17619 := hb (x 6 2)
    have b17620 := hb (x 7 13)
    have b17621 := hb (x 8 12)
    clear * - r17615 e17616 e17617 b17618 b17619 b17620 b17621 d17598 d17594
    omega
  have d17622 : (x 7 2 && x 7 13).toNat = 0 := by
    have r17623 := hand2 (x 7 2) (x 7 13)
    have b17624 := hb (x 7 13)
    have b17625 := hb (x 7 2 && x 7 13)
    clear * - r17623 b17624 b17625 d17614
    omega
  have d17626 : (x 6 1 && x 6 14).toNat = 1 := by
    have r17627 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17628 := hb (x 5 2)
    have b17629 := hb (x 7 13)
    have b17630 := hb (x 6 1 && x 6 14)
    clear * - r17627 b17628 b17629 b17630 d17614 d17559
    omega
  have d17631 : (x 6 1).toNat = 1 := by
    have r17632 := hand1 (x 6 1) (x 6 14)
    have b17633 := hb (x 6 1)
    have b17634 := hb (x 6 1 && x 6 14)
    clear * - r17632 b17633 b17634 d17626
    omega
  have d17635 : (x 7 14).toNat = 0 := by
    have r17636 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17637 := hb (x 6 1)
    have b17638 := hb (x 7 14)
    clear * - r17636 b17637 b17638 d17631
    omega
  have d17639 : (x 7 1 && x 7 14).toNat = 0 := by
    have r17640 := hand2 (x 7 1) (x 7 14)
    have b17641 := hb (x 7 14)
    have b17642 := hb (x 7 1 && x 7 14)
    clear * - r17640 b17641 b17642 d17635
    omega
  have d17643 : (x 7 2).toNat = 0 := by
    have r17644 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
    have b17645 := hb (x 7 2)
    have b17646 := hb (x 7 14)
    clear * - r17644 b17645 b17646 d17635
    omega
  have d17647 : (x 6 2).toNat = 0 := by
    have r17648 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17649 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e17650 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b17651 := hb (x 5 3)
    have b17652 := hb (x 6 2)
    have b17653 := hb (x 7 13)
    have b17654 := hb (x 8 12)
    clear * - r17648 e17649 e17650 b17651 b17652 b17653 b17654 d17598 d17614 d17594
    omega
  have d17655 : (x 6 2 && x 6 13).toNat = 0 := by
    have r17656 := hand1 (x 6 2) (x 6 13)
    have b17657 := hb (x 6 2)
    have b17658 := hb (x 6 2 && x 6 13)
    clear * - r17656 b17657 b17658 d17647
    omega
  have d17659 : (x 8 13).toNat = 1 := by
    have r17660 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17661 := hb (x 6 2)
    have b17662 := hb (x 8 13)
    have b17663 := hb (x 7 1 && x 7 14)
    clear * - r17660 b17661 b17662 b17663 d17639 d17647
    omega
  have d17664 : (x 8 1).toNat = 1 := by
    have r17665 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
    have b17666 := hb (x 8 1)
    have b17667 := hb (x 8 13)
    clear * - r17665 b17666 b17667 d17659
    omega
  have d17668 : (x 9 14).toNat = 0 := by
    have r17669 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17670 := hb (x 8 1)
    have b17671 := hb (x 9 14)
    clear * - r17669 b17670 b17671 d17664
    omega
  have d17672 : (x 9 3 && x 9 14).toNat = 0 := by
    have r17673 := hand2 (x 9 3) (x 9 14)
    have b17674 := hb (x 9 14)
    have b17675 := hb (x 9 3 && x 9 14)
    clear * - r17673 b17674 b17675 d17668
    omega
  have d17676 : (x 9 2).toNat = 0 := by
    have r17677 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
    have b17678 := hb (x 9 2)
    have b17679 := hb (x 9 14)
    clear * - r17677 b17678 b17679 d17668
    omega
  have d17680 : (x 9 12).toNat = 0 := by
    have r17681 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17682 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e17683 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b17684 := hb (x 6 3)
    have b17685 := hb (x 7 2)
    have b17686 := hb (x 8 13)
    have b17687 := hb (x 9 12)
    clear * - r17681 e17682 e17683 b17684 b17685 b17686 b17687 d17659 d17643
    omega
  have d17688 : (x 9 4).toNat = 0 := by
    have r17689 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
    have b17690 := hb (x 9 4)
    have b17691 := hb (x 9 12)
    clear * - r17689 b17690 b17691 d17680
    omega
  have d17692 : (x 6 3).toNat = 0 := by
    have r17693 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17694 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e17695 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b17696 := hb (x 6 3)
    have b17697 := hb (x 7 2)
    have b17698 := hb (x 8 13)
    have b17699 := hb (x 9 12)
    clear * - r17693 e17694 e17695 b17696 b17697 b17698 b17699 d17680 d17659 d17643
    omega
  have d17700 : (x 6 3 && x 6 14).toNat = 0 := by
    have r17701 := hand1 (x 6 3) (x 6 14)
    have b17702 := hb (x 6 3)
    have b17703 := hb (x 6 3 && x 6 14)
    clear * - r17701 b17702 b17703 d17692
    omega
  have d17704 : (x 9 11).toNat = 1 := by
    have r17705 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17706 := hb (x 5 4)
    have b17707 := hb (x 9 11)
    have b17708 := hb (x 8 1 && x 8 12)
    have b17709 := hb (x 7 2 && x 7 13)
    have b17710 := hb (x 6 3 && x 6 14)
    clear * - r17705 b17706 b17707 b17708 b17709 b17710 d17606 d17622 d17700 d17571
    omega
  have d17711 : (x 9 3).toNat = 1 := by
    have r17712 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
    have b17713 := hb (x 9 3)
    have b17714 := hb (x 9 11)
    clear * - r17712 b17713 b17714 d17704
    omega
  have d17715 : (x 12 12).toNat = 0 := by
    have r17716 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17717 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e17718 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b17719 := hb (x 9 3)
    have b17720 := hb (x 10 2)
    have b17721 := hb (x 11 13)
    have b17722 := hb (x 12 12)
    clear * - r17716 e17717 e17718 b17719 b17720 b17721 b17722 d17711
    omega
  have d17723 : (x 12 1 && x 12 12).toNat = 0 := by
    have r17724 := hand2 (x 12 1) (x 12 12)
    have b17725 := hb (x 12 12)
    have b17726 := hb (x 12 1 && x 12 12)
    clear * - r17724 b17725 b17726 d17715
    omega
  have d17727 : (x 12 4).toNat = 0 := by
    have r17728 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
    have b17729 := hb (x 12 4)
    have b17730 := hb (x 12 12)
    clear * - r17728 b17729 b17730 d17715
    omega
  have d17731 : (x 11 13).toNat = 0 := by
    have r17732 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17733 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e17734 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b17735 := hb (x 9 3)
    have b17736 := hb (x 10 2)
    have b17737 := hb (x 11 13)
    have b17738 := hb (x 12 12)
    clear * - r17732 e17733 e17734 b17735 b17736 b17737 b17738 d17715 d17711
    omega
  have d17739 : (x 11 2 && x 11 13).toNat = 0 := by
    have r17740 := hand2 (x 11 2) (x 11 13)
    have b17741 := hb (x 11 13)
    have b17742 := hb (x 11 2 && x 11 13)
    clear * - r17740 b17741 b17742 d17731
    omega
  have d17743 : (x 10 1 && x 10 14).toNat = 1 := by
    have r17744 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17745 := hb (x 9 2)
    have b17746 := hb (x 11 13)
    have b17747 := hb (x 10 1 && x 10 14)
    clear * - r17744 b17745 b17746 b17747 d17731 d17676
    omega
  have d17748 : (x 10 14).toNat = 1 := by
    have r17749 := hand2 (x 10 1) (x 10 14)
    have b17750 := hb (x 10 14)
    have b17751 := hb (x 10 1 && x 10 14)
    clear * - r17749 b17750 b17751 d17743
    omega
  have d17752 : (x 9 1).toNat = 0 := by
    have r17753 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17754 := hb (x 9 1)
    have b17755 := hb (x 10 14)
    clear * - r17753 b17754 b17755 d17748
    omega
  have d17756 : (x 9 13).toNat = 0 := by
    have r17757 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
    have b17758 := hb (x 9 1)
    have b17759 := hb (x 9 13)
    clear * - r17757 b17758 b17759 d17752
    omega
  have d17760 : (x 8 1 && x 8 14).toNat = 1 := by
    have r17761 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17762 := hb (x 7 2)
    have b17763 := hb (x 9 13)
    have b17764 := hb (x 8 1 && x 8 14)
    clear * - r17761 b17762 b17763 b17764 d17756 d17643
    omega
  have d17765 : (x 8 14).toNat = 1 := by
    have r17766 := hand2 (x 8 1) (x 8 14)
    have b17767 := hb (x 8 14)
    have b17768 := hb (x 8 1 && x 8 14)
    clear * - r17766 b17767 b17768 d17760
    omega
  have d17769 : (x 7 1).toNat = 0 := by
    have r17770 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17771 := hb (x 7 1)
    have b17772 := hb (x 8 14)
    clear * - r17770 b17771 b17772 d17765
    omega
  have d17773 : (x 7 1 && x 7 12).toNat = 0 := by
    have r17774 := hand1 (x 7 1) (x 7 12)
    have b17775 := hb (x 7 1)
    have b17776 := hb (x 7 1 && x 7 12)
    clear * - r17774 b17775 b17776 d17769
    omega
  have d17777 : (x 8 11).toNat = 1 := by
    have r17778 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17779 := hb (x 4 4)
    have b17780 := hb (x 8 11)
    have b17781 := hb (x 7 1 && x 7 12)
    have b17782 := hb (x 6 2 && x 6 13)
    have b17783 := hb (x 5 3 && x 5 14)
    clear * - r17778 b17779 b17780 b17781 b17782 b17783 d17773 d17655 d17555 d17522
    omega
  have d17784 : (x 8 3).toNat = 1 := by
    have r17785 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
    have b17786 := hb (x 8 3)
    have b17787 := hb (x 8 11)
    clear * - r17785 b17786 b17787 d17777
    omega
  have d17788 : (x 11 12).toNat = 0 := by
    have r17789 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17790 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e17791 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b17792 := hb (x 8 3)
    have b17793 := hb (x 9 2)
    have b17794 := hb (x 10 13)
    have b17795 := hb (x 11 12)
    clear * - r17789 e17790 e17791 b17792 b17793 b17794 b17795 d17676 d17784
    omega
  have d17796 : (x 11 1 && x 11 12).toNat = 0 := by
    have r17797 := hand2 (x 11 1) (x 11 12)
    have b17798 := hb (x 11 12)
    have b17799 := hb (x 11 1 && x 11 12)
    clear * - r17797 b17798 b17799 d17788
    omega
  have d17800 : (x 10 13).toNat = 0 := by
    have r17801 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17802 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e17803 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b17804 := hb (x 8 3)
    have b17805 := hb (x 9 2)
    have b17806 := hb (x 10 13)
    have b17807 := hb (x 11 12)
    clear * - r17801 e17802 e17803 b17804 b17805 b17806 b17807 d17788 d17676 d17784
    omega
  have d17808 : (x 10 2 && x 10 13).toNat = 0 := by
    have r17809 := hand2 (x 10 2) (x 10 13)
    have b17810 := hb (x 10 13)
    have b17811 := hb (x 10 2 && x 10 13)
    clear * - r17809 b17810 b17811 d17800
    omega
  have d17812 : (x 12 11).toNat = 1 := by
    have r17813 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17814 := hb (x 8 4)
    have b17815 := hb (x 12 11)
    have b17816 := hb (x 11 1 && x 11 12)
    have b17817 := hb (x 10 2 && x 10 13)
    have b17818 := hb (x 9 3 && x 9 14)
    clear * - r17813 b17814 b17815 b17816 b17817 b17818 d17796 d17808 d17672 d17610
    omega
  have d17819 : (x 12 3).toNat = 1 := by
    have r17820 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
    have b17821 := hb (x 12 3)
    have b17822 := hb (x 12 11)
    clear * - r17820 b17821 b17822 d17812
    omega
  have d17823 : (x 15 12).toNat = 0 := by
    have r17824 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17825 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e17826 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b17827 := hb (x 12 3)
    have b17828 := hb (x 13 2)
    have b17829 := hb (x 14 13)
    have b17830 := hb (x 15 12)
    clear * - r17824 e17825 e17826 b17827 b17828 b17829 b17830 d17819
    omega
  have d17831 : (x 15 1 && x 15 12).toNat = 0 := by
    have r17832 := hand2 (x 15 1) (x 15 12)
    have b17833 := hb (x 15 12)
    have b17834 := hb (x 15 1 && x 15 12)
    clear * - r17832 b17833 b17834 d17823
    omega
  have d17835 : (x 14 13).toNat = 0 := by
    have r17836 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17837 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e17838 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b17839 := hb (x 12 3)
    have b17840 := hb (x 13 2)
    have b17841 := hb (x 14 13)
    have b17842 := hb (x 15 12)
    clear * - r17836 e17837 e17838 b17839 b17840 b17841 b17842 d17823 d17819
    omega
  have d17843 : (x 14 2 && x 14 13).toNat = 0 := by
    have r17844 := hand2 (x 14 2) (x 14 13)
    have b17845 := hb (x 14 13)
    have b17846 := hb (x 14 2 && x 14 13)
    clear * - r17844 b17845 b17846 d17835
    omega
  have d17847 : (x 13 2).toNat = 0 := by
    have r17848 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17849 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e17850 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b17851 := hb (x 12 3)
    have b17852 := hb (x 13 2)
    have b17853 := hb (x 14 13)
    have b17854 := hb (x 15 12)
    clear * - r17848 e17849 e17850 b17851 b17852 b17853 b17854 d17823 d17835 d17819
    omega
  have d17855 : (x 10 1).toNat = 1 := by
    have r17856 := hand1 (x 10 1) (x 10 14)
    have b17857 := hb (x 10 1)
    have b17858 := hb (x 10 1 && x 10 14)
    clear * - r17856 b17857 b17858 d17743
    omega
  have d17859 : (x 11 14).toNat = 0 := by
    have r17860 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17861 := hb (x 10 1)
    have b17862 := hb (x 11 14)
    clear * - r17860 b17861 b17862 d17855
    omega
  have d17863 : (x 11 1 && x 11 14).toNat = 0 := by
    have r17864 := hand2 (x 11 1) (x 11 14)
    have b17865 := hb (x 11 14)
    have b17866 := hb (x 11 1 && x 11 14)
    clear * - r17864 b17865 b17866 d17859
    omega
  have d17867 : (x 11 2).toNat = 0 := by
    have r17868 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
    have b17869 := hb (x 11 2)
    have b17870 := hb (x 11 14)
    clear * - r17868 b17869 b17870 d17859
    omega
  have d17871 : (x 10 2).toNat = 0 := by
    have r17872 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17873 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e17874 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b17875 := hb (x 9 3)
    have b17876 := hb (x 10 2)
    have b17877 := hb (x 11 13)
    have b17878 := hb (x 12 12)
    clear * - r17872 e17873 e17874 b17875 b17876 b17877 b17878 d17715 d17731 d17711
    omega
  have d17879 : (x 12 13).toNat = 1 := by
    have r17880 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17881 := hb (x 10 2)
    have b17882 := hb (x 12 13)
    have b17883 := hb (x 11 1 && x 11 14)
    clear * - r17880 b17881 b17882 b17883 d17863 d17871
    omega
  have d17884 : (x 12 1).toNat = 1 := by
    have r17885 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
    have b17886 := hb (x 12 1)
    have b17887 := hb (x 12 13)
    clear * - r17885 b17886 b17887 d17879
    omega
  have d17888 : (x 13 14).toNat = 0 := by
    have r17889 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17890 := hb (x 12 1)
    have b17891 := hb (x 13 14)
    clear * - r17889 b17890 b17891 d17884
    omega
  have d17892 : (x 13 1 && x 13 14).toNat = 0 := by
    have r17893 := hand2 (x 13 1) (x 13 14)
    have b17894 := hb (x 13 14)
    have b17895 := hb (x 13 1 && x 13 14)
    clear * - r17893 b17894 b17895 d17888
    omega
  have d17896 : (x 12 2).toNat = 1 := by
    have r17897 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17898 := hb (x 12 2)
    have b17899 := hb (x 14 13)
    have b17900 := hb (x 13 1 && x 13 14)
    clear * - r17897 b17898 b17899 b17900 d17835 d17892
    omega
  have d17901 : (x 14 12).toNat = 0 := by
    have r17902 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17903 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e17904 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b17905 := hb (x 11 3)
    have b17906 := hb (x 12 2)
    have b17907 := hb (x 13 13)
    have b17908 := hb (x 14 12)
    clear * - r17902 e17903 e17904 b17905 b17906 b17907 b17908 d17896
    omega
  have d17909 : (x 14 4).toNat = 0 := by
    have r17910 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
    have b17911 := hb (x 14 4)
    have b17912 := hb (x 14 12)
    clear * - r17910 b17911 b17912 d17901
    omega
  have d17913 : (x 14 4 && x 14 14).toNat = 0 := by
    have r17914 := hand1 (x 14 4) (x 14 14)
    have b17915 := hb (x 14 4)
    have b17916 := hb (x 14 4 && x 14 14)
    clear * - r17914 b17915 b17916 d17909
    omega
  have d17917 : (x 13 13).toNat = 0 := by
    have r17918 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17919 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e17920 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b17921 := hb (x 11 3)
    have b17922 := hb (x 12 2)
    have b17923 := hb (x 13 13)
    have b17924 := hb (x 14 12)
    clear * - r17918 e17919 e17920 b17921 b17922 b17923 b17924 d17901 d17896
    omega
  have d17925 : (x 13 5).toNat = 0 := by
    have r17926 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
    have b17927 := hb (x 13 5)
    have b17928 := hb (x 13 13)
    clear * - r17926 b17927 b17928 d17917
    omega
  have d17929 : (x 13 3 && x 13 14).toNat = 0 := by
    have r17930 := hand2 (x 13 3) (x 13 14)
    have b17931 := hb (x 13 14)
    have b17932 := hb (x 13 3 && x 13 14)
    clear * - r17930 b17931 b17932 d17888
    omega
  have d17933 : (x 16 11).toNat = 1 := by
    have r17934 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17935 := hb (x 12 4)
    have b17936 := hb (x 16 11)
    have b17937 := hb (x 15 1 && x 15 12)
    have b17938 := hb (x 14 2 && x 14 13)
    have b17939 := hb (x 13 3 && x 13 14)
    clear * - r17934 b17935 b17936 b17937 b17938 b17939 d17831 d17843 d17929 d17727
    omega
  have d17940 : (x 16 3).toNat = 1 := by
    have r17941 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
    have b17942 := hb (x 16 3)
    have b17943 := hb (x 16 11)
    clear * - r17941 b17942 b17943 d17933
    omega
  have d17944 : (x 19 12).toNat = 0 := by
    have r17945 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17946 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e17947 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have b17948 := hb (x 16 3)
    have b17949 := hb (x 17 2)
    have b17950 := hb (x 18 13)
    have b17951 := hb (x 19 12)
    clear * - r17945 e17946 e17947 b17948 b17949 b17950 b17951 d17940
    omega
  have d17952 : (x 18 13).toNat = 0 := by
    have r17953 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17954 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e17955 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have b17956 := hb (x 16 3)
    have b17957 := hb (x 17 2)
    have b17958 := hb (x 18 13)
    have b17959 := hb (x 19 12)
    clear * - r17953 e17954 e17955 b17956 b17957 b17958 b17959 d17944 d17940
    omega
  have d17960 : (x 17 2).toNat = 0 := by
    have r17961 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17962 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e17963 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have b17964 := hb (x 16 3)
    have b17965 := hb (x 17 2)
    have b17966 := hb (x 18 13)
    have b17967 := hb (x 19 12)
    clear * - r17961 e17962 e17963 b17964 b17965 b17966 b17967 d17944 d17952 d17940
    omega
  have d17968 : (x 13 12).toNat = 0 := by
    have r17969 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17970 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e17971 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b17972 := hb (x 10 3)
    have b17973 := hb (x 11 2)
    have b17974 := hb (x 12 13)
    have b17975 := hb (x 13 12)
    clear * - r17969 e17970 e17971 b17972 b17973 b17974 b17975 d17879 d17867
    omega
  have d17976 : (x 13 4).toNat = 0 := by
    have r17977 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
    have b17978 := hb (x 13 4)
    have b17979 := hb (x 13 12)
    clear * - r17977 b17978 b17979 d17968
    omega
  have d17980 : (x 10 3).toNat = 0 := by
    have r17981 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17982 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e17983 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b17984 := hb (x 10 3)
    have b17985 := hb (x 11 2)
    have b17986 := hb (x 12 13)
    have b17987 := hb (x 13 12)
    clear * - r17981 e17982 e17983 b17984 b17985 b17986 b17987 d17968 d17879 d17867
    omega
  have d17988 : (x 10 3 && x 10 14).toNat = 0 := by
    have r17989 := hand1 (x 10 3) (x 10 14)
    have b17990 := hb (x 10 3)
    have b17991 := hb (x 10 3 && x 10 14)
    clear * - r17989 b17990 b17991 d17980
    omega
  have d17992 : (x 13 11).toNat = 1 := by
    have r17993 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17994 := hb (x 9 4)
    have b17995 := hb (x 13 11)
    have b17996 := hb (x 12 1 && x 12 12)
    have b17997 := hb (x 11 2 && x 11 13)
    have b17998 := hb (x 10 3 && x 10 14)
    clear * - r17993 b17994 b17995 b17996 b17997 b17998 d17723 d17739 d17988 d17688
    omega
  have d17999 : (x 13 3).toNat = 1 := by
    have r18000 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
    have b18001 := hb (x 13 3)
    have b18002 := hb (x 13 11)
    clear * - r18000 b18001 b18002 d17992
    omega
  have d18003 : (x 16 12).toNat = 0 := by
    have r18004 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18005 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e18006 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b18007 := hb (x 13 3)
    have b18008 := hb (x 14 2)
    have b18009 := hb (x 15 13)
    have b18010 := hb (x 16 12)
    clear * - r18004 e18005 e18006 b18007 b18008 b18009 b18010 d17999
    omega
  have d18011 : (x 16 1 && x 16 12).toNat = 0 := by
    have r18012 := hand2 (x 16 1) (x 16 12)
    have b18013 := hb (x 16 12)
    have b18014 := hb (x 16 1 && x 16 12)
    clear * - r18012 b18013 b18014 d18003
    omega
  have d18015 : (x 16 2 && x 16 12).toNat = 0 := by
    have r18016 := hand2 (x 16 2) (x 16 12)
    have b18017 := hb (x 16 12)
    have b18018 := hb (x 16 2 && x 16 12)
    clear * - r18016 b18017 b18018 d18003
    omega
  have d18019 : (x 15 13).toNat = 0 := by
    have r18020 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18021 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e18022 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b18023 := hb (x 13 3)
    have b18024 := hb (x 14 2)
    have b18025 := hb (x 15 13)
    have b18026 := hb (x 16 12)
    clear * - r18020 e18021 e18022 b18023 b18024 b18025 b18026 d18003 d17999
    omega
  have d18027 : (x 15 2 && x 15 13).toNat = 0 := by
    have r18028 := hand2 (x 15 2) (x 15 13)
    have b18029 := hb (x 15 13)
    have b18030 := hb (x 15 2 && x 15 13)
    clear * - r18028 b18029 b18030 d18019
    omega
  have d18031 : (x 15 3 && x 15 13).toNat = 0 := by
    have r18032 := hand2 (x 15 3) (x 15 13)
    have b18033 := hb (x 15 13)
    have b18034 := hb (x 15 3 && x 15 13)
    clear * - r18032 b18033 b18034 d18019
    omega
  have d18035 : (x 14 1 && x 14 14).toNat = 1 := by
    have r18036 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b18037 := hb (x 13 2)
    have b18038 := hb (x 15 13)
    have b18039 := hb (x 14 1 && x 14 14)
    clear * - r18036 b18037 b18038 b18039 d18019 d17847
    omega
  have d18040 : (x 14 1).toNat = 1 := by
    have r18041 := hand1 (x 14 1) (x 14 14)
    have b18042 := hb (x 14 1)
    have b18043 := hb (x 14 1 && x 14 14)
    clear * - r18041 b18042 b18043 d18035
    omega
  have d18044 : (x 15 14).toNat = 0 := by
    have r18045 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b18046 := hb (x 14 1)
    have b18047 := hb (x 15 14)
    clear * - r18045 b18046 b18047 d18040
    omega
  have d18048 : (x 15 1 && x 15 14).toNat = 0 := by
    have r18049 := hand2 (x 15 1) (x 15 14)
    have b18050 := hb (x 15 14)
    have b18051 := hb (x 15 1 && x 15 14)
    clear * - r18049 b18050 b18051 d18044
    omega
  have d18052 : (x 15 2).toNat = 0 := by
    have r18053 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
    have b18054 := hb (x 15 2)
    have b18055 := hb (x 15 14)
    clear * - r18053 b18054 b18055 d18044
    omega
  have d18056 : (x 14 2).toNat = 0 := by
    have r18057 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18058 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e18059 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b18060 := hb (x 13 3)
    have b18061 := hb (x 14 2)
    have b18062 := hb (x 15 13)
    have b18063 := hb (x 16 12)
    clear * - r18057 e18058 e18059 b18060 b18061 b18062 b18063 d18003 d18019 d17999
    omega
  have d18064 : (x 16 13).toNat = 1 := by
    have r18065 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b18066 := hb (x 14 2)
    have b18067 := hb (x 16 13)
    have b18068 := hb (x 15 1 && x 15 14)
    clear * - r18065 b18066 b18067 b18068 d18048 d18056
    omega
  have d18069 : (x 17 12).toNat = 0 := by
    have r18070 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18071 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
    have e18072 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
    have b18073 := hb (x 14 3)
    have b18074 := hb (x 15 2)
    have b18075 := hb (x 16 13)
    have b18076 := hb (x 17 12)
    clear * - r18070 e18071 e18072 b18073 b18074 b18075 b18076 d18064 d18052
    omega
  have d18077 : (x 14 3).toNat = 0 := by
    have r18078 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18079 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
    have e18080 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
    have b18081 := hb (x 14 3)
    have b18082 := hb (x 15 2)
    have b18083 := hb (x 16 13)
    have b18084 := hb (x 17 12)
    clear * - r18078 e18079 e18080 b18081 b18082 b18083 b18084 d18069 d18064 d18052
    omega
  have d18085 : (x 14 3 && x 14 14).toNat = 0 := by
    have r18086 := hand1 (x 14 3) (x 14 14)
    have b18087 := hb (x 14 3)
    have b18088 := hb (x 14 3 && x 14 14)
    clear * - r18086 b18087 b18088 d18077
    omega
  have d18089 : (x 17 11).toNat = 1 := by
    have r18090 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b18091 := hb (x 13 4)
    have b18092 := hb (x 17 11)
    have b18093 := hb (x 16 1 && x 16 12)
    have b18094 := hb (x 15 2 && x 15 13)
    have b18095 := hb (x 14 3 && x 14 14)
    clear * - r18090 b18091 b18092 b18093 b18094 b18095 d18011 d18027 d18085 d17976
    omega
  have d18096 : (x 17 3).toNat = 1 := by
    have r18097 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
    have b18098 := hb (x 17 3)
    have b18099 := hb (x 17 11)
    clear * - r18097 b18098 b18099 d18089
    omega
  have d18100 : (x 20 12).toNat = 0 := by
    have r18101 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18102 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
    have e18103 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
    have b18104 := hb (x 17 3)
    have b18105 := hb (x 18 2)
    have b18106 := hb (x 19 13)
    have b18107 := hb (x 20 12)
    clear * - r18101 e18102 e18103 b18104 b18105 b18106 b18107 d18096
    omega
  have d18108 : (x 19 13).toNat = 0 := by
    have r18109 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18110 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
    have e18111 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
    have b18112 := hb (x 17 3)
    have b18113 := hb (x 18 2)
    have b18114 := hb (x 19 13)
    have b18115 := hb (x 20 12)
    clear * - r18109 e18110 e18111 b18112 b18113 b18114 b18115 d18100 d18096
    omega
  have d18116 : (x 18 1 && x 18 14).toNat = 1 := by
    have r18117 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b18118 := hb (x 17 2)
    have b18119 := hb (x 19 13)
    have b18120 := hb (x 18 1 && x 18 14)
    clear * - r18117 b18118 b18119 b18120 d18108 d17960
    omega
  have d18121 : (x 18 14).toNat = 1 := by
    have r18122 := hand2 (x 18 1) (x 18 14)
    have b18123 := hb (x 18 14)
    have b18124 := hb (x 18 1 && x 18 14)
    clear * - r18122 b18123 b18124 d18116
    omega
  have d18125 : (x 17 1).toNat = 0 := by
    have r18126 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b18127 := hb (x 17 1)
    have b18128 := hb (x 18 14)
    clear * - r18126 b18127 b18128 d18121
    omega
  have d18129 : (x 17 1 && x 17 11).toNat = 0 := by
    have r18130 := hand1 (x 17 1) (x 17 11)
    have b18131 := hb (x 17 1)
    have b18132 := hb (x 17 1 && x 17 11)
    clear * - r18130 b18131 b18132 d18125
    omega
  have d18133 : (x 18 2).toNat = 0 := by
    have r18134 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18135 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
    have e18136 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
    have b18137 := hb (x 17 3)
    have b18138 := hb (x 18 2)
    have b18139 := hb (x 19 13)
    have b18140 := hb (x 20 12)
    clear * - r18134 e18135 e18136 b18137 b18138 b18139 b18140 d18100 d18108 d18096
    omega
  have d18141 : (x 18 10).toNat = 0 := by
    have r18142 : (x 18 10).toNat ≤ (x 18 2).toNat := himp _ _ (hp10 18)
    have b18143 := hb (x 18 2)
    have b18144 := hb (x 18 10)
    clear * - r18142 b18143 b18144 d18133
    omega
  have r18145 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := by have q := hcov10 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have b18146 := hb (x 13 5)
  have b18147 := hb (x 18 10)
  have b18148 := hb (x 17 1 && x 17 11)
  have b18149 := hb (x 16 2 && x 16 12)
  have b18150 := hb (x 15 3 && x 15 13)
  have b18151 := hb (x 14 4 && x 14 14)
  linarith only [r18145, b18146, b18147, b18148, b18149, b18150, b18151, d18141, d18129, d18015, d18031, d17913, d17925]

theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000100_p1 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-4) 11).toNat = 0)
    (g1 : (x (-3) 10).toNat = 0)
    (g2 : (x (-3) 11).toNat = 0)
    (g3 : (x (-2) 5).toNat = 0)
    (g4 : (x (-2) 9).toNat = 0)
    (g5 : (x (-2) 10).toNat = 0)
    (g6 : (x (-2) 11).toNat = 0)
    (g7 : (x (-2) 13).toNat = 0)
    (g8 : (x (-1) 3).toNat = 0)
    (g9 : (x (-1) 5).toNat = 0)
    (g10 : (x (-1) 12).toNat = 1)
    (g11 : (x (-1) 13).toNat = 1)
    (g12 : (x (-1) 14).toNat = 1)
    (g13 : (x 0 3).toNat = 0)
    (g14 : (x 0 4).toNat = 0)
    (g15 : (x 0 5).toNat = 0)
    (g16 : (x 0 6).toNat = 0)
    (g17 : (x 0 7).toNat = 0)
    (g18 : (x 0 8).toNat = 0)
    (g19 : (x 0 9).toNat = 0)
    (g20 : (x 0 10).toNat = 0)
    (g21 : (x 0 11).toNat = 0)
    (g22 : (x 0 12).toNat = 0)
    (g23 : (x 0 13).toNat = 0)
    (g24 : (x 1 2).toNat = 0)
    (g25 : (x 1 4).toNat = 0)
    (g26 : (x 1 5).toNat = 0)
    (g27 : (x 1 9).toNat = 0)
    (g28 : (x 1 10).toNat = 0)
    (g29 : (x 1 12).toNat = 0)
    (g30 : (x 1 14).toNat = 1)
    (g31 : (x 2 1).toNat = 1)
    (g32 : (x 2 13).toNat = 1)
    (g33 : (x 3 2).toNat = 0)
    (g34 : (x 3 4).toNat = 0)
    (g35 : (x 3 6).toNat = 0)
    (g36 : (x 3 10).toNat = 0)
    (g37 : (x 3 12).toNat = 0)
    (g38 : (x 1 2 && x 1 6).toNat = 0)
    (g39 : (x 0 3 && x 0 7).toNat = 0)
    (g40 : (x (-2) 5 && x (-2) 9).toNat = 0)
    (g41 : (x (-3) 6 && x (-3) 10).toNat = 0)
    (g42 : (x (-4) 7 && x (-4) 11).toNat = 0)
    (g43 : (x 1 5 && x 1 9).toNat = 0)
    (g44 : (x 0 6 && x 0 10).toNat = 0)
    (g45 : (x 3 4 && x 3 8).toNat = 0)
    (g46 : (x 1 6 && x 1 10).toNat = 0)
    (g47 : (x 0 7 && x 0 11).toNat = 0)
    (g48 : (x (-2) 9 && x (-2) 13).toNat = 0)
    (g49 : (x 1 9 && x 1 13).toNat = 0)
    (g50 : (x 3 8 && x 3 12).toNat = 0)
    (g51 : (x 3 6 && x 3 11).toNat = 0)
    (g52 : (x 1 8 && x 1 13).toNat = 0)
    (g53 : (x 0 9 && x 0 14).toNat = 0)
    (g54 : (x 3 7 && x 3 12).toNat = 0)
    (g55 : (x 1 9 && x 1 14).toNat = 0)
    (g56 : (x 3 4 && x 3 10).toNat = 0)
    (g57 : (x 1 6 && x 1 12).toNat = 0)
    (g58 : (x 0 7 && x 0 13).toNat = 0)
    (g59 : (x 3 6 && x 3 12).toNat = 0)
    (g60 : (x 1 2 && x 1 9).toNat = 0)
    (g61 : (x 0 3 && x 0 10).toNat = 0)
    (g62 : (x (-2) 5 && x (-2) 12).toNat = 0)
    (g63 : (x 3 4 && x 3 11).toNat = 0)
    (g64 : (x 1 6 && x 1 13).toNat = 0)
    (g65 : (x 0 7 && x 0 14).toNat = 0)
    (g66 : (x (-3) 1 && x (-3) 10).toNat = 0)
    (g67 : (x (-4) 2 && x (-4) 11).toNat = 0)
    (g68 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g69 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g70 : (x (-4) 3 && x (-4) 12).toNat = 0)
    (g71 : (x 0 1 && x 0 10).toNat = 0)
    (g72 : (x (-2) 3 && x (-2) 12).toNat = 0)
    (g73 : (x 1 1 && x 1 10).toNat = 0)
    (g74 : (x 0 2 && x 0 11).toNat = 0)
    (g75 : (x (-2) 4 && x (-2) 13).toNat = 0)
    (g76 : (x 3 3 && x 3 12).toNat = 0)
    (g77 : (x 1 5 && x 1 14).toNat = 0)
    (g78 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g79 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g80 : (x (-3) 2 && x (-3) 12).toNat = 0)
    (g81 : (x (-4) 3 && x (-4) 13).toNat = 0)
    (g82 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g83 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g84 : (x 1 1 && x 1 11).toNat = 0)
    (g85 : (x 0 2 && x 0 12).toNat = 0)
    (g86 : (x 1 2 && x 1 12).toNat = 0)
    (g87 : (x 0 3 && x 0 13).toNat = 0)
    (g88 : (x 3 4 && x 3 14).toNat = 0)
    (g89 : (x (-2) 1 && x (-2) 12).toNat = 0)
    (g90 : (x (-3) 2 && x (-3) 13).toNat = 0)
    (g91 : (x (-4) 3 && x (-4) 14).toNat = 0)
    (g92 : (x 3 2 && x 3 13).toNat = 0)
    (g93 : (x 3 3 && x 3 14).toNat = 0)
    (g94 : (x 3 1 && x 3 14).toNat = 0)
    (h14164 : x 1 3 = true)
    : False := cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000100_p1_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83 g84 g85 g86 g87 g88 g89 g90 g91 g92 g93 g94 h14164
