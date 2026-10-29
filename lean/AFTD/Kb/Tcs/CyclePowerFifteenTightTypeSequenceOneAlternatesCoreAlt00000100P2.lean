import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000100_p2

Topic: combinatorics   Node: 92b48cf369d6

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

Sub-branch of the window refutation cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000100 (one subtree of its case split, cut out so each piece fits the build limit): under the same layer-free tight-cover constraints for k = 15, its fixed bits and the case bits of this subtree, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000100_p2_aux (x : ℤ → Fin 16 → Bool)
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
    (h14164 : x 1 3 = false)
    (h14170 : x (-1) 4 = false)
    (h14336 : x 1 6 = false)
    (h14338 : x (-1) 7 = false)
    (h14340 : x 1 8 = false)
    (h14342 : x (-1) 9 = false)
    (h14479 : x (-2) 4 = false)
    (h14481 : x 2 5 = false)
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
  have f14165 : (x 1 3).toNat = 0 := by rw [h14164]; rfl
  have d14166 : (x 1 11).toNat = 0 := by
    have r14167 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
    have b14168 := hb (x 1 3)
    have b14169 := hb (x 1 11)
    clear * - r14167 b14168 b14169 f14165
    omega
  have f14171 : (x (-1) 4).toNat = 0 := by rw [h14170]; rfl
  have d14172 : (x (-1) 4 && x (-1) 14).toNat = 0 := by
    have r14173 := hand1 (x (-1) 4) (x (-1) 14)
    have b14174 := hb (x (-1) 4)
    have b14175 := hb (x (-1) 4 && x (-1) 14)
    clear * - r14173 b14174 b14175 f14171
    omega
  have d14176 : (x 2 1 && x 2 11).toNat = 1 := by
    have r14177 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14178 := hb (x (-2) 5)
    have b14179 := hb (x 3 10)
    have b14180 := hb (x 2 1 && x 2 11)
    have b14181 := hb (x 1 2 && x 1 12)
    have b14182 := hb (x 0 3 && x 0 13)
    have b14183 := hb (x (-1) 4 && x (-1) 14)
    clear * - r14177 b14178 b14179 b14180 b14181 b14182 b14183 g36 g86 g87 d14172 g3
    omega
  have d14184 : (x 2 11).toNat = 1 := by
    have r14185 := hand2 (x 2 1) (x 2 11)
    have b14186 := hb (x 2 11)
    have b14187 := hb (x 2 1 && x 2 11)
    clear * - r14185 b14186 b14187 d14176
    omega
  have d14188 : (x 2 3).toNat = 1 := by
    have r14189 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
    have b14190 := hb (x 2 3)
    have b14191 := hb (x 2 11)
    clear * - r14189 b14190 b14191 d14184
    omega
  have d14192 : (x 5 12).toNat = 0 := by
    have r14193 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14194 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e14195 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b14196 := hb (x 2 3)
    have b14197 := hb (x 3 2)
    have b14198 := hb (x 4 13)
    have b14199 := hb (x 5 12)
    clear * - r14193 e14194 e14195 b14196 b14197 b14198 b14199 g33 d14188
    omega
  have d14200 : (x 5 1 && x 5 12).toNat = 0 := by
    have r14201 := hand2 (x 5 1) (x 5 12)
    have b14202 := hb (x 5 12)
    have b14203 := hb (x 5 1 && x 5 12)
    clear * - r14201 b14202 b14203 d14192
    omega
  have d14204 : (x 5 2 && x 5 12).toNat = 0 := by
    have r14205 := hand2 (x 5 2) (x 5 12)
    have b14206 := hb (x 5 12)
    have b14207 := hb (x 5 2 && x 5 12)
    clear * - r14205 b14206 b14207 d14192
    omega
  have d14208 : (x 5 4).toNat = 0 := by
    have r14209 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
    have b14210 := hb (x 5 4)
    have b14211 := hb (x 5 12)
    clear * - r14209 b14210 b14211 d14192
    omega
  have d14212 : (x 5 4 && x 5 13).toNat = 0 := by
    have r14213 := hand1 (x 5 4) (x 5 13)
    have b14214 := hb (x 5 4)
    have b14215 := hb (x 5 4 && x 5 13)
    clear * - r14213 b14214 b14215 d14208
    omega
  have d14216 : (x 5 4 && x 5 10).toNat = 0 := by
    have r14217 := hand1 (x 5 4) (x 5 10)
    have b14218 := hb (x 5 4)
    have b14219 := hb (x 5 4 && x 5 10)
    clear * - r14217 b14218 b14219 d14208
    omega
  have d14220 : (x 5 4 && x 5 9).toNat = 0 := by
    have r14221 := hand1 (x 5 4) (x 5 9)
    have b14222 := hb (x 5 4)
    have b14223 := hb (x 5 4 && x 5 9)
    clear * - r14221 b14222 b14223 d14208
    omega
  have d14224 : (x 4 13).toNat = 0 := by
    have r14225 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14226 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e14227 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b14228 := hb (x 2 3)
    have b14229 := hb (x 3 2)
    have b14230 := hb (x 4 13)
    have b14231 := hb (x 5 12)
    clear * - r14225 e14226 e14227 b14228 b14229 b14230 b14231 d14192 g33 d14188
    omega
  have d14232 : (x 4 2 && x 4 13).toNat = 0 := by
    have r14233 := hand2 (x 4 2) (x 4 13)
    have b14234 := hb (x 4 13)
    have b14235 := hb (x 4 2 && x 4 13)
    clear * - r14233 b14234 b14235 d14224
    omega
  have d14236 : (x 4 3 && x 4 13).toNat = 0 := by
    have r14237 := hand2 (x 4 3) (x 4 13)
    have b14238 := hb (x 4 13)
    have b14239 := hb (x 4 3 && x 4 13)
    clear * - r14237 b14238 b14239 d14224
    omega
  have d14240 : (x 4 5).toNat = 0 := by
    have r14241 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
    have b14242 := hb (x 4 5)
    have b14243 := hb (x 4 13)
    clear * - r14241 b14242 b14243 d14224
    omega
  have d14244 : (x 4 5 && x 4 14).toNat = 0 := by
    have r14245 := hand1 (x 4 5) (x 4 14)
    have b14246 := hb (x 4 5)
    have b14247 := hb (x 4 5 && x 4 14)
    clear * - r14245 b14246 b14247 d14240
    omega
  have d14248 : (x 4 5 && x 4 11).toNat = 0 := by
    have r14249 := hand1 (x 4 5) (x 4 11)
    have b14250 := hb (x 4 5)
    have b14251 := hb (x 4 5 && x 4 11)
    clear * - r14249 b14250 b14251 d14240
    omega
  have d14252 : (x 4 5 && x 4 10).toNat = 0 := by
    have r14253 := hand1 (x 4 5) (x 4 10)
    have b14254 := hb (x 4 5)
    have b14255 := hb (x 4 5 && x 4 10)
    clear * - r14253 b14254 b14255 d14240
    omega
  have d14256 : (x 5 8).toNat = 0 := by
    have r14257 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14258 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e14259 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e14260 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e14261 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e14262 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e14263 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b14264 := hb (x (-2) 7)
    have b14265 := hb (x (-1) 6)
    have b14266 := hb (x 0 5)
    have b14267 := hb (x 1 4)
    have b14268 := hb (x 2 11)
    have b14269 := hb (x 3 10)
    have b14270 := hb (x 4 9)
    have b14271 := hb (x 5 8)
    clear * - r14257 e14258 e14259 e14260 e14261 e14262 e14263 b14264 b14265 b14266 b14267 b14268 b14269 b14270 b14271 g36 d14184 g25 g15
    omega
  have d14272 : (x 5 2 && x 5 8).toNat = 0 := by
    have r14273 := hand2 (x 5 2) (x 5 8)
    have b14274 := hb (x 5 8)
    have b14275 := hb (x 5 2 && x 5 8)
    clear * - r14273 b14274 b14275 d14256
    omega
  have d14276 : (x 5 8 && x 5 13).toNat = 0 := by
    have r14277 := hand1 (x 5 8) (x 5 13)
    have b14278 := hb (x 5 8)
    have b14279 := hb (x 5 8 && x 5 13)
    clear * - r14277 b14278 b14279 d14256
    omega
  have d14280 : (x 4 9).toNat = 0 := by
    have r14281 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14282 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e14283 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e14284 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e14285 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e14286 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e14287 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b14288 := hb (x (-2) 7)
    have b14289 := hb (x (-1) 6)
    have b14290 := hb (x 0 5)
    have b14291 := hb (x 1 4)
    have b14292 := hb (x 2 11)
    have b14293 := hb (x 3 10)
    have b14294 := hb (x 4 9)
    have b14295 := hb (x 5 8)
    clear * - r14281 e14282 e14283 e14284 e14285 e14286 e14287 b14288 b14289 b14290 b14291 b14292 b14293 b14294 b14295 d14256 g36 d14184 g25 g15
    omega
  have d14296 : (x 4 3 && x 4 9).toNat = 0 := by
    have r14297 := hand2 (x 4 3) (x 4 9)
    have b14298 := hb (x 4 9)
    have b14299 := hb (x 4 3 && x 4 9)
    clear * - r14297 b14298 b14299 d14280
    omega
  have d14300 : (x 4 9 && x 4 14).toNat = 0 := by
    have r14301 := hand1 (x 4 9) (x 4 14)
    have b14302 := hb (x 4 9)
    have b14303 := hb (x 4 9 && x 4 14)
    clear * - r14301 b14302 b14303 d14280
    omega
  have d14304 : (x (-1) 6).toNat = 0 := by
    have r14305 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14306 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e14307 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e14308 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e14309 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e14310 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e14311 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b14312 := hb (x (-2) 7)
    have b14313 := hb (x (-1) 6)
    have b14314 := hb (x 0 5)
    have b14315 := hb (x 1 4)
    have b14316 := hb (x 2 11)
    have b14317 := hb (x 3 10)
    have b14318 := hb (x 4 9)
    have b14319 := hb (x 5 8)
    clear * - r14305 e14306 e14307 e14308 e14309 e14310 e14311 b14312 b14313 b14314 b14315 b14316 b14317 b14318 b14319 d14256 d14280 g36 d14184 g25 g15
    omega
  have d14320 : (x (-2) 7).toNat = 0 := by
    have r14321 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14322 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e14323 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e14324 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e14325 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e14326 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e14327 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b14328 := hb (x (-2) 7)
    have b14329 := hb (x (-1) 6)
    have b14330 := hb (x 0 5)
    have b14331 := hb (x 1 4)
    have b14332 := hb (x 2 11)
    have b14333 := hb (x 3 10)
    have b14334 := hb (x 4 9)
    have b14335 := hb (x 5 8)
    clear * - r14321 e14322 e14323 e14324 e14325 e14326 e14327 b14328 b14329 b14330 b14331 b14332 b14333 b14334 b14335 d14256 d14280 g36 d14184 g25 g15 d14304
    omega
  have f14337 : (x 1 6).toNat = 0 := by rw [h14336]; rfl
  have f14339 : (x (-1) 7).toNat = 0 := by rw [h14338]; rfl
  have f14341 : (x 1 8).toNat = 0 := by rw [h14340]; rfl
  have f14343 : (x (-1) 9).toNat = 0 := by rw [h14342]; rfl
  have d14344 : (x (-5) 4 && x (-5) 13).toNat = 1 := by
    have r14345 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14346 := hb (x (-7) 6)
    have b14347 := hb (x (-1) 9)
    have b14348 := hb (x (-2) 1 && x (-2) 10)
    have b14349 := hb (x (-3) 2 && x (-3) 11)
    have b14350 := hb (x (-4) 3 && x (-4) 12)
    have b14351 := hb (x (-5) 4 && x (-5) 13)
    have b14352 := hb (x (-6) 5 && x (-6) 14)
    clear * - r14345 b14346 b14347 b14348 b14349 b14350 b14351 b14352 f14343 g68 g69 g70 d14076 d14148
    omega
  have d14353 : (x (-5) 13).toNat = 1 := by
    have r14354 := hand2 (x (-5) 4) (x (-5) 13)
    have b14355 := hb (x (-5) 13)
    have b14356 := hb (x (-5) 4 && x (-5) 13)
    clear * - r14354 b14355 b14356 d14344
    omega
  have d14357 : (x (-5) 1).toNat = 1 := by
    have r14358 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
    have b14359 := hb (x (-5) 1)
    have b14360 := hb (x (-5) 13)
    clear * - r14358 b14359 b14360 d14353
    omega
  have d14361 : (x (-4) 14).toNat = 0 := by
    have r14362 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14363 := hb (x (-5) 1)
    have b14364 := hb (x (-4) 14)
    clear * - r14362 b14363 b14364 d14357
    omega
  have d14365 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
    have r14366 := hand2 (x (-4) 1) (x (-4) 14)
    have b14367 := hb (x (-4) 14)
    have b14368 := hb (x (-4) 1 && x (-4) 14)
    clear * - r14366 b14367 b14368 d14361
    omega
  have d14369 : (x (-4) 6).toNat = 0 := by
    have r14370 : (x (-4) 6).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp6 (-4))
    have b14371 := hb (x (-4) 6)
    have b14372 := hb (x (-4) 14)
    clear * - r14370 b14371 b14372 d14361
    omega
  have d14373 : (x (-4) 2).toNat = 0 := by
    have r14374 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
    have b14375 := hb (x (-4) 2)
    have b14376 := hb (x (-4) 14)
    clear * - r14374 b14375 b14376 d14361
    omega
  have d14377 : (x (-4) 2 && x (-4) 13).toNat = 0 := by
    have r14378 := hand1 (x (-4) 2) (x (-4) 13)
    have b14379 := hb (x (-4) 2)
    have b14380 := hb (x (-4) 2 && x (-4) 13)
    clear * - r14378 b14379 b14380 d14373
    omega
  have d14381 : (x (-4) 2 && x (-4) 12).toNat = 0 := by
    have r14382 := hand1 (x (-4) 2) (x (-4) 12)
    have b14383 := hb (x (-4) 2)
    have b14384 := hb (x (-4) 2 && x (-4) 12)
    clear * - r14382 b14383 b14384 d14373
    omega
  have d14385 : (x (-4) 2 && x (-4) 9).toNat = 0 := by
    have r14386 := hand1 (x (-4) 2) (x (-4) 9)
    have b14387 := hb (x (-4) 2)
    have b14388 := hb (x (-4) 2 && x (-4) 9)
    clear * - r14386 b14387 b14388 d14373
    omega
  have d14389 : (x (-4) 2 && x (-4) 7).toNat = 0 := by
    have r14390 := hand1 (x (-4) 2) (x (-4) 7)
    have b14391 := hb (x (-4) 2)
    have b14392 := hb (x (-4) 2 && x (-4) 7)
    clear * - r14390 b14391 b14392 d14373
    omega
  have d14393 : (x (-4) 10).toNat = 0 := by
    have r14394 : (x (-4) 10).toNat ≤ (x (-4) 2).toNat := himp _ _ (hp10 (-4))
    have b14395 := hb (x (-4) 2)
    have b14396 := hb (x (-4) 10)
    clear * - r14394 b14395 b14396 d14373
    omega
  have d14397 : (x (-4) 1 && x (-4) 10).toNat = 0 := by
    have r14398 := hand2 (x (-4) 1) (x (-4) 10)
    have b14399 := hb (x (-4) 10)
    have b14400 := hb (x (-4) 1 && x (-4) 10)
    clear * - r14398 b14399 b14400 d14393
    omega
  have d14401 : (x (-3) 1 && x (-3) 14).toNat = 1 := by
    have r14402 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14403 := hb (x (-4) 2)
    have b14404 := hb (x (-2) 13)
    have b14405 := hb (x (-3) 1 && x (-3) 14)
    clear * - r14402 b14403 b14404 b14405 g7 d14373
    omega
  have d14406 : (x (-3) 14).toNat = 1 := by
    have r14407 := hand2 (x (-3) 1) (x (-3) 14)
    have b14408 := hb (x (-3) 14)
    have b14409 := hb (x (-3) 1 && x (-3) 14)
    clear * - r14407 b14408 b14409 d14401
    omega
  have d14410 : (x (-4) 1).toNat = 0 := by
    have r14411 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14412 := hb (x (-4) 1)
    have b14413 := hb (x (-3) 14)
    clear * - r14411 b14412 b14413 d14406
    omega
  have d14414 : (x (-4) 13).toNat = 0 := by
    have r14415 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
    have b14416 := hb (x (-4) 1)
    have b14417 := hb (x (-4) 13)
    clear * - r14415 b14416 b14417 d14410
    omega
  have d14418 : (x (-4) 9).toNat = 0 := by
    have r14419 : (x (-4) 9).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp9 (-4))
    have b14420 := hb (x (-4) 1)
    have b14421 := hb (x (-4) 9)
    clear * - r14419 b14420 b14421 d14410
    omega
  have d14422 : (x (-3) 1).toNat = 1 := by
    have r14423 := hand1 (x (-3) 1) (x (-3) 14)
    have b14424 := hb (x (-3) 1)
    have b14425 := hb (x (-3) 1 && x (-3) 14)
    clear * - r14423 b14424 b14425 d14401
    omega
  have d14426 : (x (-2) 14).toNat = 0 := by
    have r14427 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14428 := hb (x (-3) 1)
    have b14429 := hb (x (-2) 14)
    clear * - r14427 b14428 b14429 d14422
    omega
  have d14430 : (x (-2) 4 && x (-2) 14).toNat = 0 := by
    have r14431 := hand2 (x (-2) 4) (x (-2) 14)
    have b14432 := hb (x (-2) 14)
    have b14433 := hb (x (-2) 4 && x (-2) 14)
    clear * - r14431 b14432 b14433 d14426
    omega
  have d14434 : (x (-2) 6).toNat = 0 := by
    have r14435 : (x (-2) 6).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp6 (-2))
    have b14436 := hb (x (-2) 6)
    have b14437 := hb (x (-2) 14)
    clear * - r14435 b14436 b14437 d14426
    omega
  have d14438 : (x (-4) 12).toNat = 0 := by
    have r14439 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14440 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e14441 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b14442 := hb (x (-7) 3)
    have b14443 := hb (x (-6) 2)
    have b14444 := hb (x (-5) 13)
    have b14445 := hb (x (-4) 12)
    clear * - r14439 e14440 e14441 b14442 b14443 b14444 b14445 d14353
    omega
  have d14446 : (x (-6) 2).toNat = 0 := by
    have r14447 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14448 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e14449 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b14450 := hb (x (-7) 3)
    have b14451 := hb (x (-6) 2)
    have b14452 := hb (x (-5) 13)
    have b14453 := hb (x (-4) 12)
    clear * - r14447 e14448 e14449 b14450 b14451 b14452 b14453 d14438 d14353
    omega
  have d14454 : (x (-5) 1 && x (-5) 14).toNat = 1 := by
    have r14455 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14456 := hb (x (-6) 2)
    have b14457 := hb (x (-4) 13)
    have b14458 := hb (x (-5) 1 && x (-5) 14)
    clear * - r14455 b14456 b14457 b14458 d14414 d14446
    omega
  have d14459 : (x (-5) 14).toNat = 1 := by
    have r14460 := hand2 (x (-5) 1) (x (-5) 14)
    have b14461 := hb (x (-5) 14)
    have b14462 := hb (x (-5) 1 && x (-5) 14)
    clear * - r14460 b14461 b14462 d14454
    omega
  have d14463 : (x (-6) 1).toNat = 0 := by
    have r14464 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14465 := hb (x (-6) 1)
    have b14466 := hb (x (-5) 14)
    clear * - r14464 b14465 b14466 d14459
    omega
  have d14467 : (x (-6) 1 && x (-6) 12).toNat = 0 := by
    have r14468 := hand1 (x (-6) 1) (x (-6) 12)
    have b14469 := hb (x (-6) 1)
    have b14470 := hb (x (-6) 1 && x (-6) 12)
    clear * - r14468 b14469 b14470 d14463
    omega
  have d14471 : (x (-6) 9).toNat = 0 := by
    have r14472 : (x (-6) 9).toNat ≤ (x (-6) 1).toNat := himp _ _ (hp9 (-6))
    have b14473 := hb (x (-6) 1)
    have b14474 := hb (x (-6) 9)
    clear * - r14472 b14473 b14474 d14463
    omega
  have d14475 : (x (-6) 4 && x (-6) 9).toNat = 0 := by
    have r14476 := hand2 (x (-6) 4) (x (-6) 9)
    have b14477 := hb (x (-6) 9)
    have b14478 := hb (x (-6) 4 && x (-6) 9)
    clear * - r14476 b14477 b14478 d14471
    omega
  have f14480 : (x (-2) 4).toNat = 0 := by rw [h14479]; rfl
  have f14482 : (x 2 5).toNat = 0 := by rw [h14481]; rfl
  have d14483 : (x 2 5 && x 2 11).toNat = 0 := by
    have r14484 := hand1 (x 2 5) (x 2 11)
    have b14485 := hb (x 2 5)
    have b14486 := hb (x 2 5 && x 2 11)
    clear * - r14484 b14485 b14486 f14482
    omega
  have d14487 : (x (-5) 8 && x (-5) 12).toNat = 1 := by
    have r14488 : 1 ≤ (x 3 4).toNat + (x 2 1 && x 2 5).toNat + (x 1 2 && x 1 6).toNat + (x 0 3 && x 0 7).toNat + (x (-1) 4 && x (-1) 8).toNat + (x (-2) 5 && x (-2) 9).toNat + (x (-3) 6 && x (-3) 10).toNat + (x (-4) 7 && x (-4) 11).toNat + (x (-5) 8 && x (-5) 12).toNat + (x (-6) 9 && x (-6) 13).toNat + (x (-7) 10 && x (-7) 14).toNat + (x (-8) 11).toNat := by have q := hcov4 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14489 : (x 2 1 && x 2 5).toNat = (x 2 5).toNat := handr _ _ (fun h => hp13 2 (hp5 2 (h)))
    have e14490 : (x (-7) 10 && x (-7) 14).toNat = (x (-7) 10).toNat := handl _ _ (fun h => hp2 (-7) (hp10 (-7) (h)))
    have b14491 := hb (x (-8) 11)
    have b14492 := hb (x (-7) 10)
    have b14493 := hb (x 2 5)
    have b14494 := hb (x 3 4)
    have b14495 := hb (x 1 2 && x 1 6)
    have b14496 := hb (x 0 3 && x 0 7)
    have b14497 := hb (x (-1) 4 && x (-1) 8)
    have b14498 := hb (x (-2) 5 && x (-2) 9)
    have b14499 := hb (x (-3) 6 && x (-3) 10)
    have b14500 := hb (x (-4) 7 && x (-4) 11)
    have b14501 := hb (x (-5) 8 && x (-5) 12)
    have b14502 := hb (x (-6) 9 && x (-6) 13)
    clear * - r14488 e14489 e14490 b14491 b14492 b14493 b14494 b14495 b14496 b14497 b14498 b14499 b14500 b14501 b14502 g34 f14482 g38 g39 d14144 g40 g41 g42 d14068 d14092 d14112
    omega
  have d14503 : (x (-5) 8).toNat = 1 := by
    have r14504 := hand1 (x (-5) 8) (x (-5) 12)
    have b14505 := hb (x (-5) 8)
    have b14506 := hb (x (-5) 8 && x (-5) 12)
    clear * - r14504 b14505 b14506 d14487
    omega
  have d14507 : (x (-9) 4).toNat = 0 := by
    have r14508 : (x (-5) 8).toNat + (x (-6) 1 && x (-6) 9).toNat + (x (-7) 2 && x (-7) 10).toNat + (x (-8) 3 && x (-8) 11).toNat + (x (-9) 4 && x (-9) 12).toNat + (x (-10) 5 && x (-10) 13).toNat + (x (-11) 6 && x (-11) 14).toNat + (x (-12) 7).toNat = 1 := by have q := hd8 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14509 : (x (-6) 1 && x (-6) 9).toNat = (x (-6) 9).toNat := handr _ _ (fun h => hp9 (-6) (h))
    have e14510 : (x (-7) 2 && x (-7) 10).toNat = (x (-7) 10).toNat := handr _ _ (fun h => hp10 (-7) (h))
    have e14511 : (x (-8) 3 && x (-8) 11).toNat = (x (-8) 11).toNat := handr _ _ (fun h => hp11 (-8) (h))
    have e14512 : (x (-9) 4 && x (-9) 12).toNat = (x (-9) 4).toNat := handl _ _ (fun h => hp4 (-9) (h))
    have e14513 : (x (-10) 5 && x (-10) 13).toNat = (x (-10) 5).toNat := handl _ _ (fun h => hp5 (-10) (h))
    have e14514 : (x (-11) 6 && x (-11) 14).toNat = (x (-11) 6).toNat := handl _ _ (fun h => hp6 (-11) (h))
    have b14515 := hb (x (-12) 7)
    have b14516 := hb (x (-11) 6)
    have b14517 := hb (x (-10) 5)
    have b14518 := hb (x (-9) 4)
    have b14519 := hb (x (-8) 11)
    have b14520 := hb (x (-7) 10)
    have b14521 := hb (x (-6) 9)
    have b14522 := hb (x (-5) 8)
    clear * - r14508 e14509 e14510 e14511 e14512 e14513 e14514 b14515 b14516 b14517 b14518 b14519 b14520 b14521 b14522 d14503 d14471 d14092 d14112
    omega
  have d14523 : (x (-5) 11).toNat = 1 := by
    have r14524 : 1 ≤ (x (-5) 11).toNat + (x (-6) 1 && x (-6) 12).toNat + (x (-7) 2 && x (-7) 13).toNat + (x (-8) 3 && x (-8) 14).toNat + (x (-9) 4).toNat := by have q := hcov11 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14525 := hb (x (-9) 4)
    have b14526 := hb (x (-5) 11)
    have b14527 := hb (x (-6) 1 && x (-6) 12)
    have b14528 := hb (x (-7) 2 && x (-7) 13)
    have b14529 := hb (x (-8) 3 && x (-8) 14)
    clear * - r14524 b14525 b14526 b14527 b14528 b14529 d14467 d14088 d14108 d14507
    omega
  have d14530 : (x (-5) 3).toNat = 1 := by
    have r14531 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
    have b14532 := hb (x (-5) 3)
    have b14533 := hb (x (-5) 11)
    clear * - r14531 b14532 b14533 d14523
    omega
  have d14534 : (x (-2) 12).toNat = 0 := by
    have r14535 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14536 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
    have e14537 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
    have b14538 := hb (x (-5) 3)
    have b14539 := hb (x (-4) 2)
    have b14540 := hb (x (-3) 13)
    have b14541 := hb (x (-2) 12)
    clear * - r14535 e14536 e14537 b14538 b14539 b14540 b14541 d14373 d14530
    omega
  have d14542 : (x (-3) 13).toNat = 0 := by
    have r14543 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14544 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
    have e14545 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
    have b14546 := hb (x (-5) 3)
    have b14547 := hb (x (-4) 2)
    have b14548 := hb (x (-3) 13)
    have b14549 := hb (x (-2) 12)
    clear * - r14543 e14544 e14545 b14546 b14547 b14548 b14549 d14534 d14373 d14530
    omega
  have d14550 : (x (-3) 5).toNat = 0 := by
    have r14551 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
    have b14552 := hb (x (-3) 5)
    have b14553 := hb (x (-3) 13)
    clear * - r14551 b14552 b14553 d14542
    omega
  have d14554 : (x (-3) 5 && x (-3) 14).toNat = 0 := by
    have r14555 := hand1 (x (-3) 5) (x (-3) 14)
    have b14556 := hb (x (-3) 5)
    have b14557 := hb (x (-3) 5 && x (-3) 14)
    clear * - r14555 b14556 b14557 d14550
    omega
  have d14558 : (x 2 9).toNat = 1 := by
    have r14559 : 1 ≤ (x 2 9).toNat + (x 1 1 && x 1 10).toNat + (x 0 2 && x 0 11).toNat + (x (-1) 3 && x (-1) 12).toNat + (x (-2) 4 && x (-2) 13).toNat + (x (-3) 5 && x (-3) 14).toNat + (x (-4) 6).toNat := by have q := hcov9 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14560 := hb (x (-4) 6)
    have b14561 := hb (x 2 9)
    have b14562 := hb (x 1 1 && x 1 10)
    have b14563 := hb (x 0 2 && x 0 11)
    have b14564 := hb (x (-1) 3 && x (-1) 12)
    have b14565 := hb (x (-2) 4 && x (-2) 13)
    have b14566 := hb (x (-3) 5 && x (-3) 14)
    clear * - r14559 b14560 b14561 b14562 b14563 b14564 b14565 b14566 g73 g74 d14021 g75 d14554 d14369
    omega
  have d14567 : (x 3 8).toNat = 0 := by
    have r14568 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14569 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
    have e14570 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
    have e14571 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
    have e14572 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
    have e14573 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
    have e14574 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
    have b14575 := hb (x (-4) 7)
    have b14576 := hb (x (-3) 6)
    have b14577 := hb (x (-2) 5)
    have b14578 := hb (x (-1) 4)
    have b14579 := hb (x 0 11)
    have b14580 := hb (x 1 10)
    have b14581 := hb (x 2 9)
    have b14582 := hb (x 3 8)
    clear * - r14568 e14569 e14570 e14571 e14572 e14573 e14574 b14575 b14576 b14577 b14578 b14579 b14580 b14581 b14582 d14558 g28 g21 f14171 g3
    omega
  have d14583 : (x 2 10).toNat = 1 := by
    have r14584 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14585 := hb (x (-3) 5)
    have b14586 := hb (x 2 10)
    have b14587 := hb (x 1 1 && x 1 11)
    have b14588 := hb (x 0 2 && x 0 12)
    have b14589 := hb (x (-1) 3 && x (-1) 13)
    have b14590 := hb (x (-2) 4 && x (-2) 14)
    clear * - r14584 b14585 b14586 b14587 b14588 b14589 b14590 g84 g85 d14017 d14430 d14550
    omega
  have d14591 : (x 4 8).toNat = 0 := by
    have r14592 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14593 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e14594 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e14595 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e14596 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e14597 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e14598 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b14599 := hb (x (-3) 7)
    have b14600 := hb (x (-2) 6)
    have b14601 := hb (x (-1) 5)
    have b14602 := hb (x 0 4)
    have b14603 := hb (x 1 11)
    have b14604 := hb (x 2 10)
    have b14605 := hb (x 3 9)
    have b14606 := hb (x 4 8)
    clear * - r14592 e14593 e14594 e14595 e14596 e14597 e14598 b14599 b14600 b14601 b14602 b14603 b14604 b14605 b14606 d14583 d14166 g14 g9 d14434
    omega
  have d14607 : (x 3 9).toNat = 0 := by
    have r14608 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14609 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e14610 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e14611 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e14612 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e14613 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e14614 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b14615 := hb (x (-3) 7)
    have b14616 := hb (x (-2) 6)
    have b14617 := hb (x (-1) 5)
    have b14618 := hb (x 0 4)
    have b14619 := hb (x 1 11)
    have b14620 := hb (x 2 10)
    have b14621 := hb (x 3 9)
    have b14622 := hb (x 4 8)
    clear * - r14608 e14609 e14610 e14611 e14612 e14613 e14614 b14615 b14616 b14617 b14618 b14619 b14620 b14621 b14622 d14591 d14583 d14166 g14 g9 d14434
    omega
  have d14623 : (x 10 1).toNat = 0 := by
    have r14624 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14625 := hb (x (-3) 14)
    have b14626 := hb (x (-2) 13)
    have b14627 := hb (x (-1) 12)
    have b14628 := hb (x 0 11)
    have b14629 := hb (x 1 10)
    have b14630 := hb (x 2 9)
    have b14631 := hb (x 3 8)
    have b14632 := hb (x 4 7)
    have b14633 := hb (x 5 6)
    have b14634 := hb (x 6 5)
    have b14635 := hb (x 7 4)
    have b14636 := hb (x 8 3)
    have b14637 := hb (x 9 2)
    have b14638 := hb (x 10 1)
    clear * - r14624 b14625 b14626 b14627 b14628 b14629 b14630 b14631 b14632 b14633 b14634 b14635 b14636 b14637 b14638 d14567 d14558 g28 g21 g10 g7 d14406
    omega
  have d14639 : (x 10 1 && x 10 14).toNat = 0 := by
    have r14640 := hand1 (x 10 1) (x 10 14)
    have b14641 := hb (x 10 1)
    have b14642 := hb (x 10 1 && x 10 14)
    clear * - r14640 b14641 b14642 d14623
    omega
  have d14643 : (x 9 2).toNat = 0 := by
    have r14644 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14645 := hb (x (-3) 14)
    have b14646 := hb (x (-2) 13)
    have b14647 := hb (x (-1) 12)
    have b14648 := hb (x 0 11)
    have b14649 := hb (x 1 10)
    have b14650 := hb (x 2 9)
    have b14651 := hb (x 3 8)
    have b14652 := hb (x 4 7)
    have b14653 := hb (x 5 6)
    have b14654 := hb (x 6 5)
    have b14655 := hb (x 7 4)
    have b14656 := hb (x 8 3)
    have b14657 := hb (x 9 2)
    have b14658 := hb (x 10 1)
    clear * - r14644 b14645 b14646 b14647 b14648 b14649 b14650 b14651 b14652 b14653 b14654 b14655 b14656 b14657 b14658 d14623 d14567 d14558 g28 g21 g10 g7 d14406
    omega
  have d14659 : (x 11 13).toNat = 1 := by
    have r14660 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14661 := hb (x 9 2)
    have b14662 := hb (x 11 13)
    have b14663 := hb (x 10 1 && x 10 14)
    clear * - r14660 b14661 b14662 b14663 d14639 d14643
    omega
  have d14664 : (x 11 1).toNat = 1 := by
    have r14665 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
    have b14666 := hb (x 11 1)
    have b14667 := hb (x 11 13)
    clear * - r14665 b14666 b14667 d14659
    omega
  have d14668 : (x 12 14).toNat = 0 := by
    have r14669 : (x 12 14).toNat + (x 11 1).toNat = 1 := by have q := hd14 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14670 := hb (x 11 1)
    have b14671 := hb (x 12 14)
    clear * - r14669 b14670 b14671 d14664
    omega
  have d14672 : (x 12 1 && x 12 14).toNat = 0 := by
    have r14673 := hand2 (x 12 1) (x 12 14)
    have b14674 := hb (x 12 14)
    have b14675 := hb (x 12 1 && x 12 14)
    clear * - r14673 b14674 b14675 d14668
    omega
  have d14676 : (x 12 2).toNat = 0 := by
    have r14677 : (x 12 2).toNat ≤ (x 12 14).toNat := himp _ _ (hp2 12)
    have b14678 := hb (x 12 2)
    have b14679 := hb (x 12 14)
    clear * - r14677 b14678 b14679 d14668
    omega
  have d14680 : (x 12 10).toNat = 0 := by
    have r14681 : (x 12 10).toNat ≤ (x 12 2).toNat := himp _ _ (hp10 12)
    have b14682 := hb (x 12 2)
    have b14683 := hb (x 12 10)
    clear * - r14681 b14682 b14683 d14676
    omega
  have d14684 : (x 10 2).toNat = 0 := by
    have r14685 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14686 := hb (x (-2) 14)
    have b14687 := hb (x (-1) 13)
    have b14688 := hb (x 0 12)
    have b14689 := hb (x 1 11)
    have b14690 := hb (x 2 10)
    have b14691 := hb (x 3 9)
    have b14692 := hb (x 4 8)
    have b14693 := hb (x 5 7)
    have b14694 := hb (x 6 6)
    have b14695 := hb (x 7 5)
    have b14696 := hb (x 8 4)
    have b14697 := hb (x 9 3)
    have b14698 := hb (x 10 2)
    have b14699 := hb (x 11 1)
    clear * - r14685 b14686 b14687 b14688 b14689 b14690 b14691 b14692 b14693 b14694 b14695 b14696 b14697 b14698 b14699 d14664 d14591 d14607 d14583 d14166 g22 g11 d14426
    omega
  have d14700 : (x 10 2 && x 10 12).toNat = 0 := by
    have r14701 := hand1 (x 10 2) (x 10 12)
    have b14702 := hb (x 10 2)
    have b14703 := hb (x 10 2 && x 10 12)
    clear * - r14701 b14702 b14703 d14684
    omega
  have d14704 : (x 9 3).toNat = 0 := by
    have r14705 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14706 := hb (x (-2) 14)
    have b14707 := hb (x (-1) 13)
    have b14708 := hb (x 0 12)
    have b14709 := hb (x 1 11)
    have b14710 := hb (x 2 10)
    have b14711 := hb (x 3 9)
    have b14712 := hb (x 4 8)
    have b14713 := hb (x 5 7)
    have b14714 := hb (x 6 6)
    have b14715 := hb (x 7 5)
    have b14716 := hb (x 8 4)
    have b14717 := hb (x 9 3)
    have b14718 := hb (x 10 2)
    have b14719 := hb (x 11 1)
    clear * - r14705 b14706 b14707 b14708 b14709 b14710 b14711 b14712 b14713 b14714 b14715 b14716 b14717 b14718 b14719 d14664 d14684 d14591 d14607 d14583 d14166 g22 g11 d14426
    omega
  have d14720 : (x 9 3 && x 9 13).toNat = 0 := by
    have r14721 := hand1 (x 9 3) (x 9 13)
    have b14722 := hb (x 9 3)
    have b14723 := hb (x 9 3 && x 9 13)
    clear * - r14721 b14722 b14723 d14704
    omega
  have d14724 : (x 8 4).toNat = 0 := by
    have r14725 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14726 := hb (x (-2) 14)
    have b14727 := hb (x (-1) 13)
    have b14728 := hb (x 0 12)
    have b14729 := hb (x 1 11)
    have b14730 := hb (x 2 10)
    have b14731 := hb (x 3 9)
    have b14732 := hb (x 4 8)
    have b14733 := hb (x 5 7)
    have b14734 := hb (x 6 6)
    have b14735 := hb (x 7 5)
    have b14736 := hb (x 8 4)
    have b14737 := hb (x 9 3)
    have b14738 := hb (x 10 2)
    have b14739 := hb (x 11 1)
    clear * - r14725 b14726 b14727 b14728 b14729 b14730 b14731 b14732 b14733 b14734 b14735 b14736 b14737 b14738 b14739 d14664 d14684 d14704 d14591 d14607 d14583 d14166 g22 g11 d14426
    omega
  have d14740 : (x 8 4 && x 8 14).toNat = 0 := by
    have r14741 := hand1 (x 8 4) (x 8 14)
    have b14742 := hb (x 8 4)
    have b14743 := hb (x 8 4 && x 8 14)
    clear * - r14741 b14742 b14743 d14724
    omega
  have d14744 : (x 7 5).toNat = 0 := by
    have r14745 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14746 := hb (x (-2) 14)
    have b14747 := hb (x (-1) 13)
    have b14748 := hb (x 0 12)
    have b14749 := hb (x 1 11)
    have b14750 := hb (x 2 10)
    have b14751 := hb (x 3 9)
    have b14752 := hb (x 4 8)
    have b14753 := hb (x 5 7)
    have b14754 := hb (x 6 6)
    have b14755 := hb (x 7 5)
    have b14756 := hb (x 8 4)
    have b14757 := hb (x 9 3)
    have b14758 := hb (x 10 2)
    have b14759 := hb (x 11 1)
    clear * - r14745 b14746 b14747 b14748 b14749 b14750 b14751 b14752 b14753 b14754 b14755 b14756 b14757 b14758 b14759 d14664 d14684 d14704 d14724 d14591 d14607 d14583 d14166 g22 g11 d14426
    omega
  have d14760 : (x 11 1 && x 11 11).toNat = 1 := by
    have r14761 : 1 ≤ (x 12 10).toNat + (x 11 1 && x 11 11).toNat + (x 10 2 && x 10 12).toNat + (x 9 3 && x 9 13).toNat + (x 8 4 && x 8 14).toNat + (x 7 5).toNat := by have q := hcov10 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14762 := hb (x 7 5)
    have b14763 := hb (x 12 10)
    have b14764 := hb (x 11 1 && x 11 11)
    have b14765 := hb (x 10 2 && x 10 12)
    have b14766 := hb (x 9 3 && x 9 13)
    have b14767 := hb (x 8 4 && x 8 14)
    clear * - r14761 b14762 b14763 b14764 b14765 b14766 b14767 d14680 d14700 d14720 d14740 d14744
    omega
  have d14768 : (x 11 11).toNat = 1 := by
    have r14769 := hand2 (x 11 1) (x 11 11)
    have b14770 := hb (x 11 11)
    have b14771 := hb (x 11 1 && x 11 11)
    clear * - r14769 b14770 b14771 d14760
    omega
  have d14772 : (x 11 3).toNat = 1 := by
    have r14773 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
    have b14774 := hb (x 11 3)
    have b14775 := hb (x 11 11)
    clear * - r14773 b14774 b14775 d14768
    omega
  have d14776 : (x 14 12).toNat = 0 := by
    have r14777 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14778 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e14779 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b14780 := hb (x 11 3)
    have b14781 := hb (x 12 2)
    have b14782 := hb (x 13 13)
    have b14783 := hb (x 14 12)
    clear * - r14777 e14778 e14779 b14780 b14781 b14782 b14783 d14676 d14772
    omega
  have d14784 : (x 13 13).toNat = 0 := by
    have r14785 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14786 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e14787 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b14788 := hb (x 11 3)
    have b14789 := hb (x 12 2)
    have b14790 := hb (x 13 13)
    have b14791 := hb (x 14 12)
    clear * - r14785 e14786 e14787 b14788 b14789 b14790 b14791 d14776 d14676 d14772
    omega
  have d14792 : (x 11 2).toNat = 1 := by
    have r14793 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14794 := hb (x 11 2)
    have b14795 := hb (x 13 13)
    have b14796 := hb (x 12 1 && x 12 14)
    clear * - r14793 b14794 b14795 b14796 d14784 d14672
    omega
  have d14797 : (x 13 12).toNat = 0 := by
    have r14798 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14799 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e14800 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b14801 := hb (x 10 3)
    have b14802 := hb (x 11 2)
    have b14803 := hb (x 12 13)
    have b14804 := hb (x 13 12)
    clear * - r14798 e14799 e14800 b14801 b14802 b14803 b14804 d14792
    omega
  have d14805 : (x 12 13).toNat = 0 := by
    have r14806 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14807 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e14808 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b14809 := hb (x 10 3)
    have b14810 := hb (x 11 2)
    have b14811 := hb (x 12 13)
    have b14812 := hb (x 13 12)
    clear * - r14806 e14807 e14808 b14809 b14810 b14811 b14812 d14797 d14792
    omega
  have d14813 : (x 10 3).toNat = 0 := by
    have r14814 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14815 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e14816 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b14817 := hb (x 10 3)
    have b14818 := hb (x 11 2)
    have b14819 := hb (x 12 13)
    have b14820 := hb (x 13 12)
    clear * - r14814 e14815 e14816 b14817 b14818 b14819 b14820 d14797 d14805 d14792
    omega
  have d14821 : (x 12 1).toNat = 0 := by
    have r14822 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14823 := hb (x (-1) 14)
    have b14824 := hb (x 0 13)
    have b14825 := hb (x 1 12)
    have b14826 := hb (x 2 11)
    have b14827 := hb (x 3 10)
    have b14828 := hb (x 4 9)
    have b14829 := hb (x 5 8)
    have b14830 := hb (x 6 7)
    have b14831 := hb (x 7 6)
    have b14832 := hb (x 8 5)
    have b14833 := hb (x 9 4)
    have b14834 := hb (x 10 3)
    have b14835 := hb (x 11 2)
    have b14836 := hb (x 12 1)
    clear * - r14822 b14823 b14824 b14825 b14826 b14827 b14828 b14829 b14830 b14831 b14832 b14833 b14834 b14835 b14836 d14792 d14813 d14256 d14280 g36 d14184 g29 g23 g12
    omega
  have d14837 : (x 9 4).toNat = 0 := by
    have r14838 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14839 := hb (x (-1) 14)
    have b14840 := hb (x 0 13)
    have b14841 := hb (x 1 12)
    have b14842 := hb (x 2 11)
    have b14843 := hb (x 3 10)
    have b14844 := hb (x 4 9)
    have b14845 := hb (x 5 8)
    have b14846 := hb (x 6 7)
    have b14847 := hb (x 7 6)
    have b14848 := hb (x 8 5)
    have b14849 := hb (x 9 4)
    have b14850 := hb (x 10 3)
    have b14851 := hb (x 11 2)
    have b14852 := hb (x 12 1)
    clear * - r14838 b14839 b14840 b14841 b14842 b14843 b14844 b14845 b14846 b14847 b14848 b14849 b14850 b14851 b14852 d14821 d14792 d14813 d14256 d14280 g36 d14184 g29 g23 g12
    omega
  have d14853 : (x 8 5).toNat = 0 := by
    have r14854 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14855 := hb (x (-1) 14)
    have b14856 := hb (x 0 13)
    have b14857 := hb (x 1 12)
    have b14858 := hb (x 2 11)
    have b14859 := hb (x 3 10)
    have b14860 := hb (x 4 9)
    have b14861 := hb (x 5 8)
    have b14862 := hb (x 6 7)
    have b14863 := hb (x 7 6)
    have b14864 := hb (x 8 5)
    have b14865 := hb (x 9 4)
    have b14866 := hb (x 10 3)
    have b14867 := hb (x 11 2)
    have b14868 := hb (x 12 1)
    clear * - r14854 b14855 b14856 b14857 b14858 b14859 b14860 b14861 b14862 b14863 b14864 b14865 b14866 b14867 b14868 d14821 d14792 d14813 d14837 d14256 d14280 g36 d14184 g29 g23 g12
    omega
  have d14869 : (x 7 6).toNat = 0 := by
    have r14870 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14871 := hb (x (-1) 14)
    have b14872 := hb (x 0 13)
    have b14873 := hb (x 1 12)
    have b14874 := hb (x 2 11)
    have b14875 := hb (x 3 10)
    have b14876 := hb (x 4 9)
    have b14877 := hb (x 5 8)
    have b14878 := hb (x 6 7)
    have b14879 := hb (x 7 6)
    have b14880 := hb (x 8 5)
    have b14881 := hb (x 9 4)
    have b14882 := hb (x 10 3)
    have b14883 := hb (x 11 2)
    have b14884 := hb (x 12 1)
    clear * - r14870 b14871 b14872 b14873 b14874 b14875 b14876 b14877 b14878 b14879 b14880 b14881 b14882 b14883 b14884 d14821 d14792 d14813 d14837 d14853 d14256 d14280 g36 d14184 g29 g23 g12
    omega
  have d14885 : (x 6 1 && x 6 7).toNat = 1 := by
    have r14886 : 1 ≤ (x 7 6).toNat + (x 6 1 && x 6 7).toNat + (x 5 2 && x 5 8).toNat + (x 4 3 && x 4 9).toNat + (x 3 4 && x 3 10).toNat + (x 2 5 && x 2 11).toNat + (x 1 6 && x 1 12).toNat + (x 0 7 && x 0 13).toNat + (x (-1) 8 && x (-1) 14).toNat + (x (-2) 9).toNat := by have q := hcov6 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14887 := hb (x (-2) 9)
    have b14888 := hb (x 7 6)
    have b14889 := hb (x 6 1 && x 6 7)
    have b14890 := hb (x 5 2 && x 5 8)
    have b14891 := hb (x 4 3 && x 4 9)
    have b14892 := hb (x 3 4 && x 3 10)
    have b14893 := hb (x 2 5 && x 2 11)
    have b14894 := hb (x 1 6 && x 1 12)
    have b14895 := hb (x 0 7 && x 0 13)
    have b14896 := hb (x (-1) 8 && x (-1) 14)
    clear * - r14886 b14887 b14888 b14889 b14890 b14891 b14892 b14893 b14894 b14895 b14896 d14869 d14272 d14296 g56 d14483 g57 g58 d14136 g4
    omega
  have d14897 : (x 6 7).toNat = 1 := by
    have r14898 := hand2 (x 6 1) (x 6 7)
    have b14899 := hb (x 6 7)
    have b14900 := hb (x 6 1 && x 6 7)
    clear * - r14898 b14899 b14900 d14885
    omega
  have r14901 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have b14902 := hb (x (-1) 14)
  have b14903 := hb (x 0 13)
  have b14904 := hb (x 1 12)
  have b14905 := hb (x 2 11)
  have b14906 := hb (x 3 10)
  have b14907 := hb (x 4 9)
  have b14908 := hb (x 5 8)
  have b14909 := hb (x 6 7)
  have b14910 := hb (x 7 6)
  have b14911 := hb (x 8 5)
  have b14912 := hb (x 9 4)
  have b14913 := hb (x 10 3)
  have b14914 := hb (x 11 2)
  have b14915 := hb (x 12 1)
  linarith only [r14901, b14902, b14903, b14904, b14905, b14906, b14907, b14908, b14909, b14910, b14911, b14912, b14913, b14914, b14915, d14821, d14792, d14813, d14837, d14853, d14869, d14897, d14256, d14280, g36, d14184, g29, g23, g12]

theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000100_p2 (x : ℤ → Fin 16 → Bool)
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
    (h14164 : x 1 3 = false)
    (h14170 : x (-1) 4 = false)
    (h14336 : x 1 6 = false)
    (h14338 : x (-1) 7 = false)
    (h14340 : x 1 8 = false)
    (h14342 : x (-1) 9 = false)
    (h14479 : x (-2) 4 = false)
    (h14481 : x 2 5 = false)
    : False := cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000100_p2_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83 g84 g85 g86 g87 g88 g89 g90 g91 g92 g93 g94 h14164 h14170 h14336 h14338 h14340 h14342 h14479 h14481
