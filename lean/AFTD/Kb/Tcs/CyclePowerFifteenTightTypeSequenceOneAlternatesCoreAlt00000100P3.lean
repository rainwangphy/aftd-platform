import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000100_p3

Topic: combinatorics   Node: e298dca016b0

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

Sub-branch of the window refutation cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000100 (one subtree of its case split, cut out so each piece fits the build limit): under the same layer-free tight-cover constraints for k = 15, its fixed bits and the case bits of this subtree, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000100_p3_aux (x : ℤ → Fin 16 → Bool)
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
    (h14481 : x 2 5 = true)
    (h15114 : x (-2) 8 = false)
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
  have f14916 : (x 2 5).toNat = 1 := by rw [h14481]; rfl
  have d14917 : (x 7 8).toNat = 0 := by
    have r14918 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14919 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e14920 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e14921 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e14922 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e14923 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e14924 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b14925 := hb (x 0 7)
    have b14926 := hb (x 1 6)
    have b14927 := hb (x 2 5)
    have b14928 := hb (x 3 4)
    have b14929 := hb (x 4 11)
    have b14930 := hb (x 5 10)
    have b14931 := hb (x 6 9)
    have b14932 := hb (x 7 8)
    clear * - r14918 e14919 e14920 e14921 e14922 e14923 e14924 b14925 b14926 b14927 b14928 b14929 b14930 b14931 b14932 g34 f14916 f14337 g17
    omega
  have d14933 : (x 7 3 && x 7 8).toNat = 0 := by
    have r14934 := hand2 (x 7 3) (x 7 8)
    have b14935 := hb (x 7 8)
    have b14936 := hb (x 7 3 && x 7 8)
    clear * - r14934 b14935 b14936 d14917
    omega
  have d14937 : (x 7 4 && x 7 8).toNat = 0 := by
    have r14938 := hand2 (x 7 4) (x 7 8)
    have b14939 := hb (x 7 8)
    have b14940 := hb (x 7 4 && x 7 8)
    clear * - r14938 b14939 b14940 d14917
    omega
  have d14941 : (x 6 9).toNat = 0 := by
    have r14942 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14943 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e14944 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e14945 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e14946 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e14947 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e14948 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b14949 := hb (x 0 7)
    have b14950 := hb (x 1 6)
    have b14951 := hb (x 2 5)
    have b14952 := hb (x 3 4)
    have b14953 := hb (x 4 11)
    have b14954 := hb (x 5 10)
    have b14955 := hb (x 6 9)
    have b14956 := hb (x 7 8)
    clear * - r14942 e14943 e14944 e14945 e14946 e14947 e14948 b14949 b14950 b14951 b14952 b14953 b14954 b14955 b14956 d14917 g34 f14916 f14337 g17
    omega
  have d14957 : (x 6 4 && x 6 9).toNat = 0 := by
    have r14958 := hand2 (x 6 4) (x 6 9)
    have b14959 := hb (x 6 9)
    have b14960 := hb (x 6 4 && x 6 9)
    clear * - r14958 b14959 b14960 d14941
    omega
  have d14961 : (x 6 5 && x 6 9).toNat = 0 := by
    have r14962 := hand2 (x 6 5) (x 6 9)
    have b14963 := hb (x 6 9)
    have b14964 := hb (x 6 5 && x 6 9)
    clear * - r14962 b14963 b14964 d14941
    omega
  have d14965 : (x 5 10).toNat = 0 := by
    have r14966 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14967 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e14968 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e14969 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e14970 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e14971 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e14972 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b14973 := hb (x 0 7)
    have b14974 := hb (x 1 6)
    have b14975 := hb (x 2 5)
    have b14976 := hb (x 3 4)
    have b14977 := hb (x 4 11)
    have b14978 := hb (x 5 10)
    have b14979 := hb (x 6 9)
    have b14980 := hb (x 7 8)
    clear * - r14966 e14967 e14968 e14969 e14970 e14971 e14972 b14973 b14974 b14975 b14976 b14977 b14978 b14979 b14980 d14917 d14941 g34 f14916 f14337 g17
    omega
  have d14981 : (x 5 1 && x 5 10).toNat = 0 := by
    have r14982 := hand2 (x 5 1) (x 5 10)
    have b14983 := hb (x 5 10)
    have b14984 := hb (x 5 1 && x 5 10)
    clear * - r14982 b14983 b14984 d14965
    omega
  have d14985 : (x 5 5 && x 5 10).toNat = 0 := by
    have r14986 := hand2 (x 5 5) (x 5 10)
    have b14987 := hb (x 5 10)
    have b14988 := hb (x 5 5 && x 5 10)
    clear * - r14986 b14987 b14988 d14965
    omega
  have d14989 : (x 5 6 && x 5 10).toNat = 0 := by
    have r14990 := hand2 (x 5 6) (x 5 10)
    have b14991 := hb (x 5 10)
    have b14992 := hb (x 5 6 && x 5 10)
    clear * - r14990 b14991 b14992 d14965
    omega
  have d14993 : (x 4 11).toNat = 0 := by
    have r14994 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14995 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e14996 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e14997 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e14998 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e14999 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e15000 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b15001 := hb (x 0 7)
    have b15002 := hb (x 1 6)
    have b15003 := hb (x 2 5)
    have b15004 := hb (x 3 4)
    have b15005 := hb (x 4 11)
    have b15006 := hb (x 5 10)
    have b15007 := hb (x 6 9)
    have b15008 := hb (x 7 8)
    clear * - r14994 e14995 e14996 e14997 e14998 e14999 e15000 b15001 b15002 b15003 b15004 b15005 b15006 b15007 b15008 d14917 d14941 d14965 g34 f14916 f14337 g17
    omega
  have d15009 : (x 4 2 && x 4 11).toNat = 0 := by
    have r15010 := hand2 (x 4 2) (x 4 11)
    have b15011 := hb (x 4 11)
    have b15012 := hb (x 4 2 && x 4 11)
    clear * - r15010 b15011 b15012 d14993
    omega
  have d15013 : (x 2 4 && x 2 13).toNat = 1 := by
    have r15014 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15015 := hb (x 0 6)
    have b15016 := hb (x 6 9)
    have b15017 := hb (x 5 1 && x 5 10)
    have b15018 := hb (x 4 2 && x 4 11)
    have b15019 := hb (x 3 3 && x 3 12)
    have b15020 := hb (x 2 4 && x 2 13)
    have b15021 := hb (x 1 5 && x 1 14)
    clear * - r15014 b15015 b15016 b15017 b15018 b15019 b15020 b15021 d14941 d14981 d15009 g76 g77 g16
    omega
  have d15022 : (x 2 4).toNat = 1 := by
    have r15023 := hand1 (x 2 4) (x 2 13)
    have b15024 := hb (x 2 4)
    have b15025 := hb (x 2 4 && x 2 13)
    clear * - r15023 b15024 b15025 d15013
    omega
  have d15026 : (x 4 6 && x 4 11).toNat = 0 := by
    have r15027 := hand2 (x 4 6) (x 4 11)
    have b15028 := hb (x 4 11)
    have b15029 := hb (x 4 6 && x 4 11)
    clear * - r15027 b15028 b15029 d14993
    omega
  have d15030 : (x 4 7 && x 4 11).toNat = 0 := by
    have r15031 := hand2 (x 4 7) (x 4 11)
    have b15032 := hb (x 4 11)
    have b15033 := hb (x 4 7 && x 4 11)
    clear * - r15031 b15032 b15033 d14993
    omega
  have d15034 : (x 6 8).toNat = 0 := by
    have r15035 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15036 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e15037 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e15038 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e15039 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e15040 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e15041 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b15042 := hb (x (-1) 7)
    have b15043 := hb (x 0 6)
    have b15044 := hb (x 1 5)
    have b15045 := hb (x 2 4)
    have b15046 := hb (x 3 11)
    have b15047 := hb (x 4 10)
    have b15048 := hb (x 5 9)
    have b15049 := hb (x 6 8)
    clear * - r15035 e15036 e15037 e15038 e15039 e15040 e15041 b15042 b15043 b15044 b15045 b15046 b15047 b15048 b15049 d15022 g26 g16 f14339
    omega
  have d15050 : (x 6 4 && x 6 8).toNat = 0 := by
    have r15051 := hand2 (x 6 4) (x 6 8)
    have b15052 := hb (x 6 8)
    have b15053 := hb (x 6 4 && x 6 8)
    clear * - r15051 b15052 b15053 d15034
    omega
  have d15054 : (x 5 9).toNat = 0 := by
    have r15055 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15056 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e15057 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e15058 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e15059 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e15060 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e15061 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b15062 := hb (x (-1) 7)
    have b15063 := hb (x 0 6)
    have b15064 := hb (x 1 5)
    have b15065 := hb (x 2 4)
    have b15066 := hb (x 3 11)
    have b15067 := hb (x 4 10)
    have b15068 := hb (x 5 9)
    have b15069 := hb (x 6 8)
    clear * - r15055 e15056 e15057 e15058 e15059 e15060 e15061 b15062 b15063 b15064 b15065 b15066 b15067 b15068 b15069 d15034 d15022 g26 g16 f14339
    omega
  have d15070 : (x 5 5 && x 5 9).toNat = 0 := by
    have r15071 := hand2 (x 5 5) (x 5 9)
    have b15072 := hb (x 5 9)
    have b15073 := hb (x 5 5 && x 5 9)
    clear * - r15071 b15072 b15073 d15054
    omega
  have d15074 : (x 4 10).toNat = 0 := by
    have r15075 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15076 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e15077 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e15078 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e15079 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e15080 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e15081 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b15082 := hb (x (-1) 7)
    have b15083 := hb (x 0 6)
    have b15084 := hb (x 1 5)
    have b15085 := hb (x 2 4)
    have b15086 := hb (x 3 11)
    have b15087 := hb (x 4 10)
    have b15088 := hb (x 5 9)
    have b15089 := hb (x 6 8)
    clear * - r15075 e15076 e15077 e15078 e15079 e15080 e15081 b15082 b15083 b15084 b15085 b15086 b15087 b15088 b15089 d15034 d15054 d15022 g26 g16 f14339
    omega
  have d15090 : (x 4 6 && x 4 10).toNat = 0 := by
    have r15091 := hand2 (x 4 6) (x 4 10)
    have b15092 := hb (x 4 10)
    have b15093 := hb (x 4 6 && x 4 10)
    clear * - r15091 b15092 b15093 d15074
    omega
  have d15094 : (x 3 11).toNat = 0 := by
    have r15095 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15096 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e15097 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e15098 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e15099 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e15100 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e15101 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b15102 := hb (x (-1) 7)
    have b15103 := hb (x 0 6)
    have b15104 := hb (x 1 5)
    have b15105 := hb (x 2 4)
    have b15106 := hb (x 3 11)
    have b15107 := hb (x 4 10)
    have b15108 := hb (x 5 9)
    have b15109 := hb (x 6 8)
    clear * - r15095 e15096 e15097 e15098 e15099 e15100 e15101 b15102 b15103 b15104 b15105 b15106 b15107 b15108 b15109 d15034 d15054 d15074 d15022 g26 g16 f14339
    omega
  have d15110 : (x 3 7 && x 3 11).toNat = 0 := by
    have r15111 := hand2 (x 3 7) (x 3 11)
    have b15112 := hb (x 3 11)
    have b15113 := hb (x 3 7 && x 3 11)
    clear * - r15111 b15112 b15113 d15094
    omega
  have f15115 : (x (-2) 8).toNat = 0 := by rw [h15114]; rfl
  cases h15116 : x 2 8
  · have f15117 : (x 2 8).toNat = 0 := by rw [h15116]; rfl
    have d15118 : (x 2 8 && x 2 13).toNat = 0 := by
      have r15119 := hand1 (x 2 8) (x 2 13)
      have b15120 := hb (x 2 8)
      have b15121 := hb (x 2 8 && x 2 13)
      clear * - r15119 b15120 b15121 f15117
      omega
    have d15122 : (x 2 8 && x 2 12).toNat = 0 := by
      have r15123 := hand1 (x 2 8) (x 2 12)
      have b15124 := hb (x 2 8)
      have b15125 := hb (x 2 8 && x 2 12)
      clear * - r15123 b15124 b15125 f15117
      omega
    have r15126 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r15127 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15128 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e15129 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e15130 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e15131 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e15132 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e15133 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have r15134 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15135 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
    have e15136 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
    have e15137 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
    have e15138 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
    have e15139 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
    have e15140 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
    have r15141 : 1 ≤ (x 7 4).toNat + (x 6 1 && x 6 5).toNat + (x 5 2 && x 5 6).toNat + (x 4 3 && x 4 7).toNat + (x 3 4 && x 3 8).toNat + (x 2 5 && x 2 9).toNat + (x 1 6 && x 1 10).toNat + (x 0 7 && x 0 11).toNat + (x (-1) 8 && x (-1) 12).toNat + (x (-2) 9 && x (-2) 13).toNat + (x (-3) 10 && x (-3) 14).toNat + (x (-4) 11).toNat := by have q := hcov4 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15142 : (x 6 1 && x 6 5).toNat = (x 6 5).toNat := handr _ _ (fun h => hp13 6 (hp5 6 (h)))
    have e15143 : (x (-3) 10 && x (-3) 14).toNat = (x (-3) 10).toNat := handl _ _ (fun h => hp2 (-3) (hp10 (-3) (h)))
    have r15144 : 1 ≤ (x 10 4).toNat + (x 9 1 && x 9 5).toNat + (x 8 2 && x 8 6).toNat + (x 7 3 && x 7 7).toNat + (x 6 4 && x 6 8).toNat + (x 5 5 && x 5 9).toNat + (x 4 6 && x 4 10).toNat + (x 3 7 && x 3 11).toNat + (x 2 8 && x 2 12).toNat + (x 1 9 && x 1 13).toNat + (x 0 10 && x 0 14).toNat + (x (-1) 11).toNat := by have q := hcov4 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15145 : (x 9 1 && x 9 5).toNat = (x 9 5).toNat := handr _ _ (fun h => hp13 9 (hp5 9 (h)))
    have e15146 : (x 0 10 && x 0 14).toNat = (x 0 10).toNat := handl _ _ (fun h => hp2 0 (hp10 0 (h)))
    have r15147 : 1 ≤ (x 11 4).toNat + (x 10 1 && x 10 5).toNat + (x 9 2 && x 9 6).toNat + (x 8 3 && x 8 7).toNat + (x 7 4 && x 7 8).toNat + (x 6 5 && x 6 9).toNat + (x 5 6 && x 5 10).toNat + (x 4 7 && x 4 11).toNat + (x 3 8 && x 3 12).toNat + (x 2 9 && x 2 13).toNat + (x 1 10 && x 1 14).toNat + (x 0 11).toNat := by have q := hcov4 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15148 : (x 10 1 && x 10 5).toNat = (x 10 5).toNat := handr _ _ (fun h => hp13 10 (hp5 10 (h)))
    have e15149 : (x 1 10 && x 1 14).toNat = (x 1 10).toNat := handl _ _ (fun h => hp2 1 (hp10 1 (h)))
    have r15150 : 1 ≤ (x 10 5).toNat + (x 9 1 && x 9 6).toNat + (x 8 2 && x 8 7).toNat + (x 7 3 && x 7 8).toNat + (x 6 4 && x 6 9).toNat + (x 5 5 && x 5 10).toNat + (x 4 6 && x 4 11).toNat + (x 3 7 && x 3 12).toNat + (x 2 8 && x 2 13).toNat + (x 1 9 && x 1 14).toNat + (x 0 10).toNat := by have q := hcov5 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r15151 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r15152 : (x 10 5).toNat ≤ (x 10 13).toNat := himp _ _ (hp5 10)
    have r15153 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
    have r15154 := hand2 (x 5 2) (x 5 6)
    have r15155 := hand2 (x 4 3) (x 4 7)
    have r15156 := hand2 (x 2 5) (x 2 9)
    have r15157 := hand2 (x 8 2) (x 8 6)
    have r15158 := hand2 (x 7 3) (x 7 7)
    have r15159 := hand1 (x 9 2) (x 9 6)
    have r15160 := hand1 (x 8 3) (x 8 7)
    have r15161 := hand1 (x 2 9) (x 2 13)
    have r15162 := hand2 (x 9 1) (x 9 6)
    have r15163 := hand2 (x 8 2) (x 8 7)
    have r15164 := hand1 (x 10 1) (x 10 12)
    have r15165 := hand1 (x 9 2) (x 9 13)
    have r15166 := hand1 (x 8 3) (x 8 14)
    linarith only [r15126, r15127, e15128, e15129, e15130, e15131, e15132, e15133, r15134, e15135, e15136, e15137, e15138, e15139, e15140, r15141, e15142, e15143, r15144, e15145, e15146, r15147, e15148, e15149, r15150, r15151, r15152, r15153, r15154, r15155, r15156, r15157, r15158, r15159, r15160, r15161, r15162, r15163, r15164, r15165, r15166, g0, g1, d14406, g7, d14025, g10, g20, g21, g28, g45, g46, g47, d14140, g48, d15050, d15070, d15090, d15110, d15122, g49, d14937, d14961, d14989, d15030, g50, d14933, d14957, d14985, d15026, g54, d15118, g55]
  · have f15238 : (x 2 8).toNat = 1 := by rw [h15116]; rfl
    have d15239 : (x (-3) 5).toNat = 0 := by
      have r15240 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15241 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e15242 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e15243 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e15244 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e15245 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e15246 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b15247 := hb (x (-5) 7)
      have b15248 := hb (x (-4) 6)
      have b15249 := hb (x (-3) 5)
      have b15250 := hb (x (-2) 4)
      have b15251 := hb (x (-1) 11)
      have b15252 := hb (x 0 10)
      have b15253 := hb (x 1 9)
      have b15254 := hb (x 2 8)
      clear * - r15240 e15241 e15242 e15243 e15244 e15245 e15246 b15247 b15248 b15249 b15250 b15251 b15252 b15253 b15254 f15238 g27 g20 d14025 f14480 d14369
      omega
    have d15255 : (x (-3) 5 && x (-3) 14).toNat = 0 := by
      have r15256 := hand1 (x (-3) 5) (x (-3) 14)
      have b15257 := hb (x (-3) 5)
      have b15258 := hb (x (-3) 5 && x (-3) 14)
      clear * - r15256 b15257 b15258 d15239
      omega
    have d15259 : (x 2 9).toNat = 1 := by
      have r15260 : 1 ≤ (x 2 9).toNat + (x 1 1 && x 1 10).toNat + (x 0 2 && x 0 11).toNat + (x (-1) 3 && x (-1) 12).toNat + (x (-2) 4 && x (-2) 13).toNat + (x (-3) 5 && x (-3) 14).toNat + (x (-4) 6).toNat := by have q := hcov9 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b15261 := hb (x (-4) 6)
      have b15262 := hb (x 2 9)
      have b15263 := hb (x 1 1 && x 1 10)
      have b15264 := hb (x 0 2 && x 0 11)
      have b15265 := hb (x (-1) 3 && x (-1) 12)
      have b15266 := hb (x (-2) 4 && x (-2) 13)
      have b15267 := hb (x (-3) 5 && x (-3) 14)
      clear * - r15260 b15261 b15262 b15263 b15264 b15265 b15266 b15267 g73 g74 d14021 g75 d15255 d14369
      omega
    have d15268 : (x 3 8).toNat = 0 := by
      have r15269 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15270 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
      have e15271 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
      have e15272 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
      have e15273 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
      have e15274 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
      have e15275 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
      have b15276 := hb (x (-4) 7)
      have b15277 := hb (x (-3) 6)
      have b15278 := hb (x (-2) 5)
      have b15279 := hb (x (-1) 4)
      have b15280 := hb (x 0 11)
      have b15281 := hb (x 1 10)
      have b15282 := hb (x 2 9)
      have b15283 := hb (x 3 8)
      clear * - r15269 e15270 e15271 e15272 e15273 e15274 e15275 b15276 b15277 b15278 b15279 b15280 b15281 b15282 b15283 d15259 g28 g21 f14171 g3
      omega
    have d15284 : (x 2 10).toNat = 1 := by
      have r15285 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b15286 := hb (x (-3) 5)
      have b15287 := hb (x 2 10)
      have b15288 := hb (x 1 1 && x 1 11)
      have b15289 := hb (x 0 2 && x 0 12)
      have b15290 := hb (x (-1) 3 && x (-1) 13)
      have b15291 := hb (x (-2) 4 && x (-2) 14)
      clear * - r15285 b15286 b15287 b15288 b15289 b15290 b15291 g84 g85 d14017 d14430 d15239
      omega
    have d15292 : (x 4 8).toNat = 0 := by
      have r15293 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15294 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
      have e15295 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
      have e15296 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
      have e15297 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
      have e15298 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
      have e15299 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
      have b15300 := hb (x (-3) 7)
      have b15301 := hb (x (-2) 6)
      have b15302 := hb (x (-1) 5)
      have b15303 := hb (x 0 4)
      have b15304 := hb (x 1 11)
      have b15305 := hb (x 2 10)
      have b15306 := hb (x 3 9)
      have b15307 := hb (x 4 8)
      clear * - r15293 e15294 e15295 e15296 e15297 e15298 e15299 b15300 b15301 b15302 b15303 b15304 b15305 b15306 b15307 d15284 d14166 g14 g9 d14434
      omega
    have d15308 : (x 3 9).toNat = 0 := by
      have r15309 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15310 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
      have e15311 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
      have e15312 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
      have e15313 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
      have e15314 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
      have e15315 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
      have b15316 := hb (x (-3) 7)
      have b15317 := hb (x (-2) 6)
      have b15318 := hb (x (-1) 5)
      have b15319 := hb (x 0 4)
      have b15320 := hb (x 1 11)
      have b15321 := hb (x 2 10)
      have b15322 := hb (x 3 9)
      have b15323 := hb (x 4 8)
      clear * - r15309 e15310 e15311 e15312 e15313 e15314 e15315 b15316 b15317 b15318 b15319 b15320 b15321 b15322 b15323 d15292 d15284 d14166 g14 g9 d14434
      omega
    have d15324 : (x 10 1).toNat = 0 := by
      have r15325 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b15326 := hb (x (-3) 14)
      have b15327 := hb (x (-2) 13)
      have b15328 := hb (x (-1) 12)
      have b15329 := hb (x 0 11)
      have b15330 := hb (x 1 10)
      have b15331 := hb (x 2 9)
      have b15332 := hb (x 3 8)
      have b15333 := hb (x 4 7)
      have b15334 := hb (x 5 6)
      have b15335 := hb (x 6 5)
      have b15336 := hb (x 7 4)
      have b15337 := hb (x 8 3)
      have b15338 := hb (x 9 2)
      have b15339 := hb (x 10 1)
      clear * - r15325 b15326 b15327 b15328 b15329 b15330 b15331 b15332 b15333 b15334 b15335 b15336 b15337 b15338 b15339 d15268 d15259 g28 g21 g10 g7 d14406
      omega
    have d15340 : (x 10 1 && x 10 14).toNat = 0 := by
      have r15341 := hand1 (x 10 1) (x 10 14)
      have b15342 := hb (x 10 1)
      have b15343 := hb (x 10 1 && x 10 14)
      clear * - r15341 b15342 b15343 d15324
      omega
    have d15344 : (x 10 13).toNat = 0 := by
      have r15345 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
      have b15346 := hb (x 10 1)
      have b15347 := hb (x 10 13)
      clear * - r15345 b15346 b15347 d15324
      omega
    have d15348 : (x 10 5).toNat = 0 := by
      have r15349 : (x 10 5).toNat ≤ (x 10 13).toNat := himp _ _ (hp5 10)
      have b15350 := hb (x 10 5)
      have b15351 := hb (x 10 13)
      clear * - r15349 b15350 b15351 d15344
      omega
    have d15352 : (x 9 2).toNat = 0 := by
      have r15353 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b15354 := hb (x (-3) 14)
      have b15355 := hb (x (-2) 13)
      have b15356 := hb (x (-1) 12)
      have b15357 := hb (x 0 11)
      have b15358 := hb (x 1 10)
      have b15359 := hb (x 2 9)
      have b15360 := hb (x 3 8)
      have b15361 := hb (x 4 7)
      have b15362 := hb (x 5 6)
      have b15363 := hb (x 6 5)
      have b15364 := hb (x 7 4)
      have b15365 := hb (x 8 3)
      have b15366 := hb (x 9 2)
      have b15367 := hb (x 10 1)
      clear * - r15353 b15354 b15355 b15356 b15357 b15358 b15359 b15360 b15361 b15362 b15363 b15364 b15365 b15366 b15367 d15324 d15268 d15259 g28 g21 g10 g7 d14406
      omega
    have d15368 : (x 11 13).toNat = 1 := by
      have r15369 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b15370 := hb (x 9 2)
      have b15371 := hb (x 11 13)
      have b15372 := hb (x 10 1 && x 10 14)
      clear * - r15369 b15370 b15371 b15372 d15340 d15352
      omega
    have d15373 : (x 11 1).toNat = 1 := by
      have r15374 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
      have b15375 := hb (x 11 1)
      have b15376 := hb (x 11 13)
      clear * - r15374 b15375 b15376 d15368
      omega
    have d15377 : (x 12 14).toNat = 0 := by
      have r15378 : (x 12 14).toNat + (x 11 1).toNat = 1 := by have q := hd14 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b15379 := hb (x 11 1)
      have b15380 := hb (x 12 14)
      clear * - r15378 b15379 b15380 d15373
      omega
    have d15381 : (x 12 1 && x 12 14).toNat = 0 := by
      have r15382 := hand2 (x 12 1) (x 12 14)
      have b15383 := hb (x 12 14)
      have b15384 := hb (x 12 1 && x 12 14)
      clear * - r15382 b15383 b15384 d15377
      omega
    have d15385 : (x 12 5 && x 12 14).toNat = 0 := by
      have r15386 := hand2 (x 12 5) (x 12 14)
      have b15387 := hb (x 12 14)
      have b15388 := hb (x 12 5 && x 12 14)
      clear * - r15386 b15387 b15388 d15377
      omega
    have d15389 : (x 12 6).toNat = 0 := by
      have r15390 : (x 12 6).toNat ≤ (x 12 14).toNat := himp _ _ (hp6 12)
      have b15391 := hb (x 12 6)
      have b15392 := hb (x 12 14)
      clear * - r15390 b15391 b15392 d15377
      omega
    have d15393 : (x 12 1 && x 12 6).toNat = 0 := by
      have r15394 := hand2 (x 12 1) (x 12 6)
      have b15395 := hb (x 12 6)
      have b15396 := hb (x 12 1 && x 12 6)
      clear * - r15394 b15395 b15396 d15389
      omega
    have d15397 : (x 12 2).toNat = 0 := by
      have r15398 : (x 12 2).toNat ≤ (x 12 14).toNat := himp _ _ (hp2 12)
      have b15399 := hb (x 12 2)
      have b15400 := hb (x 12 14)
      clear * - r15398 b15399 b15400 d15377
      omega
    have d15401 : (x 12 10).toNat = 0 := by
      have r15402 : (x 12 10).toNat ≤ (x 12 2).toNat := himp _ _ (hp10 12)
      have b15403 := hb (x 12 2)
      have b15404 := hb (x 12 10)
      clear * - r15402 b15403 b15404 d15397
      omega
    have d15405 : (x 10 2).toNat = 0 := by
      have r15406 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b15407 := hb (x (-2) 14)
      have b15408 := hb (x (-1) 13)
      have b15409 := hb (x 0 12)
      have b15410 := hb (x 1 11)
      have b15411 := hb (x 2 10)
      have b15412 := hb (x 3 9)
      have b15413 := hb (x 4 8)
      have b15414 := hb (x 5 7)
      have b15415 := hb (x 6 6)
      have b15416 := hb (x 7 5)
      have b15417 := hb (x 8 4)
      have b15418 := hb (x 9 3)
      have b15419 := hb (x 10 2)
      have b15420 := hb (x 11 1)
      clear * - r15406 b15407 b15408 b15409 b15410 b15411 b15412 b15413 b15414 b15415 b15416 b15417 b15418 b15419 b15420 d15373 d15292 d15308 d15284 d14166 g22 g11 d14426
      omega
    have d15421 : (x 10 2 && x 10 12).toNat = 0 := by
      have r15422 := hand1 (x 10 2) (x 10 12)
      have b15423 := hb (x 10 2)
      have b15424 := hb (x 10 2 && x 10 12)
      clear * - r15422 b15423 b15424 d15405
      omega
    have d15425 : (x 9 3).toNat = 0 := by
      have r15426 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b15427 := hb (x (-2) 14)
      have b15428 := hb (x (-1) 13)
      have b15429 := hb (x 0 12)
      have b15430 := hb (x 1 11)
      have b15431 := hb (x 2 10)
      have b15432 := hb (x 3 9)
      have b15433 := hb (x 4 8)
      have b15434 := hb (x 5 7)
      have b15435 := hb (x 6 6)
      have b15436 := hb (x 7 5)
      have b15437 := hb (x 8 4)
      have b15438 := hb (x 9 3)
      have b15439 := hb (x 10 2)
      have b15440 := hb (x 11 1)
      clear * - r15426 b15427 b15428 b15429 b15430 b15431 b15432 b15433 b15434 b15435 b15436 b15437 b15438 b15439 b15440 d15373 d15405 d15292 d15308 d15284 d14166 g22 g11 d14426
      omega
    have d15441 : (x 9 3 && x 9 13).toNat = 0 := by
      have r15442 := hand1 (x 9 3) (x 9 13)
      have b15443 := hb (x 9 3)
      have b15444 := hb (x 9 3 && x 9 13)
      clear * - r15442 b15443 b15444 d15425
      omega
    have d15445 : (x 8 4).toNat = 0 := by
      have r15446 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b15447 := hb (x (-2) 14)
      have b15448 := hb (x (-1) 13)
      have b15449 := hb (x 0 12)
      have b15450 := hb (x 1 11)
      have b15451 := hb (x 2 10)
      have b15452 := hb (x 3 9)
      have b15453 := hb (x 4 8)
      have b15454 := hb (x 5 7)
      have b15455 := hb (x 6 6)
      have b15456 := hb (x 7 5)
      have b15457 := hb (x 8 4)
      have b15458 := hb (x 9 3)
      have b15459 := hb (x 10 2)
      have b15460 := hb (x 11 1)
      clear * - r15446 b15447 b15448 b15449 b15450 b15451 b15452 b15453 b15454 b15455 b15456 b15457 b15458 b15459 b15460 d15373 d15405 d15425 d15292 d15308 d15284 d14166 g22 g11 d14426
      omega
    have d15461 : (x 8 4 && x 8 14).toNat = 0 := by
      have r15462 := hand1 (x 8 4) (x 8 14)
      have b15463 := hb (x 8 4)
      have b15464 := hb (x 8 4 && x 8 14)
      clear * - r15462 b15463 b15464 d15445
      omega
    have d15465 : (x 7 5).toNat = 0 := by
      have r15466 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b15467 := hb (x (-2) 14)
      have b15468 := hb (x (-1) 13)
      have b15469 := hb (x 0 12)
      have b15470 := hb (x 1 11)
      have b15471 := hb (x 2 10)
      have b15472 := hb (x 3 9)
      have b15473 := hb (x 4 8)
      have b15474 := hb (x 5 7)
      have b15475 := hb (x 6 6)
      have b15476 := hb (x 7 5)
      have b15477 := hb (x 8 4)
      have b15478 := hb (x 9 3)
      have b15479 := hb (x 10 2)
      have b15480 := hb (x 11 1)
      clear * - r15466 b15467 b15468 b15469 b15470 b15471 b15472 b15473 b15474 b15475 b15476 b15477 b15478 b15479 b15480 d15373 d15405 d15425 d15445 d15292 d15308 d15284 d14166 g22 g11 d14426
      omega
    have d15481 : (x 11 1 && x 11 11).toNat = 1 := by
      have r15482 : 1 ≤ (x 12 10).toNat + (x 11 1 && x 11 11).toNat + (x 10 2 && x 10 12).toNat + (x 9 3 && x 9 13).toNat + (x 8 4 && x 8 14).toNat + (x 7 5).toNat := by have q := hcov10 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b15483 := hb (x 7 5)
      have b15484 := hb (x 12 10)
      have b15485 := hb (x 11 1 && x 11 11)
      have b15486 := hb (x 10 2 && x 10 12)
      have b15487 := hb (x 9 3 && x 9 13)
      have b15488 := hb (x 8 4 && x 8 14)
      clear * - r15482 b15483 b15484 b15485 b15486 b15487 b15488 d15401 d15421 d15441 d15461 d15465
      omega
    have d15489 : (x 11 11).toNat = 1 := by
      have r15490 := hand2 (x 11 1) (x 11 11)
      have b15491 := hb (x 11 11)
      have b15492 := hb (x 11 1 && x 11 11)
      clear * - r15490 b15491 b15492 d15481
      omega
    have d15493 : (x 11 3).toNat = 1 := by
      have r15494 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
      have b15495 := hb (x 11 3)
      have b15496 := hb (x 11 11)
      clear * - r15494 b15495 b15496 d15489
      omega
    have d15497 : (x 14 12).toNat = 0 := by
      have r15498 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15499 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
      have e15500 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
      have b15501 := hb (x 11 3)
      have b15502 := hb (x 12 2)
      have b15503 := hb (x 13 13)
      have b15504 := hb (x 14 12)
      clear * - r15498 e15499 e15500 b15501 b15502 b15503 b15504 d15397 d15493
      omega
    have d15505 : (x 14 3 && x 14 12).toNat = 0 := by
      have r15506 := hand2 (x 14 3) (x 14 12)
      have b15507 := hb (x 14 12)
      have b15508 := hb (x 14 3 && x 14 12)
      clear * - r15506 b15507 b15508 d15497
      omega
    have d15509 : (x 14 12 && x 14 13).toNat = 0 := by
      have r15510 := hand1 (x 14 12) (x 14 13)
      have b15511 := hb (x 14 12)
      have b15512 := hb (x 14 12 && x 14 13)
      clear * - r15510 b15511 b15512 d15497
      omega
    have d15513 : (x 14 4).toNat = 0 := by
      have r15514 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
      have b15515 := hb (x 14 4)
      have b15516 := hb (x 14 12)
      clear * - r15514 b15515 b15516 d15497
      omega
    have d15517 : (x 14 4 && x 14 13).toNat = 0 := by
      have r15518 := hand1 (x 14 4) (x 14 13)
      have b15519 := hb (x 14 4)
      have b15520 := hb (x 14 4 && x 14 13)
      clear * - r15518 b15519 b15520 d15513
      omega
    have d15521 : (x 13 13).toNat = 0 := by
      have r15522 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15523 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
      have e15524 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
      have b15525 := hb (x 11 3)
      have b15526 := hb (x 12 2)
      have b15527 := hb (x 13 13)
      have b15528 := hb (x 14 12)
      clear * - r15522 e15523 e15524 b15525 b15526 b15527 b15528 d15497 d15397 d15493
      omega
    have d15529 : (x 13 4 && x 13 13).toNat = 0 := by
      have r15530 := hand2 (x 13 4) (x 13 13)
      have b15531 := hb (x 13 13)
      have b15532 := hb (x 13 4 && x 13 13)
      clear * - r15530 b15531 b15532 d15521
      omega
    have d15533 : (x 13 13 && x 13 14).toNat = 0 := by
      have r15534 := hand1 (x 13 13) (x 13 14)
      have b15535 := hb (x 13 13)
      have b15536 := hb (x 13 13 && x 13 14)
      clear * - r15534 b15535 b15536 d15521
      omega
    have d15537 : (x 13 5).toNat = 0 := by
      have r15538 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
      have b15539 := hb (x 13 5)
      have b15540 := hb (x 13 13)
      clear * - r15538 b15539 b15540 d15521
      omega
    have d15541 : (x 13 5 && x 13 14).toNat = 0 := by
      have r15542 := hand1 (x 13 5) (x 13 14)
      have b15543 := hb (x 13 5)
      have b15544 := hb (x 13 5 && x 13 14)
      clear * - r15542 b15543 b15544 d15537
      omega
    have d15545 : (x 11 2).toNat = 1 := by
      have r15546 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b15547 := hb (x 11 2)
      have b15548 := hb (x 13 13)
      have b15549 := hb (x 12 1 && x 12 14)
      clear * - r15546 b15547 b15548 b15549 d15521 d15381
      omega
    have d15550 : (x 13 12).toNat = 0 := by
      have r15551 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15552 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
      have e15553 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
      have b15554 := hb (x 10 3)
      have b15555 := hb (x 11 2)
      have b15556 := hb (x 12 13)
      have b15557 := hb (x 13 12)
      clear * - r15551 e15552 e15553 b15554 b15555 b15556 b15557 d15545
      omega
    have d15558 : (x 13 2 && x 13 12).toNat = 0 := by
      have r15559 := hand2 (x 13 2) (x 13 12)
      have b15560 := hb (x 13 12)
      have b15561 := hb (x 13 2 && x 13 12)
      clear * - r15559 b15560 b15561 d15550
      omega
    have d15562 : (x 13 4).toNat = 0 := by
      have r15563 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
      have b15564 := hb (x 13 4)
      have b15565 := hb (x 13 12)
      clear * - r15563 b15564 b15565 d15550
      omega
    have d15566 : (x 12 13).toNat = 0 := by
      have r15567 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15568 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
      have e15569 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
      have b15570 := hb (x 10 3)
      have b15571 := hb (x 11 2)
      have b15572 := hb (x 12 13)
      have b15573 := hb (x 13 12)
      clear * - r15567 e15568 e15569 b15570 b15571 b15572 b15573 d15550 d15545
      omega
    have d15574 : (x 12 3 && x 12 13).toNat = 0 := by
      have r15575 := hand2 (x 12 3) (x 12 13)
      have b15576 := hb (x 12 13)
      have b15577 := hb (x 12 3 && x 12 13)
      clear * - r15575 b15576 b15577 d15566
      omega
    have d15578 : (x 12 5).toNat = 0 := by
      have r15579 : (x 12 5).toNat ≤ (x 12 13).toNat := himp _ _ (hp5 12)
      have b15580 := hb (x 12 5)
      have b15581 := hb (x 12 13)
      clear * - r15579 b15580 b15581 d15566
      omega
    have d15582 : (x 10 3).toNat = 0 := by
      have r15583 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15584 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
      have e15585 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
      have b15586 := hb (x 10 3)
      have b15587 := hb (x 11 2)
      have b15588 := hb (x 12 13)
      have b15589 := hb (x 13 12)
      clear * - r15583 e15584 e15585 b15586 b15587 b15588 b15589 d15550 d15566 d15545
      omega
    have d15590 : (x 10 3 && x 10 8).toNat = 0 := by
      have r15591 := hand1 (x 10 3) (x 10 8)
      have b15592 := hb (x 10 3)
      have b15593 := hb (x 10 3 && x 10 8)
      clear * - r15591 b15592 b15593 d15582
      omega
    have d15594 : (x 12 1).toNat = 0 := by
      have r15595 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b15596 := hb (x (-1) 14)
      have b15597 := hb (x 0 13)
      have b15598 := hb (x 1 12)
      have b15599 := hb (x 2 11)
      have b15600 := hb (x 3 10)
      have b15601 := hb (x 4 9)
      have b15602 := hb (x 5 8)
      have b15603 := hb (x 6 7)
      have b15604 := hb (x 7 6)
      have b15605 := hb (x 8 5)
      have b15606 := hb (x 9 4)
      have b15607 := hb (x 10 3)
      have b15608 := hb (x 11 2)
      have b15609 := hb (x 12 1)
      clear * - r15595 b15596 b15597 b15598 b15599 b15600 b15601 b15602 b15603 b15604 b15605 b15606 b15607 b15608 b15609 d15545 d15582 d14256 d14280 g36 d14184 g29 g23 g12
      omega
    have d15610 : (x 13 14).toNat = 1 := by
      have r15611 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b15612 := hb (x 12 1)
      have b15613 := hb (x 13 14)
      clear * - r15611 b15612 b15613 d15594
      omega
    have d15614 : (x 9 4).toNat = 0 := by
      have r15615 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b15616 := hb (x (-1) 14)
      have b15617 := hb (x 0 13)
      have b15618 := hb (x 1 12)
      have b15619 := hb (x 2 11)
      have b15620 := hb (x 3 10)
      have b15621 := hb (x 4 9)
      have b15622 := hb (x 5 8)
      have b15623 := hb (x 6 7)
      have b15624 := hb (x 7 6)
      have b15625 := hb (x 8 5)
      have b15626 := hb (x 9 4)
      have b15627 := hb (x 10 3)
      have b15628 := hb (x 11 2)
      have b15629 := hb (x 12 1)
      clear * - r15615 b15616 b15617 b15618 b15619 b15620 b15621 b15622 b15623 b15624 b15625 b15626 b15627 b15628 b15629 d15594 d15545 d15582 d14256 d14280 g36 d14184 g29 g23 g12
      omega
    have d15630 : (x 9 4 && x 9 9).toNat = 0 := by
      have r15631 := hand1 (x 9 4) (x 9 9)
      have b15632 := hb (x 9 4)
      have b15633 := hb (x 9 4 && x 9 9)
      clear * - r15631 b15632 b15633 d15614
      omega
    have d15634 : (x 8 5).toNat = 0 := by
      have r15635 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b15636 := hb (x (-1) 14)
      have b15637 := hb (x 0 13)
      have b15638 := hb (x 1 12)
      have b15639 := hb (x 2 11)
      have b15640 := hb (x 3 10)
      have b15641 := hb (x 4 9)
      have b15642 := hb (x 5 8)
      have b15643 := hb (x 6 7)
      have b15644 := hb (x 7 6)
      have b15645 := hb (x 8 5)
      have b15646 := hb (x 9 4)
      have b15647 := hb (x 10 3)
      have b15648 := hb (x 11 2)
      have b15649 := hb (x 12 1)
      clear * - r15635 b15636 b15637 b15638 b15639 b15640 b15641 b15642 b15643 b15644 b15645 b15646 b15647 b15648 b15649 d15594 d15545 d15582 d15614 d14256 d14280 g36 d14184 g29 g23 g12
      omega
    have d15650 : (x 8 5 && x 8 10).toNat = 0 := by
      have r15651 := hand1 (x 8 5) (x 8 10)
      have b15652 := hb (x 8 5)
      have b15653 := hb (x 8 5 && x 8 10)
      clear * - r15651 b15652 b15653 d15634
      omega
    have d15654 : (x 7 6).toNat = 0 := by
      have r15655 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b15656 := hb (x (-1) 14)
      have b15657 := hb (x 0 13)
      have b15658 := hb (x 1 12)
      have b15659 := hb (x 2 11)
      have b15660 := hb (x 3 10)
      have b15661 := hb (x 4 9)
      have b15662 := hb (x 5 8)
      have b15663 := hb (x 6 7)
      have b15664 := hb (x 7 6)
      have b15665 := hb (x 8 5)
      have b15666 := hb (x 9 4)
      have b15667 := hb (x 10 3)
      have b15668 := hb (x 11 2)
      have b15669 := hb (x 12 1)
      clear * - r15655 b15656 b15657 b15658 b15659 b15660 b15661 b15662 b15663 b15664 b15665 b15666 b15667 b15668 b15669 d15594 d15545 d15582 d15614 d15634 d14256 d14280 g36 d14184 g29 g23 g12
      omega
    have d15670 : (x 7 6 && x 7 11).toNat = 0 := by
      have r15671 := hand1 (x 7 6) (x 7 11)
      have b15672 := hb (x 7 6)
      have b15673 := hb (x 7 6 && x 7 11)
      clear * - r15671 b15672 b15673 d15654
      omega
    have d15674 : (x 6 7).toNat = 0 := by
      have r15675 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b15676 := hb (x (-1) 14)
      have b15677 := hb (x 0 13)
      have b15678 := hb (x 1 12)
      have b15679 := hb (x 2 11)
      have b15680 := hb (x 3 10)
      have b15681 := hb (x 4 9)
      have b15682 := hb (x 5 8)
      have b15683 := hb (x 6 7)
      have b15684 := hb (x 7 6)
      have b15685 := hb (x 8 5)
      have b15686 := hb (x 9 4)
      have b15687 := hb (x 10 3)
      have b15688 := hb (x 11 2)
      have b15689 := hb (x 12 1)
      clear * - r15675 b15676 b15677 b15678 b15679 b15680 b15681 b15682 b15683 b15684 b15685 b15686 b15687 b15688 b15689 d15594 d15545 d15582 d15614 d15634 d15654 d14256 d14280 g36 d14184 g29 g23 g12
      omega
    have d15690 : (x 6 7 && x 6 12).toNat = 0 := by
      have r15691 := hand1 (x 6 7) (x 6 12)
      have b15692 := hb (x 6 7)
      have b15693 := hb (x 6 7 && x 6 12)
      clear * - r15691 b15692 b15693 d15674
      omega
    have d15694 : (x 11 2 && x 11 7).toNat = 1 := by
      have r15695 : 1 ≤ (x 13 5).toNat + (x 12 1 && x 12 6).toNat + (x 11 2 && x 11 7).toNat + (x 10 3 && x 10 8).toNat + (x 9 4 && x 9 9).toNat + (x 8 5 && x 8 10).toNat + (x 7 6 && x 7 11).toNat + (x 6 7 && x 6 12).toNat + (x 5 8 && x 5 13).toNat + (x 4 9 && x 4 14).toNat + (x 3 10).toNat := by have q := hcov5 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b15696 := hb (x 3 10)
      have b15697 := hb (x 13 5)
      have b15698 := hb (x 12 1 && x 12 6)
      have b15699 := hb (x 11 2 && x 11 7)
      have b15700 := hb (x 10 3 && x 10 8)
      have b15701 := hb (x 9 4 && x 9 9)
      have b15702 := hb (x 8 5 && x 8 10)
      have b15703 := hb (x 7 6 && x 7 11)
      have b15704 := hb (x 6 7 && x 6 12)
      have b15705 := hb (x 5 8 && x 5 13)
      have b15706 := hb (x 4 9 && x 4 14)
      clear * - r15695 b15696 b15697 b15698 b15699 b15700 b15701 b15702 b15703 b15704 b15705 b15706 d15537 d15393 d15590 d15630 d15650 d15670 d15690 d14276 d14300 g36
      omega
    have d15707 : (x 11 7).toNat = 1 := by
      have r15708 := hand2 (x 11 2) (x 11 7)
      have b15709 := hb (x 11 7)
      have b15710 := hb (x 11 2 && x 11 7)
      clear * - r15708 b15709 b15710 d15694
      omega
    have d15711 : (x 18 8).toNat = 0 := by
      have r15712 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15713 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
      have e15714 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
      have e15715 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
      have e15716 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
      have e15717 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
      have e15718 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
      have b15719 := hb (x 11 7)
      have b15720 := hb (x 12 6)
      have b15721 := hb (x 13 5)
      have b15722 := hb (x 14 4)
      have b15723 := hb (x 15 11)
      have b15724 := hb (x 16 10)
      have b15725 := hb (x 17 9)
      have b15726 := hb (x 18 8)
      clear * - r15712 e15713 e15714 e15715 e15716 e15717 e15718 b15719 b15720 b15721 b15722 b15723 b15724 b15725 b15726 d15513 d15537 d15389 d15707
      omega
    have d15727 : (x 18 8 && x 18 9).toNat = 0 := by
      have r15728 := hand1 (x 18 8) (x 18 9)
      have b15729 := hb (x 18 8)
      have b15730 := hb (x 18 8 && x 18 9)
      clear * - r15728 b15729 b15730 d15711
      omega
    have d15731 : (x 17 9).toNat = 0 := by
      have r15732 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15733 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
      have e15734 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
      have e15735 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
      have e15736 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
      have e15737 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
      have e15738 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
      have b15739 := hb (x 11 7)
      have b15740 := hb (x 12 6)
      have b15741 := hb (x 13 5)
      have b15742 := hb (x 14 4)
      have b15743 := hb (x 15 11)
      have b15744 := hb (x 16 10)
      have b15745 := hb (x 17 9)
      have b15746 := hb (x 18 8)
      clear * - r15732 e15733 e15734 e15735 e15736 e15737 e15738 b15739 b15740 b15741 b15742 b15743 b15744 b15745 b15746 d15711 d15513 d15537 d15389 d15707
      omega
    have d15747 : (x 17 9 && x 17 10).toNat = 0 := by
      have r15748 := hand1 (x 17 9) (x 17 10)
      have b15749 := hb (x 17 9)
      have b15750 := hb (x 17 9 && x 17 10)
      clear * - r15748 b15749 b15750 d15731
      omega
    have d15751 : (x 16 10).toNat = 0 := by
      have r15752 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15753 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
      have e15754 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
      have e15755 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
      have e15756 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
      have e15757 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
      have e15758 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
      have b15759 := hb (x 11 7)
      have b15760 := hb (x 12 6)
      have b15761 := hb (x 13 5)
      have b15762 := hb (x 14 4)
      have b15763 := hb (x 15 11)
      have b15764 := hb (x 16 10)
      have b15765 := hb (x 17 9)
      have b15766 := hb (x 18 8)
      clear * - r15752 e15753 e15754 e15755 e15756 e15757 e15758 b15759 b15760 b15761 b15762 b15763 b15764 b15765 b15766 d15711 d15731 d15513 d15537 d15389 d15707
      omega
    have d15767 : (x 16 1 && x 16 10).toNat = 0 := by
      have r15768 := hand2 (x 16 1) (x 16 10)
      have b15769 := hb (x 16 10)
      have b15770 := hb (x 16 1 && x 16 10)
      clear * - r15768 b15769 b15770 d15751
      omega
    have d15771 : (x 16 10 && x 16 11).toNat = 0 := by
      have r15772 := hand1 (x 16 10) (x 16 11)
      have b15773 := hb (x 16 10)
      have b15774 := hb (x 16 10 && x 16 11)
      clear * - r15772 b15773 b15774 d15751
      omega
    have d15775 : (x 15 11).toNat = 0 := by
      have r15776 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15777 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
      have e15778 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
      have e15779 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
      have e15780 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
      have e15781 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
      have e15782 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
      have b15783 := hb (x 11 7)
      have b15784 := hb (x 12 6)
      have b15785 := hb (x 13 5)
      have b15786 := hb (x 14 4)
      have b15787 := hb (x 15 11)
      have b15788 := hb (x 16 10)
      have b15789 := hb (x 17 9)
      have b15790 := hb (x 18 8)
      clear * - r15776 e15777 e15778 e15779 e15780 e15781 e15782 b15783 b15784 b15785 b15786 b15787 b15788 b15789 b15790 d15711 d15731 d15751 d15513 d15537 d15389 d15707
      omega
    have d15791 : (x 15 2 && x 15 11).toNat = 0 := by
      have r15792 := hand2 (x 15 2) (x 15 11)
      have b15793 := hb (x 15 11)
      have b15794 := hb (x 15 2 && x 15 11)
      clear * - r15792 b15793 b15794 d15775
      omega
    have d15795 : (x 11 6).toNat = 1 := by
      have r15796 : 1 ≤ (x 17 9).toNat + (x 16 1 && x 16 10).toNat + (x 15 2 && x 15 11).toNat + (x 14 3 && x 14 12).toNat + (x 13 4 && x 13 13).toNat + (x 12 5 && x 12 14).toNat + (x 11 6).toNat := by have q := hcov9 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b15797 := hb (x 11 6)
      have b15798 := hb (x 17 9)
      have b15799 := hb (x 16 1 && x 16 10)
      have b15800 := hb (x 15 2 && x 15 11)
      have b15801 := hb (x 14 3 && x 14 12)
      have b15802 := hb (x 13 4 && x 13 13)
      have b15803 := hb (x 12 5 && x 12 14)
      clear * - r15796 b15797 b15798 b15799 b15800 b15801 b15802 b15803 d15731 d15767 d15791 d15505 d15529 d15385
      omega
    have d15804 : (x 17 8).toNat = 0 := by
      have r15805 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15806 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
      have e15807 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
      have e15808 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
      have e15809 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
      have e15810 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
      have e15811 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
      have b15812 := hb (x 10 7)
      have b15813 := hb (x 11 6)
      have b15814 := hb (x 12 5)
      have b15815 := hb (x 13 4)
      have b15816 := hb (x 14 11)
      have b15817 := hb (x 15 10)
      have b15818 := hb (x 16 9)
      have b15819 := hb (x 17 8)
      clear * - r15805 e15806 e15807 e15808 e15809 e15810 e15811 b15812 b15813 b15814 b15815 b15816 b15817 b15818 b15819 d15562 d15578 d15795
      omega
    have d15820 : (x 16 9).toNat = 0 := by
      have r15821 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15822 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
      have e15823 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
      have e15824 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
      have e15825 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
      have e15826 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
      have e15827 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
      have b15828 := hb (x 10 7)
      have b15829 := hb (x 11 6)
      have b15830 := hb (x 12 5)
      have b15831 := hb (x 13 4)
      have b15832 := hb (x 14 11)
      have b15833 := hb (x 15 10)
      have b15834 := hb (x 16 9)
      have b15835 := hb (x 17 8)
      clear * - r15821 e15822 e15823 e15824 e15825 e15826 e15827 b15828 b15829 b15830 b15831 b15832 b15833 b15834 b15835 d15804 d15562 d15578 d15795
      omega
    have d15836 : (x 15 10).toNat = 0 := by
      have r15837 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15838 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
      have e15839 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
      have e15840 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
      have e15841 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
      have e15842 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
      have e15843 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
      have b15844 := hb (x 10 7)
      have b15845 := hb (x 11 6)
      have b15846 := hb (x 12 5)
      have b15847 := hb (x 13 4)
      have b15848 := hb (x 14 11)
      have b15849 := hb (x 15 10)
      have b15850 := hb (x 16 9)
      have b15851 := hb (x 17 8)
      clear * - r15837 e15838 e15839 e15840 e15841 e15842 e15843 b15844 b15845 b15846 b15847 b15848 b15849 b15850 b15851 d15804 d15820 d15562 d15578 d15795
      omega
    have d15852 : (x 14 11).toNat = 0 := by
      have r15853 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15854 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
      have e15855 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
      have e15856 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
      have e15857 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
      have e15858 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
      have e15859 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
      have b15860 := hb (x 10 7)
      have b15861 := hb (x 11 6)
      have b15862 := hb (x 12 5)
      have b15863 := hb (x 13 4)
      have b15864 := hb (x 14 11)
      have b15865 := hb (x 15 10)
      have b15866 := hb (x 16 9)
      have b15867 := hb (x 17 8)
      clear * - r15853 e15854 e15855 e15856 e15857 e15858 e15859 b15860 b15861 b15862 b15863 b15864 b15865 b15866 b15867 d15804 d15820 d15836 d15562 d15578 d15795
      omega
    have d15868 : (x 14 1 && x 14 11).toNat = 0 := by
      have r15869 := hand2 (x 14 1) (x 14 11)
      have b15870 := hb (x 14 11)
      have b15871 := hb (x 14 1 && x 14 11)
      clear * - r15869 b15870 b15871 d15852
      omega
    have d15872 : (x 11 4 && x 11 14).toNat = 1 := by
      have r15873 : 1 ≤ (x 15 10).toNat + (x 14 1 && x 14 11).toNat + (x 13 2 && x 13 12).toNat + (x 12 3 && x 12 13).toNat + (x 11 4 && x 11 14).toNat + (x 10 5).toNat := by have q := hcov10 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b15874 := hb (x 10 5)
      have b15875 := hb (x 15 10)
      have b15876 := hb (x 14 1 && x 14 11)
      have b15877 := hb (x 13 2 && x 13 12)
      have b15878 := hb (x 12 3 && x 12 13)
      have b15879 := hb (x 11 4 && x 11 14)
      clear * - r15873 b15874 b15875 b15876 b15877 b15878 b15879 d15836 d15868 d15558 d15574 d15348
      omega
    have d15880 : (x 11 4).toNat = 1 := by
      have r15881 := hand1 (x 11 4) (x 11 14)
      have b15882 := hb (x 11 4)
      have b15883 := hb (x 11 4 && x 11 14)
      clear * - r15881 b15882 b15883 d15872
      omega
    have d15884 : (x 15 8).toNat = 0 := by
      have r15885 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15886 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e15887 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e15888 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e15889 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e15890 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e15891 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have b15892 := hb (x 8 7)
      have b15893 := hb (x 9 6)
      have b15894 := hb (x 10 5)
      have b15895 := hb (x 11 4)
      have b15896 := hb (x 12 11)
      have b15897 := hb (x 13 10)
      have b15898 := hb (x 14 9)
      have b15899 := hb (x 15 8)
      clear * - r15885 e15886 e15887 e15888 e15889 e15890 e15891 b15892 b15893 b15894 b15895 b15896 b15897 b15898 b15899 d15880 d15348
      omega
    have d15900 : (x 14 9).toNat = 0 := by
      have r15901 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15902 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e15903 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e15904 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e15905 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e15906 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e15907 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have b15908 := hb (x 8 7)
      have b15909 := hb (x 9 6)
      have b15910 := hb (x 10 5)
      have b15911 := hb (x 11 4)
      have b15912 := hb (x 12 11)
      have b15913 := hb (x 13 10)
      have b15914 := hb (x 14 9)
      have b15915 := hb (x 15 8)
      clear * - r15901 e15902 e15903 e15904 e15905 e15906 e15907 b15908 b15909 b15910 b15911 b15912 b15913 b15914 b15915 d15884 d15880 d15348
      omega
    have d15916 : (x 13 10).toNat = 0 := by
      have r15917 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15918 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e15919 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e15920 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e15921 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e15922 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e15923 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have b15924 := hb (x 8 7)
      have b15925 := hb (x 9 6)
      have b15926 := hb (x 10 5)
      have b15927 := hb (x 11 4)
      have b15928 := hb (x 12 11)
      have b15929 := hb (x 13 10)
      have b15930 := hb (x 14 9)
      have b15931 := hb (x 15 8)
      clear * - r15917 e15918 e15919 e15920 e15921 e15922 e15923 b15924 b15925 b15926 b15927 b15928 b15929 b15930 b15931 d15884 d15900 d15880 d15348
      omega
    have d15932 : (x 12 11).toNat = 0 := by
      have r15933 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15934 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e15935 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e15936 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e15937 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e15938 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e15939 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have b15940 := hb (x 8 7)
      have b15941 := hb (x 9 6)
      have b15942 := hb (x 10 5)
      have b15943 := hb (x 11 4)
      have b15944 := hb (x 12 11)
      have b15945 := hb (x 13 10)
      have b15946 := hb (x 14 9)
      have b15947 := hb (x 15 8)
      clear * - r15933 e15934 e15935 e15936 e15937 e15938 e15939 b15940 b15941 b15942 b15943 b15944 b15945 b15946 b15947 d15884 d15900 d15916 d15880 d15348
      omega
    have d15948 : (x 9 6).toNat = 0 := by
      have r15949 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15950 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e15951 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e15952 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e15953 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e15954 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e15955 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have b15956 := hb (x 8 7)
      have b15957 := hb (x 9 6)
      have b15958 := hb (x 10 5)
      have b15959 := hb (x 11 4)
      have b15960 := hb (x 12 11)
      have b15961 := hb (x 13 10)
      have b15962 := hb (x 14 9)
      have b15963 := hb (x 15 8)
      clear * - r15949 e15950 e15951 e15952 e15953 e15954 e15955 b15956 b15957 b15958 b15959 b15960 b15961 b15962 b15963 d15884 d15900 d15916 d15932 d15880 d15348
      omega
    have d15964 : (x 8 7).toNat = 0 := by
      have r15965 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15966 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e15967 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e15968 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e15969 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e15970 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e15971 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have b15972 := hb (x 8 7)
      have b15973 := hb (x 9 6)
      have b15974 := hb (x 10 5)
      have b15975 := hb (x 11 4)
      have b15976 := hb (x 12 11)
      have b15977 := hb (x 13 10)
      have b15978 := hb (x 14 9)
      have b15979 := hb (x 15 8)
      clear * - r15965 e15966 e15967 e15968 e15969 e15970 e15971 b15972 b15973 b15974 b15975 b15976 b15977 b15978 b15979 d15884 d15900 d15916 d15932 d15880 d15348 d15948
      omega
    have d15980 : (x 14 1).toNat = 0 := by
      have r15981 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b15982 := hb (x 1 14)
      have b15983 := hb (x 2 13)
      have b15984 := hb (x 3 12)
      have b15985 := hb (x 4 11)
      have b15986 := hb (x 5 10)
      have b15987 := hb (x 6 9)
      have b15988 := hb (x 7 8)
      have b15989 := hb (x 8 7)
      have b15990 := hb (x 9 6)
      have b15991 := hb (x 10 5)
      have b15992 := hb (x 11 4)
      have b15993 := hb (x 12 3)
      have b15994 := hb (x 13 2)
      have b15995 := hb (x 14 1)
      clear * - r15981 b15982 b15983 b15984 b15985 b15986 b15987 b15988 b15989 b15990 b15991 b15992 b15993 b15994 b15995 d15880 d15348 d15948 d15964 d14917 d14941 d14965 d14993 g37 g32 g30
      omega
    have d15996 : (x 14 1 && x 14 14).toNat = 0 := by
      have r15997 := hand1 (x 14 1) (x 14 14)
      have b15998 := hb (x 14 1)
      have b15999 := hb (x 14 1 && x 14 14)
      clear * - r15997 b15998 b15999 d15980
      omega
    have d16000 : (x 14 13).toNat = 0 := by
      have r16001 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
      have b16002 := hb (x 14 1)
      have b16003 := hb (x 14 13)
      clear * - r16001 b16002 b16003 d15980
      omega
    have d16004 : (x 13 2).toNat = 0 := by
      have r16005 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16006 := hb (x 1 14)
      have b16007 := hb (x 2 13)
      have b16008 := hb (x 3 12)
      have b16009 := hb (x 4 11)
      have b16010 := hb (x 5 10)
      have b16011 := hb (x 6 9)
      have b16012 := hb (x 7 8)
      have b16013 := hb (x 8 7)
      have b16014 := hb (x 9 6)
      have b16015 := hb (x 10 5)
      have b16016 := hb (x 11 4)
      have b16017 := hb (x 12 3)
      have b16018 := hb (x 13 2)
      have b16019 := hb (x 14 1)
      clear * - r16005 b16006 b16007 b16008 b16009 b16010 b16011 b16012 b16013 b16014 b16015 b16016 b16017 b16018 b16019 d15980 d15880 d15348 d15948 d15964 d14917 d14941 d14965 d14993 g37 g32 g30
      omega
    have d16020 : (x 15 13).toNat = 1 := by
      have r16021 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16022 := hb (x 13 2)
      have b16023 := hb (x 15 13)
      have b16024 := hb (x 14 1 && x 14 14)
      clear * - r16021 b16022 b16023 b16024 d15996 d16004
      omega
    have d16025 : (x 15 1).toNat = 1 := by
      have r16026 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
      have b16027 := hb (x 15 1)
      have b16028 := hb (x 15 13)
      clear * - r16026 b16027 b16028 d16020
      omega
    have d16029 : (x 16 14).toNat = 0 := by
      have r16030 : (x 16 14).toNat + (x 15 1).toNat = 1 := by have q := hd14 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16031 := hb (x 15 1)
      have b16032 := hb (x 16 14)
      clear * - r16030 b16031 b16032 d16025
      omega
    have d16033 : (x 16 2).toNat = 0 := by
      have r16034 : (x 16 2).toNat ≤ (x 16 14).toNat := himp _ _ (hp2 16)
      have b16035 := hb (x 16 2)
      have b16036 := hb (x 16 14)
      clear * - r16034 b16035 b16036 d16029
      omega
    have d16037 : (x 16 2 && x 16 11).toNat = 0 := by
      have r16038 := hand1 (x 16 2) (x 16 11)
      have b16039 := hb (x 16 2)
      have b16040 := hb (x 16 2 && x 16 11)
      clear * - r16038 b16039 b16040 d16033
      omega
    have d16041 : (x 12 3).toNat = 0 := by
      have r16042 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16043 := hb (x 1 14)
      have b16044 := hb (x 2 13)
      have b16045 := hb (x 3 12)
      have b16046 := hb (x 4 11)
      have b16047 := hb (x 5 10)
      have b16048 := hb (x 6 9)
      have b16049 := hb (x 7 8)
      have b16050 := hb (x 8 7)
      have b16051 := hb (x 9 6)
      have b16052 := hb (x 10 5)
      have b16053 := hb (x 11 4)
      have b16054 := hb (x 12 3)
      have b16055 := hb (x 13 2)
      have b16056 := hb (x 14 1)
      clear * - r16042 b16043 b16044 b16045 b16046 b16047 b16048 b16049 b16050 b16051 b16052 b16053 b16054 b16055 b16056 d15980 d16004 d15880 d15348 d15948 d15964 d14917 d14941 d14965 d14993 g37 g32 g30
      omega
    have d16057 : (x 15 12).toNat = 1 := by
      have r16058 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16059 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
      have e16060 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
      have b16061 := hb (x 12 3)
      have b16062 := hb (x 13 2)
      have b16063 := hb (x 14 13)
      have b16064 := hb (x 15 12)
      clear * - r16058 e16059 e16060 b16061 b16062 b16063 b16064 d16000 d16004 d16041
      omega
    have d16065 : (x 15 11 && x 15 12).toNat = 0 := by
      have r16066 := hand1 (x 15 11) (x 15 12)
      have b16067 := hb (x 15 11)
      have b16068 := hb (x 15 11 && x 15 12)
      clear * - r16066 b16067 b16068 d15775
      omega
    have r16069 : (x 17 1).toNat + (x 16 2).toNat + (x 15 3).toNat + (x 14 4).toNat + (x 13 5).toNat + (x 12 6).toNat + (x 11 7).toNat + (x 10 8).toNat + (x 9 9).toNat + (x 8 10).toNat + (x 7 11).toNat + (x 6 12).toNat + (x 5 13).toNat + (x 4 14).toNat = 3 := by have q := hcount 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r16070 : (x 26 1).toNat + (x 25 2).toNat + (x 24 3).toNat + (x 23 4).toNat + (x 22 5).toNat + (x 21 6).toNat + (x 20 7).toNat + (x 19 8).toNat + (x 18 9).toNat + (x 17 10).toNat + (x 16 11).toNat + (x 15 12).toNat + (x 14 13).toNat + (x 13 14).toNat = 3 := by have q := hcount 27; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r16071 : 1 ≤ (x 26 1).toNat + (x 25 1 && x 25 2).toNat + (x 24 2 && x 24 3).toNat + (x 23 3 && x 23 4).toNat + (x 22 4 && x 22 5).toNat + (x 21 5 && x 21 6).toNat + (x 20 6 && x 20 7).toNat + (x 19 7 && x 19 8).toNat + (x 18 8 && x 18 9).toNat + (x 17 9 && x 17 10).toNat + (x 16 10 && x 16 11).toNat + (x 15 11 && x 15 12).toNat + (x 14 12 && x 14 13).toNat + (x 13 13 && x 13 14).toNat + (x 12 14).toNat := by have q := hcov1 26; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r16072 : 1 ≤ (x 9 9).toNat + (x 8 1 && x 8 10).toNat + (x 7 2 && x 7 11).toNat + (x 6 3 && x 6 12).toNat + (x 5 4 && x 5 13).toNat + (x 4 5 && x 4 14).toNat + (x 3 6).toNat := by have q := hcov9 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r16073 : 1 ≤ (x 18 9).toNat + (x 17 1 && x 17 10).toNat + (x 16 2 && x 16 11).toNat + (x 15 3 && x 15 12).toNat + (x 14 4 && x 14 13).toNat + (x 13 5 && x 13 14).toNat + (x 12 6).toNat := by have q := hcov9 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r16074 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r16075 := hand2 (x 25 1) (x 25 2)
    have r16076 := hand2 (x 24 2) (x 24 3)
    have r16077 := hand2 (x 23 3) (x 23 4)
    have r16078 := hand2 (x 22 4) (x 22 5)
    have r16079 := hand2 (x 21 5) (x 21 6)
    have r16080 := hand2 (x 20 6) (x 20 7)
    have r16081 := hand2 (x 19 7) (x 19 8)
    have r16082 := hand2 (x 8 1) (x 8 10)
    have r16083 := hand2 (x 7 2) (x 7 11)
    have r16084 := hand2 (x 6 3) (x 6 12)
    have r16085 := hand2 (x 17 1) (x 17 10)
    have r16086 := hand1 (x 15 3) (x 15 12)
    have r16087 := hand2 (x 4 1) (x 4 14)
    linarith only [r16069, r16070, r16071, r16072, r16073, r16074, r16075, r16076, r16077, r16078, r16079, r16080, r16081, r16082, r16083, r16084, r16085, r16086, r16087, g33, g35, d15707, d15389, d15377, d15537, d15610, d15513, d16000, d16057, d16033, d15727, d15747, d15771, d16065, d15509, d15533, d14212, d14244, d16037, d15517, d15541]

theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000100_p3 (x : ℤ → Fin 16 → Bool)
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
    (h14481 : x 2 5 = true)
    (h15114 : x (-2) 8 = false)
    : False := cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000100_p3_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83 g84 g85 g86 g87 g88 g89 g90 g91 g92 g93 g94 h14164 h14170 h14336 h14338 h14340 h14342 h14479 h14481 h15114
