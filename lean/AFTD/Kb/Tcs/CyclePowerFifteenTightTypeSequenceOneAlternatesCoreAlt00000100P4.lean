import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000100_p4

Topic: combinatorics   Node: 427d1307c558

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

Sub-branch of the window refutation cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000100 (one subtree of its case split, cut out so each piece fits the build limit): under the same layer-free tight-cover constraints for k = 15, its fixed bits and the case bits of this subtree, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000100_p4_aux (x : ℤ → Fin 16 → Bool)
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
    (h15114 : x (-2) 8 = true)
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
  have f16143 : (x (-2) 8).toNat = 1 := by rw [h15114]; rfl
  have d16144 : (x (-3) 9).toNat = 0 := by
    have r16145 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16146 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
    have e16147 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
    have e16148 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
    have e16149 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
    have e16150 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
    have e16151 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
    have b16152 := hb (x (-9) 7)
    have b16153 := hb (x (-8) 6)
    have b16154 := hb (x (-7) 5)
    have b16155 := hb (x (-6) 4)
    have b16156 := hb (x (-5) 11)
    have b16157 := hb (x (-4) 10)
    have b16158 := hb (x (-3) 9)
    have b16159 := hb (x (-2) 8)
    clear * - r16145 e16146 e16147 e16148 e16149 e16150 e16151 b16152 b16153 b16154 b16155 b16156 b16157 b16158 b16159 f16143 d14393
    omega
  have d16160 : (x (-5) 11).toNat = 0 := by
    have r16161 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16162 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
    have e16163 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
    have e16164 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
    have e16165 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
    have e16166 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
    have e16167 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
    have b16168 := hb (x (-9) 7)
    have b16169 := hb (x (-8) 6)
    have b16170 := hb (x (-7) 5)
    have b16171 := hb (x (-6) 4)
    have b16172 := hb (x (-5) 11)
    have b16173 := hb (x (-4) 10)
    have b16174 := hb (x (-3) 9)
    have b16175 := hb (x (-2) 8)
    clear * - r16161 e16162 e16163 e16164 e16165 e16166 e16167 b16168 b16169 b16170 b16171 b16172 b16173 b16174 b16175 f16143 d16144 d14393
    omega
  have d16176 : (x (-5) 2 && x (-5) 11).toNat = 0 := by
    have r16177 := hand2 (x (-5) 2) (x (-5) 11)
    have b16178 := hb (x (-5) 11)
    have b16179 := hb (x (-5) 2 && x (-5) 11)
    clear * - r16177 b16178 b16179 d16160
    omega
  have d16180 : (x (-9) 4).toNat = 1 := by
    have r16181 : 1 ≤ (x (-5) 11).toNat + (x (-6) 1 && x (-6) 12).toNat + (x (-7) 2 && x (-7) 13).toNat + (x (-8) 3 && x (-8) 14).toNat + (x (-9) 4).toNat := by have q := hcov11 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16182 := hb (x (-9) 4)
    have b16183 := hb (x (-5) 11)
    have b16184 := hb (x (-6) 1 && x (-6) 12)
    have b16185 := hb (x (-7) 2 && x (-7) 13)
    have b16186 := hb (x (-8) 3 && x (-8) 14)
    clear * - r16181 b16182 b16183 b16184 b16185 b16186 d16160 d14467 d14088 d14108
    omega
  have d16187 : (x (-9) 12).toNat = 1 := by
    have r16188 : (x (-9) 4).toNat ≤ (x (-9) 12).toNat := himp _ _ (hp4 (-9))
    have b16189 := hb (x (-9) 4)
    have b16190 := hb (x (-9) 12)
    clear * - r16188 b16189 b16190 d16180
    omega
  have d16191 : (x (-10) 13).toNat = 0 := by
    have r16192 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16193 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
    have e16194 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
    have b16195 := hb (x (-12) 3)
    have b16196 := hb (x (-11) 2)
    have b16197 := hb (x (-10) 13)
    have b16198 := hb (x (-9) 12)
    clear * - r16192 e16193 e16194 b16195 b16196 b16197 b16198 d16187
    omega
  have d16199 : (x (-10) 8 && x (-10) 13).toNat = 0 := by
    have r16200 := hand2 (x (-10) 8) (x (-10) 13)
    have b16201 := hb (x (-10) 13)
    have b16202 := hb (x (-10) 8 && x (-10) 13)
    clear * - r16200 b16201 b16202 d16191
    omega
  have d16203 : (x (-10) 5).toNat = 0 := by
    have r16204 : (x (-10) 5).toNat ≤ (x (-10) 13).toNat := himp _ _ (hp5 (-10))
    have b16205 := hb (x (-10) 5)
    have b16206 := hb (x (-10) 13)
    clear * - r16204 b16205 b16206 d16191
    omega
  have d16207 : (x (-6) 4).toNat = 0 := by
    have r16208 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16209 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
    have e16210 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
    have e16211 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
    have e16212 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
    have e16213 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
    have e16214 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
    have b16215 := hb (x (-9) 7)
    have b16216 := hb (x (-8) 6)
    have b16217 := hb (x (-7) 5)
    have b16218 := hb (x (-6) 4)
    have b16219 := hb (x (-5) 11)
    have b16220 := hb (x (-4) 10)
    have b16221 := hb (x (-3) 9)
    have b16222 := hb (x (-2) 8)
    clear * - r16208 e16209 e16210 e16211 e16212 e16213 e16214 b16215 b16216 b16217 b16218 b16219 b16220 b16221 b16222 f16143 d16144 d14393 d16160
    omega
  have d16223 : (x (-6) 4 && x (-6) 14).toNat = 0 := by
    have r16224 := hand1 (x (-6) 4) (x (-6) 14)
    have b16225 := hb (x (-6) 4)
    have b16226 := hb (x (-6) 4 && x (-6) 14)
    clear * - r16224 b16225 b16226 d16207
    omega
  have d16227 : (x (-6) 4 && x (-6) 11).toNat = 0 := by
    have r16228 := hand1 (x (-6) 4) (x (-6) 11)
    have b16229 := hb (x (-6) 4)
    have b16230 := hb (x (-6) 4 && x (-6) 11)
    clear * - r16228 b16229 b16230 d16207
    omega
  have d16231 : (x (-7) 5).toNat = 0 := by
    have r16232 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16233 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
    have e16234 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
    have e16235 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
    have e16236 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
    have e16237 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
    have e16238 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
    have b16239 := hb (x (-9) 7)
    have b16240 := hb (x (-8) 6)
    have b16241 := hb (x (-7) 5)
    have b16242 := hb (x (-6) 4)
    have b16243 := hb (x (-5) 11)
    have b16244 := hb (x (-4) 10)
    have b16245 := hb (x (-3) 9)
    have b16246 := hb (x (-2) 8)
    clear * - r16232 e16233 e16234 e16235 e16236 e16237 e16238 b16239 b16240 b16241 b16242 b16243 b16244 b16245 b16246 f16143 d16144 d14393 d16160 d16207
    omega
  have d16247 : (x (-7) 5 && x (-7) 12).toNat = 0 := by
    have r16248 := hand1 (x (-7) 5) (x (-7) 12)
    have b16249 := hb (x (-7) 5)
    have b16250 := hb (x (-7) 5 && x (-7) 12)
    clear * - r16248 b16249 b16250 d16231
    omega
  have d16251 : (x (-5) 3 && x (-5) 13).toNat = 1 := by
    have r16252 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16253 := hb (x (-7) 5)
    have b16254 := hb (x (-2) 10)
    have b16255 := hb (x (-3) 1 && x (-3) 11)
    have b16256 := hb (x (-4) 2 && x (-4) 12)
    have b16257 := hb (x (-5) 3 && x (-5) 13)
    have b16258 := hb (x (-6) 4 && x (-6) 14)
    clear * - r16252 b16253 b16254 b16255 b16256 b16257 b16258 g5 g78 d14381 d16223 d16231
    omega
  have d16259 : (x (-5) 3).toNat = 1 := by
    have r16260 := hand1 (x (-5) 3) (x (-5) 13)
    have b16261 := hb (x (-5) 3)
    have b16262 := hb (x (-5) 3 && x (-5) 13)
    clear * - r16260 b16261 b16262 d16251
    omega
  have d16263 : (x (-2) 12).toNat = 0 := by
    have r16264 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16265 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
    have e16266 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
    have b16267 := hb (x (-5) 3)
    have b16268 := hb (x (-4) 2)
    have b16269 := hb (x (-3) 13)
    have b16270 := hb (x (-2) 12)
    clear * - r16264 e16265 e16266 b16267 b16268 b16269 b16270 d14373 d16259
    omega
  have d16271 : (x (-3) 13).toNat = 0 := by
    have r16272 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16273 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
    have e16274 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
    have b16275 := hb (x (-5) 3)
    have b16276 := hb (x (-4) 2)
    have b16277 := hb (x (-3) 13)
    have b16278 := hb (x (-2) 12)
    clear * - r16272 e16273 e16274 b16275 b16276 b16277 b16278 d16263 d14373 d16259
    omega
  have d16279 : (x (-3) 5).toNat = 0 := by
    have r16280 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
    have b16281 := hb (x (-3) 5)
    have b16282 := hb (x (-3) 13)
    clear * - r16280 b16281 b16282 d16271
    omega
  have d16283 : (x (-3) 5 && x (-3) 14).toNat = 0 := by
    have r16284 := hand1 (x (-3) 5) (x (-3) 14)
    have b16285 := hb (x (-3) 5)
    have b16286 := hb (x (-3) 5 && x (-3) 14)
    clear * - r16284 b16285 b16286 d16279
    omega
  have d16287 : (x 2 9).toNat = 1 := by
    have r16288 : 1 ≤ (x 2 9).toNat + (x 1 1 && x 1 10).toNat + (x 0 2 && x 0 11).toNat + (x (-1) 3 && x (-1) 12).toNat + (x (-2) 4 && x (-2) 13).toNat + (x (-3) 5 && x (-3) 14).toNat + (x (-4) 6).toNat := by have q := hcov9 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16289 := hb (x (-4) 6)
    have b16290 := hb (x 2 9)
    have b16291 := hb (x 1 1 && x 1 10)
    have b16292 := hb (x 0 2 && x 0 11)
    have b16293 := hb (x (-1) 3 && x (-1) 12)
    have b16294 := hb (x (-2) 4 && x (-2) 13)
    have b16295 := hb (x (-3) 5 && x (-3) 14)
    clear * - r16288 b16289 b16290 b16291 b16292 b16293 b16294 b16295 g73 g74 d14021 g75 d16283 d14369
    omega
  have d16296 : (x 3 8).toNat = 0 := by
    have r16297 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16298 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
    have e16299 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
    have e16300 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
    have e16301 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
    have e16302 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
    have e16303 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
    have b16304 := hb (x (-4) 7)
    have b16305 := hb (x (-3) 6)
    have b16306 := hb (x (-2) 5)
    have b16307 := hb (x (-1) 4)
    have b16308 := hb (x 0 11)
    have b16309 := hb (x 1 10)
    have b16310 := hb (x 2 9)
    have b16311 := hb (x 3 8)
    clear * - r16297 e16298 e16299 e16300 e16301 e16302 e16303 b16304 b16305 b16306 b16307 b16308 b16309 b16310 b16311 d16287 g28 g21 f14171 g3
    omega
  have d16312 : (x (-3) 6).toNat = 0 := by
    have r16313 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16314 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
    have e16315 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
    have e16316 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
    have e16317 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
    have e16318 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
    have e16319 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
    have b16320 := hb (x (-4) 7)
    have b16321 := hb (x (-3) 6)
    have b16322 := hb (x (-2) 5)
    have b16323 := hb (x (-1) 4)
    have b16324 := hb (x 0 11)
    have b16325 := hb (x 1 10)
    have b16326 := hb (x 2 9)
    have b16327 := hb (x 3 8)
    clear * - r16313 e16314 e16315 e16316 e16317 e16318 e16319 b16320 b16321 b16322 b16323 b16324 b16325 b16326 b16327 d16296 d16287 g28 g21 f14171 g3
    omega
  have d16328 : (x (-3) 1 && x (-3) 6).toNat = 0 := by
    have r16329 := hand2 (x (-3) 1) (x (-3) 6)
    have b16330 := hb (x (-3) 6)
    have b16331 := hb (x (-3) 1 && x (-3) 6)
    clear * - r16329 b16330 b16331 d16312
    omega
  have d16332 : (x (-5) 2).toNat = 1 := by
    have r16333 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16334 := hb (x (-5) 2)
    have b16335 := hb (x (-3) 13)
    have b16336 := hb (x (-4) 1 && x (-4) 14)
    clear * - r16333 b16334 b16335 b16336 d16271 d14365
    omega
  have d16337 : (x (-3) 12).toNat = 0 := by
    have r16338 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16339 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
    have e16340 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
    have b16341 := hb (x (-6) 3)
    have b16342 := hb (x (-5) 2)
    have b16343 := hb (x (-4) 13)
    have b16344 := hb (x (-3) 12)
    clear * - r16338 e16339 e16340 b16341 b16342 b16343 b16344 d14414 d16332
    omega
  have d16345 : (x (-6) 3).toNat = 0 := by
    have r16346 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16347 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
    have e16348 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
    have b16349 := hb (x (-6) 3)
    have b16350 := hb (x (-5) 2)
    have b16351 := hb (x (-4) 13)
    have b16352 := hb (x (-3) 12)
    clear * - r16346 e16347 e16348 b16349 b16350 b16351 b16352 d16337 d14414 d16332
    omega
  have d16353 : (x (-6) 3 && x (-6) 12).toNat = 0 := by
    have r16354 := hand1 (x (-6) 3) (x (-6) 12)
    have b16355 := hb (x (-6) 3)
    have b16356 := hb (x (-6) 3 && x (-6) 12)
    clear * - r16354 b16355 b16356 d16345
    omega
  have d16357 : (x (-6) 11).toNat = 0 := by
    have r16358 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
    have b16359 := hb (x (-6) 3)
    have b16360 := hb (x (-6) 11)
    clear * - r16358 b16359 b16360 d16345
    omega
  have d16361 : (x (-8) 6).toNat = 0 := by
    have r16362 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16363 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
    have e16364 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
    have e16365 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
    have e16366 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
    have e16367 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
    have e16368 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
    have b16369 := hb (x (-9) 7)
    have b16370 := hb (x (-8) 6)
    have b16371 := hb (x (-7) 5)
    have b16372 := hb (x (-6) 4)
    have b16373 := hb (x (-5) 11)
    have b16374 := hb (x (-4) 10)
    have b16375 := hb (x (-3) 9)
    have b16376 := hb (x (-2) 8)
    clear * - r16362 e16363 e16364 e16365 e16366 e16367 e16368 b16369 b16370 b16371 b16372 b16373 b16374 b16375 b16376 f16143 d16144 d14393 d16160 d16207 d16231
    omega
  have d16377 : (x (-8) 6 && x (-8) 13).toNat = 0 := by
    have r16378 := hand1 (x (-8) 6) (x (-8) 13)
    have b16379 := hb (x (-8) 6)
    have b16380 := hb (x (-8) 6 && x (-8) 13)
    clear * - r16378 b16379 b16380 d16361
    omega
  have d16381 : (x (-9) 7).toNat = 0 := by
    have r16382 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16383 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
    have e16384 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
    have e16385 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
    have e16386 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
    have e16387 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
    have e16388 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
    have b16389 := hb (x (-9) 7)
    have b16390 := hb (x (-8) 6)
    have b16391 := hb (x (-7) 5)
    have b16392 := hb (x (-6) 4)
    have b16393 := hb (x (-5) 11)
    have b16394 := hb (x (-4) 10)
    have b16395 := hb (x (-3) 9)
    have b16396 := hb (x (-2) 8)
    clear * - r16382 e16383 e16384 e16385 e16386 e16387 e16388 b16389 b16390 b16391 b16392 b16393 b16394 b16395 b16396 f16143 d16144 d14393 d16160 d16207 d16231 d16361
    omega
  have d16397 : (x (-9) 7 && x (-9) 14).toNat = 0 := by
    have r16398 := hand1 (x (-9) 7) (x (-9) 14)
    have b16399 := hb (x (-9) 7)
    have b16400 := hb (x (-9) 7 && x (-9) 14)
    clear * - r16398 b16399 b16400 d16381
    omega
  have d16401 : (x (-9) 7 && x (-9) 12).toNat = 0 := by
    have r16402 := hand1 (x (-9) 7) (x (-9) 12)
    have b16403 := hb (x (-9) 7)
    have b16404 := hb (x (-9) 7 && x (-9) 12)
    clear * - r16402 b16403 b16404 d16381
    omega
  have d16405 : (x (-5) 8).toNat = 0 := by
    have r16406 : (x (-5) 8).toNat + (x (-6) 1 && x (-6) 9).toNat + (x (-7) 2 && x (-7) 10).toNat + (x (-8) 3 && x (-8) 11).toNat + (x (-9) 4 && x (-9) 12).toNat + (x (-10) 5 && x (-10) 13).toNat + (x (-11) 6 && x (-11) 14).toNat + (x (-12) 7).toNat = 1 := by have q := hd8 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16407 : (x (-6) 1 && x (-6) 9).toNat = (x (-6) 9).toNat := handr _ _ (fun h => hp9 (-6) (h))
    have e16408 : (x (-7) 2 && x (-7) 10).toNat = (x (-7) 10).toNat := handr _ _ (fun h => hp10 (-7) (h))
    have e16409 : (x (-8) 3 && x (-8) 11).toNat = (x (-8) 11).toNat := handr _ _ (fun h => hp11 (-8) (h))
    have e16410 : (x (-9) 4 && x (-9) 12).toNat = (x (-9) 4).toNat := handl _ _ (fun h => hp4 (-9) (h))
    have e16411 : (x (-10) 5 && x (-10) 13).toNat = (x (-10) 5).toNat := handl _ _ (fun h => hp5 (-10) (h))
    have e16412 : (x (-11) 6 && x (-11) 14).toNat = (x (-11) 6).toNat := handl _ _ (fun h => hp6 (-11) (h))
    have b16413 := hb (x (-12) 7)
    have b16414 := hb (x (-11) 6)
    have b16415 := hb (x (-10) 5)
    have b16416 := hb (x (-9) 4)
    have b16417 := hb (x (-8) 11)
    have b16418 := hb (x (-7) 10)
    have b16419 := hb (x (-6) 9)
    have b16420 := hb (x (-5) 8)
    clear * - r16406 e16407 e16408 e16409 e16410 e16411 e16412 b16413 b16414 b16415 b16416 b16417 b16418 b16419 b16420 d14471 d14092 d14112 d16180 d16203
    omega
  have d16421 : (x (-5) 3 && x (-5) 8).toNat = 0 := by
    have r16422 := hand2 (x (-5) 3) (x (-5) 8)
    have b16423 := hb (x (-5) 8)
    have b16424 := hb (x (-5) 3 && x (-5) 8)
    clear * - r16422 b16423 b16424 d16405
    omega
  have r16425 : (x (-10) 8).toNat + (x (-11) 1 && x (-11) 9).toNat + (x (-12) 2 && x (-12) 10).toNat + (x (-13) 3 && x (-13) 11).toNat + (x (-14) 4 && x (-14) 12).toNat + (x (-15) 5 && x (-15) 13).toNat + (x (-16) 6 && x (-16) 14).toNat + (x (-17) 7).toNat = 1 := by have q := hd8 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e16426 : (x (-11) 1 && x (-11) 9).toNat = (x (-11) 9).toNat := handr _ _ (fun h => hp9 (-11) (h))
  have e16427 : (x (-12) 2 && x (-12) 10).toNat = (x (-12) 10).toNat := handr _ _ (fun h => hp10 (-12) (h))
  have e16428 : (x (-13) 3 && x (-13) 11).toNat = (x (-13) 11).toNat := handr _ _ (fun h => hp11 (-13) (h))
  have e16429 : (x (-14) 4 && x (-14) 12).toNat = (x (-14) 4).toNat := handl _ _ (fun h => hp4 (-14) (h))
  have e16430 : (x (-15) 5 && x (-15) 13).toNat = (x (-15) 5).toNat := handl _ _ (fun h => hp5 (-15) (h))
  have e16431 : (x (-16) 6 && x (-16) 14).toNat = (x (-16) 6).toNat := handl _ _ (fun h => hp6 (-16) (h))
  have r16432 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e16433 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
  have e16434 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
  have e16435 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
  have e16436 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
  have e16437 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
  have e16438 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
  have r16439 : 1 ≤ (x (-2) 5).toNat + (x (-3) 1 && x (-3) 6).toNat + (x (-4) 2 && x (-4) 7).toNat + (x (-5) 3 && x (-5) 8).toNat + (x (-6) 4 && x (-6) 9).toNat + (x (-7) 5 && x (-7) 10).toNat + (x (-8) 6 && x (-8) 11).toNat + (x (-9) 7 && x (-9) 12).toNat + (x (-10) 8 && x (-10) 13).toNat + (x (-11) 9 && x (-11) 14).toNat + (x (-12) 10).toNat := by have q := hcov5 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r16440 : 1 ≤ (x (-2) 7).toNat + (x (-3) 1 && x (-3) 8).toNat + (x (-4) 2 && x (-4) 9).toNat + (x (-5) 3 && x (-5) 10).toNat + (x (-6) 4 && x (-6) 11).toNat + (x (-7) 5 && x (-7) 12).toNat + (x (-8) 6 && x (-8) 13).toNat + (x (-9) 7 && x (-9) 14).toNat + (x (-10) 8).toNat := by have q := hcov7 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r16441 : 1 ≤ (x (-3) 9).toNat + (x (-4) 1 && x (-4) 10).toNat + (x (-5) 2 && x (-5) 11).toNat + (x (-6) 3 && x (-6) 12).toNat + (x (-7) 4 && x (-7) 13).toNat + (x (-8) 5 && x (-8) 14).toNat + (x (-9) 6).toNat := by have q := hcov9 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r16442 := hand1 (x (-11) 9) (x (-11) 14)
  have r16443 := hand2 (x (-3) 1) (x (-3) 8)
  have r16444 := hand2 (x (-5) 3) (x (-5) 10)
  have r16445 := hand1 (x (-7) 4) (x (-7) 13)
  have r16446 := hand1 (x (-8) 5) (x (-8) 14)
  linarith only [r16425, e16426, e16427, e16428, e16429, e16430, e16431, r16432, e16433, e16434, e16435, e16436, e16437, e16438, r16439, r16440, r16441, r16442, r16443, r16444, r16445, r16446, d16357, d14418, d16144, g3, d14320, d16328, d14389, d16421, d14475, d14096, d14116, d16401, d16199, d14385, d16227, d16247, d16377, d16397, d14397, d16176, d16353]

theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000100_p4 (x : ℤ → Fin 16 → Bool)
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
    (h15114 : x (-2) 8 = true)
    : False := cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000100_p4_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83 g84 g85 g86 g87 g88 g89 g90 g91 g92 g93 g94 h14164 h14170 h14336 h14338 h14340 h14342 h14479 h14481 h15114
