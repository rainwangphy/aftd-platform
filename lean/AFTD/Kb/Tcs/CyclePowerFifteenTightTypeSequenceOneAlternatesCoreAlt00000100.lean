import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneAlternatesCoreAlt00000100P1
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneAlternatesCoreAlt00000100P2
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneAlternatesCoreAlt00000100P3
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneAlternatesCoreAlt00000100P4
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000100

Topic: combinatorics   Node: 5346782ca040

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_alternates_core: under the layer-free tight-cover constraints for k = 15 and 95 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000100_aux (x : ℤ → Fin 16 → Bool)
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
  cases h14164 : x 1 3
  · have f14165 : (x 1 3).toNat = 0 := by rw [h14164]; rfl
    have d14166 : (x 1 11).toNat = 0 := by
      have r14167 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
      have b14168 := hb (x 1 3)
      have b14169 := hb (x 1 11)
      clear * - r14167 b14168 b14169 f14165
      omega
    cases h14170 : x (-1) 4
    · have f14171 : (x (-1) 4).toNat = 0 := by rw [h14170]; rfl
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
      cases h14336 : x 1 6
      · have f14337 : (x 1 6).toNat = 0 := by rw [h14336]; rfl
        cases h14338 : x (-1) 7
        · have f14339 : (x (-1) 7).toNat = 0 := by rw [h14338]; rfl
          cases h14340 : x 1 8
          · have f14341 : (x 1 8).toNat = 0 := by rw [h14340]; rfl
            cases h14342 : x (-1) 9
            · have f14343 : (x (-1) 9).toNat = 0 := by rw [h14342]; rfl
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
              cases h14479 : x (-2) 4
              · have f14480 : (x (-2) 4).toNat = 0 := by rw [h14479]; rfl
                cases h14481 : x 2 5
                · exact cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000100_p2 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83 g84 g85 g86 g87 g88 g89 g90 g91 g92 g93 g94 h14164 h14170 h14336 h14338 h14340 h14342 h14479 h14481
                · have f14916 : (x 2 5).toNat = 1 := by rw [h14481]; rfl
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
                  cases h15114 : x (-2) 8
                  · exact cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000100_p3 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83 g84 g85 g86 g87 g88 g89 g90 g91 g92 g93 g94 h14164 h14170 h14336 h14338 h14340 h14342 h14479 h14481 h15114
                  · exact cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000100_p4 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83 g84 g85 g86 g87 g88 g89 g90 g91 g92 g93 g94 h14164 h14170 h14336 h14338 h14340 h14342 h14479 h14481 h15114
              · have f16487 : (x (-2) 4).toNat = 1 := by rw [h14479]; rfl
                have d16488 : (x (-2) 12).toNat = 1 := by
                  have r16489 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
                  have b16490 := hb (x (-2) 4)
                  have b16491 := hb (x (-2) 12)
                  clear * - r16489 b16490 b16491 f16487
                  omega
                have d16492 : (x (-3) 13).toNat = 0 := by
                  have r16493 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e16494 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                  have e16495 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                  have b16496 := hb (x (-5) 3)
                  have b16497 := hb (x (-4) 2)
                  have b16498 := hb (x (-3) 13)
                  have b16499 := hb (x (-2) 12)
                  clear * - r16493 e16494 e16495 b16496 b16497 b16498 b16499 d16488 d14373
                  omega
                have d16500 : (x (-5) 2).toNat = 1 := by
                  have r16501 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b16502 := hb (x (-5) 2)
                  have b16503 := hb (x (-3) 13)
                  have b16504 := hb (x (-4) 1 && x (-4) 14)
                  clear * - r16501 b16502 b16503 b16504 d16492 d14365
                  omega
                have d16505 : (x (-5) 3).toNat = 0 := by
                  have r16506 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e16507 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                  have e16508 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                  have b16509 := hb (x (-5) 3)
                  have b16510 := hb (x (-4) 2)
                  have b16511 := hb (x (-3) 13)
                  have b16512 := hb (x (-2) 12)
                  clear * - r16506 e16507 e16508 b16509 b16510 b16511 b16512 d16488 d16492 d14373
                  omega
                have d16513 : (x (-5) 3 && x (-5) 14).toNat = 0 := by
                  have r16514 := hand1 (x (-5) 3) (x (-5) 14)
                  have b16515 := hb (x (-5) 3)
                  have b16516 := hb (x (-5) 3 && x (-5) 14)
                  clear * - r16514 b16515 b16516 d16505
                  omega
                have d16517 : (x (-5) 3 && x (-5) 13).toNat = 0 := by
                  have r16518 := hand1 (x (-5) 3) (x (-5) 13)
                  have b16519 := hb (x (-5) 3)
                  have b16520 := hb (x (-5) 3 && x (-5) 13)
                  clear * - r16518 b16519 b16520 d16505
                  omega
                have d16521 : (x (-3) 12).toNat = 0 := by
                  have r16522 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e16523 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                  have e16524 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                  have b16525 := hb (x (-6) 3)
                  have b16526 := hb (x (-5) 2)
                  have b16527 := hb (x (-4) 13)
                  have b16528 := hb (x (-3) 12)
                  clear * - r16522 e16523 e16524 b16525 b16526 b16527 b16528 d14414 d16500
                  omega
                have d16529 : (x (-3) 1 && x (-3) 12).toNat = 0 := by
                  have r16530 := hand2 (x (-3) 1) (x (-3) 12)
                  have b16531 := hb (x (-3) 12)
                  have b16532 := hb (x (-3) 1 && x (-3) 12)
                  clear * - r16530 b16531 b16532 d16521
                  omega
                have d16533 : (x (-6) 4).toNat = 1 := by
                  have r16534 : 1 ≤ (x (-2) 11).toNat + (x (-3) 1 && x (-3) 12).toNat + (x (-4) 2 && x (-4) 13).toNat + (x (-5) 3 && x (-5) 14).toNat + (x (-6) 4).toNat := by have q := hcov11 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b16535 := hb (x (-6) 4)
                  have b16536 := hb (x (-2) 11)
                  have b16537 := hb (x (-3) 1 && x (-3) 12)
                  have b16538 := hb (x (-4) 2 && x (-4) 13)
                  have b16539 := hb (x (-5) 3 && x (-5) 14)
                  clear * - r16534 b16535 b16536 b16537 b16538 b16539 g6 d16529 d14377 d16513
                  omega
                have d16540 : (x (-6) 12).toNat = 1 := by
                  have r16541 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
                  have b16542 := hb (x (-6) 4)
                  have b16543 := hb (x (-6) 12)
                  clear * - r16541 b16542 b16543 d16533
                  omega
                have d16544 : (x (-7) 13).toNat = 0 := by
                  have r16545 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e16546 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
                  have e16547 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
                  have b16548 := hb (x (-9) 3)
                  have b16549 := hb (x (-8) 2)
                  have b16550 := hb (x (-7) 13)
                  have b16551 := hb (x (-6) 12)
                  clear * - r16545 e16546 e16547 b16548 b16549 b16550 b16551 d16540
                  omega
                have d16552 : (x (-7) 5).toNat = 0 := by
                  have r16553 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
                  have b16554 := hb (x (-7) 5)
                  have b16555 := hb (x (-7) 13)
                  clear * - r16553 b16554 b16555 d16544
                  omega
                have d16556 : (x (-8) 2).toNat = 0 := by
                  have r16557 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e16558 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
                  have e16559 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
                  have b16560 := hb (x (-9) 3)
                  have b16561 := hb (x (-8) 2)
                  have b16562 := hb (x (-7) 13)
                  have b16563 := hb (x (-6) 12)
                  clear * - r16557 e16558 e16559 b16560 b16561 b16562 b16563 d16540 d16544
                  omega
                have d16564 : (x (-7) 1 && x (-7) 14).toNat = 1 := by
                  have r16565 : 1 ≤ (x (-6) 13).toNat + (x (-7) 1 && x (-7) 14).toNat + (x (-8) 2).toNat := by have q := hcov13 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b16566 := hb (x (-8) 2)
                  have b16567 := hb (x (-6) 13)
                  have b16568 := hb (x (-7) 1 && x (-7) 14)
                  clear * - r16565 b16566 b16567 b16568 d14056 d16556
                  omega
                have d16569 : (x (-7) 1).toNat = 1 := by
                  have r16570 := hand1 (x (-7) 1) (x (-7) 14)
                  have b16571 := hb (x (-7) 1)
                  have b16572 := hb (x (-7) 1 && x (-7) 14)
                  clear * - r16570 b16571 b16572 d16564
                  omega
                have d16573 : (x (-6) 14).toNat = 0 := by
                  have r16574 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b16575 := hb (x (-7) 1)
                  have b16576 := hb (x (-6) 14)
                  clear * - r16574 b16575 b16576 d16569
                  omega
                have d16577 : (x (-6) 4 && x (-6) 14).toNat = 0 := by
                  have r16578 := hand2 (x (-6) 4) (x (-6) 14)
                  have b16579 := hb (x (-6) 14)
                  have b16580 := hb (x (-6) 4 && x (-6) 14)
                  clear * - r16578 b16579 b16580 d16573
                  omega
                have r16581 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b16582 := hb (x (-7) 5)
                have b16583 := hb (x (-2) 10)
                have b16584 := hb (x (-3) 1 && x (-3) 11)
                have b16585 := hb (x (-4) 2 && x (-4) 12)
                have b16586 := hb (x (-5) 3 && x (-5) 13)
                have b16587 := hb (x (-6) 4 && x (-6) 14)
                linarith only [r16581, b16582, b16583, b16584, b16585, b16586, b16587, g5, g78, d14381, d16517, d16577, d16552]
            · have f16588 : (x (-1) 9).toNat = 1 := by rw [h14342]; rfl
              have d16589 : (x (-4) 4).toNat = 0 := by
                have r16590 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e16591 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                have e16592 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                have e16593 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                have e16594 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                have e16595 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                have e16596 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                have b16597 := hb (x (-7) 7)
                have b16598 := hb (x (-6) 6)
                have b16599 := hb (x (-5) 5)
                have b16600 := hb (x (-4) 4)
                have b16601 := hb (x (-3) 11)
                have b16602 := hb (x (-2) 10)
                have b16603 := hb (x (-1) 9)
                have b16604 := hb (x 0 8)
                clear * - r16590 e16591 e16592 e16593 e16594 e16595 e16596 b16597 b16598 b16599 b16600 b16601 b16602 b16603 b16604 g18 f16588 g5 g2
                omega
              have d16605 : (x (-4) 4 && x (-4) 14).toNat = 0 := by
                have r16606 := hand1 (x (-4) 4) (x (-4) 14)
                have b16607 := hb (x (-4) 4)
                have b16608 := hb (x (-4) 4 && x (-4) 14)
                clear * - r16606 b16607 b16608 d16589
                omega
              have d16609 : (x (-5) 5).toNat = 1 := by
                have r16610 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b16611 := hb (x (-5) 5)
                have b16612 := hb (x 0 10)
                have b16613 := hb (x (-1) 1 && x (-1) 11)
                have b16614 := hb (x (-2) 2 && x (-2) 12)
                have b16615 := hb (x (-3) 3 && x (-3) 13)
                have b16616 := hb (x (-4) 4 && x (-4) 14)
                clear * - r16610 b16611 b16612 b16613 b16614 b16615 b16616 g20 d14029 g82 g83 d16605
                omega
              have r16617 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e16618 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
              have e16619 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
              have e16620 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
              have e16621 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
              have e16622 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
              have e16623 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
              have b16624 := hb (x (-7) 7)
              have b16625 := hb (x (-6) 6)
              have b16626 := hb (x (-5) 5)
              have b16627 := hb (x (-4) 4)
              have b16628 := hb (x (-3) 11)
              have b16629 := hb (x (-2) 10)
              have b16630 := hb (x (-1) 9)
              have b16631 := hb (x 0 8)
              linarith only [r16617, e16618, e16619, e16620, e16621, e16622, e16623, b16624, b16625, b16626, b16627, b16628, b16629, b16630, b16631, g18, f16588, g5, g2, d16589, d16609]
          · have f16632 : (x 1 8).toNat = 1 := by rw [h14340]; rfl
            have d16633 : (x (-1) 10).toNat = 0 := by
              have r16634 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e16635 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
              have e16636 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
              have e16637 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
              have e16638 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
              have e16639 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
              have e16640 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
              have b16641 := hb (x (-6) 7)
              have b16642 := hb (x (-5) 6)
              have b16643 := hb (x (-4) 5)
              have b16644 := hb (x (-3) 4)
              have b16645 := hb (x (-2) 11)
              have b16646 := hb (x (-1) 10)
              have b16647 := hb (x 0 9)
              have b16648 := hb (x 1 8)
              clear * - r16634 e16635 e16636 e16637 e16638 e16639 e16640 b16641 b16642 b16643 b16644 b16645 b16646 b16647 b16648 f16632 g19 g6
              omega
            have d16649 : (x (-5) 4 && x (-5) 14).toNat = 1 := by
              have r16650 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b16651 := hb (x (-6) 5)
              have b16652 := hb (x (-1) 10)
              have b16653 := hb (x (-2) 1 && x (-2) 11)
              have b16654 := hb (x (-3) 2 && x (-3) 12)
              have b16655 := hb (x (-4) 3 && x (-4) 13)
              have b16656 := hb (x (-5) 4 && x (-5) 14)
              clear * - r16650 b16651 b16652 b16653 b16654 b16655 b16656 d16633 g79 g80 g81 d14072
              omega
            have d16657 : (x (-5) 14).toNat = 1 := by
              have r16658 := hand2 (x (-5) 4) (x (-5) 14)
              have b16659 := hb (x (-5) 14)
              have b16660 := hb (x (-5) 4 && x (-5) 14)
              clear * - r16658 b16659 b16660 d16649
              omega
            have d16661 : (x (-6) 1).toNat = 0 := by
              have r16662 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b16663 := hb (x (-6) 1)
              have b16664 := hb (x (-5) 14)
              clear * - r16662 b16663 b16664 d16657
              omega
            have d16665 : (x (-6) 1 && x (-6) 14).toNat = 0 := by
              have r16666 := hand1 (x (-6) 1) (x (-6) 14)
              have b16667 := hb (x (-6) 1)
              have b16668 := hb (x (-6) 1 && x (-6) 14)
              clear * - r16666 b16667 b16668 d16661
              omega
            have d16669 : (x (-5) 13).toNat = 1 := by
              have r16670 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b16671 := hb (x (-7) 2)
              have b16672 := hb (x (-5) 13)
              have b16673 := hb (x (-6) 1 && x (-6) 14)
              clear * - r16670 b16671 b16672 b16673 d16665 d14080
              omega
            have d16674 : (x (-5) 1).toNat = 1 := by
              have r16675 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
              have b16676 := hb (x (-5) 1)
              have b16677 := hb (x (-5) 13)
              clear * - r16675 b16676 b16677 d16669
              omega
            have d16678 : (x (-4) 14).toNat = 0 := by
              have r16679 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b16680 := hb (x (-5) 1)
              have b16681 := hb (x (-4) 14)
              clear * - r16679 b16680 b16681 d16674
              omega
            have d16682 : (x (-4) 5 && x (-4) 14).toNat = 0 := by
              have r16683 := hand2 (x (-4) 5) (x (-4) 14)
              have b16684 := hb (x (-4) 14)
              have b16685 := hb (x (-4) 5 && x (-4) 14)
              clear * - r16683 b16684 b16685 d16678
              omega
            have d16686 : (x (-4) 2).toNat = 0 := by
              have r16687 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
              have b16688 := hb (x (-4) 2)
              have b16689 := hb (x (-4) 14)
              clear * - r16687 b16688 b16689 d16678
              omega
            have d16690 : (x (-3) 1 && x (-3) 14).toNat = 1 := by
              have r16691 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b16692 := hb (x (-4) 2)
              have b16693 := hb (x (-2) 13)
              have b16694 := hb (x (-3) 1 && x (-3) 14)
              clear * - r16691 b16692 b16693 b16694 g7 d16686
              omega
            have d16695 : (x (-3) 14).toNat = 1 := by
              have r16696 := hand2 (x (-3) 1) (x (-3) 14)
              have b16697 := hb (x (-3) 14)
              have b16698 := hb (x (-3) 1 && x (-3) 14)
              clear * - r16696 b16697 b16698 d16690
              omega
            have d16699 : (x (-4) 1).toNat = 0 := by
              have r16700 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b16701 := hb (x (-4) 1)
              have b16702 := hb (x (-3) 14)
              clear * - r16700 b16701 b16702 d16695
              omega
            have d16703 : (x (-4) 13).toNat = 0 := by
              have r16704 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
              have b16705 := hb (x (-4) 1)
              have b16706 := hb (x (-4) 13)
              clear * - r16704 b16705 b16706 d16699
              omega
            have d16707 : (x (-4) 5).toNat = 0 := by
              have r16708 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
              have b16709 := hb (x (-4) 5)
              have b16710 := hb (x (-4) 13)
              clear * - r16708 b16709 b16710 d16703
              omega
            have d16711 : (x (-3) 4).toNat = 0 := by
              have r16712 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e16713 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
              have e16714 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
              have e16715 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
              have e16716 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
              have e16717 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
              have e16718 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
              have b16719 := hb (x (-6) 7)
              have b16720 := hb (x (-5) 6)
              have b16721 := hb (x (-4) 5)
              have b16722 := hb (x (-3) 4)
              have b16723 := hb (x (-2) 11)
              have b16724 := hb (x (-1) 10)
              have b16725 := hb (x 0 9)
              have b16726 := hb (x 1 8)
              clear * - r16712 e16713 e16714 e16715 e16716 e16717 e16718 b16719 b16720 b16721 b16722 b16723 b16724 b16725 b16726 f16632 g19 d16633 g6 d16707
              omega
            have d16727 : (x (-3) 4 && x (-3) 13).toNat = 0 := by
              have r16728 := hand1 (x (-3) 4) (x (-3) 13)
              have b16729 := hb (x (-3) 4)
              have b16730 := hb (x (-3) 4 && x (-3) 13)
              clear * - r16728 b16729 b16730 d16711
              omega
            have d16731 : (x (-5) 6).toNat = 1 := by
              have r16732 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b16733 := hb (x (-5) 6)
              have b16734 := hb (x 1 9)
              have b16735 := hb (x 0 1 && x 0 10)
              have b16736 := hb (x (-1) 2 && x (-1) 11)
              have b16737 := hb (x (-2) 3 && x (-2) 12)
              have b16738 := hb (x (-3) 4 && x (-3) 13)
              have b16739 := hb (x (-4) 5 && x (-4) 14)
              clear * - r16732 b16733 b16734 b16735 b16736 b16737 b16738 b16739 g27 g71 d14033 g72 d16727 d16682
              omega
            have r16740 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e16741 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
            have e16742 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
            have e16743 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
            have e16744 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
            have e16745 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
            have e16746 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
            have b16747 := hb (x (-6) 7)
            have b16748 := hb (x (-5) 6)
            have b16749 := hb (x (-4) 5)
            have b16750 := hb (x (-3) 4)
            have b16751 := hb (x (-2) 11)
            have b16752 := hb (x (-1) 10)
            have b16753 := hb (x 0 9)
            have b16754 := hb (x 1 8)
            linarith only [r16740, e16741, e16742, e16743, e16744, e16745, e16746, b16747, b16748, b16749, b16750, b16751, b16752, b16753, b16754, f16632, g19, d16633, g6, d16711, d16707, d16731]
        · have f16755 : (x (-1) 7).toNat = 1 := by rw [h14338]; rfl
          have d16756 : (x 6 8).toNat = 0 := by
            have r16757 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e16758 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
            have e16759 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
            have e16760 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
            have e16761 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
            have e16762 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
            have e16763 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
            have b16764 := hb (x (-1) 7)
            have b16765 := hb (x 0 6)
            have b16766 := hb (x 1 5)
            have b16767 := hb (x 2 4)
            have b16768 := hb (x 3 11)
            have b16769 := hb (x 4 10)
            have b16770 := hb (x 5 9)
            have b16771 := hb (x 6 8)
            clear * - r16757 e16758 e16759 e16760 e16761 e16762 e16763 b16764 b16765 b16766 b16767 b16768 b16769 b16770 b16771 g26 g16 f16755
            omega
          have d16772 : (x 6 1 && x 6 8).toNat = 0 := by
            have r16773 := hand2 (x 6 1) (x 6 8)
            have b16774 := hb (x 6 8)
            have b16775 := hb (x 6 1 && x 6 8)
            clear * - r16773 b16774 b16775 d16756
            omega
          have d16776 : (x 6 3 && x 6 8).toNat = 0 := by
            have r16777 := hand2 (x 6 3) (x 6 8)
            have b16778 := hb (x 6 8)
            have b16779 := hb (x 6 3 && x 6 8)
            clear * - r16777 b16778 b16779 d16756
            omega
          have d16780 : (x 5 9).toNat = 0 := by
            have r16781 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e16782 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
            have e16783 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
            have e16784 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
            have e16785 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
            have e16786 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
            have e16787 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
            have b16788 := hb (x (-1) 7)
            have b16789 := hb (x 0 6)
            have b16790 := hb (x 1 5)
            have b16791 := hb (x 2 4)
            have b16792 := hb (x 3 11)
            have b16793 := hb (x 4 10)
            have b16794 := hb (x 5 9)
            have b16795 := hb (x 6 8)
            clear * - r16781 e16782 e16783 e16784 e16785 e16786 e16787 b16788 b16789 b16790 b16791 b16792 b16793 b16794 b16795 d16756 g26 g16 f16755
            omega
          have d16796 : (x 5 2 && x 5 9).toNat = 0 := by
            have r16797 := hand2 (x 5 2) (x 5 9)
            have b16798 := hb (x 5 9)
            have b16799 := hb (x 5 2 && x 5 9)
            clear * - r16797 b16798 b16799 d16780
            omega
          have d16800 : (x 4 10).toNat = 0 := by
            have r16801 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e16802 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
            have e16803 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
            have e16804 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
            have e16805 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
            have e16806 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
            have e16807 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
            have b16808 := hb (x (-1) 7)
            have b16809 := hb (x 0 6)
            have b16810 := hb (x 1 5)
            have b16811 := hb (x 2 4)
            have b16812 := hb (x 3 11)
            have b16813 := hb (x 4 10)
            have b16814 := hb (x 5 9)
            have b16815 := hb (x 6 8)
            clear * - r16801 e16802 e16803 e16804 e16805 e16806 e16807 b16808 b16809 b16810 b16811 b16812 b16813 b16814 b16815 d16756 d16780 g26 g16 f16755
            omega
          have d16816 : (x 4 3 && x 4 10).toNat = 0 := by
            have r16817 := hand2 (x 4 3) (x 4 10)
            have b16818 := hb (x 4 10)
            have b16819 := hb (x 4 3 && x 4 10)
            clear * - r16817 b16818 b16819 d16800
            omega
          have d16820 : (x 3 11).toNat = 0 := by
            have r16821 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e16822 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
            have e16823 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
            have e16824 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
            have e16825 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
            have e16826 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
            have e16827 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
            have b16828 := hb (x (-1) 7)
            have b16829 := hb (x 0 6)
            have b16830 := hb (x 1 5)
            have b16831 := hb (x 2 4)
            have b16832 := hb (x 3 11)
            have b16833 := hb (x 4 10)
            have b16834 := hb (x 5 9)
            have b16835 := hb (x 6 8)
            clear * - r16821 e16822 e16823 e16824 e16825 e16826 e16827 b16828 b16829 b16830 b16831 b16832 b16833 b16834 b16835 d16756 d16780 d16800 g26 g16 f16755
            omega
          have d16836 : (x 2 4).toNat = 0 := by
            have r16837 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e16838 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
            have e16839 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
            have e16840 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
            have e16841 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
            have e16842 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
            have e16843 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
            have b16844 := hb (x (-1) 7)
            have b16845 := hb (x 0 6)
            have b16846 := hb (x 1 5)
            have b16847 := hb (x 2 4)
            have b16848 := hb (x 3 11)
            have b16849 := hb (x 4 10)
            have b16850 := hb (x 5 9)
            have b16851 := hb (x 6 8)
            clear * - r16837 e16838 e16839 e16840 e16841 e16842 e16843 b16844 b16845 b16846 b16847 b16848 b16849 b16850 b16851 d16756 d16780 d16800 d16820 g26 g16 f16755
            omega
          have d16852 : (x 2 4 && x 2 13).toNat = 0 := by
            have r16853 := hand1 (x 2 4) (x 2 13)
            have b16854 := hb (x 2 4)
            have b16855 := hb (x 2 4 && x 2 13)
            clear * - r16853 b16854 b16855 d16836
            omega
          have d16856 : (x 6 11).toNat = 1 := by
            have r16857 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := by have q := hcov11 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b16858 := hb (x 2 4)
            have b16859 := hb (x 6 11)
            have b16860 := hb (x 5 1 && x 5 12)
            have b16861 := hb (x 4 2 && x 4 13)
            have b16862 := hb (x 3 3 && x 3 14)
            clear * - r16857 b16858 b16859 b16860 b16861 b16862 d14200 d14232 g93 d16836
            omega
          have d16863 : (x 6 3).toNat = 1 := by
            have r16864 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
            have b16865 := hb (x 6 3)
            have b16866 := hb (x 6 11)
            clear * - r16864 b16865 b16866 d16856
            omega
          have d16867 : (x 9 12).toNat = 0 := by
            have r16868 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e16869 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
            have e16870 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
            have b16871 := hb (x 6 3)
            have b16872 := hb (x 7 2)
            have b16873 := hb (x 8 13)
            have b16874 := hb (x 9 12)
            clear * - r16868 e16869 e16870 b16871 b16872 b16873 b16874 d16863
            omega
          have d16875 : (x 8 13).toNat = 0 := by
            have r16876 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e16877 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
            have e16878 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
            have b16879 := hb (x 6 3)
            have b16880 := hb (x 7 2)
            have b16881 := hb (x 8 13)
            have b16882 := hb (x 9 12)
            clear * - r16876 e16877 e16878 b16879 b16880 b16881 b16882 d16867 d16863
            omega
          have d16883 : (x 7 2).toNat = 0 := by
            have r16884 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e16885 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
            have e16886 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
            have b16887 := hb (x 6 3)
            have b16888 := hb (x 7 2)
            have b16889 := hb (x 8 13)
            have b16890 := hb (x 9 12)
            clear * - r16884 e16885 e16886 b16887 b16888 b16889 b16890 d16867 d16875 d16863
            omega
          have d16891 : (x 7 2 && x 7 7).toNat = 0 := by
            have r16892 := hand1 (x 7 2) (x 7 7)
            have b16893 := hb (x 7 2)
            have b16894 := hb (x 7 2 && x 7 7)
            clear * - r16892 b16893 b16894 d16883
            omega
          have d16895 : (x 7 10).toNat = 0 := by
            have r16896 : (x 7 10).toNat ≤ (x 7 2).toNat := himp _ _ (hp10 7)
            have b16897 := hb (x 7 2)
            have b16898 := hb (x 7 10)
            clear * - r16896 b16897 b16898 d16883
            omega
          have d16899 : (x 9 8).toNat = 0 := by
            have r16900 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e16901 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
            have e16902 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
            have e16903 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
            have e16904 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
            have e16905 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
            have e16906 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
            have b16907 := hb (x 2 7)
            have b16908 := hb (x 3 6)
            have b16909 := hb (x 4 5)
            have b16910 := hb (x 5 4)
            have b16911 := hb (x 6 11)
            have b16912 := hb (x 7 10)
            have b16913 := hb (x 8 9)
            have b16914 := hb (x 9 8)
            clear * - r16900 e16901 e16902 e16903 e16904 e16905 e16906 b16907 b16908 b16909 b16910 b16911 b16912 b16913 b16914 d16895 d16856 d14208 d14240 g35
            omega
          have d16915 : (x 8 9).toNat = 0 := by
            have r16916 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e16917 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
            have e16918 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
            have e16919 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
            have e16920 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
            have e16921 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
            have e16922 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
            have b16923 := hb (x 2 7)
            have b16924 := hb (x 3 6)
            have b16925 := hb (x 4 5)
            have b16926 := hb (x 5 4)
            have b16927 := hb (x 6 11)
            have b16928 := hb (x 7 10)
            have b16929 := hb (x 8 9)
            have b16930 := hb (x 9 8)
            clear * - r16916 e16917 e16918 e16919 e16920 e16921 e16922 b16923 b16924 b16925 b16926 b16927 b16928 b16929 b16930 d16899 d16895 d16856 d14208 d14240 g35
            omega
          have d16931 : (x 2 7).toNat = 0 := by
            have r16932 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e16933 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
            have e16934 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
            have e16935 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
            have e16936 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
            have e16937 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
            have e16938 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
            have b16939 := hb (x 2 7)
            have b16940 := hb (x 3 6)
            have b16941 := hb (x 4 5)
            have b16942 := hb (x 5 4)
            have b16943 := hb (x 6 11)
            have b16944 := hb (x 7 10)
            have b16945 := hb (x 8 9)
            have b16946 := hb (x 9 8)
            clear * - r16932 e16933 e16934 e16935 e16936 e16937 e16938 b16939 b16940 b16941 b16942 b16943 b16944 b16945 b16946 d16899 d16915 d16895 d16856 d14208 d14240 g35
            omega
          have d16947 : (x 2 7 && x 2 12).toNat = 0 := by
            have r16948 := hand1 (x 2 7) (x 2 12)
            have b16949 := hb (x 2 7)
            have b16950 := hb (x 2 7 && x 2 12)
            clear * - r16948 b16949 b16950 d16931
            omega
          have r16951 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e16952 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e16953 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e16954 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e16955 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e16956 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e16957 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have r16958 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e16959 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e16960 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e16961 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e16962 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e16963 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e16964 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have r16965 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e16966 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
          have e16967 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
          have e16968 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
          have e16969 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
          have e16970 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
          have e16971 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
          have r16972 : 1 ≤ (x 9 5).toNat + (x 8 1 && x 8 6).toNat + (x 7 2 && x 7 7).toNat + (x 6 3 && x 6 8).toNat + (x 5 4 && x 5 9).toNat + (x 4 5 && x 4 10).toNat + (x 3 6 && x 3 11).toNat + (x 2 7 && x 2 12).toNat + (x 1 8 && x 1 13).toNat + (x 0 9 && x 0 14).toNat + (x (-1) 10).toNat := by have q := hcov5 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r16973 : 1 ≤ (x 7 7).toNat + (x 6 1 && x 6 8).toNat + (x 5 2 && x 5 9).toNat + (x 4 3 && x 4 10).toNat + (x 3 4 && x 3 11).toNat + (x 2 5 && x 2 12).toNat + (x 1 6 && x 1 13).toNat + (x 0 7 && x 0 14).toNat + (x (-1) 8).toNat := by have q := hcov7 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r16974 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r16975 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r16976 := hand2 (x 8 1) (x 8 6)
          have r16977 := hand1 (x 2 5) (x 2 12)
          have r16978 := hand1 (x (-3) 4) (x (-3) 13)
          have r16979 := hand1 (x (-4) 5) (x (-4) 14)
          have r16980 := hand2 (x 5 1) (x 5 10)
          have r16981 := hand2 (x 4 2) (x 4 11)
          linarith only [r16951, e16952, e16953, e16954, e16955, e16956, e16957, r16958, e16959, e16960, e16961, e16962, e16963, e16964, r16965, e16966, e16967, e16968, e16969, e16970, e16971, r16972, r16973, r16974, r16975, r16976, r16977, r16978, r16979, r16980, r16981, g6, d14120, g16, g17, g19, f14337, g27, g34, d16891, d16776, d14220, d14252, g51, d16947, g52, g53, d16772, d16796, d16816, g63, g64, g65, g71, d14033, g72, g76, d16852, g77]
      · have f17035 : (x 1 6).toNat = 1 := by rw [h14336]; rfl
        have d17036 : (x 7 8).toNat = 0 := by
          have r17037 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e17038 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e17039 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e17040 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e17041 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e17042 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e17043 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have b17044 := hb (x 0 7)
          have b17045 := hb (x 1 6)
          have b17046 := hb (x 2 5)
          have b17047 := hb (x 3 4)
          have b17048 := hb (x 4 11)
          have b17049 := hb (x 5 10)
          have b17050 := hb (x 6 9)
          have b17051 := hb (x 7 8)
          clear * - r17037 e17038 e17039 e17040 e17041 e17042 e17043 b17044 b17045 b17046 b17047 b17048 b17049 b17050 b17051 g34 f17035 g17
          omega
        have d17052 : (x 7 2 && x 7 8).toNat = 0 := by
          have r17053 := hand2 (x 7 2) (x 7 8)
          have b17054 := hb (x 7 8)
          have b17055 := hb (x 7 2 && x 7 8)
          clear * - r17053 b17054 b17055 d17036
          omega
        have d17056 : (x 6 9).toNat = 0 := by
          have r17057 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e17058 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e17059 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e17060 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e17061 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e17062 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e17063 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have b17064 := hb (x 0 7)
          have b17065 := hb (x 1 6)
          have b17066 := hb (x 2 5)
          have b17067 := hb (x 3 4)
          have b17068 := hb (x 4 11)
          have b17069 := hb (x 5 10)
          have b17070 := hb (x 6 9)
          have b17071 := hb (x 7 8)
          clear * - r17057 e17058 e17059 e17060 e17061 e17062 e17063 b17064 b17065 b17066 b17067 b17068 b17069 b17070 b17071 d17036 g34 f17035 g17
          omega
        have d17072 : (x 6 3 && x 6 9).toNat = 0 := by
          have r17073 := hand2 (x 6 3) (x 6 9)
          have b17074 := hb (x 6 9)
          have b17075 := hb (x 6 3 && x 6 9)
          clear * - r17073 b17074 b17075 d17056
          omega
        have d17076 : (x 5 10).toNat = 0 := by
          have r17077 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e17078 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e17079 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e17080 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e17081 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e17082 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e17083 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have b17084 := hb (x 0 7)
          have b17085 := hb (x 1 6)
          have b17086 := hb (x 2 5)
          have b17087 := hb (x 3 4)
          have b17088 := hb (x 4 11)
          have b17089 := hb (x 5 10)
          have b17090 := hb (x 6 9)
          have b17091 := hb (x 7 8)
          clear * - r17077 e17078 e17079 e17080 e17081 e17082 e17083 b17084 b17085 b17086 b17087 b17088 b17089 b17090 b17091 d17036 d17056 g34 f17035 g17
          omega
        have d17092 : (x 4 11).toNat = 0 := by
          have r17093 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e17094 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e17095 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e17096 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e17097 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e17098 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e17099 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have b17100 := hb (x 0 7)
          have b17101 := hb (x 1 6)
          have b17102 := hb (x 2 5)
          have b17103 := hb (x 3 4)
          have b17104 := hb (x 4 11)
          have b17105 := hb (x 5 10)
          have b17106 := hb (x 6 9)
          have b17107 := hb (x 7 8)
          clear * - r17093 e17094 e17095 e17096 e17097 e17098 e17099 b17100 b17101 b17102 b17103 b17104 b17105 b17106 b17107 d17036 d17056 d17076 g34 f17035 g17
          omega
        have d17108 : (x 2 5).toNat = 0 := by
          have r17109 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e17110 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e17111 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e17112 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e17113 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e17114 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e17115 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have b17116 := hb (x 0 7)
          have b17117 := hb (x 1 6)
          have b17118 := hb (x 2 5)
          have b17119 := hb (x 3 4)
          have b17120 := hb (x 4 11)
          have b17121 := hb (x 5 10)
          have b17122 := hb (x 6 9)
          have b17123 := hb (x 7 8)
          clear * - r17109 e17110 e17111 e17112 e17113 e17114 e17115 b17116 b17117 b17118 b17119 b17120 b17121 b17122 b17123 d17036 d17056 d17076 d17092 g34 f17035 g17
          omega
        have d17124 : (x 2 5 && x 2 11).toNat = 0 := by
          have r17125 := hand1 (x 2 5) (x 2 11)
          have b17126 := hb (x 2 5)
          have b17127 := hb (x 2 5 && x 2 11)
          clear * - r17125 b17126 b17127 d17108
          omega
        have r17128 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r17129 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e17130 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
        have e17131 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
        have e17132 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
        have e17133 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
        have e17134 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
        have e17135 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
        have r17136 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e17137 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
        have e17138 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
        have e17139 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
        have e17140 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
        have e17141 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
        have e17142 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
        have r17143 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e17144 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
        have e17145 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
        have e17146 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
        have e17147 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
        have e17148 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
        have e17149 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
        have r17150 : 1 ≤ (x 7 6).toNat + (x 6 1 && x 6 7).toNat + (x 5 2 && x 5 8).toNat + (x 4 3 && x 4 9).toNat + (x 3 4 && x 3 10).toNat + (x 2 5 && x 2 11).toNat + (x 1 6 && x 1 12).toNat + (x 0 7 && x 0 13).toNat + (x (-1) 8 && x (-1) 14).toNat + (x (-2) 9).toNat := by have q := hcov6 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r17151 : 1 ≤ (x 9 6).toNat + (x 8 1 && x 8 7).toNat + (x 7 2 && x 7 8).toNat + (x 6 3 && x 6 9).toNat + (x 5 4 && x 5 10).toNat + (x 4 5 && x 4 11).toNat + (x 3 6 && x 3 12).toNat + (x 2 7 && x 2 13).toNat + (x 1 8 && x 1 14).toNat + (x 0 9).toNat := by have q := hcov6 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r17152 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r17153 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r17154 : 1 ≤ (x 13 10).toNat + (x 12 1 && x 12 11).toNat + (x 11 2 && x 11 12).toNat + (x 10 3 && x 10 13).toNat + (x 9 4 && x 9 14).toNat + (x 8 5).toNat := by have q := hcov10 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r17155 := hand2 (x 6 1) (x 6 7)
        have r17156 := hand2 (x 8 1) (x 8 7)
        have r17157 := hand1 (x 2 7) (x 2 13)
        have r17158 := hand1 (x 1 8) (x 1 14)
        have r17159 := hand1 (x (-3) 4) (x (-3) 13)
        have r17160 := hand1 (x (-4) 5) (x (-4) 14)
        have r17161 := hand2 (x 6 1) (x 6 11)
        have r17162 := hand2 (x 12 1) (x 12 11)
        have r17163 := hand1 (x 11 2) (x 11 12)
        have r17164 := hand1 (x 10 3) (x 10 13)
        have r17165 := hand1 (x 9 4) (x 9 14)
        linarith only [r17128, r17129, e17130, e17131, e17132, e17133, e17134, e17135, r17136, e17137, e17138, e17139, e17140, e17141, e17142, r17143, e17144, e17145, e17146, e17147, e17148, e17149, r17150, r17151, r17152, r17153, r17154, r17155, r17156, r17157, r17158, r17159, r17160, r17161, r17162, r17163, r17164, r17165, g4, g6, g12, g19, g23, g27, g29, d17108, d14184, g35, g36, d14240, d14280, d14208, d14256, d14272, d14296, g56, d17124, g57, g58, d14136, d17052, d17072, d14216, d14248, g59, g71, d14033, g72, d14204, d14236, g88]
    · have f17236 : (x (-1) 4).toNat = 1 := by rw [h14170]; rfl
      have d17237 : (x 3 8).toNat = 0 := by
        have r17238 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e17239 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
        have e17240 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
        have e17241 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
        have e17242 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
        have e17243 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
        have e17244 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
        have b17245 := hb (x (-4) 7)
        have b17246 := hb (x (-3) 6)
        have b17247 := hb (x (-2) 5)
        have b17248 := hb (x (-1) 4)
        have b17249 := hb (x 0 11)
        have b17250 := hb (x 1 10)
        have b17251 := hb (x 2 9)
        have b17252 := hb (x 3 8)
        clear * - r17238 e17239 e17240 e17241 e17242 e17243 e17244 b17245 b17246 b17247 b17248 b17249 b17250 b17251 b17252 g28 g21 f17236 g3
        omega
      have d17253 : (x 2 9).toNat = 0 := by
        have r17254 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e17255 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
        have e17256 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
        have e17257 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
        have e17258 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
        have e17259 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
        have e17260 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
        have b17261 := hb (x (-4) 7)
        have b17262 := hb (x (-3) 6)
        have b17263 := hb (x (-2) 5)
        have b17264 := hb (x (-1) 4)
        have b17265 := hb (x 0 11)
        have b17266 := hb (x 1 10)
        have b17267 := hb (x 2 9)
        have b17268 := hb (x 3 8)
        clear * - r17254 e17255 e17256 e17257 e17258 e17259 e17260 b17261 b17262 b17263 b17264 b17265 b17266 b17267 b17268 d17237 g28 g21 f17236 g3
        omega
      have d17269 : (x (-3) 6).toNat = 0 := by
        have r17270 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e17271 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
        have e17272 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
        have e17273 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
        have e17274 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
        have e17275 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
        have e17276 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
        have b17277 := hb (x (-4) 7)
        have b17278 := hb (x (-3) 6)
        have b17279 := hb (x (-2) 5)
        have b17280 := hb (x (-1) 4)
        have b17281 := hb (x 0 11)
        have b17282 := hb (x 1 10)
        have b17283 := hb (x 2 9)
        have b17284 := hb (x 3 8)
        clear * - r17270 e17271 e17272 e17273 e17274 e17275 e17276 b17277 b17278 b17279 b17280 b17281 b17282 b17283 b17284 d17237 d17253 g28 g21 f17236 g3
        omega
      have d17285 : (x (-3) 6 && x (-3) 13).toNat = 0 := by
        have r17286 := hand1 (x (-3) 6) (x (-3) 13)
        have b17287 := hb (x (-3) 6)
        have b17288 := hb (x (-3) 6 && x (-3) 13)
        clear * - r17286 b17287 b17288 d17269
        omega
      have d17289 : (x (-4) 7).toNat = 0 := by
        have r17290 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e17291 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
        have e17292 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
        have e17293 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
        have e17294 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
        have e17295 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
        have e17296 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
        have b17297 := hb (x (-4) 7)
        have b17298 := hb (x (-3) 6)
        have b17299 := hb (x (-2) 5)
        have b17300 := hb (x (-1) 4)
        have b17301 := hb (x 0 11)
        have b17302 := hb (x 1 10)
        have b17303 := hb (x 2 9)
        have b17304 := hb (x 3 8)
        clear * - r17290 e17291 e17292 e17293 e17294 e17295 e17296 b17297 b17298 b17299 b17300 b17301 b17302 b17303 b17304 d17237 d17253 g28 g21 f17236 g3 d17269
        omega
      have d17305 : (x (-4) 7 && x (-4) 14).toNat = 0 := by
        have r17306 := hand1 (x (-4) 7) (x (-4) 14)
        have b17307 := hb (x (-4) 7)
        have b17308 := hb (x (-4) 7 && x (-4) 14)
        clear * - r17306 b17307 b17308 d17289
        omega
      have r17309 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r17310 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17311 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
      have e17312 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
      have e17313 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
      have e17314 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
      have e17315 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
      have e17316 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
      have r17317 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17318 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
      have e17319 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
      have e17320 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
      have e17321 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
      have e17322 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
      have e17323 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
      have r17324 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17325 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e17326 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e17327 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e17328 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e17329 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e17330 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have r17331 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17332 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
      have e17333 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
      have e17334 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
      have e17335 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
      have e17336 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
      have e17337 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
      have r17338 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17339 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
      have e17340 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
      have r17341 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17342 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e17343 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have r17344 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17345 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e17346 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have r17347 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17348 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
      have e17349 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
      have r17350 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r17351 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r17352 : 1 ≤ (x 6 4).toNat + (x 5 1 && x 5 5).toNat + (x 4 2 && x 4 6).toNat + (x 3 3 && x 3 7).toNat + (x 2 4 && x 2 8).toNat + (x 1 5 && x 1 9).toNat + (x 0 6 && x 0 10).toNat + (x (-1) 7 && x (-1) 11).toNat + (x (-2) 8 && x (-2) 12).toNat + (x (-3) 9 && x (-3) 13).toNat + (x (-4) 10 && x (-4) 14).toNat + (x (-5) 11).toNat := by have q := hcov4 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17353 : (x 5 1 && x 5 5).toNat = (x 5 5).toNat := handr _ _ (fun h => hp13 5 (hp5 5 (h)))
      have e17354 : (x (-4) 10 && x (-4) 14).toNat = (x (-4) 10).toNat := handl _ _ (fun h => hp2 (-4) (hp10 (-4) (h)))
      have r17355 : 1 ≤ (x 3 7).toNat + (x 2 1 && x 2 8).toNat + (x 1 2 && x 1 9).toNat + (x 0 3 && x 0 10).toNat + (x (-1) 4 && x (-1) 11).toNat + (x (-2) 5 && x (-2) 12).toNat + (x (-3) 6 && x (-3) 13).toNat + (x (-4) 7 && x (-4) 14).toNat + (x (-5) 8).toNat := by have q := hcov7 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r17356 : 1 ≤ (x (-2) 9).toNat + (x (-3) 1 && x (-3) 10).toNat + (x (-4) 2 && x (-4) 11).toNat + (x (-5) 3 && x (-5) 12).toNat + (x (-6) 4 && x (-6) 13).toNat + (x (-7) 5 && x (-7) 14).toNat + (x (-8) 6).toNat := by have q := hcov9 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r17357 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r17358 : 1 ≤ (x 2 9).toNat + (x 1 1 && x 1 10).toNat + (x 0 2 && x 0 11).toNat + (x (-1) 3 && x (-1) 12).toNat + (x (-2) 4 && x (-2) 13).toNat + (x (-3) 5 && x (-3) 14).toNat + (x (-4) 6).toNat := by have q := hcov9 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r17359 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r17360 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r17361 : 1 ≤ (x (-5) 11).toNat + (x (-6) 1 && x (-6) 12).toNat + (x (-7) 2 && x (-7) 13).toNat + (x (-8) 3 && x (-8) 14).toNat + (x (-9) 4).toNat := by have q := hcov11 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r17362 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r17363 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r17364 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r17365 : (x (-9) 4).toNat ≤ (x (-9) 12).toNat := himp _ _ (hp4 (-9))
      have r17366 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
      have r17367 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
      have r17368 : (x (-4) 6).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp6 (-4))
      have r17369 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
      have r17370 := hand2 (x 4 2) (x 4 6)
      have r17371 := hand1 (x 3 3) (x 3 7)
      have r17372 := hand2 (x 2 4) (x 2 8)
      have r17373 := hand1 (x (-2) 8) (x (-2) 12)
      have r17374 := hand1 (x (-3) 9) (x (-3) 13)
      have r17375 := hand2 (x 2 1) (x 2 8)
      have r17376 := hand1 (x (-5) 3) (x (-5) 12)
      have r17377 := hand1 (x (-7) 5) (x (-7) 14)
      have r17378 := hand2 (x (-5) 4) (x (-5) 13)
      have r17379 := hand1 (x (-3) 5) (x (-3) 14)
      have r17380 := hand1 (x (-4) 2) (x (-4) 12)
      have r17381 := hand1 (x (-5) 3) (x (-5) 13)
      have r17382 := hand1 (x (-6) 4) (x (-6) 14)
      have r17383 := hand1 (x (-4) 4) (x (-4) 14)
      have r17384 := hand2 (x (-6) 1) (x (-6) 12)
      have r17385 := hand2 (x 6 1) (x 6 12)
      have r17386 := hand1 (x 5 2) (x 5 13)
      have r17387 := hand1 (x 4 3) (x 4 14)
      have r17388 := hand1 (x 4 1) (x 4 14)
      have r17389 := hand2 (x 5 1) (x 5 14)
      linarith only [r17309, r17310, e17311, e17312, e17313, e17314, e17315, e17316, r17317, e17318, e17319, e17320, e17321, e17322, e17323, r17324, e17325, e17326, e17327, e17328, e17329, e17330, r17331, e17332, e17333, e17334, e17335, e17336, e17337, r17338, e17339, e17340, r17341, e17342, e17343, r17344, e17345, e17346, r17347, e17348, e17349, r17350, r17351, r17352, e17353, e17354, r17355, r17356, r17357, r17358, r17359, r17360, r17361, r17362, r17363, r17364, r17365, r17366, r17367, r17368, r17369, r17370, r17371, r17372, r17373, r17374, r17375, r17376, r17377, r17378, r17379, r17380, r17381, r17382, r17383, r17384, r17385, r17386, r17387, r17388, r17389, d14112, d14148, d14092, d17289, d17269, g2, g3, g4, g5, f17236, d14025, g13, g18, g20, g24, g27, g31, d17253, g33, g34, g43, g44, d14041, g60, g61, d14037, g62, d17285, d17305, g66, g67, d14064, g68, g69, g70, d14076, g73, g74, d14021, g75, g78, d14029, g82, g83, d14088, d14108]
  · exact cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000100_p1 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83 g84 g85 g86 g87 g88 g89 g90 g91 g92 g93 g94 h14164

theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000100 (x : ℤ → Fin 16 → Bool)
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
    : False := cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000100_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83 g84 g85 g86 g87 g88 g89 g90 g91 g92 g93 g94
