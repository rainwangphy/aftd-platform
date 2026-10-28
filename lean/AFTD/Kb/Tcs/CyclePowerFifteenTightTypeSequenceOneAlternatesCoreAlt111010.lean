import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt111010

Topic: combinatorics   Node: c6cf8f1bd3a0

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_alternates_core: under the layer-free tight-cover constraints for k = 15 and 52 fixed bits of the class-type sequence near position 0, the constraints are contradictory. Its module also proves the sibling branches cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt1101, cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt11100.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt1101 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 4).toNat = 0)
    (g1 : (x 0 12).toNat = 1)
    (g2 : (x 1 1).toNat = 1)
    (g3 : (x 1 2).toNat = 0)
    (g4 : (x 1 10).toNat = 0)
    (g5 : (x 1 11).toNat = 0)
    (g6 : (x 2 10).toNat = 0)
    (g7 : (x 4 2).toNat = 0)
    (g8 : (x 4 4).toNat = 0)
    (g9 : (x 4 10).toNat = 0)
    (g10 : (x 1 1 && x 1 2).toNat = 0)
    (g11 : (x 4 7 && x 4 10).toNat = 0)
    (g12 : (x 1 10 && x 1 13).toNat = 0)
    (g13 : (x 4 2 && x 4 8).toNat = 0)
    (g14 : (x 2 4 && x 2 10).toNat = 0)
    (g15 : (x 1 5 && x 1 11).toNat = 0)
    (g16 : (x 1 1 && x 1 10).toNat = 0)
    (g17 : (x 2 2 && x 2 12).toNat = 0)
    (g18 : (x 1 3 && x 1 13).toNat = 0)
    (g19 : (x 0 4 && x 0 14).toNat = 0)
    (g20 : (x 2 2 && x 2 13).toNat = 0)
    (g21 : (x 1 3 && x 1 14).toNat = 0)
    (g22 : (x 4 3 && x 4 14).toNat = 0)
    (g23 : (x 1 1 && x 1 14).toNat = 0)
    (g24 : (x 4 1 && x 4 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d31999 : (x (-1) 13).toNat = 0 := by
    have r32000 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e32001 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e32002 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b32003 := hb (x (-3) 3)
    have b32004 := hb (x (-2) 2)
    have b32005 := hb (x (-1) 13)
    have b32006 := hb (x 0 12)
    clear * - r32000 e32001 e32002 b32003 b32004 b32005 b32006 g1
    omega
  have d32007 : (x (-1) 7 && x (-1) 13).toNat = 0 := by
    have r32008 := hand2 (x (-1) 7) (x (-1) 13)
    have b32009 := hb (x (-1) 13)
    have b32010 := hb (x (-1) 7 && x (-1) 13)
    clear * - r32008 b32009 b32010 d31999
    omega
  have d32011 : (x (-1) 5).toNat = 0 := by
    have r32012 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
    have b32013 := hb (x (-1) 5)
    have b32014 := hb (x (-1) 13)
    clear * - r32012 b32013 b32014 d31999
    omega
  have d32015 : (x (-2) 2).toNat = 0 := by
    have r32016 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e32017 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e32018 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b32019 := hb (x (-3) 3)
    have b32020 := hb (x (-2) 2)
    have b32021 := hb (x (-1) 13)
    have b32022 := hb (x 0 12)
    clear * - r32016 e32017 e32018 b32019 b32020 b32021 b32022 g1 d31999
    omega
  have d32023 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
    have r32024 := hand1 (x (-2) 2) (x (-2) 13)
    have b32025 := hb (x (-2) 2)
    have b32026 := hb (x (-2) 2 && x (-2) 13)
    clear * - r32024 b32025 b32026 d32015
    omega
  have d32027 : (x (-2) 2 && x (-2) 8).toNat = 0 := by
    have r32028 := hand1 (x (-2) 2) (x (-2) 8)
    have b32029 := hb (x (-2) 2)
    have b32030 := hb (x (-2) 2 && x (-2) 8)
    clear * - r32028 b32029 b32030 d32015
    omega
  have d32031 : (x (-2) 10).toNat = 0 := by
    have r32032 : (x (-2) 10).toNat ≤ (x (-2) 2).toNat := himp _ _ (hp10 (-2))
    have b32033 := hb (x (-2) 2)
    have b32034 := hb (x (-2) 10)
    clear * - r32032 b32033 b32034 d32015
    omega
  have d32035 : (x (-2) 1 && x (-2) 10).toNat = 0 := by
    have r32036 := hand2 (x (-2) 1) (x (-2) 10)
    have b32037 := hb (x (-2) 10)
    have b32038 := hb (x (-2) 1 && x (-2) 10)
    clear * - r32036 b32037 b32038 d32031
    omega
  have d32039 : (x (-3) 3).toNat = 0 := by
    have r32040 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e32041 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e32042 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b32043 := hb (x (-3) 3)
    have b32044 := hb (x (-2) 2)
    have b32045 := hb (x (-1) 13)
    have b32046 := hb (x 0 12)
    clear * - r32040 e32041 e32042 b32043 b32044 b32045 b32046 g1 d31999 d32015
    omega
  have d32047 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
    have r32048 := hand1 (x (-3) 3) (x (-3) 14)
    have b32049 := hb (x (-3) 3)
    have b32050 := hb (x (-3) 3 && x (-3) 14)
    clear * - r32048 b32049 b32050 d32039
    omega
  have d32051 : (x (-3) 3 && x (-3) 9).toNat = 0 := by
    have r32052 := hand1 (x (-3) 3) (x (-3) 9)
    have b32053 := hb (x (-3) 3)
    have b32054 := hb (x (-3) 3 && x (-3) 9)
    clear * - r32052 b32053 b32054 d32039
    omega
  have d32055 : (x (-3) 11).toNat = 0 := by
    have r32056 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
    have b32057 := hb (x (-3) 3)
    have b32058 := hb (x (-3) 11)
    clear * - r32056 b32057 b32058 d32039
    omega
  have d32059 : (x (-3) 1 && x (-3) 11).toNat = 0 := by
    have r32060 := hand2 (x (-3) 1) (x (-3) 11)
    have b32061 := hb (x (-3) 11)
    have b32062 := hb (x (-3) 1 && x (-3) 11)
    clear * - r32060 b32061 b32062 d32055
    omega
  have d32063 : (x (-3) 2 && x (-3) 11).toNat = 0 := by
    have r32064 := hand2 (x (-3) 2) (x (-3) 11)
    have b32065 := hb (x (-3) 11)
    have b32066 := hb (x (-3) 2 && x (-3) 11)
    clear * - r32064 b32065 b32066 d32055
    omega
  have d32067 : (x 3 1 && x 3 11).toNat = 1 := by
    have r32068 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b32069 := hb (x (-1) 5)
    have b32070 := hb (x 4 10)
    have b32071 := hb (x 3 1 && x 3 11)
    have b32072 := hb (x 2 2 && x 2 12)
    have b32073 := hb (x 1 3 && x 1 13)
    have b32074 := hb (x 0 4 && x 0 14)
    clear * - r32068 b32069 b32070 b32071 b32072 b32073 b32074 g9 g17 g18 g19 d32011
    omega
  have d32075 : (x 3 11).toNat = 1 := by
    have r32076 := hand2 (x 3 1) (x 3 11)
    have b32077 := hb (x 3 11)
    have b32078 := hb (x 3 1 && x 3 11)
    clear * - r32076 b32077 b32078 d32067
    omega
  have d32079 : (x 3 3).toNat = 1 := by
    have r32080 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
    have b32081 := hb (x 3 3)
    have b32082 := hb (x 3 11)
    clear * - r32080 b32081 b32082 d32075
    omega
  have d32083 : (x 6 12).toNat = 0 := by
    have r32084 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e32085 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e32086 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b32087 := hb (x 3 3)
    have b32088 := hb (x 4 2)
    have b32089 := hb (x 5 13)
    have b32090 := hb (x 6 12)
    clear * - r32084 e32085 e32086 b32087 b32088 b32089 b32090 g7 d32079
    omega
  have d32091 : (x 6 1 && x 6 12).toNat = 0 := by
    have r32092 := hand2 (x 6 1) (x 6 12)
    have b32093 := hb (x 6 12)
    have b32094 := hb (x 6 1 && x 6 12)
    clear * - r32092 b32093 b32094 d32083
    omega
  have d32095 : (x 5 13).toNat = 0 := by
    have r32096 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e32097 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e32098 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b32099 := hb (x 3 3)
    have b32100 := hb (x 4 2)
    have b32101 := hb (x 5 13)
    have b32102 := hb (x 6 12)
    clear * - r32096 e32097 e32098 b32099 b32100 b32101 b32102 d32083 g7 d32079
    omega
  have d32103 : (x 5 2 && x 5 13).toNat = 0 := by
    have r32104 := hand2 (x 5 2) (x 5 13)
    have b32105 := hb (x 5 13)
    have b32106 := hb (x 5 2 && x 5 13)
    clear * - r32104 b32105 b32106 d32095
    omega
  have d32107 : (x 3 2).toNat = 1 := by
    have r32108 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b32109 := hb (x 3 2)
    have b32110 := hb (x 5 13)
    have b32111 := hb (x 4 1 && x 4 14)
    clear * - r32108 b32109 b32110 b32111 d32095 g24
    omega
  have d32112 : (x 3 14).toNat = 1 := by
    have r32113 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
    have b32114 := hb (x 3 2)
    have b32115 := hb (x 3 14)
    clear * - r32113 b32114 b32115 d32107
    omega
  have d32116 : (x 2 1).toNat = 0 := by
    have r32117 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b32118 := hb (x 2 1)
    have b32119 := hb (x 3 14)
    clear * - r32117 b32118 b32119 d32112
    omega
  have d32120 : (x 2 13).toNat = 0 := by
    have r32121 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
    have b32122 := hb (x 2 1)
    have b32123 := hb (x 2 13)
    clear * - r32121 b32122 b32123 d32116
    omega
  have d32124 : (x 0 2).toNat = 1 := by
    have r32125 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b32126 := hb (x 0 2)
    have b32127 := hb (x 2 13)
    have b32128 := hb (x 1 1 && x 1 14)
    clear * - r32125 b32126 b32127 b32128 d32120 g23
    omega
  have d32129 : (x 0 14).toNat = 1 := by
    have r32130 : (x 0 2).toNat ≤ (x 0 14).toNat := himp _ _ (hp2 0)
    have b32131 := hb (x 0 2)
    have b32132 := hb (x 0 14)
    clear * - r32130 b32131 b32132 d32124
    omega
  have d32133 : (x (-1) 1).toNat = 0 := by
    have r32134 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b32135 := hb (x (-1) 1)
    have b32136 := hb (x 0 14)
    clear * - r32134 b32135 b32136 d32129
    omega
  have d32137 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
    have r32138 := hand1 (x (-1) 1) (x (-1) 12)
    have b32139 := hb (x (-1) 1)
    have b32140 := hb (x (-1) 1 && x (-1) 12)
    clear * - r32138 b32139 b32140 d32133
    omega
  have d32141 : (x (-1) 1 && x (-1) 7).toNat = 0 := by
    have r32142 := hand1 (x (-1) 1) (x (-1) 7)
    have b32143 := hb (x (-1) 1)
    have b32144 := hb (x (-1) 1 && x (-1) 7)
    clear * - r32142 b32143 b32144 d32133
    omega
  have d32145 : (x (-1) 9).toNat = 0 := by
    have r32146 : (x (-1) 9).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp9 (-1))
    have b32147 := hb (x (-1) 1)
    have b32148 := hb (x (-1) 9)
    clear * - r32146 b32147 b32148 d32133
    omega
  have d32149 : (x 2 12).toNat = 0 := by
    have r32150 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e32151 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e32152 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b32153 := hb (x (-1) 3)
    have b32154 := hb (x 0 2)
    have b32155 := hb (x 1 13)
    have b32156 := hb (x 2 12)
    clear * - r32150 e32151 e32152 b32153 b32154 b32155 b32156 d32124
    omega
  have d32157 : (x 2 9 && x 2 12).toNat = 0 := by
    have r32158 := hand2 (x 2 9) (x 2 12)
    have b32159 := hb (x 2 12)
    have b32160 := hb (x 2 9 && x 2 12)
    clear * - r32158 b32159 b32160 d32149
    omega
  have d32161 : (x 2 4).toNat = 0 := by
    have r32162 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
    have b32163 := hb (x 2 4)
    have b32164 := hb (x 2 12)
    clear * - r32162 b32163 b32164 d32149
    omega
  have d32165 : (x 1 13).toNat = 0 := by
    have r32166 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e32167 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e32168 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b32169 := hb (x (-1) 3)
    have b32170 := hb (x 0 2)
    have b32171 := hb (x 1 13)
    have b32172 := hb (x 2 12)
    clear * - r32166 e32167 e32168 b32169 b32170 b32171 b32172 d32149 d32124
    omega
  have d32173 : (x 1 5).toNat = 0 := by
    have r32174 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
    have b32175 := hb (x 1 5)
    have b32176 := hb (x 1 13)
    clear * - r32174 b32175 b32176 d32165
    omega
  have d32177 : (x (-1) 3).toNat = 0 := by
    have r32178 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e32179 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e32180 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b32181 := hb (x (-1) 3)
    have b32182 := hb (x 0 2)
    have b32183 := hb (x 1 13)
    have b32184 := hb (x 2 12)
    clear * - r32178 e32179 e32180 b32181 b32182 b32183 b32184 d32149 d32165 d32124
    omega
  have d32185 : (x (-1) 3 && x (-1) 12).toNat = 0 := by
    have r32186 := hand1 (x (-1) 3) (x (-1) 12)
    have b32187 := hb (x (-1) 3)
    have b32188 := hb (x (-1) 3 && x (-1) 12)
    clear * - r32186 b32187 b32188 d32177
    omega
  have d32189 : (x (-1) 3 && x (-1) 4).toNat = 0 := by
    have r32190 := hand1 (x (-1) 3) (x (-1) 4)
    have b32191 := hb (x (-1) 3)
    have b32192 := hb (x (-1) 3 && x (-1) 4)
    clear * - r32190 b32191 b32192 d32177
    omega
  have d32193 : (x (-1) 11).toNat = 0 := by
    have r32194 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
    have b32195 := hb (x (-1) 3)
    have b32196 := hb (x (-1) 11)
    clear * - r32194 b32195 b32196 d32177
    omega
  have d32197 : (x 2 9).toNat = 0 := by
    have r32198 : (x 2 9).toNat ≤ (x 2 1).toNat := himp _ _ (hp9 2)
    have b32199 := hb (x 2 1)
    have b32200 := hb (x 2 9)
    clear * - r32198 b32199 b32200 d32116
    omega
  have d32201 : (x 6 8).toNat = 0 := by
    have r32202 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e32203 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e32204 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e32205 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e32206 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e32207 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e32208 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b32209 := hb (x (-1) 7)
    have b32210 := hb (x 0 6)
    have b32211 := hb (x 1 5)
    have b32212 := hb (x 2 4)
    have b32213 := hb (x 3 11)
    have b32214 := hb (x 4 10)
    have b32215 := hb (x 5 9)
    have b32216 := hb (x 6 8)
    clear * - r32202 e32203 e32204 e32205 e32206 e32207 e32208 b32209 b32210 b32211 b32212 b32213 b32214 b32215 b32216 g9 d32075 d32161 d32173
    omega
  have d32217 : (x 6 5 && x 6 8).toNat = 0 := by
    have r32218 := hand2 (x 6 5) (x 6 8)
    have b32219 := hb (x 6 8)
    have b32220 := hb (x 6 5 && x 6 8)
    clear * - r32218 b32219 b32220 d32201
    omega
  have d32221 : (x 5 9).toNat = 0 := by
    have r32222 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e32223 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e32224 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e32225 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e32226 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e32227 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e32228 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b32229 := hb (x (-1) 7)
    have b32230 := hb (x 0 6)
    have b32231 := hb (x 1 5)
    have b32232 := hb (x 2 4)
    have b32233 := hb (x 3 11)
    have b32234 := hb (x 4 10)
    have b32235 := hb (x 5 9)
    have b32236 := hb (x 6 8)
    clear * - r32222 e32223 e32224 e32225 e32226 e32227 e32228 b32229 b32230 b32231 b32232 b32233 b32234 b32235 b32236 d32201 g9 d32075 d32161 d32173
    omega
  have d32237 : (x 5 6 && x 5 9).toNat = 0 := by
    have r32238 := hand2 (x 5 6) (x 5 9)
    have b32239 := hb (x 5 9)
    have b32240 := hb (x 5 6 && x 5 9)
    clear * - r32238 b32239 b32240 d32221
    omega
  have d32241 : (x 0 6).toNat = 0 := by
    have r32242 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e32243 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e32244 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e32245 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e32246 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e32247 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e32248 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b32249 := hb (x (-1) 7)
    have b32250 := hb (x 0 6)
    have b32251 := hb (x 1 5)
    have b32252 := hb (x 2 4)
    have b32253 := hb (x 3 11)
    have b32254 := hb (x 4 10)
    have b32255 := hb (x 5 9)
    have b32256 := hb (x 6 8)
    clear * - r32242 e32243 e32244 e32245 e32246 e32247 e32248 b32249 b32250 b32251 b32252 b32253 b32254 b32255 b32256 d32201 d32221 g9 d32075 d32161 d32173
    omega
  have d32257 : (x 0 6 && x 0 12).toNat = 0 := by
    have r32258 := hand1 (x 0 6) (x 0 12)
    have b32259 := hb (x 0 6)
    have b32260 := hb (x 0 6 && x 0 12)
    clear * - r32258 b32259 b32260 d32241
    omega
  cases h32261 : x 0 3
  · have f32262 : (x 0 3).toNat = 0 := by rw [h32261]; rfl
    have d32263 : (x 0 2 && x 0 3).toNat = 0 := by
      have r32264 := hand2 (x 0 2) (x 0 3)
      have b32265 := hb (x 0 3)
      have b32266 := hb (x 0 2 && x 0 3)
      clear * - r32264 b32265 b32266 f32262
      omega
    have d32267 : (x 0 11).toNat = 0 := by
      have r32268 : (x 0 11).toNat ≤ (x 0 3).toNat := himp _ _ (hp11 0)
      have b32269 := hb (x 0 3)
      have b32270 := hb (x 0 11)
      clear * - r32268 b32269 b32270 f32262
      omega
    have d32271 : (x 0 2 && x 0 11).toNat = 0 := by
      have r32272 := hand2 (x 0 2) (x 0 11)
      have b32273 := hb (x 0 11)
      have b32274 := hb (x 0 2 && x 0 11)
      clear * - r32272 b32273 b32274 d32267
      omega
    have d32275 : (x 0 11 && x 0 14).toNat = 0 := by
      have r32276 := hand1 (x 0 11) (x 0 14)
      have b32277 := hb (x 0 11)
      have b32278 := hb (x 0 11 && x 0 14)
      clear * - r32276 b32277 b32278 d32267
      omega
    have d32279 : (x (-4) 4).toNat = 1 := by
      have r32280 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b32281 := hb (x (-4) 4)
      have b32282 := hb (x 0 11)
      have b32283 := hb (x (-1) 1 && x (-1) 12)
      have b32284 := hb (x (-2) 2 && x (-2) 13)
      have b32285 := hb (x (-3) 3 && x (-3) 14)
      clear * - r32280 b32281 b32282 b32283 b32284 b32285 d32267 d32137 d32023 d32047
      omega
    have d32286 : (x (-4) 12).toNat = 1 := by
      have r32287 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
      have b32288 := hb (x (-4) 4)
      have b32289 := hb (x (-4) 12)
      clear * - r32287 b32288 b32289 d32279
      omega
    have d32290 : (x (-5) 13).toNat = 0 := by
      have r32291 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32292 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e32293 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have b32294 := hb (x (-7) 3)
      have b32295 := hb (x (-6) 2)
      have b32296 := hb (x (-5) 13)
      have b32297 := hb (x (-4) 12)
      clear * - r32291 e32292 e32293 b32294 b32295 b32296 b32297 d32286
      omega
    have d32298 : (x (-5) 3 && x (-5) 13).toNat = 0 := by
      have r32299 := hand2 (x (-5) 3) (x (-5) 13)
      have b32300 := hb (x (-5) 13)
      have b32301 := hb (x (-5) 3 && x (-5) 13)
      clear * - r32299 b32300 b32301 d32290
      omega
    have d32302 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
      have r32303 := hand2 (x (-5) 4) (x (-5) 13)
      have b32304 := hb (x (-5) 13)
      have b32305 := hb (x (-5) 4 && x (-5) 13)
      clear * - r32303 b32304 b32305 d32290
      omega
    have d32306 : (x (-5) 5).toNat = 0 := by
      have r32307 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
      have b32308 := hb (x (-5) 5)
      have b32309 := hb (x (-5) 13)
      clear * - r32307 b32308 b32309 d32290
      omega
    have d32310 : (x (-5) 5 && x (-5) 11).toNat = 0 := by
      have r32311 := hand1 (x (-5) 5) (x (-5) 11)
      have b32312 := hb (x (-5) 5)
      have b32313 := hb (x (-5) 5 && x (-5) 11)
      clear * - r32311 b32312 b32313 d32306
      omega
    have d32314 : (x 0 8).toNat = 0 := by
      have r32315 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32316 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
      have e32317 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
      have e32318 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
      have e32319 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
      have e32320 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
      have e32321 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
      have b32322 := hb (x (-7) 7)
      have b32323 := hb (x (-6) 6)
      have b32324 := hb (x (-5) 5)
      have b32325 := hb (x (-4) 4)
      have b32326 := hb (x (-3) 11)
      have b32327 := hb (x (-2) 10)
      have b32328 := hb (x (-1) 9)
      have b32329 := hb (x 0 8)
      clear * - r32315 e32316 e32317 e32318 e32319 e32320 e32321 b32322 b32323 b32324 b32325 b32326 b32327 b32328 b32329 d32145 d32031 d32055 d32279 d32306
      omega
    have d32330 : (x (-6) 6).toNat = 0 := by
      have r32331 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32332 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
      have e32333 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
      have e32334 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
      have e32335 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
      have e32336 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
      have e32337 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
      have b32338 := hb (x (-7) 7)
      have b32339 := hb (x (-6) 6)
      have b32340 := hb (x (-5) 5)
      have b32341 := hb (x (-4) 4)
      have b32342 := hb (x (-3) 11)
      have b32343 := hb (x (-2) 10)
      have b32344 := hb (x (-1) 9)
      have b32345 := hb (x 0 8)
      clear * - r32331 e32332 e32333 e32334 e32335 e32336 e32337 b32338 b32339 b32340 b32341 b32342 b32343 b32344 b32345 d32314 d32145 d32031 d32055 d32279 d32306
      omega
    have d32346 : (x (-6) 6 && x (-6) 12).toNat = 0 := by
      have r32347 := hand1 (x (-6) 6) (x (-6) 12)
      have b32348 := hb (x (-6) 6)
      have b32349 := hb (x (-6) 6 && x (-6) 12)
      clear * - r32347 b32348 b32349 d32330
      omega
    have d32350 : (x (-7) 7).toNat = 0 := by
      have r32351 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32352 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
      have e32353 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
      have e32354 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
      have e32355 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
      have e32356 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
      have e32357 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
      have b32358 := hb (x (-7) 7)
      have b32359 := hb (x (-6) 6)
      have b32360 := hb (x (-5) 5)
      have b32361 := hb (x (-4) 4)
      have b32362 := hb (x (-3) 11)
      have b32363 := hb (x (-2) 10)
      have b32364 := hb (x (-1) 9)
      have b32365 := hb (x 0 8)
      clear * - r32351 e32352 e32353 e32354 e32355 e32356 e32357 b32358 b32359 b32360 b32361 b32362 b32363 b32364 b32365 d32314 d32145 d32031 d32055 d32279 d32306 d32330
      omega
    have d32366 : (x (-7) 7 && x (-7) 13).toNat = 0 := by
      have r32367 := hand1 (x (-7) 7) (x (-7) 13)
      have b32368 := hb (x (-7) 7)
      have b32369 := hb (x (-7) 7 && x (-7) 13)
      clear * - r32367 b32368 b32369 d32350
      omega
    have r32370 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r32371 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r32372 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r32373 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e32374 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
    have e32375 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
    have e32376 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
    have e32377 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
    have e32378 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
    have e32379 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
    have r32380 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e32381 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
    have e32382 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
    have e32383 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
    have e32384 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
    have e32385 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
    have e32386 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
    have r32387 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e32388 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
    have e32389 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
    have e32390 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
    have e32391 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
    have e32392 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
    have e32393 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
    have r32394 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e32395 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
    have e32396 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
    have e32397 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
    have e32398 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
    have e32399 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
    have e32400 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
    have r32401 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e32402 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
    have e32403 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
    have r32404 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e32405 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e32406 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have r32407 : 1 ≤ (x 2 1).toNat + (x 1 1 && x 1 2).toNat + (x 0 2 && x 0 3).toNat + (x (-1) 3 && x (-1) 4).toNat + (x (-2) 4 && x (-2) 5).toNat + (x (-3) 5 && x (-3) 6).toNat + (x (-4) 6 && x (-4) 7).toNat + (x (-5) 7 && x (-5) 8).toNat + (x (-6) 8 && x (-6) 9).toNat + (x (-7) 9 && x (-7) 10).toNat + (x (-8) 10 && x (-8) 11).toNat + (x (-9) 11 && x (-9) 12).toNat + (x (-10) 12 && x (-10) 13).toNat + (x (-11) 13 && x (-11) 14).toNat + (x (-12) 14).toNat := by have q := hcov1 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r32408 : 1 ≤ (x 11 3).toNat + (x 10 1 && x 10 4).toNat + (x 9 2 && x 9 5).toNat + (x 8 3 && x 8 6).toNat + (x 7 4 && x 7 7).toNat + (x 6 5 && x 6 8).toNat + (x 5 6 && x 5 9).toNat + (x 4 7 && x 4 10).toNat + (x 3 8 && x 3 11).toNat + (x 2 9 && x 2 12).toNat + (x 1 10 && x 1 13).toNat + (x 0 11 && x 0 14).toNat + (x (-1) 12).toNat := by have q := hcov3 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r32409 : 1 ≤ (x 0 6).toNat + (x (-1) 1 && x (-1) 7).toNat + (x (-2) 2 && x (-2) 8).toNat + (x (-3) 3 && x (-3) 9).toNat + (x (-4) 4 && x (-4) 10).toNat + (x (-5) 5 && x (-5) 11).toNat + (x (-6) 6 && x (-6) 12).toNat + (x (-7) 7 && x (-7) 13).toNat + (x (-8) 8 && x (-8) 14).toNat + (x (-9) 9).toNat := by have q := hcov6 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r32410 : 1 ≤ (x 6 6).toNat + (x 5 1 && x 5 7).toNat + (x 4 2 && x 4 8).toNat + (x 3 3 && x 3 9).toNat + (x 2 4 && x 2 10).toNat + (x 1 5 && x 1 11).toNat + (x 0 6 && x 0 12).toNat + (x (-1) 7 && x (-1) 13).toNat + (x (-2) 8 && x (-2) 14).toNat + (x (-3) 9).toNat := by have q := hcov6 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r32411 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r32412 : 1 ≤ (x 2 9).toNat + (x 1 1 && x 1 10).toNat + (x 0 2 && x 0 11).toNat + (x (-1) 3 && x (-1) 12).toNat + (x (-2) 4 && x (-2) 13).toNat + (x (-3) 5 && x (-3) 14).toNat + (x (-4) 6).toNat := by have q := hcov9 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r32413 : 1 ≤ (x (-8) 10).toNat + (x (-9) 1 && x (-9) 11).toNat + (x (-10) 2 && x (-10) 12).toNat + (x (-11) 3 && x (-11) 13).toNat + (x (-12) 4 && x (-12) 14).toNat + (x (-13) 5).toNat := by have q := hcov10 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r32414 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r32415 : 1 ≤ (x 12 10).toNat + (x 11 1 && x 11 11).toNat + (x 10 2 && x 10 12).toNat + (x 9 3 && x 9 13).toNat + (x 8 4 && x 8 14).toNat + (x 7 5).toNat := by have q := hcov10 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r32416 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r32417 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r32418 : (x 12 10).toNat ≤ (x 12 2).toNat := himp _ _ (hp10 12)
    have r32419 := hand1 (x (-2) 4) (x (-2) 5)
    have r32420 := hand2 (x (-3) 5) (x (-3) 6)
    have r32421 := hand2 (x (-4) 6) (x (-4) 7)
    have r32422 := hand1 (x (-5) 7) (x (-5) 8)
    have r32423 := hand1 (x (-6) 8) (x (-6) 9)
    have r32424 := hand1 (x (-7) 9) (x (-7) 10)
    have r32425 := hand1 (x (-8) 10) (x (-8) 11)
    have r32426 := hand1 (x (-9) 11) (x (-9) 12)
    have r32427 := hand1 (x (-10) 12) (x (-10) 13)
    have r32428 := hand1 (x (-11) 13) (x (-11) 14)
    have r32429 := hand2 (x 10 1) (x 10 4)
    have r32430 := hand2 (x 9 2) (x 9 5)
    have r32431 := hand2 (x 8 3) (x 8 6)
    have r32432 := hand2 (x 7 4) (x 7 7)
    have r32433 := hand1 (x 3 8) (x 3 11)
    have r32434 := hand2 (x (-4) 4) (x (-4) 10)
    have r32435 := hand1 (x (-8) 8) (x (-8) 14)
    have r32436 := hand2 (x 5 1) (x 5 7)
    have r32437 := hand2 (x 3 3) (x 3 9)
    have r32438 := hand1 (x (-2) 8) (x (-2) 14)
    have r32439 := hand1 (x (-4) 3) (x (-4) 12)
    have r32440 := hand1 (x (-6) 5) (x (-6) 14)
    have r32441 := hand1 (x (-2) 4) (x (-2) 13)
    have r32442 := hand2 (x (-2) 4) (x (-2) 13)
    have r32443 := hand1 (x (-3) 5) (x (-3) 14)
    have r32444 := hand2 (x (-9) 1) (x (-9) 11)
    have r32445 := hand2 (x (-10) 2) (x (-10) 12)
    have r32446 := hand2 (x (-11) 3) (x (-11) 13)
    have r32447 := hand2 (x (-12) 4) (x (-12) 14)
    have r32448 := hand1 (x (-4) 2) (x (-4) 12)
    have r32449 := hand1 (x (-6) 4) (x (-6) 14)
    have r32450 := hand1 (x 11 1) (x 11 11)
    have r32451 := hand1 (x 10 2) (x 10 12)
    have r32452 := hand1 (x 9 3) (x 9 13)
    have r32453 := hand1 (x 8 4) (x 8 14)
    have r32454 := hand2 (x (-2) 1) (x (-2) 12)
    have r32455 := hand2 (x (-3) 2) (x (-3) 13)
    have r32456 := hand1 (x (-4) 3) (x (-4) 14)
    have r32457 := hand2 (x (-2) 1) (x (-2) 14)
    linarith only [r32370, r32371, r32372, r32373, e32374, e32375, e32376, e32377, e32378, e32379, r32380, e32381, e32382, e32383, e32384, e32385, e32386, r32387, e32388, e32389, e32390, e32391, e32392, e32393, r32394, e32395, e32396, e32397, e32398, e32399, e32400, r32401, e32402, e32403, r32404, e32405, e32406, r32407, r32408, r32409, r32410, r32411, r32412, r32413, r32414, r32415, r32416, r32417, r32418, r32419, r32420, r32421, r32422, r32423, r32424, r32425, r32426, r32427, r32428, r32429, r32430, r32431, r32432, r32433, r32434, r32435, r32436, r32437, r32438, r32439, r32440, r32441, r32442, r32443, r32444, r32445, r32446, r32447, r32448, r32449, r32450, r32451, r32452, r32453, r32454, r32455, r32456, r32457, d32031, d32177, d32145, d32193, d31999, d32124, d32241, d32267, g1, d32129, g2, g4, g5, d32165, d32116, d32197, g6, d32149, d32075, g9, d32221, d32201, g10, d32263, d32189, d32217, d32237, g11, d32157, g12, d32275, d32141, d32027, d32051, d32310, d32346, d32366, g13, g14, g15, d32257, d32007, d32035, d32063, d32302, g16, d32271, d32185, d32059, d32298]
  · have f32612 : (x 0 3).toNat = 1 := by rw [h32261]; rfl
    have d32613 : (x 3 12).toNat = 0 := by
      have r32614 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32615 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
      have e32616 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
      have b32617 := hb (x 0 3)
      have b32618 := hb (x 1 2)
      have b32619 := hb (x 2 13)
      have b32620 := hb (x 3 12)
      clear * - r32614 e32615 e32616 b32617 b32618 b32619 b32620 d32120 g3 f32612
      omega
    have d32621 : (x 3 1 && x 3 12).toNat = 0 := by
      have r32622 := hand2 (x 3 1) (x 3 12)
      have b32623 := hb (x 3 12)
      have b32624 := hb (x 3 1 && x 3 12)
      clear * - r32622 b32623 b32624 d32613
      omega
    have d32625 : (x 3 4).toNat = 0 := by
      have r32626 : (x 3 4).toNat ≤ (x 3 12).toNat := himp _ _ (hp4 3)
      have b32627 := hb (x 3 4)
      have b32628 := hb (x 3 12)
      clear * - r32626 b32627 b32628 d32613
      omega
    have d32629 : (x 7 11).toNat = 1 := by
      have r32630 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b32631 := hb (x 3 4)
      have b32632 := hb (x 7 11)
      have b32633 := hb (x 6 1 && x 6 12)
      have b32634 := hb (x 5 2 && x 5 13)
      have b32635 := hb (x 4 3 && x 4 14)
      clear * - r32630 b32631 b32632 b32633 b32634 b32635 d32091 d32103 g22 d32625
      omega
    have d32636 : (x 7 3).toNat = 1 := by
      have r32637 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
      have b32638 := hb (x 7 3)
      have b32639 := hb (x 7 11)
      clear * - r32637 b32638 b32639 d32629
      omega
    have d32640 : (x 10 12).toNat = 0 := by
      have r32641 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32642 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e32643 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b32644 := hb (x 7 3)
      have b32645 := hb (x 8 2)
      have b32646 := hb (x 9 13)
      have b32647 := hb (x 10 12)
      clear * - r32641 e32642 e32643 b32644 b32645 b32646 b32647 d32636
      omega
    have d32648 : (x 10 1 && x 10 12).toNat = 0 := by
      have r32649 := hand2 (x 10 1) (x 10 12)
      have b32650 := hb (x 10 12)
      have b32651 := hb (x 10 1 && x 10 12)
      clear * - r32649 b32650 b32651 d32640
      omega
    have d32652 : (x 9 13).toNat = 0 := by
      have r32653 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32654 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e32655 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b32656 := hb (x 7 3)
      have b32657 := hb (x 8 2)
      have b32658 := hb (x 9 13)
      have b32659 := hb (x 10 12)
      clear * - r32653 e32654 e32655 b32656 b32657 b32658 b32659 d32640 d32636
      omega
    have d32660 : (x 9 2 && x 9 13).toNat = 0 := by
      have r32661 := hand2 (x 9 2) (x 9 13)
      have b32662 := hb (x 9 13)
      have b32663 := hb (x 9 2 && x 9 13)
      clear * - r32661 b32662 b32663 d32652
      omega
    have d32664 : (x 8 2).toNat = 0 := by
      have r32665 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32666 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e32667 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b32668 := hb (x 7 3)
      have b32669 := hb (x 8 2)
      have b32670 := hb (x 9 13)
      have b32671 := hb (x 10 12)
      clear * - r32665 e32666 e32667 b32668 b32669 b32670 b32671 d32640 d32652 d32636
      omega
    have d32672 : (x 4 11).toNat = 1 := by
      have r32673 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b32674 := hb (x 0 4)
      have b32675 := hb (x 4 11)
      have b32676 := hb (x 3 1 && x 3 12)
      have b32677 := hb (x 2 2 && x 2 13)
      have b32678 := hb (x 1 3 && x 1 14)
      clear * - r32673 b32674 b32675 b32676 b32677 b32678 d32621 g20 g21 g0
      omega
    have d32679 : (x 4 3).toNat = 1 := by
      have r32680 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
      have b32681 := hb (x 4 3)
      have b32682 := hb (x 4 11)
      clear * - r32680 b32681 b32682 d32672
      omega
    have d32683 : (x 7 12).toNat = 0 := by
      have r32684 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32685 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
      have e32686 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
      have b32687 := hb (x 4 3)
      have b32688 := hb (x 5 2)
      have b32689 := hb (x 6 13)
      have b32690 := hb (x 7 12)
      clear * - r32684 e32685 e32686 b32687 b32688 b32689 b32690 d32679
      omega
    have d32691 : (x 7 1 && x 7 12).toNat = 0 := by
      have r32692 := hand2 (x 7 1) (x 7 12)
      have b32693 := hb (x 7 12)
      have b32694 := hb (x 7 1 && x 7 12)
      clear * - r32692 b32693 b32694 d32683
      omega
    have d32695 : (x 7 4).toNat = 0 := by
      have r32696 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
      have b32697 := hb (x 7 4)
      have b32698 := hb (x 7 12)
      clear * - r32696 b32697 b32698 d32683
      omega
    have d32699 : (x 6 13).toNat = 0 := by
      have r32700 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32701 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
      have e32702 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
      have b32703 := hb (x 4 3)
      have b32704 := hb (x 5 2)
      have b32705 := hb (x 6 13)
      have b32706 := hb (x 7 12)
      clear * - r32700 e32701 e32702 b32703 b32704 b32705 b32706 d32683 d32679
      omega
    have d32707 : (x 6 2 && x 6 13).toNat = 0 := by
      have r32708 := hand2 (x 6 2) (x 6 13)
      have b32709 := hb (x 6 13)
      have b32710 := hb (x 6 2 && x 6 13)
      clear * - r32708 b32709 b32710 d32699
      omega
    have d32711 : (x 5 1 && x 5 14).toNat = 1 := by
      have r32712 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b32713 := hb (x 4 2)
      have b32714 := hb (x 6 13)
      have b32715 := hb (x 5 1 && x 5 14)
      clear * - r32712 b32713 b32714 b32715 d32699 g7
      omega
    have d32716 : (x 5 1).toNat = 1 := by
      have r32717 := hand1 (x 5 1) (x 5 14)
      have b32718 := hb (x 5 1)
      have b32719 := hb (x 5 1 && x 5 14)
      clear * - r32717 b32718 b32719 d32711
      omega
    have d32720 : (x 6 14).toNat = 0 := by
      have r32721 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b32722 := hb (x 5 1)
      have b32723 := hb (x 6 14)
      clear * - r32721 b32722 b32723 d32716
      omega
    have d32724 : (x 6 1 && x 6 14).toNat = 0 := by
      have r32725 := hand2 (x 6 1) (x 6 14)
      have b32726 := hb (x 6 14)
      have b32727 := hb (x 6 1 && x 6 14)
      clear * - r32725 b32726 b32727 d32720
      omega
    have d32728 : (x 6 2).toNat = 0 := by
      have r32729 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
      have b32730 := hb (x 6 2)
      have b32731 := hb (x 6 14)
      clear * - r32729 b32730 b32731 d32720
      omega
    have d32732 : (x 5 2).toNat = 0 := by
      have r32733 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32734 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
      have e32735 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
      have b32736 := hb (x 4 3)
      have b32737 := hb (x 5 2)
      have b32738 := hb (x 6 13)
      have b32739 := hb (x 7 12)
      clear * - r32733 e32734 e32735 b32736 b32737 b32738 b32739 d32683 d32699 d32679
      omega
    have d32740 : (x 7 13).toNat = 1 := by
      have r32741 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b32742 := hb (x 5 2)
      have b32743 := hb (x 7 13)
      have b32744 := hb (x 6 1 && x 6 14)
      clear * - r32741 b32742 b32743 b32744 d32724 d32732
      omega
    have d32745 : (x 7 1).toNat = 1 := by
      have r32746 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
      have b32747 := hb (x 7 1)
      have b32748 := hb (x 7 13)
      clear * - r32746 b32747 b32748 d32740
      omega
    have d32749 : (x 8 14).toNat = 0 := by
      have r32750 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b32751 := hb (x 7 1)
      have b32752 := hb (x 8 14)
      clear * - r32750 b32751 b32752 d32745
      omega
    have d32753 : (x 8 3 && x 8 14).toNat = 0 := by
      have r32754 := hand2 (x 8 3) (x 8 14)
      have b32755 := hb (x 8 14)
      have b32756 := hb (x 8 3 && x 8 14)
      clear * - r32754 b32755 b32756 d32749
      omega
    have d32757 : (x 11 11).toNat = 1 := by
      have r32758 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b32759 := hb (x 7 4)
      have b32760 := hb (x 11 11)
      have b32761 := hb (x 10 1 && x 10 12)
      have b32762 := hb (x 9 2 && x 9 13)
      have b32763 := hb (x 8 3 && x 8 14)
      clear * - r32758 b32759 b32760 b32761 b32762 b32763 d32648 d32660 d32753 d32695
      omega
    have d32764 : (x 11 3).toNat = 1 := by
      have r32765 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
      have b32766 := hb (x 11 3)
      have b32767 := hb (x 11 11)
      clear * - r32765 b32766 b32767 d32757
      omega
    have d32768 : (x 14 12).toNat = 0 := by
      have r32769 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32770 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
      have e32771 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
      have b32772 := hb (x 11 3)
      have b32773 := hb (x 12 2)
      have b32774 := hb (x 13 13)
      have b32775 := hb (x 14 12)
      clear * - r32769 e32770 e32771 b32772 b32773 b32774 b32775 d32764
      omega
    have d32776 : (x 14 1 && x 14 12).toNat = 0 := by
      have r32777 := hand2 (x 14 1) (x 14 12)
      have b32778 := hb (x 14 12)
      have b32779 := hb (x 14 1 && x 14 12)
      clear * - r32777 b32778 b32779 d32768
      omega
    have d32780 : (x 13 13).toNat = 0 := by
      have r32781 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32782 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
      have e32783 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
      have b32784 := hb (x 11 3)
      have b32785 := hb (x 12 2)
      have b32786 := hb (x 13 13)
      have b32787 := hb (x 14 12)
      clear * - r32781 e32782 e32783 b32784 b32785 b32786 b32787 d32768 d32764
      omega
    have d32788 : (x 13 2 && x 13 13).toNat = 0 := by
      have r32789 := hand2 (x 13 2) (x 13 13)
      have b32790 := hb (x 13 13)
      have b32791 := hb (x 13 2 && x 13 13)
      clear * - r32789 b32790 b32791 d32780
      omega
    have d32792 : (x 12 2).toNat = 0 := by
      have r32793 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32794 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
      have e32795 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
      have b32796 := hb (x 11 3)
      have b32797 := hb (x 12 2)
      have b32798 := hb (x 13 13)
      have b32799 := hb (x 14 12)
      clear * - r32793 e32794 e32795 b32796 b32797 b32798 b32799 d32768 d32780 d32764
      omega
    have d32800 : (x 8 12).toNat = 0 := by
      have r32801 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32802 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e32803 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have b32804 := hb (x 5 3)
      have b32805 := hb (x 6 2)
      have b32806 := hb (x 7 13)
      have b32807 := hb (x 8 12)
      clear * - r32801 e32802 e32803 b32804 b32805 b32806 b32807 d32740 d32728
      omega
    have d32808 : (x 8 4).toNat = 0 := by
      have r32809 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
      have b32810 := hb (x 8 4)
      have b32811 := hb (x 8 12)
      clear * - r32809 b32810 b32811 d32800
      omega
    have d32812 : (x 5 3).toNat = 0 := by
      have r32813 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32814 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e32815 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have b32816 := hb (x 5 3)
      have b32817 := hb (x 6 2)
      have b32818 := hb (x 7 13)
      have b32819 := hb (x 8 12)
      clear * - r32813 e32814 e32815 b32816 b32817 b32818 b32819 d32800 d32740 d32728
      omega
    have d32820 : (x 5 3 && x 5 14).toNat = 0 := by
      have r32821 := hand1 (x 5 3) (x 5 14)
      have b32822 := hb (x 5 3)
      have b32823 := hb (x 5 3 && x 5 14)
      clear * - r32821 b32822 b32823 d32812
      omega
    have d32824 : (x 8 11).toNat = 1 := by
      have r32825 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b32826 := hb (x 4 4)
      have b32827 := hb (x 8 11)
      have b32828 := hb (x 7 1 && x 7 12)
      have b32829 := hb (x 6 2 && x 6 13)
      have b32830 := hb (x 5 3 && x 5 14)
      clear * - r32825 b32826 b32827 b32828 b32829 b32830 d32691 d32707 d32820 g8
      omega
    have d32831 : (x 8 3).toNat = 1 := by
      have r32832 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
      have b32833 := hb (x 8 3)
      have b32834 := hb (x 8 11)
      clear * - r32832 b32833 b32834 d32824
      omega
    have d32835 : (x 11 12).toNat = 0 := by
      have r32836 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32837 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
      have e32838 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
      have b32839 := hb (x 8 3)
      have b32840 := hb (x 9 2)
      have b32841 := hb (x 10 13)
      have b32842 := hb (x 11 12)
      clear * - r32836 e32837 e32838 b32839 b32840 b32841 b32842 d32831
      omega
    have d32843 : (x 11 1 && x 11 12).toNat = 0 := by
      have r32844 := hand2 (x 11 1) (x 11 12)
      have b32845 := hb (x 11 12)
      have b32846 := hb (x 11 1 && x 11 12)
      clear * - r32844 b32845 b32846 d32835
      omega
    have d32847 : (x 11 4).toNat = 0 := by
      have r32848 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
      have b32849 := hb (x 11 4)
      have b32850 := hb (x 11 12)
      clear * - r32848 b32849 b32850 d32835
      omega
    have d32851 : (x 10 13).toNat = 0 := by
      have r32852 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32853 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
      have e32854 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
      have b32855 := hb (x 8 3)
      have b32856 := hb (x 9 2)
      have b32857 := hb (x 10 13)
      have b32858 := hb (x 11 12)
      clear * - r32852 e32853 e32854 b32855 b32856 b32857 b32858 d32835 d32831
      omega
    have d32859 : (x 10 2 && x 10 13).toNat = 0 := by
      have r32860 := hand2 (x 10 2) (x 10 13)
      have b32861 := hb (x 10 13)
      have b32862 := hb (x 10 2 && x 10 13)
      clear * - r32860 b32861 b32862 d32851
      omega
    have d32863 : (x 9 1 && x 9 14).toNat = 1 := by
      have r32864 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b32865 := hb (x 8 2)
      have b32866 := hb (x 10 13)
      have b32867 := hb (x 9 1 && x 9 14)
      clear * - r32864 b32865 b32866 b32867 d32851 d32664
      omega
    have d32868 : (x 9 1).toNat = 1 := by
      have r32869 := hand1 (x 9 1) (x 9 14)
      have b32870 := hb (x 9 1)
      have b32871 := hb (x 9 1 && x 9 14)
      clear * - r32869 b32870 b32871 d32863
      omega
    have d32872 : (x 10 14).toNat = 0 := by
      have r32873 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b32874 := hb (x 9 1)
      have b32875 := hb (x 10 14)
      clear * - r32873 b32874 b32875 d32868
      omega
    have d32876 : (x 10 1 && x 10 14).toNat = 0 := by
      have r32877 := hand2 (x 10 1) (x 10 14)
      have b32878 := hb (x 10 14)
      have b32879 := hb (x 10 1 && x 10 14)
      clear * - r32877 b32878 b32879 d32872
      omega
    have d32880 : (x 10 2).toNat = 0 := by
      have r32881 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
      have b32882 := hb (x 10 2)
      have b32883 := hb (x 10 14)
      clear * - r32881 b32882 b32883 d32872
      omega
    have d32884 : (x 9 2).toNat = 0 := by
      have r32885 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32886 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
      have e32887 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
      have b32888 := hb (x 8 3)
      have b32889 := hb (x 9 2)
      have b32890 := hb (x 10 13)
      have b32891 := hb (x 11 12)
      clear * - r32885 e32886 e32887 b32888 b32889 b32890 b32891 d32835 d32851 d32831
      omega
    have d32892 : (x 11 13).toNat = 1 := by
      have r32893 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b32894 := hb (x 9 2)
      have b32895 := hb (x 11 13)
      have b32896 := hb (x 10 1 && x 10 14)
      clear * - r32893 b32894 b32895 b32896 d32876 d32884
      omega
    have d32897 : (x 11 1).toNat = 1 := by
      have r32898 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
      have b32899 := hb (x 11 1)
      have b32900 := hb (x 11 13)
      clear * - r32898 b32899 b32900 d32892
      omega
    have d32901 : (x 12 14).toNat = 0 := by
      have r32902 : (x 12 14).toNat + (x 11 1).toNat = 1 := by have q := hd14 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b32903 := hb (x 11 1)
      have b32904 := hb (x 12 14)
      clear * - r32902 b32903 b32904 d32897
      omega
    have d32905 : (x 12 1 && x 12 14).toNat = 0 := by
      have r32906 := hand2 (x 12 1) (x 12 14)
      have b32907 := hb (x 12 14)
      have b32908 := hb (x 12 1 && x 12 14)
      clear * - r32906 b32907 b32908 d32901
      omega
    have d32909 : (x 11 2).toNat = 1 := by
      have r32910 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b32911 := hb (x 11 2)
      have b32912 := hb (x 13 13)
      have b32913 := hb (x 12 1 && x 12 14)
      clear * - r32910 b32911 b32912 b32913 d32780 d32905
      omega
    have d32914 : (x 13 12).toNat = 0 := by
      have r32915 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32916 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
      have e32917 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
      have b32918 := hb (x 10 3)
      have b32919 := hb (x 11 2)
      have b32920 := hb (x 12 13)
      have b32921 := hb (x 13 12)
      clear * - r32915 e32916 e32917 b32918 b32919 b32920 b32921 d32909
      omega
    have d32922 : (x 13 4).toNat = 0 := by
      have r32923 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
      have b32924 := hb (x 13 4)
      have b32925 := hb (x 13 12)
      clear * - r32923 b32924 b32925 d32914
      omega
    have d32926 : (x 13 4 && x 13 14).toNat = 0 := by
      have r32927 := hand1 (x 13 4) (x 13 14)
      have b32928 := hb (x 13 4)
      have b32929 := hb (x 13 4 && x 13 14)
      clear * - r32927 b32928 b32929 d32922
      omega
    have d32930 : (x 12 13).toNat = 0 := by
      have r32931 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32932 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
      have e32933 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
      have b32934 := hb (x 10 3)
      have b32935 := hb (x 11 2)
      have b32936 := hb (x 12 13)
      have b32937 := hb (x 13 12)
      clear * - r32931 e32932 e32933 b32934 b32935 b32936 b32937 d32914 d32909
      omega
    have d32938 : (x 12 5).toNat = 0 := by
      have r32939 : (x 12 5).toNat ≤ (x 12 13).toNat := himp _ _ (hp5 12)
      have b32940 := hb (x 12 5)
      have b32941 := hb (x 12 13)
      clear * - r32939 b32940 b32941 d32930
      omega
    have d32942 : (x 12 3 && x 12 14).toNat = 0 := by
      have r32943 := hand2 (x 12 3) (x 12 14)
      have b32944 := hb (x 12 14)
      have b32945 := hb (x 12 3 && x 12 14)
      clear * - r32943 b32944 b32945 d32901
      omega
    have d32946 : (x 15 11).toNat = 1 := by
      have r32947 : 1 ≤ (x 15 11).toNat + (x 14 1 && x 14 12).toNat + (x 13 2 && x 13 13).toNat + (x 12 3 && x 12 14).toNat + (x 11 4).toNat := by have q := hcov11 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b32948 := hb (x 11 4)
      have b32949 := hb (x 15 11)
      have b32950 := hb (x 14 1 && x 14 12)
      have b32951 := hb (x 13 2 && x 13 13)
      have b32952 := hb (x 12 3 && x 12 14)
      clear * - r32947 b32948 b32949 b32950 b32951 b32952 d32776 d32788 d32942 d32847
      omega
    have d32953 : (x 15 3).toNat = 1 := by
      have r32954 : (x 15 11).toNat ≤ (x 15 3).toNat := himp _ _ (hp11 15)
      have b32955 := hb (x 15 3)
      have b32956 := hb (x 15 11)
      clear * - r32954 b32955 b32956 d32946
      omega
    have d32957 : (x 18 12).toNat = 0 := by
      have r32958 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32959 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
      have e32960 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
      have b32961 := hb (x 15 3)
      have b32962 := hb (x 16 2)
      have b32963 := hb (x 17 13)
      have b32964 := hb (x 18 12)
      clear * - r32958 e32959 e32960 b32961 b32962 b32963 b32964 d32953
      omega
    have d32965 : (x 17 13).toNat = 0 := by
      have r32966 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32967 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
      have e32968 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
      have b32969 := hb (x 15 3)
      have b32970 := hb (x 16 2)
      have b32971 := hb (x 17 13)
      have b32972 := hb (x 18 12)
      clear * - r32966 e32967 e32968 b32969 b32970 b32971 b32972 d32957 d32953
      omega
    have d32973 : (x 16 2).toNat = 0 := by
      have r32974 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32975 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
      have e32976 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
      have b32977 := hb (x 15 3)
      have b32978 := hb (x 16 2)
      have b32979 := hb (x 17 13)
      have b32980 := hb (x 18 12)
      clear * - r32974 e32975 e32976 b32977 b32978 b32979 b32980 d32957 d32965 d32953
      omega
    have d32981 : (x 12 12).toNat = 0 := by
      have r32982 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32983 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
      have e32984 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
      have b32985 := hb (x 9 3)
      have b32986 := hb (x 10 2)
      have b32987 := hb (x 11 13)
      have b32988 := hb (x 12 12)
      clear * - r32982 e32983 e32984 b32985 b32986 b32987 b32988 d32892 d32880
      omega
    have d32989 : (x 12 4).toNat = 0 := by
      have r32990 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
      have b32991 := hb (x 12 4)
      have b32992 := hb (x 12 12)
      clear * - r32990 b32991 b32992 d32981
      omega
    have d32993 : (x 9 3).toNat = 0 := by
      have r32994 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32995 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
      have e32996 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
      have b32997 := hb (x 9 3)
      have b32998 := hb (x 10 2)
      have b32999 := hb (x 11 13)
      have b33000 := hb (x 12 12)
      clear * - r32994 e32995 e32996 b32997 b32998 b32999 b33000 d32981 d32892 d32880
      omega
    have d33001 : (x 9 3 && x 9 14).toNat = 0 := by
      have r33002 := hand1 (x 9 3) (x 9 14)
      have b33003 := hb (x 9 3)
      have b33004 := hb (x 9 3 && x 9 14)
      clear * - r33002 b33003 b33004 d32993
      omega
    have d33005 : (x 12 11).toNat = 1 := by
      have r33006 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b33007 := hb (x 8 4)
      have b33008 := hb (x 12 11)
      have b33009 := hb (x 11 1 && x 11 12)
      have b33010 := hb (x 10 2 && x 10 13)
      have b33011 := hb (x 9 3 && x 9 14)
      clear * - r33006 b33007 b33008 b33009 b33010 b33011 d32843 d32859 d33001 d32808
      omega
    have d33012 : (x 12 3).toNat = 1 := by
      have r33013 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
      have b33014 := hb (x 12 3)
      have b33015 := hb (x 12 11)
      clear * - r33013 b33014 b33015 d33005
      omega
    have d33016 : (x 15 12).toNat = 0 := by
      have r33017 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e33018 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
      have e33019 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
      have b33020 := hb (x 12 3)
      have b33021 := hb (x 13 2)
      have b33022 := hb (x 14 13)
      have b33023 := hb (x 15 12)
      clear * - r33017 e33018 e33019 b33020 b33021 b33022 b33023 d33012
      omega
    have d33024 : (x 15 1 && x 15 12).toNat = 0 := by
      have r33025 := hand2 (x 15 1) (x 15 12)
      have b33026 := hb (x 15 12)
      have b33027 := hb (x 15 1 && x 15 12)
      clear * - r33025 b33026 b33027 d33016
      omega
    have d33028 : (x 15 2 && x 15 12).toNat = 0 := by
      have r33029 := hand2 (x 15 2) (x 15 12)
      have b33030 := hb (x 15 12)
      have b33031 := hb (x 15 2 && x 15 12)
      clear * - r33029 b33030 b33031 d33016
      omega
    have d33032 : (x 14 13).toNat = 0 := by
      have r33033 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e33034 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
      have e33035 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
      have b33036 := hb (x 12 3)
      have b33037 := hb (x 13 2)
      have b33038 := hb (x 14 13)
      have b33039 := hb (x 15 12)
      clear * - r33033 e33034 e33035 b33036 b33037 b33038 b33039 d33016 d33012
      omega
    have d33040 : (x 14 2 && x 14 13).toNat = 0 := by
      have r33041 := hand2 (x 14 2) (x 14 13)
      have b33042 := hb (x 14 13)
      have b33043 := hb (x 14 2 && x 14 13)
      clear * - r33041 b33042 b33043 d33032
      omega
    have d33044 : (x 14 3 && x 14 13).toNat = 0 := by
      have r33045 := hand2 (x 14 3) (x 14 13)
      have b33046 := hb (x 14 13)
      have b33047 := hb (x 14 3 && x 14 13)
      clear * - r33045 b33046 b33047 d33032
      omega
    have d33048 : (x 13 1 && x 13 14).toNat = 1 := by
      have r33049 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b33050 := hb (x 12 2)
      have b33051 := hb (x 14 13)
      have b33052 := hb (x 13 1 && x 13 14)
      clear * - r33049 b33050 b33051 b33052 d33032 d32792
      omega
    have d33053 : (x 13 1).toNat = 1 := by
      have r33054 := hand1 (x 13 1) (x 13 14)
      have b33055 := hb (x 13 1)
      have b33056 := hb (x 13 1 && x 13 14)
      clear * - r33054 b33055 b33056 d33048
      omega
    have d33057 : (x 14 14).toNat = 0 := by
      have r33058 : (x 14 14).toNat + (x 13 1).toNat = 1 := by have q := hd14 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b33059 := hb (x 13 1)
      have b33060 := hb (x 14 14)
      clear * - r33058 b33059 b33060 d33053
      omega
    have d33061 : (x 14 1 && x 14 14).toNat = 0 := by
      have r33062 := hand2 (x 14 1) (x 14 14)
      have b33063 := hb (x 14 14)
      have b33064 := hb (x 14 1 && x 14 14)
      clear * - r33062 b33063 b33064 d33057
      omega
    have d33065 : (x 14 2).toNat = 0 := by
      have r33066 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
      have b33067 := hb (x 14 2)
      have b33068 := hb (x 14 14)
      clear * - r33066 b33067 b33068 d33057
      omega
    have d33069 : (x 13 2).toNat = 0 := by
      have r33070 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e33071 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
      have e33072 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
      have b33073 := hb (x 12 3)
      have b33074 := hb (x 13 2)
      have b33075 := hb (x 14 13)
      have b33076 := hb (x 15 12)
      clear * - r33070 e33071 e33072 b33073 b33074 b33075 b33076 d33016 d33032 d33012
      omega
    have d33077 : (x 15 13).toNat = 1 := by
      have r33078 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b33079 := hb (x 13 2)
      have b33080 := hb (x 15 13)
      have b33081 := hb (x 14 1 && x 14 14)
      clear * - r33078 b33079 b33080 b33081 d33061 d33069
      omega
    have d33082 : (x 16 12).toNat = 0 := by
      have r33083 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e33084 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
      have e33085 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
      have b33086 := hb (x 13 3)
      have b33087 := hb (x 14 2)
      have b33088 := hb (x 15 13)
      have b33089 := hb (x 16 12)
      clear * - r33083 e33084 e33085 b33086 b33087 b33088 b33089 d33077 d33065
      omega
    have d33090 : (x 13 3).toNat = 0 := by
      have r33091 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e33092 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
      have e33093 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
      have b33094 := hb (x 13 3)
      have b33095 := hb (x 14 2)
      have b33096 := hb (x 15 13)
      have b33097 := hb (x 16 12)
      clear * - r33091 e33092 e33093 b33094 b33095 b33096 b33097 d33082 d33077 d33065
      omega
    have d33098 : (x 13 3 && x 13 14).toNat = 0 := by
      have r33099 := hand1 (x 13 3) (x 13 14)
      have b33100 := hb (x 13 3)
      have b33101 := hb (x 13 3 && x 13 14)
      clear * - r33099 b33100 b33101 d33090
      omega
    have d33102 : (x 16 11).toNat = 1 := by
      have r33103 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b33104 := hb (x 12 4)
      have b33105 := hb (x 16 11)
      have b33106 := hb (x 15 1 && x 15 12)
      have b33107 := hb (x 14 2 && x 14 13)
      have b33108 := hb (x 13 3 && x 13 14)
      clear * - r33103 b33104 b33105 b33106 b33107 b33108 d33024 d33040 d33098 d32989
      omega
    have d33109 : (x 16 3).toNat = 1 := by
      have r33110 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
      have b33111 := hb (x 16 3)
      have b33112 := hb (x 16 11)
      clear * - r33110 b33111 b33112 d33102
      omega
    have d33113 : (x 19 12).toNat = 0 := by
      have r33114 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e33115 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
      have e33116 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
      have b33117 := hb (x 16 3)
      have b33118 := hb (x 17 2)
      have b33119 := hb (x 18 13)
      have b33120 := hb (x 19 12)
      clear * - r33114 e33115 e33116 b33117 b33118 b33119 b33120 d33109
      omega
    have d33121 : (x 18 13).toNat = 0 := by
      have r33122 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e33123 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
      have e33124 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
      have b33125 := hb (x 16 3)
      have b33126 := hb (x 17 2)
      have b33127 := hb (x 18 13)
      have b33128 := hb (x 19 12)
      clear * - r33122 e33123 e33124 b33125 b33126 b33127 b33128 d33113 d33109
      omega
    have d33129 : (x 17 1 && x 17 14).toNat = 1 := by
      have r33130 : 1 ≤ (x 18 13).toNat + (x 17 1 && x 17 14).toNat + (x 16 2).toNat := by have q := hcov13 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b33131 := hb (x 16 2)
      have b33132 := hb (x 18 13)
      have b33133 := hb (x 17 1 && x 17 14)
      clear * - r33130 b33131 b33132 b33133 d33121 d32973
      omega
    have d33134 : (x 17 14).toNat = 1 := by
      have r33135 := hand2 (x 17 1) (x 17 14)
      have b33136 := hb (x 17 14)
      have b33137 := hb (x 17 1 && x 17 14)
      clear * - r33135 b33136 b33137 d33129
      omega
    have d33138 : (x 16 1).toNat = 0 := by
      have r33139 : (x 17 14).toNat + (x 16 1).toNat = 1 := by have q := hd14 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b33140 := hb (x 16 1)
      have b33141 := hb (x 17 14)
      clear * - r33139 b33140 b33141 d33134
      omega
    have d33142 : (x 16 1 && x 16 11).toNat = 0 := by
      have r33143 := hand1 (x 16 1) (x 16 11)
      have b33144 := hb (x 16 1)
      have b33145 := hb (x 16 1 && x 16 11)
      clear * - r33143 b33144 b33145 d33138
      omega
    have d33146 : (x 17 2).toNat = 0 := by
      have r33147 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e33148 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
      have e33149 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
      have b33150 := hb (x 16 3)
      have b33151 := hb (x 17 2)
      have b33152 := hb (x 18 13)
      have b33153 := hb (x 19 12)
      clear * - r33147 e33148 e33149 b33150 b33151 b33152 b33153 d33113 d33121 d33109
      omega
    have d33154 : (x 17 10).toNat = 0 := by
      have r33155 : (x 17 10).toNat ≤ (x 17 2).toNat := himp _ _ (hp10 17)
      have b33156 := hb (x 17 2)
      have b33157 := hb (x 17 10)
      clear * - r33155 b33156 b33157 d33146
      omega
    have r33158 : 1 ≤ (x 17 10).toNat + (x 16 1 && x 16 11).toNat + (x 15 2 && x 15 12).toNat + (x 14 3 && x 14 13).toNat + (x 13 4 && x 13 14).toNat + (x 12 5).toNat := by have q := hcov10 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33159 := hb (x 12 5)
    have b33160 := hb (x 17 10)
    have b33161 := hb (x 16 1 && x 16 11)
    have b33162 := hb (x 15 2 && x 15 12)
    have b33163 := hb (x 14 3 && x 14 13)
    have b33164 := hb (x 13 4 && x 13 14)
    linarith only [r33158, b33159, b33160, b33161, b33162, b33163, b33164, d33154, d33142, d33028, d33044, d32926, d32938]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt11100 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 2).toNat = 0)
    (g1 : (x 2 2).toNat = 0)
    (g2 : (x 4 2).toNat = 0)
    (g3 : (x 1 1 && x 1 14).toNat = 0)
    (g4 : (x 4 1 && x 4 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d33450 : (x 2 13).toNat = 1 := by
    have r33451 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33452 := hb (x 0 2)
    have b33453 := hb (x 2 13)
    have b33454 := hb (x 1 1 && x 1 14)
    clear * - r33451 b33452 b33453 b33454 g3 g0
    omega
  have d33455 : (x 2 1).toNat = 1 := by
    have r33456 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
    have b33457 := hb (x 2 1)
    have b33458 := hb (x 2 13)
    clear * - r33456 b33457 b33458 d33450
    omega
  have d33459 : (x 3 14).toNat = 0 := by
    have r33460 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33461 := hb (x 2 1)
    have b33462 := hb (x 3 14)
    clear * - r33460 b33461 b33462 d33455
    omega
  have d33463 : (x 3 1 && x 3 14).toNat = 0 := by
    have r33464 := hand2 (x 3 1) (x 3 14)
    have b33465 := hb (x 3 14)
    have b33466 := hb (x 3 1 && x 3 14)
    clear * - r33464 b33465 b33466 d33459
    omega
  have d33467 : (x 4 13).toNat = 1 := by
    have r33468 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33469 := hb (x 2 2)
    have b33470 := hb (x 4 13)
    have b33471 := hb (x 3 1 && x 3 14)
    clear * - r33468 b33469 b33470 b33471 d33463 g1
    omega
  have d33472 : (x 4 1).toNat = 1 := by
    have r33473 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
    have b33474 := hb (x 4 1)
    have b33475 := hb (x 4 13)
    clear * - r33473 b33474 b33475 d33467
    omega
  have d33476 : (x 5 14).toNat = 0 := by
    have r33477 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33478 := hb (x 4 1)
    have b33479 := hb (x 5 14)
    clear * - r33477 b33478 b33479 d33472
    omega
  have d33480 : (x 5 1 && x 5 14).toNat = 0 := by
    have r33481 := hand2 (x 5 1) (x 5 14)
    have b33482 := hb (x 5 14)
    have b33483 := hb (x 5 1 && x 5 14)
    clear * - r33481 b33482 b33483 d33476
    omega
  have d33484 : (x 6 13).toNat = 1 := by
    have r33485 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33486 := hb (x 4 2)
    have b33487 := hb (x 6 13)
    have b33488 := hb (x 5 1 && x 5 14)
    clear * - r33485 b33486 b33487 b33488 d33480 g2
    omega
  have d33489 : (x 6 1).toNat = 1 := by
    have r33490 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
    have b33491 := hb (x 6 1)
    have b33492 := hb (x 6 13)
    clear * - r33490 b33491 b33492 d33484
    omega
  have d33493 : (x 7 14).toNat = 0 := by
    have r33494 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33495 := hb (x 6 1)
    have b33496 := hb (x 7 14)
    clear * - r33494 b33495 b33496 d33489
    omega
  have d33497 : (x 7 1 && x 7 14).toNat = 0 := by
    have r33498 := hand2 (x 7 1) (x 7 14)
    have b33499 := hb (x 7 14)
    have b33500 := hb (x 7 1 && x 7 14)
    clear * - r33498 b33499 b33500 d33493
    omega
  have d33501 : (x 7 2).toNat = 0 := by
    have r33502 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
    have b33503 := hb (x 7 2)
    have b33504 := hb (x 7 14)
    clear * - r33502 b33503 b33504 d33493
    omega
  have d33505 : (x 5 2).toNat = 0 := by
    have r33506 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
    have b33507 := hb (x 5 2)
    have b33508 := hb (x 5 14)
    clear * - r33506 b33507 b33508 d33476
    omega
  have d33509 : (x 3 2).toNat = 0 := by
    have r33510 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
    have b33511 := hb (x 3 2)
    have b33512 := hb (x 3 14)
    clear * - r33510 b33511 b33512 d33459
    omega
  have d33513 : (x 5 13).toNat = 1 := by
    have r33514 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33515 := hb (x 3 2)
    have b33516 := hb (x 5 13)
    have b33517 := hb (x 4 1 && x 4 14)
    clear * - r33514 b33515 b33516 b33517 g4 d33509
    omega
  have d33518 : (x 5 1).toNat = 1 := by
    have r33519 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
    have b33520 := hb (x 5 1)
    have b33521 := hb (x 5 13)
    clear * - r33519 b33520 b33521 d33513
    omega
  have d33522 : (x 6 14).toNat = 0 := by
    have r33523 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33524 := hb (x 5 1)
    have b33525 := hb (x 6 14)
    clear * - r33523 b33524 b33525 d33518
    omega
  have d33526 : (x 6 1 && x 6 14).toNat = 0 := by
    have r33527 := hand2 (x 6 1) (x 6 14)
    have b33528 := hb (x 6 14)
    have b33529 := hb (x 6 1 && x 6 14)
    clear * - r33527 b33528 b33529 d33522
    omega
  have d33530 : (x 7 13).toNat = 1 := by
    have r33531 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33532 := hb (x 5 2)
    have b33533 := hb (x 7 13)
    have b33534 := hb (x 6 1 && x 6 14)
    clear * - r33531 b33532 b33533 b33534 d33526 d33505
    omega
  have d33535 : (x 7 1).toNat = 1 := by
    have r33536 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
    have b33537 := hb (x 7 1)
    have b33538 := hb (x 7 13)
    clear * - r33536 b33537 b33538 d33530
    omega
  have d33539 : (x 8 14).toNat = 0 := by
    have r33540 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33541 := hb (x 7 1)
    have b33542 := hb (x 8 14)
    clear * - r33540 b33541 b33542 d33535
    omega
  have d33543 : (x 8 1 && x 8 14).toNat = 0 := by
    have r33544 := hand2 (x 8 1) (x 8 14)
    have b33545 := hb (x 8 14)
    have b33546 := hb (x 8 1 && x 8 14)
    clear * - r33544 b33545 b33546 d33539
    omega
  have d33547 : (x 9 13).toNat = 1 := by
    have r33548 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33549 := hb (x 7 2)
    have b33550 := hb (x 9 13)
    have b33551 := hb (x 8 1 && x 8 14)
    clear * - r33548 b33549 b33550 b33551 d33543 d33501
    omega
  have d33552 : (x 9 1).toNat = 1 := by
    have r33553 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
    have b33554 := hb (x 9 1)
    have b33555 := hb (x 9 13)
    clear * - r33553 b33554 b33555 d33547
    omega
  have d33556 : (x 10 14).toNat = 0 := by
    have r33557 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33558 := hb (x 9 1)
    have b33559 := hb (x 10 14)
    clear * - r33557 b33558 b33559 d33552
    omega
  have d33560 : (x 10 1 && x 10 14).toNat = 0 := by
    have r33561 := hand2 (x 10 1) (x 10 14)
    have b33562 := hb (x 10 14)
    have b33563 := hb (x 10 1 && x 10 14)
    clear * - r33561 b33562 b33563 d33556
    omega
  have d33564 : (x 10 2).toNat = 0 := by
    have r33565 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
    have b33566 := hb (x 10 2)
    have b33567 := hb (x 10 14)
    clear * - r33565 b33566 b33567 d33556
    omega
  have d33568 : (x 8 2).toNat = 0 := by
    have r33569 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
    have b33570 := hb (x 8 2)
    have b33571 := hb (x 8 14)
    clear * - r33569 b33570 b33571 d33539
    omega
  have d33572 : (x 6 2).toNat = 0 := by
    have r33573 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
    have b33574 := hb (x 6 2)
    have b33575 := hb (x 6 14)
    clear * - r33573 b33574 b33575 d33522
    omega
  have d33576 : (x 8 13).toNat = 1 := by
    have r33577 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33578 := hb (x 6 2)
    have b33579 := hb (x 8 13)
    have b33580 := hb (x 7 1 && x 7 14)
    clear * - r33577 b33578 b33579 b33580 d33497 d33572
    omega
  have d33581 : (x 8 1).toNat = 1 := by
    have r33582 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
    have b33583 := hb (x 8 1)
    have b33584 := hb (x 8 13)
    clear * - r33582 b33583 b33584 d33576
    omega
  have d33585 : (x 9 14).toNat = 0 := by
    have r33586 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33587 := hb (x 8 1)
    have b33588 := hb (x 9 14)
    clear * - r33586 b33587 b33588 d33581
    omega
  have d33589 : (x 9 1 && x 9 14).toNat = 0 := by
    have r33590 := hand2 (x 9 1) (x 9 14)
    have b33591 := hb (x 9 14)
    have b33592 := hb (x 9 1 && x 9 14)
    clear * - r33590 b33591 b33592 d33585
    omega
  have d33593 : (x 10 13).toNat = 1 := by
    have r33594 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33595 := hb (x 8 2)
    have b33596 := hb (x 10 13)
    have b33597 := hb (x 9 1 && x 9 14)
    clear * - r33594 b33595 b33596 b33597 d33589 d33568
    omega
  have d33598 : (x 10 1).toNat = 1 := by
    have r33599 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
    have b33600 := hb (x 10 1)
    have b33601 := hb (x 10 13)
    clear * - r33599 b33600 b33601 d33593
    omega
  have d33602 : (x 11 14).toNat = 0 := by
    have r33603 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33604 := hb (x 10 1)
    have b33605 := hb (x 11 14)
    clear * - r33603 b33604 b33605 d33598
    omega
  have d33606 : (x 11 1 && x 11 14).toNat = 0 := by
    have r33607 := hand2 (x 11 1) (x 11 14)
    have b33608 := hb (x 11 14)
    have b33609 := hb (x 11 1 && x 11 14)
    clear * - r33607 b33608 b33609 d33602
    omega
  have d33610 : (x 12 13).toNat = 1 := by
    have r33611 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33612 := hb (x 10 2)
    have b33613 := hb (x 12 13)
    have b33614 := hb (x 11 1 && x 11 14)
    clear * - r33611 b33612 b33613 b33614 d33606 d33564
    omega
  have d33615 : (x 12 1).toNat = 1 := by
    have r33616 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
    have b33617 := hb (x 12 1)
    have b33618 := hb (x 12 13)
    clear * - r33616 b33617 b33618 d33610
    omega
  have d33619 : (x 13 14).toNat = 0 := by
    have r33620 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33621 := hb (x 12 1)
    have b33622 := hb (x 13 14)
    clear * - r33620 b33621 b33622 d33615
    omega
  have d33623 : (x 13 1 && x 13 14).toNat = 0 := by
    have r33624 := hand2 (x 13 1) (x 13 14)
    have b33625 := hb (x 13 14)
    have b33626 := hb (x 13 1 && x 13 14)
    clear * - r33624 b33625 b33626 d33619
    omega
  have d33627 : (x 13 2).toNat = 0 := by
    have r33628 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
    have b33629 := hb (x 13 2)
    have b33630 := hb (x 13 14)
    clear * - r33628 b33629 b33630 d33619
    omega
  have d33631 : (x 11 2).toNat = 0 := by
    have r33632 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
    have b33633 := hb (x 11 2)
    have b33634 := hb (x 11 14)
    clear * - r33632 b33633 b33634 d33602
    omega
  have d33635 : (x 9 2).toNat = 0 := by
    have r33636 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
    have b33637 := hb (x 9 2)
    have b33638 := hb (x 9 14)
    clear * - r33636 b33637 b33638 d33585
    omega
  have d33639 : (x 11 13).toNat = 1 := by
    have r33640 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33641 := hb (x 9 2)
    have b33642 := hb (x 11 13)
    have b33643 := hb (x 10 1 && x 10 14)
    clear * - r33640 b33641 b33642 b33643 d33560 d33635
    omega
  have d33644 : (x 11 1).toNat = 1 := by
    have r33645 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
    have b33646 := hb (x 11 1)
    have b33647 := hb (x 11 13)
    clear * - r33645 b33646 b33647 d33639
    omega
  have d33648 : (x 12 14).toNat = 0 := by
    have r33649 : (x 12 14).toNat + (x 11 1).toNat = 1 := by have q := hd14 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33650 := hb (x 11 1)
    have b33651 := hb (x 12 14)
    clear * - r33649 b33650 b33651 d33644
    omega
  have d33652 : (x 12 1 && x 12 14).toNat = 0 := by
    have r33653 := hand2 (x 12 1) (x 12 14)
    have b33654 := hb (x 12 14)
    have b33655 := hb (x 12 1 && x 12 14)
    clear * - r33653 b33654 b33655 d33648
    omega
  have d33656 : (x 13 13).toNat = 1 := by
    have r33657 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33658 := hb (x 11 2)
    have b33659 := hb (x 13 13)
    have b33660 := hb (x 12 1 && x 12 14)
    clear * - r33657 b33658 b33659 b33660 d33652 d33631
    omega
  have d33661 : (x 13 1).toNat = 1 := by
    have r33662 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
    have b33663 := hb (x 13 1)
    have b33664 := hb (x 13 13)
    clear * - r33662 b33663 b33664 d33656
    omega
  have d33665 : (x 14 14).toNat = 0 := by
    have r33666 : (x 14 14).toNat + (x 13 1).toNat = 1 := by have q := hd14 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33667 := hb (x 13 1)
    have b33668 := hb (x 14 14)
    clear * - r33666 b33667 b33668 d33661
    omega
  have d33669 : (x 14 1 && x 14 14).toNat = 0 := by
    have r33670 := hand2 (x 14 1) (x 14 14)
    have b33671 := hb (x 14 14)
    have b33672 := hb (x 14 1 && x 14 14)
    clear * - r33670 b33671 b33672 d33665
    omega
  have d33673 : (x 15 13).toNat = 1 := by
    have r33674 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33675 := hb (x 13 2)
    have b33676 := hb (x 15 13)
    have b33677 := hb (x 14 1 && x 14 14)
    clear * - r33674 b33675 b33676 b33677 d33669 d33627
    omega
  have d33678 : (x 15 1).toNat = 1 := by
    have r33679 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
    have b33680 := hb (x 15 1)
    have b33681 := hb (x 15 13)
    clear * - r33679 b33680 b33681 d33673
    omega
  have d33682 : (x 16 14).toNat = 0 := by
    have r33683 : (x 16 14).toNat + (x 15 1).toNat = 1 := by have q := hd14 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33684 := hb (x 15 1)
    have b33685 := hb (x 16 14)
    clear * - r33683 b33684 b33685 d33678
    omega
  have d33686 : (x 16 1 && x 16 14).toNat = 0 := by
    have r33687 := hand2 (x 16 1) (x 16 14)
    have b33688 := hb (x 16 14)
    have b33689 := hb (x 16 1 && x 16 14)
    clear * - r33687 b33688 b33689 d33682
    omega
  have d33690 : (x 14 3 && x 14 14).toNat = 0 := by
    have r33691 := hand2 (x 14 3) (x 14 14)
    have b33692 := hb (x 14 14)
    have b33693 := hb (x 14 3 && x 14 14)
    clear * - r33691 b33692 b33693 d33665
    omega
  have d33694 : (x 14 2).toNat = 0 := by
    have r33695 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
    have b33696 := hb (x 14 2)
    have b33697 := hb (x 14 14)
    clear * - r33695 b33696 b33697 d33665
    omega
  have d33698 : (x 12 2).toNat = 0 := by
    have r33699 : (x 12 2).toNat ≤ (x 12 14).toNat := himp _ _ (hp2 12)
    have b33700 := hb (x 12 2)
    have b33701 := hb (x 12 14)
    clear * - r33699 b33700 b33701 d33648
    omega
  have d33702 : (x 14 13).toNat = 1 := by
    have r33703 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33704 := hb (x 12 2)
    have b33705 := hb (x 14 13)
    have b33706 := hb (x 13 1 && x 13 14)
    clear * - r33703 b33704 b33705 b33706 d33623 d33698
    omega
  have d33707 : (x 14 1).toNat = 1 := by
    have r33708 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
    have b33709 := hb (x 14 1)
    have b33710 := hb (x 14 13)
    clear * - r33708 b33709 b33710 d33702
    omega
  have d33711 : (x 15 14).toNat = 0 := by
    have r33712 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33713 := hb (x 14 1)
    have b33714 := hb (x 15 14)
    clear * - r33712 b33713 b33714 d33707
    omega
  have d33715 : (x 15 1 && x 15 14).toNat = 0 := by
    have r33716 := hand2 (x 15 1) (x 15 14)
    have b33717 := hb (x 15 14)
    have b33718 := hb (x 15 1 && x 15 14)
    clear * - r33716 b33717 b33718 d33711
    omega
  have d33719 : (x 16 13).toNat = 1 := by
    have r33720 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33721 := hb (x 14 2)
    have b33722 := hb (x 16 13)
    have b33723 := hb (x 15 1 && x 15 14)
    clear * - r33720 b33721 b33722 b33723 d33715 d33694
    omega
  have d33724 : (x 16 1).toNat = 1 := by
    have r33725 : (x 16 13).toNat ≤ (x 16 1).toNat := himp _ _ (hp13 16)
    have b33726 := hb (x 16 1)
    have b33727 := hb (x 16 13)
    clear * - r33725 b33726 b33727 d33719
    omega
  have d33728 : (x 17 14).toNat = 0 := by
    have r33729 : (x 17 14).toNat + (x 16 1).toNat = 1 := by have q := hd14 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33730 := hb (x 16 1)
    have b33731 := hb (x 17 14)
    clear * - r33729 b33730 b33731 d33724
    omega
  have d33732 : (x 17 2).toNat = 0 := by
    have r33733 : (x 17 2).toNat ≤ (x 17 14).toNat := himp _ _ (hp2 17)
    have b33734 := hb (x 17 2)
    have b33735 := hb (x 17 14)
    clear * - r33733 b33734 b33735 d33728
    omega
  have d33736 : (x 15 2).toNat = 0 := by
    have r33737 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
    have b33738 := hb (x 15 2)
    have b33739 := hb (x 15 14)
    clear * - r33737 b33738 b33739 d33711
    omega
  have d33740 : (x 15 2 && x 15 13).toNat = 0 := by
    have r33741 := hand1 (x 15 2) (x 15 13)
    have b33742 := hb (x 15 2)
    have b33743 := hb (x 15 2 && x 15 13)
    clear * - r33741 b33742 b33743 d33736
    omega
  have d33744 : (x 17 13).toNat = 1 := by
    have r33745 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := by have q := hcov13 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33746 := hb (x 15 2)
    have b33747 := hb (x 17 13)
    have b33748 := hb (x 16 1 && x 16 14)
    clear * - r33745 b33746 b33747 b33748 d33686 d33736
    omega
  have d33749 : (x 17 1).toNat = 1 := by
    have r33750 : (x 17 13).toNat ≤ (x 17 1).toNat := himp _ _ (hp13 17)
    have b33751 := hb (x 17 1)
    have b33752 := hb (x 17 13)
    clear * - r33750 b33751 b33752 d33744
    omega
  have d33753 : (x 18 14).toNat = 0 := by
    have r33754 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33755 := hb (x 17 1)
    have b33756 := hb (x 18 14)
    clear * - r33754 b33755 b33756 d33749
    omega
  have d33757 : (x 18 1 && x 18 14).toNat = 0 := by
    have r33758 := hand2 (x 18 1) (x 18 14)
    have b33759 := hb (x 18 14)
    have b33760 := hb (x 18 1 && x 18 14)
    clear * - r33758 b33759 b33760 d33753
    omega
  have d33761 : (x 19 13).toNat = 1 := by
    have r33762 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b33763 := hb (x 17 2)
    have b33764 := hb (x 19 13)
    have b33765 := hb (x 18 1 && x 18 14)
    clear * - r33762 b33763 b33764 b33765 d33757 d33732
    omega
  have d33766 : (x 18 2).toNat = 0 := by
    have r33767 : (x 18 2).toNat ≤ (x 18 14).toNat := himp _ _ (hp2 18)
    have b33768 := hb (x 18 2)
    have b33769 := hb (x 18 14)
    clear * - r33767 b33768 b33769 d33753
    omega
  have d33770 : (x 20 12).toNat = 0 := by
    have r33771 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e33772 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
    have e33773 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
    have b33774 := hb (x 17 3)
    have b33775 := hb (x 18 2)
    have b33776 := hb (x 19 13)
    have b33777 := hb (x 20 12)
    clear * - r33771 e33772 e33773 b33774 b33775 b33776 b33777 d33761 d33766
    omega
  have d33778 : (x 17 3).toNat = 0 := by
    have r33779 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e33780 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
    have e33781 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
    have b33782 := hb (x 17 3)
    have b33783 := hb (x 18 2)
    have b33784 := hb (x 19 13)
    have b33785 := hb (x 20 12)
    clear * - r33779 e33780 e33781 b33782 b33783 b33784 b33785 d33770 d33761 d33766
    omega
  have d33786 : (x 17 11).toNat = 0 := by
    have r33787 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
    have b33788 := hb (x 17 3)
    have b33789 := hb (x 17 11)
    clear * - r33787 b33788 b33789 d33778
    omega
  have d33790 : (x 16 12).toNat = 0 := by
    have r33791 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e33792 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e33793 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b33794 := hb (x 13 3)
    have b33795 := hb (x 14 2)
    have b33796 := hb (x 15 13)
    have b33797 := hb (x 16 12)
    clear * - r33791 e33792 e33793 b33794 b33795 b33796 b33797 d33673 d33694
    omega
  have d33798 : (x 16 1 && x 16 12).toNat = 0 := by
    have r33799 := hand2 (x 16 1) (x 16 12)
    have b33800 := hb (x 16 12)
    have b33801 := hb (x 16 1 && x 16 12)
    clear * - r33799 b33800 b33801 d33790
    omega
  have d33802 : (x 13 12).toNat = 0 := by
    have r33803 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e33804 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e33805 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b33806 := hb (x 10 3)
    have b33807 := hb (x 11 2)
    have b33808 := hb (x 12 13)
    have b33809 := hb (x 13 12)
    clear * - r33803 e33804 e33805 b33806 b33807 b33808 b33809 d33610 d33631
    omega
  have d33810 : (x 13 4).toNat = 0 := by
    have r33811 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
    have b33812 := hb (x 13 4)
    have b33813 := hb (x 13 12)
    clear * - r33811 b33812 b33813 d33802
    omega
  have r33814 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have b33815 := hb (x 13 4)
  have b33816 := hb (x 17 11)
  have b33817 := hb (x 16 1 && x 16 12)
  have b33818 := hb (x 15 2 && x 15 13)
  have b33819 := hb (x 14 3 && x 14 14)
  linarith only [r33814, b33815, b33816, b33817, b33818, b33819, d33786, d33798, d33740, d33690, d33810]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt111010_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 7).toNat = 0)
    (g1 : (x (-3) 11).toNat = 0)
    (g2 : (x (-2) 6).toNat = 0)
    (g3 : (x (-2) 10).toNat = 0)
    (g4 : (x (-2) 11).toNat = 0)
    (g5 : (x (-1) 5).toNat = 0)
    (g6 : (x (-1) 9).toNat = 0)
    (g7 : (x (-1) 10).toNat = 0)
    (g8 : (x 0 3).toNat = 0)
    (g9 : (x 0 4).toNat = 1)
    (g10 : (x 1 3).toNat = 0)
    (g11 : (x 1 10).toNat = 0)
    (g12 : (x 2 2).toNat = 0)
    (g13 : (x 2 6).toNat = 0)
    (g14 : (x 3 1).toNat = 1)
    (g15 : (x 3 9).toNat = 0)
    (g16 : (x 4 4).toNat = 0)
    (g17 : (x 4 4 && x 4 8).toNat = 0)
    (g18 : (x 3 5 && x 3 9).toNat = 0)
    (g19 : (x 2 6 && x 2 10).toNat = 0)
    (g20 : (x 1 7 && x 1 11).toNat = 0)
    (g21 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g22 : (x 2 1 && x 2 6).toNat = 0)
    (g23 : (x 1 2 && x 1 7).toNat = 0)
    (g24 : (x (-1) 4 && x (-1) 9).toNat = 0)
    (g25 : (x (-2) 5 && x (-2) 10).toNat = 0)
    (g26 : (x (-3) 6 && x (-3) 11).toNat = 0)
    (g27 : (x 4 3 && x 4 8).toNat = 0)
    (g28 : (x 3 4 && x 3 9).toNat = 0)
    (g29 : (x 2 5 && x 2 10).toNat = 0)
    (g30 : (x 1 6 && x 1 11).toNat = 0)
    (g31 : (x 0 7 && x 0 12).toNat = 0)
    (g32 : (x (-1) 8 && x (-1) 13).toNat = 0)
    (g33 : (x 2 2 && x 2 9).toNat = 0)
    (g34 : (x 1 3 && x 1 10).toNat = 0)
    (g35 : (x (-1) 5 && x (-1) 12).toNat = 0)
    (g36 : (x (-2) 6 && x (-2) 13).toNat = 0)
    (g37 : (x (-3) 7 && x (-3) 14).toNat = 0)
    (g38 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g39 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g40 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g41 : (x (-2) 2 && x (-2) 11).toNat = 0)
    (g42 : (x (-3) 3 && x (-3) 12).toNat = 0)
    (g43 : (x 2 1 && x 2 10).toNat = 0)
    (g44 : (x 1 2 && x 1 11).toNat = 0)
    (g45 : (x (-1) 4 && x (-1) 13).toNat = 0)
    (g46 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g47 : (x (-1) 2 && x (-1) 12).toNat = 0)
    (g48 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g49 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g50 : (x (-2) 2 && x (-2) 13).toNat = 0)
    (g51 : (x (-3) 3 && x (-3) 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d34012 : (x 0 3 && x 0 12).toNat = 0 := by
    have r34013 := hand1 (x 0 3) (x 0 12)
    have b34014 := hb (x 0 3)
    have b34015 := hb (x 0 3 && x 0 12)
    clear * - r34013 b34014 b34015 g8
    omega
  have d34016 : (x 0 3 && x 0 8).toNat = 0 := by
    have r34017 := hand1 (x 0 3) (x 0 8)
    have b34018 := hb (x 0 3)
    have b34019 := hb (x 0 3 && x 0 8)
    clear * - r34017 b34018 b34019 g8
    omega
  have d34020 : (x 0 11).toNat = 0 := by
    have r34021 : (x 0 11).toNat ≤ (x 0 3).toNat := himp _ _ (hp11 0)
    have b34022 := hb (x 0 3)
    have b34023 := hb (x 0 11)
    clear * - r34021 b34022 b34023 g8
    omega
  have d34024 : (x 0 1 && x 0 11).toNat = 0 := by
    have r34025 := hand2 (x 0 1) (x 0 11)
    have b34026 := hb (x 0 11)
    have b34027 := hb (x 0 1 && x 0 11)
    clear * - r34025 b34026 b34027 d34020
    omega
  have d34028 : (x 0 4 && x 0 11).toNat = 0 := by
    have r34029 := hand2 (x 0 4) (x 0 11)
    have b34030 := hb (x 0 11)
    have b34031 := hb (x 0 4 && x 0 11)
    clear * - r34029 b34030 b34031 d34020
    omega
  have d34032 : (x (-4) 4).toNat = 1 := by
    have r34033 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b34034 := hb (x (-4) 4)
    have b34035 := hb (x 0 11)
    have b34036 := hb (x (-1) 1 && x (-1) 12)
    have b34037 := hb (x (-2) 2 && x (-2) 13)
    have b34038 := hb (x (-3) 3 && x (-3) 14)
    clear * - r34033 b34034 b34035 b34036 b34037 b34038 d34020 g49 g50 g51
    omega
  have d34039 : (x (-4) 12).toNat = 1 := by
    have r34040 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
    have b34041 := hb (x (-4) 4)
    have b34042 := hb (x (-4) 12)
    clear * - r34040 b34041 b34042 d34032
    omega
  have d34043 : (x (-5) 13).toNat = 0 := by
    have r34044 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e34045 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e34046 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b34047 := hb (x (-7) 3)
    have b34048 := hb (x (-6) 2)
    have b34049 := hb (x (-5) 13)
    have b34050 := hb (x (-4) 12)
    clear * - r34044 e34045 e34046 b34047 b34048 b34049 b34050 d34039
    omega
  have d34051 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
    have r34052 := hand2 (x (-5) 4) (x (-5) 13)
    have b34053 := hb (x (-5) 13)
    have b34054 := hb (x (-5) 4 && x (-5) 13)
    clear * - r34052 b34053 b34054 d34043
    omega
  have d34055 : (x (-5) 8 && x (-5) 13).toNat = 0 := by
    have r34056 := hand2 (x (-5) 8) (x (-5) 13)
    have b34057 := hb (x (-5) 13)
    have b34058 := hb (x (-5) 8 && x (-5) 13)
    clear * - r34056 b34057 b34058 d34043
    omega
  have d34059 : (x (-5) 5).toNat = 0 := by
    have r34060 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
    have b34061 := hb (x (-5) 5)
    have b34062 := hb (x (-5) 13)
    clear * - r34060 b34061 b34062 d34043
    omega
  have d34063 : (x (-5) 5 && x (-5) 14).toNat = 0 := by
    have r34064 := hand1 (x (-5) 5) (x (-5) 14)
    have b34065 := hb (x (-5) 5)
    have b34066 := hb (x (-5) 5 && x (-5) 14)
    clear * - r34064 b34065 b34066 d34059
    omega
  have d34067 : (x (-6) 2).toNat = 0 := by
    have r34068 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e34069 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e34070 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b34071 := hb (x (-7) 3)
    have b34072 := hb (x (-6) 2)
    have b34073 := hb (x (-5) 13)
    have b34074 := hb (x (-4) 12)
    clear * - r34068 e34069 e34070 b34071 b34072 b34073 b34074 d34039 d34043
    omega
  have d34075 : (x (-6) 10).toNat = 0 := by
    have r34076 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
    have b34077 := hb (x (-6) 2)
    have b34078 := hb (x (-6) 10)
    clear * - r34076 b34077 b34078 d34067
    omega
  have d34079 : (x (-6) 1 && x (-6) 10).toNat = 0 := by
    have r34080 := hand2 (x (-6) 1) (x (-6) 10)
    have b34081 := hb (x (-6) 10)
    have b34082 := hb (x (-6) 1 && x (-6) 10)
    clear * - r34080 b34081 b34082 d34075
    omega
  have d34083 : (x (-7) 3).toNat = 0 := by
    have r34084 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e34085 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e34086 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b34087 := hb (x (-7) 3)
    have b34088 := hb (x (-6) 2)
    have b34089 := hb (x (-5) 13)
    have b34090 := hb (x (-4) 12)
    clear * - r34084 e34085 e34086 b34087 b34088 b34089 b34090 d34039 d34043 d34067
    omega
  have d34091 : (x (-7) 11).toNat = 0 := by
    have r34092 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
    have b34093 := hb (x (-7) 3)
    have b34094 := hb (x (-7) 11)
    clear * - r34092 b34093 b34094 d34083
    omega
  have d34095 : (x (-7) 2 && x (-7) 11).toNat = 0 := by
    have r34096 := hand2 (x (-7) 2) (x (-7) 11)
    have b34097 := hb (x (-7) 11)
    have b34098 := hb (x (-7) 2 && x (-7) 11)
    clear * - r34096 b34097 b34098 d34091
    omega
  have d34099 : (x 0 8).toNat = 0 := by
    have r34100 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e34101 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e34102 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e34103 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e34104 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e34105 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e34106 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b34107 := hb (x (-7) 7)
    have b34108 := hb (x (-6) 6)
    have b34109 := hb (x (-5) 5)
    have b34110 := hb (x (-4) 4)
    have b34111 := hb (x (-3) 11)
    have b34112 := hb (x (-2) 10)
    have b34113 := hb (x (-1) 9)
    have b34114 := hb (x 0 8)
    clear * - r34100 e34101 e34102 e34103 e34104 e34105 e34106 b34107 b34108 b34109 b34110 b34111 b34112 b34113 b34114 g6 g3 g1 d34032 d34059
    omega
  have d34115 : (x 0 8 && x 0 12).toNat = 0 := by
    have r34116 := hand1 (x 0 8) (x 0 12)
    have b34117 := hb (x 0 8)
    have b34118 := hb (x 0 8 && x 0 12)
    clear * - r34116 b34117 b34118 d34099
    omega
  have d34119 : (x (-6) 6).toNat = 0 := by
    have r34120 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e34121 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e34122 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e34123 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e34124 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e34125 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e34126 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b34127 := hb (x (-7) 7)
    have b34128 := hb (x (-6) 6)
    have b34129 := hb (x (-5) 5)
    have b34130 := hb (x (-4) 4)
    have b34131 := hb (x (-3) 11)
    have b34132 := hb (x (-2) 10)
    have b34133 := hb (x (-1) 9)
    have b34134 := hb (x 0 8)
    clear * - r34120 e34121 e34122 e34123 e34124 e34125 e34126 b34127 b34128 b34129 b34130 b34131 b34132 b34133 b34134 d34099 g6 g3 g1 d34032 d34059
    omega
  have r34135 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r34136 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r34137 : (x (-5) 8).toNat + (x (-6) 1 && x (-6) 9).toNat + (x (-7) 2 && x (-7) 10).toNat + (x (-8) 3 && x (-8) 11).toNat + (x (-9) 4 && x (-9) 12).toNat + (x (-10) 5 && x (-10) 13).toNat + (x (-11) 6 && x (-11) 14).toNat + (x (-12) 7).toNat = 1 := by have q := hd8 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e34138 : (x (-6) 1 && x (-6) 9).toNat = (x (-6) 9).toNat := handr _ _ (fun h => hp9 (-6) (h))
  have e34139 : (x (-7) 2 && x (-7) 10).toNat = (x (-7) 10).toNat := handr _ _ (fun h => hp10 (-7) (h))
  have e34140 : (x (-8) 3 && x (-8) 11).toNat = (x (-8) 11).toNat := handr _ _ (fun h => hp11 (-8) (h))
  have e34141 : (x (-9) 4 && x (-9) 12).toNat = (x (-9) 4).toNat := handl _ _ (fun h => hp4 (-9) (h))
  have e34142 : (x (-10) 5 && x (-10) 13).toNat = (x (-10) 5).toNat := handl _ _ (fun h => hp5 (-10) (h))
  have e34143 : (x (-11) 6 && x (-11) 14).toNat = (x (-11) 6).toNat := handl _ _ (fun h => hp6 (-11) (h))
  have r34144 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e34145 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
  have e34146 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
  have e34147 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
  have e34148 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
  have e34149 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
  have e34150 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
  have r34151 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e34152 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
  have e34153 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
  have e34154 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
  have e34155 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
  have e34156 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
  have e34157 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
  have r34158 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e34159 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
  have e34160 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
  have e34161 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
  have e34162 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
  have e34163 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
  have e34164 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
  have r34165 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e34166 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
  have e34167 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
  have e34168 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
  have e34169 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
  have e34170 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
  have e34171 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
  have r34172 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e34173 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
  have e34174 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
  have e34175 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
  have e34176 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
  have e34177 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
  have e34178 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
  have r34179 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e34180 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
  have e34181 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
  have r34182 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e34183 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
  have e34184 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
  have r34185 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e34186 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
  have e34187 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
  have r34188 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r34189 : 1 ≤ (x 8 4).toNat + (x 7 1 && x 7 5).toNat + (x 6 2 && x 6 6).toNat + (x 5 3 && x 5 7).toNat + (x 4 4 && x 4 8).toNat + (x 3 5 && x 3 9).toNat + (x 2 6 && x 2 10).toNat + (x 1 7 && x 1 11).toNat + (x 0 8 && x 0 12).toNat + (x (-1) 9 && x (-1) 13).toNat + (x (-2) 10 && x (-2) 14).toNat + (x (-3) 11).toNat := by have q := hcov4 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e34190 : (x 7 1 && x 7 5).toNat = (x 7 5).toNat := handr _ _ (fun h => hp13 7 (hp5 7 (h)))
  have e34191 : (x (-2) 10 && x (-2) 14).toNat = (x (-2) 10).toNat := handl _ _ (fun h => hp2 (-2) (hp10 (-2) (h)))
  have r34192 : 1 ≤ (x 3 5).toNat + (x 2 1 && x 2 6).toNat + (x 1 2 && x 1 7).toNat + (x 0 3 && x 0 8).toNat + (x (-1) 4 && x (-1) 9).toNat + (x (-2) 5 && x (-2) 10).toNat + (x (-3) 6 && x (-3) 11).toNat + (x (-4) 7 && x (-4) 12).toNat + (x (-5) 8 && x (-5) 13).toNat + (x (-6) 9 && x (-6) 14).toNat + (x (-7) 10).toNat := by have q := hcov5 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r34193 : 1 ≤ (x 7 5).toNat + (x 6 1 && x 6 6).toNat + (x 5 2 && x 5 7).toNat + (x 4 3 && x 4 8).toNat + (x 3 4 && x 3 9).toNat + (x 2 5 && x 2 10).toNat + (x 1 6 && x 1 11).toNat + (x 0 7 && x 0 12).toNat + (x (-1) 8 && x (-1) 13).toNat + (x (-2) 9 && x (-2) 14).toNat + (x (-3) 10).toNat := by have q := hcov5 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r34194 : 1 ≤ (x 4 7).toNat + (x 3 1 && x 3 8).toNat + (x 2 2 && x 2 9).toNat + (x 1 3 && x 1 10).toNat + (x 0 4 && x 0 11).toNat + (x (-1) 5 && x (-1) 12).toNat + (x (-2) 6 && x (-2) 13).toNat + (x (-3) 7 && x (-3) 14).toNat + (x (-4) 8).toNat := by have q := hcov7 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r34195 : 1 ≤ (x (-5) 9).toNat + (x (-6) 1 && x (-6) 10).toNat + (x (-7) 2 && x (-7) 11).toNat + (x (-8) 3 && x (-8) 12).toNat + (x (-9) 4 && x (-9) 13).toNat + (x (-10) 5 && x (-10) 14).toNat + (x (-11) 6).toNat := by have q := hcov9 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r34196 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r34197 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r34198 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r34199 : 1 ≤ (x 11 9).toNat + (x 10 1 && x 10 10).toNat + (x 9 2 && x 9 11).toNat + (x 8 3 && x 8 12).toNat + (x 7 4 && x 7 13).toNat + (x 6 5 && x 6 14).toNat + (x 5 6).toNat := by have q := hcov9 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r34200 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r34201 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r34202 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r34203 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r34204 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
  have r34205 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
  have r34206 : (x (-3) 6).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp6 (-3))
  have r34207 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
  have r34208 : (x 7 5).toNat ≤ (x 7 13).toNat := himp _ _ (hp5 7)
  have r34209 := hand1 (x 6 2) (x 6 6)
  have r34210 := hand1 (x 5 3) (x 5 7)
  have r34211 := hand1 (x (-4) 7) (x (-4) 12)
  have r34212 := hand1 (x (-6) 9) (x (-6) 14)
  have r34213 := hand2 (x 6 1) (x 6 6)
  have r34214 := hand2 (x 5 2) (x 5 7)
  have r34215 := hand1 (x (-2) 9) (x (-2) 14)
  have r34216 := hand2 (x 3 1) (x 3 8)
  have r34217 := hand1 (x (-8) 3) (x (-8) 12)
  have r34218 := hand1 (x (-9) 4) (x (-9) 13)
  have r34219 := hand1 (x (-10) 5) (x (-10) 14)
  have r34220 := hand1 (x (-4) 3) (x (-4) 12)
  have r34221 := hand1 (x (-6) 5) (x (-6) 14)
  have r34222 := hand2 (x (-4) 4) (x (-4) 13)
  have r34223 := hand1 (x (-2) 5) (x (-2) 14)
  have r34224 := hand2 (x 10 1) (x 10 10)
  have r34225 := hand2 (x 9 2) (x 9 11)
  have r34226 := hand2 (x 8 3) (x 8 12)
  have r34227 := hand1 (x 7 4) (x 7 13)
  have r34228 := hand1 (x 6 5) (x 6 14)
  have r34229 := hand1 (x (-3) 2) (x (-3) 12)
  have r34230 := hand1 (x (-4) 3) (x (-4) 13)
  have r34231 := hand1 (x (-5) 4) (x (-5) 14)
  have r34232 := hand1 (x (-3) 4) (x (-3) 14)
  have r34233 := hand1 (x 7 1) (x 7 12)
  have r34234 := hand1 (x 6 2) (x 6 13)
  have r34235 := hand1 (x 5 3) (x 5 14)
  have r34236 := hand2 (x (-6) 1) (x (-6) 14)
  linarith only [r34135, r34136, r34137, e34138, e34139, e34140, e34141, e34142, e34143, r34144, e34145, e34146, e34147, e34148, e34149, e34150, r34151, e34152, e34153, e34154, e34155, e34156, e34157, r34158, e34159, e34160, e34161, e34162, e34163, e34164, r34165, e34166, e34167, e34168, e34169, e34170, e34171, r34172, e34173, e34174, e34175, e34176, e34177, e34178, r34179, e34180, e34181, r34182, e34183, e34184, r34185, e34186, e34187, r34188, r34189, e34190, e34191, r34192, r34193, r34194, r34195, r34196, r34197, r34198, r34199, r34200, r34201, r34202, r34203, r34204, r34205, r34206, r34207, r34208, r34209, r34210, r34211, r34212, r34213, r34214, r34215, r34216, r34217, r34218, r34219, r34220, r34221, r34222, r34223, r34224, r34225, r34226, r34227, r34228, r34229, r34230, r34231, r34232, r34233, r34234, r34235, r34236, d34091, d34119, d34075, d34043, d34039, g0, g1, g2, g3, g4, g5, g6, g7, g9, d34099, d34020, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, d34115, g21, g22, g23, d34016, g24, g25, g26, d34055, g27, g28, g29, g30, g31, g32, g33, g34, d34028, g35, g36, g37, d34079, d34095, g38, g39, d34051, g40, g41, g42, d34063, g43, g44, d34012, g45, g46, d34024, g47, g48]

theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt111010 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 7).toNat = 0)
    (g1 : (x (-3) 11).toNat = 0)
    (g2 : (x (-2) 6).toNat = 0)
    (g3 : (x (-2) 10).toNat = 0)
    (g4 : (x (-2) 11).toNat = 0)
    (g5 : (x (-1) 5).toNat = 0)
    (g6 : (x (-1) 9).toNat = 0)
    (g7 : (x (-1) 10).toNat = 0)
    (g8 : (x 0 3).toNat = 0)
    (g9 : (x 0 4).toNat = 1)
    (g10 : (x 1 3).toNat = 0)
    (g11 : (x 1 10).toNat = 0)
    (g12 : (x 2 2).toNat = 0)
    (g13 : (x 2 6).toNat = 0)
    (g14 : (x 3 1).toNat = 1)
    (g15 : (x 3 9).toNat = 0)
    (g16 : (x 4 4).toNat = 0)
    (g17 : (x 4 4 && x 4 8).toNat = 0)
    (g18 : (x 3 5 && x 3 9).toNat = 0)
    (g19 : (x 2 6 && x 2 10).toNat = 0)
    (g20 : (x 1 7 && x 1 11).toNat = 0)
    (g21 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g22 : (x 2 1 && x 2 6).toNat = 0)
    (g23 : (x 1 2 && x 1 7).toNat = 0)
    (g24 : (x (-1) 4 && x (-1) 9).toNat = 0)
    (g25 : (x (-2) 5 && x (-2) 10).toNat = 0)
    (g26 : (x (-3) 6 && x (-3) 11).toNat = 0)
    (g27 : (x 4 3 && x 4 8).toNat = 0)
    (g28 : (x 3 4 && x 3 9).toNat = 0)
    (g29 : (x 2 5 && x 2 10).toNat = 0)
    (g30 : (x 1 6 && x 1 11).toNat = 0)
    (g31 : (x 0 7 && x 0 12).toNat = 0)
    (g32 : (x (-1) 8 && x (-1) 13).toNat = 0)
    (g33 : (x 2 2 && x 2 9).toNat = 0)
    (g34 : (x 1 3 && x 1 10).toNat = 0)
    (g35 : (x (-1) 5 && x (-1) 12).toNat = 0)
    (g36 : (x (-2) 6 && x (-2) 13).toNat = 0)
    (g37 : (x (-3) 7 && x (-3) 14).toNat = 0)
    (g38 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g39 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g40 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g41 : (x (-2) 2 && x (-2) 11).toNat = 0)
    (g42 : (x (-3) 3 && x (-3) 12).toNat = 0)
    (g43 : (x 2 1 && x 2 10).toNat = 0)
    (g44 : (x 1 2 && x 1 11).toNat = 0)
    (g45 : (x (-1) 4 && x (-1) 13).toNat = 0)
    (g46 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g47 : (x (-1) 2 && x (-1) 12).toNat = 0)
    (g48 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g49 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g50 : (x (-2) 2 && x (-2) 13).toNat = 0)
    (g51 : (x (-3) 3 && x (-3) 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt111010_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51
