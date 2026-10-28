import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b001

Topic: combinatorics   Node: fe575735c675

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_six_iff_seven_core: under the layer-free tight-cover constraints for k = 15 and 25 fixed bits of the class-type sequence near position 0, the constraints are contradictory. Its module also proves the sibling branches cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b0001.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b0001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 4).toNat = 1)
    (g1 : (x 0 5).toNat = 0)
    (g2 : (x 0 8).toNat = 0)
    (g3 : (x 0 9).toNat = 0)
    (g4 : (x 0 13).toNat = 0)
    (g5 : (x 5 10).toNat = 0)
    (g6 : (x 0 1 && x 0 11).toNat = 0)
    (g7 : (x 0 3 && x 0 13).toNat = 0)
    (g8 : (x 4 1 && x 4 11).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d6982 : (x 0 12).toNat = 1 := by
    have r6983 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
    have b6984 := hb (x 0 4)
    have b6985 := hb (x 0 12)
    clear * - r6983 b6984 b6985 g0
    omega
  have d6986 : (x (-1) 13).toNat = 0 := by
    have r6987 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6988 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e6989 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b6990 := hb (x (-3) 3)
    have b6991 := hb (x (-2) 2)
    have b6992 := hb (x (-1) 13)
    have b6993 := hb (x 0 12)
    clear * - r6987 e6988 e6989 b6990 b6991 b6992 b6993 d6982
    omega
  have d6994 : (x (-1) 4 && x (-1) 13).toNat = 0 := by
    have r6995 := hand2 (x (-1) 4) (x (-1) 13)
    have b6996 := hb (x (-1) 13)
    have b6997 := hb (x (-1) 4 && x (-1) 13)
    clear * - r6995 b6996 b6997 d6986
    omega
  have d6998 : (x (-1) 5).toNat = 0 := by
    have r6999 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
    have b7000 := hb (x (-1) 5)
    have b7001 := hb (x (-1) 13)
    clear * - r6999 b7000 b7001 d6986
    omega
  have d7002 : (x (-2) 2).toNat = 0 := by
    have r7003 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7004 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e7005 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b7006 := hb (x (-3) 3)
    have b7007 := hb (x (-2) 2)
    have b7008 := hb (x (-1) 13)
    have b7009 := hb (x 0 12)
    clear * - r7003 e7004 e7005 b7006 b7007 b7008 b7009 d6982 d6986
    omega
  have d7010 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
    have r7011 := hand1 (x (-2) 2) (x (-2) 13)
    have b7012 := hb (x (-2) 2)
    have b7013 := hb (x (-2) 2 && x (-2) 13)
    clear * - r7011 b7012 b7013 d7002
    omega
  have d7014 : (x (-2) 2 && x (-2) 11).toNat = 0 := by
    have r7015 := hand1 (x (-2) 2) (x (-2) 11)
    have b7016 := hb (x (-2) 2)
    have b7017 := hb (x (-2) 2 && x (-2) 11)
    clear * - r7015 b7016 b7017 d7002
    omega
  have d7018 : (x (-2) 10).toNat = 0 := by
    have r7019 : (x (-2) 10).toNat ≤ (x (-2) 2).toNat := himp _ _ (hp10 (-2))
    have b7020 := hb (x (-2) 2)
    have b7021 := hb (x (-2) 10)
    clear * - r7019 b7020 b7021 d7002
    omega
  have d7022 : (x (-1) 1 && x (-1) 14).toNat = 1 := by
    have r7023 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7024 := hb (x (-2) 2)
    have b7025 := hb (x 0 13)
    have b7026 := hb (x (-1) 1 && x (-1) 14)
    clear * - r7023 b7024 b7025 b7026 g4 d7002
    omega
  have d7027 : (x (-1) 14).toNat = 1 := by
    have r7028 := hand2 (x (-1) 1) (x (-1) 14)
    have b7029 := hb (x (-1) 14)
    have b7030 := hb (x (-1) 1 && x (-1) 14)
    clear * - r7028 b7029 b7030 d7022
    omega
  have d7031 : (x (-2) 1).toNat = 0 := by
    have r7032 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7033 := hb (x (-2) 1)
    have b7034 := hb (x (-1) 14)
    clear * - r7032 b7033 b7034 d7027
    omega
  have d7035 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
    have r7036 := hand1 (x (-2) 1) (x (-2) 14)
    have b7037 := hb (x (-2) 1)
    have b7038 := hb (x (-2) 1 && x (-2) 14)
    clear * - r7036 b7037 b7038 d7031
    omega
  have d7039 : (x (-3) 2).toNat = 1 := by
    have r7040 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7041 := hb (x (-3) 2)
    have b7042 := hb (x (-1) 13)
    have b7043 := hb (x (-2) 1 && x (-2) 14)
    clear * - r7040 b7041 b7042 b7043 d6986 d7035
    omega
  have d7044 : (x (-3) 14).toNat = 1 := by
    have r7045 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
    have b7046 := hb (x (-3) 2)
    have b7047 := hb (x (-3) 14)
    clear * - r7045 b7046 b7047 d7039
    omega
  have d7048 : (x (-4) 1).toNat = 0 := by
    have r7049 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7050 := hb (x (-4) 1)
    have b7051 := hb (x (-3) 14)
    clear * - r7049 b7050 b7051 d7044
    omega
  have d7052 : (x (-4) 13).toNat = 0 := by
    have r7053 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
    have b7054 := hb (x (-4) 1)
    have b7055 := hb (x (-4) 13)
    clear * - r7053 b7054 b7055 d7048
    omega
  have d7056 : (x (-4) 4 && x (-4) 13).toNat = 0 := by
    have r7057 := hand2 (x (-4) 4) (x (-4) 13)
    have b7058 := hb (x (-4) 13)
    have b7059 := hb (x (-4) 4 && x (-4) 13)
    clear * - r7057 b7058 b7059 d7052
    omega
  have d7060 : (x (-4) 5).toNat = 0 := by
    have r7061 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
    have b7062 := hb (x (-4) 5)
    have b7063 := hb (x (-4) 13)
    clear * - r7061 b7062 b7063 d7052
    omega
  have d7064 : (x (-2) 13).toNat = 0 := by
    have r7065 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
    have b7066 := hb (x (-2) 1)
    have b7067 := hb (x (-2) 13)
    clear * - r7065 b7066 b7067 d7031
    omega
  have d7068 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
    have r7069 := hand2 (x (-2) 3) (x (-2) 13)
    have b7070 := hb (x (-2) 13)
    have b7071 := hb (x (-2) 3 && x (-2) 13)
    clear * - r7069 b7070 b7071 d7064
    omega
  have d7072 : (x (-2) 5).toNat = 0 := by
    have r7073 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
    have b7074 := hb (x (-2) 5)
    have b7075 := hb (x (-2) 13)
    clear * - r7073 b7074 b7075 d7064
    omega
  have d7076 : (x (-2) 5 && x (-2) 14).toNat = 0 := by
    have r7077 := hand1 (x (-2) 5) (x (-2) 14)
    have b7078 := hb (x (-2) 5)
    have b7079 := hb (x (-2) 5 && x (-2) 14)
    clear * - r7077 b7078 b7079 d7072
    omega
  have d7080 : (x (-3) 3).toNat = 0 := by
    have r7081 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7082 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e7083 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b7084 := hb (x (-3) 3)
    have b7085 := hb (x (-2) 2)
    have b7086 := hb (x (-1) 13)
    have b7087 := hb (x 0 12)
    clear * - r7081 e7082 e7083 b7084 b7085 b7086 b7087 d6982 d6986 d7002
    omega
  have d7088 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
    have r7089 := hand1 (x (-3) 3) (x (-3) 14)
    have b7090 := hb (x (-3) 3)
    have b7091 := hb (x (-3) 3 && x (-3) 14)
    clear * - r7089 b7090 b7091 d7080
    omega
  have d7092 : (x (-3) 3 && x (-3) 12).toNat = 0 := by
    have r7093 := hand1 (x (-3) 3) (x (-3) 12)
    have b7094 := hb (x (-3) 3)
    have b7095 := hb (x (-3) 3 && x (-3) 12)
    clear * - r7093 b7094 b7095 d7080
    omega
  have d7096 : (x (-3) 11).toNat = 0 := by
    have r7097 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
    have b7098 := hb (x (-3) 3)
    have b7099 := hb (x (-3) 11)
    clear * - r7097 b7098 b7099 d7080
    omega
  have d7100 : (x (-1) 12).toNat = 0 := by
    have r7101 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7102 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e7103 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b7104 := hb (x (-4) 3)
    have b7105 := hb (x (-3) 2)
    have b7106 := hb (x (-2) 13)
    have b7107 := hb (x (-1) 12)
    clear * - r7101 e7102 e7103 b7104 b7105 b7106 b7107 d7064 d7039
    omega
  have d7108 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
    have r7109 := hand2 (x (-1) 1) (x (-1) 12)
    have b7110 := hb (x (-1) 12)
    have b7111 := hb (x (-1) 1 && x (-1) 12)
    clear * - r7109 b7110 b7111 d7100
    omega
  have d7112 : (x (-1) 2 && x (-1) 12).toNat = 0 := by
    have r7113 := hand2 (x (-1) 2) (x (-1) 12)
    have b7114 := hb (x (-1) 12)
    have b7115 := hb (x (-1) 2 && x (-1) 12)
    clear * - r7113 b7114 b7115 d7100
    omega
  have d7116 : (x (-1) 4).toNat = 0 := by
    have r7117 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
    have b7118 := hb (x (-1) 4)
    have b7119 := hb (x (-1) 12)
    clear * - r7117 b7118 b7119 d7100
    omega
  have d7120 : (x (-1) 4 && x (-1) 14).toNat = 0 := by
    have r7121 := hand1 (x (-1) 4) (x (-1) 14)
    have b7122 := hb (x (-1) 4)
    have b7123 := hb (x (-1) 4 && x (-1) 14)
    clear * - r7121 b7122 b7123 d7116
    omega
  have d7124 : (x 4 8).toNat = 0 := by
    have r7125 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7126 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e7127 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e7128 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e7129 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e7130 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e7131 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b7132 := hb (x (-3) 7)
    have b7133 := hb (x (-2) 6)
    have b7134 := hb (x (-1) 5)
    have b7135 := hb (x 0 4)
    have b7136 := hb (x 1 11)
    have b7137 := hb (x 2 10)
    have b7138 := hb (x 3 9)
    have b7139 := hb (x 4 8)
    clear * - r7125 e7126 e7127 e7128 e7129 e7130 e7131 b7132 b7133 b7134 b7135 b7136 b7137 b7138 b7139 g0 d6998
    omega
  have d7140 : (x 3 9).toNat = 0 := by
    have r7141 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7142 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e7143 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e7144 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e7145 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e7146 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e7147 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b7148 := hb (x (-3) 7)
    have b7149 := hb (x (-2) 6)
    have b7150 := hb (x (-1) 5)
    have b7151 := hb (x 0 4)
    have b7152 := hb (x 1 11)
    have b7153 := hb (x 2 10)
    have b7154 := hb (x 3 9)
    have b7155 := hb (x 4 8)
    clear * - r7141 e7142 e7143 e7144 e7145 e7146 e7147 b7148 b7149 b7150 b7151 b7152 b7153 b7154 b7155 d7124 g0 d6998
    omega
  have d7156 : (x 2 10).toNat = 0 := by
    have r7157 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7158 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e7159 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e7160 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e7161 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e7162 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e7163 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b7164 := hb (x (-3) 7)
    have b7165 := hb (x (-2) 6)
    have b7166 := hb (x (-1) 5)
    have b7167 := hb (x 0 4)
    have b7168 := hb (x 1 11)
    have b7169 := hb (x 2 10)
    have b7170 := hb (x 3 9)
    have b7171 := hb (x 4 8)
    clear * - r7157 e7158 e7159 e7160 e7161 e7162 e7163 b7164 b7165 b7166 b7167 b7168 b7169 b7170 b7171 d7124 d7140 g0 d6998
    omega
  have d7172 : (x 2 1 && x 2 10).toNat = 0 := by
    have r7173 := hand2 (x 2 1) (x 2 10)
    have b7174 := hb (x 2 10)
    have b7175 := hb (x 2 1 && x 2 10)
    clear * - r7173 b7174 b7175 d7156
    omega
  have d7176 : (x 1 11).toNat = 0 := by
    have r7177 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7178 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e7179 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e7180 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e7181 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e7182 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e7183 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b7184 := hb (x (-3) 7)
    have b7185 := hb (x (-2) 6)
    have b7186 := hb (x (-1) 5)
    have b7187 := hb (x 0 4)
    have b7188 := hb (x 1 11)
    have b7189 := hb (x 2 10)
    have b7190 := hb (x 3 9)
    have b7191 := hb (x 4 8)
    clear * - r7177 e7178 e7179 e7180 e7181 e7182 e7183 b7184 b7185 b7186 b7187 b7188 b7189 b7190 b7191 d7124 d7140 d7156 g0 d6998
    omega
  have d7192 : (x 1 2 && x 1 11).toNat = 0 := by
    have r7193 := hand2 (x 1 2) (x 1 11)
    have b7194 := hb (x 1 11)
    have b7195 := hb (x 1 2 && x 1 11)
    clear * - r7193 b7194 b7195 d7176
    omega
  have r7196 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e7197 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
  have e7198 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
  have e7199 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
  have e7200 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
  have e7201 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
  have e7202 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
  have r7203 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e7204 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
  have e7205 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
  have e7206 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
  have e7207 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
  have e7208 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
  have e7209 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
  have r7210 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e7211 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
  have e7212 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
  have e7213 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
  have e7214 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
  have e7215 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
  have e7216 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
  have r7217 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e7218 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
  have e7219 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
  have e7220 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
  have e7221 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
  have e7222 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
  have e7223 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
  have r7224 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e7225 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
  have e7226 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
  have r7227 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r7228 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r7229 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r7230 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r7231 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r7232 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r7233 := hand2 (x (-1) 1) (x (-1) 10)
  have r7234 := hand1 (x (-5) 5) (x (-5) 14)
  have r7235 := hand1 (x 0 3) (x 0 12)
  have r7236 := hand1 (x (-3) 4) (x (-3) 14)
  have r7237 := hand2 (x 2 1) (x 2 11)
  have r7238 := hand1 (x 1 2) (x 1 12)
  have r7239 := hand2 (x 3 2) (x 3 12)
  have r7240 := hand2 (x 2 3) (x 2 13)
  have r7241 := hand1 (x 1 4) (x 1 14)
  linarith only [r7196, e7197, e7198, e7199, e7200, e7201, e7202, r7203, e7204, e7205, e7206, e7207, e7208, e7209, r7210, e7211, e7212, e7213, e7214, e7215, e7216, r7217, e7218, e7219, e7220, e7221, e7222, e7223, r7224, e7225, e7226, r7227, r7228, r7229, r7230, r7231, r7232, r7233, r7234, r7235, r7236, r7237, r7238, r7239, r7240, r7241, d7060, d7096, d7072, d7018, d7116, g1, g2, g3, d7140, g5, d7014, d7092, d7056, d7172, d7192, d6994, d7076, g6, d7112, d7068, g7, d7120, g8, d7108, d7010, d7088]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b001_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 5).toNat = 0)
    (g1 : (x 0 6).toNat = 0)
    (g2 : (x 0 8).toNat = 0)
    (g3 : (x 0 9).toNat = 0)
    (g4 : (x 0 13).toNat = 0)
    (g5 : (x 0 14).toNat = 1)
    (g6 : (x 1 6).toNat = 0)
    (g7 : (x 3 4).toNat = 0)
    (g8 : (x 4 11).toNat = 0)
    (g9 : (x 5 10).toNat = 0)
    (g10 : (x 6 9).toNat = 0)
    (g11 : (x 0 8 && x 0 12).toNat = 0)
    (g12 : (x 0 8 && x 0 14).toNat = 0)
    (g13 : (x 7 1 && x 7 8).toNat = 0)
    (g14 : (x 6 2 && x 6 9).toNat = 0)
    (g15 : (x 5 3 && x 5 10).toNat = 0)
    (g16 : (x 4 4 && x 4 11).toNat = 0)
    (g17 : (x 5 1 && x 5 10).toNat = 0)
    (g18 : (x 4 2 && x 4 11).toNat = 0)
    (g19 : (x 3 4 && x 3 13).toNat = 0)
    (g20 : (x 2 5 && x 2 14).toNat = 0)
    (g21 : (x 4 1 && x 4 11).toNat = 0)
    (g22 : (x 0 1 && x 0 12).toNat = 0)
    (g23 : (x 0 2 && x 0 13).toNat = 0)
    (g24 : (x 0 1 && x 0 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d7306 : (x (-1) 1).toNat = 0 := by
    have r7307 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7308 := hb (x (-1) 1)
    have b7309 := hb (x 0 14)
    clear * - r7307 b7308 b7309 g5
    omega
  have d7310 : (x (-1) 1 && x (-1) 14).toNat = 0 := by
    have r7311 := hand1 (x (-1) 1) (x (-1) 14)
    have b7312 := hb (x (-1) 1)
    have b7313 := hb (x (-1) 1 && x (-1) 14)
    clear * - r7311 b7312 b7313 d7306
    omega
  have d7314 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
    have r7315 := hand1 (x (-1) 1) (x (-1) 12)
    have b7316 := hb (x (-1) 1)
    have b7317 := hb (x (-1) 1 && x (-1) 12)
    clear * - r7315 b7316 b7317 d7306
    omega
  have d7318 : (x (-1) 1 && x (-1) 10).toNat = 0 := by
    have r7319 := hand1 (x (-1) 1) (x (-1) 10)
    have b7320 := hb (x (-1) 1)
    have b7321 := hb (x (-1) 1 && x (-1) 10)
    clear * - r7319 b7320 b7321 d7306
    omega
  have d7322 : (x (-1) 13).toNat = 0 := by
    have r7323 : (x (-1) 13).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp13 (-1))
    have b7324 := hb (x (-1) 1)
    have b7325 := hb (x (-1) 13)
    clear * - r7323 b7324 b7325 d7306
    omega
  have d7326 : (x (-1) 2 && x (-1) 13).toNat = 0 := by
    have r7327 := hand2 (x (-1) 2) (x (-1) 13)
    have b7328 := hb (x (-1) 13)
    have b7329 := hb (x (-1) 2 && x (-1) 13)
    clear * - r7327 b7328 b7329 d7322
    omega
  have d7330 : (x (-1) 3 && x (-1) 13).toNat = 0 := by
    have r7331 := hand2 (x (-1) 3) (x (-1) 13)
    have b7332 := hb (x (-1) 13)
    have b7333 := hb (x (-1) 3 && x (-1) 13)
    clear * - r7331 b7332 b7333 d7322
    omega
  have d7334 : (x (-1) 9 && x (-1) 13).toNat = 0 := by
    have r7335 := hand2 (x (-1) 9) (x (-1) 13)
    have b7336 := hb (x (-1) 13)
    have b7337 := hb (x (-1) 9 && x (-1) 13)
    clear * - r7335 b7336 b7337 d7322
    omega
  have d7338 : (x (-1) 5).toNat = 0 := by
    have r7339 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
    have b7340 := hb (x (-1) 5)
    have b7341 := hb (x (-1) 13)
    clear * - r7339 b7340 b7341 d7322
    omega
  have d7342 : (x (-1) 9).toNat = 0 := by
    have r7343 : (x (-1) 9).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp9 (-1))
    have b7344 := hb (x (-1) 1)
    have b7345 := hb (x (-1) 9)
    clear * - r7343 b7344 b7345 d7306
    omega
  have d7346 : (x (-2) 2).toNat = 1 := by
    have r7347 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7348 := hb (x (-2) 2)
    have b7349 := hb (x 0 13)
    have b7350 := hb (x (-1) 1 && x (-1) 14)
    clear * - r7347 b7348 b7349 b7350 g4 d7310
    omega
  have d7351 : (x (-2) 14).toNat = 1 := by
    have r7352 : (x (-2) 2).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp2 (-2))
    have b7353 := hb (x (-2) 2)
    have b7354 := hb (x (-2) 14)
    clear * - r7352 b7353 b7354 d7346
    omega
  have d7355 : (x (-3) 1).toNat = 0 := by
    have r7356 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7357 := hb (x (-3) 1)
    have b7358 := hb (x (-2) 14)
    clear * - r7356 b7357 b7358 d7351
    omega
  have d7359 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
    have r7360 := hand1 (x (-3) 1) (x (-3) 14)
    have b7361 := hb (x (-3) 1)
    have b7362 := hb (x (-3) 1 && x (-3) 14)
    clear * - r7360 b7361 b7362 d7355
    omega
  have d7363 : (x (-3) 13).toNat = 0 := by
    have r7364 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
    have b7365 := hb (x (-3) 1)
    have b7366 := hb (x (-3) 13)
    clear * - r7364 b7365 b7366 d7355
    omega
  have d7367 : (x (-3) 2 && x (-3) 13).toNat = 0 := by
    have r7368 := hand2 (x (-3) 2) (x (-3) 13)
    have b7369 := hb (x (-3) 13)
    have b7370 := hb (x (-3) 2 && x (-3) 13)
    clear * - r7368 b7369 b7370 d7363
    omega
  have d7371 : (x (-3) 5).toNat = 0 := by
    have r7372 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
    have b7373 := hb (x (-3) 5)
    have b7374 := hb (x (-3) 13)
    clear * - r7372 b7373 b7374 d7363
    omega
  have d7375 : (x 0 12).toNat = 0 := by
    have r7376 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7377 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e7378 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b7379 := hb (x (-3) 3)
    have b7380 := hb (x (-2) 2)
    have b7381 := hb (x (-1) 13)
    have b7382 := hb (x 0 12)
    clear * - r7376 e7377 e7378 b7379 b7380 b7381 b7382 d7322 d7346
    omega
  have d7383 : (x 0 2 && x 0 12).toNat = 0 := by
    have r7384 := hand2 (x 0 2) (x 0 12)
    have b7385 := hb (x 0 12)
    have b7386 := hb (x 0 2 && x 0 12)
    clear * - r7384 b7385 b7386 d7375
    omega
  have d7387 : (x 0 4).toNat = 0 := by
    have r7388 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
    have b7389 := hb (x 0 4)
    have b7390 := hb (x 0 12)
    clear * - r7388 b7389 b7390 d7375
    omega
  have d7391 : (x 0 4 && x 0 14).toNat = 0 := by
    have r7392 := hand1 (x 0 4) (x 0 14)
    have b7393 := hb (x 0 4)
    have b7394 := hb (x 0 4 && x 0 14)
    clear * - r7392 b7393 b7394 d7387
    omega
  have d7395 : (x (-3) 3).toNat = 0 := by
    have r7396 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7397 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e7398 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b7399 := hb (x (-3) 3)
    have b7400 := hb (x (-2) 2)
    have b7401 := hb (x (-1) 13)
    have b7402 := hb (x 0 12)
    clear * - r7396 e7397 e7398 b7399 b7400 b7401 b7402 d7375 d7322 d7346
    omega
  have d7403 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
    have r7404 := hand1 (x (-3) 3) (x (-3) 14)
    have b7405 := hb (x (-3) 3)
    have b7406 := hb (x (-3) 3 && x (-3) 14)
    clear * - r7404 b7405 b7406 d7395
    omega
  have d7407 : (x (-3) 3 && x (-3) 12).toNat = 0 := by
    have r7408 := hand1 (x (-3) 3) (x (-3) 12)
    have b7409 := hb (x (-3) 3)
    have b7410 := hb (x (-3) 3 && x (-3) 12)
    clear * - r7408 b7409 b7410 d7395
    omega
  have d7411 : (x (-3) 11).toNat = 0 := by
    have r7412 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
    have b7413 := hb (x (-3) 3)
    have b7414 := hb (x (-3) 11)
    clear * - r7412 b7413 b7414 d7395
    omega
  cases h7415 : x 0 2
  · have f7416 : (x 0 2).toNat = 0 := by rw [h7415]; rfl
    have d7417 : (x 0 10).toNat = 0 := by
      have r7418 : (x 0 10).toNat ≤ (x 0 2).toNat := himp _ _ (hp10 0)
      have b7419 := hb (x 0 2)
      have b7420 := hb (x 0 10)
      clear * - r7418 b7419 b7420 f7416
      omega
    cases h7421 : x 0 3
    · have f7422 : (x 0 3).toNat = 0 := by rw [h7421]; rfl
      have d7423 : (x 0 3 && x 0 14).toNat = 0 := by
        have r7424 := hand1 (x 0 3) (x 0 14)
        have b7425 := hb (x 0 3)
        have b7426 := hb (x 0 3 && x 0 14)
        clear * - r7424 b7425 b7426 f7422
        omega
      have d7427 : (x 0 11).toNat = 0 := by
        have r7428 : (x 0 11).toNat ≤ (x 0 3).toNat := himp _ _ (hp11 0)
        have b7429 := hb (x 0 3)
        have b7430 := hb (x 0 11)
        clear * - r7428 b7429 b7430 f7422
        omega
      cases h7431 : x 1 1
      · have f7432 : (x 1 1).toNat = 0 := by rw [h7431]; rfl
        have d7433 : (x 1 1 && x 1 14).toNat = 0 := by
          have r7434 := hand1 (x 1 1) (x 1 14)
          have b7435 := hb (x 1 1)
          have b7436 := hb (x 1 1 && x 1 14)
          clear * - r7434 b7435 b7436 f7432
          omega
        have d7437 : (x 1 1 && x 1 12).toNat = 0 := by
          have r7438 := hand1 (x 1 1) (x 1 12)
          have b7439 := hb (x 1 1)
          have b7440 := hb (x 1 1 && x 1 12)
          clear * - r7438 b7439 b7440 f7432
          omega
        have d7441 : (x 1 13).toNat = 0 := by
          have r7442 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
          have b7443 := hb (x 1 1)
          have b7444 := hb (x 1 13)
          clear * - r7442 b7443 b7444 f7432
          omega
        have d7445 : (x 1 2 && x 1 13).toNat = 0 := by
          have r7446 := hand2 (x 1 2) (x 1 13)
          have b7447 := hb (x 1 13)
          have b7448 := hb (x 1 2 && x 1 13)
          clear * - r7446 b7447 b7448 d7441
          omega
        have d7449 : (x 2 13).toNat = 1 := by
          have r7450 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b7451 := hb (x 0 2)
          have b7452 := hb (x 2 13)
          have b7453 := hb (x 1 1 && x 1 14)
          clear * - r7450 b7451 b7452 b7453 d7433 f7416
          omega
        have d7454 : (x 2 1).toNat = 1 := by
          have r7455 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
          have b7456 := hb (x 2 1)
          have b7457 := hb (x 2 13)
          clear * - r7455 b7456 b7457 d7449
          omega
        have d7458 : (x 3 14).toNat = 0 := by
          have r7459 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b7460 := hb (x 2 1)
          have b7461 := hb (x 3 14)
          clear * - r7459 b7460 b7461 d7454
          omega
        have d7462 : (x 3 1 && x 3 14).toNat = 0 := by
          have r7463 := hand2 (x 3 1) (x 3 14)
          have b7464 := hb (x 3 14)
          have b7465 := hb (x 3 1 && x 3 14)
          clear * - r7463 b7464 b7465 d7458
          omega
        have d7466 : (x 3 2).toNat = 0 := by
          have r7467 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
          have b7468 := hb (x 3 2)
          have b7469 := hb (x 3 14)
          clear * - r7467 b7468 b7469 d7458
          omega
        have d7470 : (x 3 2 && x 3 13).toNat = 0 := by
          have r7471 := hand1 (x 3 2) (x 3 13)
          have b7472 := hb (x 3 2)
          have b7473 := hb (x 3 2 && x 3 13)
          clear * - r7471 b7472 b7473 d7466
          omega
        have d7474 : (x (-1) 2).toNat = 1 := by
          have r7475 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b7476 := hb (x (-1) 2)
          have b7477 := hb (x 1 13)
          have b7478 := hb (x 0 1 && x 0 14)
          clear * - r7475 b7476 b7477 b7478 d7441 g24
          omega
        have d7479 : (x (-1) 14).toNat = 1 := by
          have r7480 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
          have b7481 := hb (x (-1) 2)
          have b7482 := hb (x (-1) 14)
          clear * - r7480 b7481 b7482 d7474
          omega
        have d7483 : (x (-2) 1).toNat = 0 := by
          have r7484 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b7485 := hb (x (-2) 1)
          have b7486 := hb (x (-1) 14)
          clear * - r7484 b7485 b7486 d7479
          omega
        have d7487 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
          have r7488 := hand1 (x (-2) 1) (x (-2) 14)
          have b7489 := hb (x (-2) 1)
          have b7490 := hb (x (-2) 1 && x (-2) 14)
          clear * - r7488 b7489 b7490 d7483
          omega
        have d7491 : (x (-2) 13).toNat = 0 := by
          have r7492 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
          have b7493 := hb (x (-2) 1)
          have b7494 := hb (x (-2) 13)
          clear * - r7492 b7493 b7494 d7483
          omega
        have d7495 : (x (-3) 2).toNat = 1 := by
          have r7496 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b7497 := hb (x (-3) 2)
          have b7498 := hb (x (-1) 13)
          have b7499 := hb (x (-2) 1 && x (-2) 14)
          clear * - r7496 b7497 b7498 b7499 d7322 d7487
          omega
        have d7500 : (x (-3) 14).toNat = 1 := by
          have r7501 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
          have b7502 := hb (x (-3) 2)
          have b7503 := hb (x (-3) 14)
          clear * - r7501 b7502 b7503 d7495
          omega
        have d7504 : (x (-4) 1).toNat = 0 := by
          have r7505 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b7506 := hb (x (-4) 1)
          have b7507 := hb (x (-3) 14)
          clear * - r7505 b7506 b7507 d7500
          omega
        have d7508 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
          have r7509 := hand1 (x (-4) 1) (x (-4) 14)
          have b7510 := hb (x (-4) 1)
          have b7511 := hb (x (-4) 1 && x (-4) 14)
          clear * - r7509 b7510 b7511 d7504
          omega
        have d7512 : (x (-4) 13).toNat = 0 := by
          have r7513 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
          have b7514 := hb (x (-4) 1)
          have b7515 := hb (x (-4) 13)
          clear * - r7513 b7514 b7515 d7504
          omega
        have d7516 : (x (-4) 2).toNat = 1 := by
          have r7517 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b7518 := hb (x (-4) 2)
          have b7519 := hb (x (-2) 13)
          have b7520 := hb (x (-3) 1 && x (-3) 14)
          clear * - r7517 b7518 b7519 b7520 d7491 d7359
          omega
        have d7521 : (x (-5) 2).toNat = 1 := by
          have r7522 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b7523 := hb (x (-5) 2)
          have b7524 := hb (x (-3) 13)
          have b7525 := hb (x (-4) 1 && x (-4) 14)
          clear * - r7522 b7523 b7524 b7525 d7363 d7508
          omega
        have d7526 : (x 1 12).toNat = 0 := by
          have r7527 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e7528 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
          have e7529 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
          have b7530 := hb (x (-2) 3)
          have b7531 := hb (x (-1) 2)
          have b7532 := hb (x 0 13)
          have b7533 := hb (x 1 12)
          clear * - r7527 e7528 e7529 b7530 b7531 b7532 b7533 g4 d7474
          omega
        have d7534 : (x 1 4).toNat = 0 := by
          have r7535 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
          have b7536 := hb (x 1 4)
          have b7537 := hb (x 1 12)
          clear * - r7535 b7536 b7537 d7526
          omega
        have d7538 : (x (-2) 3).toNat = 0 := by
          have r7539 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e7540 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
          have e7541 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
          have b7542 := hb (x (-2) 3)
          have b7543 := hb (x (-1) 2)
          have b7544 := hb (x 0 13)
          have b7545 := hb (x 1 12)
          clear * - r7539 e7540 e7541 b7542 b7543 b7544 b7545 d7526 g4 d7474
          omega
        have d7546 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
          have r7547 := hand1 (x (-2) 3) (x (-2) 14)
          have b7548 := hb (x (-2) 3)
          have b7549 := hb (x (-2) 3 && x (-2) 14)
          clear * - r7547 b7548 b7549 d7538
          omega
        have d7550 : (x (-1) 12).toNat = 0 := by
          have r7551 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e7552 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e7553 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b7554 := hb (x (-4) 3)
          have b7555 := hb (x (-3) 2)
          have b7556 := hb (x (-2) 13)
          have b7557 := hb (x (-1) 12)
          clear * - r7551 e7552 e7553 b7554 b7555 b7556 b7557 d7491 d7495
          omega
        have d7558 : (x (-1) 4).toNat = 0 := by
          have r7559 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
          have b7560 := hb (x (-1) 4)
          have b7561 := hb (x (-1) 12)
          clear * - r7559 b7560 b7561 d7550
          omega
        have d7562 : (x (-2) 12).toNat = 0 := by
          have r7563 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e7564 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
          have e7565 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
          have b7566 := hb (x (-5) 3)
          have b7567 := hb (x (-4) 2)
          have b7568 := hb (x (-3) 13)
          have b7569 := hb (x (-2) 12)
          clear * - r7563 e7564 e7565 b7566 b7567 b7568 b7569 d7363 d7516
          omega
        have d7570 : (x (-2) 4).toNat = 0 := by
          have r7571 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
          have b7572 := hb (x (-2) 4)
          have b7573 := hb (x (-2) 12)
          clear * - r7571 b7572 b7573 d7562
          omega
        have d7574 : (x (-3) 12).toNat = 0 := by
          have r7575 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e7576 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
          have e7577 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
          have b7578 := hb (x (-6) 3)
          have b7579 := hb (x (-5) 2)
          have b7580 := hb (x (-4) 13)
          have b7581 := hb (x (-3) 12)
          clear * - r7575 e7576 e7577 b7578 b7579 b7580 b7581 d7512 d7521
          omega
        have d7582 : (x (-3) 4).toNat = 0 := by
          have r7583 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
          have b7584 := hb (x (-3) 4)
          have b7585 := hb (x (-3) 12)
          clear * - r7583 b7584 b7585 d7574
          omega
        have d7586 : (x 1 11).toNat = 1 := by
          have r7587 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b7588 := hb (x (-3) 4)
          have b7589 := hb (x 1 11)
          have b7590 := hb (x 0 1 && x 0 12)
          have b7591 := hb (x (-1) 2 && x (-1) 13)
          have b7592 := hb (x (-2) 3 && x (-2) 14)
          clear * - r7587 b7588 b7589 b7590 b7591 b7592 g22 d7326 d7546 d7582
          omega
        have d7593 : (x 1 3).toNat = 1 := by
          have r7594 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
          have b7595 := hb (x 1 3)
          have b7596 := hb (x 1 11)
          clear * - r7594 b7595 b7596 d7586
          omega
        have d7597 : (x 4 12).toNat = 0 := by
          have r7598 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e7599 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e7600 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b7601 := hb (x 1 3)
          have b7602 := hb (x 2 2)
          have b7603 := hb (x 3 13)
          have b7604 := hb (x 4 12)
          clear * - r7598 e7599 e7600 b7601 b7602 b7603 b7604 d7593
          omega
        have d7605 : (x 4 1 && x 4 12).toNat = 0 := by
          have r7606 := hand2 (x 4 1) (x 4 12)
          have b7607 := hb (x 4 12)
          have b7608 := hb (x 4 1 && x 4 12)
          clear * - r7606 b7607 b7608 d7597
          omega
        have d7609 : (x 4 4).toNat = 0 := by
          have r7610 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
          have b7611 := hb (x 4 4)
          have b7612 := hb (x 4 12)
          clear * - r7610 b7611 b7612 d7597
          omega
        have d7613 : (x 3 13).toNat = 0 := by
          have r7614 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e7615 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e7616 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b7617 := hb (x 1 3)
          have b7618 := hb (x 2 2)
          have b7619 := hb (x 3 13)
          have b7620 := hb (x 4 12)
          clear * - r7614 e7615 e7616 b7617 b7618 b7619 b7620 d7597 d7593
          omega
        have d7621 : (x 2 2).toNat = 0 := by
          have r7622 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e7623 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e7624 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b7625 := hb (x 1 3)
          have b7626 := hb (x 2 2)
          have b7627 := hb (x 3 13)
          have b7628 := hb (x 4 12)
          clear * - r7622 e7623 e7624 b7625 b7626 b7627 b7628 d7597 d7613 d7593
          omega
        have d7629 : (x 4 13).toNat = 1 := by
          have r7630 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b7631 := hb (x 2 2)
          have b7632 := hb (x 4 13)
          have b7633 := hb (x 3 1 && x 3 14)
          clear * - r7630 b7631 b7632 b7633 d7462 d7621
          omega
        have d7634 : (x 4 1).toNat = 1 := by
          have r7635 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
          have b7636 := hb (x 4 1)
          have b7637 := hb (x 4 13)
          clear * - r7635 b7636 b7637 d7629
          omega
        have d7638 : (x 5 14).toNat = 0 := by
          have r7639 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b7640 := hb (x 4 1)
          have b7641 := hb (x 5 14)
          clear * - r7639 b7640 b7641 d7634
          omega
        have d7642 : (x 5 1 && x 5 14).toNat = 0 := by
          have r7643 := hand2 (x 5 1) (x 5 14)
          have b7644 := hb (x 5 14)
          have b7645 := hb (x 5 1 && x 5 14)
          clear * - r7643 b7644 b7645 d7638
          omega
        have d7646 : (x 5 3 && x 5 14).toNat = 0 := by
          have r7647 := hand2 (x 5 3) (x 5 14)
          have b7648 := hb (x 5 14)
          have b7649 := hb (x 5 3 && x 5 14)
          clear * - r7647 b7648 b7649 d7638
          omega
        have d7650 : (x 5 2).toNat = 0 := by
          have r7651 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
          have b7652 := hb (x 5 2)
          have b7653 := hb (x 5 14)
          clear * - r7651 b7652 b7653 d7638
          omega
        have d7654 : (x 5 2 && x 5 13).toNat = 0 := by
          have r7655 := hand1 (x 5 2) (x 5 13)
          have b7656 := hb (x 5 2)
          have b7657 := hb (x 5 2 && x 5 13)
          clear * - r7655 b7656 b7657 d7650
          omega
        have d7658 : (x 5 12).toNat = 0 := by
          have r7659 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e7660 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e7661 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b7662 := hb (x 2 3)
          have b7663 := hb (x 3 2)
          have b7664 := hb (x 4 13)
          have b7665 := hb (x 5 12)
          clear * - r7659 e7660 e7661 b7662 b7663 b7664 b7665 d7629 d7466
          omega
        have d7666 : (x 5 4).toNat = 0 := by
          have r7667 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
          have b7668 := hb (x 5 4)
          have b7669 := hb (x 5 12)
          clear * - r7667 b7668 b7669 d7658
          omega
        have d7670 : (x 2 3).toNat = 0 := by
          have r7671 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e7672 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e7673 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b7674 := hb (x 2 3)
          have b7675 := hb (x 3 2)
          have b7676 := hb (x 4 13)
          have b7677 := hb (x 5 12)
          clear * - r7671 e7672 e7673 b7674 b7675 b7676 b7677 d7658 d7629 d7466
          omega
        have d7678 : (x 2 3 && x 2 14).toNat = 0 := by
          have r7679 := hand1 (x 2 3) (x 2 14)
          have b7680 := hb (x 2 3)
          have b7681 := hb (x 2 3 && x 2 14)
          clear * - r7679 b7680 b7681 d7670
          omega
        have d7682 : (x 5 11).toNat = 1 := by
          have r7683 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b7684 := hb (x 1 4)
          have b7685 := hb (x 5 11)
          have b7686 := hb (x 4 1 && x 4 12)
          have b7687 := hb (x 3 2 && x 3 13)
          have b7688 := hb (x 2 3 && x 2 14)
          clear * - r7683 b7684 b7685 b7686 b7687 b7688 d7605 d7470 d7678 d7534
          omega
        have d7689 : (x 5 3).toNat = 1 := by
          have r7690 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
          have b7691 := hb (x 5 3)
          have b7692 := hb (x 5 11)
          clear * - r7690 b7691 b7692 d7682
          omega
        have d7693 : (x 8 12).toNat = 0 := by
          have r7694 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e7695 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
          have e7696 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
          have b7697 := hb (x 5 3)
          have b7698 := hb (x 6 2)
          have b7699 := hb (x 7 13)
          have b7700 := hb (x 8 12)
          clear * - r7694 e7695 e7696 b7697 b7698 b7699 b7700 d7689
          omega
        have d7701 : (x 8 1 && x 8 12).toNat = 0 := by
          have r7702 := hand2 (x 8 1) (x 8 12)
          have b7703 := hb (x 8 12)
          have b7704 := hb (x 8 1 && x 8 12)
          clear * - r7702 b7703 b7704 d7693
          omega
        have d7705 : (x 7 13).toNat = 0 := by
          have r7706 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e7707 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
          have e7708 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
          have b7709 := hb (x 5 3)
          have b7710 := hb (x 6 2)
          have b7711 := hb (x 7 13)
          have b7712 := hb (x 8 12)
          clear * - r7706 e7707 e7708 b7709 b7710 b7711 b7712 d7693 d7689
          omega
        have d7713 : (x 7 2 && x 7 13).toNat = 0 := by
          have r7714 := hand2 (x 7 2) (x 7 13)
          have b7715 := hb (x 7 13)
          have b7716 := hb (x 7 2 && x 7 13)
          clear * - r7714 b7715 b7716 d7705
          omega
        have d7717 : (x 6 1 && x 6 14).toNat = 1 := by
          have r7718 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b7719 := hb (x 5 2)
          have b7720 := hb (x 7 13)
          have b7721 := hb (x 6 1 && x 6 14)
          clear * - r7718 b7719 b7720 b7721 d7705 d7650
          omega
        have d7722 : (x 6 14).toNat = 1 := by
          have r7723 := hand2 (x 6 1) (x 6 14)
          have b7724 := hb (x 6 14)
          have b7725 := hb (x 6 1 && x 6 14)
          clear * - r7723 b7724 b7725 d7717
          omega
        have d7726 : (x 5 1).toNat = 0 := by
          have r7727 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b7728 := hb (x 5 1)
          have b7729 := hb (x 6 14)
          clear * - r7727 b7728 b7729 d7722
          omega
        have d7730 : (x 5 13).toNat = 0 := by
          have r7731 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
          have b7732 := hb (x 5 1)
          have b7733 := hb (x 5 13)
          clear * - r7731 b7732 b7733 d7726
          omega
        have d7734 : (x 6 1).toNat = 1 := by
          have r7735 := hand1 (x 6 1) (x 6 14)
          have b7736 := hb (x 6 1)
          have b7737 := hb (x 6 1 && x 6 14)
          clear * - r7735 b7736 b7737 d7717
          omega
        have d7738 : (x 7 14).toNat = 0 := by
          have r7739 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b7740 := hb (x 6 1)
          have b7741 := hb (x 7 14)
          clear * - r7739 b7740 b7741 d7734
          omega
        have d7742 : (x 7 1 && x 7 14).toNat = 0 := by
          have r7743 := hand2 (x 7 1) (x 7 14)
          have b7744 := hb (x 7 14)
          have b7745 := hb (x 7 1 && x 7 14)
          clear * - r7743 b7744 b7745 d7738
          omega
        have d7746 : (x 7 2).toNat = 0 := by
          have r7747 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
          have b7748 := hb (x 7 2)
          have b7749 := hb (x 7 14)
          clear * - r7747 b7748 b7749 d7738
          omega
        have d7750 : (x 6 2).toNat = 0 := by
          have r7751 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e7752 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
          have e7753 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
          have b7754 := hb (x 5 3)
          have b7755 := hb (x 6 2)
          have b7756 := hb (x 7 13)
          have b7757 := hb (x 8 12)
          clear * - r7751 e7752 e7753 b7754 b7755 b7756 b7757 d7693 d7705 d7689
          omega
        have d7758 : (x 6 2 && x 6 13).toNat = 0 := by
          have r7759 := hand1 (x 6 2) (x 6 13)
          have b7760 := hb (x 6 2)
          have b7761 := hb (x 6 2 && x 6 13)
          clear * - r7759 b7760 b7761 d7750
          omega
        have d7762 : (x 8 13).toNat = 1 := by
          have r7763 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b7764 := hb (x 6 2)
          have b7765 := hb (x 8 13)
          have b7766 := hb (x 7 1 && x 7 14)
          clear * - r7763 b7764 b7765 b7766 d7742 d7750
          omega
        have d7767 : (x 8 1).toNat = 1 := by
          have r7768 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
          have b7769 := hb (x 8 1)
          have b7770 := hb (x 8 13)
          clear * - r7768 b7769 b7770 d7762
          omega
        have d7771 : (x 9 14).toNat = 0 := by
          have r7772 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b7773 := hb (x 8 1)
          have b7774 := hb (x 9 14)
          clear * - r7772 b7773 b7774 d7767
          omega
        have d7775 : (x 9 1 && x 9 14).toNat = 0 := by
          have r7776 := hand2 (x 9 1) (x 9 14)
          have b7777 := hb (x 9 14)
          have b7778 := hb (x 9 1 && x 9 14)
          clear * - r7776 b7777 b7778 d7771
          omega
        have d7779 : (x 9 2).toNat = 0 := by
          have r7780 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
          have b7781 := hb (x 9 2)
          have b7782 := hb (x 9 14)
          clear * - r7780 b7781 b7782 d7771
          omega
        have d7783 : (x 9 12).toNat = 0 := by
          have r7784 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e7785 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
          have e7786 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
          have b7787 := hb (x 6 3)
          have b7788 := hb (x 7 2)
          have b7789 := hb (x 8 13)
          have b7790 := hb (x 9 12)
          clear * - r7784 e7785 e7786 b7787 b7788 b7789 b7790 d7762 d7746
          omega
        have d7791 : (x 6 3).toNat = 0 := by
          have r7792 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e7793 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
          have e7794 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
          have b7795 := hb (x 6 3)
          have b7796 := hb (x 7 2)
          have b7797 := hb (x 8 13)
          have b7798 := hb (x 9 12)
          clear * - r7792 e7793 e7794 b7795 b7796 b7797 b7798 d7783 d7762 d7746
          omega
        have d7799 : (x 6 3 && x 6 14).toNat = 0 := by
          have r7800 := hand1 (x 6 3) (x 6 14)
          have b7801 := hb (x 6 3)
          have b7802 := hb (x 6 3 && x 6 14)
          clear * - r7800 b7801 b7802 d7791
          omega
        have d7803 : (x 9 11).toNat = 1 := by
          have r7804 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b7805 := hb (x 5 4)
          have b7806 := hb (x 9 11)
          have b7807 := hb (x 8 1 && x 8 12)
          have b7808 := hb (x 7 2 && x 7 13)
          have b7809 := hb (x 6 3 && x 6 14)
          clear * - r7804 b7805 b7806 b7807 b7808 b7809 d7701 d7713 d7799 d7666
          omega
        have d7810 : (x 9 3).toNat = 1 := by
          have r7811 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
          have b7812 := hb (x 9 3)
          have b7813 := hb (x 9 11)
          clear * - r7811 b7812 b7813 d7803
          omega
        have d7814 : (x 12 12).toNat = 0 := by
          have r7815 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e7816 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
          have e7817 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
          have b7818 := hb (x 9 3)
          have b7819 := hb (x 10 2)
          have b7820 := hb (x 11 13)
          have b7821 := hb (x 12 12)
          clear * - r7815 e7816 e7817 b7818 b7819 b7820 b7821 d7810
          omega
        have d7822 : (x 11 13).toNat = 0 := by
          have r7823 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e7824 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
          have e7825 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
          have b7826 := hb (x 9 3)
          have b7827 := hb (x 10 2)
          have b7828 := hb (x 11 13)
          have b7829 := hb (x 12 12)
          clear * - r7823 e7824 e7825 b7826 b7827 b7828 b7829 d7814 d7810
          omega
        have d7830 : (x 10 1 && x 10 14).toNat = 1 := by
          have r7831 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b7832 := hb (x 9 2)
          have b7833 := hb (x 11 13)
          have b7834 := hb (x 10 1 && x 10 14)
          clear * - r7831 b7832 b7833 b7834 d7822 d7779
          omega
        have d7835 : (x 10 14).toNat = 1 := by
          have r7836 := hand2 (x 10 1) (x 10 14)
          have b7837 := hb (x 10 14)
          have b7838 := hb (x 10 1 && x 10 14)
          clear * - r7836 b7837 b7838 d7830
          omega
        have d7839 : (x 9 1).toNat = 0 := by
          have r7840 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b7841 := hb (x 9 1)
          have b7842 := hb (x 10 14)
          clear * - r7840 b7841 b7842 d7835
          omega
        have d7843 : (x 9 13).toNat = 0 := by
          have r7844 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
          have b7845 := hb (x 9 1)
          have b7846 := hb (x 9 13)
          clear * - r7844 b7845 b7846 d7839
          omega
        have d7847 : (x 8 1 && x 8 14).toNat = 1 := by
          have r7848 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b7849 := hb (x 7 2)
          have b7850 := hb (x 9 13)
          have b7851 := hb (x 8 1 && x 8 14)
          clear * - r7848 b7849 b7850 b7851 d7843 d7746
          omega
        have d7852 : (x 8 14).toNat = 1 := by
          have r7853 := hand2 (x 8 1) (x 8 14)
          have b7854 := hb (x 8 14)
          have b7855 := hb (x 8 1 && x 8 14)
          clear * - r7853 b7854 b7855 d7847
          omega
        have d7856 : (x 7 1).toNat = 0 := by
          have r7857 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b7858 := hb (x 7 1)
          have b7859 := hb (x 8 14)
          clear * - r7857 b7858 b7859 d7852
          omega
        have d7860 : (x 7 1 && x 7 12).toNat = 0 := by
          have r7861 := hand1 (x 7 1) (x 7 12)
          have b7862 := hb (x 7 1)
          have b7863 := hb (x 7 1 && x 7 12)
          clear * - r7861 b7862 b7863 d7856
          omega
        have d7864 : (x 8 11).toNat = 1 := by
          have r7865 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b7866 := hb (x 4 4)
          have b7867 := hb (x 8 11)
          have b7868 := hb (x 7 1 && x 7 12)
          have b7869 := hb (x 6 2 && x 6 13)
          have b7870 := hb (x 5 3 && x 5 14)
          clear * - r7865 b7866 b7867 b7868 b7869 b7870 d7860 d7758 d7646 d7609
          omega
        have d7871 : (x 8 3).toNat = 1 := by
          have r7872 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
          have b7873 := hb (x 8 3)
          have b7874 := hb (x 8 11)
          clear * - r7872 b7873 b7874 d7864
          omega
        have d7875 : (x 11 12).toNat = 0 := by
          have r7876 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e7877 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e7878 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have b7879 := hb (x 8 3)
          have b7880 := hb (x 9 2)
          have b7881 := hb (x 10 13)
          have b7882 := hb (x 11 12)
          clear * - r7876 e7877 e7878 b7879 b7880 b7881 b7882 d7779 d7871
          omega
        have d7883 : (x 10 13).toNat = 0 := by
          have r7884 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e7885 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e7886 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have b7887 := hb (x 8 3)
          have b7888 := hb (x 9 2)
          have b7889 := hb (x 10 13)
          have b7890 := hb (x 11 12)
          clear * - r7884 e7885 e7886 b7887 b7888 b7889 b7890 d7875 d7779 d7871
          omega
        have d7891 : (x 8 2).toNat = 1 := by
          have r7892 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b7893 := hb (x 8 2)
          have b7894 := hb (x 10 13)
          have b7895 := hb (x 9 1 && x 9 14)
          clear * - r7892 b7893 b7894 b7895 d7883 d7775
          omega
        have d7896 : (x 10 12).toNat = 0 := by
          have r7897 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e7898 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
          have e7899 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
          have b7900 := hb (x 7 3)
          have b7901 := hb (x 8 2)
          have b7902 := hb (x 9 13)
          have b7903 := hb (x 10 12)
          clear * - r7897 e7898 e7899 b7900 b7901 b7902 b7903 d7843 d7891
          omega
        have d7904 : (x 7 3).toNat = 0 := by
          have r7905 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e7906 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
          have e7907 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
          have b7908 := hb (x 7 3)
          have b7909 := hb (x 8 2)
          have b7910 := hb (x 9 13)
          have b7911 := hb (x 10 12)
          clear * - r7905 e7906 e7907 b7908 b7909 b7910 b7911 d7896 d7843 d7891
          omega
        have d7912 : (x 7 11).toNat = 0 := by
          have r7913 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
          have b7914 := hb (x 7 3)
          have b7915 := hb (x 7 11)
          clear * - r7913 b7914 b7915 d7904
          omega
        have d7916 : (x 2 11).toNat = 0 := by
          have r7917 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
          have b7918 := hb (x 2 3)
          have b7919 := hb (x 2 11)
          clear * - r7917 b7918 b7919 d7670
          omega
        have d7920 : (x (-1) 3 && x (-1) 14).toNat = 1 := by
          have r7921 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := by have q := hcov11 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b7922 := hb (x (-2) 4)
          have b7923 := hb (x 2 11)
          have b7924 := hb (x 1 1 && x 1 12)
          have b7925 := hb (x 0 2 && x 0 13)
          have b7926 := hb (x (-1) 3 && x (-1) 14)
          clear * - r7921 b7922 b7923 b7924 b7925 b7926 d7916 d7437 g23 d7570
          omega
        have d7927 : (x (-1) 3).toNat = 1 := by
          have r7928 := hand1 (x (-1) 3) (x (-1) 14)
          have b7929 := hb (x (-1) 3)
          have b7930 := hb (x (-1) 3 && x (-1) 14)
          clear * - r7928 b7929 b7930 d7920
          omega
        have d7931 : (x 2 12).toNat = 0 := by
          have r7932 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e7933 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
          have e7934 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
          have b7935 := hb (x (-1) 3)
          have b7936 := hb (x 0 2)
          have b7937 := hb (x 1 13)
          have b7938 := hb (x 2 12)
          clear * - r7932 e7933 e7934 b7935 b7936 b7937 b7938 d7441 f7416 d7927
          omega
        have d7939 : (x 2 1 && x 2 12).toNat = 0 := by
          have r7940 := hand2 (x 2 1) (x 2 12)
          have b7941 := hb (x 2 12)
          have b7942 := hb (x 2 1 && x 2 12)
          clear * - r7940 b7941 b7942 d7931
          omega
        have d7943 : (x 3 11).toNat = 1 := by
          have r7944 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b7945 := hb (x (-1) 4)
          have b7946 := hb (x 3 11)
          have b7947 := hb (x 2 1 && x 2 12)
          have b7948 := hb (x 1 2 && x 1 13)
          have b7949 := hb (x 0 3 && x 0 14)
          clear * - r7944 b7945 b7946 b7947 b7948 b7949 d7939 d7445 d7423 d7558
          omega
        have d7950 : (x 3 3).toNat = 1 := by
          have r7951 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
          have b7952 := hb (x 3 3)
          have b7953 := hb (x 3 11)
          clear * - r7951 b7952 b7953 d7943
          omega
        have d7954 : (x 6 12).toNat = 0 := by
          have r7955 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e7956 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e7957 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b7958 := hb (x 3 3)
          have b7959 := hb (x 4 2)
          have b7960 := hb (x 5 13)
          have b7961 := hb (x 6 12)
          clear * - r7955 e7956 e7957 b7958 b7959 b7960 b7961 d7730 d7950
          omega
        have d7962 : (x 6 1 && x 6 12).toNat = 0 := by
          have r7963 := hand2 (x 6 1) (x 6 12)
          have b7964 := hb (x 6 12)
          have b7965 := hb (x 6 1 && x 6 12)
          clear * - r7963 b7964 b7965 d7954
          omega
        have d7966 : (x 4 3 && x 4 14).toNat = 1 := by
          have r7967 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b7968 := hb (x 3 4)
          have b7969 := hb (x 7 11)
          have b7970 := hb (x 6 1 && x 6 12)
          have b7971 := hb (x 5 2 && x 5 13)
          have b7972 := hb (x 4 3 && x 4 14)
          clear * - r7967 b7968 b7969 b7970 b7971 b7972 d7912 d7962 d7654 g7
          omega
        have d7973 : (x 4 3).toNat = 1 := by
          have r7974 := hand1 (x 4 3) (x 4 14)
          have b7975 := hb (x 4 3)
          have b7976 := hb (x 4 3 && x 4 14)
          clear * - r7974 b7975 b7976 d7966
          omega
        have d7977 : (x 7 12).toNat = 0 := by
          have r7978 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e7979 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
          have e7980 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
          have b7981 := hb (x 4 3)
          have b7982 := hb (x 5 2)
          have b7983 := hb (x 6 13)
          have b7984 := hb (x 7 12)
          clear * - r7978 e7979 e7980 b7981 b7982 b7983 b7984 d7650 d7973
          omega
        have d7985 : (x 6 13).toNat = 0 := by
          have r7986 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e7987 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
          have e7988 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
          have b7989 := hb (x 4 3)
          have b7990 := hb (x 5 2)
          have b7991 := hb (x 6 13)
          have b7992 := hb (x 7 12)
          clear * - r7986 e7987 e7988 b7989 b7990 b7991 b7992 d7977 d7650 d7973
          omega
        have d7993 : (x 4 2).toNat = 1 := by
          have r7994 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b7995 := hb (x 4 2)
          have b7996 := hb (x 6 13)
          have b7997 := hb (x 5 1 && x 5 14)
          clear * - r7994 b7995 b7996 b7997 d7985 d7642
          omega
        have r7998 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e7999 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
        have e8000 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
        have b8001 := hb (x 3 3)
        have b8002 := hb (x 4 2)
        have b8003 := hb (x 5 13)
        have b8004 := hb (x 6 12)
        linarith only [r7998, e7999, e8000, b8001, b8002, b8003, b8004, d7954, d7730, d7993, d7950]
      · have f8005 : (x 1 1).toNat = 1 := by rw [h7431]; rfl
        have d8006 : (x 2 14).toNat = 0 := by
          have r8007 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b8008 := hb (x 1 1)
          have b8009 := hb (x 2 14)
          clear * - r8007 b8008 b8009 f8005
          omega
        have d8010 : (x 2 1 && x 2 14).toNat = 0 := by
          have r8011 := hand2 (x 2 1) (x 2 14)
          have b8012 := hb (x 2 14)
          have b8013 := hb (x 2 1 && x 2 14)
          clear * - r8011 b8012 b8013 d8006
          omega
        have d8014 : (x 2 6).toNat = 0 := by
          have r8015 : (x 2 6).toNat ≤ (x 2 14).toNat := himp _ _ (hp6 2)
          have b8016 := hb (x 2 6)
          have b8017 := hb (x 2 14)
          clear * - r8015 b8016 b8017 d8006
          omega
        have d8018 : (x 2 6 && x 2 13).toNat = 0 := by
          have r8019 := hand1 (x 2 6) (x 2 13)
          have b8020 := hb (x 2 6)
          have b8021 := hb (x 2 6 && x 2 13)
          clear * - r8019 b8020 b8021 d8014
          omega
        have d8022 : (x 2 6 && x 2 12).toNat = 0 := by
          have r8023 := hand1 (x 2 6) (x 2 12)
          have b8024 := hb (x 2 6)
          have b8025 := hb (x 2 6 && x 2 12)
          clear * - r8023 b8024 b8025 d8014
          omega
        have d8026 : (x 2 6 && x 2 10).toNat = 0 := by
          have r8027 := hand1 (x 2 6) (x 2 10)
          have b8028 := hb (x 2 6)
          have b8029 := hb (x 2 6 && x 2 10)
          clear * - r8027 b8028 b8029 d8014
          omega
        have d8030 : (x 2 2).toNat = 0 := by
          have r8031 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
          have b8032 := hb (x 2 2)
          have b8033 := hb (x 2 14)
          clear * - r8031 b8032 b8033 d8006
          omega
        have d8034 : (x 2 2 && x 2 13).toNat = 0 := by
          have r8035 := hand1 (x 2 2) (x 2 13)
          have b8036 := hb (x 2 2)
          have b8037 := hb (x 2 2 && x 2 13)
          clear * - r8035 b8036 b8037 d8030
          omega
        have d8038 : (x 2 2 && x 2 12).toNat = 0 := by
          have r8039 := hand1 (x 2 2) (x 2 12)
          have b8040 := hb (x 2 2)
          have b8041 := hb (x 2 2 && x 2 12)
          clear * - r8039 b8040 b8041 d8030
          omega
        have d8042 : (x 2 10).toNat = 0 := by
          have r8043 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
          have b8044 := hb (x 2 2)
          have b8045 := hb (x 2 10)
          clear * - r8043 b8044 b8045 d8030
          omega
        cases h8046 : x (-1) 2
        · have f8047 : (x (-1) 2).toNat = 0 := by rw [h8046]; rfl
          have d8048 : (x (-1) 10).toNat = 0 := by
            have r8049 : (x (-1) 10).toNat ≤ (x (-1) 2).toNat := himp _ _ (hp10 (-1))
            have b8050 := hb (x (-1) 2)
            have b8051 := hb (x (-1) 10)
            clear * - r8049 b8050 b8051 f8047
            omega
          have d8052 : (x 1 13).toNat = 1 := by
            have r8053 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b8054 := hb (x (-1) 2)
            have b8055 := hb (x 1 13)
            have b8056 := hb (x 0 1 && x 0 14)
            clear * - r8053 b8054 b8055 b8056 g24 f8047
            omega
          have d8057 : (x 2 12).toNat = 0 := by
            have r8058 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e8059 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
            have e8060 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
            have b8061 := hb (x (-1) 3)
            have b8062 := hb (x 0 2)
            have b8063 := hb (x 1 13)
            have b8064 := hb (x 2 12)
            clear * - r8058 e8059 e8060 b8061 b8062 b8063 b8064 d8052 f7416
            omega
          have d8065 : (x 2 8 && x 2 12).toNat = 0 := by
            have r8066 := hand2 (x 2 8) (x 2 12)
            have b8067 := hb (x 2 12)
            have b8068 := hb (x 2 8 && x 2 12)
            clear * - r8066 b8067 b8068 d8057
            omega
          have d8069 : (x 2 4).toNat = 0 := by
            have r8070 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
            have b8071 := hb (x 2 4)
            have b8072 := hb (x 2 12)
            clear * - r8070 b8071 b8072 d8057
            omega
          have d8073 : (x 2 4 && x 2 13).toNat = 0 := by
            have r8074 := hand1 (x 2 4) (x 2 13)
            have b8075 := hb (x 2 4)
            have b8076 := hb (x 2 4 && x 2 13)
            clear * - r8074 b8075 b8076 d8069
            omega
          have d8077 : (x (-1) 3).toNat = 0 := by
            have r8078 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e8079 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
            have e8080 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
            have b8081 := hb (x (-1) 3)
            have b8082 := hb (x 0 2)
            have b8083 := hb (x 1 13)
            have b8084 := hb (x 2 12)
            clear * - r8078 e8079 e8080 b8081 b8082 b8083 b8084 d8057 d8052 f7416
            omega
          have d8085 : (x (-1) 11).toNat = 0 := by
            have r8086 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
            have b8087 := hb (x (-1) 3)
            have b8088 := hb (x (-1) 11)
            clear * - r8086 b8087 b8088 d8077
            omega
          cases h8089 : x 1 2
          · have f8090 : (x 1 2).toNat = 0 := by rw [h8089]; rfl
            have d8091 : (x 3 13).toNat = 1 := by
              have r8092 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b8093 := hb (x 1 2)
              have b8094 := hb (x 3 13)
              have b8095 := hb (x 2 1 && x 2 14)
              clear * - r8092 b8093 b8094 b8095 d8010 f8090
              omega
            have d8096 : (x 3 1).toNat = 1 := by
              have r8097 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
              have b8098 := hb (x 3 1)
              have b8099 := hb (x 3 13)
              clear * - r8097 b8098 b8099 d8091
              omega
            have d8100 : (x 4 14).toNat = 0 := by
              have r8101 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b8102 := hb (x 3 1)
              have b8103 := hb (x 4 14)
              clear * - r8101 b8102 b8103 d8096
              omega
            have d8104 : (x 4 3 && x 4 14).toNat = 0 := by
              have r8105 := hand2 (x 4 3) (x 4 14)
              have b8106 := hb (x 4 14)
              have b8107 := hb (x 4 3 && x 4 14)
              clear * - r8105 b8106 b8107 d8100
              omega
            have d8108 : (x 4 6).toNat = 0 := by
              have r8109 : (x 4 6).toNat ≤ (x 4 14).toNat := himp _ _ (hp6 4)
              have b8110 := hb (x 4 6)
              have b8111 := hb (x 4 14)
              clear * - r8109 b8110 b8111 d8100
              omega
            have d8112 : (x 4 6 && x 4 10).toNat = 0 := by
              have r8113 := hand1 (x 4 6) (x 4 10)
              have b8114 := hb (x 4 6)
              have b8115 := hb (x 4 6 && x 4 10)
              clear * - r8113 b8114 b8115 d8108
              omega
            have d8116 : (x 4 2).toNat = 0 := by
              have r8117 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
              have b8118 := hb (x 4 2)
              have b8119 := hb (x 4 14)
              clear * - r8117 b8118 b8119 d8100
              omega
            have d8120 : (x 4 10).toNat = 0 := by
              have r8121 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
              have b8122 := hb (x 4 2)
              have b8123 := hb (x 4 10)
              clear * - r8121 b8122 b8123 d8116
              omega
            have d8124 : (x 4 12).toNat = 0 := by
              have r8125 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e8126 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e8127 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b8128 := hb (x 1 3)
              have b8129 := hb (x 2 2)
              have b8130 := hb (x 3 13)
              have b8131 := hb (x 4 12)
              clear * - r8125 e8126 e8127 b8128 b8129 b8130 b8131 d8091 d8030
              omega
            have d8132 : (x 1 3).toNat = 0 := by
              have r8133 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e8134 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e8135 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b8136 := hb (x 1 3)
              have b8137 := hb (x 2 2)
              have b8138 := hb (x 3 13)
              have b8139 := hb (x 4 12)
              clear * - r8133 e8134 e8135 b8136 b8137 b8138 b8139 d8124 d8091 d8030
              omega
            have d8140 : (x 1 3 && x 1 13).toNat = 0 := by
              have r8141 := hand1 (x 1 3) (x 1 13)
              have b8142 := hb (x 1 3)
              have b8143 := hb (x 1 3 && x 1 13)
              clear * - r8141 b8142 b8143 d8132
              omega
            have d8144 : (x 1 11).toNat = 0 := by
              have r8145 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
              have b8146 := hb (x 1 3)
              have b8147 := hb (x 1 11)
              clear * - r8145 b8146 b8147 d8132
              omega
            have d8148 : (x 1 1 && x 1 11).toNat = 0 := by
              have r8149 := hand2 (x 1 1) (x 1 11)
              have b8150 := hb (x 1 11)
              have b8151 := hb (x 1 1 && x 1 11)
              clear * - r8149 b8150 b8151 d8144
              omega
            have d8152 : (x 3 1 && x 3 11).toNat = 1 := by
              have r8153 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b8154 := hb (x (-1) 5)
              have b8155 := hb (x 4 10)
              have b8156 := hb (x 3 1 && x 3 11)
              have b8157 := hb (x 2 2 && x 2 12)
              have b8158 := hb (x 1 3 && x 1 13)
              have b8159 := hb (x 0 4 && x 0 14)
              clear * - r8153 b8154 b8155 b8156 b8157 b8158 b8159 d8120 d8038 d8140 d7391 d7338
              omega
            have d8160 : (x 3 11).toNat = 1 := by
              have r8161 := hand2 (x 3 1) (x 3 11)
              have b8162 := hb (x 3 11)
              have b8163 := hb (x 3 1 && x 3 11)
              clear * - r8161 b8162 b8163 d8152
              omega
            have d8164 : (x 3 3).toNat = 1 := by
              have r8165 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
              have b8166 := hb (x 3 3)
              have b8167 := hb (x 3 11)
              clear * - r8165 b8166 b8167 d8160
              omega
            have d8168 : (x 6 12).toNat = 0 := by
              have r8169 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e8170 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
              have e8171 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
              have b8172 := hb (x 3 3)
              have b8173 := hb (x 4 2)
              have b8174 := hb (x 5 13)
              have b8175 := hb (x 6 12)
              clear * - r8169 e8170 e8171 b8172 b8173 b8174 b8175 d8116 d8164
              omega
            have d8176 : (x 6 1 && x 6 12).toNat = 0 := by
              have r8177 := hand2 (x 6 1) (x 6 12)
              have b8178 := hb (x 6 12)
              have b8179 := hb (x 6 1 && x 6 12)
              clear * - r8177 b8178 b8179 d8168
              omega
            have d8180 : (x 6 4).toNat = 0 := by
              have r8181 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
              have b8182 := hb (x 6 4)
              have b8183 := hb (x 6 12)
              clear * - r8181 b8182 b8183 d8168
              omega
            have d8184 : (x 6 4 && x 6 8).toNat = 0 := by
              have r8185 := hand1 (x 6 4) (x 6 8)
              have b8186 := hb (x 6 4)
              have b8187 := hb (x 6 4 && x 6 8)
              clear * - r8185 b8186 b8187 d8180
              omega
            have d8188 : (x 5 13).toNat = 0 := by
              have r8189 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e8190 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
              have e8191 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
              have b8192 := hb (x 3 3)
              have b8193 := hb (x 4 2)
              have b8194 := hb (x 5 13)
              have b8195 := hb (x 6 12)
              clear * - r8189 e8190 e8191 b8192 b8193 b8194 b8195 d8168 d8116 d8164
              omega
            have d8196 : (x 5 2 && x 5 13).toNat = 0 := by
              have r8197 := hand2 (x 5 2) (x 5 13)
              have b8198 := hb (x 5 13)
              have b8199 := hb (x 5 2 && x 5 13)
              clear * - r8197 b8198 b8199 d8188
              omega
            have d8200 : (x 7 11).toNat = 1 := by
              have r8201 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b8202 := hb (x 3 4)
              have b8203 := hb (x 7 11)
              have b8204 := hb (x 6 1 && x 6 12)
              have b8205 := hb (x 5 2 && x 5 13)
              have b8206 := hb (x 4 3 && x 4 14)
              clear * - r8201 b8202 b8203 b8204 b8205 b8206 d8176 d8196 d8104 g7
              omega
            have d8207 : (x 7 3).toNat = 1 := by
              have r8208 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
              have b8209 := hb (x 7 3)
              have b8210 := hb (x 7 11)
              clear * - r8208 b8209 b8210 d8200
              omega
            have d8211 : (x 10 12).toNat = 0 := by
              have r8212 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e8213 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
              have e8214 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
              have b8215 := hb (x 7 3)
              have b8216 := hb (x 8 2)
              have b8217 := hb (x 9 13)
              have b8218 := hb (x 10 12)
              clear * - r8212 e8213 e8214 b8215 b8216 b8217 b8218 d8207
              omega
            have d8219 : (x 10 4).toNat = 0 := by
              have r8220 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
              have b8221 := hb (x 10 4)
              have b8222 := hb (x 10 12)
              clear * - r8220 b8221 b8222 d8211
              omega
            have d8223 : (x 9 13).toNat = 0 := by
              have r8224 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e8225 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
              have e8226 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
              have b8227 := hb (x 7 3)
              have b8228 := hb (x 8 2)
              have b8229 := hb (x 9 13)
              have b8230 := hb (x 10 12)
              clear * - r8224 e8225 e8226 b8227 b8228 b8229 b8230 d8211 d8207
              omega
            have d8231 : (x 9 5).toNat = 0 := by
              have r8232 : (x 9 5).toNat ≤ (x 9 13).toNat := himp _ _ (hp5 9)
              have b8233 := hb (x 9 5)
              have b8234 := hb (x 9 13)
              clear * - r8232 b8233 b8234 d8223
              omega
            have d8235 : (x 8 2).toNat = 0 := by
              have r8236 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e8237 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
              have e8238 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
              have b8239 := hb (x 7 3)
              have b8240 := hb (x 8 2)
              have b8241 := hb (x 9 13)
              have b8242 := hb (x 10 12)
              clear * - r8236 e8237 e8238 b8239 b8240 b8241 b8242 d8211 d8223 d8207
              omega
            have d8243 : (x 8 2 && x 8 6).toNat = 0 := by
              have r8244 := hand1 (x 8 2) (x 8 6)
              have b8245 := hb (x 8 2)
              have b8246 := hb (x 8 2 && x 8 6)
              clear * - r8244 b8245 b8246 d8235
              omega
            have d8247 : (x 8 10).toNat = 0 := by
              have r8248 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
              have b8249 := hb (x 8 2)
              have b8250 := hb (x 8 10)
              clear * - r8248 b8249 b8250 d8235
              omega
            have d8251 : (x 5 5).toNat = 0 := by
              have r8252 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
              have b8253 := hb (x 5 5)
              have b8254 := hb (x 5 13)
              clear * - r8252 b8253 b8254 d8188
              omega
            have d8255 : (x 5 5 && x 5 9).toNat = 0 := by
              have r8256 := hand1 (x 5 5) (x 5 9)
              have b8257 := hb (x 5 5)
              have b8258 := hb (x 5 5 && x 5 9)
              clear * - r8256 b8257 b8258 d8251
              omega
            have d8259 : (x (-2) 4 && x (-2) 14).toNat = 1 := by
              have r8260 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b8261 := hb (x (-3) 5)
              have b8262 := hb (x 2 10)
              have b8263 := hb (x 1 1 && x 1 11)
              have b8264 := hb (x 0 2 && x 0 12)
              have b8265 := hb (x (-1) 3 && x (-1) 13)
              have b8266 := hb (x (-2) 4 && x (-2) 14)
              clear * - r8260 b8261 b8262 b8263 b8264 b8265 b8266 d8042 d8148 d7383 d7330 d7371
              omega
            have d8267 : (x (-2) 4).toNat = 1 := by
              have r8268 := hand1 (x (-2) 4) (x (-2) 14)
              have b8269 := hb (x (-2) 4)
              have b8270 := hb (x (-2) 4 && x (-2) 14)
              clear * - r8268 b8269 b8270 d8259
              omega
            have d8271 : (x 10 8).toNat = 0 := by
              have r8272 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e8273 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
              have e8274 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
              have e8275 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
              have e8276 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
              have e8277 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
              have e8278 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
              have b8279 := hb (x 3 7)
              have b8280 := hb (x 4 6)
              have b8281 := hb (x 5 5)
              have b8282 := hb (x 6 4)
              have b8283 := hb (x 7 11)
              have b8284 := hb (x 8 10)
              have b8285 := hb (x 9 9)
              have b8286 := hb (x 10 8)
              clear * - r8272 e8273 e8274 e8275 e8276 e8277 e8278 b8279 b8280 b8281 b8282 b8283 b8284 b8285 b8286 d8247 d8200 d8180 d8251 d8108
              omega
            have d8287 : (x 9 9).toNat = 0 := by
              have r8288 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e8289 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
              have e8290 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
              have e8291 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
              have e8292 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
              have e8293 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
              have e8294 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
              have b8295 := hb (x 3 7)
              have b8296 := hb (x 4 6)
              have b8297 := hb (x 5 5)
              have b8298 := hb (x 6 4)
              have b8299 := hb (x 7 11)
              have b8300 := hb (x 8 10)
              have b8301 := hb (x 9 9)
              have b8302 := hb (x 10 8)
              clear * - r8288 e8289 e8290 e8291 e8292 e8293 e8294 b8295 b8296 b8297 b8298 b8299 b8300 b8301 b8302 d8271 d8247 d8200 d8180 d8251 d8108
              omega
            have d8303 : (x 3 7).toNat = 0 := by
              have r8304 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e8305 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
              have e8306 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
              have e8307 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
              have e8308 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
              have e8309 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
              have e8310 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
              have b8311 := hb (x 3 7)
              have b8312 := hb (x 4 6)
              have b8313 := hb (x 5 5)
              have b8314 := hb (x 6 4)
              have b8315 := hb (x 7 11)
              have b8316 := hb (x 8 10)
              have b8317 := hb (x 9 9)
              have b8318 := hb (x 10 8)
              clear * - r8304 e8305 e8306 e8307 e8308 e8309 e8310 b8311 b8312 b8313 b8314 b8315 b8316 b8317 b8318 d8271 d8287 d8247 d8200 d8180 d8251 d8108
              omega
            have d8319 : (x 3 7 && x 3 11).toNat = 0 := by
              have r8320 := hand1 (x 3 7) (x 3 11)
              have b8321 := hb (x 3 7)
              have b8322 := hb (x 3 7 && x 3 11)
              clear * - r8320 b8321 b8322 d8303
              omega
            have d8323 : (x 6 8).toNat = 0 := by
              have r8324 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e8325 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
              have e8326 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
              have e8327 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
              have e8328 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
              have e8329 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
              have e8330 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
              have b8331 := hb (x (-1) 7)
              have b8332 := hb (x 0 6)
              have b8333 := hb (x 1 5)
              have b8334 := hb (x 2 4)
              have b8335 := hb (x 3 11)
              have b8336 := hb (x 4 10)
              have b8337 := hb (x 5 9)
              have b8338 := hb (x 6 8)
              clear * - r8324 e8325 e8326 e8327 e8328 e8329 e8330 b8331 b8332 b8333 b8334 b8335 b8336 b8337 b8338 d8120 d8160 d8069 g1
              omega
            have d8339 : (x 5 9).toNat = 0 := by
              have r8340 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e8341 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
              have e8342 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
              have e8343 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
              have e8344 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
              have e8345 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
              have e8346 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
              have b8347 := hb (x (-1) 7)
              have b8348 := hb (x 0 6)
              have b8349 := hb (x 1 5)
              have b8350 := hb (x 2 4)
              have b8351 := hb (x 3 11)
              have b8352 := hb (x 4 10)
              have b8353 := hb (x 5 9)
              have b8354 := hb (x 6 8)
              clear * - r8340 e8341 e8342 e8343 e8344 e8345 e8346 b8347 b8348 b8349 b8350 b8351 b8352 b8353 b8354 d8323 d8120 d8160 d8069 g1
              omega
            have d8355 : (x 2 8).toNat = 0 := by
              have r8356 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e8357 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
              have e8358 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
              have e8359 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
              have e8360 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
              have e8361 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
              have e8362 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
              have b8363 := hb (x (-5) 7)
              have b8364 := hb (x (-4) 6)
              have b8365 := hb (x (-3) 5)
              have b8366 := hb (x (-2) 4)
              have b8367 := hb (x (-1) 11)
              have b8368 := hb (x 0 10)
              have b8369 := hb (x 1 9)
              have b8370 := hb (x 2 8)
              clear * - r8356 e8357 e8358 e8359 e8360 e8361 e8362 b8363 b8364 b8365 b8366 b8367 b8368 b8369 b8370 d7417 d8085 d8267 d7371
              omega
            have d8371 : (x 1 9).toNat = 0 := by
              have r8372 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e8373 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
              have e8374 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
              have e8375 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
              have e8376 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
              have e8377 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
              have e8378 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
              have b8379 := hb (x (-5) 7)
              have b8380 := hb (x (-4) 6)
              have b8381 := hb (x (-3) 5)
              have b8382 := hb (x (-2) 4)
              have b8383 := hb (x (-1) 11)
              have b8384 := hb (x 0 10)
              have b8385 := hb (x 1 9)
              have b8386 := hb (x 2 8)
              clear * - r8372 e8373 e8374 e8375 e8376 e8377 e8378 b8379 b8380 b8381 b8382 b8383 b8384 b8385 b8386 d8355 d7417 d8085 d8267 d7371
              omega
            have d8387 : (x 1 9 && x 1 13).toNat = 0 := by
              have r8388 := hand1 (x 1 9) (x 1 13)
              have b8389 := hb (x 1 9)
              have b8390 := hb (x 1 9 && x 1 13)
              clear * - r8388 b8389 b8390 d8371
              omega
            have d8391 : (x 7 3 && x 7 7).toNat = 1 := by
              have r8392 : 1 ≤ (x 10 4).toNat + (x 9 1 && x 9 5).toNat + (x 8 2 && x 8 6).toNat + (x 7 3 && x 7 7).toNat + (x 6 4 && x 6 8).toNat + (x 5 5 && x 5 9).toNat + (x 4 6 && x 4 10).toNat + (x 3 7 && x 3 11).toNat + (x 2 8 && x 2 12).toNat + (x 1 9 && x 1 13).toNat + (x 0 10 && x 0 14).toNat + (x (-1) 11).toNat := by have q := hcov4 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e8393 : (x 9 1 && x 9 5).toNat = (x 9 5).toNat := handr _ _ (fun h => hp13 9 (hp5 9 (h)))
              have e8394 : (x 0 10 && x 0 14).toNat = (x 0 10).toNat := handl _ _ (fun h => hp2 0 (hp10 0 (h)))
              have b8395 := hb (x (-1) 11)
              have b8396 := hb (x 0 10)
              have b8397 := hb (x 9 5)
              have b8398 := hb (x 10 4)
              have b8399 := hb (x 8 2 && x 8 6)
              have b8400 := hb (x 7 3 && x 7 7)
              have b8401 := hb (x 6 4 && x 6 8)
              have b8402 := hb (x 5 5 && x 5 9)
              have b8403 := hb (x 4 6 && x 4 10)
              have b8404 := hb (x 3 7 && x 3 11)
              have b8405 := hb (x 2 8 && x 2 12)
              have b8406 := hb (x 1 9 && x 1 13)
              clear * - r8392 e8393 e8394 b8395 b8396 b8397 b8398 b8399 b8400 b8401 b8402 b8403 b8404 b8405 b8406 d8219 d8231 d8243 d8184 d8255 d8112 d8319 d8065 d8387 d7417 d8085
              omega
            have d8407 : (x 7 7).toNat = 1 := by
              have r8408 := hand2 (x 7 3) (x 7 7)
              have b8409 := hb (x 7 7)
              have b8410 := hb (x 7 3 && x 7 7)
              clear * - r8408 b8409 b8410 d8391
              omega
            have d8411 : (x 14 8).toNat = 0 := by
              have r8412 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e8413 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
              have e8414 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
              have e8415 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
              have e8416 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
              have e8417 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
              have e8418 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
              have b8419 := hb (x 7 7)
              have b8420 := hb (x 8 6)
              have b8421 := hb (x 9 5)
              have b8422 := hb (x 10 4)
              have b8423 := hb (x 11 11)
              have b8424 := hb (x 12 10)
              have b8425 := hb (x 13 9)
              have b8426 := hb (x 14 8)
              clear * - r8412 e8413 e8414 e8415 e8416 e8417 e8418 b8419 b8420 b8421 b8422 b8423 b8424 b8425 b8426 d8219 d8231 d8407
              omega
            have d8427 : (x 13 9).toNat = 0 := by
              have r8428 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e8429 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
              have e8430 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
              have e8431 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
              have e8432 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
              have e8433 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
              have e8434 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
              have b8435 := hb (x 7 7)
              have b8436 := hb (x 8 6)
              have b8437 := hb (x 9 5)
              have b8438 := hb (x 10 4)
              have b8439 := hb (x 11 11)
              have b8440 := hb (x 12 10)
              have b8441 := hb (x 13 9)
              have b8442 := hb (x 14 8)
              clear * - r8428 e8429 e8430 e8431 e8432 e8433 e8434 b8435 b8436 b8437 b8438 b8439 b8440 b8441 b8442 d8411 d8219 d8231 d8407
              omega
            have d8443 : (x 12 10).toNat = 0 := by
              have r8444 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e8445 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
              have e8446 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
              have e8447 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
              have e8448 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
              have e8449 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
              have e8450 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
              have b8451 := hb (x 7 7)
              have b8452 := hb (x 8 6)
              have b8453 := hb (x 9 5)
              have b8454 := hb (x 10 4)
              have b8455 := hb (x 11 11)
              have b8456 := hb (x 12 10)
              have b8457 := hb (x 13 9)
              have b8458 := hb (x 14 8)
              clear * - r8444 e8445 e8446 e8447 e8448 e8449 e8450 b8451 b8452 b8453 b8454 b8455 b8456 b8457 b8458 d8411 d8427 d8219 d8231 d8407
              omega
            have d8459 : (x 11 11).toNat = 0 := by
              have r8460 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e8461 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
              have e8462 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
              have e8463 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
              have e8464 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
              have e8465 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
              have e8466 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
              have b8467 := hb (x 7 7)
              have b8468 := hb (x 8 6)
              have b8469 := hb (x 9 5)
              have b8470 := hb (x 10 4)
              have b8471 := hb (x 11 11)
              have b8472 := hb (x 12 10)
              have b8473 := hb (x 13 9)
              have b8474 := hb (x 14 8)
              clear * - r8460 e8461 e8462 e8463 e8464 e8465 e8466 b8467 b8468 b8469 b8470 b8471 b8472 b8473 b8474 d8411 d8427 d8443 d8219 d8231 d8407
              omega
            have d8475 : (x 8 6).toNat = 0 := by
              have r8476 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e8477 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
              have e8478 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
              have e8479 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
              have e8480 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
              have e8481 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
              have e8482 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
              have b8483 := hb (x 7 7)
              have b8484 := hb (x 8 6)
              have b8485 := hb (x 9 5)
              have b8486 := hb (x 10 4)
              have b8487 := hb (x 11 11)
              have b8488 := hb (x 12 10)
              have b8489 := hb (x 13 9)
              have b8490 := hb (x 14 8)
              clear * - r8476 e8477 e8478 e8479 e8480 e8481 e8482 b8483 b8484 b8485 b8486 b8487 b8488 b8489 b8490 d8411 d8427 d8443 d8459 d8219 d8231 d8407
              omega
            have r8491 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b8492 := hb (x 0 14)
            have b8493 := hb (x 1 13)
            have b8494 := hb (x 2 12)
            have b8495 := hb (x 3 11)
            have b8496 := hb (x 4 10)
            have b8497 := hb (x 5 9)
            have b8498 := hb (x 6 8)
            have b8499 := hb (x 7 7)
            have b8500 := hb (x 8 6)
            have b8501 := hb (x 9 5)
            have b8502 := hb (x 10 4)
            have b8503 := hb (x 11 3)
            have b8504 := hb (x 12 2)
            have b8505 := hb (x 13 1)
            linarith only [r8491, b8492, b8493, b8494, b8495, b8496, b8497, b8498, b8499, b8500, b8501, b8502, b8503, b8504, b8505, d8219, d8231, d8475, d8407, d8323, d8339, d8120, d8160, d8057, d8052, g5]
          · have f8506 : (x 1 2).toNat = 1 := by rw [h8089]; rfl
            have d8507 : (x 3 12).toNat = 0 := by
              have r8508 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e8509 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
              have e8510 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
              have b8511 := hb (x 0 3)
              have b8512 := hb (x 1 2)
              have b8513 := hb (x 2 13)
              have b8514 := hb (x 3 12)
              clear * - r8508 e8509 e8510 b8511 b8512 b8513 b8514 f8506 f7422
              omega
            have d8515 : (x 3 1 && x 3 12).toNat = 0 := by
              have r8516 := hand2 (x 3 1) (x 3 12)
              have b8517 := hb (x 3 12)
              have b8518 := hb (x 3 1 && x 3 12)
              clear * - r8516 b8517 b8518 d8507
              omega
            have d8519 : (x 3 2 && x 3 12).toNat = 0 := by
              have r8520 := hand2 (x 3 2) (x 3 12)
              have b8521 := hb (x 3 12)
              have b8522 := hb (x 3 2 && x 3 12)
              clear * - r8520 b8521 b8522 d8507
              omega
            have d8523 : (x 3 3 && x 3 12).toNat = 0 := by
              have r8524 := hand2 (x 3 3) (x 3 12)
              have b8525 := hb (x 3 12)
              have b8526 := hb (x 3 3 && x 3 12)
              clear * - r8524 b8525 b8526 d8507
              omega
            have d8527 : (x 3 5 && x 3 12).toNat = 0 := by
              have r8528 := hand2 (x 3 5) (x 3 12)
              have b8529 := hb (x 3 12)
              have b8530 := hb (x 3 5 && x 3 12)
              clear * - r8528 b8529 b8530 d8507
              omega
            have d8531 : (x 2 13).toNat = 0 := by
              have r8532 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e8533 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
              have e8534 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
              have b8535 := hb (x 0 3)
              have b8536 := hb (x 1 2)
              have b8537 := hb (x 2 13)
              have b8538 := hb (x 3 12)
              clear * - r8532 e8533 e8534 b8535 b8536 b8537 b8538 d8507 f8506 f7422
              omega
            have d8539 : (x 2 3 && x 2 13).toNat = 0 := by
              have r8540 := hand2 (x 2 3) (x 2 13)
              have b8541 := hb (x 2 13)
              have b8542 := hb (x 2 3 && x 2 13)
              clear * - r8540 b8541 b8542 d8531
              omega
            have d8543 : (x 1 3 && x 1 14).toNat = 1 := by
              have r8544 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b8545 := hb (x 0 4)
              have b8546 := hb (x 4 11)
              have b8547 := hb (x 3 1 && x 3 12)
              have b8548 := hb (x 2 2 && x 2 13)
              have b8549 := hb (x 1 3 && x 1 14)
              clear * - r8544 b8545 b8546 b8547 b8548 b8549 g8 d8515 d8034 d7387
              omega
            have d8550 : (x 1 3).toNat = 1 := by
              have r8551 := hand1 (x 1 3) (x 1 14)
              have b8552 := hb (x 1 3)
              have b8553 := hb (x 1 3 && x 1 14)
              clear * - r8551 b8552 b8553 d8543
              omega
            have d8554 : (x 4 12).toNat = 0 := by
              have r8555 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e8556 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e8557 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b8558 := hb (x 1 3)
              have b8559 := hb (x 2 2)
              have b8560 := hb (x 3 13)
              have b8561 := hb (x 4 12)
              clear * - r8555 e8556 e8557 b8558 b8559 b8560 b8561 d8030 d8550
              omega
            have d8562 : (x 4 3 && x 4 12).toNat = 0 := by
              have r8563 := hand2 (x 4 3) (x 4 12)
              have b8564 := hb (x 4 12)
              have b8565 := hb (x 4 3 && x 4 12)
              clear * - r8563 b8564 b8565 d8554
              omega
            have d8566 : (x 4 4).toNat = 0 := by
              have r8567 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
              have b8568 := hb (x 4 4)
              have b8569 := hb (x 4 12)
              clear * - r8567 b8568 b8569 d8554
              omega
            have d8570 : (x 4 4 && x 4 10).toNat = 0 := by
              have r8571 := hand1 (x 4 4) (x 4 10)
              have b8572 := hb (x 4 4)
              have b8573 := hb (x 4 4 && x 4 10)
              clear * - r8571 b8572 b8573 d8566
              omega
            have d8574 : (x 4 4 && x 4 8).toNat = 0 := by
              have r8575 := hand1 (x 4 4) (x 4 8)
              have b8576 := hb (x 4 4)
              have b8577 := hb (x 4 4 && x 4 8)
              clear * - r8575 b8576 b8577 d8566
              omega
            have d8578 : (x 3 13).toNat = 0 := by
              have r8579 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e8580 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e8581 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b8582 := hb (x 1 3)
              have b8583 := hb (x 2 2)
              have b8584 := hb (x 3 13)
              have b8585 := hb (x 4 12)
              clear * - r8579 e8580 e8581 b8582 b8583 b8584 b8585 d8554 d8030 d8550
              omega
            have d8586 : (x 3 5).toNat = 0 := by
              have r8587 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
              have b8588 := hb (x 3 5)
              have b8589 := hb (x 3 13)
              clear * - r8587 b8588 b8589 d8578
              omega
            have d8590 : (x 3 5 && x 3 11).toNat = 0 := by
              have r8591 := hand1 (x 3 5) (x 3 11)
              have b8592 := hb (x 3 5)
              have b8593 := hb (x 3 5 && x 3 11)
              clear * - r8591 b8592 b8593 d8586
              omega
            have d8594 : (x 3 5 && x 3 9).toNat = 0 := by
              have r8595 := hand1 (x 3 5) (x 3 9)
              have b8596 := hb (x 3 5)
              have b8597 := hb (x 3 5 && x 3 9)
              clear * - r8595 b8596 b8597 d8586
              omega
            have d8598 : (x 1 4 && x 1 14).toNat = 1 := by
              have r8599 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b8600 := hb (x 0 5)
              have b8601 := hb (x 5 10)
              have b8602 := hb (x 4 1 && x 4 11)
              have b8603 := hb (x 3 2 && x 3 12)
              have b8604 := hb (x 2 3 && x 2 13)
              have b8605 := hb (x 1 4 && x 1 14)
              clear * - r8599 b8600 b8601 b8602 b8603 b8604 b8605 g9 g21 d8519 d8539 g0
              omega
            have d8606 : (x 1 4).toNat = 1 := by
              have r8607 := hand1 (x 1 4) (x 1 14)
              have b8608 := hb (x 1 4)
              have b8609 := hb (x 1 4 && x 1 14)
              clear * - r8607 b8608 b8609 d8598
              omega
            have d8610 : (x 1 12).toNat = 1 := by
              have r8611 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
              have b8612 := hb (x 1 4)
              have b8613 := hb (x 1 12)
              clear * - r8611 b8612 b8613 d8606
              omega
            have d8614 : (x (-2) 3).toNat = 0 := by
              have r8615 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e8616 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
              have e8617 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
              have b8618 := hb (x (-2) 3)
              have b8619 := hb (x (-1) 2)
              have b8620 := hb (x 0 13)
              have b8621 := hb (x 1 12)
              clear * - r8615 e8616 e8617 b8618 b8619 b8620 b8621 d8610 g4 f8047
              omega
            have d8622 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
              have r8623 := hand1 (x (-2) 3) (x (-2) 14)
              have b8624 := hb (x (-2) 3)
              have b8625 := hb (x (-2) 3 && x (-2) 14)
              clear * - r8623 b8624 b8625 d8614
              omega
            have d8626 : (x (-2) 11).toNat = 0 := by
              have r8627 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
              have b8628 := hb (x (-2) 3)
              have b8629 := hb (x (-2) 11)
              clear * - r8627 b8628 b8629 d8614
              omega
            have d8630 : (x (-2) 1 && x (-2) 11).toNat = 0 := by
              have r8631 := hand2 (x (-2) 1) (x (-2) 11)
              have b8632 := hb (x (-2) 11)
              have b8633 := hb (x (-2) 1 && x (-2) 11)
              clear * - r8631 b8632 b8633 d8626
              omega
            have d8634 : (x (-2) 2 && x (-2) 11).toNat = 0 := by
              have r8635 := hand2 (x (-2) 2) (x (-2) 11)
              have b8636 := hb (x (-2) 11)
              have b8637 := hb (x (-2) 2 && x (-2) 11)
              clear * - r8635 b8636 b8637 d8626
              omega
            have d8638 : (x 1 5 && x 1 14).toNat = 1 := by
              have r8639 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b8640 := hb (x 0 6)
              have b8641 := hb (x 6 9)
              have b8642 := hb (x 5 1 && x 5 10)
              have b8643 := hb (x 4 2 && x 4 11)
              have b8644 := hb (x 3 3 && x 3 12)
              have b8645 := hb (x 2 4 && x 2 13)
              have b8646 := hb (x 1 5 && x 1 14)
              clear * - r8639 b8640 b8641 b8642 b8643 b8644 b8645 b8646 g10 g17 g18 d8523 d8073 g1
              omega
            have d8647 : (x 1 5).toNat = 1 := by
              have r8648 := hand1 (x 1 5) (x 1 14)
              have b8649 := hb (x 1 5)
              have b8650 := hb (x 1 5 && x 1 14)
              clear * - r8648 b8649 b8650 d8638
              omega
            have d8651 : (x 6 8).toNat = 0 := by
              have r8652 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e8653 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
              have e8654 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
              have e8655 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
              have e8656 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
              have e8657 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
              have e8658 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
              have b8659 := hb (x (-1) 7)
              have b8660 := hb (x 0 6)
              have b8661 := hb (x 1 5)
              have b8662 := hb (x 2 4)
              have b8663 := hb (x 3 11)
              have b8664 := hb (x 4 10)
              have b8665 := hb (x 5 9)
              have b8666 := hb (x 6 8)
              clear * - r8652 e8653 e8654 e8655 e8656 e8657 e8658 b8659 b8660 b8661 b8662 b8663 b8664 b8665 b8666 d8069 d8647 g1
              omega
            have d8667 : (x 6 2 && x 6 8).toNat = 0 := by
              have r8668 := hand2 (x 6 2) (x 6 8)
              have b8669 := hb (x 6 8)
              have b8670 := hb (x 6 2 && x 6 8)
              clear * - r8668 b8669 b8670 d8651
              omega
            have d8671 : (x 5 9).toNat = 0 := by
              have r8672 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e8673 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
              have e8674 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
              have e8675 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
              have e8676 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
              have e8677 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
              have e8678 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
              have b8679 := hb (x (-1) 7)
              have b8680 := hb (x 0 6)
              have b8681 := hb (x 1 5)
              have b8682 := hb (x 2 4)
              have b8683 := hb (x 3 11)
              have b8684 := hb (x 4 10)
              have b8685 := hb (x 5 9)
              have b8686 := hb (x 6 8)
              clear * - r8672 e8673 e8674 e8675 e8676 e8677 e8678 b8679 b8680 b8681 b8682 b8683 b8684 b8685 b8686 d8651 d8069 d8647 g1
              omega
            have d8687 : (x 5 3 && x 5 9).toNat = 0 := by
              have r8688 := hand2 (x 5 3) (x 5 9)
              have b8689 := hb (x 5 9)
              have b8690 := hb (x 5 3 && x 5 9)
              clear * - r8688 b8689 b8690 d8671
              omega
            have d8691 : (x 4 10).toNat = 0 := by
              have r8692 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e8693 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
              have e8694 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
              have e8695 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
              have e8696 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
              have e8697 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
              have e8698 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
              have b8699 := hb (x (-1) 7)
              have b8700 := hb (x 0 6)
              have b8701 := hb (x 1 5)
              have b8702 := hb (x 2 4)
              have b8703 := hb (x 3 11)
              have b8704 := hb (x 4 10)
              have b8705 := hb (x 5 9)
              have b8706 := hb (x 6 8)
              clear * - r8692 e8693 e8694 e8695 e8696 e8697 e8698 b8699 b8700 b8701 b8702 b8703 b8704 b8705 b8706 d8651 d8671 d8069 d8647 g1
              omega
            have d8707 : (x 3 11).toNat = 0 := by
              have r8708 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e8709 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
              have e8710 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
              have e8711 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
              have e8712 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
              have e8713 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
              have e8714 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
              have b8715 := hb (x (-1) 7)
              have b8716 := hb (x 0 6)
              have b8717 := hb (x 1 5)
              have b8718 := hb (x 2 4)
              have b8719 := hb (x 3 11)
              have b8720 := hb (x 4 10)
              have b8721 := hb (x 5 9)
              have b8722 := hb (x 6 8)
              clear * - r8708 e8709 e8710 e8711 e8712 e8713 e8714 b8715 b8716 b8717 b8718 b8719 b8720 b8721 b8722 d8651 d8671 d8691 d8069 d8647 g1
              omega
            cases h8723 : x (-1) 4
            · have f8724 : (x (-1) 4).toNat = 0 := by rw [h8723]; rfl
              cases h8725 : x 1 7
              · have f8726 : (x 1 7).toNat = 0 := by rw [h8725]; rfl
                have d8727 : (x 1 7 && x 1 14).toNat = 0 := by
                  have r8728 := hand1 (x 1 7) (x 1 14)
                  have b8729 := hb (x 1 7)
                  have b8730 := hb (x 1 7 && x 1 14)
                  clear * - r8728 b8729 b8730 f8726
                  omega
                have d8731 : (x 1 7 && x 1 13).toNat = 0 := by
                  have r8732 := hand1 (x 1 7) (x 1 13)
                  have b8733 := hb (x 1 7)
                  have b8734 := hb (x 1 7 && x 1 13)
                  clear * - r8732 b8733 b8734 f8726
                  omega
                have d8735 : (x 1 7 && x 1 11).toNat = 0 := by
                  have r8736 := hand1 (x 1 7) (x 1 11)
                  have b8737 := hb (x 1 7)
                  have b8738 := hb (x 1 7 && x 1 11)
                  clear * - r8736 b8737 b8738 f8726
                  omega
                have d8739 : (x 8 7).toNat = 1 := by
                  have r8740 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := by have q := hcov7 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b8741 := hb (x 0 8)
                  have b8742 := hb (x 8 7)
                  have b8743 := hb (x 7 1 && x 7 8)
                  have b8744 := hb (x 6 2 && x 6 9)
                  have b8745 := hb (x 5 3 && x 5 10)
                  have b8746 := hb (x 4 4 && x 4 11)
                  have b8747 := hb (x 3 5 && x 3 12)
                  have b8748 := hb (x 2 6 && x 2 13)
                  have b8749 := hb (x 1 7 && x 1 14)
                  clear * - r8740 b8741 b8742 b8743 b8744 b8745 b8746 b8747 b8748 b8749 g13 g14 g15 g16 d8527 d8018 d8727 g2
                  omega
                have d8750 : (x 15 8).toNat = 0 := by
                  have r8751 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e8752 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                  have e8753 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                  have e8754 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                  have e8755 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                  have e8756 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                  have e8757 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                  have b8758 := hb (x 8 7)
                  have b8759 := hb (x 9 6)
                  have b8760 := hb (x 10 5)
                  have b8761 := hb (x 11 4)
                  have b8762 := hb (x 12 11)
                  have b8763 := hb (x 13 10)
                  have b8764 := hb (x 14 9)
                  have b8765 := hb (x 15 8)
                  clear * - r8751 e8752 e8753 e8754 e8755 e8756 e8757 b8758 b8759 b8760 b8761 b8762 b8763 b8764 b8765 d8739
                  omega
                have d8766 : (x 14 9).toNat = 0 := by
                  have r8767 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e8768 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                  have e8769 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                  have e8770 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                  have e8771 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                  have e8772 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                  have e8773 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                  have b8774 := hb (x 8 7)
                  have b8775 := hb (x 9 6)
                  have b8776 := hb (x 10 5)
                  have b8777 := hb (x 11 4)
                  have b8778 := hb (x 12 11)
                  have b8779 := hb (x 13 10)
                  have b8780 := hb (x 14 9)
                  have b8781 := hb (x 15 8)
                  clear * - r8767 e8768 e8769 e8770 e8771 e8772 e8773 b8774 b8775 b8776 b8777 b8778 b8779 b8780 b8781 d8750 d8739
                  omega
                have d8782 : (x 13 10).toNat = 0 := by
                  have r8783 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e8784 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                  have e8785 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                  have e8786 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                  have e8787 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                  have e8788 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                  have e8789 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                  have b8790 := hb (x 8 7)
                  have b8791 := hb (x 9 6)
                  have b8792 := hb (x 10 5)
                  have b8793 := hb (x 11 4)
                  have b8794 := hb (x 12 11)
                  have b8795 := hb (x 13 10)
                  have b8796 := hb (x 14 9)
                  have b8797 := hb (x 15 8)
                  clear * - r8783 e8784 e8785 e8786 e8787 e8788 e8789 b8790 b8791 b8792 b8793 b8794 b8795 b8796 b8797 d8750 d8766 d8739
                  omega
                have d8798 : (x 13 1 && x 13 10).toNat = 0 := by
                  have r8799 := hand2 (x 13 1) (x 13 10)
                  have b8800 := hb (x 13 10)
                  have b8801 := hb (x 13 1 && x 13 10)
                  clear * - r8799 b8800 b8801 d8782
                  omega
                have d8802 : (x 12 11).toNat = 0 := by
                  have r8803 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e8804 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                  have e8805 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                  have e8806 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                  have e8807 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                  have e8808 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                  have e8809 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                  have b8810 := hb (x 8 7)
                  have b8811 := hb (x 9 6)
                  have b8812 := hb (x 10 5)
                  have b8813 := hb (x 11 4)
                  have b8814 := hb (x 12 11)
                  have b8815 := hb (x 13 10)
                  have b8816 := hb (x 14 9)
                  have b8817 := hb (x 15 8)
                  clear * - r8803 e8804 e8805 e8806 e8807 e8808 e8809 b8810 b8811 b8812 b8813 b8814 b8815 b8816 b8817 d8750 d8766 d8782 d8739
                  omega
                have d8818 : (x 12 2 && x 12 11).toNat = 0 := by
                  have r8819 := hand2 (x 12 2) (x 12 11)
                  have b8820 := hb (x 12 11)
                  have b8821 := hb (x 12 2 && x 12 11)
                  clear * - r8819 b8820 b8821 d8802
                  omega
                have r8822 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r8823 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r8824 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r8825 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e8826 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                have e8827 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                have e8828 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                have e8829 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                have e8830 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                have e8831 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                have r8832 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e8833 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                have e8834 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                have r8835 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e8836 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                have e8837 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                have r8838 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e8839 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                have e8840 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                have r8841 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r8842 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r8843 : 1 ≤ (x 8 4).toNat + (x 7 1 && x 7 5).toNat + (x 6 2 && x 6 6).toNat + (x 5 3 && x 5 7).toNat + (x 4 4 && x 4 8).toNat + (x 3 5 && x 3 9).toNat + (x 2 6 && x 2 10).toNat + (x 1 7 && x 1 11).toNat + (x 0 8 && x 0 12).toNat + (x (-1) 9 && x (-1) 13).toNat + (x (-2) 10 && x (-2) 14).toNat + (x (-3) 11).toNat := by have q := hcov4 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e8844 : (x 7 1 && x 7 5).toNat = (x 7 5).toNat := handr _ _ (fun h => hp13 7 (hp5 7 (h)))
                have e8845 : (x (-2) 10 && x (-2) 14).toNat = (x (-2) 10).toNat := handl _ _ (fun h => hp2 (-2) (hp10 (-2) (h)))
                have r8846 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r8847 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r8848 : 1 ≤ (x 14 9).toNat + (x 13 1 && x 13 10).toNat + (x 12 2 && x 12 11).toNat + (x 11 3 && x 11 12).toNat + (x 10 4 && x 10 13).toNat + (x 9 5 && x 9 14).toNat + (x 8 6).toNat := by have q := hcov9 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r8849 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r8850 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r8851 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r8852 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r8853 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
                have r8854 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
                have r8855 : (x 8 6).toNat ≤ (x 8 14).toNat := himp _ _ (hp6 8)
                have r8856 := hand2 (x 6 2) (x 6 6)
                have r8857 := hand2 (x 5 3) (x 5 7)
                have r8858 := hand2 (x 7 1) (x 7 7)
                have r8859 := hand1 (x (-4) 4) (x (-4) 13)
                have r8860 := hand1 (x (-5) 5) (x (-5) 14)
                have r8861 := hand1 (x 11 3) (x 11 12)
                have r8862 := hand1 (x 10 4) (x 10 13)
                have r8863 := hand1 (x 9 5) (x 9 14)
                have r8864 := hand1 (x 11 1) (x 11 12)
                have r8865 := hand1 (x 10 2) (x 10 13)
                have r8866 := hand1 (x 9 3) (x 9 14)
                have r8867 := hand1 (x (-5) 1) (x (-5) 14)
                have r8868 := hand2 (x (-4) 1) (x (-4) 14)
                have b8874 := hb (x (-6) 14)
                linarith only [r8822, r8823, r8824, r8825, e8826, e8827, e8828, e8829, e8830, e8831, r8832, e8833, e8834, r8835, e8836, e8837, r8838, e8839, e8840, r8841, r8842, r8843, e8844, e8845, r8846, r8847, r8848, r8849, r8850, r8851, r8852, r8853, r8854, r8855, r8856, r8857, r8858, r8859, r8860, r8861, r8862, r8863, r8864, r8865, r8866, r8867, r8868, b8874, d7411, d7363, d7351, d7342, d7322, g2, g3, d7375, g5, f8726, d8052, d8014, d8042, d8057, d8586, d8707, d8566, d8691, d8671, d8651, d8802, d8766, d8574, d8594, d8026, d8735, g11, d7334, d8667, d8687, d8570, d8590, d8022, d8731, g12, d7318, d8634, d7407, d8798, d8818, g22, d7326, d8622]
              · have f8965 : (x 1 7).toNat = 1 := by rw [h8725]; rfl
                have d8966 : (x 8 8).toNat = 0 := by
                  have r8967 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e8968 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                  have e8969 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                  have e8970 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                  have e8971 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                  have e8972 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                  have e8973 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                  have b8974 := hb (x 1 7)
                  have b8975 := hb (x 2 6)
                  have b8976 := hb (x 3 5)
                  have b8977 := hb (x 4 4)
                  have b8978 := hb (x 5 11)
                  have b8979 := hb (x 6 10)
                  have b8980 := hb (x 7 9)
                  have b8981 := hb (x 8 8)
                  clear * - r8967 e8968 e8969 e8970 e8971 e8972 e8973 b8974 b8975 b8976 b8977 b8978 b8979 b8980 b8981 d8566 d8586 d8014 f8965
                  omega
                have d8982 : (x 7 9).toNat = 0 := by
                  have r8983 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e8984 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                  have e8985 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                  have e8986 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                  have e8987 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                  have e8988 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                  have e8989 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                  have b8990 := hb (x 1 7)
                  have b8991 := hb (x 2 6)
                  have b8992 := hb (x 3 5)
                  have b8993 := hb (x 4 4)
                  have b8994 := hb (x 5 11)
                  have b8995 := hb (x 6 10)
                  have b8996 := hb (x 7 9)
                  have b8997 := hb (x 8 8)
                  clear * - r8983 e8984 e8985 e8986 e8987 e8988 e8989 b8990 b8991 b8992 b8993 b8994 b8995 b8996 b8997 d8966 d8566 d8586 d8014 f8965
                  omega
                have d8998 : (x 6 10).toNat = 0 := by
                  have r8999 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e9000 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                  have e9001 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                  have e9002 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                  have e9003 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                  have e9004 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                  have e9005 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                  have b9006 := hb (x 1 7)
                  have b9007 := hb (x 2 6)
                  have b9008 := hb (x 3 5)
                  have b9009 := hb (x 4 4)
                  have b9010 := hb (x 5 11)
                  have b9011 := hb (x 6 10)
                  have b9012 := hb (x 7 9)
                  have b9013 := hb (x 8 8)
                  clear * - r8999 e9000 e9001 e9002 e9003 e9004 e9005 b9006 b9007 b9008 b9009 b9010 b9011 b9012 b9013 d8966 d8982 d8566 d8586 d8014 f8965
                  omega
                have d9014 : (x 6 1 && x 6 10).toNat = 0 := by
                  have r9015 := hand2 (x 6 1) (x 6 10)
                  have b9016 := hb (x 6 10)
                  have b9017 := hb (x 6 1 && x 6 10)
                  clear * - r9015 b9016 b9017 d8998
                  omega
                have d9018 : (x 5 2 && x 5 11).toNat = 1 := by
                  have r9019 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b9020 := hb (x 1 6)
                  have b9021 := hb (x 7 9)
                  have b9022 := hb (x 6 1 && x 6 10)
                  have b9023 := hb (x 5 2 && x 5 11)
                  have b9024 := hb (x 4 3 && x 4 12)
                  have b9025 := hb (x 3 4 && x 3 13)
                  have b9026 := hb (x 2 5 && x 2 14)
                  clear * - r9019 b9020 b9021 b9022 b9023 b9024 b9025 b9026 d8982 d9014 d8562 g19 g20 g6
                  omega
                have d9027 : (x 5 11).toNat = 1 := by
                  have r9028 := hand2 (x 5 2) (x 5 11)
                  have b9029 := hb (x 5 11)
                  have b9030 := hb (x 5 2 && x 5 11)
                  clear * - r9028 b9029 b9030 d9018
                  omega
                have r9031 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e9032 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e9033 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e9034 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e9035 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e9036 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e9037 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b9038 := hb (x 1 7)
                have b9039 := hb (x 2 6)
                have b9040 := hb (x 3 5)
                have b9041 := hb (x 4 4)
                have b9042 := hb (x 5 11)
                have b9043 := hb (x 6 10)
                have b9044 := hb (x 7 9)
                have b9045 := hb (x 8 8)
                linarith only [r9031, e9032, e9033, e9034, e9035, e9036, e9037, b9038, b9039, b9040, b9041, b9042, b9043, b9044, b9045, d8966, d8982, d8998, d9027, d8566, d8586, d8014, f8965]
            · have f9046 : (x (-1) 4).toNat = 1 := by rw [h8723]; rfl
              have d9047 : (x (-1) 12).toNat = 1 := by
                have r9048 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
                have b9049 := hb (x (-1) 4)
                have b9050 := hb (x (-1) 12)
                clear * - r9048 b9049 b9050 f9046
                omega
              have d9051 : (x (-2) 13).toNat = 0 := by
                have r9052 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e9053 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                have e9054 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                have b9055 := hb (x (-4) 3)
                have b9056 := hb (x (-3) 2)
                have b9057 := hb (x (-2) 13)
                have b9058 := hb (x (-1) 12)
                clear * - r9052 e9053 e9054 b9055 b9056 b9057 b9058 d9047
                omega
              have d9059 : (x (-4) 2).toNat = 1 := by
                have r9060 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b9061 := hb (x (-4) 2)
                have b9062 := hb (x (-2) 13)
                have b9063 := hb (x (-3) 1 && x (-3) 14)
                clear * - r9060 b9061 b9062 b9063 d9051 d7359
                omega
              have d9064 : (x (-4) 14).toNat = 1 := by
                have r9065 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
                have b9066 := hb (x (-4) 2)
                have b9067 := hb (x (-4) 14)
                clear * - r9065 b9066 b9067 d9059
                omega
              have d9068 : (x (-5) 1).toNat = 0 := by
                have r9069 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b9070 := hb (x (-5) 1)
                have b9071 := hb (x (-4) 14)
                clear * - r9069 b9070 b9071 d9064
                omega
              have d9072 : (x (-5) 13).toNat = 0 := by
                have r9073 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
                have b9074 := hb (x (-5) 1)
                have b9075 := hb (x (-5) 13)
                clear * - r9073 b9074 b9075 d9068
                omega
              have d9076 : (x (-3) 2).toNat = 0 := by
                have r9077 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e9078 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                have e9079 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                have b9080 := hb (x (-4) 3)
                have b9081 := hb (x (-3) 2)
                have b9082 := hb (x (-2) 13)
                have b9083 := hb (x (-1) 12)
                clear * - r9077 e9078 e9079 b9080 b9081 b9082 b9083 d9047 d9051
                omega
              have d9084 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
                have r9085 := hand1 (x (-3) 2) (x (-3) 12)
                have b9086 := hb (x (-3) 2)
                have b9087 := hb (x (-3) 2 && x (-3) 12)
                clear * - r9085 b9086 b9087 d9076
                omega
              have d9088 : (x (-4) 3).toNat = 0 := by
                have r9089 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e9090 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                have e9091 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                have b9092 := hb (x (-4) 3)
                have b9093 := hb (x (-3) 2)
                have b9094 := hb (x (-2) 13)
                have b9095 := hb (x (-1) 12)
                clear * - r9089 e9090 e9091 b9092 b9093 b9094 b9095 d9047 d9051 d9076
                omega
              have d9096 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
                have r9097 := hand1 (x (-4) 3) (x (-4) 14)
                have b9098 := hb (x (-4) 3)
                have b9099 := hb (x (-4) 3 && x (-4) 14)
                clear * - r9097 b9098 b9099 d9088
                omega
              have d9100 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
                have r9101 := hand1 (x (-4) 3) (x (-4) 13)
                have b9102 := hb (x (-4) 3)
                have b9103 := hb (x (-4) 3 && x (-4) 13)
                clear * - r9101 b9102 b9103 d9088
                omega
              have d9104 : (x (-2) 12).toNat = 0 := by
                have r9105 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e9106 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                have e9107 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                have b9108 := hb (x (-5) 3)
                have b9109 := hb (x (-4) 2)
                have b9110 := hb (x (-3) 13)
                have b9111 := hb (x (-2) 12)
                clear * - r9105 e9106 e9107 b9108 b9109 b9110 b9111 d7363 d9059
                omega
              have d9112 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
                have r9113 := hand2 (x (-2) 1) (x (-2) 12)
                have b9114 := hb (x (-2) 12)
                have b9115 := hb (x (-2) 1 && x (-2) 12)
                clear * - r9113 b9114 b9115 d9104
                omega
              have d9116 : (x (-5) 4).toNat = 1 := by
                have r9117 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b9118 := hb (x (-5) 4)
                have b9119 := hb (x (-1) 11)
                have b9120 := hb (x (-2) 1 && x (-2) 12)
                have b9121 := hb (x (-3) 2 && x (-3) 13)
                have b9122 := hb (x (-4) 3 && x (-4) 14)
                clear * - r9117 b9118 b9119 b9120 b9121 b9122 d8085 d9112 d7367 d9096
                omega
              have d9123 : (x (-5) 12).toNat = 1 := by
                have r9124 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
                have b9125 := hb (x (-5) 4)
                have b9126 := hb (x (-5) 12)
                clear * - r9124 b9125 b9126 d9116
                omega
              have d9127 : (x (-6) 13).toNat = 0 := by
                have r9128 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e9129 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                have e9130 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                have b9131 := hb (x (-8) 3)
                have b9132 := hb (x (-7) 2)
                have b9133 := hb (x (-6) 13)
                have b9134 := hb (x (-5) 12)
                clear * - r9128 e9129 e9130 b9131 b9132 b9133 b9134 d9123
                omega
              have d9135 : (x (-6) 5).toNat = 0 := by
                have r9136 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
                have b9137 := hb (x (-6) 5)
                have b9138 := hb (x (-6) 13)
                clear * - r9136 b9137 b9138 d9127
                omega
              have d9139 : (x (-7) 2).toNat = 0 := by
                have r9140 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e9141 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                have e9142 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                have b9143 := hb (x (-8) 3)
                have b9144 := hb (x (-7) 2)
                have b9145 := hb (x (-6) 13)
                have b9146 := hb (x (-5) 12)
                clear * - r9140 e9141 e9142 b9143 b9144 b9145 b9146 d9123 d9127
                omega
              have d9147 : (x (-6) 1 && x (-6) 14).toNat = 1 := by
                have r9148 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b9149 := hb (x (-7) 2)
                have b9150 := hb (x (-5) 13)
                have b9151 := hb (x (-6) 1 && x (-6) 14)
                clear * - r9148 b9149 b9150 b9151 d9072 d9139
                omega
              have d9152 : (x (-6) 1).toNat = 1 := by
                have r9153 := hand1 (x (-6) 1) (x (-6) 14)
                have b9154 := hb (x (-6) 1)
                have b9155 := hb (x (-6) 1 && x (-6) 14)
                clear * - r9153 b9154 b9155 d9147
                omega
              have d9156 : (x (-5) 14).toNat = 0 := by
                have r9157 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b9158 := hb (x (-6) 1)
                have b9159 := hb (x (-5) 14)
                clear * - r9157 b9158 b9159 d9152
                omega
              have d9160 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
                have r9161 := hand2 (x (-5) 4) (x (-5) 14)
                have b9162 := hb (x (-5) 14)
                have b9163 := hb (x (-5) 4 && x (-5) 14)
                clear * - r9161 b9162 b9163 d9156
                omega
              have r9164 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b9165 := hb (x (-6) 5)
              have b9166 := hb (x (-1) 10)
              have b9167 := hb (x (-2) 1 && x (-2) 11)
              have b9168 := hb (x (-3) 2 && x (-3) 12)
              have b9169 := hb (x (-4) 3 && x (-4) 13)
              have b9170 := hb (x (-5) 4 && x (-5) 14)
              linarith only [r9164, b9165, b9166, b9167, b9168, b9169, b9170, d8048, d8630, d9084, d9100, d9160, d9135]
        · have f9171 : (x (-1) 2).toNat = 1 := by rw [h8046]; rfl
          have d9172 : (x (-1) 14).toNat = 1 := by
            have r9173 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
            have b9174 := hb (x (-1) 2)
            have b9175 := hb (x (-1) 14)
            clear * - r9173 b9174 b9175 f9171
            omega
          have d9176 : (x (-2) 1).toNat = 0 := by
            have r9177 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b9178 := hb (x (-2) 1)
            have b9179 := hb (x (-1) 14)
            clear * - r9177 b9178 b9179 d9172
            omega
          have d9180 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
            have r9181 := hand1 (x (-2) 1) (x (-2) 14)
            have b9182 := hb (x (-2) 1)
            have b9183 := hb (x (-2) 1 && x (-2) 14)
            clear * - r9181 b9182 b9183 d9176
            omega
          have d9184 : (x (-2) 13).toNat = 0 := by
            have r9185 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
            have b9186 := hb (x (-2) 1)
            have b9187 := hb (x (-2) 13)
            clear * - r9185 b9186 b9187 d9176
            omega
          have d9188 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
            have r9189 := hand2 (x (-2) 2) (x (-2) 13)
            have b9190 := hb (x (-2) 13)
            have b9191 := hb (x (-2) 2 && x (-2) 13)
            clear * - r9189 b9190 b9191 d9184
            omega
          have d9192 : (x (-3) 2).toNat = 1 := by
            have r9193 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b9194 := hb (x (-3) 2)
            have b9195 := hb (x (-1) 13)
            have b9196 := hb (x (-2) 1 && x (-2) 14)
            clear * - r9193 b9194 b9195 b9196 d7322 d9180
            omega
          have d9197 : (x (-3) 14).toNat = 1 := by
            have r9198 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
            have b9199 := hb (x (-3) 2)
            have b9200 := hb (x (-3) 14)
            clear * - r9198 b9199 b9200 d9192
            omega
          have d9201 : (x (-4) 1).toNat = 0 := by
            have r9202 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b9203 := hb (x (-4) 1)
            have b9204 := hb (x (-3) 14)
            clear * - r9202 b9203 b9204 d9197
            omega
          have d9205 : (x (-4) 13).toNat = 0 := by
            have r9206 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
            have b9207 := hb (x (-4) 1)
            have b9208 := hb (x (-4) 13)
            clear * - r9206 b9207 b9208 d9201
            omega
          have d9209 : (x (-4) 2).toNat = 1 := by
            have r9210 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b9211 := hb (x (-4) 2)
            have b9212 := hb (x (-2) 13)
            have b9213 := hb (x (-3) 1 && x (-3) 14)
            clear * - r9210 b9211 b9212 b9213 d9184 d7359
            omega
          have d9214 : (x (-4) 14).toNat = 1 := by
            have r9215 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
            have b9216 := hb (x (-4) 2)
            have b9217 := hb (x (-4) 14)
            clear * - r9215 b9216 b9217 d9209
            omega
          have d9218 : (x (-5) 1).toNat = 0 := by
            have r9219 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b9220 := hb (x (-5) 1)
            have b9221 := hb (x (-4) 14)
            clear * - r9219 b9220 b9221 d9214
            omega
          have d9222 : (x (-5) 1 && x (-5) 14).toNat = 0 := by
            have r9223 := hand1 (x (-5) 1) (x (-5) 14)
            have b9224 := hb (x (-5) 1)
            have b9225 := hb (x (-5) 1 && x (-5) 14)
            clear * - r9223 b9224 b9225 d9218
            omega
          have d9226 : (x (-5) 13).toNat = 0 := by
            have r9227 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
            have b9228 := hb (x (-5) 1)
            have b9229 := hb (x (-5) 13)
            clear * - r9227 b9228 b9229 d9218
            omega
          have d9230 : (x (-6) 2).toNat = 1 := by
            have r9231 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b9232 := hb (x (-6) 2)
            have b9233 := hb (x (-4) 13)
            have b9234 := hb (x (-5) 1 && x (-5) 14)
            clear * - r9231 b9232 b9233 b9234 d9205 d9222
            omega
          have d9235 : (x (-4) 12).toNat = 0 := by
            have r9236 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e9237 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
            have e9238 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
            have b9239 := hb (x (-7) 3)
            have b9240 := hb (x (-6) 2)
            have b9241 := hb (x (-5) 13)
            have b9242 := hb (x (-4) 12)
            clear * - r9236 e9237 e9238 b9239 b9240 b9241 b9242 d9226 d9230
            omega
          have d9243 : (x (-4) 4).toNat = 0 := by
            have r9244 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
            have b9245 := hb (x (-4) 4)
            have b9246 := hb (x (-4) 12)
            clear * - r9244 b9245 b9246 d9235
            omega
          have r9247 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b9248 := hb (x (-4) 4)
          have b9249 := hb (x 0 11)
          have b9250 := hb (x (-1) 1 && x (-1) 12)
          have b9251 := hb (x (-2) 2 && x (-2) 13)
          have b9252 := hb (x (-3) 3 && x (-3) 14)
          linarith only [r9247, b9248, b9249, b9250, b9251, b9252, d7427, d7314, d9188, d7403, d9243]
    · have f9253 : (x 0 3).toNat = 1 := by rw [h7421]; rfl
      have d9254 : (x 3 12).toNat = 0 := by
        have r9255 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9256 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
        have e9257 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
        have b9258 := hb (x 0 3)
        have b9259 := hb (x 1 2)
        have b9260 := hb (x 2 13)
        have b9261 := hb (x 3 12)
        clear * - r9255 e9256 e9257 b9258 b9259 b9260 b9261 f9253
        omega
      have d9262 : (x 3 1 && x 3 12).toNat = 0 := by
        have r9263 := hand2 (x 3 1) (x 3 12)
        have b9264 := hb (x 3 12)
        have b9265 := hb (x 3 1 && x 3 12)
        clear * - r9263 b9264 b9265 d9254
        omega
      have d9266 : (x 2 13).toNat = 0 := by
        have r9267 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9268 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
        have e9269 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
        have b9270 := hb (x 0 3)
        have b9271 := hb (x 1 2)
        have b9272 := hb (x 2 13)
        have b9273 := hb (x 3 12)
        clear * - r9267 e9268 e9269 b9270 b9271 b9272 b9273 d9254 f9253
        omega
      have d9274 : (x 2 2 && x 2 13).toNat = 0 := by
        have r9275 := hand2 (x 2 2) (x 2 13)
        have b9276 := hb (x 2 13)
        have b9277 := hb (x 2 2 && x 2 13)
        clear * - r9275 b9276 b9277 d9266
        omega
      have d9278 : (x 1 1 && x 1 14).toNat = 1 := by
        have r9279 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9280 := hb (x 0 2)
        have b9281 := hb (x 2 13)
        have b9282 := hb (x 1 1 && x 1 14)
        clear * - r9279 b9280 b9281 b9282 d9266 f7416
        omega
      have d9283 : (x 1 1).toNat = 1 := by
        have r9284 := hand1 (x 1 1) (x 1 14)
        have b9285 := hb (x 1 1)
        have b9286 := hb (x 1 1 && x 1 14)
        clear * - r9284 b9285 b9286 d9278
        omega
      have d9287 : (x 2 14).toNat = 0 := by
        have r9288 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9289 := hb (x 1 1)
        have b9290 := hb (x 2 14)
        clear * - r9288 b9289 b9290 d9283
        omega
      have d9291 : (x 2 1 && x 2 14).toNat = 0 := by
        have r9292 := hand2 (x 2 1) (x 2 14)
        have b9293 := hb (x 2 14)
        have b9294 := hb (x 2 1 && x 2 14)
        clear * - r9292 b9293 b9294 d9287
        omega
      have d9295 : (x 2 2).toNat = 0 := by
        have r9296 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
        have b9297 := hb (x 2 2)
        have b9298 := hb (x 2 14)
        clear * - r9296 b9297 b9298 d9287
        omega
      have d9299 : (x 1 2).toNat = 0 := by
        have r9300 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9301 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
        have e9302 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
        have b9303 := hb (x 0 3)
        have b9304 := hb (x 1 2)
        have b9305 := hb (x 2 13)
        have b9306 := hb (x 3 12)
        clear * - r9300 e9301 e9302 b9303 b9304 b9305 b9306 d9254 d9266 f9253
        omega
      have d9307 : (x 3 13).toNat = 1 := by
        have r9308 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9309 := hb (x 1 2)
        have b9310 := hb (x 3 13)
        have b9311 := hb (x 2 1 && x 2 14)
        clear * - r9308 b9309 b9310 b9311 d9291 d9299
        omega
      have d9312 : (x 4 12).toNat = 0 := by
        have r9313 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9314 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e9315 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b9316 := hb (x 1 3)
        have b9317 := hb (x 2 2)
        have b9318 := hb (x 3 13)
        have b9319 := hb (x 4 12)
        clear * - r9313 e9314 e9315 b9316 b9317 b9318 b9319 d9307 d9295
        omega
      have d9320 : (x 1 3).toNat = 0 := by
        have r9321 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9322 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e9323 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b9324 := hb (x 1 3)
        have b9325 := hb (x 2 2)
        have b9326 := hb (x 3 13)
        have b9327 := hb (x 4 12)
        clear * - r9321 e9322 e9323 b9324 b9325 b9326 b9327 d9312 d9307 d9295
        omega
      have d9328 : (x 1 3 && x 1 14).toNat = 0 := by
        have r9329 := hand1 (x 1 3) (x 1 14)
        have b9330 := hb (x 1 3)
        have b9331 := hb (x 1 3 && x 1 14)
        clear * - r9329 b9330 b9331 d9320
        omega
      have r9332 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9333 := hb (x 0 4)
      have b9334 := hb (x 4 11)
      have b9335 := hb (x 3 1 && x 3 12)
      have b9336 := hb (x 2 2 && x 2 13)
      have b9337 := hb (x 1 3 && x 1 14)
      linarith only [r9332, b9333, b9334, b9335, b9336, b9337, g8, d9262, d9274, d9328, d7387]
  · have f9338 : (x 0 2).toNat = 1 := by rw [h7415]; rfl
    have d9339 : (x 2 12).toNat = 0 := by
      have r9340 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9341 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e9342 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b9343 := hb (x (-1) 3)
      have b9344 := hb (x 0 2)
      have b9345 := hb (x 1 13)
      have b9346 := hb (x 2 12)
      clear * - r9340 e9341 e9342 b9343 b9344 b9345 b9346 f9338
      omega
    have d9347 : (x 2 1 && x 2 12).toNat = 0 := by
      have r9348 := hand2 (x 2 1) (x 2 12)
      have b9349 := hb (x 2 12)
      have b9350 := hb (x 2 1 && x 2 12)
      clear * - r9348 b9349 b9350 d9339
      omega
    have d9351 : (x 1 13).toNat = 0 := by
      have r9352 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9353 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e9354 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b9355 := hb (x (-1) 3)
      have b9356 := hb (x 0 2)
      have b9357 := hb (x 1 13)
      have b9358 := hb (x 2 12)
      clear * - r9352 e9353 e9354 b9355 b9356 b9357 b9358 d9339 f9338
      omega
    have d9359 : (x 1 2 && x 1 13).toNat = 0 := by
      have r9360 := hand2 (x 1 2) (x 1 13)
      have b9361 := hb (x 1 13)
      have b9362 := hb (x 1 2 && x 1 13)
      clear * - r9360 b9361 b9362 d9351
      omega
    have d9363 : (x (-1) 2).toNat = 1 := by
      have r9364 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9365 := hb (x (-1) 2)
      have b9366 := hb (x 1 13)
      have b9367 := hb (x 0 1 && x 0 14)
      clear * - r9364 b9365 b9366 b9367 d9351 g24
      omega
    have d9368 : (x (-1) 14).toNat = 1 := by
      have r9369 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
      have b9370 := hb (x (-1) 2)
      have b9371 := hb (x (-1) 14)
      clear * - r9369 b9370 b9371 d9363
      omega
    have d9372 : (x (-2) 1).toNat = 0 := by
      have r9373 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9374 := hb (x (-2) 1)
      have b9375 := hb (x (-1) 14)
      clear * - r9373 b9374 b9375 d9368
      omega
    have d9376 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
      have r9377 := hand1 (x (-2) 1) (x (-2) 14)
      have b9378 := hb (x (-2) 1)
      have b9379 := hb (x (-2) 1 && x (-2) 14)
      clear * - r9377 b9378 b9379 d9372
      omega
    have d9380 : (x (-3) 2).toNat = 1 := by
      have r9381 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9382 := hb (x (-3) 2)
      have b9383 := hb (x (-1) 13)
      have b9384 := hb (x (-2) 1 && x (-2) 14)
      clear * - r9381 b9382 b9383 b9384 d7322 d9376
      omega
    have d9385 : (x (-3) 14).toNat = 1 := by
      have r9386 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
      have b9387 := hb (x (-3) 2)
      have b9388 := hb (x (-3) 14)
      clear * - r9386 b9387 b9388 d9380
      omega
    have d9389 : (x (-4) 1).toNat = 0 := by
      have r9390 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9391 := hb (x (-4) 1)
      have b9392 := hb (x (-3) 14)
      clear * - r9390 b9391 b9392 d9385
      omega
    have d9393 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
      have r9394 := hand1 (x (-4) 1) (x (-4) 14)
      have b9395 := hb (x (-4) 1)
      have b9396 := hb (x (-4) 1 && x (-4) 14)
      clear * - r9394 b9395 b9396 d9389
      omega
    have d9397 : (x (-5) 2).toNat = 1 := by
      have r9398 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9399 := hb (x (-5) 2)
      have b9400 := hb (x (-3) 13)
      have b9401 := hb (x (-4) 1 && x (-4) 14)
      clear * - r9398 b9399 b9400 b9401 d7363 d9393
      omega
    have d9402 : (x (-4) 13).toNat = 0 := by
      have r9403 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
      have b9404 := hb (x (-4) 1)
      have b9405 := hb (x (-4) 13)
      clear * - r9403 b9404 b9405 d9389
      omega
    have d9406 : (x (-2) 13).toNat = 0 := by
      have r9407 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
      have b9408 := hb (x (-2) 1)
      have b9409 := hb (x (-2) 13)
      clear * - r9407 b9408 b9409 d9372
      omega
    have d9410 : (x (-4) 2).toNat = 1 := by
      have r9411 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9412 := hb (x (-4) 2)
      have b9413 := hb (x (-2) 13)
      have b9414 := hb (x (-3) 1 && x (-3) 14)
      clear * - r9411 b9412 b9413 b9414 d9406 d7359
      omega
    have d9415 : (x (-1) 3).toNat = 0 := by
      have r9416 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9417 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e9418 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b9419 := hb (x (-1) 3)
      have b9420 := hb (x 0 2)
      have b9421 := hb (x 1 13)
      have b9422 := hb (x 2 12)
      clear * - r9416 e9417 e9418 b9419 b9420 b9421 b9422 d9339 d9351 f9338
      omega
    have d9423 : (x (-1) 3 && x (-1) 14).toNat = 0 := by
      have r9424 := hand1 (x (-1) 3) (x (-1) 14)
      have b9425 := hb (x (-1) 3)
      have b9426 := hb (x (-1) 3 && x (-1) 14)
      clear * - r9424 b9425 b9426 d9415
      omega
    have d9427 : (x 1 12).toNat = 0 := by
      have r9428 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9429 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e9430 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b9431 := hb (x (-2) 3)
      have b9432 := hb (x (-1) 2)
      have b9433 := hb (x 0 13)
      have b9434 := hb (x 1 12)
      clear * - r9428 e9429 e9430 b9431 b9432 b9433 b9434 g4 d9363
      omega
    have d9435 : (x 1 1 && x 1 12).toNat = 0 := by
      have r9436 := hand2 (x 1 1) (x 1 12)
      have b9437 := hb (x 1 12)
      have b9438 := hb (x 1 1 && x 1 12)
      clear * - r9436 b9437 b9438 d9427
      omega
    have d9439 : (x (-2) 3).toNat = 0 := by
      have r9440 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9441 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e9442 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b9443 := hb (x (-2) 3)
      have b9444 := hb (x (-1) 2)
      have b9445 := hb (x 0 13)
      have b9446 := hb (x 1 12)
      clear * - r9440 e9441 e9442 b9443 b9444 b9445 b9446 d9427 g4 d9363
      omega
    have d9447 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
      have r9448 := hand1 (x (-2) 3) (x (-2) 14)
      have b9449 := hb (x (-2) 3)
      have b9450 := hb (x (-2) 3 && x (-2) 14)
      clear * - r9448 b9449 b9450 d9439
      omega
    have d9451 : (x (-1) 12).toNat = 0 := by
      have r9452 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9453 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e9454 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b9455 := hb (x (-4) 3)
      have b9456 := hb (x (-3) 2)
      have b9457 := hb (x (-2) 13)
      have b9458 := hb (x (-1) 12)
      clear * - r9452 e9453 e9454 b9455 b9456 b9457 b9458 d9406 d9380
      omega
    have d9459 : (x (-1) 4).toNat = 0 := by
      have r9460 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
      have b9461 := hb (x (-1) 4)
      have b9462 := hb (x (-1) 12)
      clear * - r9460 b9461 b9462 d9451
      omega
    have d9463 : (x (-2) 12).toNat = 0 := by
      have r9464 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9465 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e9466 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have b9467 := hb (x (-5) 3)
      have b9468 := hb (x (-4) 2)
      have b9469 := hb (x (-3) 13)
      have b9470 := hb (x (-2) 12)
      clear * - r9464 e9465 e9466 b9467 b9468 b9469 b9470 d7363 d9410
      omega
    have d9471 : (x (-2) 4).toNat = 0 := by
      have r9472 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
      have b9473 := hb (x (-2) 4)
      have b9474 := hb (x (-2) 12)
      clear * - r9472 b9473 b9474 d9463
      omega
    have d9475 : (x (-3) 12).toNat = 0 := by
      have r9476 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9477 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e9478 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b9479 := hb (x (-6) 3)
      have b9480 := hb (x (-5) 2)
      have b9481 := hb (x (-4) 13)
      have b9482 := hb (x (-3) 12)
      clear * - r9476 e9477 e9478 b9479 b9480 b9481 b9482 d9402 d9397
      omega
    have d9483 : (x (-3) 4).toNat = 0 := by
      have r9484 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
      have b9485 := hb (x (-3) 4)
      have b9486 := hb (x (-3) 12)
      clear * - r9484 b9485 b9486 d9475
      omega
    have d9487 : (x 2 11).toNat = 1 := by
      have r9488 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := by have q := hcov11 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9489 := hb (x (-2) 4)
      have b9490 := hb (x 2 11)
      have b9491 := hb (x 1 1 && x 1 12)
      have b9492 := hb (x 0 2 && x 0 13)
      have b9493 := hb (x (-1) 3 && x (-1) 14)
      clear * - r9488 b9489 b9490 b9491 b9492 b9493 d9435 g23 d9423 d9471
      omega
    have d9494 : (x 2 3).toNat = 1 := by
      have r9495 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
      have b9496 := hb (x 2 3)
      have b9497 := hb (x 2 11)
      clear * - r9495 b9496 b9497 d9487
      omega
    have d9498 : (x 5 12).toNat = 0 := by
      have r9499 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9500 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e9501 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b9502 := hb (x 2 3)
      have b9503 := hb (x 3 2)
      have b9504 := hb (x 4 13)
      have b9505 := hb (x 5 12)
      clear * - r9499 e9500 e9501 b9502 b9503 b9504 b9505 d9494
      omega
    have d9506 : (x 4 13).toNat = 0 := by
      have r9507 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9508 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e9509 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b9510 := hb (x 2 3)
      have b9511 := hb (x 3 2)
      have b9512 := hb (x 4 13)
      have b9513 := hb (x 5 12)
      clear * - r9507 e9508 e9509 b9510 b9511 b9512 b9513 d9498 d9494
      omega
    have d9514 : (x 3 2).toNat = 0 := by
      have r9515 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9516 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e9517 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b9518 := hb (x 2 3)
      have b9519 := hb (x 3 2)
      have b9520 := hb (x 4 13)
      have b9521 := hb (x 5 12)
      clear * - r9515 e9516 e9517 b9518 b9519 b9520 b9521 d9498 d9506 d9494
      omega
    have d9522 : (x 1 11).toNat = 1 := by
      have r9523 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9524 := hb (x (-3) 4)
      have b9525 := hb (x 1 11)
      have b9526 := hb (x 0 1 && x 0 12)
      have b9527 := hb (x (-1) 2 && x (-1) 13)
      have b9528 := hb (x (-2) 3 && x (-2) 14)
      clear * - r9523 b9524 b9525 b9526 b9527 b9528 g22 d7326 d9447 d9483
      omega
    have d9529 : (x 1 3).toNat = 1 := by
      have r9530 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
      have b9531 := hb (x 1 3)
      have b9532 := hb (x 1 11)
      clear * - r9530 b9531 b9532 d9522
      omega
    have d9533 : (x 4 12).toNat = 0 := by
      have r9534 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9535 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e9536 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b9537 := hb (x 1 3)
      have b9538 := hb (x 2 2)
      have b9539 := hb (x 3 13)
      have b9540 := hb (x 4 12)
      clear * - r9534 e9535 e9536 b9537 b9538 b9539 b9540 d9529
      omega
    have d9541 : (x 3 13).toNat = 0 := by
      have r9542 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9543 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e9544 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b9545 := hb (x 1 3)
      have b9546 := hb (x 2 2)
      have b9547 := hb (x 3 13)
      have b9548 := hb (x 4 12)
      clear * - r9542 e9543 e9544 b9545 b9546 b9547 b9548 d9533 d9529
      omega
    have d9549 : (x 2 2).toNat = 0 := by
      have r9550 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9551 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e9552 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b9553 := hb (x 1 3)
      have b9554 := hb (x 2 2)
      have b9555 := hb (x 3 13)
      have b9556 := hb (x 4 12)
      clear * - r9550 e9551 e9552 b9553 b9554 b9555 b9556 d9533 d9541 d9529
      omega
    have d9557 : (x 3 1 && x 3 14).toNat = 1 := by
      have r9558 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9559 := hb (x 2 2)
      have b9560 := hb (x 4 13)
      have b9561 := hb (x 3 1 && x 3 14)
      clear * - r9558 b9559 b9560 b9561 d9506 d9549
      omega
    have d9562 : (x 3 14).toNat = 1 := by
      have r9563 := hand2 (x 3 1) (x 3 14)
      have b9564 := hb (x 3 14)
      have b9565 := hb (x 3 1 && x 3 14)
      clear * - r9563 b9564 b9565 d9557
      omega
    have d9566 : (x 2 1).toNat = 0 := by
      have r9567 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9568 := hb (x 2 1)
      have b9569 := hb (x 3 14)
      clear * - r9567 b9568 b9569 d9562
      omega
    have d9570 : (x 2 1 && x 2 14).toNat = 0 := by
      have r9571 := hand1 (x 2 1) (x 2 14)
      have b9572 := hb (x 2 1)
      have b9573 := hb (x 2 1 && x 2 14)
      clear * - r9571 b9572 b9573 d9566
      omega
    have d9574 : (x 1 2).toNat = 1 := by
      have r9575 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9576 := hb (x 1 2)
      have b9577 := hb (x 3 13)
      have b9578 := hb (x 2 1 && x 2 14)
      clear * - r9575 b9576 b9577 b9578 d9541 d9570
      omega
    have d9579 : (x 3 12).toNat = 0 := by
      have r9580 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9581 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
      have e9582 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
      have b9583 := hb (x 0 3)
      have b9584 := hb (x 1 2)
      have b9585 := hb (x 2 13)
      have b9586 := hb (x 3 12)
      clear * - r9580 e9581 e9582 b9583 b9584 b9585 b9586 d9574
      omega
    have d9587 : (x 2 13).toNat = 0 := by
      have r9588 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9589 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
      have e9590 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
      have b9591 := hb (x 0 3)
      have b9592 := hb (x 1 2)
      have b9593 := hb (x 2 13)
      have b9594 := hb (x 3 12)
      clear * - r9588 e9589 e9590 b9591 b9592 b9593 b9594 d9579 d9574
      omega
    have d9595 : (x 0 3).toNat = 0 := by
      have r9596 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9597 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
      have e9598 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
      have b9599 := hb (x 0 3)
      have b9600 := hb (x 1 2)
      have b9601 := hb (x 2 13)
      have b9602 := hb (x 3 12)
      clear * - r9596 e9597 e9598 b9599 b9600 b9601 b9602 d9579 d9587 d9574
      omega
    have d9603 : (x 0 3 && x 0 14).toNat = 0 := by
      have r9604 := hand1 (x 0 3) (x 0 14)
      have b9605 := hb (x 0 3)
      have b9606 := hb (x 0 3 && x 0 14)
      clear * - r9604 b9605 b9606 d9595
      omega
    have d9607 : (x 3 11).toNat = 1 := by
      have r9608 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9609 := hb (x (-1) 4)
      have b9610 := hb (x 3 11)
      have b9611 := hb (x 2 1 && x 2 12)
      have b9612 := hb (x 1 2 && x 1 13)
      have b9613 := hb (x 0 3 && x 0 14)
      clear * - r9608 b9609 b9610 b9611 b9612 b9613 d9347 d9359 d9603 d9459
      omega
    have d9614 : (x 3 3).toNat = 1 := by
      have r9615 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
      have b9616 := hb (x 3 3)
      have b9617 := hb (x 3 11)
      clear * - r9615 b9616 b9617 d9607
      omega
    have d9618 : (x 6 12).toNat = 0 := by
      have r9619 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9620 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e9621 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b9622 := hb (x 3 3)
      have b9623 := hb (x 4 2)
      have b9624 := hb (x 5 13)
      have b9625 := hb (x 6 12)
      clear * - r9619 e9620 e9621 b9622 b9623 b9624 b9625 d9614
      omega
    have d9626 : (x 5 13).toNat = 0 := by
      have r9627 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9628 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e9629 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b9630 := hb (x 3 3)
      have b9631 := hb (x 4 2)
      have b9632 := hb (x 5 13)
      have b9633 := hb (x 6 12)
      clear * - r9627 e9628 e9629 b9630 b9631 b9632 b9633 d9618 d9614
      omega
    have d9634 : (x 4 1 && x 4 14).toNat = 1 := by
      have r9635 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9636 := hb (x 3 2)
      have b9637 := hb (x 5 13)
      have b9638 := hb (x 4 1 && x 4 14)
      clear * - r9635 b9636 b9637 b9638 d9626 d9514
      omega
    have d9639 : (x 4 14).toNat = 1 := by
      have r9640 := hand2 (x 4 1) (x 4 14)
      have b9641 := hb (x 4 14)
      have b9642 := hb (x 4 1 && x 4 14)
      clear * - r9640 b9641 b9642 d9634
      omega
    have d9643 : (x 3 1).toNat = 0 := by
      have r9644 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9645 := hb (x 3 1)
      have b9646 := hb (x 4 14)
      clear * - r9644 b9645 b9646 d9639
      omega
    have r9647 := hand1 (x 3 1) (x 3 14)
    have b9648 := hb (x 3 1)
    have b9649 := hb (x 3 1 && x 3 14)
    linarith only [r9647, b9648, b9649, d9557, d9643]

theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 5).toNat = 0)
    (g1 : (x 0 6).toNat = 0)
    (g2 : (x 0 8).toNat = 0)
    (g3 : (x 0 9).toNat = 0)
    (g4 : (x 0 13).toNat = 0)
    (g5 : (x 0 14).toNat = 1)
    (g6 : (x 1 6).toNat = 0)
    (g7 : (x 3 4).toNat = 0)
    (g8 : (x 4 11).toNat = 0)
    (g9 : (x 5 10).toNat = 0)
    (g10 : (x 6 9).toNat = 0)
    (g11 : (x 0 8 && x 0 12).toNat = 0)
    (g12 : (x 0 8 && x 0 14).toNat = 0)
    (g13 : (x 7 1 && x 7 8).toNat = 0)
    (g14 : (x 6 2 && x 6 9).toNat = 0)
    (g15 : (x 5 3 && x 5 10).toNat = 0)
    (g16 : (x 4 4 && x 4 11).toNat = 0)
    (g17 : (x 5 1 && x 5 10).toNat = 0)
    (g18 : (x 4 2 && x 4 11).toNat = 0)
    (g19 : (x 3 4 && x 3 13).toNat = 0)
    (g20 : (x 2 5 && x 2 14).toNat = 0)
    (g21 : (x 4 1 && x 4 11).toNat = 0)
    (g22 : (x 0 1 && x 0 12).toNat = 0)
    (g23 : (x 0 2 && x 0 13).toNat = 0)
    (g24 : (x 0 1 && x 0 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b001_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24
