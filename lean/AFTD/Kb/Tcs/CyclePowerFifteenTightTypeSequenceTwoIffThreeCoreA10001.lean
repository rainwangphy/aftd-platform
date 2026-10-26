import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a10001

Topic: combinatorics   Node: 23765a215cf7

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP; the same generator on the same window refutes x(0,2) != x(0,3) (a case-split tree of 109 + 3 nodes).

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_two_iff_three_core: under the layer-free tight-cover constraints for k = 15 and 30 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a10001_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-1) 5).toNat = 0)
    (g1 : (x (-1) 11).toNat = 0)
    (g2 : (x 0 3).toNat = 0)
    (g3 : (x 0 5).toNat = 0)
    (g4 : (x 0 6).toNat = 0)
    (g5 : (x 0 7).toNat = 1)
    (g6 : (x 0 14).toNat = 1)
    (g7 : (x 1 2).toNat = 0)
    (g8 : (x 1 5).toNat = 0)
    (g9 : (x 1 6).toNat = 0)
    (g10 : (x 1 10).toNat = 0)
    (g11 : (x 1 13).toNat = 0)
    (g12 : (x 2 4).toNat = 0)
    (g13 : (x 2 12).toNat = 0)
    (g14 : (x 2 8 && x 2 12).toNat = 0)
    (g15 : (x 1 9 && x 1 13).toNat = 0)
    (g16 : (x 2 4 && x 2 13).toNat = 0)
    (g17 : (x 1 5 && x 1 14).toNat = 0)
    (g18 : (x 0 1 && x 0 11).toNat = 0)
    (g19 : (x (-1) 2 && x (-1) 12).toNat = 0)
    (g20 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g21 : (x 0 2 && x 0 12).toNat = 0)
    (g22 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g23 : (x 2 2 && x 2 12).toNat = 0)
    (g24 : (x 1 3 && x 1 13).toNat = 0)
    (g25 : (x 0 4 && x 0 14).toNat = 0)
    (g26 : (x 1 4 && x 1 14).toNat = 0)
    (g27 : (x 0 1 && x 0 12).toNat = 0)
    (g28 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g29 : (x (-2) 3 && x (-2) 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d14980 : (x 7 8).toNat = 0 := by
    have r14981 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14982 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e14983 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e14984 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e14985 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e14986 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e14987 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b14988 := hb (x 0 7)
    have b14989 := hb (x 1 6)
    have b14990 := hb (x 2 5)
    have b14991 := hb (x 3 4)
    have b14992 := hb (x 4 11)
    have b14993 := hb (x 5 10)
    have b14994 := hb (x 6 9)
    have b14995 := hb (x 7 8)
    clear * - r14981 e14982 e14983 e14984 e14985 e14986 e14987 b14988 b14989 b14990 b14991 b14992 b14993 b14994 b14995 g9 g5
    omega
  have d14996 : (x 7 8 && x 7 12).toNat = 0 := by
    have r14997 := hand1 (x 7 8) (x 7 12)
    have b14998 := hb (x 7 8)
    have b14999 := hb (x 7 8 && x 7 12)
    clear * - r14997 b14998 b14999 d14980
    omega
  have d15000 : (x 6 9).toNat = 0 := by
    have r15001 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15002 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e15003 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e15004 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e15005 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e15006 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e15007 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b15008 := hb (x 0 7)
    have b15009 := hb (x 1 6)
    have b15010 := hb (x 2 5)
    have b15011 := hb (x 3 4)
    have b15012 := hb (x 4 11)
    have b15013 := hb (x 5 10)
    have b15014 := hb (x 6 9)
    have b15015 := hb (x 7 8)
    clear * - r15001 e15002 e15003 e15004 e15005 e15006 e15007 b15008 b15009 b15010 b15011 b15012 b15013 b15014 b15015 d14980 g9 g5
    omega
  have d15016 : (x 6 9 && x 6 13).toNat = 0 := by
    have r15017 := hand1 (x 6 9) (x 6 13)
    have b15018 := hb (x 6 9)
    have b15019 := hb (x 6 9 && x 6 13)
    clear * - r15017 b15018 b15019 d15000
    omega
  have d15020 : (x 5 10).toNat = 0 := by
    have r15021 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15022 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e15023 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e15024 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e15025 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e15026 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e15027 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b15028 := hb (x 0 7)
    have b15029 := hb (x 1 6)
    have b15030 := hb (x 2 5)
    have b15031 := hb (x 3 4)
    have b15032 := hb (x 4 11)
    have b15033 := hb (x 5 10)
    have b15034 := hb (x 6 9)
    have b15035 := hb (x 7 8)
    clear * - r15021 e15022 e15023 e15024 e15025 e15026 e15027 b15028 b15029 b15030 b15031 b15032 b15033 b15034 b15035 d14980 d15000 g9 g5
    omega
  have d15036 : (x 5 1 && x 5 10).toNat = 0 := by
    have r15037 := hand2 (x 5 1) (x 5 10)
    have b15038 := hb (x 5 10)
    have b15039 := hb (x 5 1 && x 5 10)
    clear * - r15037 b15038 b15039 d15020
    omega
  have d15040 : (x 4 11).toNat = 0 := by
    have r15041 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15042 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e15043 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e15044 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e15045 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e15046 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e15047 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b15048 := hb (x 0 7)
    have b15049 := hb (x 1 6)
    have b15050 := hb (x 2 5)
    have b15051 := hb (x 3 4)
    have b15052 := hb (x 4 11)
    have b15053 := hb (x 5 10)
    have b15054 := hb (x 6 9)
    have b15055 := hb (x 7 8)
    clear * - r15041 e15042 e15043 e15044 e15045 e15046 e15047 b15048 b15049 b15050 b15051 b15052 b15053 b15054 b15055 d14980 d15000 d15020 g9 g5
    omega
  have d15056 : (x 4 1 && x 4 11).toNat = 0 := by
    have r15057 := hand2 (x 4 1) (x 4 11)
    have b15058 := hb (x 4 11)
    have b15059 := hb (x 4 1 && x 4 11)
    clear * - r15057 b15058 b15059 d15040
    omega
  have d15060 : (x 4 2 && x 4 11).toNat = 0 := by
    have r15061 := hand2 (x 4 2) (x 4 11)
    have b15062 := hb (x 4 11)
    have b15063 := hb (x 4 2 && x 4 11)
    clear * - r15061 b15062 b15063 d15040
    omega
  have d15064 : (x 3 3 && x 3 12).toNat = 1 := by
    have r15065 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15066 := hb (x 0 6)
    have b15067 := hb (x 6 9)
    have b15068 := hb (x 5 1 && x 5 10)
    have b15069 := hb (x 4 2 && x 4 11)
    have b15070 := hb (x 3 3 && x 3 12)
    have b15071 := hb (x 2 4 && x 2 13)
    have b15072 := hb (x 1 5 && x 1 14)
    clear * - r15065 b15066 b15067 b15068 b15069 b15070 b15071 b15072 d15000 d15036 d15060 g16 g17 g4
    omega
  have d15073 : (x 3 12).toNat = 1 := by
    have r15074 := hand2 (x 3 3) (x 3 12)
    have b15075 := hb (x 3 12)
    have b15076 := hb (x 3 3 && x 3 12)
    clear * - r15074 b15075 b15076 d15064
    omega
  have d15077 : (x 2 13).toNat = 0 := by
    have r15078 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15079 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e15080 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b15081 := hb (x 0 3)
    have b15082 := hb (x 1 2)
    have b15083 := hb (x 2 13)
    have b15084 := hb (x 3 12)
    clear * - r15078 e15079 e15080 b15081 b15082 b15083 b15084 d15073 g7 g2
    omega
  have d15085 : (x 2 3 && x 2 13).toNat = 0 := by
    have r15086 := hand2 (x 2 3) (x 2 13)
    have b15087 := hb (x 2 13)
    have b15088 := hb (x 2 3 && x 2 13)
    clear * - r15086 b15087 b15088 d15077
    omega
  have d15089 : (x 3 2 && x 3 12).toNat = 1 := by
    have r15090 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15091 := hb (x 0 5)
    have b15092 := hb (x 5 10)
    have b15093 := hb (x 4 1 && x 4 11)
    have b15094 := hb (x 3 2 && x 3 12)
    have b15095 := hb (x 2 3 && x 2 13)
    have b15096 := hb (x 1 4 && x 1 14)
    clear * - r15090 b15091 b15092 b15093 b15094 b15095 b15096 d15020 d15056 d15085 g26 g3
    omega
  have d15097 : (x 3 2).toNat = 1 := by
    have r15098 := hand1 (x 3 2) (x 3 12)
    have b15099 := hb (x 3 2)
    have b15100 := hb (x 3 2 && x 3 12)
    clear * - r15098 b15099 b15100 d15089
    omega
  have d15101 : (x 3 14).toNat = 1 := by
    have r15102 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
    have b15103 := hb (x 3 2)
    have b15104 := hb (x 3 14)
    clear * - r15102 b15103 b15104 d15097
    omega
  have d15105 : (x 2 1).toNat = 0 := by
    have r15106 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15107 := hb (x 2 1)
    have b15108 := hb (x 3 14)
    clear * - r15106 b15107 b15108 d15101
    omega
  have d15109 : (x 2 1 && x 2 14).toNat = 0 := by
    have r15110 := hand1 (x 2 1) (x 2 14)
    have b15111 := hb (x 2 1)
    have b15112 := hb (x 2 1 && x 2 14)
    clear * - r15110 b15111 b15112 d15105
    omega
  have d15113 : (x 3 13).toNat = 1 := by
    have r15114 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15115 := hb (x 1 2)
    have b15116 := hb (x 3 13)
    have b15117 := hb (x 2 1 && x 2 14)
    clear * - r15114 b15115 b15116 b15117 d15109 g7
    omega
  have d15118 : (x 3 1).toNat = 1 := by
    have r15119 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
    have b15120 := hb (x 3 1)
    have b15121 := hb (x 3 13)
    clear * - r15119 b15120 b15121 d15113
    omega
  have d15122 : (x 4 14).toNat = 0 := by
    have r15123 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15124 := hb (x 3 1)
    have b15125 := hb (x 4 14)
    clear * - r15123 b15124 b15125 d15118
    omega
  have d15126 : (x 4 3 && x 4 14).toNat = 0 := by
    have r15127 := hand2 (x 4 3) (x 4 14)
    have b15128 := hb (x 4 14)
    have b15129 := hb (x 4 3 && x 4 14)
    clear * - r15127 b15128 b15129 d15122
    omega
  have d15130 : (x 4 6).toNat = 0 := by
    have r15131 : (x 4 6).toNat ≤ (x 4 14).toNat := himp _ _ (hp6 4)
    have b15132 := hb (x 4 6)
    have b15133 := hb (x 4 14)
    clear * - r15131 b15132 b15133 d15122
    omega
  have d15134 : (x 4 6 && x 4 12).toNat = 0 := by
    have r15135 := hand1 (x 4 6) (x 4 12)
    have b15136 := hb (x 4 6)
    have b15137 := hb (x 4 6 && x 4 12)
    clear * - r15135 b15136 b15137 d15130
    omega
  have d15138 : (x 4 6 && x 4 10).toNat = 0 := by
    have r15139 := hand1 (x 4 6) (x 4 10)
    have b15140 := hb (x 4 6)
    have b15141 := hb (x 4 6 && x 4 10)
    clear * - r15139 b15140 b15141 d15130
    omega
  have d15142 : (x 4 2).toNat = 0 := by
    have r15143 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
    have b15144 := hb (x 4 2)
    have b15145 := hb (x 4 14)
    clear * - r15143 b15144 b15145 d15122
    omega
  have d15146 : (x 4 10).toNat = 0 := by
    have r15147 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
    have b15148 := hb (x 4 2)
    have b15149 := hb (x 4 10)
    clear * - r15147 b15148 b15149 d15142
    omega
  have d15150 : (x 3 1 && x 3 11).toNat = 1 := by
    have r15151 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15152 := hb (x (-1) 5)
    have b15153 := hb (x 4 10)
    have b15154 := hb (x 3 1 && x 3 11)
    have b15155 := hb (x 2 2 && x 2 12)
    have b15156 := hb (x 1 3 && x 1 13)
    have b15157 := hb (x 0 4 && x 0 14)
    clear * - r15151 b15152 b15153 b15154 b15155 b15156 b15157 d15146 g23 g24 g25 g0
    omega
  have d15158 : (x 3 11).toNat = 1 := by
    have r15159 := hand2 (x 3 1) (x 3 11)
    have b15160 := hb (x 3 11)
    have b15161 := hb (x 3 1 && x 3 11)
    clear * - r15159 b15160 b15161 d15150
    omega
  have d15162 : (x 3 3).toNat = 1 := by
    have r15163 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
    have b15164 := hb (x 3 3)
    have b15165 := hb (x 3 11)
    clear * - r15163 b15164 b15165 d15158
    omega
  have d15166 : (x 6 12).toNat = 0 := by
    have r15167 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15168 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e15169 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b15170 := hb (x 3 3)
    have b15171 := hb (x 4 2)
    have b15172 := hb (x 5 13)
    have b15173 := hb (x 6 12)
    clear * - r15167 e15168 e15169 b15170 b15171 b15172 b15173 d15142 d15162
    omega
  have d15174 : (x 6 1 && x 6 12).toNat = 0 := by
    have r15175 := hand2 (x 6 1) (x 6 12)
    have b15176 := hb (x 6 12)
    have b15177 := hb (x 6 1 && x 6 12)
    clear * - r15175 b15176 b15177 d15166
    omega
  have d15178 : (x 6 4).toNat = 0 := by
    have r15179 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
    have b15180 := hb (x 6 4)
    have b15181 := hb (x 6 12)
    clear * - r15179 b15180 b15181 d15166
    omega
  have d15182 : (x 6 4 && x 6 10).toNat = 0 := by
    have r15183 := hand1 (x 6 4) (x 6 10)
    have b15184 := hb (x 6 4)
    have b15185 := hb (x 6 4 && x 6 10)
    clear * - r15183 b15184 b15185 d15178
    omega
  have d15186 : (x 6 4 && x 6 8).toNat = 0 := by
    have r15187 := hand1 (x 6 4) (x 6 8)
    have b15188 := hb (x 6 4)
    have b15189 := hb (x 6 4 && x 6 8)
    clear * - r15187 b15188 b15189 d15178
    omega
  have d15190 : (x 5 13).toNat = 0 := by
    have r15191 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15192 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e15193 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b15194 := hb (x 3 3)
    have b15195 := hb (x 4 2)
    have b15196 := hb (x 5 13)
    have b15197 := hb (x 6 12)
    clear * - r15191 e15192 e15193 b15194 b15195 b15196 b15197 d15166 d15142 d15162
    omega
  have d15198 : (x 5 2 && x 5 13).toNat = 0 := by
    have r15199 := hand2 (x 5 2) (x 5 13)
    have b15200 := hb (x 5 13)
    have b15201 := hb (x 5 2 && x 5 13)
    clear * - r15199 b15200 b15201 d15190
    omega
  have d15202 : (x 5 5).toNat = 0 := by
    have r15203 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
    have b15204 := hb (x 5 5)
    have b15205 := hb (x 5 13)
    clear * - r15203 b15204 b15205 d15190
    omega
  have d15206 : (x 5 5 && x 5 11).toNat = 0 := by
    have r15207 := hand1 (x 5 5) (x 5 11)
    have b15208 := hb (x 5 5)
    have b15209 := hb (x 5 5 && x 5 11)
    clear * - r15207 b15208 b15209 d15202
    omega
  have d15210 : (x 5 5 && x 5 9).toNat = 0 := by
    have r15211 := hand1 (x 5 5) (x 5 9)
    have b15212 := hb (x 5 5)
    have b15213 := hb (x 5 5 && x 5 9)
    clear * - r15211 b15212 b15213 d15202
    omega
  have d15214 : (x 4 12).toNat = 0 := by
    have r15215 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15216 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e15217 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b15218 := hb (x 1 3)
    have b15219 := hb (x 2 2)
    have b15220 := hb (x 3 13)
    have b15221 := hb (x 4 12)
    clear * - r15215 e15216 e15217 b15218 b15219 b15220 b15221 d15113
    omega
  have d15222 : (x 2 2).toNat = 0 := by
    have r15223 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15224 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e15225 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b15226 := hb (x 1 3)
    have b15227 := hb (x 2 2)
    have b15228 := hb (x 3 13)
    have b15229 := hb (x 4 12)
    clear * - r15223 e15224 e15225 b15226 b15227 b15228 b15229 d15214 d15113
    omega
  have d15230 : (x 2 10).toNat = 0 := by
    have r15231 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
    have b15232 := hb (x 2 2)
    have b15233 := hb (x 2 10)
    clear * - r15231 b15232 b15233 d15222
    omega
  have d15234 : (x 1 3).toNat = 0 := by
    have r15235 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15236 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e15237 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b15238 := hb (x 1 3)
    have b15239 := hb (x 2 2)
    have b15240 := hb (x 3 13)
    have b15241 := hb (x 4 12)
    clear * - r15235 e15236 e15237 b15238 b15239 b15240 b15241 d15214 d15113 d15222
    omega
  have d15242 : (x 1 11).toNat = 0 := by
    have r15243 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
    have b15244 := hb (x 1 3)
    have b15245 := hb (x 1 11)
    clear * - r15243 b15244 b15245 d15234
    omega
  have d15246 : (x 1 1 && x 1 11).toNat = 0 := by
    have r15247 := hand2 (x 1 1) (x 1 11)
    have b15248 := hb (x 1 11)
    have b15249 := hb (x 1 1 && x 1 11)
    clear * - r15247 b15248 b15249 d15242
    omega
  have d15250 : (x (-3) 4).toNat = 1 := by
    have r15251 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15252 := hb (x (-3) 4)
    have b15253 := hb (x 1 11)
    have b15254 := hb (x 0 1 && x 0 12)
    have b15255 := hb (x (-1) 2 && x (-1) 13)
    have b15256 := hb (x (-2) 3 && x (-2) 14)
    clear * - r15251 b15252 b15253 b15254 b15255 b15256 d15242 g27 g28 g29
    omega
  have d15257 : (x (-3) 12).toNat = 1 := by
    have r15258 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
    have b15259 := hb (x (-3) 4)
    have b15260 := hb (x (-3) 12)
    clear * - r15258 b15259 b15260 d15250
    omega
  have d15261 : (x (-4) 13).toNat = 0 := by
    have r15262 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15263 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
    have e15264 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
    have b15265 := hb (x (-6) 3)
    have b15266 := hb (x (-5) 2)
    have b15267 := hb (x (-4) 13)
    have b15268 := hb (x (-3) 12)
    clear * - r15262 e15263 e15264 b15265 b15266 b15267 b15268 d15257
    omega
  have d15269 : (x (-4) 5).toNat = 0 := by
    have r15270 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
    have b15271 := hb (x (-4) 5)
    have b15272 := hb (x (-4) 13)
    clear * - r15270 b15271 b15272 d15261
    omega
  have d15273 : (x (-3) 4 && x (-3) 14).toNat = 1 := by
    have r15274 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15275 := hb (x (-4) 5)
    have b15276 := hb (x 1 10)
    have b15277 := hb (x 0 1 && x 0 11)
    have b15278 := hb (x (-1) 2 && x (-1) 12)
    have b15279 := hb (x (-2) 3 && x (-2) 13)
    have b15280 := hb (x (-3) 4 && x (-3) 14)
    clear * - r15274 b15275 b15276 b15277 b15278 b15279 b15280 g10 g18 g19 g20 d15269
    omega
  have d15281 : (x (-3) 14).toNat = 1 := by
    have r15282 := hand2 (x (-3) 4) (x (-3) 14)
    have b15283 := hb (x (-3) 14)
    have b15284 := hb (x (-3) 4 && x (-3) 14)
    clear * - r15282 b15283 b15284 d15273
    omega
  have d15285 : (x (-4) 1).toNat = 0 := by
    have r15286 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15287 := hb (x (-4) 1)
    have b15288 := hb (x (-3) 14)
    clear * - r15286 b15287 b15288 d15281
    omega
  have d15289 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
    have r15290 := hand1 (x (-4) 1) (x (-4) 14)
    have b15291 := hb (x (-4) 1)
    have b15292 := hb (x (-4) 1 && x (-4) 14)
    clear * - r15290 b15291 b15292 d15285
    omega
  have d15293 : (x (-5) 2).toNat = 0 := by
    have r15294 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15295 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
    have e15296 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
    have b15297 := hb (x (-6) 3)
    have b15298 := hb (x (-5) 2)
    have b15299 := hb (x (-4) 13)
    have b15300 := hb (x (-3) 12)
    clear * - r15294 e15295 e15296 b15297 b15298 b15299 b15300 d15257 d15261
    omega
  have d15301 : (x (-3) 13).toNat = 1 := by
    have r15302 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15303 := hb (x (-5) 2)
    have b15304 := hb (x (-3) 13)
    have b15305 := hb (x (-4) 1 && x (-4) 14)
    clear * - r15302 b15303 b15304 b15305 d15289 d15293
    omega
  have d15306 : (x (-3) 1).toNat = 1 := by
    have r15307 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
    have b15308 := hb (x (-3) 1)
    have b15309 := hb (x (-3) 13)
    clear * - r15307 b15308 b15309 d15301
    omega
  have d15310 : (x (-2) 14).toNat = 0 := by
    have r15311 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15312 := hb (x (-3) 1)
    have b15313 := hb (x (-2) 14)
    clear * - r15311 b15312 b15313 d15306
    omega
  have d15314 : (x (-2) 4 && x (-2) 14).toNat = 0 := by
    have r15315 := hand2 (x (-2) 4) (x (-2) 14)
    have b15316 := hb (x (-2) 14)
    have b15317 := hb (x (-2) 4 && x (-2) 14)
    clear * - r15315 b15316 b15317 d15310
    omega
  have d15318 : (x (-3) 5).toNat = 1 := by
    have r15319 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15320 := hb (x (-3) 5)
    have b15321 := hb (x 2 10)
    have b15322 := hb (x 1 1 && x 1 11)
    have b15323 := hb (x 0 2 && x 0 12)
    have b15324 := hb (x (-1) 3 && x (-1) 13)
    have b15325 := hb (x (-2) 4 && x (-2) 14)
    clear * - r15319 b15320 b15321 b15322 b15323 b15324 b15325 d15230 d15246 g21 g22 d15314
    omega
  have d15326 : (x (-2) 12).toNat = 0 := by
    have r15327 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15328 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
    have e15329 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
    have b15330 := hb (x (-5) 3)
    have b15331 := hb (x (-4) 2)
    have b15332 := hb (x (-3) 13)
    have b15333 := hb (x (-2) 12)
    clear * - r15327 e15328 e15329 b15330 b15331 b15332 b15333 d15301
    omega
  have d15334 : (x (-2) 4).toNat = 0 := by
    have r15335 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
    have b15336 := hb (x (-2) 4)
    have b15337 := hb (x (-2) 12)
    clear * - r15335 b15336 b15337 d15326
    omega
  have d15338 : (x 5 12).toNat = 0 := by
    have r15339 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15340 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e15341 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b15342 := hb (x 2 3)
    have b15343 := hb (x 3 2)
    have b15344 := hb (x 4 13)
    have b15345 := hb (x 5 12)
    clear * - r15339 e15340 e15341 b15342 b15343 b15344 b15345 d15097
    omega
  have d15346 : (x 5 2 && x 5 12).toNat = 0 := by
    have r15347 := hand2 (x 5 2) (x 5 12)
    have b15348 := hb (x 5 12)
    have b15349 := hb (x 5 2 && x 5 12)
    clear * - r15347 b15348 b15349 d15338
    omega
  have d15350 : (x 5 4).toNat = 0 := by
    have r15351 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
    have b15352 := hb (x 5 4)
    have b15353 := hb (x 5 12)
    clear * - r15351 b15352 b15353 d15338
    omega
  have d15354 : (x 4 13).toNat = 0 := by
    have r15355 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15356 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e15357 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b15358 := hb (x 2 3)
    have b15359 := hb (x 3 2)
    have b15360 := hb (x 4 13)
    have b15361 := hb (x 5 12)
    clear * - r15355 e15356 e15357 b15358 b15359 b15360 b15361 d15338 d15097
    omega
  have d15362 : (x 4 3 && x 4 13).toNat = 0 := by
    have r15363 := hand2 (x 4 3) (x 4 13)
    have b15364 := hb (x 4 13)
    have b15365 := hb (x 4 3 && x 4 13)
    clear * - r15363 b15364 b15365 d15354
    omega
  have d15366 : (x 4 5).toNat = 0 := by
    have r15367 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
    have b15368 := hb (x 4 5)
    have b15369 := hb (x 4 13)
    clear * - r15367 b15368 b15369 d15354
    omega
  have d15370 : (x 2 5).toNat = 0 := by
    have r15371 : (x 2 5).toNat ≤ (x 2 13).toNat := himp _ _ (hp5 2)
    have b15372 := hb (x 2 5)
    have b15373 := hb (x 2 13)
    clear * - r15371 b15372 b15373 d15077
    omega
  have d15374 : (x 3 4).toNat = 0 := by
    have r15375 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15376 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e15377 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e15378 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e15379 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e15380 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e15381 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b15382 := hb (x 0 7)
    have b15383 := hb (x 1 6)
    have b15384 := hb (x 2 5)
    have b15385 := hb (x 3 4)
    have b15386 := hb (x 4 11)
    have b15387 := hb (x 5 10)
    have b15388 := hb (x 6 9)
    have b15389 := hb (x 7 8)
    clear * - r15375 e15376 e15377 e15378 e15379 e15380 e15381 b15382 b15383 b15384 b15385 b15386 b15387 b15388 b15389 d14980 d15000 d15020 d15040 d15370 g9 g5
    omega
  have d15390 : (x 3 4 && x 3 14).toNat = 0 := by
    have r15391 := hand1 (x 3 4) (x 3 14)
    have b15392 := hb (x 3 4)
    have b15393 := hb (x 3 4 && x 3 14)
    clear * - r15391 b15392 b15393 d15374
    omega
  have d15394 : (x 7 11).toNat = 1 := by
    have r15395 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15396 := hb (x 3 4)
    have b15397 := hb (x 7 11)
    have b15398 := hb (x 6 1 && x 6 12)
    have b15399 := hb (x 5 2 && x 5 13)
    have b15400 := hb (x 4 3 && x 4 14)
    clear * - r15395 b15396 b15397 b15398 b15399 b15400 d15174 d15198 d15126 d15374
    omega
  have d15401 : (x 7 3).toNat = 1 := by
    have r15402 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
    have b15403 := hb (x 7 3)
    have b15404 := hb (x 7 11)
    clear * - r15402 b15403 b15404 d15394
    omega
  have d15405 : (x 10 12).toNat = 0 := by
    have r15406 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15407 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e15408 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b15409 := hb (x 7 3)
    have b15410 := hb (x 8 2)
    have b15411 := hb (x 9 13)
    have b15412 := hb (x 10 12)
    clear * - r15406 e15407 e15408 b15409 b15410 b15411 b15412 d15401
    omega
  have d15413 : (x 10 3 && x 10 12).toNat = 0 := by
    have r15414 := hand2 (x 10 3) (x 10 12)
    have b15415 := hb (x 10 12)
    have b15416 := hb (x 10 3 && x 10 12)
    clear * - r15414 b15415 b15416 d15405
    omega
  have d15417 : (x 10 5 && x 10 12).toNat = 0 := by
    have r15418 := hand2 (x 10 5) (x 10 12)
    have b15419 := hb (x 10 12)
    have b15420 := hb (x 10 5 && x 10 12)
    clear * - r15418 b15419 b15420 d15405
    omega
  have d15421 : (x 10 4).toNat = 0 := by
    have r15422 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
    have b15423 := hb (x 10 4)
    have b15424 := hb (x 10 12)
    clear * - r15422 b15423 b15424 d15405
    omega
  have d15425 : (x 10 4 && x 10 14).toNat = 0 := by
    have r15426 := hand1 (x 10 4) (x 10 14)
    have b15427 := hb (x 10 4)
    have b15428 := hb (x 10 4 && x 10 14)
    clear * - r15426 b15427 b15428 d15421
    omega
  have d15429 : (x 9 13).toNat = 0 := by
    have r15430 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15431 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e15432 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b15433 := hb (x 7 3)
    have b15434 := hb (x 8 2)
    have b15435 := hb (x 9 13)
    have b15436 := hb (x 10 12)
    clear * - r15430 e15431 e15432 b15433 b15434 b15435 b15436 d15405 d15401
    omega
  have d15437 : (x 9 4 && x 9 13).toNat = 0 := by
    have r15438 := hand2 (x 9 4) (x 9 13)
    have b15439 := hb (x 9 13)
    have b15440 := hb (x 9 4 && x 9 13)
    clear * - r15438 b15439 b15440 d15429
    omega
  have d15441 : (x 9 6 && x 9 13).toNat = 0 := by
    have r15442 := hand2 (x 9 6) (x 9 13)
    have b15443 := hb (x 9 13)
    have b15444 := hb (x 9 6 && x 9 13)
    clear * - r15442 b15443 b15444 d15429
    omega
  have d15445 : (x 9 5).toNat = 0 := by
    have r15446 : (x 9 5).toNat ≤ (x 9 13).toNat := himp _ _ (hp5 9)
    have b15447 := hb (x 9 5)
    have b15448 := hb (x 9 13)
    clear * - r15446 b15447 b15448 d15429
    omega
  have d15449 : (x 8 2).toNat = 0 := by
    have r15450 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15451 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e15452 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b15453 := hb (x 7 3)
    have b15454 := hb (x 8 2)
    have b15455 := hb (x 9 13)
    have b15456 := hb (x 10 12)
    clear * - r15450 e15451 e15452 b15453 b15454 b15455 b15456 d15405 d15429 d15401
    omega
  have d15457 : (x 8 2 && x 8 8).toNat = 0 := by
    have r15458 := hand1 (x 8 2) (x 8 8)
    have b15459 := hb (x 8 2)
    have b15460 := hb (x 8 2 && x 8 8)
    clear * - r15458 b15459 b15460 d15449
    omega
  have d15461 : (x 8 2 && x 8 6).toNat = 0 := by
    have r15462 := hand1 (x 8 2) (x 8 6)
    have b15463 := hb (x 8 2)
    have b15464 := hb (x 8 2 && x 8 6)
    clear * - r15462 b15463 b15464 d15449
    omega
  have d15465 : (x 8 10).toNat = 0 := by
    have r15466 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
    have b15467 := hb (x 8 2)
    have b15468 := hb (x 8 10)
    clear * - r15466 b15467 b15468 d15449
    omega
  have d15469 : (x 10 8).toNat = 0 := by
    have r15470 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15471 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
    have e15472 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
    have e15473 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
    have e15474 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
    have e15475 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
    have e15476 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
    have b15477 := hb (x 3 7)
    have b15478 := hb (x 4 6)
    have b15479 := hb (x 5 5)
    have b15480 := hb (x 6 4)
    have b15481 := hb (x 7 11)
    have b15482 := hb (x 8 10)
    have b15483 := hb (x 9 9)
    have b15484 := hb (x 10 8)
    clear * - r15470 e15471 e15472 e15473 e15474 e15475 e15476 b15477 b15478 b15479 b15480 b15481 b15482 b15483 b15484 d15465 d15394 d15178 d15202 d15130
    omega
  have d15485 : (x 9 9).toNat = 0 := by
    have r15486 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15487 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
    have e15488 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
    have e15489 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
    have e15490 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
    have e15491 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
    have e15492 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
    have b15493 := hb (x 3 7)
    have b15494 := hb (x 4 6)
    have b15495 := hb (x 5 5)
    have b15496 := hb (x 6 4)
    have b15497 := hb (x 7 11)
    have b15498 := hb (x 8 10)
    have b15499 := hb (x 9 9)
    have b15500 := hb (x 10 8)
    clear * - r15486 e15487 e15488 e15489 e15490 e15491 e15492 b15493 b15494 b15495 b15496 b15497 b15498 b15499 b15500 d15469 d15465 d15394 d15178 d15202 d15130
    omega
  have d15501 : (x 3 7).toNat = 0 := by
    have r15502 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15503 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
    have e15504 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
    have e15505 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
    have e15506 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
    have e15507 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
    have e15508 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
    have b15509 := hb (x 3 7)
    have b15510 := hb (x 4 6)
    have b15511 := hb (x 5 5)
    have b15512 := hb (x 6 4)
    have b15513 := hb (x 7 11)
    have b15514 := hb (x 8 10)
    have b15515 := hb (x 9 9)
    have b15516 := hb (x 10 8)
    clear * - r15502 e15503 e15504 e15505 e15506 e15507 e15508 b15509 b15510 b15511 b15512 b15513 b15514 b15515 b15516 d15469 d15485 d15465 d15394 d15178 d15202 d15130
    omega
  have d15517 : (x 3 7 && x 3 13).toNat = 0 := by
    have r15518 := hand1 (x 3 7) (x 3 13)
    have b15519 := hb (x 3 7)
    have b15520 := hb (x 3 7 && x 3 13)
    clear * - r15518 b15519 b15520 d15501
    omega
  have d15521 : (x 3 7 && x 3 11).toNat = 0 := by
    have r15522 := hand1 (x 3 7) (x 3 11)
    have b15523 := hb (x 3 7)
    have b15524 := hb (x 3 7 && x 3 11)
    clear * - r15522 b15523 b15524 d15501
    omega
  have d15525 : (x 6 8).toNat = 0 := by
    have r15526 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15527 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e15528 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e15529 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e15530 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e15531 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e15532 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b15533 := hb (x (-1) 7)
    have b15534 := hb (x 0 6)
    have b15535 := hb (x 1 5)
    have b15536 := hb (x 2 4)
    have b15537 := hb (x 3 11)
    have b15538 := hb (x 4 10)
    have b15539 := hb (x 5 9)
    have b15540 := hb (x 6 8)
    clear * - r15526 e15527 e15528 e15529 e15530 e15531 e15532 b15533 b15534 b15535 b15536 b15537 b15538 b15539 b15540 d15146 d15158 g12 g8 g4
    omega
  have d15541 : (x 5 9).toNat = 0 := by
    have r15542 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15543 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e15544 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e15545 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e15546 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e15547 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e15548 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b15549 := hb (x (-1) 7)
    have b15550 := hb (x 0 6)
    have b15551 := hb (x 1 5)
    have b15552 := hb (x 2 4)
    have b15553 := hb (x 3 11)
    have b15554 := hb (x 4 10)
    have b15555 := hb (x 5 9)
    have b15556 := hb (x 6 8)
    clear * - r15542 e15543 e15544 e15545 e15546 e15547 e15548 b15549 b15550 b15551 b15552 b15553 b15554 b15555 b15556 d15525 d15146 d15158 g12 g8 g4
    omega
  have d15557 : (x 2 8).toNat = 0 := by
    have r15558 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15559 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
    have e15560 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
    have e15561 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
    have e15562 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
    have e15563 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
    have e15564 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
    have b15565 := hb (x (-5) 7)
    have b15566 := hb (x (-4) 6)
    have b15567 := hb (x (-3) 5)
    have b15568 := hb (x (-2) 4)
    have b15569 := hb (x (-1) 11)
    have b15570 := hb (x 0 10)
    have b15571 := hb (x 1 9)
    have b15572 := hb (x 2 8)
    clear * - r15558 e15559 e15560 e15561 e15562 e15563 e15564 b15565 b15566 b15567 b15568 b15569 b15570 b15571 b15572 g1 d15334 d15318
    omega
  have d15573 : (x 2 8 && x 2 14).toNat = 0 := by
    have r15574 := hand1 (x 2 8) (x 2 14)
    have b15575 := hb (x 2 8)
    have b15576 := hb (x 2 8 && x 2 14)
    clear * - r15574 b15575 b15576 d15557
    omega
  have d15577 : (x 1 9).toNat = 0 := by
    have r15578 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15579 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
    have e15580 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
    have e15581 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
    have e15582 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
    have e15583 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
    have e15584 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
    have b15585 := hb (x (-5) 7)
    have b15586 := hb (x (-4) 6)
    have b15587 := hb (x (-3) 5)
    have b15588 := hb (x (-2) 4)
    have b15589 := hb (x (-1) 11)
    have b15590 := hb (x 0 10)
    have b15591 := hb (x 1 9)
    have b15592 := hb (x 2 8)
    clear * - r15578 e15579 e15580 e15581 e15582 e15583 e15584 b15585 b15586 b15587 b15588 b15589 b15590 b15591 b15592 d15557 g1 d15334 d15318
    omega
  have d15593 : (x 0 10).toNat = 0 := by
    have r15594 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15595 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
    have e15596 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
    have e15597 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
    have e15598 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
    have e15599 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
    have e15600 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
    have b15601 := hb (x (-5) 7)
    have b15602 := hb (x (-4) 6)
    have b15603 := hb (x (-3) 5)
    have b15604 := hb (x (-2) 4)
    have b15605 := hb (x (-1) 11)
    have b15606 := hb (x 0 10)
    have b15607 := hb (x 1 9)
    have b15608 := hb (x 2 8)
    clear * - r15594 e15595 e15596 e15597 e15598 e15599 e15600 b15601 b15602 b15603 b15604 b15605 b15606 b15607 b15608 d15557 d15577 g1 d15334 d15318
    omega
  have d15609 : (x 7 3 && x 7 7).toNat = 1 := by
    have r15610 : 1 ≤ (x 10 4).toNat + (x 9 1 && x 9 5).toNat + (x 8 2 && x 8 6).toNat + (x 7 3 && x 7 7).toNat + (x 6 4 && x 6 8).toNat + (x 5 5 && x 5 9).toNat + (x 4 6 && x 4 10).toNat + (x 3 7 && x 3 11).toNat + (x 2 8 && x 2 12).toNat + (x 1 9 && x 1 13).toNat + (x 0 10 && x 0 14).toNat + (x (-1) 11).toNat := by have q := hcov4 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15611 : (x 9 1 && x 9 5).toNat = (x 9 5).toNat := handr _ _ (fun h => hp13 9 (hp5 9 (h)))
    have e15612 : (x 0 10 && x 0 14).toNat = (x 0 10).toNat := handl _ _ (fun h => hp2 0 (hp10 0 (h)))
    have b15613 := hb (x (-1) 11)
    have b15614 := hb (x 0 10)
    have b15615 := hb (x 9 5)
    have b15616 := hb (x 10 4)
    have b15617 := hb (x 8 2 && x 8 6)
    have b15618 := hb (x 7 3 && x 7 7)
    have b15619 := hb (x 6 4 && x 6 8)
    have b15620 := hb (x 5 5 && x 5 9)
    have b15621 := hb (x 4 6 && x 4 10)
    have b15622 := hb (x 3 7 && x 3 11)
    have b15623 := hb (x 2 8 && x 2 12)
    have b15624 := hb (x 1 9 && x 1 13)
    clear * - r15610 e15611 e15612 b15613 b15614 b15615 b15616 b15617 b15618 b15619 b15620 b15621 b15622 b15623 b15624 d15421 d15445 d15461 d15186 d15210 d15138 d15521 g14 g15 d15593 g1
    omega
  have d15625 : (x 7 7).toNat = 1 := by
    have r15626 := hand2 (x 7 3) (x 7 7)
    have b15627 := hb (x 7 7)
    have b15628 := hb (x 7 3 && x 7 7)
    clear * - r15626 b15627 b15628 d15609
    omega
  have d15629 : (x 14 8).toNat = 0 := by
    have r15630 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15631 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e15632 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e15633 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e15634 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e15635 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e15636 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have b15637 := hb (x 7 7)
    have b15638 := hb (x 8 6)
    have b15639 := hb (x 9 5)
    have b15640 := hb (x 10 4)
    have b15641 := hb (x 11 11)
    have b15642 := hb (x 12 10)
    have b15643 := hb (x 13 9)
    have b15644 := hb (x 14 8)
    clear * - r15630 e15631 e15632 e15633 e15634 e15635 e15636 b15637 b15638 b15639 b15640 b15641 b15642 b15643 b15644 d15421 d15445 d15625
    omega
  have d15645 : (x 14 1 && x 14 8).toNat = 0 := by
    have r15646 := hand2 (x 14 1) (x 14 8)
    have b15647 := hb (x 14 8)
    have b15648 := hb (x 14 1 && x 14 8)
    clear * - r15646 b15647 b15648 d15629
    omega
  have d15649 : (x 13 9).toNat = 0 := by
    have r15650 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15651 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e15652 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e15653 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e15654 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e15655 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e15656 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have b15657 := hb (x 7 7)
    have b15658 := hb (x 8 6)
    have b15659 := hb (x 9 5)
    have b15660 := hb (x 10 4)
    have b15661 := hb (x 11 11)
    have b15662 := hb (x 12 10)
    have b15663 := hb (x 13 9)
    have b15664 := hb (x 14 8)
    clear * - r15650 e15651 e15652 e15653 e15654 e15655 e15656 b15657 b15658 b15659 b15660 b15661 b15662 b15663 b15664 d15629 d15421 d15445 d15625
    omega
  have d15665 : (x 13 2 && x 13 9).toNat = 0 := by
    have r15666 := hand2 (x 13 2) (x 13 9)
    have b15667 := hb (x 13 9)
    have b15668 := hb (x 13 2 && x 13 9)
    clear * - r15666 b15667 b15668 d15649
    omega
  have d15669 : (x 12 10).toNat = 0 := by
    have r15670 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15671 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e15672 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e15673 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e15674 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e15675 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e15676 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have b15677 := hb (x 7 7)
    have b15678 := hb (x 8 6)
    have b15679 := hb (x 9 5)
    have b15680 := hb (x 10 4)
    have b15681 := hb (x 11 11)
    have b15682 := hb (x 12 10)
    have b15683 := hb (x 13 9)
    have b15684 := hb (x 14 8)
    clear * - r15670 e15671 e15672 e15673 e15674 e15675 e15676 b15677 b15678 b15679 b15680 b15681 b15682 b15683 b15684 d15629 d15649 d15421 d15445 d15625
    omega
  have d15685 : (x 12 1 && x 12 10).toNat = 0 := by
    have r15686 := hand2 (x 12 1) (x 12 10)
    have b15687 := hb (x 12 10)
    have b15688 := hb (x 12 1 && x 12 10)
    clear * - r15686 b15687 b15688 d15669
    omega
  have d15689 : (x 12 3 && x 12 10).toNat = 0 := by
    have r15690 := hand2 (x 12 3) (x 12 10)
    have b15691 := hb (x 12 10)
    have b15692 := hb (x 12 3 && x 12 10)
    clear * - r15690 b15691 b15692 d15669
    omega
  have d15693 : (x 11 11).toNat = 0 := by
    have r15694 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15695 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e15696 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e15697 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e15698 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e15699 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e15700 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have b15701 := hb (x 7 7)
    have b15702 := hb (x 8 6)
    have b15703 := hb (x 9 5)
    have b15704 := hb (x 10 4)
    have b15705 := hb (x 11 11)
    have b15706 := hb (x 12 10)
    have b15707 := hb (x 13 9)
    have b15708 := hb (x 14 8)
    clear * - r15694 e15695 e15696 e15697 e15698 e15699 e15700 b15701 b15702 b15703 b15704 b15705 b15706 b15707 b15708 d15629 d15649 d15669 d15421 d15445 d15625
    omega
  have d15709 : (x 11 2 && x 11 11).toNat = 0 := by
    have r15710 := hand2 (x 11 2) (x 11 11)
    have b15711 := hb (x 11 11)
    have b15712 := hb (x 11 2 && x 11 11)
    clear * - r15710 b15711 b15712 d15693
    omega
  have d15713 : (x 11 4 && x 11 11).toNat = 0 := by
    have r15714 := hand2 (x 11 4) (x 11 11)
    have b15715 := hb (x 11 11)
    have b15716 := hb (x 11 4 && x 11 11)
    clear * - r15714 b15715 b15716 d15693
    omega
  have d15717 : (x 8 6).toNat = 0 := by
    have r15718 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15719 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e15720 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e15721 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e15722 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e15723 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e15724 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have b15725 := hb (x 7 7)
    have b15726 := hb (x 8 6)
    have b15727 := hb (x 9 5)
    have b15728 := hb (x 10 4)
    have b15729 := hb (x 11 11)
    have b15730 := hb (x 12 10)
    have b15731 := hb (x 13 9)
    have b15732 := hb (x 14 8)
    clear * - r15718 e15719 e15720 e15721 e15722 e15723 e15724 b15725 b15726 b15727 b15728 b15729 b15730 b15731 b15732 d15629 d15649 d15669 d15693 d15421 d15445 d15625
    omega
  have d15733 : (x 13 1).toNat = 0 := by
    have r15734 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15735 := hb (x 0 14)
    have b15736 := hb (x 1 13)
    have b15737 := hb (x 2 12)
    have b15738 := hb (x 3 11)
    have b15739 := hb (x 4 10)
    have b15740 := hb (x 5 9)
    have b15741 := hb (x 6 8)
    have b15742 := hb (x 7 7)
    have b15743 := hb (x 8 6)
    have b15744 := hb (x 9 5)
    have b15745 := hb (x 10 4)
    have b15746 := hb (x 11 3)
    have b15747 := hb (x 12 2)
    have b15748 := hb (x 13 1)
    clear * - r15734 b15735 b15736 b15737 b15738 b15739 b15740 b15741 b15742 b15743 b15744 b15745 b15746 b15747 b15748 d15421 d15445 d15717 d15625 d15525 d15541 d15146 d15158 g13 g11 g6
    omega
  have d15749 : (x 13 1 && x 13 14).toNat = 0 := by
    have r15750 := hand1 (x 13 1) (x 13 14)
    have b15751 := hb (x 13 1)
    have b15752 := hb (x 13 1 && x 13 14)
    clear * - r15750 b15751 b15752 d15733
    omega
  have d15753 : (x 13 1 && x 13 12).toNat = 0 := by
    have r15754 := hand1 (x 13 1) (x 13 12)
    have b15755 := hb (x 13 1)
    have b15756 := hb (x 13 1 && x 13 12)
    clear * - r15754 b15755 b15756 d15733
    omega
  have d15757 : (x 13 1 && x 13 11).toNat = 0 := by
    have r15758 := hand1 (x 13 1) (x 13 11)
    have b15759 := hb (x 13 1)
    have b15760 := hb (x 13 1 && x 13 11)
    clear * - r15758 b15759 b15760 d15733
    omega
  have d15761 : (x 12 2).toNat = 0 := by
    have r15762 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15763 := hb (x 0 14)
    have b15764 := hb (x 1 13)
    have b15765 := hb (x 2 12)
    have b15766 := hb (x 3 11)
    have b15767 := hb (x 4 10)
    have b15768 := hb (x 5 9)
    have b15769 := hb (x 6 8)
    have b15770 := hb (x 7 7)
    have b15771 := hb (x 8 6)
    have b15772 := hb (x 9 5)
    have b15773 := hb (x 10 4)
    have b15774 := hb (x 11 3)
    have b15775 := hb (x 12 2)
    have b15776 := hb (x 13 1)
    clear * - r15762 b15763 b15764 b15765 b15766 b15767 b15768 b15769 b15770 b15771 b15772 b15773 b15774 b15775 b15776 d15733 d15421 d15445 d15717 d15625 d15525 d15541 d15146 d15158 g13 g11 g6
    omega
  have d15777 : (x 12 2 && x 12 13).toNat = 0 := by
    have r15778 := hand1 (x 12 2) (x 12 13)
    have b15779 := hb (x 12 2)
    have b15780 := hb (x 12 2 && x 12 13)
    clear * - r15778 b15779 b15780 d15761
    omega
  have d15781 : (x 12 2 && x 12 12).toNat = 0 := by
    have r15782 := hand1 (x 12 2) (x 12 12)
    have b15783 := hb (x 12 2)
    have b15784 := hb (x 12 2 && x 12 12)
    clear * - r15782 b15783 b15784 d15761
    omega
  have d15785 : (x 14 13).toNat = 1 := by
    have r15786 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15787 := hb (x 12 2)
    have b15788 := hb (x 14 13)
    have b15789 := hb (x 13 1 && x 13 14)
    clear * - r15786 b15787 b15788 b15789 d15749 d15761
    omega
  have d15790 : (x 14 1).toNat = 1 := by
    have r15791 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
    have b15792 := hb (x 14 1)
    have b15793 := hb (x 14 13)
    clear * - r15791 b15792 b15793 d15785
    omega
  have d15794 : (x 15 14).toNat = 0 := by
    have r15795 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15796 := hb (x 14 1)
    have b15797 := hb (x 15 14)
    clear * - r15795 b15796 b15797 d15790
    omega
  have d15798 : (x 15 1 && x 15 14).toNat = 0 := by
    have r15799 := hand2 (x 15 1) (x 15 14)
    have b15800 := hb (x 15 14)
    have b15801 := hb (x 15 1 && x 15 14)
    clear * - r15799 b15800 b15801 d15794
    omega
  have d15802 : (x 15 2).toNat = 0 := by
    have r15803 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
    have b15804 := hb (x 15 2)
    have b15805 := hb (x 15 14)
    clear * - r15803 b15804 b15805 d15794
    omega
  have d15806 : (x 15 2 && x 15 8).toNat = 0 := by
    have r15807 := hand1 (x 15 2) (x 15 8)
    have b15808 := hb (x 15 2)
    have b15809 := hb (x 15 2 && x 15 8)
    clear * - r15807 b15808 b15809 d15802
    omega
  have d15810 : (x 15 10).toNat = 0 := by
    have r15811 : (x 15 10).toNat ≤ (x 15 2).toNat := himp _ _ (hp10 15)
    have b15812 := hb (x 15 2)
    have b15813 := hb (x 15 10)
    clear * - r15811 b15812 b15813 d15802
    omega
  have d15814 : (x 15 12).toNat = 0 := by
    have r15815 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15816 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e15817 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b15818 := hb (x 12 3)
    have b15819 := hb (x 13 2)
    have b15820 := hb (x 14 13)
    have b15821 := hb (x 15 12)
    clear * - r15815 e15816 e15817 b15818 b15819 b15820 b15821 d15785
    omega
  have d15822 : (x 15 4).toNat = 0 := by
    have r15823 : (x 15 4).toNat ≤ (x 15 12).toNat := himp _ _ (hp4 15)
    have b15824 := hb (x 15 4)
    have b15825 := hb (x 15 12)
    clear * - r15823 b15824 b15825 d15814
    omega
  have d15826 : (x 15 4 && x 15 8).toNat = 0 := by
    have r15827 := hand1 (x 15 4) (x 15 8)
    have b15828 := hb (x 15 4)
    have b15829 := hb (x 15 4 && x 15 8)
    clear * - r15827 b15828 b15829 d15822
    omega
  have d15830 : (x 13 2).toNat = 0 := by
    have r15831 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15832 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e15833 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b15834 := hb (x 12 3)
    have b15835 := hb (x 13 2)
    have b15836 := hb (x 14 13)
    have b15837 := hb (x 15 12)
    clear * - r15831 e15832 e15833 b15834 b15835 b15836 b15837 d15814 d15785
    omega
  have d15838 : (x 13 2 && x 13 6).toNat = 0 := by
    have r15839 := hand1 (x 13 2) (x 13 6)
    have b15840 := hb (x 13 2)
    have b15841 := hb (x 13 2 && x 13 6)
    clear * - r15839 b15840 b15841 d15830
    omega
  have d15842 : (x 13 10).toNat = 0 := by
    have r15843 : (x 13 10).toNat ≤ (x 13 2).toNat := himp _ _ (hp10 13)
    have b15844 := hb (x 13 2)
    have b15845 := hb (x 13 10)
    clear * - r15843 b15844 b15845 d15830
    omega
  have d15846 : (x 13 4 && x 13 10).toNat = 0 := by
    have r15847 := hand2 (x 13 4) (x 13 10)
    have b15848 := hb (x 13 10)
    have b15849 := hb (x 13 4 && x 13 10)
    clear * - r15847 b15848 b15849 d15842
    omega
  have d15850 : (x 13 6 && x 13 10).toNat = 0 := by
    have r15851 := hand2 (x 13 6) (x 13 10)
    have b15852 := hb (x 13 10)
    have b15853 := hb (x 13 6 && x 13 10)
    clear * - r15851 b15852 b15853 d15842
    omega
  have d15854 : (x 12 3).toNat = 0 := by
    have r15855 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15856 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e15857 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b15858 := hb (x 12 3)
    have b15859 := hb (x 13 2)
    have b15860 := hb (x 14 13)
    have b15861 := hb (x 15 12)
    clear * - r15855 e15856 e15857 b15858 b15859 b15860 b15861 d15814 d15785 d15830
    omega
  have d15862 : (x 12 3 && x 12 7).toNat = 0 := by
    have r15863 := hand1 (x 12 3) (x 12 7)
    have b15864 := hb (x 12 3)
    have b15865 := hb (x 12 3 && x 12 7)
    clear * - r15863 b15864 b15865 d15854
    omega
  have d15866 : (x 12 11).toNat = 0 := by
    have r15867 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
    have b15868 := hb (x 12 3)
    have b15869 := hb (x 12 11)
    clear * - r15867 b15868 b15869 d15854
    omega
  have d15870 : (x 12 5 && x 12 11).toNat = 0 := by
    have r15871 := hand2 (x 12 5) (x 12 11)
    have b15872 := hb (x 12 11)
    have b15873 := hb (x 12 5 && x 12 11)
    clear * - r15871 b15872 b15873 d15866
    omega
  have d15874 : (x 12 7 && x 12 11).toNat = 0 := by
    have r15875 := hand2 (x 12 7) (x 12 11)
    have b15876 := hb (x 12 11)
    have b15877 := hb (x 12 7 && x 12 11)
    clear * - r15875 b15876 b15877 d15866
    omega
  have d15878 : (x 11 3).toNat = 0 := by
    have r15879 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15880 := hb (x 0 14)
    have b15881 := hb (x 1 13)
    have b15882 := hb (x 2 12)
    have b15883 := hb (x 3 11)
    have b15884 := hb (x 4 10)
    have b15885 := hb (x 5 9)
    have b15886 := hb (x 6 8)
    have b15887 := hb (x 7 7)
    have b15888 := hb (x 8 6)
    have b15889 := hb (x 9 5)
    have b15890 := hb (x 10 4)
    have b15891 := hb (x 11 3)
    have b15892 := hb (x 12 2)
    have b15893 := hb (x 13 1)
    clear * - r15879 b15880 b15881 b15882 b15883 b15884 b15885 b15886 b15887 b15888 b15889 b15890 b15891 b15892 b15893 d15733 d15761 d15421 d15445 d15717 d15625 d15525 d15541 d15146 d15158 g13 g11 g6
    omega
  have d15894 : (x 11 3 && x 11 14).toNat = 0 := by
    have r15895 := hand1 (x 11 3) (x 11 14)
    have b15896 := hb (x 11 3)
    have b15897 := hb (x 11 3 && x 11 14)
    clear * - r15895 b15896 b15897 d15878
    omega
  have d15898 : (x 14 11).toNat = 1 := by
    have r15899 : 1 ≤ (x 14 11).toNat + (x 13 1 && x 13 12).toNat + (x 12 2 && x 12 13).toNat + (x 11 3 && x 11 14).toNat + (x 10 4).toNat := by have q := hcov11 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15900 := hb (x 10 4)
    have b15901 := hb (x 14 11)
    have b15902 := hb (x 13 1 && x 13 12)
    have b15903 := hb (x 12 2 && x 12 13)
    have b15904 := hb (x 11 3 && x 11 14)
    clear * - r15899 b15900 b15901 b15902 b15903 b15904 d15753 d15777 d15894 d15421
    omega
  have d15905 : (x 14 3).toNat = 1 := by
    have r15906 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
    have b15907 := hb (x 14 3)
    have b15908 := hb (x 14 11)
    clear * - r15906 b15907 b15908 d15898
    omega
  have d15909 : (x 17 12).toNat = 0 := by
    have r15910 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15911 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
    have e15912 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
    have b15913 := hb (x 14 3)
    have b15914 := hb (x 15 2)
    have b15915 := hb (x 16 13)
    have b15916 := hb (x 17 12)
    clear * - r15910 e15911 e15912 b15913 b15914 b15915 b15916 d15802 d15905
    omega
  have d15917 : (x 16 13).toNat = 0 := by
    have r15918 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15919 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
    have e15920 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
    have b15921 := hb (x 14 3)
    have b15922 := hb (x 15 2)
    have b15923 := hb (x 16 13)
    have b15924 := hb (x 17 12)
    clear * - r15918 e15919 e15920 b15921 b15922 b15923 b15924 d15909 d15802 d15905
    omega
  have d15925 : (x 14 2).toNat = 1 := by
    have r15926 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15927 := hb (x 14 2)
    have b15928 := hb (x 16 13)
    have b15929 := hb (x 15 1 && x 15 14)
    clear * - r15926 b15927 b15928 b15929 d15917 d15798
    omega
  have d15930 : (x 16 12).toNat = 0 := by
    have r15931 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15932 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e15933 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b15934 := hb (x 13 3)
    have b15935 := hb (x 14 2)
    have b15936 := hb (x 15 13)
    have b15937 := hb (x 16 12)
    clear * - r15931 e15932 e15933 b15934 b15935 b15936 b15937 d15925
    omega
  have d15938 : (x 15 13).toNat = 0 := by
    have r15939 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15940 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e15941 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b15942 := hb (x 13 3)
    have b15943 := hb (x 14 2)
    have b15944 := hb (x 15 13)
    have b15945 := hb (x 16 12)
    clear * - r15939 e15940 e15941 b15942 b15943 b15944 b15945 d15930 d15925
    omega
  have d15946 : (x 13 3).toNat = 0 := by
    have r15947 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15948 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e15949 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b15950 := hb (x 13 3)
    have b15951 := hb (x 14 2)
    have b15952 := hb (x 15 13)
    have b15953 := hb (x 16 12)
    clear * - r15947 e15948 e15949 b15950 b15951 b15952 b15953 d15930 d15938 d15925
    omega
  have d15954 : (x 13 11).toNat = 0 := by
    have r15955 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
    have b15956 := hb (x 13 3)
    have b15957 := hb (x 13 11)
    clear * - r15955 b15956 b15957 d15946
    omega
  have d15958 : (x 17 8).toNat = 0 := by
    have r15959 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15960 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
    have e15961 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
    have e15962 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
    have e15963 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
    have e15964 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
    have e15965 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
    have b15966 := hb (x 10 7)
    have b15967 := hb (x 11 6)
    have b15968 := hb (x 12 5)
    have b15969 := hb (x 13 4)
    have b15970 := hb (x 14 11)
    have b15971 := hb (x 15 10)
    have b15972 := hb (x 16 9)
    have b15973 := hb (x 17 8)
    clear * - r15959 e15960 e15961 e15962 e15963 e15964 e15965 b15966 b15967 b15968 b15969 b15970 b15971 b15972 b15973 d15810 d15898
    omega
  have d15974 : (x 16 9).toNat = 0 := by
    have r15975 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15976 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
    have e15977 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
    have e15978 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
    have e15979 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
    have e15980 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
    have e15981 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
    have b15982 := hb (x 10 7)
    have b15983 := hb (x 11 6)
    have b15984 := hb (x 12 5)
    have b15985 := hb (x 13 4)
    have b15986 := hb (x 14 11)
    have b15987 := hb (x 15 10)
    have b15988 := hb (x 16 9)
    have b15989 := hb (x 17 8)
    clear * - r15975 e15976 e15977 e15978 e15979 e15980 e15981 b15982 b15983 b15984 b15985 b15986 b15987 b15988 b15989 d15958 d15810 d15898
    omega
  have d15990 : (x 13 4).toNat = 0 := by
    have r15991 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15992 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
    have e15993 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
    have e15994 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
    have e15995 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
    have e15996 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
    have e15997 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
    have b15998 := hb (x 10 7)
    have b15999 := hb (x 11 6)
    have b16000 := hb (x 12 5)
    have b16001 := hb (x 13 4)
    have b16002 := hb (x 14 11)
    have b16003 := hb (x 15 10)
    have b16004 := hb (x 16 9)
    have b16005 := hb (x 17 8)
    clear * - r15991 e15992 e15993 e15994 e15995 e15996 e15997 b15998 b15999 b16000 b16001 b16002 b16003 b16004 b16005 d15958 d15974 d15810 d15898
    omega
  have d16006 : (x 12 5).toNat = 0 := by
    have r16007 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16008 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
    have e16009 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
    have e16010 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
    have e16011 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
    have e16012 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
    have e16013 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
    have b16014 := hb (x 10 7)
    have b16015 := hb (x 11 6)
    have b16016 := hb (x 12 5)
    have b16017 := hb (x 13 4)
    have b16018 := hb (x 14 11)
    have b16019 := hb (x 15 10)
    have b16020 := hb (x 16 9)
    have b16021 := hb (x 17 8)
    clear * - r16007 e16008 e16009 e16010 e16011 e16012 e16013 b16014 b16015 b16016 b16017 b16018 b16019 b16020 b16021 d15958 d15974 d15810 d15898 d15990
    omega
  have d16022 : (x 11 6).toNat = 0 := by
    have r16023 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16024 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
    have e16025 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
    have e16026 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
    have e16027 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
    have e16028 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
    have e16029 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
    have b16030 := hb (x 10 7)
    have b16031 := hb (x 11 6)
    have b16032 := hb (x 12 5)
    have b16033 := hb (x 13 4)
    have b16034 := hb (x 14 11)
    have b16035 := hb (x 15 10)
    have b16036 := hb (x 16 9)
    have b16037 := hb (x 17 8)
    clear * - r16023 e16024 e16025 e16026 e16027 e16028 e16029 b16030 b16031 b16032 b16033 b16034 b16035 b16036 b16037 d15958 d15974 d15810 d15898 d15990 d16006
    omega
  have d16038 : (x 11 6 && x 11 12).toNat = 0 := by
    have r16039 := hand1 (x 11 6) (x 11 12)
    have b16040 := hb (x 11 6)
    have b16041 := hb (x 11 6 && x 11 12)
    clear * - r16039 b16040 b16041 d16022
    omega
  have d16042 : (x 10 7).toNat = 0 := by
    have r16043 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16044 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
    have e16045 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
    have e16046 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
    have e16047 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
    have e16048 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
    have e16049 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
    have b16050 := hb (x 10 7)
    have b16051 := hb (x 11 6)
    have b16052 := hb (x 12 5)
    have b16053 := hb (x 13 4)
    have b16054 := hb (x 14 11)
    have b16055 := hb (x 15 10)
    have b16056 := hb (x 16 9)
    have b16057 := hb (x 17 8)
    clear * - r16043 e16044 e16045 e16046 e16047 e16048 e16049 b16050 b16051 b16052 b16053 b16054 b16055 b16056 b16057 d15958 d15974 d15810 d15898 d15990 d16006 d16022
    omega
  have d16058 : (x 10 7 && x 10 13).toNat = 0 := by
    have r16059 := hand1 (x 10 7) (x 10 13)
    have b16060 := hb (x 10 7)
    have b16061 := hb (x 10 7 && x 10 13)
    clear * - r16059 b16060 b16061 d16042
    omega
  have d16062 : (x 11 3 && x 11 13).toNat = 0 := by
    have r16063 := hand1 (x 11 3) (x 11 13)
    have b16064 := hb (x 11 3)
    have b16065 := hb (x 11 3 && x 11 13)
    clear * - r16063 b16064 b16065 d15878
    omega
  have d16066 : (x 14 10).toNat = 1 := by
    have r16067 : 1 ≤ (x 14 10).toNat + (x 13 1 && x 13 11).toNat + (x 12 2 && x 12 12).toNat + (x 11 3 && x 11 13).toNat + (x 10 4 && x 10 14).toNat + (x 9 5).toNat := by have q := hcov10 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16068 := hb (x 9 5)
    have b16069 := hb (x 14 10)
    have b16070 := hb (x 13 1 && x 13 11)
    have b16071 := hb (x 12 2 && x 12 12)
    have b16072 := hb (x 11 3 && x 11 13)
    have b16073 := hb (x 10 4 && x 10 14)
    clear * - r16067 b16068 b16069 b16070 b16071 b16072 b16073 d15757 d15781 d16062 d15425 d15445
    omega
  have d16074 : (x 16 8).toNat = 0 := by
    have r16075 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16076 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
    have e16077 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
    have e16078 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
    have e16079 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
    have e16080 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
    have e16081 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
    have b16082 := hb (x 9 7)
    have b16083 := hb (x 10 6)
    have b16084 := hb (x 11 5)
    have b16085 := hb (x 12 4)
    have b16086 := hb (x 13 11)
    have b16087 := hb (x 14 10)
    have b16088 := hb (x 15 9)
    have b16089 := hb (x 16 8)
    clear * - r16075 e16076 e16077 e16078 e16079 e16080 e16081 b16082 b16083 b16084 b16085 b16086 b16087 b16088 b16089 d16066 d15954
    omega
  have d16090 : (x 15 9).toNat = 0 := by
    have r16091 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16092 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
    have e16093 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
    have e16094 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
    have e16095 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
    have e16096 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
    have e16097 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
    have b16098 := hb (x 9 7)
    have b16099 := hb (x 10 6)
    have b16100 := hb (x 11 5)
    have b16101 := hb (x 12 4)
    have b16102 := hb (x 13 11)
    have b16103 := hb (x 14 10)
    have b16104 := hb (x 15 9)
    have b16105 := hb (x 16 8)
    clear * - r16091 e16092 e16093 e16094 e16095 e16096 e16097 b16098 b16099 b16100 b16101 b16102 b16103 b16104 b16105 d16074 d16066 d15954
    omega
  have d16106 : (x 12 4).toNat = 0 := by
    have r16107 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16108 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
    have e16109 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
    have e16110 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
    have e16111 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
    have e16112 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
    have e16113 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
    have b16114 := hb (x 9 7)
    have b16115 := hb (x 10 6)
    have b16116 := hb (x 11 5)
    have b16117 := hb (x 12 4)
    have b16118 := hb (x 13 11)
    have b16119 := hb (x 14 10)
    have b16120 := hb (x 15 9)
    have b16121 := hb (x 16 8)
    clear * - r16107 e16108 e16109 e16110 e16111 e16112 e16113 b16114 b16115 b16116 b16117 b16118 b16119 b16120 b16121 d16074 d16090 d16066 d15954
    omega
  have d16122 : (x 11 5).toNat = 0 := by
    have r16123 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16124 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
    have e16125 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
    have e16126 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
    have e16127 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
    have e16128 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
    have e16129 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
    have b16130 := hb (x 9 7)
    have b16131 := hb (x 10 6)
    have b16132 := hb (x 11 5)
    have b16133 := hb (x 12 4)
    have b16134 := hb (x 13 11)
    have b16135 := hb (x 14 10)
    have b16136 := hb (x 15 9)
    have b16137 := hb (x 16 8)
    clear * - r16123 e16124 e16125 e16126 e16127 e16128 e16129 b16130 b16131 b16132 b16133 b16134 b16135 b16136 b16137 d16074 d16090 d16066 d15954 d16106
    omega
  have d16138 : (x 10 6).toNat = 0 := by
    have r16139 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16140 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
    have e16141 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
    have e16142 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
    have e16143 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
    have e16144 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
    have e16145 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
    have b16146 := hb (x 9 7)
    have b16147 := hb (x 10 6)
    have b16148 := hb (x 11 5)
    have b16149 := hb (x 12 4)
    have b16150 := hb (x 13 11)
    have b16151 := hb (x 14 10)
    have b16152 := hb (x 15 9)
    have b16153 := hb (x 16 8)
    clear * - r16139 e16140 e16141 e16142 e16143 e16144 e16145 b16146 b16147 b16148 b16149 b16150 b16151 b16152 b16153 d16074 d16090 d16066 d15954 d16106 d16122
    omega
  have d16154 : (x 9 7).toNat = 0 := by
    have r16155 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16156 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
    have e16157 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
    have e16158 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
    have e16159 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
    have e16160 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
    have e16161 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
    have b16162 := hb (x 9 7)
    have b16163 := hb (x 10 6)
    have b16164 := hb (x 11 5)
    have b16165 := hb (x 12 4)
    have b16166 := hb (x 13 11)
    have b16167 := hb (x 14 10)
    have b16168 := hb (x 15 9)
    have b16169 := hb (x 16 8)
    clear * - r16155 e16156 e16157 e16158 e16159 e16160 e16161 b16162 b16163 b16164 b16165 b16166 b16167 b16168 b16169 d16074 d16090 d16066 d15954 d16106 d16122 d16138
    omega
  have d16170 : (x 9 1 && x 9 7).toNat = 0 := by
    have r16171 := hand2 (x 9 1) (x 9 7)
    have b16172 := hb (x 9 7)
    have b16173 := hb (x 9 1 && x 9 7)
    clear * - r16171 b16172 b16173 d16154
    omega
  have d16174 : (x 7 3 && x 7 9).toNat = 1 := by
    have r16175 : 1 ≤ (x 10 6).toNat + (x 9 1 && x 9 7).toNat + (x 8 2 && x 8 8).toNat + (x 7 3 && x 7 9).toNat + (x 6 4 && x 6 10).toNat + (x 5 5 && x 5 11).toNat + (x 4 6 && x 4 12).toNat + (x 3 7 && x 3 13).toNat + (x 2 8 && x 2 14).toNat + (x 1 9).toNat := by have q := hcov6 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16176 := hb (x 1 9)
    have b16177 := hb (x 10 6)
    have b16178 := hb (x 9 1 && x 9 7)
    have b16179 := hb (x 8 2 && x 8 8)
    have b16180 := hb (x 7 3 && x 7 9)
    have b16181 := hb (x 6 4 && x 6 10)
    have b16182 := hb (x 5 5 && x 5 11)
    have b16183 := hb (x 4 6 && x 4 12)
    have b16184 := hb (x 3 7 && x 3 13)
    have b16185 := hb (x 2 8 && x 2 14)
    clear * - r16175 b16176 b16177 b16178 b16179 b16180 b16181 b16182 b16183 b16184 b16185 d16138 d16170 d15457 d15182 d15206 d15134 d15517 d15573 d15577
    omega
  have d16186 : (x 7 9).toNat = 1 := by
    have r16187 := hand2 (x 7 3) (x 7 9)
    have b16188 := hb (x 7 9)
    have b16189 := hb (x 7 3 && x 7 9)
    clear * - r16187 b16188 b16189 d16174
    omega
  have d16190 : (x 7 1).toNat = 1 := by
    have r16191 : (x 7 9).toNat ≤ (x 7 1).toNat := himp _ _ (hp9 7)
    have b16192 := hb (x 7 1)
    have b16193 := hb (x 7 9)
    clear * - r16191 b16192 b16193 d16186
    omega
  have d16194 : (x 8 14).toNat = 0 := by
    have r16195 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16196 := hb (x 7 1)
    have b16197 := hb (x 8 14)
    clear * - r16195 b16196 b16197 d16190
    omega
  have d16198 : (x 8 1 && x 8 14).toNat = 0 := by
    have r16199 := hand2 (x 8 1) (x 8 14)
    have b16200 := hb (x 8 14)
    have b16201 := hb (x 8 1 && x 8 14)
    clear * - r16199 b16200 b16201 d16194
    omega
  have d16202 : (x 7 2).toNat = 1 := by
    have r16203 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16204 := hb (x 7 2)
    have b16205 := hb (x 9 13)
    have b16206 := hb (x 8 1 && x 8 14)
    clear * - r16203 b16204 b16205 b16206 d15429 d16198
    omega
  have d16207 : (x 7 14).toNat = 1 := by
    have r16208 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
    have b16209 := hb (x 7 2)
    have b16210 := hb (x 7 14)
    clear * - r16208 b16209 b16210 d16202
    omega
  have d16211 : (x 6 1).toNat = 0 := by
    have r16212 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16213 := hb (x 6 1)
    have b16214 := hb (x 7 14)
    clear * - r16212 b16213 b16214 d16207
    omega
  have d16215 : (x 6 1 && x 6 11).toNat = 0 := by
    have r16216 := hand1 (x 6 1) (x 6 11)
    have b16217 := hb (x 6 1)
    have b16218 := hb (x 6 1 && x 6 11)
    clear * - r16216 b16217 b16218 d16211
    omega
  have d16219 : (x 7 10).toNat = 1 := by
    have r16220 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16221 := hb (x 2 5)
    have b16222 := hb (x 7 10)
    have b16223 := hb (x 6 1 && x 6 11)
    have b16224 := hb (x 5 2 && x 5 12)
    have b16225 := hb (x 4 3 && x 4 13)
    have b16226 := hb (x 3 4 && x 3 14)
    clear * - r16220 b16221 b16222 b16223 b16224 b16225 b16226 d16215 d15346 d15362 d15390 d15370
    omega
  have d16227 : (x 9 8).toNat = 0 := by
    have r16228 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16229 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
    have e16230 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
    have e16231 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
    have e16232 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
    have e16233 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
    have e16234 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
    have b16235 := hb (x 2 7)
    have b16236 := hb (x 3 6)
    have b16237 := hb (x 4 5)
    have b16238 := hb (x 5 4)
    have b16239 := hb (x 6 11)
    have b16240 := hb (x 7 10)
    have b16241 := hb (x 8 9)
    have b16242 := hb (x 9 8)
    clear * - r16228 e16229 e16230 e16231 e16232 e16233 e16234 b16235 b16236 b16237 b16238 b16239 b16240 b16241 b16242 d16219 d15350 d15366
    omega
  have d16243 : (x 9 8 && x 9 14).toNat = 0 := by
    have r16244 := hand1 (x 9 8) (x 9 14)
    have b16245 := hb (x 9 8)
    have b16246 := hb (x 9 8 && x 9 14)
    clear * - r16244 b16245 b16246 d16227
    omega
  have d16247 : (x 8 9).toNat = 0 := by
    have r16248 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16249 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
    have e16250 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
    have e16251 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
    have e16252 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
    have e16253 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
    have e16254 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
    have b16255 := hb (x 2 7)
    have b16256 := hb (x 3 6)
    have b16257 := hb (x 4 5)
    have b16258 := hb (x 5 4)
    have b16259 := hb (x 6 11)
    have b16260 := hb (x 7 10)
    have b16261 := hb (x 8 9)
    have b16262 := hb (x 9 8)
    clear * - r16248 e16249 e16250 e16251 e16252 e16253 e16254 b16255 b16256 b16257 b16258 b16259 b16260 b16261 b16262 d16227 d16219 d15350 d15366
    omega
  have d16263 : (x 6 11).toNat = 0 := by
    have r16264 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16265 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
    have e16266 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
    have e16267 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
    have e16268 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
    have e16269 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
    have e16270 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
    have b16271 := hb (x 2 7)
    have b16272 := hb (x 3 6)
    have b16273 := hb (x 4 5)
    have b16274 := hb (x 5 4)
    have b16275 := hb (x 6 11)
    have b16276 := hb (x 7 10)
    have b16277 := hb (x 8 9)
    have b16278 := hb (x 9 8)
    clear * - r16264 e16265 e16266 e16267 e16268 e16269 e16270 b16271 b16272 b16273 b16274 b16275 b16276 b16277 b16278 d16227 d16247 d16219 d15350 d15366
    omega
  have d16279 : (x 16 1).toNat = 0 := by
    have r16280 : (x 16 1).toNat + (x 15 2).toNat + (x 14 3).toNat + (x 13 4).toNat + (x 12 5).toNat + (x 11 6).toNat + (x 10 7).toNat + (x 9 8).toNat + (x 8 9).toNat + (x 7 10).toNat + (x 6 11).toNat + (x 5 12).toNat + (x 4 13).toNat + (x 3 14).toNat = 3 := by have q := hcount 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16281 := hb (x 3 14)
    have b16282 := hb (x 4 13)
    have b16283 := hb (x 5 12)
    have b16284 := hb (x 6 11)
    have b16285 := hb (x 7 10)
    have b16286 := hb (x 8 9)
    have b16287 := hb (x 9 8)
    have b16288 := hb (x 10 7)
    have b16289 := hb (x 11 6)
    have b16290 := hb (x 12 5)
    have b16291 := hb (x 13 4)
    have b16292 := hb (x 14 3)
    have b16293 := hb (x 15 2)
    have b16294 := hb (x 16 1)
    clear * - r16280 b16281 b16282 b16283 b16284 b16285 b16286 b16287 b16288 b16289 b16290 b16291 b16292 b16293 b16294 d15802 d15905 d15990 d16006 d16022 d16042 d16227 d16247 d16219 d16263 d15338 d15354 d15101
    omega
  have d16295 : (x 16 1 && x 16 14).toNat = 0 := by
    have r16296 := hand1 (x 16 1) (x 16 14)
    have b16297 := hb (x 16 1)
    have b16298 := hb (x 16 1 && x 16 14)
    clear * - r16296 b16297 b16298 d16279
    omega
  have d16299 : (x 17 13).toNat = 1 := by
    have r16300 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := by have q := hcov13 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16301 := hb (x 15 2)
    have b16302 := hb (x 17 13)
    have b16303 := hb (x 16 1 && x 16 14)
    clear * - r16300 b16301 b16302 b16303 d16295 d15802
    omega
  have d16304 : (x 18 12).toNat = 0 := by
    have r16305 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16306 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
    have e16307 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
    have b16308 := hb (x 15 3)
    have b16309 := hb (x 16 2)
    have b16310 := hb (x 17 13)
    have b16311 := hb (x 18 12)
    clear * - r16305 e16306 e16307 b16308 b16309 b16310 b16311 d16299
    omega
  have d16312 : (x 18 1 && x 18 12).toNat = 0 := by
    have r16313 := hand2 (x 18 1) (x 18 12)
    have b16314 := hb (x 18 12)
    have b16315 := hb (x 18 1 && x 18 12)
    clear * - r16313 b16314 b16315 d16304
    omega
  have d16316 : (x 18 4).toNat = 0 := by
    have r16317 : (x 18 4).toNat ≤ (x 18 12).toNat := himp _ _ (hp4 18)
    have b16318 := hb (x 18 4)
    have b16319 := hb (x 18 12)
    clear * - r16317 b16318 b16319 d16304
    omega
  have d16320 : (x 16 1 && x 16 7).toNat = 0 := by
    have r16321 := hand1 (x 16 1) (x 16 7)
    have b16322 := hb (x 16 1)
    have b16323 := hb (x 16 1 && x 16 7)
    clear * - r16321 b16322 b16323 d16279
    omega
  have d16324 : (x 6 13).toNat = 0 := by
    have r16325 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
    have b16326 := hb (x 6 1)
    have b16327 := hb (x 6 13)
    clear * - r16325 b16326 b16327 d16211
    omega
  have d16328 : (x 6 5).toNat = 0 := by
    have r16329 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
    have b16330 := hb (x 6 5)
    have b16331 := hb (x 6 13)
    clear * - r16329 b16330 b16331 d16324
    omega
  have d16332 : (x 5 1 && x 5 14).toNat = 1 := by
    have r16333 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16334 := hb (x 4 2)
    have b16335 := hb (x 6 13)
    have b16336 := hb (x 5 1 && x 5 14)
    clear * - r16333 b16334 b16335 b16336 d16324 d15142
    omega
  have d16337 : (x 5 14).toNat = 1 := by
    have r16338 := hand2 (x 5 1) (x 5 14)
    have b16339 := hb (x 5 14)
    have b16340 := hb (x 5 1 && x 5 14)
    clear * - r16338 b16339 b16340 d16332
    omega
  have d16341 : (x 9 12).toNat = 0 := by
    have r16342 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16343 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e16344 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b16345 := hb (x 6 3)
    have b16346 := hb (x 7 2)
    have b16347 := hb (x 8 13)
    have b16348 := hb (x 9 12)
    clear * - r16342 e16343 e16344 b16345 b16346 b16347 b16348 d16202
    omega
  have d16349 : (x 9 2 && x 9 12).toNat = 0 := by
    have r16350 := hand2 (x 9 2) (x 9 12)
    have b16351 := hb (x 9 12)
    have b16352 := hb (x 9 2 && x 9 12)
    clear * - r16350 b16351 b16352 d16341
    omega
  have d16353 : (x 9 4).toNat = 0 := by
    have r16354 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
    have b16355 := hb (x 9 4)
    have b16356 := hb (x 9 12)
    clear * - r16354 b16355 b16356 d16341
    omega
  have d16357 : (x 8 13).toNat = 0 := by
    have r16358 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16359 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e16360 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b16361 := hb (x 6 3)
    have b16362 := hb (x 7 2)
    have b16363 := hb (x 8 13)
    have b16364 := hb (x 9 12)
    clear * - r16358 e16359 e16360 b16361 b16362 b16363 b16364 d16341 d16202
    omega
  have d16365 : (x 8 3 && x 8 13).toNat = 0 := by
    have r16366 := hand2 (x 8 3) (x 8 13)
    have b16367 := hb (x 8 13)
    have b16368 := hb (x 8 3 && x 8 13)
    clear * - r16366 b16367 b16368 d16357
    omega
  have d16369 : (x 8 5).toNat = 0 := by
    have r16370 : (x 8 5).toNat ≤ (x 8 13).toNat := himp _ _ (hp5 8)
    have b16371 := hb (x 8 5)
    have b16372 := hb (x 8 13)
    clear * - r16370 b16371 b16372 d16357
    omega
  have d16373 : (x 8 5 && x 8 14).toNat = 0 := by
    have r16374 := hand1 (x 8 5) (x 8 14)
    have b16375 := hb (x 8 5)
    have b16376 := hb (x 8 5 && x 8 14)
    clear * - r16374 b16375 b16376 d16369
    omega
  have d16377 : (x 7 6).toNat = 1 := by
    have r16378 : 1 ≤ (x 13 9).toNat + (x 12 1 && x 12 10).toNat + (x 11 2 && x 11 11).toNat + (x 10 3 && x 10 12).toNat + (x 9 4 && x 9 13).toNat + (x 8 5 && x 8 14).toNat + (x 7 6).toNat := by have q := hcov9 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16379 := hb (x 7 6)
    have b16380 := hb (x 13 9)
    have b16381 := hb (x 12 1 && x 12 10)
    have b16382 := hb (x 11 2 && x 11 11)
    have b16383 := hb (x 10 3 && x 10 12)
    have b16384 := hb (x 9 4 && x 9 13)
    have b16385 := hb (x 8 5 && x 8 14)
    clear * - r16378 b16379 b16380 b16381 b16382 b16383 b16384 b16385 d15649 d15685 d15709 d15413 d15437 d16373
    omega
  have d16386 : (x 13 8).toNat = 0 := by
    have r16387 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16388 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
    have e16389 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
    have e16390 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
    have e16391 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
    have e16392 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
    have e16393 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
    have b16394 := hb (x 6 7)
    have b16395 := hb (x 7 6)
    have b16396 := hb (x 8 5)
    have b16397 := hb (x 9 4)
    have b16398 := hb (x 10 11)
    have b16399 := hb (x 11 10)
    have b16400 := hb (x 12 9)
    have b16401 := hb (x 13 8)
    clear * - r16387 e16388 e16389 e16390 e16391 e16392 e16393 b16394 b16395 b16396 b16397 b16398 b16399 b16400 b16401 d16353 d16369 d16377
    omega
  have d16402 : (x 12 9).toNat = 0 := by
    have r16403 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16404 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
    have e16405 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
    have e16406 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
    have e16407 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
    have e16408 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
    have e16409 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
    have b16410 := hb (x 6 7)
    have b16411 := hb (x 7 6)
    have b16412 := hb (x 8 5)
    have b16413 := hb (x 9 4)
    have b16414 := hb (x 10 11)
    have b16415 := hb (x 11 10)
    have b16416 := hb (x 12 9)
    have b16417 := hb (x 13 8)
    clear * - r16403 e16404 e16405 e16406 e16407 e16408 e16409 b16410 b16411 b16412 b16413 b16414 b16415 b16416 b16417 d16386 d16353 d16369 d16377
    omega
  have d16418 : (x 11 10).toNat = 0 := by
    have r16419 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16420 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
    have e16421 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
    have e16422 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
    have e16423 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
    have e16424 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
    have e16425 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
    have b16426 := hb (x 6 7)
    have b16427 := hb (x 7 6)
    have b16428 := hb (x 8 5)
    have b16429 := hb (x 9 4)
    have b16430 := hb (x 10 11)
    have b16431 := hb (x 11 10)
    have b16432 := hb (x 12 9)
    have b16433 := hb (x 13 8)
    clear * - r16419 e16420 e16421 e16422 e16423 e16424 e16425 b16426 b16427 b16428 b16429 b16430 b16431 b16432 b16433 d16386 d16402 d16353 d16369 d16377
    omega
  have d16434 : (x 10 11).toNat = 0 := by
    have r16435 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16436 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
    have e16437 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
    have e16438 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
    have e16439 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
    have e16440 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
    have e16441 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
    have b16442 := hb (x 6 7)
    have b16443 := hb (x 7 6)
    have b16444 := hb (x 8 5)
    have b16445 := hb (x 9 4)
    have b16446 := hb (x 10 11)
    have b16447 := hb (x 11 10)
    have b16448 := hb (x 12 9)
    have b16449 := hb (x 13 8)
    clear * - r16435 e16436 e16437 e16438 e16439 e16440 e16441 b16442 b16443 b16444 b16445 b16446 b16447 b16448 b16449 d16386 d16402 d16418 d16353 d16369 d16377
    omega
  have d16450 : (x 10 1 && x 10 11).toNat = 0 := by
    have r16451 := hand2 (x 10 1) (x 10 11)
    have b16452 := hb (x 10 11)
    have b16453 := hb (x 10 1 && x 10 11)
    clear * - r16451 b16452 b16453 d16434
    omega
  have d16454 : (x 7 4 && x 7 14).toNat = 1 := by
    have r16455 : 1 ≤ (x 11 10).toNat + (x 10 1 && x 10 11).toNat + (x 9 2 && x 9 12).toNat + (x 8 3 && x 8 13).toNat + (x 7 4 && x 7 14).toNat + (x 6 5).toNat := by have q := hcov10 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16456 := hb (x 6 5)
    have b16457 := hb (x 11 10)
    have b16458 := hb (x 10 1 && x 10 11)
    have b16459 := hb (x 9 2 && x 9 12)
    have b16460 := hb (x 8 3 && x 8 13)
    have b16461 := hb (x 7 4 && x 7 14)
    clear * - r16455 b16456 b16457 b16458 b16459 b16460 b16461 d16418 d16450 d16349 d16365 d16328
    omega
  have d16462 : (x 7 4).toNat = 1 := by
    have r16463 := hand1 (x 7 4) (x 7 14)
    have b16464 := hb (x 7 4)
    have b16465 := hb (x 7 4 && x 7 14)
    clear * - r16463 b16464 b16465 d16454
    omega
  have d16466 : (x 7 12).toNat = 1 := by
    have r16467 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
    have b16468 := hb (x 7 4)
    have b16469 := hb (x 7 12)
    clear * - r16467 b16468 b16469 d16462
    omega
  have d16470 : (x 11 8).toNat = 0 := by
    have r16471 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16472 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e16473 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e16474 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e16475 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e16476 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e16477 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have b16478 := hb (x 4 7)
    have b16479 := hb (x 5 6)
    have b16480 := hb (x 6 5)
    have b16481 := hb (x 7 4)
    have b16482 := hb (x 8 11)
    have b16483 := hb (x 9 10)
    have b16484 := hb (x 10 9)
    have b16485 := hb (x 11 8)
    clear * - r16471 e16472 e16473 e16474 e16475 e16476 e16477 b16478 b16479 b16480 b16481 b16482 b16483 b16484 b16485 d16462 d16328
    omega
  have d16486 : (x 11 8 && x 11 12).toNat = 0 := by
    have r16487 := hand1 (x 11 8) (x 11 12)
    have b16488 := hb (x 11 8)
    have b16489 := hb (x 11 8 && x 11 12)
    clear * - r16487 b16488 b16489 d16470
    omega
  have d16490 : (x 11 4 && x 11 8).toNat = 0 := by
    have r16491 := hand2 (x 11 4) (x 11 8)
    have b16492 := hb (x 11 8)
    have b16493 := hb (x 11 4 && x 11 8)
    clear * - r16491 b16492 b16493 d16470
    omega
  have d16494 : (x 10 9).toNat = 0 := by
    have r16495 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16496 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e16497 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e16498 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e16499 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e16500 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e16501 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have b16502 := hb (x 4 7)
    have b16503 := hb (x 5 6)
    have b16504 := hb (x 6 5)
    have b16505 := hb (x 7 4)
    have b16506 := hb (x 8 11)
    have b16507 := hb (x 9 10)
    have b16508 := hb (x 10 9)
    have b16509 := hb (x 11 8)
    clear * - r16495 e16496 e16497 e16498 e16499 e16500 e16501 b16502 b16503 b16504 b16505 b16506 b16507 b16508 b16509 d16470 d16462 d16328
    omega
  have d16510 : (x 10 9 && x 10 13).toNat = 0 := by
    have r16511 := hand1 (x 10 9) (x 10 13)
    have b16512 := hb (x 10 9)
    have b16513 := hb (x 10 9 && x 10 13)
    clear * - r16511 b16512 b16513 d16494
    omega
  have d16514 : (x 10 5 && x 10 9).toNat = 0 := by
    have r16515 := hand2 (x 10 5) (x 10 9)
    have b16516 := hb (x 10 9)
    have b16517 := hb (x 10 5 && x 10 9)
    clear * - r16515 b16516 b16517 d16494
    omega
  have d16518 : (x 9 10).toNat = 0 := by
    have r16519 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16520 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e16521 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e16522 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e16523 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e16524 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e16525 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have b16526 := hb (x 4 7)
    have b16527 := hb (x 5 6)
    have b16528 := hb (x 6 5)
    have b16529 := hb (x 7 4)
    have b16530 := hb (x 8 11)
    have b16531 := hb (x 9 10)
    have b16532 := hb (x 10 9)
    have b16533 := hb (x 11 8)
    clear * - r16519 e16520 e16521 e16522 e16523 e16524 e16525 b16526 b16527 b16528 b16529 b16530 b16531 b16532 b16533 d16470 d16494 d16462 d16328
    omega
  have d16534 : (x 9 6 && x 9 10).toNat = 0 := by
    have r16535 := hand2 (x 9 6) (x 9 10)
    have b16536 := hb (x 9 10)
    have b16537 := hb (x 9 6 && x 9 10)
    clear * - r16535 b16536 b16537 d16518
    omega
  have d16538 : (x 8 11).toNat = 0 := by
    have r16539 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16540 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e16541 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e16542 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e16543 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e16544 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e16545 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have b16546 := hb (x 4 7)
    have b16547 := hb (x 5 6)
    have b16548 := hb (x 6 5)
    have b16549 := hb (x 7 4)
    have b16550 := hb (x 8 11)
    have b16551 := hb (x 9 10)
    have b16552 := hb (x 10 9)
    have b16553 := hb (x 11 8)
    clear * - r16539 e16540 e16541 e16542 e16543 e16544 e16545 b16546 b16547 b16548 b16549 b16550 b16551 b16552 b16553 d16470 d16494 d16518 d16462 d16328
    omega
  have d16554 : (x 8 7 && x 8 11).toNat = 0 := by
    have r16555 := hand2 (x 8 7) (x 8 11)
    have b16556 := hb (x 8 11)
    have b16557 := hb (x 8 7 && x 8 11)
    clear * - r16555 b16556 b16557 d16538
    omega
  have d16558 : (x 14 5).toNat = 1 := by
    have r16559 : 1 ≤ (x 15 4).toNat + (x 14 1 && x 14 5).toNat + (x 13 2 && x 13 6).toNat + (x 12 3 && x 12 7).toNat + (x 11 4 && x 11 8).toNat + (x 10 5 && x 10 9).toNat + (x 9 6 && x 9 10).toNat + (x 8 7 && x 8 11).toNat + (x 7 8 && x 7 12).toNat + (x 6 9 && x 6 13).toNat + (x 5 10 && x 5 14).toNat + (x 4 11).toNat := by have q := hcov4 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16560 : (x 14 1 && x 14 5).toNat = (x 14 5).toNat := handr _ _ (fun h => hp13 14 (hp5 14 (h)))
    have e16561 : (x 5 10 && x 5 14).toNat = (x 5 10).toNat := handl _ _ (fun h => hp2 5 (hp10 5 (h)))
    have b16562 := hb (x 4 11)
    have b16563 := hb (x 5 10)
    have b16564 := hb (x 14 5)
    have b16565 := hb (x 15 4)
    have b16566 := hb (x 13 2 && x 13 6)
    have b16567 := hb (x 12 3 && x 12 7)
    have b16568 := hb (x 11 4 && x 11 8)
    have b16569 := hb (x 10 5 && x 10 9)
    have b16570 := hb (x 9 6 && x 9 10)
    have b16571 := hb (x 8 7 && x 8 11)
    have b16572 := hb (x 7 8 && x 7 12)
    have b16573 := hb (x 6 9 && x 6 13)
    clear * - r16559 e16560 e16561 b16562 b16563 b16564 b16565 b16566 b16567 b16568 b16569 b16570 b16571 b16572 b16573 d15822 d15838 d15862 d16490 d16514 d16534 d16554 d14996 d15016 d15020 d15040
    omega
  have d16574 : (x 19 8).toNat = 0 := by
    have r16575 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16576 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
    have e16577 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
    have e16578 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
    have e16579 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
    have e16580 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
    have e16581 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
    have b16582 := hb (x 12 7)
    have b16583 := hb (x 13 6)
    have b16584 := hb (x 14 5)
    have b16585 := hb (x 15 4)
    have b16586 := hb (x 16 11)
    have b16587 := hb (x 17 10)
    have b16588 := hb (x 18 9)
    have b16589 := hb (x 19 8)
    clear * - r16575 e16576 e16577 e16578 e16579 e16580 e16581 b16582 b16583 b16584 b16585 b16586 b16587 b16588 b16589 d15822 d16558
    omega
  have d16590 : (x 18 9).toNat = 0 := by
    have r16591 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16592 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
    have e16593 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
    have e16594 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
    have e16595 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
    have e16596 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
    have e16597 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
    have b16598 := hb (x 12 7)
    have b16599 := hb (x 13 6)
    have b16600 := hb (x 14 5)
    have b16601 := hb (x 15 4)
    have b16602 := hb (x 16 11)
    have b16603 := hb (x 17 10)
    have b16604 := hb (x 18 9)
    have b16605 := hb (x 19 8)
    clear * - r16591 e16592 e16593 e16594 e16595 e16596 e16597 b16598 b16599 b16600 b16601 b16602 b16603 b16604 b16605 d16574 d15822 d16558
    omega
  have d16606 : (x 17 10).toNat = 0 := by
    have r16607 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16608 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
    have e16609 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
    have e16610 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
    have e16611 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
    have e16612 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
    have e16613 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
    have b16614 := hb (x 12 7)
    have b16615 := hb (x 13 6)
    have b16616 := hb (x 14 5)
    have b16617 := hb (x 15 4)
    have b16618 := hb (x 16 11)
    have b16619 := hb (x 17 10)
    have b16620 := hb (x 18 9)
    have b16621 := hb (x 19 8)
    clear * - r16607 e16608 e16609 e16610 e16611 e16612 e16613 b16614 b16615 b16616 b16617 b16618 b16619 b16620 b16621 d16574 d16590 d15822 d16558
    omega
  have d16622 : (x 16 11).toNat = 0 := by
    have r16623 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16624 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
    have e16625 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
    have e16626 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
    have e16627 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
    have e16628 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
    have e16629 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
    have b16630 := hb (x 12 7)
    have b16631 := hb (x 13 6)
    have b16632 := hb (x 14 5)
    have b16633 := hb (x 15 4)
    have b16634 := hb (x 16 11)
    have b16635 := hb (x 17 10)
    have b16636 := hb (x 18 9)
    have b16637 := hb (x 19 8)
    clear * - r16623 e16624 e16625 e16626 e16627 e16628 e16629 b16630 b16631 b16632 b16633 b16634 b16635 b16636 b16637 d16574 d16590 d16606 d15822 d16558
    omega
  have d16638 : (x 13 6).toNat = 0 := by
    have r16639 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16640 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
    have e16641 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
    have e16642 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
    have e16643 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
    have e16644 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
    have e16645 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
    have b16646 := hb (x 12 7)
    have b16647 := hb (x 13 6)
    have b16648 := hb (x 14 5)
    have b16649 := hb (x 15 4)
    have b16650 := hb (x 16 11)
    have b16651 := hb (x 17 10)
    have b16652 := hb (x 18 9)
    have b16653 := hb (x 19 8)
    clear * - r16639 e16640 e16641 e16642 e16643 e16644 e16645 b16646 b16647 b16648 b16649 b16650 b16651 b16652 b16653 d16574 d16590 d16606 d16622 d15822 d16558
    omega
  have d16654 : (x 12 7).toNat = 0 := by
    have r16655 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16656 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
    have e16657 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
    have e16658 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
    have e16659 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
    have e16660 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
    have e16661 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
    have b16662 := hb (x 12 7)
    have b16663 := hb (x 13 6)
    have b16664 := hb (x 14 5)
    have b16665 := hb (x 15 4)
    have b16666 := hb (x 16 11)
    have b16667 := hb (x 17 10)
    have b16668 := hb (x 18 9)
    have b16669 := hb (x 19 8)
    clear * - r16655 e16656 e16657 e16658 e16659 e16660 e16661 b16662 b16663 b16664 b16665 b16666 b16667 b16668 b16669 d16574 d16590 d16606 d16622 d15822 d16558 d16638
    omega
  have d16670 : (x 18 1).toNat = 0 := by
    have r16671 : (x 18 1).toNat + (x 17 2).toNat + (x 16 3).toNat + (x 15 4).toNat + (x 14 5).toNat + (x 13 6).toNat + (x 12 7).toNat + (x 11 8).toNat + (x 10 9).toNat + (x 9 10).toNat + (x 8 11).toNat + (x 7 12).toNat + (x 6 13).toNat + (x 5 14).toNat = 3 := by have q := hcount 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16672 := hb (x 5 14)
    have b16673 := hb (x 6 13)
    have b16674 := hb (x 7 12)
    have b16675 := hb (x 8 11)
    have b16676 := hb (x 9 10)
    have b16677 := hb (x 10 9)
    have b16678 := hb (x 11 8)
    have b16679 := hb (x 12 7)
    have b16680 := hb (x 13 6)
    have b16681 := hb (x 14 5)
    have b16682 := hb (x 15 4)
    have b16683 := hb (x 16 3)
    have b16684 := hb (x 17 2)
    have b16685 := hb (x 18 1)
    clear * - r16671 b16672 b16673 b16674 b16675 b16676 b16677 b16678 b16679 b16680 b16681 b16682 b16683 b16684 b16685 d15822 d16558 d16638 d16654 d16470 d16494 d16518 d16538 d16466 d16324 d16337
    omega
  have d16686 : (x 18 13).toNat = 0 := by
    have r16687 : (x 18 13).toNat ≤ (x 18 1).toNat := himp _ _ (hp13 18)
    have b16688 := hb (x 18 1)
    have b16689 := hb (x 18 13)
    clear * - r16687 b16688 b16689 d16670
    omega
  have d16690 : (x 18 5).toNat = 0 := by
    have r16691 : (x 18 5).toNat ≤ (x 18 13).toNat := himp _ _ (hp5 18)
    have b16692 := hb (x 18 5)
    have b16693 := hb (x 18 13)
    clear * - r16691 b16692 b16693 d16686
    omega
  have d16694 : (x 17 2).toNat = 0 := by
    have r16695 : (x 18 1).toNat + (x 17 2).toNat + (x 16 3).toNat + (x 15 4).toNat + (x 14 5).toNat + (x 13 6).toNat + (x 12 7).toNat + (x 11 8).toNat + (x 10 9).toNat + (x 9 10).toNat + (x 8 11).toNat + (x 7 12).toNat + (x 6 13).toNat + (x 5 14).toNat = 3 := by have q := hcount 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16696 := hb (x 5 14)
    have b16697 := hb (x 6 13)
    have b16698 := hb (x 7 12)
    have b16699 := hb (x 8 11)
    have b16700 := hb (x 9 10)
    have b16701 := hb (x 10 9)
    have b16702 := hb (x 11 8)
    have b16703 := hb (x 12 7)
    have b16704 := hb (x 13 6)
    have b16705 := hb (x 14 5)
    have b16706 := hb (x 15 4)
    have b16707 := hb (x 16 3)
    have b16708 := hb (x 17 2)
    have b16709 := hb (x 18 1)
    clear * - r16695 b16696 b16697 b16698 b16699 b16700 b16701 b16702 b16703 b16704 b16705 b16706 b16707 b16708 b16709 d16670 d15822 d16558 d16638 d16654 d16470 d16494 d16518 d16538 d16466 d16324 d16337
    omega
  have d16710 : (x 17 2 && x 17 13).toNat = 0 := by
    have r16711 := hand1 (x 17 2) (x 17 13)
    have b16712 := hb (x 17 2)
    have b16713 := hb (x 17 2 && x 17 13)
    clear * - r16711 b16712 b16713 d16694
    omega
  have d16714 : (x 17 2 && x 17 6).toNat = 0 := by
    have r16715 := hand1 (x 17 2) (x 17 6)
    have b16716 := hb (x 17 2)
    have b16717 := hb (x 17 2 && x 17 6)
    clear * - r16715 b16716 b16717 d16694
    omega
  have d16718 : (x 16 3).toNat = 0 := by
    have r16719 : (x 18 1).toNat + (x 17 2).toNat + (x 16 3).toNat + (x 15 4).toNat + (x 14 5).toNat + (x 13 6).toNat + (x 12 7).toNat + (x 11 8).toNat + (x 10 9).toNat + (x 9 10).toNat + (x 8 11).toNat + (x 7 12).toNat + (x 6 13).toNat + (x 5 14).toNat = 3 := by have q := hcount 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16720 := hb (x 5 14)
    have b16721 := hb (x 6 13)
    have b16722 := hb (x 7 12)
    have b16723 := hb (x 8 11)
    have b16724 := hb (x 9 10)
    have b16725 := hb (x 10 9)
    have b16726 := hb (x 11 8)
    have b16727 := hb (x 12 7)
    have b16728 := hb (x 13 6)
    have b16729 := hb (x 14 5)
    have b16730 := hb (x 15 4)
    have b16731 := hb (x 16 3)
    have b16732 := hb (x 17 2)
    have b16733 := hb (x 18 1)
    clear * - r16719 b16720 b16721 b16722 b16723 b16724 b16725 b16726 b16727 b16728 b16729 b16730 b16731 b16732 b16733 d16670 d16694 d15822 d16558 d16638 d16654 d16470 d16494 d16518 d16538 d16466 d16324 d16337
    omega
  have d16734 : (x 16 3 && x 16 14).toNat = 0 := by
    have r16735 := hand1 (x 16 3) (x 16 14)
    have b16736 := hb (x 16 3)
    have b16737 := hb (x 16 3 && x 16 14)
    clear * - r16735 b16736 b16737 d16718
    omega
  have d16738 : (x 19 11).toNat = 1 := by
    have r16739 : 1 ≤ (x 19 11).toNat + (x 18 1 && x 18 12).toNat + (x 17 2 && x 17 13).toNat + (x 16 3 && x 16 14).toNat + (x 15 4).toNat := by have q := hcov11 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16740 := hb (x 15 4)
    have b16741 := hb (x 19 11)
    have b16742 := hb (x 18 1 && x 18 12)
    have b16743 := hb (x 17 2 && x 17 13)
    have b16744 := hb (x 16 3 && x 16 14)
    clear * - r16739 b16740 b16741 b16742 b16743 b16744 d16312 d16710 d16734 d15822
    omega
  have d16745 : (x 22 8).toNat = 0 := by
    have r16746 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16747 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
    have e16748 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
    have e16749 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
    have e16750 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
    have e16751 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
    have e16752 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
    have b16753 := hb (x 15 7)
    have b16754 := hb (x 16 6)
    have b16755 := hb (x 17 5)
    have b16756 := hb (x 18 4)
    have b16757 := hb (x 19 11)
    have b16758 := hb (x 20 10)
    have b16759 := hb (x 21 9)
    have b16760 := hb (x 22 8)
    clear * - r16746 e16747 e16748 e16749 e16750 e16751 e16752 b16753 b16754 b16755 b16756 b16757 b16758 b16759 b16760 d16738 d16316
    omega
  have d16761 : (x 21 9).toNat = 0 := by
    have r16762 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16763 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
    have e16764 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
    have e16765 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
    have e16766 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
    have e16767 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
    have e16768 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
    have b16769 := hb (x 15 7)
    have b16770 := hb (x 16 6)
    have b16771 := hb (x 17 5)
    have b16772 := hb (x 18 4)
    have b16773 := hb (x 19 11)
    have b16774 := hb (x 20 10)
    have b16775 := hb (x 21 9)
    have b16776 := hb (x 22 8)
    clear * - r16762 e16763 e16764 e16765 e16766 e16767 e16768 b16769 b16770 b16771 b16772 b16773 b16774 b16775 b16776 d16745 d16738 d16316
    omega
  have d16777 : (x 20 10).toNat = 0 := by
    have r16778 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16779 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
    have e16780 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
    have e16781 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
    have e16782 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
    have e16783 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
    have e16784 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
    have b16785 := hb (x 15 7)
    have b16786 := hb (x 16 6)
    have b16787 := hb (x 17 5)
    have b16788 := hb (x 18 4)
    have b16789 := hb (x 19 11)
    have b16790 := hb (x 20 10)
    have b16791 := hb (x 21 9)
    have b16792 := hb (x 22 8)
    clear * - r16778 e16779 e16780 e16781 e16782 e16783 e16784 b16785 b16786 b16787 b16788 b16789 b16790 b16791 b16792 d16745 d16761 d16738 d16316
    omega
  have d16793 : (x 17 5).toNat = 0 := by
    have r16794 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16795 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
    have e16796 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
    have e16797 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
    have e16798 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
    have e16799 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
    have e16800 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
    have b16801 := hb (x 15 7)
    have b16802 := hb (x 16 6)
    have b16803 := hb (x 17 5)
    have b16804 := hb (x 18 4)
    have b16805 := hb (x 19 11)
    have b16806 := hb (x 20 10)
    have b16807 := hb (x 21 9)
    have b16808 := hb (x 22 8)
    clear * - r16794 e16795 e16796 e16797 e16798 e16799 e16800 b16801 b16802 b16803 b16804 b16805 b16806 b16807 b16808 d16745 d16761 d16777 d16738 d16316
    omega
  have d16809 : (x 16 6).toNat = 0 := by
    have r16810 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16811 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
    have e16812 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
    have e16813 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
    have e16814 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
    have e16815 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
    have e16816 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
    have b16817 := hb (x 15 7)
    have b16818 := hb (x 16 6)
    have b16819 := hb (x 17 5)
    have b16820 := hb (x 18 4)
    have b16821 := hb (x 19 11)
    have b16822 := hb (x 20 10)
    have b16823 := hb (x 21 9)
    have b16824 := hb (x 22 8)
    clear * - r16810 e16811 e16812 e16813 e16814 e16815 e16816 b16817 b16818 b16819 b16820 b16821 b16822 b16823 b16824 d16745 d16761 d16777 d16738 d16316 d16793
    omega
  have d16825 : (x 15 7).toNat = 0 := by
    have r16826 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16827 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
    have e16828 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
    have e16829 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
    have e16830 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
    have e16831 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
    have e16832 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
    have b16833 := hb (x 15 7)
    have b16834 := hb (x 16 6)
    have b16835 := hb (x 17 5)
    have b16836 := hb (x 18 4)
    have b16837 := hb (x 19 11)
    have b16838 := hb (x 20 10)
    have b16839 := hb (x 21 9)
    have b16840 := hb (x 22 8)
    clear * - r16826 e16827 e16828 e16829 e16830 e16831 e16832 b16833 b16834 b16835 b16836 b16837 b16838 b16839 b16840 d16745 d16761 d16777 d16738 d16316 d16793 d16809
    omega
  have d16841 : (x 8 7 && x 8 14).toNat = 1 := by
    have r16842 : 1 ≤ (x 15 7).toNat + (x 14 1 && x 14 8).toNat + (x 13 2 && x 13 9).toNat + (x 12 3 && x 12 10).toNat + (x 11 4 && x 11 11).toNat + (x 10 5 && x 10 12).toNat + (x 9 6 && x 9 13).toNat + (x 8 7 && x 8 14).toNat + (x 7 8).toNat := by have q := hcov7 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16843 := hb (x 7 8)
    have b16844 := hb (x 15 7)
    have b16845 := hb (x 14 1 && x 14 8)
    have b16846 := hb (x 13 2 && x 13 9)
    have b16847 := hb (x 12 3 && x 12 10)
    have b16848 := hb (x 11 4 && x 11 11)
    have b16849 := hb (x 10 5 && x 10 12)
    have b16850 := hb (x 9 6 && x 9 13)
    have b16851 := hb (x 8 7 && x 8 14)
    clear * - r16842 b16843 b16844 b16845 b16846 b16847 b16848 b16849 b16850 b16851 d16825 d15645 d15665 d15689 d15713 d15417 d15441 d14980
    omega
  have d16852 : (x 8 7).toNat = 1 := by
    have r16853 := hand1 (x 8 7) (x 8 14)
    have b16854 := hb (x 8 7)
    have b16855 := hb (x 8 7 && x 8 14)
    clear * - r16853 b16854 b16855 d16841
    omega
  have d16856 : (x 15 8).toNat = 0 := by
    have r16857 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16858 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
    have e16859 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
    have e16860 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
    have e16861 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
    have e16862 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
    have e16863 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
    have b16864 := hb (x 8 7)
    have b16865 := hb (x 9 6)
    have b16866 := hb (x 10 5)
    have b16867 := hb (x 11 4)
    have b16868 := hb (x 12 11)
    have b16869 := hb (x 13 10)
    have b16870 := hb (x 14 9)
    have b16871 := hb (x 15 8)
    clear * - r16857 e16858 e16859 e16860 e16861 e16862 e16863 b16864 b16865 b16866 b16867 b16868 b16869 b16870 b16871 d15842 d15866 d16852
    omega
  have d16872 : (x 14 9).toNat = 0 := by
    have r16873 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16874 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
    have e16875 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
    have e16876 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
    have e16877 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
    have e16878 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
    have e16879 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
    have b16880 := hb (x 8 7)
    have b16881 := hb (x 9 6)
    have b16882 := hb (x 10 5)
    have b16883 := hb (x 11 4)
    have b16884 := hb (x 12 11)
    have b16885 := hb (x 13 10)
    have b16886 := hb (x 14 9)
    have b16887 := hb (x 15 8)
    clear * - r16873 e16874 e16875 e16876 e16877 e16878 e16879 b16880 b16881 b16882 b16883 b16884 b16885 b16886 b16887 d16856 d15842 d15866 d16852
    omega
  have d16888 : (x 14 3 && x 14 9).toNat = 0 := by
    have r16889 := hand2 (x 14 3) (x 14 9)
    have b16890 := hb (x 14 9)
    have b16891 := hb (x 14 3 && x 14 9)
    clear * - r16889 b16890 b16891 d16872
    omega
  have d16892 : (x 17 6).toNat = 1 := by
    have r16893 : 1 ≤ (x 17 6).toNat + (x 16 1 && x 16 7).toNat + (x 15 2 && x 15 8).toNat + (x 14 3 && x 14 9).toNat + (x 13 4 && x 13 10).toNat + (x 12 5 && x 12 11).toNat + (x 11 6 && x 11 12).toNat + (x 10 7 && x 10 13).toNat + (x 9 8 && x 9 14).toNat + (x 8 9).toNat := by have q := hcov6 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16894 := hb (x 8 9)
    have b16895 := hb (x 17 6)
    have b16896 := hb (x 16 1 && x 16 7)
    have b16897 := hb (x 15 2 && x 15 8)
    have b16898 := hb (x 14 3 && x 14 9)
    have b16899 := hb (x 13 4 && x 13 10)
    have b16900 := hb (x 12 5 && x 12 11)
    have b16901 := hb (x 11 6 && x 11 12)
    have b16902 := hb (x 10 7 && x 10 13)
    have b16903 := hb (x 9 8 && x 9 14)
    clear * - r16893 b16894 b16895 b16896 b16897 b16898 b16899 b16900 b16901 b16902 b16903 d16320 d15806 d16888 d15846 d15870 d16038 d16058 d16243 d16247
    omega
  have d16904 : (x 23 8).toNat = 0 := by
    have r16905 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16906 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
    have e16907 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
    have e16908 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
    have e16909 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
    have e16910 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
    have e16911 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
    have b16912 := hb (x 16 7)
    have b16913 := hb (x 17 6)
    have b16914 := hb (x 18 5)
    have b16915 := hb (x 19 4)
    have b16916 := hb (x 20 11)
    have b16917 := hb (x 21 10)
    have b16918 := hb (x 22 9)
    have b16919 := hb (x 23 8)
    clear * - r16905 e16906 e16907 e16908 e16909 e16910 e16911 b16912 b16913 b16914 b16915 b16916 b16917 b16918 b16919 d16690 d16892
    omega
  have d16920 : (x 22 9).toNat = 0 := by
    have r16921 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16922 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
    have e16923 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
    have e16924 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
    have e16925 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
    have e16926 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
    have e16927 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
    have b16928 := hb (x 16 7)
    have b16929 := hb (x 17 6)
    have b16930 := hb (x 18 5)
    have b16931 := hb (x 19 4)
    have b16932 := hb (x 20 11)
    have b16933 := hb (x 21 10)
    have b16934 := hb (x 22 9)
    have b16935 := hb (x 23 8)
    clear * - r16921 e16922 e16923 e16924 e16925 e16926 e16927 b16928 b16929 b16930 b16931 b16932 b16933 b16934 b16935 d16904 d16690 d16892
    omega
  have d16936 : (x 21 10).toNat = 0 := by
    have r16937 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16938 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
    have e16939 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
    have e16940 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
    have e16941 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
    have e16942 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
    have e16943 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
    have b16944 := hb (x 16 7)
    have b16945 := hb (x 17 6)
    have b16946 := hb (x 18 5)
    have b16947 := hb (x 19 4)
    have b16948 := hb (x 20 11)
    have b16949 := hb (x 21 10)
    have b16950 := hb (x 22 9)
    have b16951 := hb (x 23 8)
    clear * - r16937 e16938 e16939 e16940 e16941 e16942 e16943 b16944 b16945 b16946 b16947 b16948 b16949 b16950 b16951 d16904 d16920 d16690 d16892
    omega
  have d16952 : (x 20 11).toNat = 0 := by
    have r16953 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16954 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
    have e16955 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
    have e16956 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
    have e16957 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
    have e16958 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
    have e16959 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
    have b16960 := hb (x 16 7)
    have b16961 := hb (x 17 6)
    have b16962 := hb (x 18 5)
    have b16963 := hb (x 19 4)
    have b16964 := hb (x 20 11)
    have b16965 := hb (x 21 10)
    have b16966 := hb (x 22 9)
    have b16967 := hb (x 23 8)
    clear * - r16953 e16954 e16955 e16956 e16957 e16958 e16959 b16960 b16961 b16962 b16963 b16964 b16965 b16966 b16967 d16904 d16920 d16936 d16690 d16892
    omega
  have d16968 : (x 19 4).toNat = 0 := by
    have r16969 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16970 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
    have e16971 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
    have e16972 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
    have e16973 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
    have e16974 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
    have e16975 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
    have b16976 := hb (x 16 7)
    have b16977 := hb (x 17 6)
    have b16978 := hb (x 18 5)
    have b16979 := hb (x 19 4)
    have b16980 := hb (x 20 11)
    have b16981 := hb (x 21 10)
    have b16982 := hb (x 22 9)
    have b16983 := hb (x 23 8)
    clear * - r16969 e16970 e16971 e16972 e16973 e16974 e16975 b16976 b16977 b16978 b16979 b16980 b16981 b16982 b16983 d16904 d16920 d16936 d16952 d16690 d16892
    omega
  have d16984 : (x 16 7).toNat = 0 := by
    have r16985 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16986 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
    have e16987 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
    have e16988 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
    have e16989 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
    have e16990 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
    have e16991 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
    have b16992 := hb (x 16 7)
    have b16993 := hb (x 17 6)
    have b16994 := hb (x 18 5)
    have b16995 := hb (x 19 4)
    have b16996 := hb (x 20 11)
    have b16997 := hb (x 21 10)
    have b16998 := hb (x 22 9)
    have b16999 := hb (x 23 8)
    clear * - r16985 e16986 e16987 e16988 e16989 e16990 e16991 b16992 b16993 b16994 b16995 b16996 b16997 b16998 b16999 d16904 d16920 d16936 d16952 d16968 d16690 d16892
    omega
  have d17000 : (x 16 3 && x 16 7).toNat = 0 := by
    have r17001 := hand2 (x 16 3) (x 16 7)
    have b17002 := hb (x 16 7)
    have b17003 := hb (x 16 3 && x 16 7)
    clear * - r17001 b17002 b17003 d16984
    omega
  have d17004 : (x 14 5 && x 14 9).toNat = 1 := by
    have r17005 : 1 ≤ (x 19 4).toNat + (x 18 1 && x 18 5).toNat + (x 17 2 && x 17 6).toNat + (x 16 3 && x 16 7).toNat + (x 15 4 && x 15 8).toNat + (x 14 5 && x 14 9).toNat + (x 13 6 && x 13 10).toNat + (x 12 7 && x 12 11).toNat + (x 11 8 && x 11 12).toNat + (x 10 9 && x 10 13).toNat + (x 9 10 && x 9 14).toNat + (x 8 11).toNat := by have q := hcov4 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17006 : (x 18 1 && x 18 5).toNat = (x 18 5).toNat := handr _ _ (fun h => hp13 18 (hp5 18 (h)))
    have e17007 : (x 9 10 && x 9 14).toNat = (x 9 10).toNat := handl _ _ (fun h => hp2 9 (hp10 9 (h)))
    have b17008 := hb (x 8 11)
    have b17009 := hb (x 9 10)
    have b17010 := hb (x 18 5)
    have b17011 := hb (x 19 4)
    have b17012 := hb (x 17 2 && x 17 6)
    have b17013 := hb (x 16 3 && x 16 7)
    have b17014 := hb (x 15 4 && x 15 8)
    have b17015 := hb (x 14 5 && x 14 9)
    have b17016 := hb (x 13 6 && x 13 10)
    have b17017 := hb (x 12 7 && x 12 11)
    have b17018 := hb (x 11 8 && x 11 12)
    have b17019 := hb (x 10 9 && x 10 13)
    clear * - r17005 e17006 e17007 b17008 b17009 b17010 b17011 b17012 b17013 b17014 b17015 b17016 b17017 b17018 b17019 d16968 d16690 d16714 d17000 d15826 d15850 d15874 d16486 d16510 d16518 d16538
    omega
  have r17020 := hand2 (x 14 5) (x 14 9)
  have b17021 := hb (x 14 9)
  have b17022 := hb (x 14 5 && x 14 9)
  linarith only [r17020, b17021, b17022, d17004, d16872]

theorem cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a10001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-1) 5).toNat = 0)
    (g1 : (x (-1) 11).toNat = 0)
    (g2 : (x 0 3).toNat = 0)
    (g3 : (x 0 5).toNat = 0)
    (g4 : (x 0 6).toNat = 0)
    (g5 : (x 0 7).toNat = 1)
    (g6 : (x 0 14).toNat = 1)
    (g7 : (x 1 2).toNat = 0)
    (g8 : (x 1 5).toNat = 0)
    (g9 : (x 1 6).toNat = 0)
    (g10 : (x 1 10).toNat = 0)
    (g11 : (x 1 13).toNat = 0)
    (g12 : (x 2 4).toNat = 0)
    (g13 : (x 2 12).toNat = 0)
    (g14 : (x 2 8 && x 2 12).toNat = 0)
    (g15 : (x 1 9 && x 1 13).toNat = 0)
    (g16 : (x 2 4 && x 2 13).toNat = 0)
    (g17 : (x 1 5 && x 1 14).toNat = 0)
    (g18 : (x 0 1 && x 0 11).toNat = 0)
    (g19 : (x (-1) 2 && x (-1) 12).toNat = 0)
    (g20 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g21 : (x 0 2 && x 0 12).toNat = 0)
    (g22 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g23 : (x 2 2 && x 2 12).toNat = 0)
    (g24 : (x 1 3 && x 1 13).toNat = 0)
    (g25 : (x 0 4 && x 0 14).toNat = 0)
    (g26 : (x 1 4 && x 1 14).toNat = 0)
    (g27 : (x 0 1 && x 0 12).toNat = 0)
    (g28 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g29 : (x (-2) 3 && x (-2) 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a10001_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29
