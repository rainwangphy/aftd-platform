import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt001

Topic: combinatorics   Node: 0c2097b31604

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_alternates_core: under the layer-free tight-cover constraints for k = 15 and 10 fixed bits of the class-type sequence near position 0, the constraints are contradictory. Its module also proves the sibling branches cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt000101, cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00011.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt000101 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-2) 13).toNat = 0)
    (g1 : (x 0 2).toNat = 0)
    (g2 : (x 0 6).toNat = 1)
    (g3 : (x 0 13).toNat = 0)
    (g4 : (x 1 4).toNat = 0)
    (g5 : (x 1 13).toNat = 0)
    (g6 : (x 3 2).toNat = 0)
    (g7 : (x 3 4).toNat = 0)
    (g8 : (x 0 1 && x 0 12).toNat = 0)
    (g9 : (x (-2) 3 && x (-2) 14).toNat = 0)
    (g10 : (x 1 1 && x 1 12).toNat = 0)
    (g11 : (x 0 2 && x 0 13).toNat = 0)
    (g12 : (x 1 2 && x 1 13).toNat = 0)
    (g13 : (x 0 3 && x 0 14).toNat = 0)
    (g14 : (x 3 2 && x 3 13).toNat = 0)
    (g15 : (x (-2) 1 && x (-2) 14).toNat = 0)
    (g16 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d26978 : (x 0 14).toNat = 1 := by
    have r26979 : (x 0 6).toNat ≤ (x 0 14).toNat := himp _ _ (hp6 0)
    have b26980 := hb (x 0 6)
    have b26981 := hb (x 0 14)
    clear * - r26979 b26980 b26981 g2
    omega
  have d26982 : (x (-1) 1).toNat = 0 := by
    have r26983 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26984 := hb (x (-1) 1)
    have b26985 := hb (x 0 14)
    clear * - r26983 b26984 b26985 d26978
    omega
  have d26986 : (x (-1) 1 && x (-1) 14).toNat = 0 := by
    have r26987 := hand1 (x (-1) 1) (x (-1) 14)
    have b26988 := hb (x (-1) 1)
    have b26989 := hb (x (-1) 1 && x (-1) 14)
    clear * - r26987 b26988 b26989 d26982
    omega
  have d26990 : (x (-1) 13).toNat = 0 := by
    have r26991 : (x (-1) 13).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp13 (-1))
    have b26992 := hb (x (-1) 1)
    have b26993 := hb (x (-1) 13)
    clear * - r26991 b26992 b26993 d26982
    omega
  have d26994 : (x (-1) 2 && x (-1) 13).toNat = 0 := by
    have r26995 := hand2 (x (-1) 2) (x (-1) 13)
    have b26996 := hb (x (-1) 13)
    have b26997 := hb (x (-1) 2 && x (-1) 13)
    clear * - r26995 b26996 b26997 d26990
    omega
  have d26998 : (x (-2) 2).toNat = 1 := by
    have r26999 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27000 := hb (x (-2) 2)
    have b27001 := hb (x 0 13)
    have b27002 := hb (x (-1) 1 && x (-1) 14)
    clear * - r26999 b27000 b27001 b27002 g3 d26986
    omega
  have d27003 : (x (-2) 14).toNat = 1 := by
    have r27004 : (x (-2) 2).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp2 (-2))
    have b27005 := hb (x (-2) 2)
    have b27006 := hb (x (-2) 14)
    clear * - r27004 b27005 b27006 d26998
    omega
  have d27007 : (x (-3) 1).toNat = 0 := by
    have r27008 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27009 := hb (x (-3) 1)
    have b27010 := hb (x (-2) 14)
    clear * - r27008 b27009 b27010 d27003
    omega
  have d27011 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
    have r27012 := hand1 (x (-3) 1) (x (-3) 14)
    have b27013 := hb (x (-3) 1)
    have b27014 := hb (x (-3) 1 && x (-3) 14)
    clear * - r27012 b27013 b27014 d27007
    omega
  have d27015 : (x (-3) 13).toNat = 0 := by
    have r27016 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
    have b27017 := hb (x (-3) 1)
    have b27018 := hb (x (-3) 13)
    clear * - r27016 b27017 b27018 d27007
    omega
  have d27019 : (x (-3) 2).toNat = 1 := by
    have r27020 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27021 := hb (x (-3) 2)
    have b27022 := hb (x (-1) 13)
    have b27023 := hb (x (-2) 1 && x (-2) 14)
    clear * - r27020 b27021 b27022 b27023 d26990 g15
    omega
  have d27024 : (x (-3) 14).toNat = 1 := by
    have r27025 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
    have b27026 := hb (x (-3) 2)
    have b27027 := hb (x (-3) 14)
    clear * - r27025 b27026 b27027 d27019
    omega
  have d27028 : (x (-4) 1).toNat = 0 := by
    have r27029 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27030 := hb (x (-4) 1)
    have b27031 := hb (x (-3) 14)
    clear * - r27029 b27030 b27031 d27024
    omega
  have d27032 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
    have r27033 := hand1 (x (-4) 1) (x (-4) 14)
    have b27034 := hb (x (-4) 1)
    have b27035 := hb (x (-4) 1 && x (-4) 14)
    clear * - r27033 b27034 b27035 d27028
    omega
  have d27036 : (x (-4) 13).toNat = 0 := by
    have r27037 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
    have b27038 := hb (x (-4) 1)
    have b27039 := hb (x (-4) 13)
    clear * - r27037 b27038 b27039 d27028
    omega
  have d27040 : (x (-4) 2).toNat = 1 := by
    have r27041 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27042 := hb (x (-4) 2)
    have b27043 := hb (x (-2) 13)
    have b27044 := hb (x (-3) 1 && x (-3) 14)
    clear * - r27041 b27042 b27043 b27044 g0 d27011
    omega
  have d27045 : (x (-5) 2).toNat = 1 := by
    have r27046 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27047 := hb (x (-5) 2)
    have b27048 := hb (x (-3) 13)
    have b27049 := hb (x (-4) 1 && x (-4) 14)
    clear * - r27046 b27047 b27048 b27049 d27015 d27032
    omega
  have d27050 : (x (-1) 12).toNat = 0 := by
    have r27051 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27052 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e27053 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b27054 := hb (x (-4) 3)
    have b27055 := hb (x (-3) 2)
    have b27056 := hb (x (-2) 13)
    have b27057 := hb (x (-1) 12)
    clear * - r27051 e27052 e27053 b27054 b27055 b27056 b27057 g0 d27019
    omega
  have d27058 : (x (-1) 4).toNat = 0 := by
    have r27059 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
    have b27060 := hb (x (-1) 4)
    have b27061 := hb (x (-1) 12)
    clear * - r27059 b27060 b27061 d27050
    omega
  have d27062 : (x (-2) 12).toNat = 0 := by
    have r27063 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27064 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
    have e27065 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
    have b27066 := hb (x (-5) 3)
    have b27067 := hb (x (-4) 2)
    have b27068 := hb (x (-3) 13)
    have b27069 := hb (x (-2) 12)
    clear * - r27063 e27064 e27065 b27066 b27067 b27068 b27069 d27015 d27040
    omega
  have d27070 : (x (-2) 4).toNat = 0 := by
    have r27071 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
    have b27072 := hb (x (-2) 4)
    have b27073 := hb (x (-2) 12)
    clear * - r27071 b27072 b27073 d27062
    omega
  have d27074 : (x (-3) 12).toNat = 0 := by
    have r27075 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27076 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
    have e27077 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
    have b27078 := hb (x (-6) 3)
    have b27079 := hb (x (-5) 2)
    have b27080 := hb (x (-4) 13)
    have b27081 := hb (x (-3) 12)
    clear * - r27075 e27076 e27077 b27078 b27079 b27080 b27081 d27036 d27045
    omega
  have d27082 : (x (-3) 4).toNat = 0 := by
    have r27083 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
    have b27084 := hb (x (-3) 4)
    have b27085 := hb (x (-3) 12)
    clear * - r27083 b27084 b27085 d27074
    omega
  have d27086 : (x 1 11).toNat = 1 := by
    have r27087 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27088 := hb (x (-3) 4)
    have b27089 := hb (x 1 11)
    have b27090 := hb (x 0 1 && x 0 12)
    have b27091 := hb (x (-1) 2 && x (-1) 13)
    have b27092 := hb (x (-2) 3 && x (-2) 14)
    clear * - r27087 b27088 b27089 b27090 b27091 b27092 g8 d26994 g9 d27082
    omega
  have d27093 : (x 1 3).toNat = 1 := by
    have r27094 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
    have b27095 := hb (x 1 3)
    have b27096 := hb (x 1 11)
    clear * - r27094 b27095 b27096 d27086
    omega
  have d27097 : (x 4 12).toNat = 0 := by
    have r27098 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27099 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e27100 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b27101 := hb (x 1 3)
    have b27102 := hb (x 2 2)
    have b27103 := hb (x 3 13)
    have b27104 := hb (x 4 12)
    clear * - r27098 e27099 e27100 b27101 b27102 b27103 b27104 d27093
    omega
  have d27105 : (x 4 1 && x 4 12).toNat = 0 := by
    have r27106 := hand2 (x 4 1) (x 4 12)
    have b27107 := hb (x 4 12)
    have b27108 := hb (x 4 1 && x 4 12)
    clear * - r27106 b27107 b27108 d27097
    omega
  have d27109 : (x 4 4).toNat = 0 := by
    have r27110 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
    have b27111 := hb (x 4 4)
    have b27112 := hb (x 4 12)
    clear * - r27110 b27111 b27112 d27097
    omega
  have d27113 : (x 3 13).toNat = 0 := by
    have r27114 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27115 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e27116 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b27117 := hb (x 1 3)
    have b27118 := hb (x 2 2)
    have b27119 := hb (x 3 13)
    have b27120 := hb (x 4 12)
    clear * - r27114 e27115 e27116 b27117 b27118 b27119 b27120 d27097 d27093
    omega
  have d27121 : (x 2 2).toNat = 0 := by
    have r27122 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27123 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e27124 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b27125 := hb (x 1 3)
    have b27126 := hb (x 2 2)
    have b27127 := hb (x 3 13)
    have b27128 := hb (x 4 12)
    clear * - r27122 e27123 e27124 b27125 b27126 b27127 b27128 d27097 d27113 d27093
    omega
  have d27129 : (x 4 13).toNat = 1 := by
    have r27130 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27131 := hb (x 2 2)
    have b27132 := hb (x 4 13)
    have b27133 := hb (x 3 1 && x 3 14)
    clear * - r27130 b27131 b27132 b27133 g16 d27121
    omega
  have d27134 : (x 4 1).toNat = 1 := by
    have r27135 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
    have b27136 := hb (x 4 1)
    have b27137 := hb (x 4 13)
    clear * - r27135 b27136 b27137 d27129
    omega
  have d27138 : (x 5 14).toNat = 0 := by
    have r27139 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27140 := hb (x 4 1)
    have b27141 := hb (x 5 14)
    clear * - r27139 b27140 b27141 d27134
    omega
  have d27142 : (x 5 1 && x 5 14).toNat = 0 := by
    have r27143 := hand2 (x 5 1) (x 5 14)
    have b27144 := hb (x 5 14)
    have b27145 := hb (x 5 1 && x 5 14)
    clear * - r27143 b27144 b27145 d27138
    omega
  have d27146 : (x 5 3 && x 5 14).toNat = 0 := by
    have r27147 := hand2 (x 5 3) (x 5 14)
    have b27148 := hb (x 5 14)
    have b27149 := hb (x 5 3 && x 5 14)
    clear * - r27147 b27148 b27149 d27138
    omega
  have d27150 : (x 5 2).toNat = 0 := by
    have r27151 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
    have b27152 := hb (x 5 2)
    have b27153 := hb (x 5 14)
    clear * - r27151 b27152 b27153 d27138
    omega
  have d27154 : (x 5 2 && x 5 13).toNat = 0 := by
    have r27155 := hand1 (x 5 2) (x 5 13)
    have b27156 := hb (x 5 2)
    have b27157 := hb (x 5 2 && x 5 13)
    clear * - r27155 b27156 b27157 d27150
    omega
  have d27158 : (x 5 12).toNat = 0 := by
    have r27159 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27160 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e27161 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b27162 := hb (x 2 3)
    have b27163 := hb (x 3 2)
    have b27164 := hb (x 4 13)
    have b27165 := hb (x 5 12)
    clear * - r27159 e27160 e27161 b27162 b27163 b27164 b27165 d27129 g6
    omega
  have d27166 : (x 5 4).toNat = 0 := by
    have r27167 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
    have b27168 := hb (x 5 4)
    have b27169 := hb (x 5 12)
    clear * - r27167 b27168 b27169 d27158
    omega
  have d27170 : (x 2 3).toNat = 0 := by
    have r27171 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27172 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e27173 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b27174 := hb (x 2 3)
    have b27175 := hb (x 3 2)
    have b27176 := hb (x 4 13)
    have b27177 := hb (x 5 12)
    clear * - r27171 e27172 e27173 b27174 b27175 b27176 b27177 d27158 d27129 g6
    omega
  have d27178 : (x 2 3 && x 2 14).toNat = 0 := by
    have r27179 := hand1 (x 2 3) (x 2 14)
    have b27180 := hb (x 2 3)
    have b27181 := hb (x 2 3 && x 2 14)
    clear * - r27179 b27180 b27181 d27170
    omega
  have d27182 : (x 5 11).toNat = 1 := by
    have r27183 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27184 := hb (x 1 4)
    have b27185 := hb (x 5 11)
    have b27186 := hb (x 4 1 && x 4 12)
    have b27187 := hb (x 3 2 && x 3 13)
    have b27188 := hb (x 2 3 && x 2 14)
    clear * - r27183 b27184 b27185 b27186 b27187 b27188 d27105 g14 d27178 g4
    omega
  have d27189 : (x 5 3).toNat = 1 := by
    have r27190 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
    have b27191 := hb (x 5 3)
    have b27192 := hb (x 5 11)
    clear * - r27190 b27191 b27192 d27182
    omega
  have d27193 : (x 8 12).toNat = 0 := by
    have r27194 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27195 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e27196 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b27197 := hb (x 5 3)
    have b27198 := hb (x 6 2)
    have b27199 := hb (x 7 13)
    have b27200 := hb (x 8 12)
    clear * - r27194 e27195 e27196 b27197 b27198 b27199 b27200 d27189
    omega
  have d27201 : (x 8 1 && x 8 12).toNat = 0 := by
    have r27202 := hand2 (x 8 1) (x 8 12)
    have b27203 := hb (x 8 12)
    have b27204 := hb (x 8 1 && x 8 12)
    clear * - r27202 b27203 b27204 d27193
    omega
  have d27205 : (x 7 13).toNat = 0 := by
    have r27206 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27207 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e27208 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b27209 := hb (x 5 3)
    have b27210 := hb (x 6 2)
    have b27211 := hb (x 7 13)
    have b27212 := hb (x 8 12)
    clear * - r27206 e27207 e27208 b27209 b27210 b27211 b27212 d27193 d27189
    omega
  have d27213 : (x 7 2 && x 7 13).toNat = 0 := by
    have r27214 := hand2 (x 7 2) (x 7 13)
    have b27215 := hb (x 7 13)
    have b27216 := hb (x 7 2 && x 7 13)
    clear * - r27214 b27215 b27216 d27205
    omega
  have d27217 : (x 6 1 && x 6 14).toNat = 1 := by
    have r27218 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27219 := hb (x 5 2)
    have b27220 := hb (x 7 13)
    have b27221 := hb (x 6 1 && x 6 14)
    clear * - r27218 b27219 b27220 b27221 d27205 d27150
    omega
  have d27222 : (x 6 14).toNat = 1 := by
    have r27223 := hand2 (x 6 1) (x 6 14)
    have b27224 := hb (x 6 14)
    have b27225 := hb (x 6 1 && x 6 14)
    clear * - r27223 b27224 b27225 d27217
    omega
  have d27226 : (x 5 1).toNat = 0 := by
    have r27227 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27228 := hb (x 5 1)
    have b27229 := hb (x 6 14)
    clear * - r27227 b27228 b27229 d27222
    omega
  have d27230 : (x 5 13).toNat = 0 := by
    have r27231 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
    have b27232 := hb (x 5 1)
    have b27233 := hb (x 5 13)
    clear * - r27231 b27232 b27233 d27226
    omega
  have d27234 : (x 6 1).toNat = 1 := by
    have r27235 := hand1 (x 6 1) (x 6 14)
    have b27236 := hb (x 6 1)
    have b27237 := hb (x 6 1 && x 6 14)
    clear * - r27235 b27236 b27237 d27217
    omega
  have d27238 : (x 7 14).toNat = 0 := by
    have r27239 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27240 := hb (x 6 1)
    have b27241 := hb (x 7 14)
    clear * - r27239 b27240 b27241 d27234
    omega
  have d27242 : (x 7 1 && x 7 14).toNat = 0 := by
    have r27243 := hand2 (x 7 1) (x 7 14)
    have b27244 := hb (x 7 14)
    have b27245 := hb (x 7 1 && x 7 14)
    clear * - r27243 b27244 b27245 d27238
    omega
  have d27246 : (x 7 2).toNat = 0 := by
    have r27247 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
    have b27248 := hb (x 7 2)
    have b27249 := hb (x 7 14)
    clear * - r27247 b27248 b27249 d27238
    omega
  have d27250 : (x 6 2).toNat = 0 := by
    have r27251 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27252 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e27253 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b27254 := hb (x 5 3)
    have b27255 := hb (x 6 2)
    have b27256 := hb (x 7 13)
    have b27257 := hb (x 8 12)
    clear * - r27251 e27252 e27253 b27254 b27255 b27256 b27257 d27193 d27205 d27189
    omega
  have d27258 : (x 6 2 && x 6 13).toNat = 0 := by
    have r27259 := hand1 (x 6 2) (x 6 13)
    have b27260 := hb (x 6 2)
    have b27261 := hb (x 6 2 && x 6 13)
    clear * - r27259 b27260 b27261 d27250
    omega
  have d27262 : (x 8 13).toNat = 1 := by
    have r27263 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27264 := hb (x 6 2)
    have b27265 := hb (x 8 13)
    have b27266 := hb (x 7 1 && x 7 14)
    clear * - r27263 b27264 b27265 b27266 d27242 d27250
    omega
  have d27267 : (x 8 1).toNat = 1 := by
    have r27268 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
    have b27269 := hb (x 8 1)
    have b27270 := hb (x 8 13)
    clear * - r27268 b27269 b27270 d27262
    omega
  have d27271 : (x 9 14).toNat = 0 := by
    have r27272 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27273 := hb (x 8 1)
    have b27274 := hb (x 9 14)
    clear * - r27272 b27273 b27274 d27267
    omega
  have d27275 : (x 9 1 && x 9 14).toNat = 0 := by
    have r27276 := hand2 (x 9 1) (x 9 14)
    have b27277 := hb (x 9 14)
    have b27278 := hb (x 9 1 && x 9 14)
    clear * - r27276 b27277 b27278 d27271
    omega
  have d27279 : (x 9 2).toNat = 0 := by
    have r27280 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
    have b27281 := hb (x 9 2)
    have b27282 := hb (x 9 14)
    clear * - r27280 b27281 b27282 d27271
    omega
  have d27283 : (x 9 12).toNat = 0 := by
    have r27284 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27285 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e27286 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b27287 := hb (x 6 3)
    have b27288 := hb (x 7 2)
    have b27289 := hb (x 8 13)
    have b27290 := hb (x 9 12)
    clear * - r27284 e27285 e27286 b27287 b27288 b27289 b27290 d27262 d27246
    omega
  have d27291 : (x 6 3).toNat = 0 := by
    have r27292 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27293 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e27294 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b27295 := hb (x 6 3)
    have b27296 := hb (x 7 2)
    have b27297 := hb (x 8 13)
    have b27298 := hb (x 9 12)
    clear * - r27292 e27293 e27294 b27295 b27296 b27297 b27298 d27283 d27262 d27246
    omega
  have d27299 : (x 6 3 && x 6 14).toNat = 0 := by
    have r27300 := hand1 (x 6 3) (x 6 14)
    have b27301 := hb (x 6 3)
    have b27302 := hb (x 6 3 && x 6 14)
    clear * - r27300 b27301 b27302 d27291
    omega
  have d27303 : (x 9 11).toNat = 1 := by
    have r27304 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27305 := hb (x 5 4)
    have b27306 := hb (x 9 11)
    have b27307 := hb (x 8 1 && x 8 12)
    have b27308 := hb (x 7 2 && x 7 13)
    have b27309 := hb (x 6 3 && x 6 14)
    clear * - r27304 b27305 b27306 b27307 b27308 b27309 d27201 d27213 d27299 d27166
    omega
  have d27310 : (x 9 3).toNat = 1 := by
    have r27311 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
    have b27312 := hb (x 9 3)
    have b27313 := hb (x 9 11)
    clear * - r27311 b27312 b27313 d27303
    omega
  have d27314 : (x 12 12).toNat = 0 := by
    have r27315 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27316 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e27317 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b27318 := hb (x 9 3)
    have b27319 := hb (x 10 2)
    have b27320 := hb (x 11 13)
    have b27321 := hb (x 12 12)
    clear * - r27315 e27316 e27317 b27318 b27319 b27320 b27321 d27310
    omega
  have d27322 : (x 11 13).toNat = 0 := by
    have r27323 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27324 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e27325 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b27326 := hb (x 9 3)
    have b27327 := hb (x 10 2)
    have b27328 := hb (x 11 13)
    have b27329 := hb (x 12 12)
    clear * - r27323 e27324 e27325 b27326 b27327 b27328 b27329 d27314 d27310
    omega
  have d27330 : (x 10 1 && x 10 14).toNat = 1 := by
    have r27331 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27332 := hb (x 9 2)
    have b27333 := hb (x 11 13)
    have b27334 := hb (x 10 1 && x 10 14)
    clear * - r27331 b27332 b27333 b27334 d27322 d27279
    omega
  have d27335 : (x 10 14).toNat = 1 := by
    have r27336 := hand2 (x 10 1) (x 10 14)
    have b27337 := hb (x 10 14)
    have b27338 := hb (x 10 1 && x 10 14)
    clear * - r27336 b27337 b27338 d27330
    omega
  have d27339 : (x 9 1).toNat = 0 := by
    have r27340 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27341 := hb (x 9 1)
    have b27342 := hb (x 10 14)
    clear * - r27340 b27341 b27342 d27335
    omega
  have d27343 : (x 9 13).toNat = 0 := by
    have r27344 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
    have b27345 := hb (x 9 1)
    have b27346 := hb (x 9 13)
    clear * - r27344 b27345 b27346 d27339
    omega
  have d27347 : (x 8 1 && x 8 14).toNat = 1 := by
    have r27348 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27349 := hb (x 7 2)
    have b27350 := hb (x 9 13)
    have b27351 := hb (x 8 1 && x 8 14)
    clear * - r27348 b27349 b27350 b27351 d27343 d27246
    omega
  have d27352 : (x 8 14).toNat = 1 := by
    have r27353 := hand2 (x 8 1) (x 8 14)
    have b27354 := hb (x 8 14)
    have b27355 := hb (x 8 1 && x 8 14)
    clear * - r27353 b27354 b27355 d27347
    omega
  have d27356 : (x 7 1).toNat = 0 := by
    have r27357 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27358 := hb (x 7 1)
    have b27359 := hb (x 8 14)
    clear * - r27357 b27358 b27359 d27352
    omega
  have d27360 : (x 7 1 && x 7 12).toNat = 0 := by
    have r27361 := hand1 (x 7 1) (x 7 12)
    have b27362 := hb (x 7 1)
    have b27363 := hb (x 7 1 && x 7 12)
    clear * - r27361 b27362 b27363 d27356
    omega
  have d27364 : (x 8 11).toNat = 1 := by
    have r27365 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27366 := hb (x 4 4)
    have b27367 := hb (x 8 11)
    have b27368 := hb (x 7 1 && x 7 12)
    have b27369 := hb (x 6 2 && x 6 13)
    have b27370 := hb (x 5 3 && x 5 14)
    clear * - r27365 b27366 b27367 b27368 b27369 b27370 d27360 d27258 d27146 d27109
    omega
  have d27371 : (x 8 3).toNat = 1 := by
    have r27372 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
    have b27373 := hb (x 8 3)
    have b27374 := hb (x 8 11)
    clear * - r27372 b27373 b27374 d27364
    omega
  have d27375 : (x 11 12).toNat = 0 := by
    have r27376 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27377 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e27378 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b27379 := hb (x 8 3)
    have b27380 := hb (x 9 2)
    have b27381 := hb (x 10 13)
    have b27382 := hb (x 11 12)
    clear * - r27376 e27377 e27378 b27379 b27380 b27381 b27382 d27279 d27371
    omega
  have d27383 : (x 10 13).toNat = 0 := by
    have r27384 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27385 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e27386 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b27387 := hb (x 8 3)
    have b27388 := hb (x 9 2)
    have b27389 := hb (x 10 13)
    have b27390 := hb (x 11 12)
    clear * - r27384 e27385 e27386 b27387 b27388 b27389 b27390 d27375 d27279 d27371
    omega
  have d27391 : (x 8 2).toNat = 1 := by
    have r27392 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27393 := hb (x 8 2)
    have b27394 := hb (x 10 13)
    have b27395 := hb (x 9 1 && x 9 14)
    clear * - r27392 b27393 b27394 b27395 d27383 d27275
    omega
  have d27396 : (x 10 12).toNat = 0 := by
    have r27397 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27398 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e27399 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b27400 := hb (x 7 3)
    have b27401 := hb (x 8 2)
    have b27402 := hb (x 9 13)
    have b27403 := hb (x 10 12)
    clear * - r27397 e27398 e27399 b27400 b27401 b27402 b27403 d27343 d27391
    omega
  have d27404 : (x 7 3).toNat = 0 := by
    have r27405 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27406 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e27407 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b27408 := hb (x 7 3)
    have b27409 := hb (x 8 2)
    have b27410 := hb (x 9 13)
    have b27411 := hb (x 10 12)
    clear * - r27405 e27406 e27407 b27408 b27409 b27410 b27411 d27396 d27343 d27391
    omega
  have d27412 : (x 7 11).toNat = 0 := by
    have r27413 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
    have b27414 := hb (x 7 3)
    have b27415 := hb (x 7 11)
    clear * - r27413 b27414 b27415 d27404
    omega
  have d27416 : (x 2 11).toNat = 0 := by
    have r27417 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
    have b27418 := hb (x 2 3)
    have b27419 := hb (x 2 11)
    clear * - r27417 b27418 b27419 d27170
    omega
  have d27420 : (x (-1) 3 && x (-1) 14).toNat = 1 := by
    have r27421 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := by have q := hcov11 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27422 := hb (x (-2) 4)
    have b27423 := hb (x 2 11)
    have b27424 := hb (x 1 1 && x 1 12)
    have b27425 := hb (x 0 2 && x 0 13)
    have b27426 := hb (x (-1) 3 && x (-1) 14)
    clear * - r27421 b27422 b27423 b27424 b27425 b27426 d27416 g10 g11 d27070
    omega
  have d27427 : (x (-1) 3).toNat = 1 := by
    have r27428 := hand1 (x (-1) 3) (x (-1) 14)
    have b27429 := hb (x (-1) 3)
    have b27430 := hb (x (-1) 3 && x (-1) 14)
    clear * - r27428 b27429 b27430 d27420
    omega
  have d27431 : (x 2 12).toNat = 0 := by
    have r27432 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27433 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e27434 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b27435 := hb (x (-1) 3)
    have b27436 := hb (x 0 2)
    have b27437 := hb (x 1 13)
    have b27438 := hb (x 2 12)
    clear * - r27432 e27433 e27434 b27435 b27436 b27437 b27438 g5 g1 d27427
    omega
  have d27439 : (x 2 1 && x 2 12).toNat = 0 := by
    have r27440 := hand2 (x 2 1) (x 2 12)
    have b27441 := hb (x 2 12)
    have b27442 := hb (x 2 1 && x 2 12)
    clear * - r27440 b27441 b27442 d27431
    omega
  have d27443 : (x 3 11).toNat = 1 := by
    have r27444 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27445 := hb (x (-1) 4)
    have b27446 := hb (x 3 11)
    have b27447 := hb (x 2 1 && x 2 12)
    have b27448 := hb (x 1 2 && x 1 13)
    have b27449 := hb (x 0 3 && x 0 14)
    clear * - r27444 b27445 b27446 b27447 b27448 b27449 d27439 g12 g13 d27058
    omega
  have d27450 : (x 3 3).toNat = 1 := by
    have r27451 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
    have b27452 := hb (x 3 3)
    have b27453 := hb (x 3 11)
    clear * - r27451 b27452 b27453 d27443
    omega
  have d27454 : (x 6 12).toNat = 0 := by
    have r27455 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27456 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e27457 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b27458 := hb (x 3 3)
    have b27459 := hb (x 4 2)
    have b27460 := hb (x 5 13)
    have b27461 := hb (x 6 12)
    clear * - r27455 e27456 e27457 b27458 b27459 b27460 b27461 d27230 d27450
    omega
  have d27462 : (x 6 1 && x 6 12).toNat = 0 := by
    have r27463 := hand2 (x 6 1) (x 6 12)
    have b27464 := hb (x 6 12)
    have b27465 := hb (x 6 1 && x 6 12)
    clear * - r27463 b27464 b27465 d27454
    omega
  have d27466 : (x 4 3 && x 4 14).toNat = 1 := by
    have r27467 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27468 := hb (x 3 4)
    have b27469 := hb (x 7 11)
    have b27470 := hb (x 6 1 && x 6 12)
    have b27471 := hb (x 5 2 && x 5 13)
    have b27472 := hb (x 4 3 && x 4 14)
    clear * - r27467 b27468 b27469 b27470 b27471 b27472 d27412 d27462 d27154 g7
    omega
  have d27473 : (x 4 3).toNat = 1 := by
    have r27474 := hand1 (x 4 3) (x 4 14)
    have b27475 := hb (x 4 3)
    have b27476 := hb (x 4 3 && x 4 14)
    clear * - r27474 b27475 b27476 d27466
    omega
  have d27477 : (x 7 12).toNat = 0 := by
    have r27478 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27479 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e27480 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b27481 := hb (x 4 3)
    have b27482 := hb (x 5 2)
    have b27483 := hb (x 6 13)
    have b27484 := hb (x 7 12)
    clear * - r27478 e27479 e27480 b27481 b27482 b27483 b27484 d27150 d27473
    omega
  have d27485 : (x 6 13).toNat = 0 := by
    have r27486 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27487 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e27488 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b27489 := hb (x 4 3)
    have b27490 := hb (x 5 2)
    have b27491 := hb (x 6 13)
    have b27492 := hb (x 7 12)
    clear * - r27486 e27487 e27488 b27489 b27490 b27491 b27492 d27477 d27150 d27473
    omega
  have d27493 : (x 4 2).toNat = 1 := by
    have r27494 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27495 := hb (x 4 2)
    have b27496 := hb (x 6 13)
    have b27497 := hb (x 5 1 && x 5 14)
    clear * - r27494 b27495 b27496 b27497 d27485 d27142
    omega
  have r27498 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e27499 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
  have e27500 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
  have b27501 := hb (x 3 3)
  have b27502 := hb (x 4 2)
  have b27503 := hb (x 5 13)
  have b27504 := hb (x 6 12)
  linarith only [r27498, e27499, e27500, b27501, b27502, b27503, b27504, d27454, d27230, d27493, d27450]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00011 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-4) 4).toNat = 0)
    (g1 : (x (-2) 13).toNat = 0)
    (g2 : (x 0 4).toNat = 1)
    (g3 : (x 0 11).toNat = 0)
    (g4 : (x (-2) 2 && x (-2) 13).toNat = 0)
    (g5 : (x (-2) 1 && x (-2) 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d27506 : (x 0 12).toNat = 1 := by
    have r27507 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
    have b27508 := hb (x 0 4)
    have b27509 := hb (x 0 12)
    clear * - r27507 b27508 b27509 g2
    omega
  have d27510 : (x (-1) 13).toNat = 0 := by
    have r27511 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27512 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e27513 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b27514 := hb (x (-3) 3)
    have b27515 := hb (x (-2) 2)
    have b27516 := hb (x (-1) 13)
    have b27517 := hb (x 0 12)
    clear * - r27511 e27512 e27513 b27514 b27515 b27516 b27517 d27506
    omega
  have d27518 : (x (-3) 2).toNat = 1 := by
    have r27519 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27520 := hb (x (-3) 2)
    have b27521 := hb (x (-1) 13)
    have b27522 := hb (x (-2) 1 && x (-2) 14)
    clear * - r27519 b27520 b27521 b27522 d27510 g5
    omega
  have d27523 : (x (-2) 2).toNat = 0 := by
    have r27524 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27525 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e27526 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b27527 := hb (x (-3) 3)
    have b27528 := hb (x (-2) 2)
    have b27529 := hb (x (-1) 13)
    have b27530 := hb (x 0 12)
    clear * - r27524 e27525 e27526 b27527 b27528 b27529 b27530 d27506 d27510
    omega
  have d27531 : (x (-3) 3).toNat = 0 := by
    have r27532 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27533 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e27534 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b27535 := hb (x (-3) 3)
    have b27536 := hb (x (-2) 2)
    have b27537 := hb (x (-1) 13)
    have b27538 := hb (x 0 12)
    clear * - r27532 e27533 e27534 b27535 b27536 b27537 b27538 d27506 d27510 d27523
    omega
  have d27539 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
    have r27540 := hand1 (x (-3) 3) (x (-3) 14)
    have b27541 := hb (x (-3) 3)
    have b27542 := hb (x (-3) 3 && x (-3) 14)
    clear * - r27540 b27541 b27542 d27531
    omega
  have d27543 : (x (-1) 12).toNat = 0 := by
    have r27544 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27545 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e27546 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b27547 := hb (x (-4) 3)
    have b27548 := hb (x (-3) 2)
    have b27549 := hb (x (-2) 13)
    have b27550 := hb (x (-1) 12)
    clear * - r27544 e27545 e27546 b27547 b27548 b27549 b27550 g1 d27518
    omega
  have d27551 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
    have r27552 := hand2 (x (-1) 1) (x (-1) 12)
    have b27553 := hb (x (-1) 12)
    have b27554 := hb (x (-1) 1 && x (-1) 12)
    clear * - r27552 b27553 b27554 d27543
    omega
  have r27555 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have b27556 := hb (x (-4) 4)
  have b27557 := hb (x 0 11)
  have b27558 := hb (x (-1) 1 && x (-1) 12)
  have b27559 := hb (x (-2) 2 && x (-2) 13)
  have b27560 := hb (x (-3) 3 && x (-3) 14)
  linarith only [r27555, b27556, b27557, b27558, b27559, b27560, g3, d27551, g4, d27539, g0]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt001_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-2) 13).toNat = 0)
    (g1 : (x 0 2).toNat = 1)
    (g2 : (x 0 13).toNat = 0)
    (g3 : (x 1 13).toNat = 0)
    (g4 : (x 0 1 && x 0 12).toNat = 0)
    (g5 : (x (-2) 3 && x (-2) 14).toNat = 0)
    (g6 : (x 1 1 && x 1 12).toNat = 0)
    (g7 : (x 0 2 && x 0 13).toNat = 0)
    (g8 : (x 1 2 && x 1 13).toNat = 0)
    (g9 : (x (-2) 1 && x (-2) 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d27562 : (x 0 14).toNat = 1 := by
    have r27563 : (x 0 2).toNat ≤ (x 0 14).toNat := himp _ _ (hp2 0)
    have b27564 := hb (x 0 2)
    have b27565 := hb (x 0 14)
    clear * - r27563 b27564 b27565 g1
    omega
  have d27566 : (x (-1) 1).toNat = 0 := by
    have r27567 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27568 := hb (x (-1) 1)
    have b27569 := hb (x 0 14)
    clear * - r27567 b27568 b27569 d27562
    omega
  have d27570 : (x (-1) 1 && x (-1) 14).toNat = 0 := by
    have r27571 := hand1 (x (-1) 1) (x (-1) 14)
    have b27572 := hb (x (-1) 1)
    have b27573 := hb (x (-1) 1 && x (-1) 14)
    clear * - r27571 b27572 b27573 d27566
    omega
  have d27574 : (x (-1) 13).toNat = 0 := by
    have r27575 : (x (-1) 13).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp13 (-1))
    have b27576 := hb (x (-1) 1)
    have b27577 := hb (x (-1) 13)
    clear * - r27575 b27576 b27577 d27566
    omega
  have d27578 : (x (-1) 2 && x (-1) 13).toNat = 0 := by
    have r27579 := hand2 (x (-1) 2) (x (-1) 13)
    have b27580 := hb (x (-1) 13)
    have b27581 := hb (x (-1) 2 && x (-1) 13)
    clear * - r27579 b27580 b27581 d27574
    omega
  have d27582 : (x (-2) 2).toNat = 1 := by
    have r27583 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27584 := hb (x (-2) 2)
    have b27585 := hb (x 0 13)
    have b27586 := hb (x (-1) 1 && x (-1) 14)
    clear * - r27583 b27584 b27585 b27586 g2 d27570
    omega
  have d27587 : (x (-2) 14).toNat = 1 := by
    have r27588 : (x (-2) 2).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp2 (-2))
    have b27589 := hb (x (-2) 2)
    have b27590 := hb (x (-2) 14)
    clear * - r27588 b27589 b27590 d27582
    omega
  have d27591 : (x (-3) 1).toNat = 0 := by
    have r27592 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27593 := hb (x (-3) 1)
    have b27594 := hb (x (-2) 14)
    clear * - r27592 b27593 b27594 d27587
    omega
  have d27595 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
    have r27596 := hand1 (x (-3) 1) (x (-3) 14)
    have b27597 := hb (x (-3) 1)
    have b27598 := hb (x (-3) 1 && x (-3) 14)
    clear * - r27596 b27597 b27598 d27591
    omega
  have d27599 : (x (-3) 13).toNat = 0 := by
    have r27600 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
    have b27601 := hb (x (-3) 1)
    have b27602 := hb (x (-3) 13)
    clear * - r27600 b27601 b27602 d27591
    omega
  have d27603 : (x (-3) 2).toNat = 1 := by
    have r27604 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27605 := hb (x (-3) 2)
    have b27606 := hb (x (-1) 13)
    have b27607 := hb (x (-2) 1 && x (-2) 14)
    clear * - r27604 b27605 b27606 b27607 d27574 g9
    omega
  have d27608 : (x (-3) 14).toNat = 1 := by
    have r27609 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
    have b27610 := hb (x (-3) 2)
    have b27611 := hb (x (-3) 14)
    clear * - r27609 b27610 b27611 d27603
    omega
  have d27612 : (x (-4) 1).toNat = 0 := by
    have r27613 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27614 := hb (x (-4) 1)
    have b27615 := hb (x (-3) 14)
    clear * - r27613 b27614 b27615 d27608
    omega
  have d27616 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
    have r27617 := hand1 (x (-4) 1) (x (-4) 14)
    have b27618 := hb (x (-4) 1)
    have b27619 := hb (x (-4) 1 && x (-4) 14)
    clear * - r27617 b27618 b27619 d27612
    omega
  have d27620 : (x (-4) 13).toNat = 0 := by
    have r27621 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
    have b27622 := hb (x (-4) 1)
    have b27623 := hb (x (-4) 13)
    clear * - r27621 b27622 b27623 d27612
    omega
  have d27624 : (x (-4) 2).toNat = 1 := by
    have r27625 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27626 := hb (x (-4) 2)
    have b27627 := hb (x (-2) 13)
    have b27628 := hb (x (-3) 1 && x (-3) 14)
    clear * - r27625 b27626 b27627 b27628 g0 d27595
    omega
  have d27629 : (x (-5) 2).toNat = 1 := by
    have r27630 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27631 := hb (x (-5) 2)
    have b27632 := hb (x (-3) 13)
    have b27633 := hb (x (-4) 1 && x (-4) 14)
    clear * - r27630 b27631 b27632 b27633 d27599 d27616
    omega
  have d27634 : (x 2 12).toNat = 0 := by
    have r27635 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27636 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e27637 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b27638 := hb (x (-1) 3)
    have b27639 := hb (x 0 2)
    have b27640 := hb (x 1 13)
    have b27641 := hb (x 2 12)
    clear * - r27635 e27636 e27637 b27638 b27639 b27640 b27641 g3 g1
    omega
  have d27642 : (x 2 1 && x 2 12).toNat = 0 := by
    have r27643 := hand2 (x 2 1) (x 2 12)
    have b27644 := hb (x 2 12)
    have b27645 := hb (x 2 1 && x 2 12)
    clear * - r27643 b27644 b27645 d27634
    omega
  have d27646 : (x (-1) 3).toNat = 0 := by
    have r27647 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27648 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e27649 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b27650 := hb (x (-1) 3)
    have b27651 := hb (x 0 2)
    have b27652 := hb (x 1 13)
    have b27653 := hb (x 2 12)
    clear * - r27647 e27648 e27649 b27650 b27651 b27652 b27653 d27634 g3 g1
    omega
  have d27654 : (x (-1) 3 && x (-1) 14).toNat = 0 := by
    have r27655 := hand1 (x (-1) 3) (x (-1) 14)
    have b27656 := hb (x (-1) 3)
    have b27657 := hb (x (-1) 3 && x (-1) 14)
    clear * - r27655 b27656 b27657 d27646
    omega
  have d27658 : (x (-1) 12).toNat = 0 := by
    have r27659 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27660 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e27661 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b27662 := hb (x (-4) 3)
    have b27663 := hb (x (-3) 2)
    have b27664 := hb (x (-2) 13)
    have b27665 := hb (x (-1) 12)
    clear * - r27659 e27660 e27661 b27662 b27663 b27664 b27665 g0 d27603
    omega
  have d27666 : (x (-1) 4).toNat = 0 := by
    have r27667 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
    have b27668 := hb (x (-1) 4)
    have b27669 := hb (x (-1) 12)
    clear * - r27667 b27668 b27669 d27658
    omega
  have d27670 : (x (-2) 12).toNat = 0 := by
    have r27671 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27672 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
    have e27673 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
    have b27674 := hb (x (-5) 3)
    have b27675 := hb (x (-4) 2)
    have b27676 := hb (x (-3) 13)
    have b27677 := hb (x (-2) 12)
    clear * - r27671 e27672 e27673 b27674 b27675 b27676 b27677 d27599 d27624
    omega
  have d27678 : (x (-2) 4).toNat = 0 := by
    have r27679 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
    have b27680 := hb (x (-2) 4)
    have b27681 := hb (x (-2) 12)
    clear * - r27679 b27680 b27681 d27670
    omega
  have d27682 : (x (-3) 12).toNat = 0 := by
    have r27683 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27684 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
    have e27685 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
    have b27686 := hb (x (-6) 3)
    have b27687 := hb (x (-5) 2)
    have b27688 := hb (x (-4) 13)
    have b27689 := hb (x (-3) 12)
    clear * - r27683 e27684 e27685 b27686 b27687 b27688 b27689 d27620 d27629
    omega
  have d27690 : (x (-3) 4).toNat = 0 := by
    have r27691 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
    have b27692 := hb (x (-3) 4)
    have b27693 := hb (x (-3) 12)
    clear * - r27691 b27692 b27693 d27682
    omega
  have d27694 : (x 2 11).toNat = 1 := by
    have r27695 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := by have q := hcov11 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27696 := hb (x (-2) 4)
    have b27697 := hb (x 2 11)
    have b27698 := hb (x 1 1 && x 1 12)
    have b27699 := hb (x 0 2 && x 0 13)
    have b27700 := hb (x (-1) 3 && x (-1) 14)
    clear * - r27695 b27696 b27697 b27698 b27699 b27700 g6 g7 d27654 d27678
    omega
  have d27701 : (x 2 3).toNat = 1 := by
    have r27702 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
    have b27703 := hb (x 2 3)
    have b27704 := hb (x 2 11)
    clear * - r27702 b27703 b27704 d27694
    omega
  have d27705 : (x 5 12).toNat = 0 := by
    have r27706 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27707 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e27708 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b27709 := hb (x 2 3)
    have b27710 := hb (x 3 2)
    have b27711 := hb (x 4 13)
    have b27712 := hb (x 5 12)
    clear * - r27706 e27707 e27708 b27709 b27710 b27711 b27712 d27701
    omega
  have d27713 : (x 4 13).toNat = 0 := by
    have r27714 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27715 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e27716 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b27717 := hb (x 2 3)
    have b27718 := hb (x 3 2)
    have b27719 := hb (x 4 13)
    have b27720 := hb (x 5 12)
    clear * - r27714 e27715 e27716 b27717 b27718 b27719 b27720 d27705 d27701
    omega
  have d27721 : (x 3 2).toNat = 0 := by
    have r27722 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27723 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e27724 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b27725 := hb (x 2 3)
    have b27726 := hb (x 3 2)
    have b27727 := hb (x 4 13)
    have b27728 := hb (x 5 12)
    clear * - r27722 e27723 e27724 b27725 b27726 b27727 b27728 d27705 d27713 d27701
    omega
  have d27729 : (x 1 11).toNat = 1 := by
    have r27730 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27731 := hb (x (-3) 4)
    have b27732 := hb (x 1 11)
    have b27733 := hb (x 0 1 && x 0 12)
    have b27734 := hb (x (-1) 2 && x (-1) 13)
    have b27735 := hb (x (-2) 3 && x (-2) 14)
    clear * - r27730 b27731 b27732 b27733 b27734 b27735 g4 d27578 g5 d27690
    omega
  have d27736 : (x 1 3).toNat = 1 := by
    have r27737 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
    have b27738 := hb (x 1 3)
    have b27739 := hb (x 1 11)
    clear * - r27737 b27738 b27739 d27729
    omega
  have d27740 : (x 4 12).toNat = 0 := by
    have r27741 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27742 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e27743 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b27744 := hb (x 1 3)
    have b27745 := hb (x 2 2)
    have b27746 := hb (x 3 13)
    have b27747 := hb (x 4 12)
    clear * - r27741 e27742 e27743 b27744 b27745 b27746 b27747 d27736
    omega
  have d27748 : (x 3 13).toNat = 0 := by
    have r27749 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27750 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e27751 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b27752 := hb (x 1 3)
    have b27753 := hb (x 2 2)
    have b27754 := hb (x 3 13)
    have b27755 := hb (x 4 12)
    clear * - r27749 e27750 e27751 b27752 b27753 b27754 b27755 d27740 d27736
    omega
  have d27756 : (x 2 2).toNat = 0 := by
    have r27757 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27758 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e27759 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b27760 := hb (x 1 3)
    have b27761 := hb (x 2 2)
    have b27762 := hb (x 3 13)
    have b27763 := hb (x 4 12)
    clear * - r27757 e27758 e27759 b27760 b27761 b27762 b27763 d27740 d27748 d27736
    omega
  have d27764 : (x 3 1 && x 3 14).toNat = 1 := by
    have r27765 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27766 := hb (x 2 2)
    have b27767 := hb (x 4 13)
    have b27768 := hb (x 3 1 && x 3 14)
    clear * - r27765 b27766 b27767 b27768 d27713 d27756
    omega
  have d27769 : (x 3 14).toNat = 1 := by
    have r27770 := hand2 (x 3 1) (x 3 14)
    have b27771 := hb (x 3 14)
    have b27772 := hb (x 3 1 && x 3 14)
    clear * - r27770 b27771 b27772 d27764
    omega
  have d27773 : (x 2 1).toNat = 0 := by
    have r27774 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27775 := hb (x 2 1)
    have b27776 := hb (x 3 14)
    clear * - r27774 b27775 b27776 d27769
    omega
  have d27777 : (x 2 1 && x 2 14).toNat = 0 := by
    have r27778 := hand1 (x 2 1) (x 2 14)
    have b27779 := hb (x 2 1)
    have b27780 := hb (x 2 1 && x 2 14)
    clear * - r27778 b27779 b27780 d27773
    omega
  have d27781 : (x 1 2).toNat = 1 := by
    have r27782 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27783 := hb (x 1 2)
    have b27784 := hb (x 3 13)
    have b27785 := hb (x 2 1 && x 2 14)
    clear * - r27782 b27783 b27784 b27785 d27748 d27777
    omega
  have d27786 : (x 3 12).toNat = 0 := by
    have r27787 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27788 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e27789 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b27790 := hb (x 0 3)
    have b27791 := hb (x 1 2)
    have b27792 := hb (x 2 13)
    have b27793 := hb (x 3 12)
    clear * - r27787 e27788 e27789 b27790 b27791 b27792 b27793 d27781
    omega
  have d27794 : (x 2 13).toNat = 0 := by
    have r27795 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27796 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e27797 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b27798 := hb (x 0 3)
    have b27799 := hb (x 1 2)
    have b27800 := hb (x 2 13)
    have b27801 := hb (x 3 12)
    clear * - r27795 e27796 e27797 b27798 b27799 b27800 b27801 d27786 d27781
    omega
  have d27802 : (x 0 3).toNat = 0 := by
    have r27803 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27804 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e27805 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b27806 := hb (x 0 3)
    have b27807 := hb (x 1 2)
    have b27808 := hb (x 2 13)
    have b27809 := hb (x 3 12)
    clear * - r27803 e27804 e27805 b27806 b27807 b27808 b27809 d27786 d27794 d27781
    omega
  have d27810 : (x 0 3 && x 0 14).toNat = 0 := by
    have r27811 := hand1 (x 0 3) (x 0 14)
    have b27812 := hb (x 0 3)
    have b27813 := hb (x 0 3 && x 0 14)
    clear * - r27811 b27812 b27813 d27802
    omega
  have d27814 : (x 3 11).toNat = 1 := by
    have r27815 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27816 := hb (x (-1) 4)
    have b27817 := hb (x 3 11)
    have b27818 := hb (x 2 1 && x 2 12)
    have b27819 := hb (x 1 2 && x 1 13)
    have b27820 := hb (x 0 3 && x 0 14)
    clear * - r27815 b27816 b27817 b27818 b27819 b27820 d27642 g8 d27810 d27666
    omega
  have d27821 : (x 3 3).toNat = 1 := by
    have r27822 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
    have b27823 := hb (x 3 3)
    have b27824 := hb (x 3 11)
    clear * - r27822 b27823 b27824 d27814
    omega
  have d27825 : (x 6 12).toNat = 0 := by
    have r27826 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27827 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e27828 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b27829 := hb (x 3 3)
    have b27830 := hb (x 4 2)
    have b27831 := hb (x 5 13)
    have b27832 := hb (x 6 12)
    clear * - r27826 e27827 e27828 b27829 b27830 b27831 b27832 d27821
    omega
  have d27833 : (x 5 13).toNat = 0 := by
    have r27834 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27835 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e27836 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b27837 := hb (x 3 3)
    have b27838 := hb (x 4 2)
    have b27839 := hb (x 5 13)
    have b27840 := hb (x 6 12)
    clear * - r27834 e27835 e27836 b27837 b27838 b27839 b27840 d27825 d27821
    omega
  have d27841 : (x 4 1 && x 4 14).toNat = 1 := by
    have r27842 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27843 := hb (x 3 2)
    have b27844 := hb (x 5 13)
    have b27845 := hb (x 4 1 && x 4 14)
    clear * - r27842 b27843 b27844 b27845 d27833 d27721
    omega
  have d27846 : (x 4 14).toNat = 1 := by
    have r27847 := hand2 (x 4 1) (x 4 14)
    have b27848 := hb (x 4 14)
    have b27849 := hb (x 4 1 && x 4 14)
    clear * - r27847 b27848 b27849 d27841
    omega
  have d27850 : (x 3 1).toNat = 0 := by
    have r27851 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27852 := hb (x 3 1)
    have b27853 := hb (x 4 14)
    clear * - r27851 b27852 b27853 d27846
    omega
  have r27854 := hand1 (x 3 1) (x 3 14)
  have b27855 := hb (x 3 1)
  have b27856 := hb (x 3 1 && x 3 14)
  linarith only [r27854, b27855, b27856, d27764, d27850]

theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-2) 13).toNat = 0)
    (g1 : (x 0 2).toNat = 1)
    (g2 : (x 0 13).toNat = 0)
    (g3 : (x 1 13).toNat = 0)
    (g4 : (x 0 1 && x 0 12).toNat = 0)
    (g5 : (x (-2) 3 && x (-2) 14).toNat = 0)
    (g6 : (x 1 1 && x 1 12).toNat = 0)
    (g7 : (x 0 2 && x 0 13).toNat = 0)
    (g8 : (x 1 2 && x 1 13).toNat = 0)
    (g9 : (x (-2) 1 && x (-2) 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt001_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
