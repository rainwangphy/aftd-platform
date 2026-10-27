import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceTwoIffThreeCoreB0
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceTwoIffThreeCoreB1
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceTwoIffThreeCoreA0000
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceTwoIffThreeCoreA0001000
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceTwoIffThreeCoreA0001001
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceTwoIffThreeCoreA000101
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceTwoIffThreeCoreA00011
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceTwoIffThreeCoreA001
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceTwoIffThreeCoreA01
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceTwoIffThreeCoreA1000000
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceTwoIffThreeCoreA1000001
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceTwoIffThreeCoreA100001
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceTwoIffThreeCoreA10001
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceTwoIffThreeCoreA101
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceTwoIffThreeCoreA1100
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceTwoIffThreeCoreA1101
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceTwoIffThreeCoreA111

/-!
# cycle_power_fifteen_tight_type_sequence_two_iff_three_core

Topic: combinatorics   Node: ce7051d89182

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP; the same generator on the same window refutes x(0,2) != x(0,3) (a case-split tree of 109 + 3 nodes).

Layer-free one_iff_fourteen for tight five-layer covers of C_n^15, on the integer line. Let x p j say that the class starting at p (the class of the distance-15 pair (p, p+15)) contains p + j. Assume every vertex is an inner element (offsets 1..14) of exactly three classes; every pair at distance 14, 12, 8 is covered exactly once; every pair at distance 1..7, 9, 10, 11, 13 is covered; and every class is closed under the parent map of the tight-class forest (2→14, 4→12, 5→13, 6→14, 9→1, 10→2, 11→3, 13→1). Then the class at 0 contains 2 exactly when it contains 3 (a step of the pairing of adjacent class bits behind the six-type classification).
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_two_iff_three_core_aux (x : ℤ → Fin 16 → Bool)
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
    : x 0 2 = x 0 3 := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  cases h01 : x 0 2 <;> cases h014 : x 0 3
  · rfl
  · exfalso
    have g1 : (x 0 2).toNat = 0 := by rw [h01]; rfl
    have g14 : (x 0 3).toNat = 1 := by rw [h014]; rfl
    have d1 : (x 3 12).toNat = 0 := by
      have r2 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e3 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
      have e4 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
      have b5 := hb (x 0 3)
      have b6 := hb (x 1 2)
      have b7 := hb (x 2 13)
      have b8 := hb (x 3 12)
      clear * - r2 e3 e4 b5 b6 b7 b8 g14
      omega
    have d9 : (x 3 1 && x 3 12).toNat = 0 := by
      have r10 := hand2 (x 3 1) (x 3 12)
      have b11 := hb (x 3 12)
      have b12 := hb (x 3 1 && x 3 12)
      clear * - r10 b11 b12 d1
      omega
    have d13 : (x 3 2 && x 3 12).toNat = 0 := by
      have r14 := hand2 (x 3 2) (x 3 12)
      have b15 := hb (x 3 12)
      have b16 := hb (x 3 2 && x 3 12)
      clear * - r14 b15 b16 d1
      omega
    have d17 : (x 3 4).toNat = 0 := by
      have r18 : (x 3 4).toNat ≤ (x 3 12).toNat := himp _ _ (hp4 3)
      have b19 := hb (x 3 4)
      have b20 := hb (x 3 12)
      clear * - r18 b19 b20 d1
      omega
    have d21 : (x 3 4 && x 3 11).toNat = 0 := by
      have r22 := hand1 (x 3 4) (x 3 11)
      have b23 := hb (x 3 4)
      have b24 := hb (x 3 4 && x 3 11)
      clear * - r22 b23 b24 d17
      omega
    have d25 : (x 2 13).toNat = 0 := by
      have r26 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
      have e28 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
      have b29 := hb (x 0 3)
      have b30 := hb (x 1 2)
      have b31 := hb (x 2 13)
      have b32 := hb (x 3 12)
      clear * - r26 e27 e28 b29 b30 b31 b32 d1 g14
      omega
    have d33 : (x 2 2 && x 2 13).toNat = 0 := by
      have r34 := hand2 (x 2 2) (x 2 13)
      have b35 := hb (x 2 13)
      have b36 := hb (x 2 2 && x 2 13)
      clear * - r34 b35 b36 d25
      omega
    have d37 : (x 2 3 && x 2 13).toNat = 0 := by
      have r38 := hand2 (x 2 3) (x 2 13)
      have b39 := hb (x 2 13)
      have b40 := hb (x 2 3 && x 2 13)
      clear * - r38 b39 b40 d25
      omega
    have d41 : (x 2 5).toNat = 0 := by
      have r42 : (x 2 5).toNat ≤ (x 2 13).toNat := himp _ _ (hp5 2)
      have b43 := hb (x 2 5)
      have b44 := hb (x 2 13)
      clear * - r42 b43 b44 d25
      omega
    have d45 : (x 2 5 && x 2 12).toNat = 0 := by
      have r46 := hand1 (x 2 5) (x 2 12)
      have b47 := hb (x 2 5)
      have b48 := hb (x 2 5 && x 2 12)
      clear * - r46 b47 b48 d41
      omega
    have d49 : (x 1 1 && x 1 14).toNat = 1 := by
      have r50 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b51 := hb (x 0 2)
      have b52 := hb (x 2 13)
      have b53 := hb (x 1 1 && x 1 14)
      clear * - r50 b51 b52 b53 d25 g1
      omega
    have d54 : (x 1 14).toNat = 1 := by
      have r55 := hand2 (x 1 1) (x 1 14)
      have b56 := hb (x 1 14)
      have b57 := hb (x 1 1 && x 1 14)
      clear * - r55 b56 b57 d49
      omega
    have d58 : (x 0 1).toNat = 0 := by
      have r59 : (x 1 14).toNat + (x 0 1).toNat = 1 := by have q := hd14 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b60 := hb (x 0 1)
      have b61 := hb (x 1 14)
      clear * - r59 b60 b61 d54
      omega
    have d62 : (x 0 1 && x 0 11).toNat = 0 := by
      have r63 := hand1 (x 0 1) (x 0 11)
      have b64 := hb (x 0 1)
      have b65 := hb (x 0 1 && x 0 11)
      clear * - r63 b64 b65 d58
      omega
    have d66 : (x 0 13).toNat = 0 := by
      have r67 : (x 0 13).toNat ≤ (x 0 1).toNat := himp _ _ (hp13 0)
      have b68 := hb (x 0 1)
      have b69 := hb (x 0 13)
      clear * - r67 b68 b69 d58
      omega
    have d70 : (x 0 3 && x 0 13).toNat = 0 := by
      have r71 := hand2 (x 0 3) (x 0 13)
      have b72 := hb (x 0 13)
      have b73 := hb (x 0 3 && x 0 13)
      clear * - r71 b72 b73 d66
      omega
    have d74 : (x 0 5).toNat = 0 := by
      have r75 : (x 0 5).toNat ≤ (x 0 13).toNat := himp _ _ (hp5 0)
      have b76 := hb (x 0 5)
      have b77 := hb (x 0 13)
      clear * - r75 b76 b77 d66
      omega
    have d78 : (x 0 5 && x 0 12).toNat = 0 := by
      have r79 := hand1 (x 0 5) (x 0 12)
      have b80 := hb (x 0 5)
      have b81 := hb (x 0 5 && x 0 12)
      clear * - r79 b80 b81 d74
      omega
    have d82 : (x 0 9).toNat = 0 := by
      have r83 : (x 0 9).toNat ≤ (x 0 1).toNat := himp _ _ (hp9 0)
      have b84 := hb (x 0 1)
      have b85 := hb (x 0 9)
      clear * - r83 b84 b85 d58
      omega
    have d86 : (x 1 1).toNat = 1 := by
      have r87 := hand1 (x 1 1) (x 1 14)
      have b88 := hb (x 1 1)
      have b89 := hb (x 1 1 && x 1 14)
      clear * - r87 b88 b89 d49
      omega
    have d90 : (x 2 14).toNat = 0 := by
      have r91 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b92 := hb (x 1 1)
      have b93 := hb (x 2 14)
      clear * - r91 b92 b93 d86
      omega
    have d94 : (x 2 1 && x 2 14).toNat = 0 := by
      have r95 := hand2 (x 2 1) (x 2 14)
      have b96 := hb (x 2 14)
      have b97 := hb (x 2 1 && x 2 14)
      clear * - r95 b96 b97 d90
      omega
    have d98 : (x 2 2).toNat = 0 := by
      have r99 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
      have b100 := hb (x 2 2)
      have b101 := hb (x 2 14)
      clear * - r99 b100 b101 d90
      omega
    have d102 : (x 2 2 && x 2 12).toNat = 0 := by
      have r103 := hand1 (x 2 2) (x 2 12)
      have b104 := hb (x 2 2)
      have b105 := hb (x 2 2 && x 2 12)
      clear * - r103 b104 b105 d98
      omega
    have d106 : (x 2 10).toNat = 0 := by
      have r107 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
      have b108 := hb (x 2 2)
      have b109 := hb (x 2 10)
      clear * - r107 b108 b109 d98
      omega
    have d110 : (x 2 3 && x 2 10).toNat = 0 := by
      have r111 := hand2 (x 2 3) (x 2 10)
      have b112 := hb (x 2 10)
      have b113 := hb (x 2 3 && x 2 10)
      clear * - r111 b112 b113 d106
      omega
    have d114 : (x 1 2).toNat = 0 := by
      have r115 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e116 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
      have e117 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
      have b118 := hb (x 0 3)
      have b119 := hb (x 1 2)
      have b120 := hb (x 2 13)
      have b121 := hb (x 3 12)
      clear * - r115 e116 e117 b118 b119 b120 b121 d1 d25 g14
      omega
    have d122 : (x 1 2 && x 1 12).toNat = 0 := by
      have r123 := hand1 (x 1 2) (x 1 12)
      have b124 := hb (x 1 2)
      have b125 := hb (x 1 2 && x 1 12)
      clear * - r123 b124 b125 d114
      omega
    have d126 : (x 1 10).toNat = 0 := by
      have r127 : (x 1 10).toNat ≤ (x 1 2).toNat := himp _ _ (hp10 1)
      have b128 := hb (x 1 2)
      have b129 := hb (x 1 10)
      clear * - r127 b128 b129 d114
      omega
    have d130 : (x 3 13).toNat = 1 := by
      have r131 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b132 := hb (x 1 2)
      have b133 := hb (x 3 13)
      have b134 := hb (x 2 1 && x 2 14)
      clear * - r131 b132 b133 b134 d94 d114
      omega
    have d135 : (x 3 1).toNat = 1 := by
      have r136 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
      have b137 := hb (x 3 1)
      have b138 := hb (x 3 13)
      clear * - r136 b137 b138 d130
      omega
    have d139 : (x 4 14).toNat = 0 := by
      have r140 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b141 := hb (x 3 1)
      have b142 := hb (x 4 14)
      clear * - r140 b141 b142 d135
      omega
    have d143 : (x 4 1 && x 4 14).toNat = 0 := by
      have r144 := hand2 (x 4 1) (x 4 14)
      have b145 := hb (x 4 14)
      have b146 := hb (x 4 1 && x 4 14)
      clear * - r144 b145 b146 d139
      omega
    have d147 : (x 4 3 && x 4 14).toNat = 0 := by
      have r148 := hand2 (x 4 3) (x 4 14)
      have b149 := hb (x 4 14)
      have b150 := hb (x 4 3 && x 4 14)
      clear * - r148 b149 b150 d139
      omega
    have d151 : (x 4 2).toNat = 0 := by
      have r152 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
      have b153 := hb (x 4 2)
      have b154 := hb (x 4 14)
      clear * - r152 b153 b154 d139
      omega
    have d155 : (x 4 10).toNat = 0 := by
      have r156 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
      have b157 := hb (x 4 2)
      have b158 := hb (x 4 10)
      clear * - r156 b157 b158 d151
      omega
    have d159 : (x 4 3 && x 4 10).toNat = 0 := by
      have r160 := hand2 (x 4 3) (x 4 10)
      have b161 := hb (x 4 10)
      have b162 := hb (x 4 3 && x 4 10)
      clear * - r160 b161 b162 d155
      omega
    have d163 : (x 4 12).toNat = 0 := by
      have r164 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e165 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e166 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b167 := hb (x 1 3)
      have b168 := hb (x 2 2)
      have b169 := hb (x 3 13)
      have b170 := hb (x 4 12)
      clear * - r164 e165 e166 b167 b168 b169 b170 d130 d98
      omega
    have d171 : (x 4 4).toNat = 0 := by
      have r172 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
      have b173 := hb (x 4 4)
      have b174 := hb (x 4 12)
      clear * - r172 b173 b174 d163
      omega
    have d175 : (x 1 3).toNat = 0 := by
      have r176 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e177 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e178 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b179 := hb (x 1 3)
      have b180 := hb (x 2 2)
      have b181 := hb (x 3 13)
      have b182 := hb (x 4 12)
      clear * - r176 e177 e178 b179 b180 b181 b182 d163 d130 d98
      omega
    have d183 : (x 1 3 && x 1 14).toNat = 0 := by
      have r184 := hand1 (x 1 3) (x 1 14)
      have b185 := hb (x 1 3)
      have b186 := hb (x 1 3 && x 1 14)
      clear * - r184 b185 b186 d175
      omega
    have d187 : (x 1 3 && x 1 13).toNat = 0 := by
      have r188 := hand1 (x 1 3) (x 1 13)
      have b189 := hb (x 1 3)
      have b190 := hb (x 1 3 && x 1 13)
      clear * - r188 b189 b190 d175
      omega
    have d191 : (x 1 11).toNat = 0 := by
      have r192 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
      have b193 := hb (x 1 3)
      have b194 := hb (x 1 11)
      clear * - r192 b193 b194 d175
      omega
    have d195 : (x 1 4 && x 1 11).toNat = 0 := by
      have r196 := hand2 (x 1 4) (x 1 11)
      have b197 := hb (x 1 11)
      have b198 := hb (x 1 4 && x 1 11)
      clear * - r196 b197 b198 d191
      omega
    cases h199 : x 0 4
    · have f200 : (x 0 4).toNat = 0 := by rw [h199]; rfl
      exact cycle_power_fifteen_tight_type_sequence_two_iff_three_core_b0 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 f200 d17 d151 d171 d9 d33 d183 d147
    · have f766 : (x 0 4).toNat = 1 := by rw [h199]; rfl
      exact cycle_power_fifteen_tight_type_sequence_two_iff_three_core_b1 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 f766 d74 d82 d66 d126 d191 d41 d106 d17 d151 d155 d110 d195 d78 d159 d21 d45 d62 d122 d70 d102 d187 d13 d37 d147 d143
  · exfalso
    have g1 : (x 0 2).toNat = 1 := by rw [h01]; rfl
    have g14 : (x 0 3).toNat = 0 := by rw [h014]; rfl
    have d1934 : (x 0 3 && x 0 14).toNat = 0 := by
      have r1935 := hand1 (x 0 3) (x 0 14)
      have b1936 := hb (x 0 3)
      have b1937 := hb (x 0 3 && x 0 14)
      clear * - r1935 b1936 b1937 g14
      omega
    have d1938 : (x 0 3 && x 0 13).toNat = 0 := by
      have r1939 := hand1 (x 0 3) (x 0 13)
      have b1940 := hb (x 0 3)
      have b1941 := hb (x 0 3 && x 0 13)
      clear * - r1939 b1940 b1941 g14
      omega
    have d1942 : (x 0 3 && x 0 12).toNat = 0 := by
      have r1943 := hand1 (x 0 3) (x 0 12)
      have b1944 := hb (x 0 3)
      have b1945 := hb (x 0 3 && x 0 12)
      clear * - r1943 b1944 b1945 g14
      omega
    have d1946 : (x 0 1 && x 0 3).toNat = 0 := by
      have r1947 := hand2 (x 0 1) (x 0 3)
      have b1948 := hb (x 0 3)
      have b1949 := hb (x 0 1 && x 0 3)
      clear * - r1947 b1948 b1949 g14
      omega
    have d1950 : (x 0 11).toNat = 0 := by
      have r1951 : (x 0 11).toNat ≤ (x 0 3).toNat := himp _ _ (hp11 0)
      have b1952 := hb (x 0 3)
      have b1953 := hb (x 0 11)
      clear * - r1951 b1952 b1953 g14
      omega
    have d1954 : (x 0 1 && x 0 11).toNat = 0 := by
      have r1955 := hand2 (x 0 1) (x 0 11)
      have b1956 := hb (x 0 11)
      have b1957 := hb (x 0 1 && x 0 11)
      clear * - r1955 b1956 b1957 d1950
      omega
    have d1958 : (x 0 2 && x 0 11).toNat = 0 := by
      have r1959 := hand2 (x 0 2) (x 0 11)
      have b1960 := hb (x 0 11)
      have b1961 := hb (x 0 2 && x 0 11)
      clear * - r1959 b1960 b1961 d1950
      omega
    have d1962 : (x 0 11 && x 0 14).toNat = 0 := by
      have r1963 := hand1 (x 0 11) (x 0 14)
      have b1964 := hb (x 0 11)
      have b1965 := hb (x 0 11 && x 0 14)
      clear * - r1963 b1964 b1965 d1950
      omega
    have d1966 : (x 0 11 && x 0 13).toNat = 0 := by
      have r1967 := hand1 (x 0 11) (x 0 13)
      have b1968 := hb (x 0 11)
      have b1969 := hb (x 0 11 && x 0 13)
      clear * - r1967 b1968 b1969 d1950
      omega
    have d1970 : (x 0 11 && x 0 12).toNat = 0 := by
      have r1971 := hand1 (x 0 11) (x 0 12)
      have b1972 := hb (x 0 11)
      have b1973 := hb (x 0 11 && x 0 12)
      clear * - r1971 b1972 b1973 d1950
      omega
    have d1974 : (x 0 14).toNat = 1 := by
      have r1975 : (x 0 2).toNat ≤ (x 0 14).toNat := himp _ _ (hp2 0)
      have b1976 := hb (x 0 2)
      have b1977 := hb (x 0 14)
      clear * - r1975 b1976 b1977 g1
      omega
    have d1978 : (x (-1) 1).toNat = 0 := by
      have r1979 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1980 := hb (x (-1) 1)
      have b1981 := hb (x 0 14)
      clear * - r1979 b1980 b1981 d1974
      omega
    have d1982 : (x (-1) 1 && x (-1) 14).toNat = 0 := by
      have r1983 := hand1 (x (-1) 1) (x (-1) 14)
      have b1984 := hb (x (-1) 1)
      have b1985 := hb (x (-1) 1 && x (-1) 14)
      clear * - r1983 b1984 b1985 d1978
      omega
    have d1986 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
      have r1987 := hand1 (x (-1) 1) (x (-1) 12)
      have b1988 := hb (x (-1) 1)
      have b1989 := hb (x (-1) 1 && x (-1) 12)
      clear * - r1987 b1988 b1989 d1978
      omega
    have d1990 : (x (-1) 1 && x (-1) 10).toNat = 0 := by
      have r1991 := hand1 (x (-1) 1) (x (-1) 10)
      have b1992 := hb (x (-1) 1)
      have b1993 := hb (x (-1) 1 && x (-1) 10)
      clear * - r1991 b1992 b1993 d1978
      omega
    have d1994 : (x (-1) 1 && x (-1) 8).toNat = 0 := by
      have r1995 := hand1 (x (-1) 1) (x (-1) 8)
      have b1996 := hb (x (-1) 1)
      have b1997 := hb (x (-1) 1 && x (-1) 8)
      clear * - r1995 b1996 b1997 d1978
      omega
    have d1998 : (x (-1) 1 && x (-1) 6).toNat = 0 := by
      have r1999 := hand1 (x (-1) 1) (x (-1) 6)
      have b2000 := hb (x (-1) 1)
      have b2001 := hb (x (-1) 1 && x (-1) 6)
      clear * - r1999 b2000 b2001 d1978
      omega
    have d2002 : (x (-1) 13).toNat = 0 := by
      have r2003 : (x (-1) 13).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp13 (-1))
      have b2004 := hb (x (-1) 1)
      have b2005 := hb (x (-1) 13)
      clear * - r2003 b2004 b2005 d1978
      omega
    have d2006 : (x (-1) 2 && x (-1) 13).toNat = 0 := by
      have r2007 := hand2 (x (-1) 2) (x (-1) 13)
      have b2008 := hb (x (-1) 13)
      have b2009 := hb (x (-1) 2 && x (-1) 13)
      clear * - r2007 b2008 b2009 d2002
      omega
    have d2010 : (x (-1) 3 && x (-1) 13).toNat = 0 := by
      have r2011 := hand2 (x (-1) 3) (x (-1) 13)
      have b2012 := hb (x (-1) 13)
      have b2013 := hb (x (-1) 3 && x (-1) 13)
      clear * - r2011 b2012 b2013 d2002
      omega
    have d2014 : (x (-1) 4 && x (-1) 13).toNat = 0 := by
      have r2015 := hand2 (x (-1) 4) (x (-1) 13)
      have b2016 := hb (x (-1) 13)
      have b2017 := hb (x (-1) 4 && x (-1) 13)
      clear * - r2015 b2016 b2017 d2002
      omega
    have d2018 : (x (-1) 7 && x (-1) 13).toNat = 0 := by
      have r2019 := hand2 (x (-1) 7) (x (-1) 13)
      have b2020 := hb (x (-1) 13)
      have b2021 := hb (x (-1) 7 && x (-1) 13)
      clear * - r2019 b2020 b2021 d2002
      omega
    have d2022 : (x (-1) 8 && x (-1) 13).toNat = 0 := by
      have r2023 := hand2 (x (-1) 8) (x (-1) 13)
      have b2024 := hb (x (-1) 13)
      have b2025 := hb (x (-1) 8 && x (-1) 13)
      clear * - r2023 b2024 b2025 d2002
      omega
    have d2026 : (x (-1) 9 && x (-1) 13).toNat = 0 := by
      have r2027 := hand2 (x (-1) 9) (x (-1) 13)
      have b2028 := hb (x (-1) 13)
      have b2029 := hb (x (-1) 9 && x (-1) 13)
      clear * - r2027 b2028 b2029 d2002
      omega
    have d2030 : (x (-1) 12 && x (-1) 13).toNat = 0 := by
      have r2031 := hand2 (x (-1) 12) (x (-1) 13)
      have b2032 := hb (x (-1) 13)
      have b2033 := hb (x (-1) 12 && x (-1) 13)
      clear * - r2031 b2032 b2033 d2002
      omega
    have d2034 : (x (-1) 5).toNat = 0 := by
      have r2035 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
      have b2036 := hb (x (-1) 5)
      have b2037 := hb (x (-1) 13)
      clear * - r2035 b2036 b2037 d2002
      omega
    have d2038 : (x (-1) 5 && x (-1) 14).toNat = 0 := by
      have r2039 := hand1 (x (-1) 5) (x (-1) 14)
      have b2040 := hb (x (-1) 5)
      have b2041 := hb (x (-1) 5 && x (-1) 14)
      clear * - r2039 b2040 b2041 d2034
      omega
    have d2042 : (x (-1) 5 && x (-1) 10).toNat = 0 := by
      have r2043 := hand1 (x (-1) 5) (x (-1) 10)
      have b2044 := hb (x (-1) 5)
      have b2045 := hb (x (-1) 5 && x (-1) 10)
      clear * - r2043 b2044 b2045 d2034
      omega
    have d2046 : (x (-1) 5 && x (-1) 9).toNat = 0 := by
      have r2047 := hand1 (x (-1) 5) (x (-1) 9)
      have b2048 := hb (x (-1) 5)
      have b2049 := hb (x (-1) 5 && x (-1) 9)
      clear * - r2047 b2048 b2049 d2034
      omega
    have d2050 : (x (-1) 2 && x (-1) 5).toNat = 0 := by
      have r2051 := hand2 (x (-1) 2) (x (-1) 5)
      have b2052 := hb (x (-1) 5)
      have b2053 := hb (x (-1) 2 && x (-1) 5)
      clear * - r2051 b2052 b2053 d2034
      omega
    have d2054 : (x (-1) 3 && x (-1) 5).toNat = 0 := by
      have r2055 := hand2 (x (-1) 3) (x (-1) 5)
      have b2056 := hb (x (-1) 5)
      have b2057 := hb (x (-1) 3 && x (-1) 5)
      clear * - r2055 b2056 b2057 d2034
      omega
    have d2058 : (x (-1) 9).toNat = 0 := by
      have r2059 : (x (-1) 9).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp9 (-1))
      have b2060 := hb (x (-1) 1)
      have b2061 := hb (x (-1) 9)
      clear * - r2059 b2060 b2061 d1978
      omega
    have d2062 : (x (-1) 3 && x (-1) 9).toNat = 0 := by
      have r2063 := hand2 (x (-1) 3) (x (-1) 9)
      have b2064 := hb (x (-1) 9)
      have b2065 := hb (x (-1) 3 && x (-1) 9)
      clear * - r2063 b2064 b2065 d2058
      omega
    have d2066 : (x (-1) 9 && x (-1) 14).toNat = 0 := by
      have r2067 := hand1 (x (-1) 9) (x (-1) 14)
      have b2068 := hb (x (-1) 9)
      have b2069 := hb (x (-1) 9 && x (-1) 14)
      clear * - r2067 b2068 b2069 d2058
      omega
    have d2070 : (x 2 12).toNat = 0 := by
      have r2071 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2072 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e2073 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b2074 := hb (x (-1) 3)
      have b2075 := hb (x 0 2)
      have b2076 := hb (x 1 13)
      have b2077 := hb (x 2 12)
      clear * - r2071 e2072 e2073 b2074 b2075 b2076 b2077 g1
      omega
    have d2078 : (x 2 1 && x 2 12).toNat = 0 := by
      have r2079 := hand2 (x 2 1) (x 2 12)
      have b2080 := hb (x 2 12)
      have b2081 := hb (x 2 1 && x 2 12)
      clear * - r2079 b2080 b2081 d2070
      omega
    have d2082 : (x 2 2 && x 2 12).toNat = 0 := by
      have r2083 := hand2 (x 2 2) (x 2 12)
      have b2084 := hb (x 2 12)
      have b2085 := hb (x 2 2 && x 2 12)
      clear * - r2083 b2084 b2085 d2070
      omega
    have d2086 : (x 2 5 && x 2 12).toNat = 0 := by
      have r2087 := hand2 (x 2 5) (x 2 12)
      have b2088 := hb (x 2 12)
      have b2089 := hb (x 2 5 && x 2 12)
      clear * - r2087 b2088 b2089 d2070
      omega
    have d2090 : (x 2 6 && x 2 12).toNat = 0 := by
      have r2091 := hand2 (x 2 6) (x 2 12)
      have b2092 := hb (x 2 12)
      have b2093 := hb (x 2 6 && x 2 12)
      clear * - r2091 b2092 b2093 d2070
      omega
    have d2094 : (x 2 7 && x 2 12).toNat = 0 := by
      have r2095 := hand2 (x 2 7) (x 2 12)
      have b2096 := hb (x 2 12)
      have b2097 := hb (x 2 7 && x 2 12)
      clear * - r2095 b2096 b2097 d2070
      omega
    have d2098 : (x 2 8 && x 2 12).toNat = 0 := by
      have r2099 := hand2 (x 2 8) (x 2 12)
      have b2100 := hb (x 2 12)
      have b2101 := hb (x 2 8 && x 2 12)
      clear * - r2099 b2100 b2101 d2070
      omega
    have d2102 : (x 2 9 && x 2 12).toNat = 0 := by
      have r2103 := hand2 (x 2 9) (x 2 12)
      have b2104 := hb (x 2 12)
      have b2105 := hb (x 2 9 && x 2 12)
      clear * - r2103 b2104 b2105 d2070
      omega
    have d2106 : (x 2 4).toNat = 0 := by
      have r2107 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
      have b2108 := hb (x 2 4)
      have b2109 := hb (x 2 12)
      clear * - r2107 b2108 b2109 d2070
      omega
    have d2110 : (x 2 4 && x 2 13).toNat = 0 := by
      have r2111 := hand1 (x 2 4) (x 2 13)
      have b2112 := hb (x 2 4)
      have b2113 := hb (x 2 4 && x 2 13)
      clear * - r2111 b2112 b2113 d2106
      omega
    have d2114 : (x 2 4 && x 2 10).toNat = 0 := by
      have r2115 := hand1 (x 2 4) (x 2 10)
      have b2116 := hb (x 2 4)
      have b2117 := hb (x 2 4 && x 2 10)
      clear * - r2115 b2116 b2117 d2106
      omega
    have d2118 : (x 2 4 && x 2 8).toNat = 0 := by
      have r2119 := hand1 (x 2 4) (x 2 8)
      have b2120 := hb (x 2 4)
      have b2121 := hb (x 2 4 && x 2 8)
      clear * - r2119 b2120 b2121 d2106
      omega
    have d2122 : (x 1 13).toNat = 0 := by
      have r2123 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2124 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e2125 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b2126 := hb (x (-1) 3)
      have b2127 := hb (x 0 2)
      have b2128 := hb (x 1 13)
      have b2129 := hb (x 2 12)
      clear * - r2123 e2124 e2125 b2126 b2127 b2128 b2129 d2070 g1
      omega
    have d2130 : (x 1 2 && x 1 13).toNat = 0 := by
      have r2131 := hand2 (x 1 2) (x 1 13)
      have b2132 := hb (x 1 13)
      have b2133 := hb (x 1 2 && x 1 13)
      clear * - r2131 b2132 b2133 d2122
      omega
    have d2134 : (x 1 3 && x 1 13).toNat = 0 := by
      have r2135 := hand2 (x 1 3) (x 1 13)
      have b2136 := hb (x 1 13)
      have b2137 := hb (x 1 3 && x 1 13)
      clear * - r2135 b2136 b2137 d2122
      omega
    have d2138 : (x 1 6 && x 1 13).toNat = 0 := by
      have r2139 := hand2 (x 1 6) (x 1 13)
      have b2140 := hb (x 1 13)
      have b2141 := hb (x 1 6 && x 1 13)
      clear * - r2139 b2140 b2141 d2122
      omega
    have d2142 : (x 1 7 && x 1 13).toNat = 0 := by
      have r2143 := hand2 (x 1 7) (x 1 13)
      have b2144 := hb (x 1 13)
      have b2145 := hb (x 1 7 && x 1 13)
      clear * - r2143 b2144 b2145 d2122
      omega
    have d2146 : (x 1 8 && x 1 13).toNat = 0 := by
      have r2147 := hand2 (x 1 8) (x 1 13)
      have b2148 := hb (x 1 13)
      have b2149 := hb (x 1 8 && x 1 13)
      clear * - r2147 b2148 b2149 d2122
      omega
    have d2150 : (x 1 9 && x 1 13).toNat = 0 := by
      have r2151 := hand2 (x 1 9) (x 1 13)
      have b2152 := hb (x 1 13)
      have b2153 := hb (x 1 9 && x 1 13)
      clear * - r2151 b2152 b2153 d2122
      omega
    have d2154 : (x 1 10 && x 1 13).toNat = 0 := by
      have r2155 := hand2 (x 1 10) (x 1 13)
      have b2156 := hb (x 1 13)
      have b2157 := hb (x 1 10 && x 1 13)
      clear * - r2155 b2156 b2157 d2122
      omega
    have d2158 : (x 1 5).toNat = 0 := by
      have r2159 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
      have b2160 := hb (x 1 5)
      have b2161 := hb (x 1 13)
      clear * - r2159 b2160 b2161 d2122
      omega
    have d2162 : (x 1 5 && x 1 14).toNat = 0 := by
      have r2163 := hand1 (x 1 5) (x 1 14)
      have b2164 := hb (x 1 5)
      have b2165 := hb (x 1 5 && x 1 14)
      clear * - r2163 b2164 b2165 d2158
      omega
    have d2166 : (x 1 5 && x 1 11).toNat = 0 := by
      have r2167 := hand1 (x 1 5) (x 1 11)
      have b2168 := hb (x 1 5)
      have b2169 := hb (x 1 5 && x 1 11)
      clear * - r2167 b2168 b2169 d2158
      omega
    have d2170 : (x 1 5 && x 1 9).toNat = 0 := by
      have r2171 := hand1 (x 1 5) (x 1 9)
      have b2172 := hb (x 1 5)
      have b2173 := hb (x 1 5 && x 1 9)
      clear * - r2171 b2172 b2173 d2158
      omega
    have d2174 : (x (-1) 3).toNat = 0 := by
      have r2175 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2176 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e2177 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b2178 := hb (x (-1) 3)
      have b2179 := hb (x 0 2)
      have b2180 := hb (x 1 13)
      have b2181 := hb (x 2 12)
      clear * - r2175 e2176 e2177 b2178 b2179 b2180 b2181 d2070 d2122 g1
      omega
    have d2182 : (x (-1) 3 && x (-1) 14).toNat = 0 := by
      have r2183 := hand1 (x (-1) 3) (x (-1) 14)
      have b2184 := hb (x (-1) 3)
      have b2185 := hb (x (-1) 3 && x (-1) 14)
      clear * - r2183 b2184 b2185 d2174
      omega
    have d2186 : (x (-1) 3 && x (-1) 12).toNat = 0 := by
      have r2187 := hand1 (x (-1) 3) (x (-1) 12)
      have b2188 := hb (x (-1) 3)
      have b2189 := hb (x (-1) 3 && x (-1) 12)
      clear * - r2187 b2188 b2189 d2174
      omega
    have d2190 : (x (-1) 3 && x (-1) 10).toNat = 0 := by
      have r2191 := hand1 (x (-1) 3) (x (-1) 10)
      have b2192 := hb (x (-1) 3)
      have b2193 := hb (x (-1) 3 && x (-1) 10)
      clear * - r2191 b2192 b2193 d2174
      omega
    have d2194 : (x (-1) 3 && x (-1) 8).toNat = 0 := by
      have r2195 := hand1 (x (-1) 3) (x (-1) 8)
      have b2196 := hb (x (-1) 3)
      have b2197 := hb (x (-1) 3 && x (-1) 8)
      clear * - r2195 b2196 b2197 d2174
      omega
    have d2198 : (x (-1) 3 && x (-1) 7).toNat = 0 := by
      have r2199 := hand1 (x (-1) 3) (x (-1) 7)
      have b2200 := hb (x (-1) 3)
      have b2201 := hb (x (-1) 3 && x (-1) 7)
      clear * - r2199 b2200 b2201 d2174
      omega
    have d2202 : (x (-1) 3 && x (-1) 6).toNat = 0 := by
      have r2203 := hand1 (x (-1) 3) (x (-1) 6)
      have b2204 := hb (x (-1) 3)
      have b2205 := hb (x (-1) 3 && x (-1) 6)
      clear * - r2203 b2204 b2205 d2174
      omega
    have d2206 : (x (-1) 11).toNat = 0 := by
      have r2207 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
      have b2208 := hb (x (-1) 3)
      have b2209 := hb (x (-1) 11)
      clear * - r2207 b2208 b2209 d2174
      omega
    have d2210 : (x (-1) 7 && x (-1) 11).toNat = 0 := by
      have r2211 := hand2 (x (-1) 7) (x (-1) 11)
      have b2212 := hb (x (-1) 11)
      have b2213 := hb (x (-1) 7 && x (-1) 11)
      clear * - r2211 b2212 b2213 d2206
      omega
    cases h2214 : x 0 13
    · have f2215 : (x 0 13).toNat = 0 := by rw [h2214]; rfl
      have d2216 : (x 0 2 && x 0 13).toNat = 0 := by
        have r2217 := hand2 (x 0 2) (x 0 13)
        have b2218 := hb (x 0 13)
        have b2219 := hb (x 0 2 && x 0 13)
        clear * - r2217 b2218 b2219 f2215
        omega
      have d2220 : (x 0 4 && x 0 13).toNat = 0 := by
        have r2221 := hand2 (x 0 4) (x 0 13)
        have b2222 := hb (x 0 13)
        have b2223 := hb (x 0 4 && x 0 13)
        clear * - r2221 b2222 b2223 f2215
        omega
      have d2224 : (x 0 5).toNat = 0 := by
        have r2225 : (x 0 5).toNat ≤ (x 0 13).toNat := himp _ _ (hp5 0)
        have b2226 := hb (x 0 5)
        have b2227 := hb (x 0 13)
        clear * - r2225 b2226 b2227 f2215
        omega
      have d2228 : (x 0 2 && x 0 5).toNat = 0 := by
        have r2229 := hand2 (x 0 2) (x 0 5)
        have b2230 := hb (x 0 5)
        have b2231 := hb (x 0 2 && x 0 5)
        clear * - r2229 b2230 b2231 d2224
        omega
      have d2232 : (x (-2) 2).toNat = 1 := by
        have r2233 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b2234 := hb (x (-2) 2)
        have b2235 := hb (x 0 13)
        have b2236 := hb (x (-1) 1 && x (-1) 14)
        clear * - r2233 b2234 b2235 b2236 f2215 d1982
        omega
      have d2237 : (x (-2) 14).toNat = 1 := by
        have r2238 : (x (-2) 2).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp2 (-2))
        have b2239 := hb (x (-2) 2)
        have b2240 := hb (x (-2) 14)
        clear * - r2238 b2239 b2240 d2232
        omega
      have d2241 : (x (-3) 1).toNat = 0 := by
        have r2242 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b2243 := hb (x (-3) 1)
        have b2244 := hb (x (-2) 14)
        clear * - r2242 b2243 b2244 d2237
        omega
      have d2245 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
        have r2246 := hand1 (x (-3) 1) (x (-3) 14)
        have b2247 := hb (x (-3) 1)
        have b2248 := hb (x (-3) 1 && x (-3) 14)
        clear * - r2246 b2247 b2248 d2241
        omega
      have d2249 : (x (-3) 1 && x (-3) 12).toNat = 0 := by
        have r2250 := hand1 (x (-3) 1) (x (-3) 12)
        have b2251 := hb (x (-3) 1)
        have b2252 := hb (x (-3) 1 && x (-3) 12)
        clear * - r2250 b2251 b2252 d2241
        omega
      have d2253 : (x (-3) 1 && x (-3) 11).toNat = 0 := by
        have r2254 := hand1 (x (-3) 1) (x (-3) 11)
        have b2255 := hb (x (-3) 1)
        have b2256 := hb (x (-3) 1 && x (-3) 11)
        clear * - r2254 b2255 b2256 d2241
        omega
      have d2257 : (x (-3) 13).toNat = 0 := by
        have r2258 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
        have b2259 := hb (x (-3) 1)
        have b2260 := hb (x (-3) 13)
        clear * - r2258 b2259 b2260 d2241
        omega
      have d2261 : (x (-3) 2 && x (-3) 13).toNat = 0 := by
        have r2262 := hand2 (x (-3) 2) (x (-3) 13)
        have b2263 := hb (x (-3) 13)
        have b2264 := hb (x (-3) 2 && x (-3) 13)
        clear * - r2262 b2263 b2264 d2257
        omega
      have d2265 : (x (-3) 9 && x (-3) 13).toNat = 0 := by
        have r2266 := hand2 (x (-3) 9) (x (-3) 13)
        have b2267 := hb (x (-3) 13)
        have b2268 := hb (x (-3) 9 && x (-3) 13)
        clear * - r2266 b2267 b2268 d2257
        omega
      have d2269 : (x (-3) 5).toNat = 0 := by
        have r2270 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
        have b2271 := hb (x (-3) 5)
        have b2272 := hb (x (-3) 13)
        clear * - r2270 b2271 b2272 d2257
        omega
      have d2273 : (x (-3) 5 && x (-3) 14).toNat = 0 := by
        have r2274 := hand1 (x (-3) 5) (x (-3) 14)
        have b2275 := hb (x (-3) 5)
        have b2276 := hb (x (-3) 5 && x (-3) 14)
        clear * - r2274 b2275 b2276 d2269
        omega
      have d2277 : (x (-3) 5 && x (-3) 12).toNat = 0 := by
        have r2278 := hand1 (x (-3) 5) (x (-3) 12)
        have b2279 := hb (x (-3) 5)
        have b2280 := hb (x (-3) 5 && x (-3) 12)
        clear * - r2278 b2279 b2280 d2269
        omega
      have d2281 : (x (-3) 5 && x (-3) 10).toNat = 0 := by
        have r2282 := hand1 (x (-3) 5) (x (-3) 10)
        have b2283 := hb (x (-3) 5)
        have b2284 := hb (x (-3) 5 && x (-3) 10)
        clear * - r2282 b2283 b2284 d2269
        omega
      have d2285 : (x (-3) 5 && x (-3) 9).toNat = 0 := by
        have r2286 := hand1 (x (-3) 5) (x (-3) 9)
        have b2287 := hb (x (-3) 5)
        have b2288 := hb (x (-3) 5 && x (-3) 9)
        clear * - r2286 b2287 b2288 d2269
        omega
      have d2289 : (x (-3) 5 && x (-3) 8).toNat = 0 := by
        have r2290 := hand1 (x (-3) 5) (x (-3) 8)
        have b2291 := hb (x (-3) 5)
        have b2292 := hb (x (-3) 5 && x (-3) 8)
        clear * - r2290 b2291 b2292 d2269
        omega
      have d2293 : (x (-3) 9).toNat = 0 := by
        have r2294 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
        have b2295 := hb (x (-3) 1)
        have b2296 := hb (x (-3) 9)
        clear * - r2294 b2295 b2296 d2241
        omega
      have d2297 : (x (-3) 4 && x (-3) 9).toNat = 0 := by
        have r2298 := hand2 (x (-3) 4) (x (-3) 9)
        have b2299 := hb (x (-3) 9)
        have b2300 := hb (x (-3) 4 && x (-3) 9)
        clear * - r2298 b2299 b2300 d2293
        omega
      have d2301 : (x 0 12).toNat = 0 := by
        have r2302 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e2303 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
        have e2304 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
        have b2305 := hb (x (-3) 3)
        have b2306 := hb (x (-2) 2)
        have b2307 := hb (x (-1) 13)
        have b2308 := hb (x 0 12)
        clear * - r2302 e2303 e2304 b2305 b2306 b2307 b2308 d2002 d2232
        omega
      have d2309 : (x 0 1 && x 0 12).toNat = 0 := by
        have r2310 := hand2 (x 0 1) (x 0 12)
        have b2311 := hb (x 0 12)
        have b2312 := hb (x 0 1 && x 0 12)
        clear * - r2310 b2311 b2312 d2301
        omega
      have d2313 : (x 0 2 && x 0 12).toNat = 0 := by
        have r2314 := hand2 (x 0 2) (x 0 12)
        have b2315 := hb (x 0 12)
        have b2316 := hb (x 0 2 && x 0 12)
        clear * - r2314 b2315 b2316 d2301
        omega
      have d2317 : (x 0 4).toNat = 0 := by
        have r2318 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
        have b2319 := hb (x 0 4)
        have b2320 := hb (x 0 12)
        clear * - r2318 b2319 b2320 d2301
        omega
      have d2321 : (x 0 4 && x 0 14).toNat = 0 := by
        have r2322 := hand1 (x 0 4) (x 0 14)
        have b2323 := hb (x 0 4)
        have b2324 := hb (x 0 4 && x 0 14)
        clear * - r2322 b2323 b2324 d2317
        omega
      have d2325 : (x 0 1 && x 0 4).toNat = 0 := by
        have r2326 := hand2 (x 0 1) (x 0 4)
        have b2327 := hb (x 0 4)
        have b2328 := hb (x 0 1 && x 0 4)
        clear * - r2326 b2327 b2328 d2317
        omega
      have d2329 : (x (-3) 3).toNat = 0 := by
        have r2330 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e2331 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
        have e2332 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
        have b2333 := hb (x (-3) 3)
        have b2334 := hb (x (-2) 2)
        have b2335 := hb (x (-1) 13)
        have b2336 := hb (x 0 12)
        clear * - r2330 e2331 e2332 b2333 b2334 b2335 b2336 d2301 d2002 d2232
        omega
      have d2337 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
        have r2338 := hand1 (x (-3) 3) (x (-3) 14)
        have b2339 := hb (x (-3) 3)
        have b2340 := hb (x (-3) 3 && x (-3) 14)
        clear * - r2338 b2339 b2340 d2329
        omega
      have d2341 : (x (-3) 11).toNat = 0 := by
        have r2342 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
        have b2343 := hb (x (-3) 3)
        have b2344 := hb (x (-3) 11)
        clear * - r2342 b2343 b2344 d2329
        omega
      have d2345 : (x (-3) 2 && x (-3) 11).toNat = 0 := by
        have r2346 := hand2 (x (-3) 2) (x (-3) 11)
        have b2347 := hb (x (-3) 11)
        have b2348 := hb (x (-3) 2 && x (-3) 11)
        clear * - r2346 b2347 b2348 d2341
        omega
      cases h2349 : x 0 7
      · have f2350 : (x 0 7).toNat = 0 := by rw [h2349]; rfl
        have d2351 : (x 0 1 && x 0 7).toNat = 0 := by
          have r2352 := hand2 (x 0 1) (x 0 7)
          have b2353 := hb (x 0 7)
          have b2354 := hb (x 0 1 && x 0 7)
          clear * - r2352 b2353 b2354 f2350
          omega
        have d2355 : (x 0 2 && x 0 7).toNat = 0 := by
          have r2356 := hand2 (x 0 2) (x 0 7)
          have b2357 := hb (x 0 7)
          have b2358 := hb (x 0 2 && x 0 7)
          clear * - r2356 b2357 b2358 f2350
          omega
        cases h2359 : x 0 8
        · have f2360 : (x 0 8).toNat = 0 := by rw [h2359]; rfl
          have d2361 : (x 0 8 && x 0 14).toNat = 0 := by
            have r2362 := hand1 (x 0 8) (x 0 14)
            have b2363 := hb (x 0 8)
            have b2364 := hb (x 0 8 && x 0 14)
            clear * - r2362 b2363 b2364 f2360
            omega
          cases h2365 : x 0 1
          · have f2366 : (x 0 1).toNat = 0 := by rw [h2365]; rfl
            exact cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a0000 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d2257 d2002 f2366 f2215 d2122 d2309 d2006 d2216 d2182 d2078 d2130 d1934 d2245
          · have f2601 : (x 0 1).toNat = 1 := by rw [h2365]; rfl
            have d2602 : (x 1 14).toNat = 0 := by
              have r2603 : (x 1 14).toNat + (x 0 1).toNat = 1 := by have q := hd14 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b2604 := hb (x 0 1)
              have b2605 := hb (x 1 14)
              clear * - r2603 b2604 b2605 f2601
              omega
            have d2606 : (x 1 3 && x 1 14).toNat = 0 := by
              have r2607 := hand2 (x 1 3) (x 1 14)
              have b2608 := hb (x 1 14)
              have b2609 := hb (x 1 3 && x 1 14)
              clear * - r2607 b2608 b2609 d2602
              omega
            have d2610 : (x 1 7 && x 1 14).toNat = 0 := by
              have r2611 := hand2 (x 1 7) (x 1 14)
              have b2612 := hb (x 1 14)
              have b2613 := hb (x 1 7 && x 1 14)
              clear * - r2611 b2612 b2613 d2602
              omega
            have d2614 : (x 1 6).toNat = 0 := by
              have r2615 : (x 1 6).toNat ≤ (x 1 14).toNat := himp _ _ (hp6 1)
              have b2616 := hb (x 1 6)
              have b2617 := hb (x 1 14)
              clear * - r2615 b2616 b2617 d2602
              omega
            have d2618 : (x 1 1 && x 1 6).toNat = 0 := by
              have r2619 := hand2 (x 1 1) (x 1 6)
              have b2620 := hb (x 1 6)
              have b2621 := hb (x 1 1 && x 1 6)
              clear * - r2619 b2620 b2621 d2614
              omega
            have d2622 : (x 1 2).toNat = 0 := by
              have r2623 : (x 1 2).toNat ≤ (x 1 14).toNat := himp _ _ (hp2 1)
              have b2624 := hb (x 1 2)
              have b2625 := hb (x 1 14)
              clear * - r2623 b2624 b2625 d2602
              omega
            have d2626 : (x 1 2 && x 1 12).toNat = 0 := by
              have r2627 := hand1 (x 1 2) (x 1 12)
              have b2628 := hb (x 1 2)
              have b2629 := hb (x 1 2 && x 1 12)
              clear * - r2627 b2628 b2629 d2622
              omega
            have d2630 : (x 1 10).toNat = 0 := by
              have r2631 : (x 1 10).toNat ≤ (x 1 2).toNat := himp _ _ (hp10 1)
              have b2632 := hb (x 1 2)
              have b2633 := hb (x 1 10)
              clear * - r2631 b2632 b2633 d2622
              omega
            have d2634 : (x 1 1 && x 1 10).toNat = 0 := by
              have r2635 := hand2 (x 1 1) (x 1 10)
              have b2636 := hb (x 1 10)
              have b2637 := hb (x 1 1 && x 1 10)
              clear * - r2635 b2636 b2637 d2630
              omega
            cases h2638 : x 0 6
            · have f2639 : (x 0 6).toNat = 0 := by rw [h2638]; rfl
              have d2640 : (x 0 1 && x 0 6).toNat = 0 := by
                have r2641 := hand2 (x 0 1) (x 0 6)
                have b2642 := hb (x 0 6)
                have b2643 := hb (x 0 1 && x 0 6)
                clear * - r2641 b2642 b2643 f2639
                omega
              have d2644 : (x 0 6 && x 0 10).toNat = 0 := by
                have r2645 := hand1 (x 0 6) (x 0 10)
                have b2646 := hb (x 0 6)
                have b2647 := hb (x 0 6 && x 0 10)
                clear * - r2645 b2646 b2647 f2639
                omega
              cases h2648 : x 0 9
              · have f2649 : (x 0 9).toNat = 0 := by rw [h2648]; rfl
                have d2650 : (x 0 2 && x 0 9).toNat = 0 := by
                  have r2651 := hand2 (x 0 2) (x 0 9)
                  have b2652 := hb (x 0 9)
                  have b2653 := hb (x 0 2 && x 0 9)
                  clear * - r2651 b2652 b2653 f2649
                  omega
                cases h2654 : x 0 10
                · have f2655 : (x 0 10).toNat = 0 := by rw [h2654]; rfl
                  exact cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a0001000 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d2329 d2269 d2293 d2341 d2257 d2232 d1978 d2174 d2034 d2058 d2206 d2002 f2601 g1 d2317 d2224 f2639 f2350 f2360 f2649 f2655 d1950 f2215 d1974 d2622 d2158 d2614 d2630 d2122 d2106 d2070 d2325 d2050 d2228 d2202 d2289 d2118 d2170 d2644 d2210 d2265 d2640 d2297 d2618 d2355 d2194 d2281 d2351 d2090 d2142 d2361 d2650 d2190 d2277 d2610 d2345 d2220 d2038 d1954 d2313 d2010 d2626 d1938 d2082 d2134 d2321 d2249 d2261 d1986 d2337 d2309 d2006 d2216 d2182 d2078 d2130 d1934 d2606 d2245
                · have f7453 : (x 0 10).toNat = 1 := by rw [h2654]; rfl
                  exact cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a0001001 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d2269 d2034 d2206 f7453 d1950 d2630 d2634 d1958 d2186 d2273 d2082 d2134 d2321 d2078 d2130 d1934
              · have f7638 : (x 0 9).toNat = 1 := by rw [h2648]; rfl
                exact cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a000101 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d2269 d2174 d2034 f2601 g1 f7638 d2622 d2614 d2630 d2351 d1954 d2313 d2010 d2082 d2134 d2321 d2309 d2006 d2078 d2130 d1934
            · have f7947 : (x 0 6).toNat = 1 := by rw [h2638]; rfl
              exact cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a00011 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d2034 f7947 d2158 d2106 d2082 d2134 d2321
        · have f8023 : (x 0 8).toNat = 1 := by rw [h2359]; rfl
          exact cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a001 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d2269 d2293 d2341 d2257 d2174 d2034 d2058 d2206 g1 f8023 d1950 d2158 d2122 d2106 d2198 d2285 d2297 d2253 d2313 d2010 d2082 d2134 d2321 d1986 d2337 d2309 d2006 d2078 d2130 d1934
      · have f8522 : (x 0 7).toNat = 1 := by rw [h2349]; rfl
        exact cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a01 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d2269 d2257 d2034 d2206 d2002 g14 d2224 f8522 f2215 d1974 d2158 d2122 d2106 d2070 d2098 d2150 d1958 d2186 d2273 d2110 d2162 d2082 d2134 d2321 d2309 d2006 d2216 d2182 d2078 d2130 d1934 d2245
    · have f9062 : (x 0 13).toNat = 1 := by rw [h2214]; rfl
      have d9063 : (x 0 1).toNat = 1 := by
        have r9064 : (x 0 13).toNat ≤ (x 0 1).toNat := himp _ _ (hp13 0)
        have b9065 := hb (x 0 1)
        have b9066 := hb (x 0 13)
        clear * - r9064 b9065 b9066 f9062
        omega
      have d9067 : (x 1 14).toNat = 0 := by
        have r9068 : (x 1 14).toNat + (x 0 1).toNat = 1 := by have q := hd14 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9069 := hb (x 0 1)
        have b9070 := hb (x 1 14)
        clear * - r9068 b9069 b9070 d9063
        omega
      have d9071 : (x 1 4 && x 1 14).toNat = 0 := by
        have r9072 := hand2 (x 1 4) (x 1 14)
        have b9073 := hb (x 1 14)
        have b9074 := hb (x 1 4 && x 1 14)
        clear * - r9072 b9073 b9074 d9067
        omega
      have d9075 : (x 1 7 && x 1 14).toNat = 0 := by
        have r9076 := hand2 (x 1 7) (x 1 14)
        have b9077 := hb (x 1 14)
        have b9078 := hb (x 1 7 && x 1 14)
        clear * - r9076 b9077 b9078 d9067
        omega
      have d9079 : (x 1 9 && x 1 14).toNat = 0 := by
        have r9080 := hand2 (x 1 9) (x 1 14)
        have b9081 := hb (x 1 14)
        have b9082 := hb (x 1 9 && x 1 14)
        clear * - r9080 b9081 b9082 d9067
        omega
      have d9083 : (x 1 6).toNat = 0 := by
        have r9084 : (x 1 6).toNat ≤ (x 1 14).toNat := himp _ _ (hp6 1)
        have b9085 := hb (x 1 6)
        have b9086 := hb (x 1 14)
        clear * - r9084 b9085 b9086 d9067
        omega
      have d9087 : (x 1 6 && x 1 12).toNat = 0 := by
        have r9088 := hand1 (x 1 6) (x 1 12)
        have b9089 := hb (x 1 6)
        have b9090 := hb (x 1 6 && x 1 12)
        clear * - r9088 b9089 b9090 d9083
        omega
      have d9091 : (x 1 6 && x 1 11).toNat = 0 := by
        have r9092 := hand1 (x 1 6) (x 1 11)
        have b9093 := hb (x 1 6)
        have b9094 := hb (x 1 6 && x 1 11)
        clear * - r9092 b9093 b9094 d9083
        omega
      have d9095 : (x 1 1 && x 1 6).toNat = 0 := by
        have r9096 := hand2 (x 1 1) (x 1 6)
        have b9097 := hb (x 1 6)
        have b9098 := hb (x 1 1 && x 1 6)
        clear * - r9096 b9097 b9098 d9083
        omega
      have d9099 : (x 1 2).toNat = 0 := by
        have r9100 : (x 1 2).toNat ≤ (x 1 14).toNat := himp _ _ (hp2 1)
        have b9101 := hb (x 1 2)
        have b9102 := hb (x 1 14)
        clear * - r9100 b9101 b9102 d9067
        omega
      have d9103 : (x 1 2 && x 1 12).toNat = 0 := by
        have r9104 := hand1 (x 1 2) (x 1 12)
        have b9105 := hb (x 1 2)
        have b9106 := hb (x 1 2 && x 1 12)
        clear * - r9104 b9105 b9106 d9099
        omega
      have d9107 : (x 1 2 && x 1 11).toNat = 0 := by
        have r9108 := hand1 (x 1 2) (x 1 11)
        have b9109 := hb (x 1 2)
        have b9110 := hb (x 1 2 && x 1 11)
        clear * - r9108 b9109 b9110 d9099
        omega
      have d9111 : (x 1 10).toNat = 0 := by
        have r9112 : (x 1 10).toNat ≤ (x 1 2).toNat := himp _ _ (hp10 1)
        have b9113 := hb (x 1 2)
        have b9114 := hb (x 1 10)
        clear * - r9112 b9113 b9114 d9099
        omega
      have d9115 : (x 1 1 && x 1 10).toNat = 0 := by
        have r9116 := hand2 (x 1 1) (x 1 10)
        have b9117 := hb (x 1 10)
        have b9118 := hb (x 1 1 && x 1 10)
        clear * - r9116 b9117 b9118 d9111
        omega
      have d9119 : (x 1 10 && x 1 12).toNat = 0 := by
        have r9120 := hand1 (x 1 10) (x 1 12)
        have b9121 := hb (x 1 10)
        have b9122 := hb (x 1 10 && x 1 12)
        clear * - r9120 b9121 b9122 d9111
        omega
      have d9123 : (x 1 10 && x 1 11).toNat = 0 := by
        have r9124 := hand1 (x 1 10) (x 1 11)
        have b9125 := hb (x 1 10)
        have b9126 := hb (x 1 10 && x 1 11)
        clear * - r9124 b9125 b9126 d9111
        omega
      have d9127 : (x 1 12).toNat = 0 := by
        have r9128 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9129 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e9130 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b9131 := hb (x (-2) 3)
        have b9132 := hb (x (-1) 2)
        have b9133 := hb (x 0 13)
        have b9134 := hb (x 1 12)
        clear * - r9128 e9129 e9130 b9131 b9132 b9133 b9134 f9062
        omega
      have d9135 : (x 1 3 && x 1 12).toNat = 0 := by
        have r9136 := hand2 (x 1 3) (x 1 12)
        have b9137 := hb (x 1 12)
        have b9138 := hb (x 1 3 && x 1 12)
        clear * - r9136 b9137 b9138 d9127
        omega
      have d9139 : (x 1 7 && x 1 12).toNat = 0 := by
        have r9140 := hand2 (x 1 7) (x 1 12)
        have b9141 := hb (x 1 12)
        have b9142 := hb (x 1 7 && x 1 12)
        clear * - r9140 b9141 b9142 d9127
        omega
      have d9143 : (x 1 8 && x 1 12).toNat = 0 := by
        have r9144 := hand2 (x 1 8) (x 1 12)
        have b9145 := hb (x 1 12)
        have b9146 := hb (x 1 8 && x 1 12)
        clear * - r9144 b9145 b9146 d9127
        omega
      have d9147 : (x 1 4).toNat = 0 := by
        have r9148 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
        have b9149 := hb (x 1 4)
        have b9150 := hb (x 1 12)
        clear * - r9148 b9149 b9150 d9127
        omega
      have d9151 : (x (-1) 2).toNat = 0 := by
        have r9152 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9153 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e9154 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b9155 := hb (x (-2) 3)
        have b9156 := hb (x (-1) 2)
        have b9157 := hb (x 0 13)
        have b9158 := hb (x 1 12)
        clear * - r9152 e9153 e9154 b9155 b9156 b9157 b9158 d9127 f9062
        omega
      have d9159 : (x (-1) 2 && x (-1) 12).toNat = 0 := by
        have r9160 := hand1 (x (-1) 2) (x (-1) 12)
        have b9161 := hb (x (-1) 2)
        have b9162 := hb (x (-1) 2 && x (-1) 12)
        clear * - r9160 b9161 b9162 d9151
        omega
      have d9163 : (x (-1) 2 && x (-1) 8).toNat = 0 := by
        have r9164 := hand1 (x (-1) 2) (x (-1) 8)
        have b9165 := hb (x (-1) 2)
        have b9166 := hb (x (-1) 2 && x (-1) 8)
        clear * - r9164 b9165 b9166 d9151
        omega
      have d9167 : (x (-1) 2 && x (-1) 7).toNat = 0 := by
        have r9168 := hand1 (x (-1) 2) (x (-1) 7)
        have b9169 := hb (x (-1) 2)
        have b9170 := hb (x (-1) 2 && x (-1) 7)
        clear * - r9168 b9169 b9170 d9151
        omega
      have d9171 : (x (-1) 2 && x (-1) 4).toNat = 0 := by
        have r9172 := hand1 (x (-1) 2) (x (-1) 4)
        have b9173 := hb (x (-1) 2)
        have b9174 := hb (x (-1) 2 && x (-1) 4)
        clear * - r9172 b9173 b9174 d9151
        omega
      have d9175 : (x (-1) 10).toNat = 0 := by
        have r9176 : (x (-1) 10).toNat ≤ (x (-1) 2).toNat := himp _ _ (hp10 (-1))
        have b9177 := hb (x (-1) 2)
        have b9178 := hb (x (-1) 10)
        clear * - r9176 b9177 b9178 d9151
        omega
      have d9179 : (x (-2) 3).toNat = 0 := by
        have r9180 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9181 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e9182 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b9183 := hb (x (-2) 3)
        have b9184 := hb (x (-1) 2)
        have b9185 := hb (x 0 13)
        have b9186 := hb (x 1 12)
        clear * - r9180 e9181 e9182 b9183 b9184 b9185 b9186 d9127 f9062 d9151
        omega
      have d9187 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
        have r9188 := hand1 (x (-2) 3) (x (-2) 14)
        have b9189 := hb (x (-2) 3)
        have b9190 := hb (x (-2) 3 && x (-2) 14)
        clear * - r9188 b9189 b9190 d9179
        omega
      have d9191 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
        have r9192 := hand1 (x (-2) 3) (x (-2) 13)
        have b9193 := hb (x (-2) 3)
        have b9194 := hb (x (-2) 3 && x (-2) 13)
        clear * - r9192 b9193 b9194 d9179
        omega
      have d9195 : (x (-2) 3 && x (-2) 9).toNat = 0 := by
        have r9196 := hand1 (x (-2) 3) (x (-2) 9)
        have b9197 := hb (x (-2) 3)
        have b9198 := hb (x (-2) 3 && x (-2) 9)
        clear * - r9196 b9197 b9198 d9179
        omega
      have d9199 : (x (-2) 3 && x (-2) 8).toNat = 0 := by
        have r9200 := hand1 (x (-2) 3) (x (-2) 8)
        have b9201 := hb (x (-2) 3)
        have b9202 := hb (x (-2) 3 && x (-2) 8)
        clear * - r9200 b9201 b9202 d9179
        omega
      have d9203 : (x (-2) 3 && x (-2) 6).toNat = 0 := by
        have r9204 := hand1 (x (-2) 3) (x (-2) 6)
        have b9205 := hb (x (-2) 3)
        have b9206 := hb (x (-2) 3 && x (-2) 6)
        clear * - r9204 b9205 b9206 d9179
        omega
      have d9207 : (x (-2) 3 && x (-2) 5).toNat = 0 := by
        have r9208 := hand1 (x (-2) 3) (x (-2) 5)
        have b9209 := hb (x (-2) 3)
        have b9210 := hb (x (-2) 3 && x (-2) 5)
        clear * - r9208 b9209 b9210 d9179
        omega
      have d9211 : (x (-2) 11).toNat = 0 := by
        have r9212 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
        have b9213 := hb (x (-2) 3)
        have b9214 := hb (x (-2) 11)
        clear * - r9212 b9213 b9214 d9179
        omega
      have d9215 : (x (-2) 1 && x (-2) 11).toNat = 0 := by
        have r9216 := hand2 (x (-2) 1) (x (-2) 11)
        have b9217 := hb (x (-2) 11)
        have b9218 := hb (x (-2) 1 && x (-2) 11)
        clear * - r9216 b9217 b9218 d9211
        omega
      have d9219 : (x (-2) 2 && x (-2) 11).toNat = 0 := by
        have r9220 := hand2 (x (-2) 2) (x (-2) 11)
        have b9221 := hb (x (-2) 11)
        have b9222 := hb (x (-2) 2 && x (-2) 11)
        clear * - r9220 b9221 b9222 d9211
        omega
      have d9223 : (x (-2) 6 && x (-2) 11).toNat = 0 := by
        have r9224 := hand2 (x (-2) 6) (x (-2) 11)
        have b9225 := hb (x (-2) 11)
        have b9226 := hb (x (-2) 6 && x (-2) 11)
        clear * - r9224 b9225 b9226 d9211
        omega
      cases h9227 : x 0 12
      · have f9228 : (x 0 12).toNat = 0 := by rw [h9227]; rfl
        have d9229 : (x 0 1 && x 0 12).toNat = 0 := by
          have r9230 := hand2 (x 0 1) (x 0 12)
          have b9231 := hb (x 0 12)
          have b9232 := hb (x 0 1 && x 0 12)
          clear * - r9230 b9231 b9232 f9228
          omega
        have d9233 : (x 0 2 && x 0 12).toNat = 0 := by
          have r9234 := hand2 (x 0 2) (x 0 12)
          have b9235 := hb (x 0 12)
          have b9236 := hb (x 0 2 && x 0 12)
          clear * - r9234 b9235 b9236 f9228
          omega
        have d9237 : (x 0 4).toNat = 0 := by
          have r9238 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
          have b9239 := hb (x 0 4)
          have b9240 := hb (x 0 12)
          clear * - r9238 b9239 b9240 f9228
          omega
        have d9241 : (x 0 4 && x 0 14).toNat = 0 := by
          have r9242 := hand1 (x 0 4) (x 0 14)
          have b9243 := hb (x 0 4)
          have b9244 := hb (x 0 4 && x 0 14)
          clear * - r9242 b9243 b9244 d9237
          omega
        have d9245 : (x 0 4 && x 0 13).toNat = 0 := by
          have r9246 := hand1 (x 0 4) (x 0 13)
          have b9247 := hb (x 0 4)
          have b9248 := hb (x 0 4 && x 0 13)
          clear * - r9246 b9247 b9248 d9237
          omega
        have d9249 : (x 0 1 && x 0 4).toNat = 0 := by
          have r9250 := hand2 (x 0 1) (x 0 4)
          have b9251 := hb (x 0 4)
          have b9252 := hb (x 0 1 && x 0 4)
          clear * - r9250 b9251 b9252 d9237
          omega
        have d9253 : (x 0 2 && x 0 4).toNat = 0 := by
          have r9254 := hand2 (x 0 2) (x 0 4)
          have b9255 := hb (x 0 4)
          have b9256 := hb (x 0 2 && x 0 4)
          clear * - r9254 b9255 b9256 d9237
          omega
        cases h9257 : x 0 5
        · have f9258 : (x 0 5).toNat = 0 := by rw [h9257]; rfl
          cases h9259 : x 0 6
          · have f9260 : (x 0 6).toNat = 0 := by rw [h9259]; rfl
            have d9261 : (x 0 1 && x 0 6).toNat = 0 := by
              have r9262 := hand2 (x 0 1) (x 0 6)
              have b9263 := hb (x 0 6)
              have b9264 := hb (x 0 1 && x 0 6)
              clear * - r9262 b9263 b9264 f9260
              omega
            have d9265 : (x 0 2 && x 0 6).toNat = 0 := by
              have r9266 := hand2 (x 0 2) (x 0 6)
              have b9267 := hb (x 0 6)
              have b9268 := hb (x 0 2 && x 0 6)
              clear * - r9266 b9267 b9268 f9260
              omega
            cases h9269 : x 0 7
            · have f9270 : (x 0 7).toNat = 0 := by rw [h9269]; rfl
              have d9271 : (x 0 7 && x 0 14).toNat = 0 := by
                have r9272 := hand1 (x 0 7) (x 0 14)
                have b9273 := hb (x 0 7)
                have b9274 := hb (x 0 7 && x 0 14)
                clear * - r9272 b9273 b9274 f9270
                omega
              have d9275 : (x 0 7 && x 0 13).toNat = 0 := by
                have r9276 := hand1 (x 0 7) (x 0 13)
                have b9277 := hb (x 0 7)
                have b9278 := hb (x 0 7 && x 0 13)
                clear * - r9276 b9277 b9278 f9270
                omega
              have d9279 : (x 0 1 && x 0 7).toNat = 0 := by
                have r9280 := hand2 (x 0 1) (x 0 7)
                have b9281 := hb (x 0 7)
                have b9282 := hb (x 0 1 && x 0 7)
                clear * - r9280 b9281 b9282 f9270
                omega
              have d9283 : (x 0 2 && x 0 7).toNat = 0 := by
                have r9284 := hand2 (x 0 2) (x 0 7)
                have b9285 := hb (x 0 7)
                have b9286 := hb (x 0 2 && x 0 7)
                clear * - r9284 b9285 b9286 f9270
                omega
              cases h9287 : x 0 8
              · have f9288 : (x 0 8).toNat = 0 := by rw [h9287]; rfl
                have d9289 : (x 0 8 && x 0 14).toNat = 0 := by
                  have r9290 := hand1 (x 0 8) (x 0 14)
                  have b9291 := hb (x 0 8)
                  have b9292 := hb (x 0 8 && x 0 14)
                  clear * - r9290 b9291 b9292 f9288
                  omega
                have d9293 : (x 0 2 && x 0 8).toNat = 0 := by
                  have r9294 := hand2 (x 0 2) (x 0 8)
                  have b9295 := hb (x 0 8)
                  have b9296 := hb (x 0 2 && x 0 8)
                  clear * - r9294 b9295 b9296 f9288
                  omega
                have d9297 : (x 0 8 && x 0 13).toNat = 0 := by
                  have r9298 := hand1 (x 0 8) (x 0 13)
                  have b9299 := hb (x 0 8)
                  have b9300 := hb (x 0 8 && x 0 13)
                  clear * - r9298 b9299 b9300 f9288
                  omega
                cases h9301 : x 0 9
                · have f9302 : (x 0 9).toNat = 0 := by rw [h9301]; rfl
                  exact cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a1000000 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d9179 d9211 d9151 d2174 d2034 d2058 d9175 d2206 d2002 d9063 g1 g14 d9237 f9258 f9260 f9270 f9288 f9302 d1950 f9228 f9062 d1974 d9099 d9147 d2158 d9083 d9111 d9127 d2122 d2106 d2070 d9253 d2054 d9119 d1966 d9249 d2050 d9203 d2102 d2154 d1962 d9265 d2198 d9143 d9261 d9167 d9199 d9095 d9283 d2194 d9139 d9297 d2066 d2094 d2146 d9279 d9163 d9195 d9293 d2062 d9087 d9275 d2090 d2142 d9289 d2086 d2138 d9271 d9115 d1958 d2186 d9107 d1942 d2014 d1954 d9159 d9191 d9233 d2010 d9103 d1938 d2082 d2134 d9241 d9229 d2006 d9187 d2078 d2130 d1934
                · have f14404 : (x 0 9).toNat = 1 := by rw [h9301]; rfl
                  exact cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a1000001 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d9211 d2034 d9175 d2002 f14404 d9099 d9111 d1954 d9159 d9191 d9233 d2010 d2082 d2134 d9241 d9229 d2006 d9187 d2078 d2130 d1934
              · have f14662 : (x 0 8).toNat = 1 := by rw [h9287]; rfl
                exact cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a100001 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d9211 d2058 d9175 d2002 f9258 f9270 f14662 d1950 f9228 d9111 d1998 d1994 d1990 d9219 d1954 d9159 d9191 d1986
            · have f14979 : (x 0 7).toNat = 1 := by rw [h9269]; rfl
              exact cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a10001 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d2034 d2206 g14 f9258 f9260 f14979 d1974 d9099 d2158 d9083 d9111 d2122 d2106 d2070 d2098 d2150 d2110 d2162 d1954 d9159 d9191 d9233 d2010 d2082 d2134 d9241 d9071 d9229 d2006 d9187
          · have f17023 : (x 0 6).toNat = 1 := by rw [h9259]; rfl
            exact cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a00011 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d2034 f17023 d2158 d2106 d2082 d2134 d9241
        · have f17099 : (x 0 5).toNat = 1 := by rw [h9257]; rfl
          exact cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a101 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d2034 d9237 f17099 d9147 d9111 d9135 d9245 d2038 d1954 d9159 d9191 d9229 d2006 d9187
      · have f17312 : (x 0 12).toNat = 1 := by rw [h9227]; rfl
        have d17313 : (x (-2) 2).toNat = 0 := by
          have r17314 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e17315 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
          have e17316 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
          have b17317 := hb (x (-3) 3)
          have b17318 := hb (x (-2) 2)
          have b17319 := hb (x (-1) 13)
          have b17320 := hb (x 0 12)
          clear * - r17314 e17315 e17316 b17317 b17318 b17319 b17320 f17312 d2002
          omega
        have d17321 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
          have r17322 := hand1 (x (-2) 2) (x (-2) 13)
          have b17323 := hb (x (-2) 2)
          have b17324 := hb (x (-2) 2 && x (-2) 13)
          clear * - r17322 b17323 b17324 d17313
          omega
        have d17325 : (x (-2) 2 && x (-2) 9).toNat = 0 := by
          have r17326 := hand1 (x (-2) 2) (x (-2) 9)
          have b17327 := hb (x (-2) 2)
          have b17328 := hb (x (-2) 2 && x (-2) 9)
          clear * - r17326 b17327 b17328 d17313
          omega
        have d17329 : (x (-2) 10).toNat = 0 := by
          have r17330 : (x (-2) 10).toNat ≤ (x (-2) 2).toNat := himp _ _ (hp10 (-2))
          have b17331 := hb (x (-2) 2)
          have b17332 := hb (x (-2) 10)
          clear * - r17330 b17331 b17332 d17313
          omega
        have d17333 : (x (-2) 1 && x (-2) 10).toNat = 0 := by
          have r17334 := hand2 (x (-2) 1) (x (-2) 10)
          have b17335 := hb (x (-2) 10)
          have b17336 := hb (x (-2) 1 && x (-2) 10)
          clear * - r17334 b17335 b17336 d17329
          omega
        have d17337 : (x (-2) 6 && x (-2) 10).toNat = 0 := by
          have r17338 := hand2 (x (-2) 6) (x (-2) 10)
          have b17339 := hb (x (-2) 10)
          have b17340 := hb (x (-2) 6 && x (-2) 10)
          clear * - r17338 b17339 b17340 d17329
          omega
        have d17341 : (x (-3) 3).toNat = 0 := by
          have r17342 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e17343 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
          have e17344 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
          have b17345 := hb (x (-3) 3)
          have b17346 := hb (x (-2) 2)
          have b17347 := hb (x (-1) 13)
          have b17348 := hb (x 0 12)
          clear * - r17342 e17343 e17344 b17345 b17346 b17347 b17348 f17312 d2002 d17313
          omega
        have d17349 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
          have r17350 := hand1 (x (-3) 3) (x (-3) 14)
          have b17351 := hb (x (-3) 3)
          have b17352 := hb (x (-3) 3 && x (-3) 14)
          clear * - r17350 b17351 b17352 d17341
          omega
        have d17353 : (x (-3) 3 && x (-3) 12).toNat = 0 := by
          have r17354 := hand1 (x (-3) 3) (x (-3) 12)
          have b17355 := hb (x (-3) 3)
          have b17356 := hb (x (-3) 3 && x (-3) 12)
          clear * - r17354 b17355 b17356 d17341
          omega
        have d17357 : (x (-3) 3 && x (-3) 10).toNat = 0 := by
          have r17358 := hand1 (x (-3) 3) (x (-3) 10)
          have b17359 := hb (x (-3) 3)
          have b17360 := hb (x (-3) 3 && x (-3) 10)
          clear * - r17358 b17359 b17360 d17341
          omega
        have d17361 : (x (-3) 11).toNat = 0 := by
          have r17362 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
          have b17363 := hb (x (-3) 3)
          have b17364 := hb (x (-3) 11)
          clear * - r17362 b17363 b17364 d17341
          omega
        have d17365 : (x (-3) 1 && x (-3) 11).toNat = 0 := by
          have r17366 := hand2 (x (-3) 1) (x (-3) 11)
          have b17367 := hb (x (-3) 11)
          have b17368 := hb (x (-3) 1 && x (-3) 11)
          clear * - r17366 b17367 b17368 d17361
          omega
        have d17369 : (x (-3) 2 && x (-3) 11).toNat = 0 := by
          have r17370 := hand2 (x (-3) 2) (x (-3) 11)
          have b17371 := hb (x (-3) 11)
          have b17372 := hb (x (-3) 2 && x (-3) 11)
          clear * - r17370 b17371 b17372 d17361
          omega
        have d17373 : (x (-3) 7 && x (-3) 11).toNat = 0 := by
          have r17374 := hand2 (x (-3) 7) (x (-3) 11)
          have b17375 := hb (x (-3) 11)
          have b17376 := hb (x (-3) 7 && x (-3) 11)
          clear * - r17374 b17375 b17376 d17361
          omega
        have d17377 : (x (-4) 4).toNat = 1 := by
          have r17378 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b17379 := hb (x (-4) 4)
          have b17380 := hb (x 0 11)
          have b17381 := hb (x (-1) 1 && x (-1) 12)
          have b17382 := hb (x (-2) 2 && x (-2) 13)
          have b17383 := hb (x (-3) 3 && x (-3) 14)
          clear * - r17378 b17379 b17380 b17381 b17382 b17383 d1950 d1986 d17321 d17349
          omega
        have d17384 : (x (-4) 12).toNat = 1 := by
          have r17385 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
          have b17386 := hb (x (-4) 4)
          have b17387 := hb (x (-4) 12)
          clear * - r17385 b17386 b17387 d17377
          omega
        have d17388 : (x (-5) 13).toNat = 0 := by
          have r17389 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e17390 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
          have e17391 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
          have b17392 := hb (x (-7) 3)
          have b17393 := hb (x (-6) 2)
          have b17394 := hb (x (-5) 13)
          have b17395 := hb (x (-4) 12)
          clear * - r17389 e17390 e17391 b17392 b17393 b17394 b17395 d17384
          omega
        have d17396 : (x (-5) 3 && x (-5) 13).toNat = 0 := by
          have r17397 := hand2 (x (-5) 3) (x (-5) 13)
          have b17398 := hb (x (-5) 13)
          have b17399 := hb (x (-5) 3 && x (-5) 13)
          clear * - r17397 b17398 b17399 d17388
          omega
        have d17400 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
          have r17401 := hand2 (x (-5) 4) (x (-5) 13)
          have b17402 := hb (x (-5) 13)
          have b17403 := hb (x (-5) 4 && x (-5) 13)
          clear * - r17401 b17402 b17403 d17388
          omega
        have d17404 : (x (-5) 9 && x (-5) 13).toNat = 0 := by
          have r17405 := hand2 (x (-5) 9) (x (-5) 13)
          have b17406 := hb (x (-5) 13)
          have b17407 := hb (x (-5) 9 && x (-5) 13)
          clear * - r17405 b17406 b17407 d17388
          omega
        have d17408 : (x (-5) 5).toNat = 0 := by
          have r17409 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
          have b17410 := hb (x (-5) 5)
          have b17411 := hb (x (-5) 13)
          clear * - r17409 b17410 b17411 d17388
          omega
        have d17412 : (x (-5) 5 && x (-5) 14).toNat = 0 := by
          have r17413 := hand1 (x (-5) 5) (x (-5) 14)
          have b17414 := hb (x (-5) 5)
          have b17415 := hb (x (-5) 5 && x (-5) 14)
          clear * - r17413 b17414 b17415 d17408
          omega
        have d17416 : (x (-5) 5 && x (-5) 12).toNat = 0 := by
          have r17417 := hand1 (x (-5) 5) (x (-5) 12)
          have b17418 := hb (x (-5) 5)
          have b17419 := hb (x (-5) 5 && x (-5) 12)
          clear * - r17417 b17418 b17419 d17408
          omega
        have d17420 : (x (-6) 2).toNat = 0 := by
          have r17421 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e17422 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
          have e17423 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
          have b17424 := hb (x (-7) 3)
          have b17425 := hb (x (-6) 2)
          have b17426 := hb (x (-5) 13)
          have b17427 := hb (x (-4) 12)
          clear * - r17421 e17422 e17423 b17424 b17425 b17426 b17427 d17384 d17388
          omega
        have d17428 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
          have r17429 := hand1 (x (-6) 2) (x (-6) 13)
          have b17430 := hb (x (-6) 2)
          have b17431 := hb (x (-6) 2 && x (-6) 13)
          clear * - r17429 b17430 b17431 d17420
          omega
        have d17432 : (x (-6) 2 && x (-6) 11).toNat = 0 := by
          have r17433 := hand1 (x (-6) 2) (x (-6) 11)
          have b17434 := hb (x (-6) 2)
          have b17435 := hb (x (-6) 2 && x (-6) 11)
          clear * - r17433 b17434 b17435 d17420
          omega
        have d17436 : (x (-6) 10).toNat = 0 := by
          have r17437 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
          have b17438 := hb (x (-6) 2)
          have b17439 := hb (x (-6) 10)
          clear * - r17437 b17438 b17439 d17420
          omega
        have d17440 : (x (-6) 1 && x (-6) 10).toNat = 0 := by
          have r17441 := hand2 (x (-6) 1) (x (-6) 10)
          have b17442 := hb (x (-6) 10)
          have b17443 := hb (x (-6) 1 && x (-6) 10)
          clear * - r17441 b17442 b17443 d17436
          omega
        have d17444 : (x (-6) 5 && x (-6) 10).toNat = 0 := by
          have r17445 := hand2 (x (-6) 5) (x (-6) 10)
          have b17446 := hb (x (-6) 10)
          have b17447 := hb (x (-6) 5 && x (-6) 10)
          clear * - r17445 b17446 b17447 d17436
          omega
        have d17448 : (x (-7) 3).toNat = 0 := by
          have r17449 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e17450 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
          have e17451 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
          have b17452 := hb (x (-7) 3)
          have b17453 := hb (x (-6) 2)
          have b17454 := hb (x (-5) 13)
          have b17455 := hb (x (-4) 12)
          clear * - r17449 e17450 e17451 b17452 b17453 b17454 b17455 d17384 d17388 d17420
          omega
        have d17456 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
          have r17457 := hand1 (x (-7) 3) (x (-7) 14)
          have b17458 := hb (x (-7) 3)
          have b17459 := hb (x (-7) 3 && x (-7) 14)
          clear * - r17457 b17458 b17459 d17448
          omega
        have d17460 : (x (-7) 3 && x (-7) 12).toNat = 0 := by
          have r17461 := hand1 (x (-7) 3) (x (-7) 12)
          have b17462 := hb (x (-7) 3)
          have b17463 := hb (x (-7) 3 && x (-7) 12)
          clear * - r17461 b17462 b17463 d17448
          omega
        have d17464 : (x (-7) 11).toNat = 0 := by
          have r17465 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
          have b17466 := hb (x (-7) 3)
          have b17467 := hb (x (-7) 11)
          clear * - r17465 b17466 b17467 d17448
          omega
        have d17468 : (x (-7) 2 && x (-7) 11).toNat = 0 := by
          have r17469 := hand2 (x (-7) 2) (x (-7) 11)
          have b17470 := hb (x (-7) 11)
          have b17471 := hb (x (-7) 2 && x (-7) 11)
          clear * - r17469 b17470 b17471 d17464
          omega
        have d17472 : (x (-7) 6 && x (-7) 11).toNat = 0 := by
          have r17473 := hand2 (x (-7) 6) (x (-7) 11)
          have b17474 := hb (x (-7) 11)
          have b17475 := hb (x (-7) 6 && x (-7) 11)
          clear * - r17473 b17474 b17475 d17464
          omega
        have d17476 : (x 0 8).toNat = 0 := by
          have r17477 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e17478 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e17479 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e17480 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e17481 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e17482 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e17483 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b17484 := hb (x (-7) 7)
          have b17485 := hb (x (-6) 6)
          have b17486 := hb (x (-5) 5)
          have b17487 := hb (x (-4) 4)
          have b17488 := hb (x (-3) 11)
          have b17489 := hb (x (-2) 10)
          have b17490 := hb (x (-1) 9)
          have b17491 := hb (x 0 8)
          clear * - r17477 e17478 e17479 e17480 e17481 e17482 e17483 b17484 b17485 b17486 b17487 b17488 b17489 b17490 b17491 d2058 d17329 d17361 d17377 d17408
          omega
        have d17492 : (x 0 8 && x 0 13).toNat = 0 := by
          have r17493 := hand1 (x 0 8) (x 0 13)
          have b17494 := hb (x 0 8)
          have b17495 := hb (x 0 8 && x 0 13)
          clear * - r17493 b17494 b17495 d17476
          omega
        have d17496 : (x 0 8 && x 0 12).toNat = 0 := by
          have r17497 := hand1 (x 0 8) (x 0 12)
          have b17498 := hb (x 0 8)
          have b17499 := hb (x 0 8 && x 0 12)
          clear * - r17497 b17498 b17499 d17476
          omega
        have d17500 : (x 0 4 && x 0 8).toNat = 0 := by
          have r17501 := hand2 (x 0 4) (x 0 8)
          have b17502 := hb (x 0 8)
          have b17503 := hb (x 0 4 && x 0 8)
          clear * - r17501 b17502 b17503 d17476
          omega
        have d17504 : (x (-6) 6).toNat = 0 := by
          have r17505 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e17506 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e17507 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e17508 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e17509 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e17510 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e17511 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b17512 := hb (x (-7) 7)
          have b17513 := hb (x (-6) 6)
          have b17514 := hb (x (-5) 5)
          have b17515 := hb (x (-4) 4)
          have b17516 := hb (x (-3) 11)
          have b17517 := hb (x (-2) 10)
          have b17518 := hb (x (-1) 9)
          have b17519 := hb (x 0 8)
          clear * - r17505 e17506 e17507 e17508 e17509 e17510 e17511 b17512 b17513 b17514 b17515 b17516 b17517 b17518 b17519 d17476 d2058 d17329 d17361 d17377 d17408
          omega
        have d17520 : (x (-6) 6 && x (-6) 13).toNat = 0 := by
          have r17521 := hand1 (x (-6) 6) (x (-6) 13)
          have b17522 := hb (x (-6) 6)
          have b17523 := hb (x (-6) 6 && x (-6) 13)
          clear * - r17521 b17522 b17523 d17504
          omega
        have d17524 : (x (-7) 7).toNat = 0 := by
          have r17525 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e17526 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e17527 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e17528 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e17529 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e17530 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e17531 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b17532 := hb (x (-7) 7)
          have b17533 := hb (x (-6) 6)
          have b17534 := hb (x (-5) 5)
          have b17535 := hb (x (-4) 4)
          have b17536 := hb (x (-3) 11)
          have b17537 := hb (x (-2) 10)
          have b17538 := hb (x (-1) 9)
          have b17539 := hb (x 0 8)
          clear * - r17525 e17526 e17527 e17528 e17529 e17530 e17531 b17532 b17533 b17534 b17535 b17536 b17537 b17538 b17539 d17476 d2058 d17329 d17361 d17377 d17408 d17504
          omega
        have d17540 : (x (-7) 7 && x (-7) 14).toNat = 0 := by
          have r17541 := hand1 (x (-7) 7) (x (-7) 14)
          have b17542 := hb (x (-7) 7)
          have b17543 := hb (x (-7) 7 && x (-7) 14)
          clear * - r17541 b17542 b17543 d17524
          omega
        cases h17544 : x 0 4
        · have f17545 : (x 0 4).toNat = 0 := by rw [h17544]; rfl
          have d17546 : (x 0 4 && x 0 14).toNat = 0 := by
            have r17547 := hand1 (x 0 4) (x 0 14)
            have b17548 := hb (x 0 4)
            have b17549 := hb (x 0 4 && x 0 14)
            clear * - r17547 b17548 b17549 f17545
            omega
          have d17550 : (x 0 4 && x 0 13).toNat = 0 := by
            have r17551 := hand1 (x 0 4) (x 0 13)
            have b17552 := hb (x 0 4)
            have b17553 := hb (x 0 4 && x 0 13)
            clear * - r17551 b17552 b17553 f17545
            omega
          have d17554 : (x 0 4 && x 0 9).toNat = 0 := by
            have r17555 := hand1 (x 0 4) (x 0 9)
            have b17556 := hb (x 0 4)
            have b17557 := hb (x 0 4 && x 0 9)
            clear * - r17555 b17556 b17557 f17545
            omega
          cases h17558 : x 0 5
          · have f17559 : (x 0 5).toNat = 0 := by rw [h17558]; rfl
            exact cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a1100 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d17464 d17504 d17436 d17388 d9179 d9211 d9151 d2174 d2034 d2058 d9175 d2206 d2002 d9063 g1 g14 f17545 f17559 d17476 d1950 f17312 f9062 d1974 d9099 d9147 d2158 d9083 d9111 d9127 d2122 d9067 d2106 d2070 d9123 d1970 d2030 d1946 d9171 d9207 d2102 d2154 d1962 d17500 d2046 d17337 d17373 d17404 d17444 d17472 d9095 d2194 d9091 d2022 d9079 d9075 d17440 d17468 d17333 d17369 d17400 d1990 d9219 d17353 d17412 d9115 d1958 d2186 d9107 d1942 d2014 d2110 d2162 d9215 d1954 d9159 d9191 d9103 d1938 d2082 d2134 d17546 d9071 d17428 d17456 d2078 d2130 d1934
          · have f22094 : (x 0 5).toNat = 1 := by rw [h17558]; rfl
            exact cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a1101 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d17464 d17504 d17436 d17388 d17384 d17361 d17329 d9211 d2034 d2058 d9175 d2206 f17545 f22094 d17476 d1950 d1974 d9099 d9147 d2158 d9083 d9111 d2122 d2106 d2070 d17500 d2046 d17337 d17373 d17404 d17554 d2042 d9223 d9139 d17492 d2066 d1994 d17325 d17357 d17416 d17520 d17540 d17432 d17460 d17333 d17369 d17400 d1990 d9219 d17353 d17412 d9107 d1942 d2014 d9135 d17550 d2038 d9215 d1954 d9159 d9191 d2082 d2134 d17546 d17428 d17456 d2078 d2130 d1934
        · have f24274 : (x 0 4).toNat = 1 := by rw [h17544]; rfl
          exact cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a111 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d17504 d17361 d17329 d9211 d2034 d2058 d9175 d2206 f24274 d2158 d9111 d2106 d17496 d2026 d2114 d2166 d2018 d17333 d17369 d17400 d1990 d9219 d17353 d17412 d9107 d1942 d2014 d17365 d17396 d1954 d9159 d9191 d2078 d2130 d1934
  · rfl

theorem cycle_power_fifteen_tight_type_sequence_two_iff_three_core (x : ℤ → Fin 16 → Bool)
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
    : x 0 2 = x 0 3 := cycle_power_fifteen_tight_type_sequence_two_iff_three_core_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13
