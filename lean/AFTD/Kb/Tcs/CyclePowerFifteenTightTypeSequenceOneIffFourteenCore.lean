import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneIffFourteenCoreB00000
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneIffFourteenCoreB0000100
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneIffFourteenCoreB0000101
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneIffFourteenCoreB000011
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneIffFourteenCoreB0001
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneIffFourteenCoreB001
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneIffFourteenCoreB01
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneIffFourteenCoreB1
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneIffFourteenCoreA000000
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneIffFourteenCoreA000001
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneIffFourteenCoreA0000100
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneIffFourteenCoreA0000101
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneIffFourteenCoreA00001100000
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneIffFourteenCoreA000011000010
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneIffFourteenCoreA0000110000110
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneIffFourteenCoreA0000110000111
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneIffFourteenCoreA0000110001
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneIffFourteenCoreA000011001
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneIffFourteenCoreA00001101
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneIffFourteenCoreA0000111
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneIffFourteenCoreA0001
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneIffFourteenCoreA001
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneIffFourteenCoreA01000
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneIffFourteenCoreA01001
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneIffFourteenCoreA0101
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneIffFourteenCoreA011
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneIffFourteenCoreA1

/-!
# cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core

Topic: combinatorics   Node: 43780b47e5cd

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP.

Layer-free one_iff_fourteen for tight five-layer covers of C_n^15, on the integer line. Let x p j say that the class starting at p (the class of the distance-15 pair (p, p+15)) contains p + j. Assume every vertex is an inner element (offsets 1..14) of exactly three classes; every pair at distance 14, 12, 8 is covered exactly once; every pair at distance 1..7, 9, 10, 11, 13 is covered; and every class is closed under the parent map of the tight-class forest (2→14, 4→12, 5→13, 6→14, 9→1, 10→2, 11→3, 13→1). Then the class at 0 contains 1 exactly when it contains 14.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_aux (x : ℤ → Fin 16 → Bool)
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
    : x 0 1 = x 0 14 := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  cases h01 : x 0 1 <;> cases h014 : x 0 14
  · rfl
  · exfalso
    have g1 : (x 0 1).toNat = 0 := by rw [h01]; rfl
    have g14 : (x 0 14).toNat = 1 := by rw [h014]; rfl
    have d1 : (x 0 1 && x 0 14).toNat = 0 := by
      have r2 := hand1 (x 0 1) (x 0 14)
      have b3 := hb (x 0 1)
      have b4 := hb (x 0 1 && x 0 14)
      clear * - r2 b3 b4 g1
      omega
    have d5 : (x 0 1 && x 0 12).toNat = 0 := by
      have r6 := hand1 (x 0 1) (x 0 12)
      have b7 := hb (x 0 1)
      have b8 := hb (x 0 1 && x 0 12)
      clear * - r6 b7 b8 g1
      omega
    have d9 : (x 0 1 && x 0 10).toNat = 0 := by
      have r10 := hand1 (x 0 1) (x 0 10)
      have b11 := hb (x 0 1)
      have b12 := hb (x 0 1 && x 0 10)
      clear * - r10 b11 b12 g1
      omega
    have d13 : (x 0 1 && x 0 8).toNat = 0 := by
      have r14 := hand1 (x 0 1) (x 0 8)
      have b15 := hb (x 0 1)
      have b16 := hb (x 0 1 && x 0 8)
      clear * - r14 b15 b16 g1
      omega
    have d17 : (x 0 1 && x 0 6).toNat = 0 := by
      have r18 := hand1 (x 0 1) (x 0 6)
      have b19 := hb (x 0 1)
      have b20 := hb (x 0 1 && x 0 6)
      clear * - r18 b19 b20 g1
      omega
    have d21 : (x 0 13).toNat = 0 := by
      have r22 : (x 0 13).toNat ≤ (x 0 1).toNat := himp _ _ (hp13 0)
      have b23 := hb (x 0 1)
      have b24 := hb (x 0 13)
      clear * - r22 b23 b24 g1
      omega
    have d25 : (x 0 2 && x 0 13).toNat = 0 := by
      have r26 := hand2 (x 0 2) (x 0 13)
      have b27 := hb (x 0 13)
      have b28 := hb (x 0 2 && x 0 13)
      clear * - r26 b27 b28 d21
      omega
    have d29 : (x 0 4 && x 0 13).toNat = 0 := by
      have r30 := hand2 (x 0 4) (x 0 13)
      have b31 := hb (x 0 13)
      have b32 := hb (x 0 4 && x 0 13)
      clear * - r30 b31 b32 d21
      omega
    have d33 : (x 0 9 && x 0 13).toNat = 0 := by
      have r34 := hand2 (x 0 9) (x 0 13)
      have b35 := hb (x 0 13)
      have b36 := hb (x 0 9 && x 0 13)
      clear * - r34 b35 b36 d21
      omega
    have d37 : (x 0 13 && x 0 14).toNat = 0 := by
      have r38 := hand1 (x 0 13) (x 0 14)
      have b39 := hb (x 0 13)
      have b40 := hb (x 0 13 && x 0 14)
      clear * - r38 b39 b40 d21
      omega
    have d41 : (x 0 9).toNat = 0 := by
      have r42 : (x 0 9).toNat ≤ (x 0 1).toNat := himp _ _ (hp9 0)
      have b43 := hb (x 0 1)
      have b44 := hb (x 0 9)
      clear * - r42 b43 b44 g1
      omega
    have d45 : (x 0 9 && x 0 14).toNat = 0 := by
      have r46 := hand1 (x 0 9) (x 0 14)
      have b47 := hb (x 0 9)
      have b48 := hb (x 0 9 && x 0 14)
      clear * - r46 b47 b48 d41
      omega
    have d49 : (x 0 5).toNat = 0 := by
      have r50 : (x 0 5).toNat ≤ (x 0 13).toNat := himp _ _ (hp5 0)
      have b51 := hb (x 0 5)
      have b52 := hb (x 0 13)
      clear * - r50 b51 b52 d21
      omega
    have d53 : (x 0 5 && x 0 14).toNat = 0 := by
      have r54 := hand1 (x 0 5) (x 0 14)
      have b55 := hb (x 0 5)
      have b56 := hb (x 0 5 && x 0 14)
      clear * - r54 b55 b56 d49
      omega
    have d57 : (x 0 2 && x 0 5).toNat = 0 := by
      have r58 := hand2 (x 0 2) (x 0 5)
      have b59 := hb (x 0 5)
      have b60 := hb (x 0 2 && x 0 5)
      clear * - r58 b59 b60 d49
      omega
    have d61 : (x 0 4 && x 0 5).toNat = 0 := by
      have r62 := hand2 (x 0 4) (x 0 5)
      have b63 := hb (x 0 5)
      have b64 := hb (x 0 4 && x 0 5)
      clear * - r62 b63 b64 d49
      omega
    have d65 : (x 1 14).toNat = 1 := by
      have r66 : (x 1 14).toNat + (x 0 1).toNat = 1 := hd14 1
      have b67 := hb (x 0 1)
      have b68 := hb (x 1 14)
      clear * - r66 b67 b68 g1
      omega
    have d69 : (x (-1) 1).toNat = 0 := by
      have r70 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := hd14 0
      have b71 := hb (x (-1) 1)
      have b72 := hb (x 0 14)
      clear * - r70 b71 b72 g14
      omega
    have d73 : (x (-1) 1 && x (-1) 14).toNat = 0 := by
      have r74 := hand1 (x (-1) 1) (x (-1) 14)
      have b75 := hb (x (-1) 1)
      have b76 := hb (x (-1) 1 && x (-1) 14)
      clear * - r74 b75 b76 d69
      omega
    have d77 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
      have r78 := hand1 (x (-1) 1) (x (-1) 12)
      have b79 := hb (x (-1) 1)
      have b80 := hb (x (-1) 1 && x (-1) 12)
      clear * - r78 b79 b80 d69
      omega
    have d81 : (x (-1) 1 && x (-1) 11).toNat = 0 := by
      have r82 := hand1 (x (-1) 1) (x (-1) 11)
      have b83 := hb (x (-1) 1)
      have b84 := hb (x (-1) 1 && x (-1) 11)
      clear * - r82 b83 b84 d69
      omega
    have d85 : (x (-1) 1 && x (-1) 10).toNat = 0 := by
      have r86 := hand1 (x (-1) 1) (x (-1) 10)
      have b87 := hb (x (-1) 1)
      have b88 := hb (x (-1) 1 && x (-1) 10)
      clear * - r86 b87 b88 d69
      omega
    have d89 : (x (-1) 1 && x (-1) 8).toNat = 0 := by
      have r90 := hand1 (x (-1) 1) (x (-1) 8)
      have b91 := hb (x (-1) 1)
      have b92 := hb (x (-1) 1 && x (-1) 8)
      clear * - r90 b91 b92 d69
      omega
    have d93 : (x (-1) 1 && x (-1) 6).toNat = 0 := by
      have r94 := hand1 (x (-1) 1) (x (-1) 6)
      have b95 := hb (x (-1) 1)
      have b96 := hb (x (-1) 1 && x (-1) 6)
      clear * - r94 b95 b96 d69
      omega
    have d97 : (x (-1) 13).toNat = 0 := by
      have r98 : (x (-1) 13).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp13 (-1))
      have b99 := hb (x (-1) 1)
      have b100 := hb (x (-1) 13)
      clear * - r98 b99 b100 d69
      omega
    have d101 : (x (-1) 2 && x (-1) 13).toNat = 0 := by
      have r102 := hand2 (x (-1) 2) (x (-1) 13)
      have b103 := hb (x (-1) 13)
      have b104 := hb (x (-1) 2 && x (-1) 13)
      clear * - r102 b103 b104 d97
      omega
    have d105 : (x (-1) 3 && x (-1) 13).toNat = 0 := by
      have r106 := hand2 (x (-1) 3) (x (-1) 13)
      have b107 := hb (x (-1) 13)
      have b108 := hb (x (-1) 3 && x (-1) 13)
      clear * - r106 b107 b108 d97
      omega
    have d109 : (x (-1) 4 && x (-1) 13).toNat = 0 := by
      have r110 := hand2 (x (-1) 4) (x (-1) 13)
      have b111 := hb (x (-1) 13)
      have b112 := hb (x (-1) 4 && x (-1) 13)
      clear * - r110 b111 b112 d97
      omega
    have d113 : (x (-1) 8 && x (-1) 13).toNat = 0 := by
      have r114 := hand2 (x (-1) 8) (x (-1) 13)
      have b115 := hb (x (-1) 13)
      have b116 := hb (x (-1) 8 && x (-1) 13)
      clear * - r114 b115 b116 d97
      omega
    have d117 : (x (-1) 9 && x (-1) 13).toNat = 0 := by
      have r118 := hand2 (x (-1) 9) (x (-1) 13)
      have b119 := hb (x (-1) 13)
      have b120 := hb (x (-1) 9 && x (-1) 13)
      clear * - r118 b119 b120 d97
      omega
    have d121 : (x (-1) 5).toNat = 0 := by
      have r122 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
      have b123 := hb (x (-1) 5)
      have b124 := hb (x (-1) 13)
      clear * - r122 b123 b124 d97
      omega
    have d125 : (x (-1) 5 && x (-1) 14).toNat = 0 := by
      have r126 := hand1 (x (-1) 5) (x (-1) 14)
      have b127 := hb (x (-1) 5)
      have b128 := hb (x (-1) 5 && x (-1) 14)
      clear * - r126 b127 b128 d121
      omega
    have d129 : (x (-1) 5 && x (-1) 9).toNat = 0 := by
      have r130 := hand1 (x (-1) 5) (x (-1) 9)
      have b131 := hb (x (-1) 5)
      have b132 := hb (x (-1) 5 && x (-1) 9)
      clear * - r130 b131 b132 d121
      omega
    have d133 : (x (-1) 5 && x (-1) 6).toNat = 0 := by
      have r134 := hand1 (x (-1) 5) (x (-1) 6)
      have b135 := hb (x (-1) 5)
      have b136 := hb (x (-1) 5 && x (-1) 6)
      clear * - r134 b135 b136 d121
      omega
    have d137 : (x (-1) 9).toNat = 0 := by
      have r138 : (x (-1) 9).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp9 (-1))
      have b139 := hb (x (-1) 1)
      have b140 := hb (x (-1) 9)
      clear * - r138 b139 b140 d69
      omega
    have d141 : (x (-1) 2 && x (-1) 9).toNat = 0 := by
      have r142 := hand2 (x (-1) 2) (x (-1) 9)
      have b143 := hb (x (-1) 9)
      have b144 := hb (x (-1) 2 && x (-1) 9)
      clear * - r142 b143 b144 d137
      omega
    have d145 : (x (-1) 3 && x (-1) 9).toNat = 0 := by
      have r146 := hand2 (x (-1) 3) (x (-1) 9)
      have b147 := hb (x (-1) 9)
      have b148 := hb (x (-1) 3 && x (-1) 9)
      clear * - r146 b147 b148 d137
      omega
    have d149 : (x (-2) 2).toNat = 1 := by
      have r150 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := hcov13 0
      have b151 := hb (x (-2) 2)
      have b152 := hb (x 0 13)
      have b153 := hb (x (-1) 1 && x (-1) 14)
      clear * - r150 b151 b152 b153 d21 d73
      omega
    have d154 : (x (-2) 14).toNat = 1 := by
      have r155 : (x (-2) 2).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp2 (-2))
      have b156 := hb (x (-2) 2)
      have b157 := hb (x (-2) 14)
      clear * - r155 b156 b157 d149
      omega
    have d158 : (x (-3) 1).toNat = 0 := by
      have r159 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := hd14 (-2)
      have b160 := hb (x (-3) 1)
      have b161 := hb (x (-2) 14)
      clear * - r159 b160 b161 d154
      omega
    have d162 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
      have r163 := hand1 (x (-3) 1) (x (-3) 14)
      have b164 := hb (x (-3) 1)
      have b165 := hb (x (-3) 1 && x (-3) 14)
      clear * - r163 b164 b165 d158
      omega
    have d166 : (x (-3) 1 && x (-3) 10).toNat = 0 := by
      have r167 := hand1 (x (-3) 1) (x (-3) 10)
      have b168 := hb (x (-3) 1)
      have b169 := hb (x (-3) 1 && x (-3) 10)
      clear * - r167 b168 b169 d158
      omega
    have d170 : (x (-3) 13).toNat = 0 := by
      have r171 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
      have b172 := hb (x (-3) 1)
      have b173 := hb (x (-3) 13)
      clear * - r171 b172 b173 d158
      omega
    have d174 : (x (-3) 2 && x (-3) 13).toNat = 0 := by
      have r175 := hand2 (x (-3) 2) (x (-3) 13)
      have b176 := hb (x (-3) 13)
      have b177 := hb (x (-3) 2 && x (-3) 13)
      clear * - r175 b176 b177 d170
      omega
    have d178 : (x (-3) 3 && x (-3) 13).toNat = 0 := by
      have r179 := hand2 (x (-3) 3) (x (-3) 13)
      have b180 := hb (x (-3) 13)
      have b181 := hb (x (-3) 3 && x (-3) 13)
      clear * - r179 b180 b181 d170
      omega
    have d182 : (x (-3) 4 && x (-3) 13).toNat = 0 := by
      have r183 := hand2 (x (-3) 4) (x (-3) 13)
      have b184 := hb (x (-3) 13)
      have b185 := hb (x (-3) 4 && x (-3) 13)
      clear * - r183 b184 b185 d170
      omega
    have d186 : (x (-3) 5).toNat = 0 := by
      have r187 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
      have b188 := hb (x (-3) 5)
      have b189 := hb (x (-3) 13)
      clear * - r187 b188 b189 d170
      omega
    have d190 : (x (-3) 5 && x (-3) 14).toNat = 0 := by
      have r191 := hand1 (x (-3) 5) (x (-3) 14)
      have b192 := hb (x (-3) 5)
      have b193 := hb (x (-3) 5 && x (-3) 14)
      clear * - r191 b192 b193 d186
      omega
    have d194 : (x (-3) 5 && x (-3) 11).toNat = 0 := by
      have r195 := hand1 (x (-3) 5) (x (-3) 11)
      have b196 := hb (x (-3) 5)
      have b197 := hb (x (-3) 5 && x (-3) 11)
      clear * - r195 b196 b197 d186
      omega
    have d198 : (x (-3) 5 && x (-3) 8).toNat = 0 := by
      have r199 := hand1 (x (-3) 5) (x (-3) 8)
      have b200 := hb (x (-3) 5)
      have b201 := hb (x (-3) 5 && x (-3) 8)
      clear * - r199 b200 b201 d186
      omega
    have d202 : (x (-3) 9).toNat = 0 := by
      have r203 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
      have b204 := hb (x (-3) 1)
      have b205 := hb (x (-3) 9)
      clear * - r203 b204 b205 d158
      omega
    have d206 : (x (-3) 4 && x (-3) 9).toNat = 0 := by
      have r207 := hand2 (x (-3) 4) (x (-3) 9)
      have b208 := hb (x (-3) 9)
      have b209 := hb (x (-3) 4 && x (-3) 9)
      clear * - r207 b208 b209 d202
      omega
    have d210 : (x 0 12).toNat = 0 := by
      have r211 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := hd12 0
      have e212 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e213 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have b214 := hb (x (-3) 3)
      have b215 := hb (x (-2) 2)
      have b216 := hb (x (-1) 13)
      have b217 := hb (x 0 12)
      clear * - r211 e212 e213 b214 b215 b216 b217 d97 d149
      omega
    have d218 : (x 0 2 && x 0 12).toNat = 0 := by
      have r219 := hand2 (x 0 2) (x 0 12)
      have b220 := hb (x 0 12)
      have b221 := hb (x 0 2 && x 0 12)
      clear * - r219 b220 b221 d210
      omega
    have d222 : (x 0 3 && x 0 12).toNat = 0 := by
      have r223 := hand2 (x 0 3) (x 0 12)
      have b224 := hb (x 0 12)
      have b225 := hb (x 0 3 && x 0 12)
      clear * - r223 b224 b225 d210
      omega
    have d226 : (x 0 7 && x 0 12).toNat = 0 := by
      have r227 := hand2 (x 0 7) (x 0 12)
      have b228 := hb (x 0 12)
      have b229 := hb (x 0 7 && x 0 12)
      clear * - r227 b228 b229 d210
      omega
    have d230 : (x 0 8 && x 0 12).toNat = 0 := by
      have r231 := hand2 (x 0 8) (x 0 12)
      have b232 := hb (x 0 12)
      have b233 := hb (x 0 8 && x 0 12)
      clear * - r231 b232 b233 d210
      omega
    have d234 : (x 0 4).toNat = 0 := by
      have r235 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
      have b236 := hb (x 0 4)
      have b237 := hb (x 0 12)
      clear * - r235 b236 b237 d210
      omega
    have d238 : (x 0 4 && x 0 14).toNat = 0 := by
      have r239 := hand1 (x 0 4) (x 0 14)
      have b240 := hb (x 0 4)
      have b241 := hb (x 0 4 && x 0 14)
      clear * - r239 b240 b241 d234
      omega
    have d242 : (x 0 4 && x 0 8).toNat = 0 := by
      have r243 := hand1 (x 0 4) (x 0 8)
      have b244 := hb (x 0 4)
      have b245 := hb (x 0 4 && x 0 8)
      clear * - r243 b244 b245 d234
      omega
    have d246 : (x (-3) 3).toNat = 0 := by
      have r247 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := hd12 0
      have e248 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e249 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have b250 := hb (x (-3) 3)
      have b251 := hb (x (-2) 2)
      have b252 := hb (x (-1) 13)
      have b253 := hb (x 0 12)
      clear * - r247 e248 e249 b250 b251 b252 b253 d210 d97 d149
      omega
    have d254 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
      have r255 := hand1 (x (-3) 3) (x (-3) 14)
      have b256 := hb (x (-3) 3)
      have b257 := hb (x (-3) 3 && x (-3) 14)
      clear * - r255 b256 b257 d246
      omega
    have d258 : (x (-3) 3 && x (-3) 12).toNat = 0 := by
      have r259 := hand1 (x (-3) 3) (x (-3) 12)
      have b260 := hb (x (-3) 3)
      have b261 := hb (x (-3) 3 && x (-3) 12)
      clear * - r259 b260 b261 d246
      omega
    have d262 : (x (-3) 3 && x (-3) 10).toNat = 0 := by
      have r263 := hand1 (x (-3) 3) (x (-3) 10)
      have b264 := hb (x (-3) 3)
      have b265 := hb (x (-3) 3 && x (-3) 10)
      clear * - r263 b264 b265 d246
      omega
    have d266 : (x (-3) 3 && x (-3) 8).toNat = 0 := by
      have r267 := hand1 (x (-3) 3) (x (-3) 8)
      have b268 := hb (x (-3) 3)
      have b269 := hb (x (-3) 3 && x (-3) 8)
      clear * - r267 b268 b269 d246
      omega
    have d270 : (x (-3) 11).toNat = 0 := by
      have r271 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
      have b272 := hb (x (-3) 3)
      have b273 := hb (x (-3) 11)
      clear * - r271 b272 b273 d246
      omega
    have d274 : (x (-3) 2 && x (-3) 11).toNat = 0 := by
      have r275 := hand2 (x (-3) 2) (x (-3) 11)
      have b276 := hb (x (-3) 11)
      have b277 := hb (x (-3) 2 && x (-3) 11)
      clear * - r275 b276 b277 d270
      omega
    have d278 : (x (-3) 4 && x (-3) 11).toNat = 0 := by
      have r279 := hand2 (x (-3) 4) (x (-3) 11)
      have b280 := hb (x (-3) 11)
      have b281 := hb (x (-3) 4 && x (-3) 11)
      clear * - r279 b280 b281 d270
      omega
    have d282 : (x (-3) 7 && x (-3) 11).toNat = 0 := by
      have r283 := hand2 (x (-3) 7) (x (-3) 11)
      have b284 := hb (x (-3) 11)
      have b285 := hb (x (-3) 7 && x (-3) 11)
      clear * - r283 b284 b285 d270
      omega
    cases h286 : x 0 2
    · have f287 : (x 0 2).toNat = 0 := by rw [h286]; rfl
      have d288 : (x 0 2 && x 0 11).toNat = 0 := by
        have r289 := hand1 (x 0 2) (x 0 11)
        have b290 := hb (x 0 2)
        have b291 := hb (x 0 2 && x 0 11)
        clear * - r289 b290 b291 f287
        omega
      have d292 : (x 0 2 && x 0 8).toNat = 0 := by
        have r293 := hand1 (x 0 2) (x 0 8)
        have b294 := hb (x 0 2)
        have b295 := hb (x 0 2 && x 0 8)
        clear * - r293 b294 b295 f287
        omega
      have d296 : (x 0 10).toNat = 0 := by
        have r297 : (x 0 10).toNat ≤ (x 0 2).toNat := himp _ _ (hp10 0)
        have b298 := hb (x 0 2)
        have b299 := hb (x 0 10)
        clear * - r297 b298 b299 f287
        omega
      cases h300 : x 0 7
      · have f301 : (x 0 7).toNat = 0 := by rw [h300]; rfl
        have d302 : (x 0 7 && x 0 14).toNat = 0 := by
          have r303 := hand1 (x 0 7) (x 0 14)
          have b304 := hb (x 0 7)
          have b305 := hb (x 0 7 && x 0 14)
          clear * - r303 b304 b305 f301
          omega
        cases h306 : x 0 8
        · have f307 : (x 0 8).toNat = 0 := by rw [h306]; rfl
          have d308 : (x 0 8 && x 0 14).toNat = 0 := by
            have r309 := hand1 (x 0 8) (x 0 14)
            have b310 := hb (x 0 8)
            have b311 := hb (x 0 8 && x 0 14)
            clear * - r309 b310 b311 f307
            omega
          cases h312 : x 0 3
          · have f313 : (x 0 3).toNat = 0 := by rw [h312]; rfl
            have d314 : (x 0 3 && x 0 14).toNat = 0 := by
              have r315 := hand1 (x 0 3) (x 0 14)
              have b316 := hb (x 0 3)
              have b317 := hb (x 0 3 && x 0 14)
              clear * - r315 b316 b317 f313
              omega
            have d318 : (x 0 11).toNat = 0 := by
              have r319 : (x 0 11).toNat ≤ (x 0 3).toNat := himp _ _ (hp11 0)
              have b320 := hb (x 0 3)
              have b321 := hb (x 0 11)
              clear * - r319 b320 b321 f313
              omega
            cases h322 : x 1 3
            · have f323 : (x 1 3).toNat = 0 := by rw [h322]; rfl
              exact cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b00000 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d186 d270 d170 d121 d97 f287 f313 d234 d49 f301 d296 d318 d21 g14 f323 d65 d57 d198 d222 d109 d29 d125 d81 d178 d218 d105 d238 d77 d254 d5 d101 d314 d162 d1
            · have f4285 : (x 1 3).toNat = 1 := by rw [h322]; rfl
              have d4286 : (x 4 12).toNat = 0 := by
                have r4287 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
                have e4288 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e4289 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b4290 := hb (x 1 3)
                have b4291 := hb (x 2 2)
                have b4292 := hb (x 3 13)
                have b4293 := hb (x 4 12)
                clear * - r4287 e4288 e4289 b4290 b4291 b4292 b4293 f4285
                omega
              have d4294 : (x 4 1 && x 4 12).toNat = 0 := by
                have r4295 := hand2 (x 4 1) (x 4 12)
                have b4296 := hb (x 4 12)
                have b4297 := hb (x 4 1 && x 4 12)
                clear * - r4295 b4296 b4297 d4286
                omega
              have d4298 : (x 4 2 && x 4 12).toNat = 0 := by
                have r4299 := hand2 (x 4 2) (x 4 12)
                have b4300 := hb (x 4 12)
                have b4301 := hb (x 4 2 && x 4 12)
                clear * - r4299 b4300 b4301 d4286
                omega
              have d4302 : (x 4 3 && x 4 12).toNat = 0 := by
                have r4303 := hand2 (x 4 3) (x 4 12)
                have b4304 := hb (x 4 12)
                have b4305 := hb (x 4 3 && x 4 12)
                clear * - r4303 b4304 b4305 d4286
                omega
              have d4306 : (x 4 5 && x 4 12).toNat = 0 := by
                have r4307 := hand2 (x 4 5) (x 4 12)
                have b4308 := hb (x 4 12)
                have b4309 := hb (x 4 5 && x 4 12)
                clear * - r4307 b4308 b4309 d4286
                omega
              have d4310 : (x 4 6 && x 4 12).toNat = 0 := by
                have r4311 := hand2 (x 4 6) (x 4 12)
                have b4312 := hb (x 4 12)
                have b4313 := hb (x 4 6 && x 4 12)
                clear * - r4311 b4312 b4313 d4286
                omega
              have d4314 : (x 4 7 && x 4 12).toNat = 0 := by
                have r4315 := hand2 (x 4 7) (x 4 12)
                have b4316 := hb (x 4 12)
                have b4317 := hb (x 4 7 && x 4 12)
                clear * - r4315 b4316 b4317 d4286
                omega
              have d4318 : (x 4 4).toNat = 0 := by
                have r4319 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
                have b4320 := hb (x 4 4)
                have b4321 := hb (x 4 12)
                clear * - r4319 b4320 b4321 d4286
                omega
              have d4322 : (x 4 4 && x 4 14).toNat = 0 := by
                have r4323 := hand1 (x 4 4) (x 4 14)
                have b4324 := hb (x 4 4)
                have b4325 := hb (x 4 4 && x 4 14)
                clear * - r4323 b4324 b4325 d4318
                omega
              have d4326 : (x 4 4 && x 4 13).toNat = 0 := by
                have r4327 := hand1 (x 4 4) (x 4 13)
                have b4328 := hb (x 4 4)
                have b4329 := hb (x 4 4 && x 4 13)
                clear * - r4327 b4328 b4329 d4318
                omega
              have d4330 : (x 4 4 && x 4 11).toNat = 0 := by
                have r4331 := hand1 (x 4 4) (x 4 11)
                have b4332 := hb (x 4 4)
                have b4333 := hb (x 4 4 && x 4 11)
                clear * - r4331 b4332 b4333 d4318
                omega
              have d4334 : (x 4 4 && x 4 10).toNat = 0 := by
                have r4335 := hand1 (x 4 4) (x 4 10)
                have b4336 := hb (x 4 4)
                have b4337 := hb (x 4 4 && x 4 10)
                clear * - r4335 b4336 b4337 d4318
                omega
              have d4338 : (x 4 4 && x 4 8).toNat = 0 := by
                have r4339 := hand1 (x 4 4) (x 4 8)
                have b4340 := hb (x 4 4)
                have b4341 := hb (x 4 4 && x 4 8)
                clear * - r4339 b4340 b4341 d4318
                omega
              have d4342 : (x 3 13).toNat = 0 := by
                have r4343 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
                have e4344 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e4345 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b4346 := hb (x 1 3)
                have b4347 := hb (x 2 2)
                have b4348 := hb (x 3 13)
                have b4349 := hb (x 4 12)
                clear * - r4343 e4344 e4345 b4346 b4347 b4348 b4349 d4286 f4285
                omega
              have d4350 : (x 3 2 && x 3 13).toNat = 0 := by
                have r4351 := hand2 (x 3 2) (x 3 13)
                have b4352 := hb (x 3 13)
                have b4353 := hb (x 3 2 && x 3 13)
                clear * - r4351 b4352 b4353 d4342
                omega
              have d4354 : (x 3 3 && x 3 13).toNat = 0 := by
                have r4355 := hand2 (x 3 3) (x 3 13)
                have b4356 := hb (x 3 13)
                have b4357 := hb (x 3 3 && x 3 13)
                clear * - r4355 b4356 b4357 d4342
                omega
              have d4358 : (x 3 4 && x 3 13).toNat = 0 := by
                have r4359 := hand2 (x 3 4) (x 3 13)
                have b4360 := hb (x 3 13)
                have b4361 := hb (x 3 4 && x 3 13)
                clear * - r4359 b4360 b4361 d4342
                omega
              have d4362 : (x 3 6 && x 3 13).toNat = 0 := by
                have r4363 := hand2 (x 3 6) (x 3 13)
                have b4364 := hb (x 3 13)
                have b4365 := hb (x 3 6 && x 3 13)
                clear * - r4363 b4364 b4365 d4342
                omega
              have d4366 : (x 3 7 && x 3 13).toNat = 0 := by
                have r4367 := hand2 (x 3 7) (x 3 13)
                have b4368 := hb (x 3 13)
                have b4369 := hb (x 3 7 && x 3 13)
                clear * - r4367 b4368 b4369 d4342
                omega
              have d4370 : (x 3 8 && x 3 13).toNat = 0 := by
                have r4371 := hand2 (x 3 8) (x 3 13)
                have b4372 := hb (x 3 13)
                have b4373 := hb (x 3 8 && x 3 13)
                clear * - r4371 b4372 b4373 d4342
                omega
              have d4374 : (x 3 5).toNat = 0 := by
                have r4375 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
                have b4376 := hb (x 3 5)
                have b4377 := hb (x 3 13)
                clear * - r4375 b4376 b4377 d4342
                omega
              have d4378 : (x 3 5 && x 3 14).toNat = 0 := by
                have r4379 := hand1 (x 3 5) (x 3 14)
                have b4380 := hb (x 3 5)
                have b4381 := hb (x 3 5 && x 3 14)
                clear * - r4379 b4380 b4381 d4374
                omega
              have d4382 : (x 3 5 && x 3 12).toNat = 0 := by
                have r4383 := hand1 (x 3 5) (x 3 12)
                have b4384 := hb (x 3 5)
                have b4385 := hb (x 3 5 && x 3 12)
                clear * - r4383 b4384 b4385 d4374
                omega
              have d4386 : (x 3 5 && x 3 11).toNat = 0 := by
                have r4387 := hand1 (x 3 5) (x 3 11)
                have b4388 := hb (x 3 5)
                have b4389 := hb (x 3 5 && x 3 11)
                clear * - r4387 b4388 b4389 d4374
                omega
              have d4390 : (x 3 5 && x 3 9).toNat = 0 := by
                have r4391 := hand1 (x 3 5) (x 3 9)
                have b4392 := hb (x 3 5)
                have b4393 := hb (x 3 5 && x 3 9)
                clear * - r4391 b4392 b4393 d4374
                omega
              have d4394 : (x 2 2).toNat = 0 := by
                have r4395 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
                have e4396 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e4397 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b4398 := hb (x 1 3)
                have b4399 := hb (x 2 2)
                have b4400 := hb (x 3 13)
                have b4401 := hb (x 4 12)
                clear * - r4395 e4396 e4397 b4398 b4399 b4400 b4401 d4286 d4342 f4285
                omega
              have d4402 : (x 2 2 && x 2 12).toNat = 0 := by
                have r4403 := hand1 (x 2 2) (x 2 12)
                have b4404 := hb (x 2 2)
                have b4405 := hb (x 2 2 && x 2 12)
                clear * - r4403 b4404 b4405 d4394
                omega
              have d4406 : (x 2 2 && x 2 11).toNat = 0 := by
                have r4407 := hand1 (x 2 2) (x 2 11)
                have b4408 := hb (x 2 2)
                have b4409 := hb (x 2 2 && x 2 11)
                clear * - r4407 b4408 b4409 d4394
                omega
              have d4410 : (x 2 2 && x 2 6).toNat = 0 := by
                have r4411 := hand1 (x 2 2) (x 2 6)
                have b4412 := hb (x 2 2)
                have b4413 := hb (x 2 2 && x 2 6)
                clear * - r4411 b4412 b4413 d4394
                omega
              have d4414 : (x 2 2 && x 2 3).toNat = 0 := by
                have r4415 := hand1 (x 2 2) (x 2 3)
                have b4416 := hb (x 2 2)
                have b4417 := hb (x 2 2 && x 2 3)
                clear * - r4415 b4416 b4417 d4394
                omega
              have d4418 : (x 2 10).toNat = 0 := by
                have r4419 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
                have b4420 := hb (x 2 2)
                have b4421 := hb (x 2 10)
                clear * - r4419 b4420 b4421 d4394
                omega
              have d4422 : (x 2 5 && x 2 10).toNat = 0 := by
                have r4423 := hand2 (x 2 5) (x 2 10)
                have b4424 := hb (x 2 10)
                have b4425 := hb (x 2 5 && x 2 10)
                clear * - r4423 b4424 b4425 d4418
                omega
              have d4426 : (x 2 6 && x 2 10).toNat = 0 := by
                have r4427 := hand2 (x 2 6) (x 2 10)
                have b4428 := hb (x 2 10)
                have b4429 := hb (x 2 6 && x 2 10)
                clear * - r4427 b4428 b4429 d4418
                omega
              cases h4430 : x 1 8
              · have f4431 : (x 1 8).toNat = 0 := by rw [h4430]; rfl
                have d4432 : (x 1 8 && x 1 14).toNat = 0 := by
                  have r4433 := hand1 (x 1 8) (x 1 14)
                  have b4434 := hb (x 1 8)
                  have b4435 := hb (x 1 8 && x 1 14)
                  clear * - r4433 b4434 b4435 f4431
                  omega
                have d4436 : (x 1 8 && x 1 13).toNat = 0 := by
                  have r4437 := hand1 (x 1 8) (x 1 13)
                  have b4438 := hb (x 1 8)
                  have b4439 := hb (x 1 8 && x 1 13)
                  clear * - r4437 b4438 b4439 f4431
                  omega
                have d4440 : (x 1 8 && x 1 12).toNat = 0 := by
                  have r4441 := hand1 (x 1 8) (x 1 12)
                  have b4442 := hb (x 1 8)
                  have b4443 := hb (x 1 8 && x 1 12)
                  clear * - r4441 b4442 b4443 f4431
                  omega
                cases h4444 : x 1 4
                · have f4445 : (x 1 4).toNat = 0 := by rw [h4444]; rfl
                  exact cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b0000100 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d186 d270 d170 d154 d121 d137 d97 f287 f313 d234 d49 f301 d296 d318 d210 d21 g14 f4285 f4445 f4431 d4394 d4418 d4374 d4342 d4318 d4414 d61 d133 d37 d4334 d4386 d308 d4306 d4362 d4406 d29 d125 d53 d4302 d4358 d4326 d4378 d81 d178 d218 d105 d4402 d238 d77 d254 d5 d101 d25 d314 d4294 d4350 d162 d1
                · have f6298 : (x 1 4).toNat = 1 := by rw [h4444]; rfl
                  exact cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b0000101 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d186 d202 d270 d170 d154 d121 d137 d97 f287 f313 d234 d49 f301 f307 d41 d296 d318 d210 d21 g14 f6298 f4431 d65 d4394 d4418 d4374 d4342 d4318 d4286 d4410 d242 d129 d282 d4338 d4390 d4426 d230 d117 d4440 d33 d4422 d226 d113 d4436 d45 d4314 d4370 d4334 d4386 d308 d4432 d4310 d4366 d302 d4330 d4382 d4306 d4362 d166 d274 d85 d258 d9 d182 d288 d190 d4302 d4358 d4326 d4378 d81 d178 d218 d105 d4298 d4354 d4322 d174 d77 d254 d5 d101 d162 d1
              · have f11831 : (x 1 8).toNat = 1 := by rw [h4430]; rfl
                exact cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b000011 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d246 d186 d270 d170 d149 d154 d69 d121 d137 d97 g1 f287 f313 d234 d49 f301 f307 d41 d296 d318 d210 d21 g14 f4285 f11831 d4394 d4418 d4374 d4342 d4318 d4410 d242 d129 d282 d4338 d4390 d4426 d230 d117 d93 d266 d17 d206 d292 d145 d194 d4334 d4386 d308 d13 d141 d278 d85 d258 d9 d182 d53 d4302 d4358 d4402 d238 d4298 d4354 d174 d77 d254 d25 d314 d4294 d4350 d162 d1
          · have f14180 : (x 0 3).toNat = 1 := by rw [h312]; rfl
            exact cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b0001 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 f287 f14180 d234
        · have f14848 : (x 0 8).toNat = 1 := by rw [h306]; rfl
          exact cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b001 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d270 d170 d137 f287 d49 f301 f14848 d41 d296 d21 g14 d37 d93 d266 d89 d262 d274 d85 d258 d53 d81 d178 d162 d1
      · have f15404 : (x 0 7).toNat = 1 := by rw [h300]; rfl
        exact cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b01 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d186 d270 d170 d154 d121 d137 d97 f287 d234 d49 f15404 d41 d296 d210 d21 g14 d230 d117 d45 d85 d258 d53 d218 d105 d238 d174 d77 d254 d5 d101 d25 d162 d1
    · have f19013 : (x 0 2).toNat = 1 := by rw [h286]; rfl
      exact cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b1 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d170 d97 f19013 d21 d5 d101 d25 d162 d1
  · exfalso
    have g1 : (x 0 1).toNat = 1 := by rw [h01]; rfl
    have g14 : (x 0 14).toNat = 0 := by rw [h014]; rfl
    have d19325 : (x 0 1 && x 0 14).toNat = 0 := by
      have r19326 := hand2 (x 0 1) (x 0 14)
      have b19327 := hb (x 0 14)
      have b19328 := hb (x 0 1 && x 0 14)
      clear * - r19326 b19327 b19328 g14
      omega
    have d19329 : (x 0 3 && x 0 14).toNat = 0 := by
      have r19330 := hand2 (x 0 3) (x 0 14)
      have b19331 := hb (x 0 14)
      have b19332 := hb (x 0 3 && x 0 14)
      clear * - r19330 b19331 b19332 g14
      omega
    have d19333 : (x 0 4 && x 0 14).toNat = 0 := by
      have r19334 := hand2 (x 0 4) (x 0 14)
      have b19335 := hb (x 0 14)
      have b19336 := hb (x 0 4 && x 0 14)
      clear * - r19334 b19335 b19336 g14
      omega
    have d19337 : (x 0 5 && x 0 14).toNat = 0 := by
      have r19338 := hand2 (x 0 5) (x 0 14)
      have b19339 := hb (x 0 14)
      have b19340 := hb (x 0 5 && x 0 14)
      clear * - r19338 b19339 b19340 g14
      omega
    have d19341 : (x 0 6).toNat = 0 := by
      have r19342 : (x 0 6).toNat ≤ (x 0 14).toNat := himp _ _ (hp6 0)
      have b19343 := hb (x 0 6)
      have b19344 := hb (x 0 14)
      clear * - r19342 b19343 b19344 g14
      omega
    have d19345 : (x 0 6 && x 0 12).toNat = 0 := by
      have r19346 := hand1 (x 0 6) (x 0 12)
      have b19347 := hb (x 0 6)
      have b19348 := hb (x 0 6 && x 0 12)
      clear * - r19346 b19347 b19348 d19341
      omega
    have d19349 : (x 0 6 && x 0 11).toNat = 0 := by
      have r19350 := hand1 (x 0 6) (x 0 11)
      have b19351 := hb (x 0 6)
      have b19352 := hb (x 0 6 && x 0 11)
      clear * - r19350 b19351 b19352 d19341
      omega
    have d19353 : (x 0 1 && x 0 6).toNat = 0 := by
      have r19354 := hand2 (x 0 1) (x 0 6)
      have b19355 := hb (x 0 6)
      have b19356 := hb (x 0 1 && x 0 6)
      clear * - r19354 b19355 b19356 d19341
      omega
    have d19357 : (x 0 6 && x 0 10).toNat = 0 := by
      have r19358 := hand1 (x 0 6) (x 0 10)
      have b19359 := hb (x 0 6)
      have b19360 := hb (x 0 6 && x 0 10)
      clear * - r19358 b19359 b19360 d19341
      omega
    have d19361 : (x 0 6 && x 0 9).toNat = 0 := by
      have r19362 := hand1 (x 0 6) (x 0 9)
      have b19363 := hb (x 0 6)
      have b19364 := hb (x 0 6 && x 0 9)
      clear * - r19362 b19363 b19364 d19341
      omega
    have d19365 : (x 0 6 && x 0 7).toNat = 0 := by
      have r19366 := hand1 (x 0 6) (x 0 7)
      have b19367 := hb (x 0 6)
      have b19368 := hb (x 0 6 && x 0 7)
      clear * - r19366 b19367 b19368 d19341
      omega
    have d19369 : (x 0 2).toNat = 0 := by
      have r19370 : (x 0 2).toNat ≤ (x 0 14).toNat := himp _ _ (hp2 0)
      have b19371 := hb (x 0 2)
      have b19372 := hb (x 0 14)
      clear * - r19370 b19371 b19372 g14
      omega
    have d19373 : (x 0 2 && x 0 13).toNat = 0 := by
      have r19374 := hand1 (x 0 2) (x 0 13)
      have b19375 := hb (x 0 2)
      have b19376 := hb (x 0 2 && x 0 13)
      clear * - r19374 b19375 b19376 d19369
      omega
    have d19377 : (x 0 2 && x 0 12).toNat = 0 := by
      have r19378 := hand1 (x 0 2) (x 0 12)
      have b19379 := hb (x 0 2)
      have b19380 := hb (x 0 2 && x 0 12)
      clear * - r19378 b19379 b19380 d19369
      omega
    have d19381 : (x 0 2 && x 0 11).toNat = 0 := by
      have r19382 := hand1 (x 0 2) (x 0 11)
      have b19383 := hb (x 0 2)
      have b19384 := hb (x 0 2 && x 0 11)
      clear * - r19382 b19383 b19384 d19369
      omega
    have d19385 : (x 0 1 && x 0 2).toNat = 0 := by
      have r19386 := hand2 (x 0 1) (x 0 2)
      have b19387 := hb (x 0 2)
      have b19388 := hb (x 0 1 && x 0 2)
      clear * - r19386 b19387 b19388 d19369
      omega
    have d19389 : (x 0 10).toNat = 0 := by
      have r19390 : (x 0 10).toNat ≤ (x 0 2).toNat := himp _ _ (hp10 0)
      have b19391 := hb (x 0 2)
      have b19392 := hb (x 0 10)
      clear * - r19390 b19391 b19392 d19369
      omega
    have d19393 : (x 0 1 && x 0 10).toNat = 0 := by
      have r19394 := hand2 (x 0 1) (x 0 10)
      have b19395 := hb (x 0 10)
      have b19396 := hb (x 0 1 && x 0 10)
      clear * - r19394 b19395 b19396 d19389
      omega
    have d19397 : (x 0 5 && x 0 10).toNat = 0 := by
      have r19398 := hand2 (x 0 5) (x 0 10)
      have b19399 := hb (x 0 10)
      have b19400 := hb (x 0 5 && x 0 10)
      clear * - r19398 b19399 b19400 d19389
      omega
    have d19401 : (x 0 10 && x 0 13).toNat = 0 := by
      have r19402 := hand1 (x 0 10) (x 0 13)
      have b19403 := hb (x 0 10)
      have b19404 := hb (x 0 10 && x 0 13)
      clear * - r19402 b19403 b19404 d19389
      omega
    have d19405 : (x 0 10 && x 0 11).toNat = 0 := by
      have r19406 := hand1 (x 0 10) (x 0 11)
      have b19407 := hb (x 0 10)
      have b19408 := hb (x 0 10 && x 0 11)
      clear * - r19406 b19407 b19408 d19389
      omega
    have d19409 : (x 1 14).toNat = 0 := by
      have r19410 : (x 1 14).toNat + (x 0 1).toNat = 1 := hd14 1
      have b19411 := hb (x 0 1)
      have b19412 := hb (x 1 14)
      clear * - r19410 b19411 b19412 g1
      omega
    have d19413 : (x 1 1 && x 1 14).toNat = 0 := by
      have r19414 := hand2 (x 1 1) (x 1 14)
      have b19415 := hb (x 1 14)
      have b19416 := hb (x 1 1 && x 1 14)
      clear * - r19414 b19415 b19416 d19409
      omega
    have d19417 : (x 1 3 && x 1 14).toNat = 0 := by
      have r19418 := hand2 (x 1 3) (x 1 14)
      have b19419 := hb (x 1 14)
      have b19420 := hb (x 1 3 && x 1 14)
      clear * - r19418 b19419 b19420 d19409
      omega
    have d19421 : (x 1 4 && x 1 14).toNat = 0 := by
      have r19422 := hand2 (x 1 4) (x 1 14)
      have b19423 := hb (x 1 14)
      have b19424 := hb (x 1 4 && x 1 14)
      clear * - r19422 b19423 b19424 d19409
      omega
    have d19425 : (x 1 5 && x 1 14).toNat = 0 := by
      have r19426 := hand2 (x 1 5) (x 1 14)
      have b19427 := hb (x 1 14)
      have b19428 := hb (x 1 5 && x 1 14)
      clear * - r19426 b19427 b19428 d19409
      omega
    have d19429 : (x 1 7 && x 1 14).toNat = 0 := by
      have r19430 := hand2 (x 1 7) (x 1 14)
      have b19431 := hb (x 1 14)
      have b19432 := hb (x 1 7 && x 1 14)
      clear * - r19430 b19431 b19432 d19409
      omega
    have d19433 : (x 1 8 && x 1 14).toNat = 0 := by
      have r19434 := hand2 (x 1 8) (x 1 14)
      have b19435 := hb (x 1 14)
      have b19436 := hb (x 1 8 && x 1 14)
      clear * - r19434 b19435 b19436 d19409
      omega
    have d19437 : (x 1 9 && x 1 14).toNat = 0 := by
      have r19438 := hand2 (x 1 9) (x 1 14)
      have b19439 := hb (x 1 14)
      have b19440 := hb (x 1 9 && x 1 14)
      clear * - r19438 b19439 b19440 d19409
      omega
    have d19441 : (x 1 11 && x 1 14).toNat = 0 := by
      have r19442 := hand2 (x 1 11) (x 1 14)
      have b19443 := hb (x 1 14)
      have b19444 := hb (x 1 11 && x 1 14)
      clear * - r19442 b19443 b19444 d19409
      omega
    have d19445 : (x 1 6).toNat = 0 := by
      have r19446 : (x 1 6).toNat ≤ (x 1 14).toNat := himp _ _ (hp6 1)
      have b19447 := hb (x 1 6)
      have b19448 := hb (x 1 14)
      clear * - r19446 b19447 b19448 d19409
      omega
    have d19449 : (x 1 6 && x 1 10).toNat = 0 := by
      have r19450 := hand1 (x 1 6) (x 1 10)
      have b19451 := hb (x 1 6)
      have b19452 := hb (x 1 6 && x 1 10)
      clear * - r19450 b19451 b19452 d19445
      omega
    have d19453 : (x 1 2 && x 1 6).toNat = 0 := by
      have r19454 := hand2 (x 1 2) (x 1 6)
      have b19455 := hb (x 1 6)
      have b19456 := hb (x 1 2 && x 1 6)
      clear * - r19454 b19455 b19456 d19445
      omega
    have d19457 : (x 1 5 && x 1 6).toNat = 0 := by
      have r19458 := hand2 (x 1 5) (x 1 6)
      have b19459 := hb (x 1 6)
      have b19460 := hb (x 1 5 && x 1 6)
      clear * - r19458 b19459 b19460 d19445
      omega
    have d19461 : (x 1 2).toNat = 0 := by
      have r19462 : (x 1 2).toNat ≤ (x 1 14).toNat := himp _ _ (hp2 1)
      have b19463 := hb (x 1 2)
      have b19464 := hb (x 1 14)
      clear * - r19462 b19463 b19464 d19409
      omega
    have d19465 : (x 1 2 && x 1 13).toNat = 0 := by
      have r19466 := hand1 (x 1 2) (x 1 13)
      have b19467 := hb (x 1 2)
      have b19468 := hb (x 1 2 && x 1 13)
      clear * - r19466 b19467 b19468 d19461
      omega
    have d19469 : (x 1 2 && x 1 12).toNat = 0 := by
      have r19470 := hand1 (x 1 2) (x 1 12)
      have b19471 := hb (x 1 2)
      have b19472 := hb (x 1 2 && x 1 12)
      clear * - r19470 b19471 b19472 d19461
      omega
    have d19473 : (x 1 2 && x 1 11).toNat = 0 := by
      have r19474 := hand1 (x 1 2) (x 1 11)
      have b19475 := hb (x 1 2)
      have b19476 := hb (x 1 2 && x 1 11)
      clear * - r19474 b19475 b19476 d19461
      omega
    have d19477 : (x 1 2 && x 1 7).toNat = 0 := by
      have r19478 := hand1 (x 1 2) (x 1 7)
      have b19479 := hb (x 1 2)
      have b19480 := hb (x 1 2 && x 1 7)
      clear * - r19478 b19479 b19480 d19461
      omega
    have d19481 : (x 1 10).toNat = 0 := by
      have r19482 : (x 1 10).toNat ≤ (x 1 2).toNat := himp _ _ (hp10 1)
      have b19483 := hb (x 1 2)
      have b19484 := hb (x 1 10)
      clear * - r19482 b19483 b19484 d19461
      omega
    have d19485 : (x 1 1 && x 1 10).toNat = 0 := by
      have r19486 := hand2 (x 1 1) (x 1 10)
      have b19487 := hb (x 1 10)
      have b19488 := hb (x 1 1 && x 1 10)
      clear * - r19486 b19487 b19488 d19481
      omega
    have d19489 : (x 1 5 && x 1 10).toNat = 0 := by
      have r19490 := hand2 (x 1 5) (x 1 10)
      have b19491 := hb (x 1 10)
      have b19492 := hb (x 1 5 && x 1 10)
      clear * - r19490 b19491 b19492 d19481
      omega
    have d19493 : (x 1 9 && x 1 10).toNat = 0 := by
      have r19494 := hand2 (x 1 9) (x 1 10)
      have b19495 := hb (x 1 10)
      have b19496 := hb (x 1 9 && x 1 10)
      clear * - r19494 b19495 b19496 d19481
      omega
    have d19497 : (x (-1) 1).toNat = 1 := by
      have r19498 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := hd14 0
      have b19499 := hb (x (-1) 1)
      have b19500 := hb (x 0 14)
      clear * - r19498 b19499 b19500 g14
      omega
    have d19501 : (x 2 13).toNat = 1 := by
      have r19502 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := hcov13 2
      have b19503 := hb (x 0 2)
      have b19504 := hb (x 2 13)
      have b19505 := hb (x 1 1 && x 1 14)
      clear * - r19502 b19503 b19504 b19505 d19413 d19369
      omega
    have d19506 : (x 2 1).toNat = 1 := by
      have r19507 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
      have b19508 := hb (x 2 1)
      have b19509 := hb (x 2 13)
      clear * - r19507 b19508 b19509 d19501
      omega
    have d19510 : (x 3 14).toNat = 0 := by
      have r19511 : (x 3 14).toNat + (x 2 1).toNat = 1 := hd14 3
      have b19512 := hb (x 2 1)
      have b19513 := hb (x 3 14)
      clear * - r19511 b19512 b19513 d19506
      omega
    have d19514 : (x 3 1 && x 3 14).toNat = 0 := by
      have r19515 := hand2 (x 3 1) (x 3 14)
      have b19516 := hb (x 3 14)
      have b19517 := hb (x 3 1 && x 3 14)
      clear * - r19515 b19516 b19517 d19510
      omega
    have d19518 : (x 3 3 && x 3 14).toNat = 0 := by
      have r19519 := hand2 (x 3 3) (x 3 14)
      have b19520 := hb (x 3 14)
      have b19521 := hb (x 3 3 && x 3 14)
      clear * - r19519 b19520 b19521 d19510
      omega
    have d19522 : (x 3 4 && x 3 14).toNat = 0 := by
      have r19523 := hand2 (x 3 4) (x 3 14)
      have b19524 := hb (x 3 14)
      have b19525 := hb (x 3 4 && x 3 14)
      clear * - r19523 b19524 b19525 d19510
      omega
    have d19526 : (x 3 5 && x 3 14).toNat = 0 := by
      have r19527 := hand2 (x 3 5) (x 3 14)
      have b19528 := hb (x 3 14)
      have b19529 := hb (x 3 5 && x 3 14)
      clear * - r19527 b19528 b19529 d19510
      omega
    have d19530 : (x 3 6).toNat = 0 := by
      have r19531 : (x 3 6).toNat ≤ (x 3 14).toNat := himp _ _ (hp6 3)
      have b19532 := hb (x 3 6)
      have b19533 := hb (x 3 14)
      clear * - r19531 b19532 b19533 d19510
      omega
    have d19534 : (x 3 6 && x 3 13).toNat = 0 := by
      have r19535 := hand1 (x 3 6) (x 3 13)
      have b19536 := hb (x 3 6)
      have b19537 := hb (x 3 6 && x 3 13)
      clear * - r19535 b19536 b19537 d19530
      omega
    have d19538 : (x 3 6 && x 3 12).toNat = 0 := by
      have r19539 := hand1 (x 3 6) (x 3 12)
      have b19540 := hb (x 3 6)
      have b19541 := hb (x 3 6 && x 3 12)
      clear * - r19539 b19540 b19541 d19530
      omega
    have d19542 : (x 3 6 && x 3 10).toNat = 0 := by
      have r19543 := hand1 (x 3 6) (x 3 10)
      have b19544 := hb (x 3 6)
      have b19545 := hb (x 3 6 && x 3 10)
      clear * - r19543 b19544 b19545 d19530
      omega
    have d19546 : (x 3 3 && x 3 6).toNat = 0 := by
      have r19547 := hand2 (x 3 3) (x 3 6)
      have b19548 := hb (x 3 6)
      have b19549 := hb (x 3 3 && x 3 6)
      clear * - r19547 b19548 b19549 d19530
      omega
    have d19550 : (x 3 2).toNat = 0 := by
      have r19551 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
      have b19552 := hb (x 3 2)
      have b19553 := hb (x 3 14)
      clear * - r19551 b19552 b19553 d19510
      omega
    have d19554 : (x 3 2 && x 3 13).toNat = 0 := by
      have r19555 := hand1 (x 3 2) (x 3 13)
      have b19556 := hb (x 3 2)
      have b19557 := hb (x 3 2 && x 3 13)
      clear * - r19555 b19556 b19557 d19550
      omega
    have d19558 : (x 3 2 && x 3 12).toNat = 0 := by
      have r19559 := hand1 (x 3 2) (x 3 12)
      have b19560 := hb (x 3 2)
      have b19561 := hb (x 3 2 && x 3 12)
      clear * - r19559 b19560 b19561 d19550
      omega
    have d19562 : (x 3 2 && x 3 11).toNat = 0 := by
      have r19563 := hand1 (x 3 2) (x 3 11)
      have b19564 := hb (x 3 2)
      have b19565 := hb (x 3 2 && x 3 11)
      clear * - r19563 b19564 b19565 d19550
      omega
    have d19566 : (x 3 2 && x 3 9).toNat = 0 := by
      have r19567 := hand1 (x 3 2) (x 3 9)
      have b19568 := hb (x 3 2)
      have b19569 := hb (x 3 2 && x 3 9)
      clear * - r19567 b19568 b19569 d19550
      omega
    have d19570 : (x 3 2 && x 3 7).toNat = 0 := by
      have r19571 := hand1 (x 3 2) (x 3 7)
      have b19572 := hb (x 3 2)
      have b19573 := hb (x 3 2 && x 3 7)
      clear * - r19571 b19572 b19573 d19550
      omega
    have d19574 : (x 3 10).toNat = 0 := by
      have r19575 : (x 3 10).toNat ≤ (x 3 2).toNat := himp _ _ (hp10 3)
      have b19576 := hb (x 3 2)
      have b19577 := hb (x 3 10)
      clear * - r19575 b19576 b19577 d19550
      omega
    have d19578 : (x 3 5 && x 3 10).toNat = 0 := by
      have r19579 := hand2 (x 3 5) (x 3 10)
      have b19580 := hb (x 3 10)
      have b19581 := hb (x 3 5 && x 3 10)
      clear * - r19579 b19580 b19581 d19574
      omega
    have d19582 : (x 3 7 && x 3 10).toNat = 0 := by
      have r19583 := hand2 (x 3 7) (x 3 10)
      have b19584 := hb (x 3 10)
      have b19585 := hb (x 3 7 && x 3 10)
      clear * - r19583 b19584 b19585 d19574
      omega
    have d19586 : (x 3 12).toNat = 0 := by
      have r19587 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := hd12 3
      have e19588 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
      have e19589 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
      have b19590 := hb (x 0 3)
      have b19591 := hb (x 1 2)
      have b19592 := hb (x 2 13)
      have b19593 := hb (x 3 12)
      clear * - r19587 e19588 e19589 b19590 b19591 b19592 b19593 d19501 d19461
      omega
    have d19594 : (x 3 1 && x 3 12).toNat = 0 := by
      have r19595 := hand2 (x 3 1) (x 3 12)
      have b19596 := hb (x 3 12)
      have b19597 := hb (x 3 1 && x 3 12)
      clear * - r19595 b19596 b19597 d19586
      omega
    have d19598 : (x 3 3 && x 3 12).toNat = 0 := by
      have r19599 := hand2 (x 3 3) (x 3 12)
      have b19600 := hb (x 3 12)
      have b19601 := hb (x 3 3 && x 3 12)
      clear * - r19599 b19600 b19601 d19586
      omega
    have d19602 : (x 3 5 && x 3 12).toNat = 0 := by
      have r19603 := hand2 (x 3 5) (x 3 12)
      have b19604 := hb (x 3 12)
      have b19605 := hb (x 3 5 && x 3 12)
      clear * - r19603 b19604 b19605 d19586
      omega
    have d19606 : (x 3 7 && x 3 12).toNat = 0 := by
      have r19607 := hand2 (x 3 7) (x 3 12)
      have b19608 := hb (x 3 12)
      have b19609 := hb (x 3 7 && x 3 12)
      clear * - r19607 b19608 b19609 d19586
      omega
    have d19610 : (x 3 8 && x 3 12).toNat = 0 := by
      have r19611 := hand2 (x 3 8) (x 3 12)
      have b19612 := hb (x 3 12)
      have b19613 := hb (x 3 8 && x 3 12)
      clear * - r19611 b19612 b19613 d19586
      omega
    have d19614 : (x 3 9 && x 3 12).toNat = 0 := by
      have r19615 := hand2 (x 3 9) (x 3 12)
      have b19616 := hb (x 3 12)
      have b19617 := hb (x 3 9 && x 3 12)
      clear * - r19615 b19616 b19617 d19586
      omega
    have d19618 : (x 3 4).toNat = 0 := by
      have r19619 : (x 3 4).toNat ≤ (x 3 12).toNat := himp _ _ (hp4 3)
      have b19620 := hb (x 3 4)
      have b19621 := hb (x 3 12)
      clear * - r19619 b19620 b19621 d19586
      omega
    have d19622 : (x 3 4 && x 3 13).toNat = 0 := by
      have r19623 := hand1 (x 3 4) (x 3 13)
      have b19624 := hb (x 3 4)
      have b19625 := hb (x 3 4 && x 3 13)
      clear * - r19623 b19624 b19625 d19618
      omega
    have d19626 : (x 3 4 && x 3 8).toNat = 0 := by
      have r19627 := hand1 (x 3 4) (x 3 8)
      have b19628 := hb (x 3 4)
      have b19629 := hb (x 3 4 && x 3 8)
      clear * - r19627 b19628 b19629 d19618
      omega
    have d19630 : (x 3 3 && x 3 4).toNat = 0 := by
      have r19631 := hand2 (x 3 3) (x 3 4)
      have b19632 := hb (x 3 4)
      have b19633 := hb (x 3 3 && x 3 4)
      clear * - r19631 b19632 b19633 d19618
      omega
    have d19634 : (x 0 3).toNat = 0 := by
      have r19635 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := hd12 3
      have e19636 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
      have e19637 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
      have b19638 := hb (x 0 3)
      have b19639 := hb (x 1 2)
      have b19640 := hb (x 2 13)
      have b19641 := hb (x 3 12)
      clear * - r19635 e19636 e19637 b19638 b19639 b19640 b19641 d19586 d19501 d19461
      omega
    have d19642 : (x 0 3 && x 0 13).toNat = 0 := by
      have r19643 := hand1 (x 0 3) (x 0 13)
      have b19644 := hb (x 0 3)
      have b19645 := hb (x 0 3 && x 0 13)
      clear * - r19643 b19644 b19645 d19634
      omega
    have d19646 : (x 0 3 && x 0 12).toNat = 0 := by
      have r19647 := hand1 (x 0 3) (x 0 12)
      have b19648 := hb (x 0 3)
      have b19649 := hb (x 0 3 && x 0 12)
      clear * - r19647 b19648 b19649 d19634
      omega
    have d19650 : (x 0 3 && x 0 8).toNat = 0 := by
      have r19651 := hand1 (x 0 3) (x 0 8)
      have b19652 := hb (x 0 3)
      have b19653 := hb (x 0 3 && x 0 8)
      clear * - r19651 b19652 b19653 d19634
      omega
    have d19654 : (x 0 3 && x 0 7).toNat = 0 := by
      have r19655 := hand1 (x 0 3) (x 0 7)
      have b19656 := hb (x 0 3)
      have b19657 := hb (x 0 3 && x 0 7)
      clear * - r19655 b19656 b19657 d19634
      omega
    have d19658 : (x 0 1 && x 0 3).toNat = 0 := by
      have r19659 := hand2 (x 0 1) (x 0 3)
      have b19660 := hb (x 0 3)
      have b19661 := hb (x 0 1 && x 0 3)
      clear * - r19659 b19660 b19661 d19634
      omega
    have d19662 : (x 0 11).toNat = 0 := by
      have r19663 : (x 0 11).toNat ≤ (x 0 3).toNat := himp _ _ (hp11 0)
      have b19664 := hb (x 0 3)
      have b19665 := hb (x 0 11)
      clear * - r19663 b19664 b19665 d19634
      omega
    have d19666 : (x 0 1 && x 0 11).toNat = 0 := by
      have r19667 := hand2 (x 0 1) (x 0 11)
      have b19668 := hb (x 0 11)
      have b19669 := hb (x 0 1 && x 0 11)
      clear * - r19667 b19668 b19669 d19662
      omega
    have d19670 : (x 0 7 && x 0 11).toNat = 0 := by
      have r19671 := hand2 (x 0 7) (x 0 11)
      have b19672 := hb (x 0 11)
      have b19673 := hb (x 0 7 && x 0 11)
      clear * - r19671 b19672 b19673 d19662
      omega
    cases h19674 : x 0 4
    · have f19675 : (x 0 4).toNat = 0 := by rw [h19674]; rfl
      cases h19676 : x 0 8
      · have f19677 : (x 0 8).toNat = 0 := by rw [h19676]; rfl
        have d19678 : (x 0 8 && x 0 13).toNat = 0 := by
          have r19679 := hand1 (x 0 8) (x 0 13)
          have b19680 := hb (x 0 8)
          have b19681 := hb (x 0 8 && x 0 13)
          clear * - r19679 b19680 b19681 f19677
          omega
        cases h19682 : x 0 13
        · have f19683 : (x 0 13).toNat = 0 := by rw [h19682]; rfl
          have d19684 : (x 0 9 && x 0 13).toNat = 0 := by
            have r19685 := hand2 (x 0 9) (x 0 13)
            have b19686 := hb (x 0 13)
            have b19687 := hb (x 0 9 && x 0 13)
            clear * - r19685 b19686 b19687 f19683
            omega
          have d19688 : (x 0 5).toNat = 0 := by
            have r19689 : (x 0 5).toNat ≤ (x 0 13).toNat := himp _ _ (hp5 0)
            have b19690 := hb (x 0 5)
            have b19691 := hb (x 0 13)
            clear * - r19689 b19690 b19691 f19683
            omega
          have d19692 : (x 0 5 && x 0 12).toNat = 0 := by
            have r19693 := hand1 (x 0 5) (x 0 12)
            have b19694 := hb (x 0 5)
            have b19695 := hb (x 0 5 && x 0 12)
            clear * - r19693 b19694 b19695 d19688
            omega
          cases h19696 : x 0 7
          · have f19697 : (x 0 7).toNat = 0 := by rw [h19696]; rfl
            have d19698 : (x 0 1 && x 0 7).toNat = 0 := by
              have r19699 := hand2 (x 0 1) (x 0 7)
              have b19700 := hb (x 0 7)
              have b19701 := hb (x 0 1 && x 0 7)
              clear * - r19699 b19700 b19701 f19697
              omega
            cases h19702 : x (-1) 3
            · have f19703 : (x (-1) 3).toNat = 0 := by rw [h19702]; rfl
              have d19704 : (x (-1) 3 && x (-1) 13).toNat = 0 := by
                have r19705 := hand1 (x (-1) 3) (x (-1) 13)
                have b19706 := hb (x (-1) 3)
                have b19707 := hb (x (-1) 3 && x (-1) 13)
                clear * - r19705 b19706 b19707 f19703
                omega
              have d19708 : (x (-1) 3 && x (-1) 12).toNat = 0 := by
                have r19709 := hand1 (x (-1) 3) (x (-1) 12)
                have b19710 := hb (x (-1) 3)
                have b19711 := hb (x (-1) 3 && x (-1) 12)
                clear * - r19709 b19710 b19711 f19703
                omega
              have d19712 : (x (-1) 1 && x (-1) 3).toNat = 0 := by
                have r19713 := hand2 (x (-1) 1) (x (-1) 3)
                have b19714 := hb (x (-1) 3)
                have b19715 := hb (x (-1) 1 && x (-1) 3)
                clear * - r19713 b19714 b19715 f19703
                omega
              have d19716 : (x (-1) 2 && x (-1) 3).toNat = 0 := by
                have r19717 := hand2 (x (-1) 2) (x (-1) 3)
                have b19718 := hb (x (-1) 3)
                have b19719 := hb (x (-1) 2 && x (-1) 3)
                clear * - r19717 b19718 b19719 f19703
                omega
              have d19720 : (x (-1) 11).toNat = 0 := by
                have r19721 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
                have b19722 := hb (x (-1) 3)
                have b19723 := hb (x (-1) 11)
                clear * - r19721 b19722 b19723 f19703
                omega
              have d19724 : (x (-1) 1 && x (-1) 11).toNat = 0 := by
                have r19725 := hand2 (x (-1) 1) (x (-1) 11)
                have b19726 := hb (x (-1) 11)
                have b19727 := hb (x (-1) 1 && x (-1) 11)
                clear * - r19725 b19726 b19727 d19720
                omega
              have d19728 : (x (-1) 2 && x (-1) 11).toNat = 0 := by
                have r19729 := hand2 (x (-1) 2) (x (-1) 11)
                have b19730 := hb (x (-1) 11)
                have b19731 := hb (x (-1) 2 && x (-1) 11)
                clear * - r19729 b19730 b19731 d19720
                omega
              have d19732 : (x (-1) 11 && x (-1) 14).toNat = 0 := by
                have r19733 := hand1 (x (-1) 11) (x (-1) 14)
                have b19734 := hb (x (-1) 11)
                have b19735 := hb (x (-1) 11 && x (-1) 14)
                clear * - r19733 b19734 b19735 d19720
                omega
              have d19736 : (x (-1) 11 && x (-1) 12).toNat = 0 := by
                have r19737 := hand1 (x (-1) 11) (x (-1) 12)
                have b19738 := hb (x (-1) 11)
                have b19739 := hb (x (-1) 11 && x (-1) 12)
                clear * - r19737 b19738 b19739 d19720
                omega
              cases h19740 : x (-1) 13
              · have f19741 : (x (-1) 13).toNat = 0 := by rw [h19740]; rfl
                exact cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a000000 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 f19741 g1 f19675 d19688 d19389 d19662 f19683 d19461 d19481 d19550 d19574 d19724 d19666 d19469 d19642 d19594 d19417 d19325 d19514
              · have f21610 : (x (-1) 13).toNat = 1 := by rw [h19740]; rfl
                exact cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a000001 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d19497 f19703 d19720 f21610 g1 d19369 f19675 d19688 d19341 f19677 d19389 d19662 f19683 g14 d19461 d19445 d19481 d19550 d19618 d19530 d19574 d19385 d19716 d19493 d19405 d19736 d19712 d19658 d19582 d19401 d19732 d19542 d19684 d19353 d19578 d19678 d19698 d19534 d19393 d19728 d19485 d19381 d19708 d19473 d19646 d19526 d19724 d19666 d19377 d19704 d19469 d19642 d19558 d19421 d19594 d19417 d19554 d19518 d19325 d19514
            · have f25725 : (x (-1) 3).toNat = 1 := by rw [h19702]; rfl
              have d25726 : (x 2 12).toNat = 0 := by
                have r25727 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := hd12 2
                have e25728 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
                have e25729 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
                have b25730 := hb (x (-1) 3)
                have b25731 := hb (x 0 2)
                have b25732 := hb (x 1 13)
                have b25733 := hb (x 2 12)
                clear * - r25727 e25728 e25729 b25730 b25731 b25732 b25733 d19369 f25725
                omega
              have d25734 : (x 2 1 && x 2 12).toNat = 0 := by
                have r25735 := hand2 (x 2 1) (x 2 12)
                have b25736 := hb (x 2 12)
                have b25737 := hb (x 2 1 && x 2 12)
                clear * - r25735 b25736 b25737 d25726
                omega
              have d25738 : (x 2 2 && x 2 12).toNat = 0 := by
                have r25739 := hand2 (x 2 2) (x 2 12)
                have b25740 := hb (x 2 12)
                have b25741 := hb (x 2 2 && x 2 12)
                clear * - r25739 b25740 b25741 d25726
                omega
              have d25742 : (x 2 3 && x 2 12).toNat = 0 := by
                have r25743 := hand2 (x 2 3) (x 2 12)
                have b25744 := hb (x 2 12)
                have b25745 := hb (x 2 3 && x 2 12)
                clear * - r25743 b25744 b25745 d25726
                omega
              have d25746 : (x 2 12 && x 2 14).toNat = 0 := by
                have r25747 := hand1 (x 2 12) (x 2 14)
                have b25748 := hb (x 2 12)
                have b25749 := hb (x 2 12 && x 2 14)
                clear * - r25747 b25748 b25749 d25726
                omega
              have d25750 : (x 2 4).toNat = 0 := by
                have r25751 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
                have b25752 := hb (x 2 4)
                have b25753 := hb (x 2 12)
                clear * - r25751 b25752 b25753 d25726
                omega
              have d25754 : (x 2 4 && x 2 14).toNat = 0 := by
                have r25755 := hand1 (x 2 4) (x 2 14)
                have b25756 := hb (x 2 4)
                have b25757 := hb (x 2 4 && x 2 14)
                clear * - r25755 b25756 b25757 d25750
                omega
              have d25758 : (x 2 4 && x 2 13).toNat = 0 := by
                have r25759 := hand1 (x 2 4) (x 2 13)
                have b25760 := hb (x 2 4)
                have b25761 := hb (x 2 4 && x 2 13)
                clear * - r25759 b25760 b25761 d25750
                omega
              have d25762 : (x 2 4 && x 2 10).toNat = 0 := by
                have r25763 := hand1 (x 2 4) (x 2 10)
                have b25764 := hb (x 2 4)
                have b25765 := hb (x 2 4 && x 2 10)
                clear * - r25763 b25764 b25765 d25750
                omega
              have d25766 : (x 2 4 && x 2 9).toNat = 0 := by
                have r25767 := hand1 (x 2 4) (x 2 9)
                have b25768 := hb (x 2 4)
                have b25769 := hb (x 2 4 && x 2 9)
                clear * - r25767 b25768 b25769 d25750
                omega
              have d25770 : (x 2 4 && x 2 8).toNat = 0 := by
                have r25771 := hand1 (x 2 4) (x 2 8)
                have b25772 := hb (x 2 4)
                have b25773 := hb (x 2 4 && x 2 8)
                clear * - r25771 b25772 b25773 d25750
                omega
              have d25774 : (x 2 4 && x 2 7).toNat = 0 := by
                have r25775 := hand1 (x 2 4) (x 2 7)
                have b25776 := hb (x 2 4)
                have b25777 := hb (x 2 4 && x 2 7)
                clear * - r25775 b25776 b25777 d25750
                omega
              have d25778 : (x 2 4 && x 2 5).toNat = 0 := by
                have r25779 := hand1 (x 2 4) (x 2 5)
                have b25780 := hb (x 2 4)
                have b25781 := hb (x 2 4 && x 2 5)
                clear * - r25779 b25780 b25781 d25750
                omega
              have d25782 : (x 1 13).toNat = 0 := by
                have r25783 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := hd12 2
                have e25784 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
                have e25785 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
                have b25786 := hb (x (-1) 3)
                have b25787 := hb (x 0 2)
                have b25788 := hb (x 1 13)
                have b25789 := hb (x 2 12)
                clear * - r25783 e25784 e25785 b25786 b25787 b25788 b25789 d25726 d19369 f25725
                omega
              have d25790 : (x 1 3 && x 1 13).toNat = 0 := by
                have r25791 := hand2 (x 1 3) (x 1 13)
                have b25792 := hb (x 1 13)
                have b25793 := hb (x 1 3 && x 1 13)
                clear * - r25791 b25792 b25793 d25782
                omega
              have d25794 : (x 1 4 && x 1 13).toNat = 0 := by
                have r25795 := hand2 (x 1 4) (x 1 13)
                have b25796 := hb (x 1 13)
                have b25797 := hb (x 1 4 && x 1 13)
                clear * - r25795 b25796 b25797 d25782
                omega
              have d25798 : (x 1 5).toNat = 0 := by
                have r25799 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
                have b25800 := hb (x 1 5)
                have b25801 := hb (x 1 13)
                clear * - r25799 b25800 b25801 d25782
                omega
              have d25802 : (x 1 5 && x 1 11).toNat = 0 := by
                have r25803 := hand1 (x 1 5) (x 1 11)
                have b25804 := hb (x 1 5)
                have b25805 := hb (x 1 5 && x 1 11)
                clear * - r25803 b25804 b25805 d25798
                omega
              have d25806 : (x 1 5 && x 1 9).toNat = 0 := by
                have r25807 := hand1 (x 1 5) (x 1 9)
                have b25808 := hb (x 1 5)
                have b25809 := hb (x 1 5 && x 1 9)
                clear * - r25807 b25808 b25809 d25798
                omega
              have d25810 : (x 1 5 && x 1 8).toNat = 0 := by
                have r25811 := hand1 (x 1 5) (x 1 8)
                have b25812 := hb (x 1 5)
                have b25813 := hb (x 1 5 && x 1 8)
                clear * - r25811 b25812 b25813 d25798
                omega
              have d25814 : (x (-1) 2).toNat = 1 := by
                have r25815 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := hcov13 1
                have b25816 := hb (x (-1) 2)
                have b25817 := hb (x 1 13)
                have b25818 := hb (x 0 1 && x 0 14)
                clear * - r25815 b25816 b25817 b25818 d25782 d19325
                omega
              have d25819 : (x (-1) 14).toNat = 1 := by
                have r25820 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
                have b25821 := hb (x (-1) 2)
                have b25822 := hb (x (-1) 14)
                clear * - r25820 b25821 b25822 d25814
                omega
              have d25823 : (x (-2) 1).toNat = 0 := by
                have r25824 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := hd14 (-1)
                have b25825 := hb (x (-2) 1)
                have b25826 := hb (x (-1) 14)
                clear * - r25824 b25825 b25826 d25819
                omega
              have d25827 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
                have r25828 := hand1 (x (-2) 1) (x (-2) 14)
                have b25829 := hb (x (-2) 1)
                have b25830 := hb (x (-2) 1 && x (-2) 14)
                clear * - r25828 b25829 b25830 d25823
                omega
              have d25831 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
                have r25832 := hand1 (x (-2) 1) (x (-2) 12)
                have b25833 := hb (x (-2) 1)
                have b25834 := hb (x (-2) 1 && x (-2) 12)
                clear * - r25832 b25833 b25834 d25823
                omega
              have d25835 : (x (-2) 1 && x (-2) 11).toNat = 0 := by
                have r25836 := hand1 (x (-2) 1) (x (-2) 11)
                have b25837 := hb (x (-2) 1)
                have b25838 := hb (x (-2) 1 && x (-2) 11)
                clear * - r25836 b25837 b25838 d25823
                omega
              have d25839 : (x (-2) 1 && x (-2) 10).toNat = 0 := by
                have r25840 := hand1 (x (-2) 1) (x (-2) 10)
                have b25841 := hb (x (-2) 1)
                have b25842 := hb (x (-2) 1 && x (-2) 10)
                clear * - r25840 b25841 b25842 d25823
                omega
              have d25843 : (x (-2) 1 && x (-2) 8).toNat = 0 := by
                have r25844 := hand1 (x (-2) 1) (x (-2) 8)
                have b25845 := hb (x (-2) 1)
                have b25846 := hb (x (-2) 1 && x (-2) 8)
                clear * - r25844 b25845 b25846 d25823
                omega
              have d25847 : (x (-2) 1 && x (-2) 7).toNat = 0 := by
                have r25848 := hand1 (x (-2) 1) (x (-2) 7)
                have b25849 := hb (x (-2) 1)
                have b25850 := hb (x (-2) 1 && x (-2) 7)
                clear * - r25848 b25849 b25850 d25823
                omega
              have d25851 : (x (-2) 1 && x (-2) 6).toNat = 0 := by
                have r25852 := hand1 (x (-2) 1) (x (-2) 6)
                have b25853 := hb (x (-2) 1)
                have b25854 := hb (x (-2) 1 && x (-2) 6)
                clear * - r25852 b25853 b25854 d25823
                omega
              have d25855 : (x (-2) 13).toNat = 0 := by
                have r25856 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
                have b25857 := hb (x (-2) 1)
                have b25858 := hb (x (-2) 13)
                clear * - r25856 b25857 b25858 d25823
                omega
              have d25859 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
                have r25860 := hand2 (x (-2) 3) (x (-2) 13)
                have b25861 := hb (x (-2) 13)
                have b25862 := hb (x (-2) 3 && x (-2) 13)
                clear * - r25860 b25861 b25862 d25855
                omega
              have d25863 : (x (-2) 8 && x (-2) 13).toNat = 0 := by
                have r25864 := hand2 (x (-2) 8) (x (-2) 13)
                have b25865 := hb (x (-2) 13)
                have b25866 := hb (x (-2) 8 && x (-2) 13)
                clear * - r25864 b25865 b25866 d25855
                omega
              have d25867 : (x (-2) 5).toNat = 0 := by
                have r25868 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
                have b25869 := hb (x (-2) 5)
                have b25870 := hb (x (-2) 13)
                clear * - r25868 b25869 b25870 d25855
                omega
              have d25871 : (x (-2) 5 && x (-2) 9).toNat = 0 := by
                have r25872 := hand1 (x (-2) 5) (x (-2) 9)
                have b25873 := hb (x (-2) 5)
                have b25874 := hb (x (-2) 5 && x (-2) 9)
                clear * - r25872 b25873 b25874 d25867
                omega
              have d25875 : (x (-2) 9).toNat = 0 := by
                have r25876 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
                have b25877 := hb (x (-2) 1)
                have b25878 := hb (x (-2) 9)
                clear * - r25876 b25877 b25878 d25823
                omega
              have d25879 : (x (-2) 3 && x (-2) 9).toNat = 0 := by
                have r25880 := hand2 (x (-2) 3) (x (-2) 9)
                have b25881 := hb (x (-2) 9)
                have b25882 := hb (x (-2) 3 && x (-2) 9)
                clear * - r25880 b25881 b25882 d25875
                omega
              have d25883 : (x (-2) 8 && x (-2) 9).toNat = 0 := by
                have r25884 := hand2 (x (-2) 8) (x (-2) 9)
                have b25885 := hb (x (-2) 9)
                have b25886 := hb (x (-2) 8 && x (-2) 9)
                clear * - r25884 b25885 b25886 d25875
                omega
              have d25887 : (x 1 12).toNat = 0 := by
                have r25888 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
                have e25889 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
                have e25890 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
                have b25891 := hb (x (-2) 3)
                have b25892 := hb (x (-1) 2)
                have b25893 := hb (x 0 13)
                have b25894 := hb (x 1 12)
                clear * - r25888 e25889 e25890 b25891 b25892 b25893 b25894 f19683 d25814
                omega
              have d25895 : (x 1 4).toNat = 0 := by
                have r25896 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
                have b25897 := hb (x 1 4)
                have b25898 := hb (x 1 12)
                clear * - r25896 b25897 b25898 d25887
                omega
              have d25899 : (x 1 4 && x 1 11).toNat = 0 := by
                have r25900 := hand1 (x 1 4) (x 1 11)
                have b25901 := hb (x 1 4)
                have b25902 := hb (x 1 4 && x 1 11)
                clear * - r25900 b25901 b25902 d25895
                omega
              have d25903 : (x 1 4 && x 1 9).toNat = 0 := by
                have r25904 := hand1 (x 1 4) (x 1 9)
                have b25905 := hb (x 1 4)
                have b25906 := hb (x 1 4 && x 1 9)
                clear * - r25904 b25905 b25906 d25895
                omega
              have d25907 : (x (-2) 3).toNat = 0 := by
                have r25908 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
                have e25909 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
                have e25910 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
                have b25911 := hb (x (-2) 3)
                have b25912 := hb (x (-1) 2)
                have b25913 := hb (x 0 13)
                have b25914 := hb (x 1 12)
                clear * - r25908 e25909 e25910 b25911 b25912 b25913 b25914 d25887 f19683 d25814
                omega
              have d25915 : (x (-2) 3 && x (-2) 8).toNat = 0 := by
                have r25916 := hand1 (x (-2) 3) (x (-2) 8)
                have b25917 := hb (x (-2) 3)
                have b25918 := hb (x (-2) 3 && x (-2) 8)
                clear * - r25916 b25917 b25918 d25907
                omega
              have d25919 : (x (-2) 11).toNat = 0 := by
                have r25920 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
                have b25921 := hb (x (-2) 3)
                have b25922 := hb (x (-2) 11)
                clear * - r25920 b25921 b25922 d25907
                omega
              have d25923 : (x (-2) 8 && x (-2) 11).toNat = 0 := by
                have r25924 := hand2 (x (-2) 8) (x (-2) 11)
                have b25925 := hb (x (-2) 11)
                have b25926 := hb (x (-2) 8 && x (-2) 11)
                clear * - r25924 b25925 b25926 d25919
                omega
              cases h25927 : x (-1) 8
              · have f25928 : (x (-1) 8).toNat = 0 := by rw [h25927]; rfl
                have d25929 : (x (-1) 2 && x (-1) 8).toNat = 0 := by
                  have r25930 := hand2 (x (-1) 2) (x (-1) 8)
                  have b25931 := hb (x (-1) 8)
                  have b25932 := hb (x (-1) 2 && x (-1) 8)
                  clear * - r25930 b25931 b25932 f25928
                  omega
                have d25933 : (x (-1) 4 && x (-1) 8).toNat = 0 := by
                  have r25934 := hand2 (x (-1) 4) (x (-1) 8)
                  have b25935 := hb (x (-1) 8)
                  have b25936 := hb (x (-1) 4 && x (-1) 8)
                  clear * - r25934 b25935 b25936 f25928
                  omega
                cases h25937 : x 0 9
                · have f25938 : (x 0 9).toNat = 0 := by rw [h25937]; rfl
                  exact cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0000100 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d25907 d25867 d25875 d25855 d25814 f25928 g1 d19634 d19341 f19697 d19662 d19461 d25895 d19445 d19481 d19506 d25750 d19550 d19618 d19453 d19654 d25933 d25871 d19698 d25929 d25879 d19598 d25758 d19425 d25734 d19465 d19329 d19554 d19518 d25827 d19514
                · have f28371 : (x 0 9).toNat = 1 := by rw [h25937]; rfl
                  exact cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0000101 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d25867 d25919 d25855 d19634 d19341 f19697 f28371 d19662 d19461 d25895 d19445 d19481 d19506 d25750 d19550 d19618 d19453 d19654 d25933 d25871 d19698 d25929 d25879 d19598 d25758 d19425 d25835 d19666 d25859 d25734 d19465 d19329 d19554 d19518 d19514
              · have f30308 : (x (-1) 8).toNat = 1 := by rw [h25927]; rfl
                have d30309 : (x (-3) 10).toNat = 0 := by
                  have r30310 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
                  have e30311 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                  have e30312 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                  have e30313 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                  have e30314 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                  have e30315 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                  have e30316 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                  have b30317 := hb (x (-8) 7)
                  have b30318 := hb (x (-7) 6)
                  have b30319 := hb (x (-6) 5)
                  have b30320 := hb (x (-5) 4)
                  have b30321 := hb (x (-4) 11)
                  have b30322 := hb (x (-3) 10)
                  have b30323 := hb (x (-2) 9)
                  have b30324 := hb (x (-1) 8)
                  clear * - r30310 e30311 e30312 e30313 e30314 e30315 e30316 b30317 b30318 b30319 b30320 b30321 b30322 b30323 b30324 f30308 d25875
                  omega
                have d30325 : (x (-3) 1 && x (-3) 10).toNat = 0 := by
                  have r30326 := hand2 (x (-3) 1) (x (-3) 10)
                  have b30327 := hb (x (-3) 10)
                  have b30328 := hb (x (-3) 1 && x (-3) 10)
                  clear * - r30326 b30327 b30328 d30309
                  omega
                have d30329 : (x (-3) 9 && x (-3) 10).toNat = 0 := by
                  have r30330 := hand2 (x (-3) 9) (x (-3) 10)
                  have b30331 := hb (x (-3) 10)
                  have b30332 := hb (x (-3) 9 && x (-3) 10)
                  clear * - r30330 b30331 b30332 d30309
                  omega
                have d30333 : (x (-4) 11).toNat = 0 := by
                  have r30334 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
                  have e30335 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                  have e30336 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                  have e30337 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                  have e30338 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                  have e30339 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                  have e30340 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                  have b30341 := hb (x (-8) 7)
                  have b30342 := hb (x (-7) 6)
                  have b30343 := hb (x (-6) 5)
                  have b30344 := hb (x (-5) 4)
                  have b30345 := hb (x (-4) 11)
                  have b30346 := hb (x (-3) 10)
                  have b30347 := hb (x (-2) 9)
                  have b30348 := hb (x (-1) 8)
                  clear * - r30334 e30335 e30336 e30337 e30338 e30339 e30340 b30341 b30342 b30343 b30344 b30345 b30346 b30347 b30348 f30308 d25875 d30309
                  omega
                have d30349 : (x (-4) 1 && x (-4) 11).toNat = 0 := by
                  have r30350 := hand2 (x (-4) 1) (x (-4) 11)
                  have b30351 := hb (x (-4) 11)
                  have b30352 := hb (x (-4) 1 && x (-4) 11)
                  clear * - r30350 b30351 b30352 d30333
                  omega
                have d30353 : (x (-4) 2 && x (-4) 11).toNat = 0 := by
                  have r30354 := hand2 (x (-4) 2) (x (-4) 11)
                  have b30355 := hb (x (-4) 11)
                  have b30356 := hb (x (-4) 2 && x (-4) 11)
                  clear * - r30354 b30355 b30356 d30333
                  omega
                have d30357 : (x (-4) 10 && x (-4) 11).toNat = 0 := by
                  have r30358 := hand2 (x (-4) 10) (x (-4) 11)
                  have b30359 := hb (x (-4) 11)
                  have b30360 := hb (x (-4) 10 && x (-4) 11)
                  clear * - r30358 b30359 b30360 d30333
                  omega
                have d30361 : (x (-5) 4).toNat = 0 := by
                  have r30362 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
                  have e30363 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                  have e30364 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                  have e30365 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                  have e30366 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                  have e30367 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                  have e30368 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                  have b30369 := hb (x (-8) 7)
                  have b30370 := hb (x (-7) 6)
                  have b30371 := hb (x (-6) 5)
                  have b30372 := hb (x (-5) 4)
                  have b30373 := hb (x (-4) 11)
                  have b30374 := hb (x (-3) 10)
                  have b30375 := hb (x (-2) 9)
                  have b30376 := hb (x (-1) 8)
                  clear * - r30362 e30363 e30364 e30365 e30366 e30367 e30368 b30369 b30370 b30371 b30372 b30373 b30374 b30375 b30376 f30308 d25875 d30309 d30333
                  omega
                have d30377 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
                  have r30378 := hand1 (x (-5) 4) (x (-5) 14)
                  have b30379 := hb (x (-5) 4)
                  have b30380 := hb (x (-5) 4 && x (-5) 14)
                  clear * - r30378 b30379 b30380 d30361
                  omega
                have d30381 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
                  have r30382 := hand1 (x (-5) 4) (x (-5) 13)
                  have b30383 := hb (x (-5) 4)
                  have b30384 := hb (x (-5) 4 && x (-5) 13)
                  clear * - r30382 b30383 b30384 d30361
                  omega
                have d30385 : (x (-5) 4 && x (-5) 11).toNat = 0 := by
                  have r30386 := hand1 (x (-5) 4) (x (-5) 11)
                  have b30387 := hb (x (-5) 4)
                  have b30388 := hb (x (-5) 4 && x (-5) 11)
                  clear * - r30386 b30387 b30388 d30361
                  omega
                have d30389 : (x (-5) 4 && x (-5) 10).toNat = 0 := by
                  have r30390 := hand1 (x (-5) 4) (x (-5) 10)
                  have b30391 := hb (x (-5) 4)
                  have b30392 := hb (x (-5) 4 && x (-5) 10)
                  clear * - r30390 b30391 b30392 d30361
                  omega
                have d30393 : (x (-5) 4 && x (-5) 9).toNat = 0 := by
                  have r30394 := hand1 (x (-5) 4) (x (-5) 9)
                  have b30395 := hb (x (-5) 4)
                  have b30396 := hb (x (-5) 4 && x (-5) 9)
                  clear * - r30394 b30395 b30396 d30361
                  omega
                have d30397 : (x (-6) 5).toNat = 0 := by
                  have r30398 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
                  have e30399 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                  have e30400 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                  have e30401 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                  have e30402 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                  have e30403 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                  have e30404 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                  have b30405 := hb (x (-8) 7)
                  have b30406 := hb (x (-7) 6)
                  have b30407 := hb (x (-6) 5)
                  have b30408 := hb (x (-5) 4)
                  have b30409 := hb (x (-4) 11)
                  have b30410 := hb (x (-3) 10)
                  have b30411 := hb (x (-2) 9)
                  have b30412 := hb (x (-1) 8)
                  clear * - r30398 e30399 e30400 e30401 e30402 e30403 e30404 b30405 b30406 b30407 b30408 b30409 b30410 b30411 b30412 f30308 d25875 d30309 d30333 d30361
                  omega
                have d30413 : (x (-6) 5 && x (-6) 14).toNat = 0 := by
                  have r30414 := hand1 (x (-6) 5) (x (-6) 14)
                  have b30415 := hb (x (-6) 5)
                  have b30416 := hb (x (-6) 5 && x (-6) 14)
                  clear * - r30414 b30415 b30416 d30397
                  omega
                have d30417 : (x (-6) 5 && x (-6) 12).toNat = 0 := by
                  have r30418 := hand1 (x (-6) 5) (x (-6) 12)
                  have b30419 := hb (x (-6) 5)
                  have b30420 := hb (x (-6) 5 && x (-6) 12)
                  clear * - r30418 b30419 b30420 d30397
                  omega
                have d30421 : (x (-6) 5 && x (-6) 11).toNat = 0 := by
                  have r30422 := hand1 (x (-6) 5) (x (-6) 11)
                  have b30423 := hb (x (-6) 5)
                  have b30424 := hb (x (-6) 5 && x (-6) 11)
                  clear * - r30422 b30423 b30424 d30397
                  omega
                have d30425 : (x (-6) 5 && x (-6) 10).toNat = 0 := by
                  have r30426 := hand1 (x (-6) 5) (x (-6) 10)
                  have b30427 := hb (x (-6) 5)
                  have b30428 := hb (x (-6) 5 && x (-6) 10)
                  clear * - r30426 b30427 b30428 d30397
                  omega
                have d30429 : (x (-7) 6).toNat = 0 := by
                  have r30430 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
                  have e30431 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                  have e30432 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                  have e30433 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                  have e30434 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                  have e30435 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                  have e30436 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                  have b30437 := hb (x (-8) 7)
                  have b30438 := hb (x (-7) 6)
                  have b30439 := hb (x (-6) 5)
                  have b30440 := hb (x (-5) 4)
                  have b30441 := hb (x (-4) 11)
                  have b30442 := hb (x (-3) 10)
                  have b30443 := hb (x (-2) 9)
                  have b30444 := hb (x (-1) 8)
                  clear * - r30430 e30431 e30432 e30433 e30434 e30435 e30436 b30437 b30438 b30439 b30440 b30441 b30442 b30443 b30444 f30308 d25875 d30309 d30333 d30361 d30397
                  omega
                have d30445 : (x (-7) 6 && x (-7) 13).toNat = 0 := by
                  have r30446 := hand1 (x (-7) 6) (x (-7) 13)
                  have b30447 := hb (x (-7) 6)
                  have b30448 := hb (x (-7) 6 && x (-7) 13)
                  clear * - r30446 b30447 b30448 d30429
                  omega
                have d30449 : (x (-7) 6 && x (-7) 12).toNat = 0 := by
                  have r30450 := hand1 (x (-7) 6) (x (-7) 12)
                  have b30451 := hb (x (-7) 6)
                  have b30452 := hb (x (-7) 6 && x (-7) 12)
                  clear * - r30450 b30451 b30452 d30429
                  omega
                have d30453 : (x (-7) 6 && x (-7) 11).toNat = 0 := by
                  have r30454 := hand1 (x (-7) 6) (x (-7) 11)
                  have b30455 := hb (x (-7) 6)
                  have b30456 := hb (x (-7) 6 && x (-7) 11)
                  clear * - r30454 b30455 b30456 d30429
                  omega
                have d30457 : (x (-8) 7).toNat = 0 := by
                  have r30458 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
                  have e30459 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                  have e30460 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                  have e30461 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                  have e30462 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                  have e30463 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                  have e30464 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                  have b30465 := hb (x (-8) 7)
                  have b30466 := hb (x (-7) 6)
                  have b30467 := hb (x (-6) 5)
                  have b30468 := hb (x (-5) 4)
                  have b30469 := hb (x (-4) 11)
                  have b30470 := hb (x (-3) 10)
                  have b30471 := hb (x (-2) 9)
                  have b30472 := hb (x (-1) 8)
                  clear * - r30458 e30459 e30460 e30461 e30462 e30463 e30464 b30465 b30466 b30467 b30468 b30469 b30470 b30471 b30472 f30308 d25875 d30309 d30333 d30361 d30397 d30429
                  omega
                have d30473 : (x (-8) 7 && x (-8) 14).toNat = 0 := by
                  have r30474 := hand1 (x (-8) 7) (x (-8) 14)
                  have b30475 := hb (x (-8) 7)
                  have b30476 := hb (x (-8) 7 && x (-8) 14)
                  clear * - r30474 b30475 b30476 d30457
                  omega
                have d30477 : (x (-8) 7 && x (-8) 13).toNat = 0 := by
                  have r30478 := hand1 (x (-8) 7) (x (-8) 13)
                  have b30479 := hb (x (-8) 7)
                  have b30480 := hb (x (-8) 7 && x (-8) 13)
                  clear * - r30478 b30479 b30480 d30457
                  omega
                have d30481 : (x (-8) 7 && x (-8) 12).toNat = 0 := by
                  have r30482 := hand1 (x (-8) 7) (x (-8) 12)
                  have b30483 := hb (x (-8) 7)
                  have b30484 := hb (x (-8) 7 && x (-8) 12)
                  clear * - r30482 b30483 b30484 d30457
                  omega
                cases h30485 : x 0 9
                · have f30486 : (x 0 9).toNat = 0 := by rw [h30485]; rfl
                  cases h30487 : x 0 12
                  · have f30488 : (x 0 12).toNat = 0 := by rw [h30487]; rfl
                    cases h30489 : x 1 1
                    · have f30490 : (x 1 1).toNat = 0 := by rw [h30489]; rfl
                      have d30491 : (x 1 9).toNat = 0 := by
                        have r30492 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
                        have b30493 := hb (x 1 1)
                        have b30494 := hb (x 1 9)
                        clear * - r30492 b30493 b30494 f30490
                        omega
                      have d30495 : (x 2 14).toNat = 1 := by
                        have r30496 : (x 2 14).toNat + (x 1 1).toNat = 1 := hd14 2
                        have b30497 := hb (x 1 1)
                        have b30498 := hb (x 2 14)
                        clear * - r30496 b30497 b30498 f30490
                        omega
                      cases h30499 : x 1 3
                      · have f30500 : (x 1 3).toNat = 0 := by rw [h30499]; rfl
                        have d30501 : (x 1 11).toNat = 0 := by
                          have r30502 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
                          have b30503 := hb (x 1 3)
                          have b30504 := hb (x 1 11)
                          clear * - r30502 b30503 b30504 f30500
                          omega
                        cases h30505 : x (-1) 4
                        · have f30506 : (x (-1) 4).toNat = 0 := by rw [h30505]; rfl
                          exact cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a00001100000 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 f30506 d25750 d19550 d19618 d25734 d19465 d19329 d19518
                        · have f31072 : (x (-1) 4).toNat = 1 := by rw [h30505]; rfl
                          have d31073 : (x (-1) 12).toNat = 1 := by
                            have r31074 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
                            have b31075 := hb (x (-1) 4)
                            have b31076 := hb (x (-1) 12)
                            clear * - r31074 b31075 b31076 f31072
                            omega
                          have d31077 : (x (-3) 2).toNat = 0 := by
                            have r31078 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
                            have e31079 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                            have e31080 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                            have b31081 := hb (x (-4) 3)
                            have b31082 := hb (x (-3) 2)
                            have b31083 := hb (x (-2) 13)
                            have b31084 := hb (x (-1) 12)
                            clear * - r31078 e31079 e31080 b31081 b31082 b31083 b31084 d31073 d25855
                            omega
                          have d31085 : (x (-3) 2 && x (-3) 13).toNat = 0 := by
                            have r31086 := hand1 (x (-3) 2) (x (-3) 13)
                            have b31087 := hb (x (-3) 2)
                            have b31088 := hb (x (-3) 2 && x (-3) 13)
                            clear * - r31086 b31087 b31088 d31077
                            omega
                          have d31089 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
                            have r31090 := hand1 (x (-3) 2) (x (-3) 12)
                            have b31091 := hb (x (-3) 2)
                            have b31092 := hb (x (-3) 2 && x (-3) 12)
                            clear * - r31090 b31091 b31092 d31077
                            omega
                          have d31093 : (x (-3) 2 && x (-3) 11).toNat = 0 := by
                            have r31094 := hand1 (x (-3) 2) (x (-3) 11)
                            have b31095 := hb (x (-3) 2)
                            have b31096 := hb (x (-3) 2 && x (-3) 11)
                            clear * - r31094 b31095 b31096 d31077
                            omega
                          have d31097 : (x (-3) 2 && x (-3) 9).toNat = 0 := by
                            have r31098 := hand1 (x (-3) 2) (x (-3) 9)
                            have b31099 := hb (x (-3) 2)
                            have b31100 := hb (x (-3) 2 && x (-3) 9)
                            clear * - r31098 b31099 b31100 d31077
                            omega
                          have d31101 : (x (-3) 2 && x (-3) 8).toNat = 0 := by
                            have r31102 := hand1 (x (-3) 2) (x (-3) 8)
                            have b31103 := hb (x (-3) 2)
                            have b31104 := hb (x (-3) 2 && x (-3) 8)
                            clear * - r31102 b31103 b31104 d31077
                            omega
                          have d31105 : (x (-3) 2 && x (-3) 7).toNat = 0 := by
                            have r31106 := hand1 (x (-3) 2) (x (-3) 7)
                            have b31107 := hb (x (-3) 2)
                            have b31108 := hb (x (-3) 2 && x (-3) 7)
                            clear * - r31106 b31107 b31108 d31077
                            omega
                          have d31109 : (x (-1) 13).toNat = 1 := by
                            have r31110 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := hcov13 (-1)
                            have b31111 := hb (x (-3) 2)
                            have b31112 := hb (x (-1) 13)
                            have b31113 := hb (x (-2) 1 && x (-2) 14)
                            clear * - r31110 b31111 b31112 b31113 d25827 d31077
                            omega
                          have d31114 : (x (-2) 2).toNat = 0 := by
                            have r31115 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := hd12 0
                            have e31116 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
                            have e31117 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
                            have b31118 := hb (x (-3) 3)
                            have b31119 := hb (x (-2) 2)
                            have b31120 := hb (x (-1) 13)
                            have b31121 := hb (x 0 12)
                            clear * - r31115 e31116 e31117 b31118 b31119 b31120 b31121 f30488 d31109
                            omega
                          have d31122 : (x (-2) 2 && x (-2) 8).toNat = 0 := by
                            have r31123 := hand1 (x (-2) 2) (x (-2) 8)
                            have b31124 := hb (x (-2) 2)
                            have b31125 := hb (x (-2) 2 && x (-2) 8)
                            clear * - r31123 b31124 b31125 d31114
                            omega
                          have d31126 : (x (-2) 10).toNat = 0 := by
                            have r31127 : (x (-2) 10).toNat ≤ (x (-2) 2).toNat := himp _ _ (hp10 (-2))
                            have b31128 := hb (x (-2) 2)
                            have b31129 := hb (x (-2) 10)
                            clear * - r31127 b31128 b31129 d31114
                            omega
                          have d31130 : (x (-3) 3).toNat = 0 := by
                            have r31131 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := hd12 0
                            have e31132 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
                            have e31133 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
                            have b31134 := hb (x (-3) 3)
                            have b31135 := hb (x (-2) 2)
                            have b31136 := hb (x (-1) 13)
                            have b31137 := hb (x 0 12)
                            clear * - r31131 e31132 e31133 b31134 b31135 b31136 b31137 f30488 d31109 d31114
                            omega
                          have d31138 : (x (-3) 3 && x (-3) 9).toNat = 0 := by
                            have r31139 := hand1 (x (-3) 3) (x (-3) 9)
                            have b31140 := hb (x (-3) 3)
                            have b31141 := hb (x (-3) 3 && x (-3) 9)
                            clear * - r31139 b31140 b31141 d31130
                            omega
                          have d31142 : (x (-3) 11).toNat = 0 := by
                            have r31143 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
                            have b31144 := hb (x (-3) 3)
                            have b31145 := hb (x (-3) 11)
                            clear * - r31143 b31144 b31145 d31130
                            omega
                          have d31146 : (x (-3) 1 && x (-3) 11).toNat = 0 := by
                            have r31147 := hand2 (x (-3) 1) (x (-3) 11)
                            have b31148 := hb (x (-3) 11)
                            have b31149 := hb (x (-3) 1 && x (-3) 11)
                            clear * - r31147 b31148 b31149 d31142
                            omega
                          have d31150 : (x (-4) 3).toNat = 0 := by
                            have r31151 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
                            have e31152 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                            have e31153 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                            have b31154 := hb (x (-4) 3)
                            have b31155 := hb (x (-3) 2)
                            have b31156 := hb (x (-2) 13)
                            have b31157 := hb (x (-1) 12)
                            clear * - r31151 e31152 e31153 b31154 b31155 b31156 b31157 d31073 d25855 d31077
                            omega
                          have d31158 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
                            have r31159 := hand1 (x (-4) 3) (x (-4) 14)
                            have b31160 := hb (x (-4) 3)
                            have b31161 := hb (x (-4) 3 && x (-4) 14)
                            clear * - r31159 b31160 b31161 d31150
                            omega
                          have d31162 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
                            have r31163 := hand1 (x (-4) 3) (x (-4) 13)
                            have b31164 := hb (x (-4) 3)
                            have b31165 := hb (x (-4) 3 && x (-4) 13)
                            clear * - r31163 b31164 b31165 d31150
                            omega
                          have d31166 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
                            have r31167 := hand1 (x (-4) 3) (x (-4) 12)
                            have b31168 := hb (x (-4) 3)
                            have b31169 := hb (x (-4) 3 && x (-4) 12)
                            clear * - r31167 b31168 b31169 d31150
                            omega
                          have d31170 : (x (-4) 3 && x (-4) 10).toNat = 0 := by
                            have r31171 := hand1 (x (-4) 3) (x (-4) 10)
                            have b31172 := hb (x (-4) 3)
                            have b31173 := hb (x (-4) 3 && x (-4) 10)
                            clear * - r31171 b31172 b31173 d31150
                            omega
                          have d31174 : (x (-4) 3 && x (-4) 9).toNat = 0 := by
                            have r31175 := hand1 (x (-4) 3) (x (-4) 9)
                            have b31176 := hb (x (-4) 3)
                            have b31177 := hb (x (-4) 3 && x (-4) 9)
                            clear * - r31175 b31176 b31177 d31150
                            omega
                          have d31178 : (x (-4) 3 && x (-4) 8).toNat = 0 := by
                            have r31179 := hand1 (x (-4) 3) (x (-4) 8)
                            have b31180 := hb (x (-4) 3)
                            have b31181 := hb (x (-4) 3 && x (-4) 8)
                            clear * - r31179 b31180 b31181 d31150
                            omega
                          have d31182 : (x (-1) 11).toNat = 1 := by
                            have r31183 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := hcov11 (-1)
                            have b31184 := hb (x (-5) 4)
                            have b31185 := hb (x (-1) 11)
                            have b31186 := hb (x (-2) 1 && x (-2) 12)
                            have b31187 := hb (x (-3) 2 && x (-3) 13)
                            have b31188 := hb (x (-4) 3 && x (-4) 14)
                            clear * - r31183 b31184 b31185 b31186 b31187 b31188 d25831 d31085 d31158 d30361
                            omega
                          have d31189 : (x (-1) 10).toNat = 1 := by
                            have r31190 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := hcov10 (-1)
                            have b31191 := hb (x (-6) 5)
                            have b31192 := hb (x (-1) 10)
                            have b31193 := hb (x (-2) 1 && x (-2) 11)
                            have b31194 := hb (x (-3) 2 && x (-3) 12)
                            have b31195 := hb (x (-4) 3 && x (-4) 13)
                            have b31196 := hb (x (-5) 4 && x (-5) 14)
                            clear * - r31190 b31191 b31192 b31193 b31194 b31195 b31196 d25835 d31089 d31162 d30377 d30397
                            omega
                          have d31197 : (x (-1) 9).toNat = 1 := by
                            have r31198 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := hcov9 (-1)
                            have b31199 := hb (x (-7) 6)
                            have b31200 := hb (x (-1) 9)
                            have b31201 := hb (x (-2) 1 && x (-2) 10)
                            have b31202 := hb (x (-3) 2 && x (-3) 11)
                            have b31203 := hb (x (-4) 3 && x (-4) 12)
                            have b31204 := hb (x (-5) 4 && x (-5) 13)
                            have b31205 := hb (x (-6) 5 && x (-6) 14)
                            clear * - r31198 b31199 b31200 b31201 b31202 b31203 b31204 b31205 d25839 d31093 d31166 d30381 d30413 d30429
                            omega
                          have d31206 : (x 3 8).toNat = 0 := by
                            have r31207 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := hd8 3
                            have e31208 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
                            have e31209 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
                            have e31210 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
                            have e31211 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
                            have e31212 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
                            have e31213 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
                            have b31214 := hb (x (-4) 7)
                            have b31215 := hb (x (-3) 6)
                            have b31216 := hb (x (-2) 5)
                            have b31217 := hb (x (-1) 4)
                            have b31218 := hb (x 0 11)
                            have b31219 := hb (x 1 10)
                            have b31220 := hb (x 2 9)
                            have b31221 := hb (x 3 8)
                            clear * - r31207 e31208 e31209 e31210 e31211 e31212 e31213 b31214 b31215 b31216 b31217 b31218 b31219 b31220 b31221 d19481 d19662 f31072 d25867
                            omega
                          have d31222 : (x 3 8 && x 3 13).toNat = 0 := by
                            have r31223 := hand1 (x 3 8) (x 3 13)
                            have b31224 := hb (x 3 8)
                            have b31225 := hb (x 3 8 && x 3 13)
                            clear * - r31223 b31224 b31225 d31206
                            omega
                          have d31226 : (x 3 3 && x 3 8).toNat = 0 := by
                            have r31227 := hand2 (x 3 3) (x 3 8)
                            have b31228 := hb (x 3 8)
                            have b31229 := hb (x 3 3 && x 3 8)
                            clear * - r31227 b31228 b31229 d31206
                            omega
                          have d31230 : (x 2 9).toNat = 0 := by
                            have r31231 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := hd8 3
                            have e31232 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
                            have e31233 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
                            have e31234 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
                            have e31235 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
                            have e31236 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
                            have e31237 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
                            have b31238 := hb (x (-4) 7)
                            have b31239 := hb (x (-3) 6)
                            have b31240 := hb (x (-2) 5)
                            have b31241 := hb (x (-1) 4)
                            have b31242 := hb (x 0 11)
                            have b31243 := hb (x 1 10)
                            have b31244 := hb (x 2 9)
                            have b31245 := hb (x 3 8)
                            clear * - r31231 e31232 e31233 e31234 e31235 e31236 e31237 b31238 b31239 b31240 b31241 b31242 b31243 b31244 b31245 d31206 d19481 d19662 f31072 d25867
                            omega
                          have d31246 : (x 2 9 && x 2 14).toNat = 0 := by
                            have r31247 := hand1 (x 2 9) (x 2 14)
                            have b31248 := hb (x 2 9)
                            have b31249 := hb (x 2 9 && x 2 14)
                            clear * - r31247 b31248 b31249 d31230
                            omega
                          have d31250 : (x 2 9 && x 2 13).toNat = 0 := by
                            have r31251 := hand1 (x 2 9) (x 2 13)
                            have b31252 := hb (x 2 9)
                            have b31253 := hb (x 2 9 && x 2 13)
                            clear * - r31251 b31252 b31253 d31230
                            omega
                          have d31254 : (x (-3) 6).toNat = 0 := by
                            have r31255 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := hd8 3
                            have e31256 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
                            have e31257 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
                            have e31258 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
                            have e31259 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
                            have e31260 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
                            have e31261 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
                            have b31262 := hb (x (-4) 7)
                            have b31263 := hb (x (-3) 6)
                            have b31264 := hb (x (-2) 5)
                            have b31265 := hb (x (-1) 4)
                            have b31266 := hb (x 0 11)
                            have b31267 := hb (x 1 10)
                            have b31268 := hb (x 2 9)
                            have b31269 := hb (x 3 8)
                            clear * - r31255 e31256 e31257 e31258 e31259 e31260 e31261 b31262 b31263 b31264 b31265 b31266 b31267 b31268 b31269 d31206 d31230 d19481 d19662 f31072 d25867
                            omega
                          have d31270 : (x (-3) 1 && x (-3) 6).toNat = 0 := by
                            have r31271 := hand2 (x (-3) 1) (x (-3) 6)
                            have b31272 := hb (x (-3) 6)
                            have b31273 := hb (x (-3) 1 && x (-3) 6)
                            clear * - r31271 b31272 b31273 d31254
                            omega
                          have d31274 : (x (-4) 7).toNat = 0 := by
                            have r31275 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := hd8 3
                            have e31276 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
                            have e31277 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
                            have e31278 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
                            have e31279 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
                            have e31280 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
                            have e31281 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
                            have b31282 := hb (x (-4) 7)
                            have b31283 := hb (x (-3) 6)
                            have b31284 := hb (x (-2) 5)
                            have b31285 := hb (x (-1) 4)
                            have b31286 := hb (x 0 11)
                            have b31287 := hb (x 1 10)
                            have b31288 := hb (x 2 9)
                            have b31289 := hb (x 3 8)
                            clear * - r31275 e31276 e31277 e31278 e31279 e31280 e31281 b31282 b31283 b31284 b31285 b31286 b31287 b31288 b31289 d31206 d31230 d19481 d19662 f31072 d25867 d31254
                            omega
                          have d31290 : (x (-4) 2 && x (-4) 7).toNat = 0 := by
                            have r31291 := hand2 (x (-4) 2) (x (-4) 7)
                            have b31292 := hb (x (-4) 7)
                            have b31293 := hb (x (-4) 2 && x (-4) 7)
                            clear * - r31291 b31292 b31293 d31274
                            omega
                          have d31294 : (x 2 8).toNat = 0 := by
                            have r31295 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := hd8 2
                            have e31296 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                            have e31297 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                            have e31298 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                            have e31299 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                            have e31300 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                            have e31301 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                            have b31302 := hb (x (-5) 7)
                            have b31303 := hb (x (-4) 6)
                            have b31304 := hb (x (-3) 5)
                            have b31305 := hb (x (-2) 4)
                            have b31306 := hb (x (-1) 11)
                            have b31307 := hb (x 0 10)
                            have b31308 := hb (x 1 9)
                            have b31309 := hb (x 2 8)
                            clear * - r31295 e31296 e31297 e31298 e31299 e31300 e31301 b31302 b31303 b31304 b31305 b31306 b31307 b31308 b31309 d30491 d19389 d31182
                            omega
                          have d31310 : (x 2 8 && x 2 13).toNat = 0 := by
                            have r31311 := hand1 (x 2 8) (x 2 13)
                            have b31312 := hb (x 2 8)
                            have b31313 := hb (x 2 8 && x 2 13)
                            clear * - r31311 b31312 b31313 d31294
                            omega
                          have d31314 : (x 2 3 && x 2 8).toNat = 0 := by
                            have r31315 := hand2 (x 2 3) (x 2 8)
                            have b31316 := hb (x 2 8)
                            have b31317 := hb (x 2 3 && x 2 8)
                            clear * - r31315 b31316 b31317 d31294
                            omega
                          have d31318 : (x (-2) 4).toNat = 0 := by
                            have r31319 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := hd8 2
                            have e31320 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                            have e31321 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                            have e31322 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                            have e31323 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                            have e31324 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                            have e31325 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                            have b31326 := hb (x (-5) 7)
                            have b31327 := hb (x (-4) 6)
                            have b31328 := hb (x (-3) 5)
                            have b31329 := hb (x (-2) 4)
                            have b31330 := hb (x (-1) 11)
                            have b31331 := hb (x 0 10)
                            have b31332 := hb (x 1 9)
                            have b31333 := hb (x 2 8)
                            clear * - r31319 e31320 e31321 e31322 e31323 e31324 e31325 b31326 b31327 b31328 b31329 b31330 b31331 b31332 b31333 d31294 d30491 d19389 d31182
                            omega
                          have d31334 : (x (-3) 5).toNat = 0 := by
                            have r31335 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := hd8 2
                            have e31336 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                            have e31337 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                            have e31338 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                            have e31339 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                            have e31340 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                            have e31341 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                            have b31342 := hb (x (-5) 7)
                            have b31343 := hb (x (-4) 6)
                            have b31344 := hb (x (-3) 5)
                            have b31345 := hb (x (-2) 4)
                            have b31346 := hb (x (-1) 11)
                            have b31347 := hb (x 0 10)
                            have b31348 := hb (x 1 9)
                            have b31349 := hb (x 2 8)
                            clear * - r31335 e31336 e31337 e31338 e31339 e31340 e31341 b31342 b31343 b31344 b31345 b31346 b31347 b31348 b31349 d31294 d30491 d19389 d31182 d31318
                            omega
                          have d31350 : (x (-4) 6).toNat = 0 := by
                            have r31351 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := hd8 2
                            have e31352 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                            have e31353 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                            have e31354 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                            have e31355 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                            have e31356 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                            have e31357 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                            have b31358 := hb (x (-5) 7)
                            have b31359 := hb (x (-4) 6)
                            have b31360 := hb (x (-3) 5)
                            have b31361 := hb (x (-2) 4)
                            have b31362 := hb (x (-1) 11)
                            have b31363 := hb (x 0 10)
                            have b31364 := hb (x 1 9)
                            have b31365 := hb (x 2 8)
                            clear * - r31351 e31352 e31353 e31354 e31355 e31356 e31357 b31358 b31359 b31360 b31361 b31362 b31363 b31364 b31365 d31294 d30491 d19389 d31182 d31318 d31334
                            omega
                          have d31366 : (x (-4) 2 && x (-4) 6).toNat = 0 := by
                            have r31367 := hand2 (x (-4) 2) (x (-4) 6)
                            have b31368 := hb (x (-4) 6)
                            have b31369 := hb (x (-4) 2 && x (-4) 6)
                            clear * - r31367 b31368 b31369 d31350
                            omega
                          have d31370 : (x (-5) 7).toNat = 0 := by
                            have r31371 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := hd8 2
                            have e31372 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                            have e31373 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                            have e31374 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                            have e31375 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                            have e31376 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                            have e31377 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                            have b31378 := hb (x (-5) 7)
                            have b31379 := hb (x (-4) 6)
                            have b31380 := hb (x (-3) 5)
                            have b31381 := hb (x (-2) 4)
                            have b31382 := hb (x (-1) 11)
                            have b31383 := hb (x 0 10)
                            have b31384 := hb (x 1 9)
                            have b31385 := hb (x 2 8)
                            clear * - r31371 e31372 e31373 e31374 e31375 e31376 e31377 b31378 b31379 b31380 b31381 b31382 b31383 b31384 b31385 d31294 d30491 d19389 d31182 d31318 d31334 d31350
                            omega
                          have d31386 : (x (-5) 3 && x (-5) 7).toNat = 0 := by
                            have r31387 := hand2 (x (-5) 3) (x (-5) 7)
                            have b31388 := hb (x (-5) 7)
                            have b31389 := hb (x (-5) 3 && x (-5) 7)
                            clear * - r31387 b31388 b31389 d31370
                            omega
                          have d31390 : (x 1 8).toNat = 0 := by
                            have r31391 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
                            have e31392 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                            have e31393 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                            have e31394 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                            have e31395 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                            have e31396 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                            have e31397 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                            have b31398 := hb (x (-6) 7)
                            have b31399 := hb (x (-5) 6)
                            have b31400 := hb (x (-4) 5)
                            have b31401 := hb (x (-3) 4)
                            have b31402 := hb (x (-2) 11)
                            have b31403 := hb (x (-1) 10)
                            have b31404 := hb (x 0 9)
                            have b31405 := hb (x 1 8)
                            clear * - r31391 e31392 e31393 e31394 e31395 e31396 e31397 b31398 b31399 b31400 b31401 b31402 b31403 b31404 b31405 f30486 d31189 d25919
                            omega
                          have d31406 : (x (-3) 4).toNat = 0 := by
                            have r31407 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
                            have e31408 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                            have e31409 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                            have e31410 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                            have e31411 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                            have e31412 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                            have e31413 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                            have b31414 := hb (x (-6) 7)
                            have b31415 := hb (x (-5) 6)
                            have b31416 := hb (x (-4) 5)
                            have b31417 := hb (x (-3) 4)
                            have b31418 := hb (x (-2) 11)
                            have b31419 := hb (x (-1) 10)
                            have b31420 := hb (x 0 9)
                            have b31421 := hb (x 1 8)
                            clear * - r31407 e31408 e31409 e31410 e31411 e31412 e31413 b31414 b31415 b31416 b31417 b31418 b31419 b31420 b31421 d31390 f30486 d31189 d25919
                            omega
                          have d31422 : (x (-3) 4 && x (-3) 9).toNat = 0 := by
                            have r31423 := hand1 (x (-3) 4) (x (-3) 9)
                            have b31424 := hb (x (-3) 4)
                            have b31425 := hb (x (-3) 4 && x (-3) 9)
                            clear * - r31423 b31424 b31425 d31406
                            omega
                          have d31426 : (x (-4) 5).toNat = 0 := by
                            have r31427 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
                            have e31428 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                            have e31429 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                            have e31430 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                            have e31431 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                            have e31432 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                            have e31433 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                            have b31434 := hb (x (-6) 7)
                            have b31435 := hb (x (-5) 6)
                            have b31436 := hb (x (-4) 5)
                            have b31437 := hb (x (-3) 4)
                            have b31438 := hb (x (-2) 11)
                            have b31439 := hb (x (-1) 10)
                            have b31440 := hb (x 0 9)
                            have b31441 := hb (x 1 8)
                            clear * - r31427 e31428 e31429 e31430 e31431 e31432 e31433 b31434 b31435 b31436 b31437 b31438 b31439 b31440 b31441 d31390 f30486 d31189 d25919 d31406
                            omega
                          have d31442 : (x (-4) 5 && x (-4) 10).toNat = 0 := by
                            have r31443 := hand1 (x (-4) 5) (x (-4) 10)
                            have b31444 := hb (x (-4) 5)
                            have b31445 := hb (x (-4) 5 && x (-4) 10)
                            clear * - r31443 b31444 b31445 d31426
                            omega
                          have d31446 : (x (-5) 6).toNat = 0 := by
                            have r31447 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
                            have e31448 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                            have e31449 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                            have e31450 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                            have e31451 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                            have e31452 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                            have e31453 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                            have b31454 := hb (x (-6) 7)
                            have b31455 := hb (x (-5) 6)
                            have b31456 := hb (x (-4) 5)
                            have b31457 := hb (x (-3) 4)
                            have b31458 := hb (x (-2) 11)
                            have b31459 := hb (x (-1) 10)
                            have b31460 := hb (x 0 9)
                            have b31461 := hb (x 1 8)
                            clear * - r31447 e31448 e31449 e31450 e31451 e31452 e31453 b31454 b31455 b31456 b31457 b31458 b31459 b31460 b31461 d31390 f30486 d31189 d25919 d31406 d31426
                            omega
                          have d31462 : (x (-5) 6 && x (-5) 11).toNat = 0 := by
                            have r31463 := hand1 (x (-5) 6) (x (-5) 11)
                            have b31464 := hb (x (-5) 6)
                            have b31465 := hb (x (-5) 6 && x (-5) 11)
                            clear * - r31463 b31464 b31465 d31446
                            omega
                          have d31466 : (x (-6) 7).toNat = 0 := by
                            have r31467 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
                            have e31468 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                            have e31469 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                            have e31470 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                            have e31471 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                            have e31472 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                            have e31473 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                            have b31474 := hb (x (-6) 7)
                            have b31475 := hb (x (-5) 6)
                            have b31476 := hb (x (-4) 5)
                            have b31477 := hb (x (-3) 4)
                            have b31478 := hb (x (-2) 11)
                            have b31479 := hb (x (-1) 10)
                            have b31480 := hb (x 0 9)
                            have b31481 := hb (x 1 8)
                            clear * - r31467 e31468 e31469 e31470 e31471 e31472 e31473 b31474 b31475 b31476 b31477 b31478 b31479 b31480 b31481 d31390 f30486 d31189 d25919 d31406 d31426 d31446
                            omega
                          have d31482 : (x (-6) 7 && x (-6) 12).toNat = 0 := by
                            have r31483 := hand1 (x (-6) 7) (x (-6) 12)
                            have b31484 := hb (x (-6) 7)
                            have b31485 := hb (x (-6) 7 && x (-6) 12)
                            clear * - r31483 b31484 b31485 d31466
                            omega
                          have d31486 : (x (-4) 4).toNat = 0 := by
                            have r31487 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
                            have e31488 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                            have e31489 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                            have e31490 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                            have e31491 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                            have e31492 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                            have e31493 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                            have b31494 := hb (x (-7) 7)
                            have b31495 := hb (x (-6) 6)
                            have b31496 := hb (x (-5) 5)
                            have b31497 := hb (x (-4) 4)
                            have b31498 := hb (x (-3) 11)
                            have b31499 := hb (x (-2) 10)
                            have b31500 := hb (x (-1) 9)
                            have b31501 := hb (x 0 8)
                            clear * - r31487 e31488 e31489 e31490 e31491 e31492 e31493 b31494 b31495 b31496 b31497 b31498 b31499 b31500 b31501 f19677 d31197 d31126 d31142
                            omega
                          have d31502 : (x (-4) 4 && x (-4) 10).toNat = 0 := by
                            have r31503 := hand1 (x (-4) 4) (x (-4) 10)
                            have b31504 := hb (x (-4) 4)
                            have b31505 := hb (x (-4) 4 && x (-4) 10)
                            clear * - r31503 b31504 b31505 d31486
                            omega
                          have d31506 : (x (-5) 5).toNat = 0 := by
                            have r31507 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
                            have e31508 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                            have e31509 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                            have e31510 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                            have e31511 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                            have e31512 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                            have e31513 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                            have b31514 := hb (x (-7) 7)
                            have b31515 := hb (x (-6) 6)
                            have b31516 := hb (x (-5) 5)
                            have b31517 := hb (x (-4) 4)
                            have b31518 := hb (x (-3) 11)
                            have b31519 := hb (x (-2) 10)
                            have b31520 := hb (x (-1) 9)
                            have b31521 := hb (x 0 8)
                            clear * - r31507 e31508 e31509 e31510 e31511 e31512 e31513 b31514 b31515 b31516 b31517 b31518 b31519 b31520 b31521 f19677 d31197 d31126 d31142 d31486
                            omega
                          have d31522 : (x (-5) 5 && x (-5) 11).toNat = 0 := by
                            have r31523 := hand1 (x (-5) 5) (x (-5) 11)
                            have b31524 := hb (x (-5) 5)
                            have b31525 := hb (x (-5) 5 && x (-5) 11)
                            clear * - r31523 b31524 b31525 d31506
                            omega
                          have d31526 : (x (-6) 6).toNat = 0 := by
                            have r31527 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
                            have e31528 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                            have e31529 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                            have e31530 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                            have e31531 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                            have e31532 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                            have e31533 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                            have b31534 := hb (x (-7) 7)
                            have b31535 := hb (x (-6) 6)
                            have b31536 := hb (x (-5) 5)
                            have b31537 := hb (x (-4) 4)
                            have b31538 := hb (x (-3) 11)
                            have b31539 := hb (x (-2) 10)
                            have b31540 := hb (x (-1) 9)
                            have b31541 := hb (x 0 8)
                            clear * - r31527 e31528 e31529 e31530 e31531 e31532 e31533 b31534 b31535 b31536 b31537 b31538 b31539 b31540 b31541 f19677 d31197 d31126 d31142 d31486 d31506
                            omega
                          have d31542 : (x (-6) 6 && x (-6) 12).toNat = 0 := by
                            have r31543 := hand1 (x (-6) 6) (x (-6) 12)
                            have b31544 := hb (x (-6) 6)
                            have b31545 := hb (x (-6) 6 && x (-6) 12)
                            clear * - r31543 b31544 b31545 d31526
                            omega
                          have d31546 : (x (-7) 7).toNat = 0 := by
                            have r31547 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
                            have e31548 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                            have e31549 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                            have e31550 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                            have e31551 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                            have e31552 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                            have e31553 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                            have b31554 := hb (x (-7) 7)
                            have b31555 := hb (x (-6) 6)
                            have b31556 := hb (x (-5) 5)
                            have b31557 := hb (x (-4) 4)
                            have b31558 := hb (x (-3) 11)
                            have b31559 := hb (x (-2) 10)
                            have b31560 := hb (x (-1) 9)
                            have b31561 := hb (x 0 8)
                            clear * - r31547 e31548 e31549 e31550 e31551 e31552 e31553 b31554 b31555 b31556 b31557 b31558 b31559 b31560 b31561 f19677 d31197 d31126 d31142 d31486 d31506 d31526
                            omega
                          have d31562 : (x (-7) 7 && x (-7) 13).toNat = 0 := by
                            have r31563 := hand1 (x (-7) 7) (x (-7) 13)
                            have b31564 := hb (x (-7) 7)
                            have b31565 := hb (x (-7) 7 && x (-7) 13)
                            clear * - r31563 b31564 b31565 d31546
                            omega
                          cases h31566 : x (-1) 5
                          · have f31567 : (x (-1) 5).toNat = 0 := by rw [h31566]; rfl
                            exact cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a000011000010 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d30333 d30309 d31142 d25875 d31126 d25919 d25855 f31567 f30308 d31197 d31189 d31073 d19688 d19341 f19697 f19677 f30486 d19662 g14 f30500 d25798 d19445 d31390 d19481 d25782 d19409 d25750 d31230 d25726 d19501 d30495 d19550 d19618 d19530 d31206 d19586 d19546 d25774 d25810 d19361 d25923 d25851 d31105 d31178 d30393 d30425 d30453 d30481 d19353 d25915 d31422 d31442 d31462 d31482 d31226 d25766 d19489 d19349 d25863 d31122 d31138 d31502 d31522 d31542 d31562 d19538 d19433 d25843 d31097 d31170 d30385 d30417 d30445 d30473 d19534 d30325 d30353 d19598 d25758 d19425 d30349 d25738 d25790 d19333 d19558 d19421 d25754 d19518 d19514
                          · have f33996 : (x (-1) 5).toNat = 1 := by rw [h31566]; rfl
                            have d33997 : (x 4 8).toNat = 0 := by
                              have r33998 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := hd8 4
                              have e33999 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
                              have e34000 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
                              have e34001 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
                              have e34002 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
                              have e34003 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
                              have e34004 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
                              have b34005 := hb (x (-3) 7)
                              have b34006 := hb (x (-2) 6)
                              have b34007 := hb (x (-1) 5)
                              have b34008 := hb (x 0 4)
                              have b34009 := hb (x 1 11)
                              have b34010 := hb (x 2 10)
                              have b34011 := hb (x 3 9)
                              have b34012 := hb (x 4 8)
                              clear * - r33998 e33999 e34000 e34001 e34002 e34003 e34004 b34005 b34006 b34007 b34008 b34009 b34010 b34011 b34012 d30501 f19675 f33996
                              omega
                            have d34013 : (x 4 1 && x 4 8).toNat = 0 := by
                              have r34014 := hand2 (x 4 1) (x 4 8)
                              have b34015 := hb (x 4 8)
                              have b34016 := hb (x 4 1 && x 4 8)
                              clear * - r34014 b34015 b34016 d33997
                              omega
                            have d34017 : (x 4 8 && x 4 14).toNat = 0 := by
                              have r34018 := hand1 (x 4 8) (x 4 14)
                              have b34019 := hb (x 4 8)
                              have b34020 := hb (x 4 8 && x 4 14)
                              clear * - r34018 b34019 b34020 d33997
                              omega
                            have d34021 : (x 4 2 && x 4 8).toNat = 0 := by
                              have r34022 := hand2 (x 4 2) (x 4 8)
                              have b34023 := hb (x 4 8)
                              have b34024 := hb (x 4 2 && x 4 8)
                              clear * - r34022 b34023 b34024 d33997
                              omega
                            have d34025 : (x 4 8 && x 4 12).toNat = 0 := by
                              have r34026 := hand1 (x 4 8) (x 4 12)
                              have b34027 := hb (x 4 8)
                              have b34028 := hb (x 4 8 && x 4 12)
                              clear * - r34026 b34027 b34028 d33997
                              omega
                            have d34029 : (x 4 8 && x 4 11).toNat = 0 := by
                              have r34030 := hand1 (x 4 8) (x 4 11)
                              have b34031 := hb (x 4 8)
                              have b34032 := hb (x 4 8 && x 4 11)
                              clear * - r34030 b34031 b34032 d33997
                              omega
                            have d34033 : (x 3 9).toNat = 0 := by
                              have r34034 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := hd8 4
                              have e34035 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
                              have e34036 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
                              have e34037 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
                              have e34038 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
                              have e34039 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
                              have e34040 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
                              have b34041 := hb (x (-3) 7)
                              have b34042 := hb (x (-2) 6)
                              have b34043 := hb (x (-1) 5)
                              have b34044 := hb (x 0 4)
                              have b34045 := hb (x 1 11)
                              have b34046 := hb (x 2 10)
                              have b34047 := hb (x 3 9)
                              have b34048 := hb (x 4 8)
                              clear * - r34034 e34035 e34036 e34037 e34038 e34039 e34040 b34041 b34042 b34043 b34044 b34045 b34046 b34047 b34048 d33997 d30501 f19675 f33996
                              omega
                            have d34049 : (x 3 3 && x 3 9).toNat = 0 := by
                              have r34050 := hand2 (x 3 3) (x 3 9)
                              have b34051 := hb (x 3 9)
                              have b34052 := hb (x 3 3 && x 3 9)
                              clear * - r34050 b34051 b34052 d34033
                              omega
                            have d34053 : (x 3 9 && x 3 13).toNat = 0 := by
                              have r34054 := hand1 (x 3 9) (x 3 13)
                              have b34055 := hb (x 3 9)
                              have b34056 := hb (x 3 9 && x 3 13)
                              clear * - r34054 b34055 b34056 d34033
                              omega
                            have d34057 : (x 2 10).toNat = 0 := by
                              have r34058 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := hd8 4
                              have e34059 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
                              have e34060 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
                              have e34061 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
                              have e34062 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
                              have e34063 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
                              have e34064 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
                              have b34065 := hb (x (-3) 7)
                              have b34066 := hb (x (-2) 6)
                              have b34067 := hb (x (-1) 5)
                              have b34068 := hb (x 0 4)
                              have b34069 := hb (x 1 11)
                              have b34070 := hb (x 2 10)
                              have b34071 := hb (x 3 9)
                              have b34072 := hb (x 4 8)
                              clear * - r34058 e34059 e34060 e34061 e34062 e34063 e34064 b34065 b34066 b34067 b34068 b34069 b34070 b34071 b34072 d33997 d34033 d30501 f19675 f33996
                              omega
                            have d34073 : (x 2 3 && x 2 10).toNat = 0 := by
                              have r34074 := hand2 (x 2 3) (x 2 10)
                              have b34075 := hb (x 2 10)
                              have b34076 := hb (x 2 3 && x 2 10)
                              clear * - r34074 b34075 b34076 d34057
                              omega
                            have d34077 : (x 2 10 && x 2 13).toNat = 0 := by
                              have r34078 := hand1 (x 2 10) (x 2 13)
                              have b34079 := hb (x 2 10)
                              have b34080 := hb (x 2 10 && x 2 13)
                              clear * - r34078 b34079 b34080 d34057
                              omega
                            cases h34081 : x (-1) 6
                            · have f34082 : (x (-1) 6).toNat = 0 := by rw [h34081]; rfl
                              exact cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0000110000110 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d31466 d31446 d31426 d31274 d30333 d31406 d31254 d30309 d31142 d25907 d25867 d25875 d31126 d25919 d25855 d25814 f31072 f34082 f30308 d31197 d31189 d31182 d31109 g1 d19634 f19675 d19341 f19697 f19677 f30486 d19389 d19662 f30488 d19461 f30500 d25798 d19445 d31390 d30491 d19481 d30501 d19409 d19506 d25750 d31294 d34057 d19501 d30495 d19550 d19618 d19530 d34033 d19586 d33997 d19630 d25778 d19457 d19365 d25883 d30329 d30357 d25770 d25806 d19357 d19610 d31250 d34025 d34053 d31270 d31290 d19353 d25915 d31422 d31442 d31462 d31482 d19570 d31314 d25903 d19397 d31226 d25766 d19489 d19349 d25863 d31222 d31246 d25847 d31101 d31174 d30389 d30421 d30449 d30477 d31122 d31138 d31502 d31522 d31542 d31562 d34021 d34049 d25762 d25802 d19345 d34017 d25843 d31097 d31170 d30385 d30417 d30445 d30473 d34013 d19566 d34073 d25899 d19692 d19602 d19429 d30325 d30353 d19562 d25742 d25794 d19337 d19598 d25758 d19425 d19622 d19526 d31146 d25754 d19594 d19417 d19514
                            · have f38438 : (x (-1) 6).toNat = 1 := by rw [h34081]; rfl
                              exact cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0000110000111 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d31466 d31446 d31426 d31406 d31334 d25907 d31318 d25814 g1 f19675 d19341 f19697 f19677 d19389 f30488 g14 f30500 d25798 d19445 d30501 d25782 d19409 d25750 d34057 d25726 d19501 d30495 d19550 d19618 d19586 d25746 d34029 d19614 d34077 d19441 d31366 d31386 d34025 d34053 d19353 d25915 d31422 d31442 d31462 d31482 d19606 d31310 d19437 d31122 d31138 d31502 d31522 d31542 d31562 d25843 d31097 d31170 d30385 d30417 d30445 d30473 d19602 d19429 d19598 d25758 d19425 d25754 d19594 d19417 d19514
                      · have f39467 : (x 1 3).toNat = 1 := by rw [h30499]; rfl
                        exact cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0000110001 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 f39467 d25895 d19550 d19554 d19514
                    · have f40110 : (x 1 1).toNat = 1 := by rw [h30489]; rfl
                      exact cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a000011001 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 f40110 d19461 d19550 d19514
                  · have f40493 : (x 0 12).toNat = 1 := by rw [h30487]; rfl
                    exact cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a00001101 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d25855 f40493 d25750 d19550 d19618 d25734 d19465 d19329 d19518 d25827
                · have f41084 : (x 0 9).toNat = 1 := by rw [h30485]; rfl
                  exact cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0000111 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d30397 d25919 d25855 f41084 d19481 d25835 d30377 d19666 d25859
          · have f41196 : (x 0 7).toNat = 1 := by rw [h19696]; rfl
            exact cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0001 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d19369 d19688 d19341 f41196 f19677 d19389 f19683 d19445 d19550 d19618 d19530 d19574 d19542 d19684 d19606 d19437 d19602 d19429 d19393 d19598 d19425 d19622 d19558 d19421 d19522 d19373 d19325 d19514
        · have f41830 : (x 0 13).toNat = 1 := by rw [h19682]; rfl
          exact cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a001 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 f41830 d19461 d19550 d19325 d19514
      · have f42383 : (x 0 8).toNat = 1 := by rw [h19676]; rfl
        have d42384 : (x (-1) 9).toNat = 0 := by
          have r42385 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
          have e42386 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e42387 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e42388 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e42389 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e42390 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e42391 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b42392 := hb (x (-7) 7)
          have b42393 := hb (x (-6) 6)
          have b42394 := hb (x (-5) 5)
          have b42395 := hb (x (-4) 4)
          have b42396 := hb (x (-3) 11)
          have b42397 := hb (x (-2) 10)
          have b42398 := hb (x (-1) 9)
          have b42399 := hb (x 0 8)
          clear * - r42385 e42386 e42387 e42388 e42389 e42390 e42391 b42392 b42393 b42394 b42395 b42396 b42397 b42398 b42399 f42383
          omega
        have d42400 : (x (-1) 4 && x (-1) 9).toNat = 0 := by
          have r42401 := hand2 (x (-1) 4) (x (-1) 9)
          have b42402 := hb (x (-1) 9)
          have b42403 := hb (x (-1) 4 && x (-1) 9)
          clear * - r42401 b42402 b42403 d42384
          omega
        have d42404 : (x (-2) 10).toNat = 0 := by
          have r42405 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
          have e42406 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e42407 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e42408 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e42409 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e42410 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e42411 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b42412 := hb (x (-7) 7)
          have b42413 := hb (x (-6) 6)
          have b42414 := hb (x (-5) 5)
          have b42415 := hb (x (-4) 4)
          have b42416 := hb (x (-3) 11)
          have b42417 := hb (x (-2) 10)
          have b42418 := hb (x (-1) 9)
          have b42419 := hb (x 0 8)
          clear * - r42405 e42406 e42407 e42408 e42409 e42410 e42411 b42412 b42413 b42414 b42415 b42416 b42417 b42418 b42419 f42383 d42384
          omega
        have d42420 : (x (-2) 1 && x (-2) 10).toNat = 0 := by
          have r42421 := hand2 (x (-2) 1) (x (-2) 10)
          have b42422 := hb (x (-2) 10)
          have b42423 := hb (x (-2) 1 && x (-2) 10)
          clear * - r42421 b42422 b42423 d42404
          omega
        have d42424 : (x (-2) 5 && x (-2) 10).toNat = 0 := by
          have r42425 := hand2 (x (-2) 5) (x (-2) 10)
          have b42426 := hb (x (-2) 10)
          have b42427 := hb (x (-2) 5 && x (-2) 10)
          clear * - r42425 b42426 b42427 d42404
          omega
        have d42428 : (x (-3) 11).toNat = 0 := by
          have r42429 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
          have e42430 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e42431 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e42432 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e42433 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e42434 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e42435 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b42436 := hb (x (-7) 7)
          have b42437 := hb (x (-6) 6)
          have b42438 := hb (x (-5) 5)
          have b42439 := hb (x (-4) 4)
          have b42440 := hb (x (-3) 11)
          have b42441 := hb (x (-2) 10)
          have b42442 := hb (x (-1) 9)
          have b42443 := hb (x 0 8)
          clear * - r42429 e42430 e42431 e42432 e42433 e42434 e42435 b42436 b42437 b42438 b42439 b42440 b42441 b42442 b42443 f42383 d42384 d42404
          omega
        have d42444 : (x (-3) 1 && x (-3) 11).toNat = 0 := by
          have r42445 := hand2 (x (-3) 1) (x (-3) 11)
          have b42446 := hb (x (-3) 11)
          have b42447 := hb (x (-3) 1 && x (-3) 11)
          clear * - r42445 b42446 b42447 d42428
          omega
        have d42448 : (x (-3) 2 && x (-3) 11).toNat = 0 := by
          have r42449 := hand2 (x (-3) 2) (x (-3) 11)
          have b42450 := hb (x (-3) 11)
          have b42451 := hb (x (-3) 2 && x (-3) 11)
          clear * - r42449 b42450 b42451 d42428
          omega
        have d42452 : (x (-3) 6 && x (-3) 11).toNat = 0 := by
          have r42453 := hand2 (x (-3) 6) (x (-3) 11)
          have b42454 := hb (x (-3) 11)
          have b42455 := hb (x (-3) 6 && x (-3) 11)
          clear * - r42453 b42454 b42455 d42428
          omega
        have d42456 : (x (-4) 4).toNat = 0 := by
          have r42457 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
          have e42458 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e42459 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e42460 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e42461 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e42462 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e42463 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b42464 := hb (x (-7) 7)
          have b42465 := hb (x (-6) 6)
          have b42466 := hb (x (-5) 5)
          have b42467 := hb (x (-4) 4)
          have b42468 := hb (x (-3) 11)
          have b42469 := hb (x (-2) 10)
          have b42470 := hb (x (-1) 9)
          have b42471 := hb (x 0 8)
          clear * - r42457 e42458 e42459 e42460 e42461 e42462 e42463 b42464 b42465 b42466 b42467 b42468 b42469 b42470 b42471 f42383 d42384 d42404 d42428
          omega
        have d42472 : (x (-4) 4 && x (-4) 14).toNat = 0 := by
          have r42473 := hand1 (x (-4) 4) (x (-4) 14)
          have b42474 := hb (x (-4) 4)
          have b42475 := hb (x (-4) 4 && x (-4) 14)
          clear * - r42473 b42474 b42475 d42456
          omega
        have d42476 : (x (-4) 4 && x (-4) 11).toNat = 0 := by
          have r42477 := hand1 (x (-4) 4) (x (-4) 11)
          have b42478 := hb (x (-4) 4)
          have b42479 := hb (x (-4) 4 && x (-4) 11)
          clear * - r42477 b42478 b42479 d42456
          omega
        have d42480 : (x (-5) 5).toNat = 0 := by
          have r42481 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
          have e42482 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e42483 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e42484 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e42485 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e42486 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e42487 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b42488 := hb (x (-7) 7)
          have b42489 := hb (x (-6) 6)
          have b42490 := hb (x (-5) 5)
          have b42491 := hb (x (-4) 4)
          have b42492 := hb (x (-3) 11)
          have b42493 := hb (x (-2) 10)
          have b42494 := hb (x (-1) 9)
          have b42495 := hb (x 0 8)
          clear * - r42481 e42482 e42483 e42484 e42485 e42486 e42487 b42488 b42489 b42490 b42491 b42492 b42493 b42494 b42495 f42383 d42384 d42404 d42428 d42456
          omega
        have d42496 : (x (-5) 5 && x (-5) 12).toNat = 0 := by
          have r42497 := hand1 (x (-5) 5) (x (-5) 12)
          have b42498 := hb (x (-5) 5)
          have b42499 := hb (x (-5) 5 && x (-5) 12)
          clear * - r42497 b42498 b42499 d42480
          omega
        have d42500 : (x (-6) 6).toNat = 0 := by
          have r42501 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
          have e42502 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e42503 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e42504 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e42505 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e42506 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e42507 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b42508 := hb (x (-7) 7)
          have b42509 := hb (x (-6) 6)
          have b42510 := hb (x (-5) 5)
          have b42511 := hb (x (-4) 4)
          have b42512 := hb (x (-3) 11)
          have b42513 := hb (x (-2) 10)
          have b42514 := hb (x (-1) 9)
          have b42515 := hb (x 0 8)
          clear * - r42501 e42502 e42503 e42504 e42505 e42506 e42507 b42508 b42509 b42510 b42511 b42512 b42513 b42514 b42515 f42383 d42384 d42404 d42428 d42456 d42480
          omega
        have d42516 : (x (-6) 6 && x (-6) 13).toNat = 0 := by
          have r42517 := hand1 (x (-6) 6) (x (-6) 13)
          have b42518 := hb (x (-6) 6)
          have b42519 := hb (x (-6) 6 && x (-6) 13)
          clear * - r42517 b42518 b42519 d42500
          omega
        have d42520 : (x (-7) 7).toNat = 0 := by
          have r42521 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
          have e42522 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e42523 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e42524 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e42525 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e42526 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e42527 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b42528 := hb (x (-7) 7)
          have b42529 := hb (x (-6) 6)
          have b42530 := hb (x (-5) 5)
          have b42531 := hb (x (-4) 4)
          have b42532 := hb (x (-3) 11)
          have b42533 := hb (x (-2) 10)
          have b42534 := hb (x (-1) 9)
          have b42535 := hb (x 0 8)
          clear * - r42521 e42522 e42523 e42524 e42525 e42526 e42527 b42528 b42529 b42530 b42531 b42532 b42533 b42534 b42535 f42383 d42384 d42404 d42428 d42456 d42480 d42500
          omega
        have d42536 : (x (-7) 7 && x (-7) 14).toNat = 0 := by
          have r42537 := hand1 (x (-7) 7) (x (-7) 14)
          have b42538 := hb (x (-7) 7)
          have b42539 := hb (x (-7) 7 && x (-7) 14)
          clear * - r42537 b42538 b42539 d42520
          omega
        cases h42540 : x 0 5
        · have f42541 : (x 0 5).toNat = 0 := by rw [h42540]; rfl
          cases h42542 : x 0 7
          · have f42543 : (x 0 7).toNat = 0 := by rw [h42542]; rfl
            have d42544 : (x 0 1 && x 0 7).toNat = 0 := by
              have r42545 := hand2 (x 0 1) (x 0 7)
              have b42546 := hb (x 0 7)
              have b42547 := hb (x 0 1 && x 0 7)
              clear * - r42545 b42546 b42547 f42543
              omega
            cases h42548 : x 0 9
            · have f42549 : (x 0 9).toNat = 0 := by rw [h42548]; rfl
              exact cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a01000 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d42480 d42456 d42428 d42404 d42384 g1 d19369 d19634 f19675 d19341 f42543 f42383 d19389 d19662 d19461 d19445 d19481 d19506 d19550 d19618 d19453 d19654 d19626 d19449 d19670 d19477 d19650 d42400 d42424 d42452 d42544 d42476 d42496 d42516 d42536 d42420 d42448 d19598 d19425 d42472 d19666 d19465 d19329 d19594 d19417 d19554 d19518 d19325 d19514
            · have f45417 : (x 0 9).toNat = 1 := by rw [h42548]; rfl
              exact cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a01001 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d42480 d42456 d19369 d19634 f19675 d19341 f42543 f45417 d19389 d19662 d19461 d19445 d19481 d19506 d19550 d19618 d19453 d19654 d42476 d42496 d42516 d42536 d19598 d19425 d42472 d19666 d19465 d19329 d19594 d19417 d19554 d19518 d19325 d19514
          · have f48240 : (x 0 7).toNat = 1 := by rw [h42542]; rfl
            exact cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0101 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d42480 d42404 g1 d19369 f42541 d19341 f48240 d19389 d19445 d19550 d19618 d19353 d19393 d19598 d19425 d42444 d42472 d19558 d19421 d19325 d19514
        · have f48609 : (x 0 5).toNat = 1 := by rw [h42540]; rfl
          exact cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a011 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 f48609 d19461 d19550 d19325 d19514
    · have f49166 : (x 0 4).toNat = 1 := by rw [h19674]; rfl
      exact cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a1 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 d19369 f49166 d19389 d19662 d19461 d19445 d19481 d19550 d19618 d19574 d19473 d19646 d19666 d19469 d19642 d19558 d19421 d19465 d19329 d19325 d19514
  · rfl

theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core (x : ℤ → Fin 16 → Bool)
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
    : x 0 1 = x 0 14 := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13
