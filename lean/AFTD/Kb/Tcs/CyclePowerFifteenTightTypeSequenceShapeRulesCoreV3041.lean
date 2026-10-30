import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_shape_rules_core_v30_41

Topic: combinatorics   Node: 6b4b5f2026dd

Provenance: helper lemma. Research thread RT-1, open case k = 15 (m = 4) of OP-205 (arXiv:2610.15635, Theorems 1.3-1.4: eq(C_n^k) for k+1 = 2^m, n even, (k+1) not dividing n). Experiment 9757: on the integer window [-24, 24] the layer-free tight-class model leaves 13 class types at the centre, none with an island; on [-32, 32] the six types {0,15}, {0,1,14,15}, {0..3,12..15}, {0..7,12..15}, {0..3,8..15}, {0..15}.

Window refutation for k = 15: in the layer-free tight-class model on the integer line (x p j: the class starting at p contains p + j; inner count 3 per vertex, distances 14, 12, 8 covered exactly once, the other distances covered, classes closed under the tight-class parent map), with x p 1 = x p 14 and x p 2 = x p 3 everywhere, the class at 0 cannot have bit 3 = 0 and bit 4 = 1.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_shape_rules_core_v30_41_aux (x : ℤ → Fin 16 → Bool)
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
    (h114 : ∀ p, x p 1 = x p 14)
    (h23 : ∀ p, x p 2 = x p 3)
    (g0 : (x 0 3).toNat = 0) (g1 : (x 0 4).toNat = 1) : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d1 : (x 0 3 && x 0 12).toNat = 0 := by
    have r2 := hand1 (x 0 3) (x 0 12)
    have b3 := hb (x 0 3)
    have b4 := hb (x 0 3 && x 0 12)
    clear * - r2 b3 b4 g0
    omega
  have d5 : (x 0 2).toNat = 0 := by
    have r6 : (x 0 2).toNat = (x 0 3).toNat := congrArg Bool.toNat (h23 0)
    have b7 := hb (x 0 2)
    have b8 := hb (x 0 3)
    clear * - r6 b7 b8 g0
    omega
  have d9 : (x 0 2 && x 0 12).toNat = 0 := by
    have r10 := hand1 (x 0 2) (x 0 12)
    have b11 := hb (x 0 2)
    have b12 := hb (x 0 2 && x 0 12)
    clear * - r10 b11 b12 d5
    omega
  have d13 : (x 0 2 && x 0 9).toNat = 0 := by
    have r14 := hand1 (x 0 2) (x 0 9)
    have b15 := hb (x 0 2)
    have b16 := hb (x 0 2 && x 0 9)
    clear * - r14 b15 b16 d5
    omega
  have d17 : (x 0 11).toNat = 0 := by
    have r18 : (x 0 11).toNat ≤ (x 0 3).toNat := himp _ _ (hp11 0)
    have b19 := hb (x 0 3)
    have b20 := hb (x 0 11)
    clear * - r18 b19 b20 g0
    omega
  have d21 : (x 0 4 && x 0 11).toNat = 0 := by
    have r22 := hand2 (x 0 4) (x 0 11)
    have b23 := hb (x 0 11)
    have b24 := hb (x 0 4 && x 0 11)
    clear * - r22 b23 b24 d17
    omega
  have d25 : (x 0 10).toNat = 0 := by
    have r26 : (x 0 10).toNat ≤ (x 0 2).toNat := himp _ _ (hp10 0)
    have b27 := hb (x 0 2)
    have b28 := hb (x 0 10)
    clear * - r26 b27 b28 d5
    omega
  have d29 : (x 0 12).toNat = 1 := by
    have r30 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
    have b31 := hb (x 0 4)
    have b32 := hb (x 0 12)
    clear * - r30 b31 b32 g1
    omega
  have d33 : (x (-1) 13).toNat = 0 := by
    have r34 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e35 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e36 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b37 := hb (x (-3) 3)
    have b38 := hb (x (-2) 2)
    have b39 := hb (x (-1) 13)
    have b40 := hb (x 0 12)
    clear * - r34 e35 e36 b37 b38 b39 b40 d29
    omega
  have d41 : (x (-1) 3 && x (-1) 13).toNat = 0 := by
    have r42 := hand2 (x (-1) 3) (x (-1) 13)
    have b43 := hb (x (-1) 13)
    have b44 := hb (x (-1) 3 && x (-1) 13)
    clear * - r42 b43 b44 d33
    omega
  have d45 : (x (-1) 4 && x (-1) 13).toNat = 0 := by
    have r46 := hand2 (x (-1) 4) (x (-1) 13)
    have b47 := hb (x (-1) 13)
    have b48 := hb (x (-1) 4 && x (-1) 13)
    clear * - r46 b47 b48 d33
    omega
  have d49 : (x (-1) 5).toNat = 0 := by
    have r50 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
    have b51 := hb (x (-1) 5)
    have b52 := hb (x (-1) 13)
    clear * - r50 b51 b52 d33
    omega
  have d53 : (x (-1) 5 && x (-1) 12).toNat = 0 := by
    have r54 := hand1 (x (-1) 5) (x (-1) 12)
    have b55 := hb (x (-1) 5)
    have b56 := hb (x (-1) 5 && x (-1) 12)
    clear * - r54 b55 b56 d49
    omega
  have d57 : (x (-2) 2).toNat = 0 := by
    have r58 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e59 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e60 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b61 := hb (x (-3) 3)
    have b62 := hb (x (-2) 2)
    have b63 := hb (x (-1) 13)
    have b64 := hb (x 0 12)
    clear * - r58 e59 e60 b61 b62 b63 b64 d29 d33
    omega
  have d65 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
    have r66 := hand1 (x (-2) 2) (x (-2) 13)
    have b67 := hb (x (-2) 2)
    have b68 := hb (x (-2) 2 && x (-2) 13)
    clear * - r66 b67 b68 d57
    omega
  have d69 : (x (-2) 2 && x (-2) 9).toNat = 0 := by
    have r70 := hand1 (x (-2) 2) (x (-2) 9)
    have b71 := hb (x (-2) 2)
    have b72 := hb (x (-2) 2 && x (-2) 9)
    clear * - r70 b71 b72 d57
    omega
  have d73 : (x (-2) 3).toNat = 0 := by
    have r74 : (x (-2) 2).toNat = (x (-2) 3).toNat := congrArg Bool.toNat (h23 (-2))
    have b75 := hb (x (-2) 2)
    have b76 := hb (x (-2) 3)
    clear * - r74 b75 b76 d57
    omega
  have d77 : (x (-2) 11).toNat = 0 := by
    have r78 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
    have b79 := hb (x (-2) 3)
    have b80 := hb (x (-2) 11)
    clear * - r78 b79 b80 d73
    omega
  have d81 : (x (-2) 1 && x (-2) 11).toNat = 0 := by
    have r82 := hand2 (x (-2) 1) (x (-2) 11)
    have b83 := hb (x (-2) 11)
    have b84 := hb (x (-2) 1 && x (-2) 11)
    clear * - r82 b83 b84 d77
    omega
  have d85 : (x (-2) 4 && x (-2) 11).toNat = 0 := by
    have r86 := hand2 (x (-2) 4) (x (-2) 11)
    have b87 := hb (x (-2) 11)
    have b88 := hb (x (-2) 4 && x (-2) 11)
    clear * - r86 b87 b88 d77
    omega
  have d89 : (x (-2) 10).toNat = 0 := by
    have r90 : (x (-2) 10).toNat ≤ (x (-2) 2).toNat := himp _ _ (hp10 (-2))
    have b91 := hb (x (-2) 2)
    have b92 := hb (x (-2) 10)
    clear * - r90 b91 b92 d57
    omega
  have d93 : (x (-3) 3).toNat = 0 := by
    have r94 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e95 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e96 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b97 := hb (x (-3) 3)
    have b98 := hb (x (-2) 2)
    have b99 := hb (x (-1) 13)
    have b100 := hb (x 0 12)
    clear * - r94 e95 e96 b97 b98 b99 b100 d29 d33 d57
    omega
  have d101 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
    have r102 := hand1 (x (-3) 3) (x (-3) 14)
    have b103 := hb (x (-3) 3)
    have b104 := hb (x (-3) 3 && x (-3) 14)
    clear * - r102 b103 b104 d93
    omega
  have d105 : (x (-3) 3 && x (-3) 10).toNat = 0 := by
    have r106 := hand1 (x (-3) 3) (x (-3) 10)
    have b107 := hb (x (-3) 3)
    have b108 := hb (x (-3) 3 && x (-3) 10)
    clear * - r106 b107 b108 d93
    omega
  have d109 : (x (-3) 2).toNat = 0 := by
    have r110 : (x (-3) 2).toNat = (x (-3) 3).toNat := congrArg Bool.toNat (h23 (-3))
    have b111 := hb (x (-3) 2)
    have b112 := hb (x (-3) 3)
    clear * - r110 b111 b112 d93
    omega
  have d113 : (x (-3) 2 && x (-3) 13).toNat = 0 := by
    have r114 := hand1 (x (-3) 2) (x (-3) 13)
    have b115 := hb (x (-3) 2)
    have b116 := hb (x (-3) 2 && x (-3) 13)
    clear * - r114 b115 b116 d109
    omega
  have d117 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
    have r118 := hand1 (x (-3) 2) (x (-3) 12)
    have b119 := hb (x (-3) 2)
    have b120 := hb (x (-3) 2 && x (-3) 12)
    clear * - r118 b119 b120 d109
    omega
  have d121 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
    have r122 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b123 := hb (x (-3) 2)
    have b124 := hb (x (-1) 13)
    have b125 := hb (x (-2) 1 && x (-2) 14)
    clear * - r122 b123 b124 b125 d33 d109
    omega
  have d126 : (x (-2) 14).toNat = 1 := by
    have r127 := hand2 (x (-2) 1) (x (-2) 14)
    have b128 := hb (x (-2) 14)
    have b129 := hb (x (-2) 1 && x (-2) 14)
    clear * - r127 b128 b129 d121
    omega
  have d130 : (x (-2) 1).toNat = 1 := by
    have r131 : (x (-2) 1).toNat = (x (-2) 14).toNat := congrArg Bool.toNat (h114 (-2))
    have b132 := hb (x (-2) 1)
    have b133 := hb (x (-2) 14)
    clear * - r131 b132 b133 d126
    omega
  have d134 : (x (-1) 14).toNat = 0 := by
    have r135 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b136 := hb (x (-2) 1)
    have b137 := hb (x (-1) 14)
    clear * - r135 b136 b137 d130
    omega
  have d138 : (x (-1) 1 && x (-1) 14).toNat = 0 := by
    have r139 := hand2 (x (-1) 1) (x (-1) 14)
    have b140 := hb (x (-1) 14)
    have b141 := hb (x (-1) 1 && x (-1) 14)
    clear * - r139 b140 b141 d134
    omega
  have d142 : (x 0 13).toNat = 1 := by
    have r143 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b144 := hb (x (-2) 2)
    have b145 := hb (x 0 13)
    have b146 := hb (x (-1) 1 && x (-1) 14)
    clear * - r143 b144 b145 b146 d138 d57
    omega
  have d147 : (x 0 1).toNat = 1 := by
    have r148 : (x 0 13).toNat ≤ (x 0 1).toNat := himp _ _ (hp13 0)
    have b149 := hb (x 0 1)
    have b150 := hb (x 0 13)
    clear * - r148 b149 b150 d142
    omega
  have d151 : (x 0 14).toNat = 1 := by
    have r152 : (x 0 1).toNat = (x 0 14).toNat := congrArg Bool.toNat (h114 0)
    have b153 := hb (x 0 1)
    have b154 := hb (x 0 14)
    clear * - r152 b153 b154 d147
    omega
  have d155 : (x (-1) 1).toNat = 0 := by
    have r156 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b157 := hb (x (-1) 1)
    have b158 := hb (x 0 14)
    clear * - r156 b157 b158 d151
    omega
  have d159 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
    have r160 := hand1 (x (-1) 1) (x (-1) 12)
    have b161 := hb (x (-1) 1)
    have b162 := hb (x (-1) 1 && x (-1) 12)
    clear * - r160 b161 b162 d155
    omega
  have d163 : (x (-1) 1 && x (-1) 8).toNat = 0 := by
    have r164 := hand1 (x (-1) 1) (x (-1) 8)
    have b165 := hb (x (-1) 1)
    have b166 := hb (x (-1) 1 && x (-1) 8)
    clear * - r164 b165 b166 d155
    omega
  have d167 : (x (-1) 9).toNat = 0 := by
    have r168 : (x (-1) 9).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp9 (-1))
    have b169 := hb (x (-1) 1)
    have b170 := hb (x (-1) 9)
    clear * - r168 b169 b170 d155
    omega
  have d171 : (x 1 14).toNat = 0 := by
    have r172 : (x 1 14).toNat + (x 0 1).toNat = 1 := by have q := hd14 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b173 := hb (x 0 1)
    have b174 := hb (x 1 14)
    clear * - r172 b173 b174 d147
    omega
  have d175 : (x 1 1 && x 1 14).toNat = 0 := by
    have r176 := hand2 (x 1 1) (x 1 14)
    have b177 := hb (x 1 14)
    have b178 := hb (x 1 1 && x 1 14)
    clear * - r176 b177 b178 d171
    omega
  have d179 : (x 2 13).toNat = 1 := by
    have r180 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b181 := hb (x 0 2)
    have b182 := hb (x 2 13)
    have b183 := hb (x 1 1 && x 1 14)
    clear * - r180 b181 b182 b183 d175 d5
    omega
  have d184 : (x 2 1).toNat = 1 := by
    have r185 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
    have b186 := hb (x 2 1)
    have b187 := hb (x 2 13)
    clear * - r185 b186 b187 d179
    omega
  have d188 : (x 2 14).toNat = 1 := by
    have r189 : (x 2 1).toNat = (x 2 14).toNat := congrArg Bool.toNat (h114 2)
    have b190 := hb (x 2 1)
    have b191 := hb (x 2 14)
    clear * - r189 b190 b191 d184
    omega
  have d192 : (x 1 1).toNat = 0 := by
    have r193 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b194 := hb (x 1 1)
    have b195 := hb (x 2 14)
    clear * - r193 b194 b195 d188
    omega
  have d196 : (x 1 1 && x 1 11).toNat = 0 := by
    have r197 := hand1 (x 1 1) (x 1 11)
    have b198 := hb (x 1 1)
    have b199 := hb (x 1 1 && x 1 11)
    clear * - r197 b198 b199 d192
    omega
  have d200 : (x 1 1 && x 1 8).toNat = 0 := by
    have r201 := hand1 (x 1 1) (x 1 8)
    have b202 := hb (x 1 1)
    have b203 := hb (x 1 1 && x 1 8)
    clear * - r201 b202 b203 d192
    omega
  have d204 : (x 1 9).toNat = 0 := by
    have r205 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
    have b206 := hb (x 1 1)
    have b207 := hb (x 1 9)
    clear * - r205 b206 b207 d192
    omega
  have d208 : (x 3 14).toNat = 0 := by
    have r209 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b210 := hb (x 2 1)
    have b211 := hb (x 3 14)
    clear * - r209 b210 b211 d184
    omega
  have d212 : (x 3 4 && x 3 14).toNat = 0 := by
    have r213 := hand2 (x 3 4) (x 3 14)
    have b214 := hb (x 3 14)
    have b215 := hb (x 3 4 && x 3 14)
    clear * - r213 b214 b215 d208
    omega
  have d216 : (x 3 1).toNat = 0 := by
    have r217 : (x 3 1).toNat = (x 3 14).toNat := congrArg Bool.toNat (h114 3)
    have b218 := hb (x 3 1)
    have b219 := hb (x 3 14)
    clear * - r217 b218 b219 d208
    omega
  have d220 : (x 3 1 && x 3 8).toNat = 0 := by
    have r221 := hand1 (x 3 1) (x 3 8)
    have b222 := hb (x 3 1)
    have b223 := hb (x 3 1 && x 3 8)
    clear * - r221 b222 b223 d216
    omega
  have d224 : (x 3 9).toNat = 0 := by
    have r225 : (x 3 9).toNat ≤ (x 3 1).toNat := himp _ _ (hp9 3)
    have b226 := hb (x 3 1)
    have b227 := hb (x 3 9)
    clear * - r225 b226 b227 d216
    omega
  have d228 : (x 4 14).toNat = 1 := by
    have r229 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b230 := hb (x 3 1)
    have b231 := hb (x 4 14)
    clear * - r229 b230 b231 d216
    omega
  have d232 : (x 4 1).toNat = 1 := by
    have r233 : (x 4 1).toNat = (x 4 14).toNat := congrArg Bool.toNat (h114 4)
    have b234 := hb (x 4 1)
    have b235 := hb (x 4 14)
    clear * - r233 b234 b235 d228
    omega
  have d236 : (x 5 14).toNat = 0 := by
    have r237 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b238 := hb (x 4 1)
    have b239 := hb (x 5 14)
    clear * - r237 b238 b239 d232
    omega
  have d240 : (x 5 4 && x 5 14).toNat = 0 := by
    have r241 := hand2 (x 5 4) (x 5 14)
    have b242 := hb (x 5 14)
    have b243 := hb (x 5 4 && x 5 14)
    clear * - r241 b242 b243 d236
    omega
  have d244 : (x 5 1).toNat = 0 := by
    have r245 : (x 5 1).toNat = (x 5 14).toNat := congrArg Bool.toNat (h114 5)
    have b246 := hb (x 5 1)
    have b247 := hb (x 5 14)
    clear * - r245 b246 b247 d236
    omega
  have d248 : (x 6 14).toNat = 1 := by
    have r249 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b250 := hb (x 5 1)
    have b251 := hb (x 6 14)
    clear * - r249 b250 b251 d244
    omega
  have d252 : (x 6 1).toNat = 1 := by
    have r253 : (x 6 1).toNat = (x 6 14).toNat := congrArg Bool.toNat (h114 6)
    have b254 := hb (x 6 1)
    have b255 := hb (x 6 14)
    clear * - r253 b254 b255 d248
    omega
  have d256 : (x 7 14).toNat = 0 := by
    have r257 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b258 := hb (x 6 1)
    have b259 := hb (x 7 14)
    clear * - r257 b258 b259 d252
    omega
  have d260 : (x 7 1).toNat = 0 := by
    have r261 : (x 7 1).toNat = (x 7 14).toNat := congrArg Bool.toNat (h114 7)
    have b262 := hb (x 7 1)
    have b263 := hb (x 7 14)
    clear * - r261 b262 b263 d256
    omega
  have d264 : (x 8 14).toNat = 1 := by
    have r265 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b266 := hb (x 7 1)
    have b267 := hb (x 8 14)
    clear * - r265 b266 b267 d260
    omega
  have d268 : (x 8 1).toNat = 1 := by
    have r269 : (x 8 1).toNat = (x 8 14).toNat := congrArg Bool.toNat (h114 8)
    have b270 := hb (x 8 1)
    have b271 := hb (x 8 14)
    clear * - r269 b270 b271 d264
    omega
  have d272 : (x 9 14).toNat = 0 := by
    have r273 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b274 := hb (x 8 1)
    have b275 := hb (x 9 14)
    clear * - r273 b274 b275 d268
    omega
  have d276 : (x 9 2).toNat = 0 := by
    have r277 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
    have b278 := hb (x 9 2)
    have b279 := hb (x 9 14)
    clear * - r277 b278 b279 d272
    omega
  have d280 : (x 9 10).toNat = 0 := by
    have r281 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
    have b282 := hb (x 9 2)
    have b283 := hb (x 9 10)
    clear * - r281 b282 b283 d276
    omega
  have d284 : (x 7 2).toNat = 0 := by
    have r285 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
    have b286 := hb (x 7 2)
    have b287 := hb (x 7 14)
    clear * - r285 b286 b287 d256
    omega
  have d288 : (x 7 2 && x 7 12).toNat = 0 := by
    have r289 := hand1 (x 7 2) (x 7 12)
    have b290 := hb (x 7 2)
    have b291 := hb (x 7 2 && x 7 12)
    clear * - r289 b290 b291 d284
    omega
  have d292 : (x 7 10).toNat = 0 := by
    have r293 : (x 7 10).toNat ≤ (x 7 2).toNat := himp _ _ (hp10 7)
    have b294 := hb (x 7 2)
    have b295 := hb (x 7 10)
    clear * - r293 b294 b295 d284
    omega
  have d296 : (x 5 6).toNat = 0 := by
    have r297 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
    have b298 := hb (x 5 6)
    have b299 := hb (x 5 14)
    clear * - r297 b298 b299 d236
    omega
  have d300 : (x 5 2).toNat = 0 := by
    have r301 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
    have b302 := hb (x 5 2)
    have b303 := hb (x 5 14)
    clear * - r301 b302 b303 d236
    omega
  have d304 : (x 5 2 && x 5 12).toNat = 0 := by
    have r305 := hand1 (x 5 2) (x 5 12)
    have b306 := hb (x 5 2)
    have b307 := hb (x 5 2 && x 5 12)
    clear * - r305 b306 b307 d300
    omega
  have d308 : (x 5 10).toNat = 0 := by
    have r309 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
    have b310 := hb (x 5 2)
    have b311 := hb (x 5 10)
    clear * - r309 b310 b311 d300
    omega
  have d312 : (x 3 6).toNat = 0 := by
    have r313 : (x 3 6).toNat ≤ (x 3 14).toNat := himp _ _ (hp6 3)
    have b314 := hb (x 3 6)
    have b315 := hb (x 3 14)
    clear * - r313 b314 b315 d208
    omega
  have d316 : (x 3 12).toNat = 0 := by
    have r317 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e318 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e319 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b320 := hb (x 0 3)
    have b321 := hb (x 1 2)
    have b322 := hb (x 2 13)
    have b323 := hb (x 3 12)
    clear * - r317 e318 e319 b320 b321 b322 b323 d179 g0
    omega
  have d324 : (x 3 4).toNat = 0 := by
    have r325 : (x 3 4).toNat ≤ (x 3 12).toNat := himp _ _ (hp4 3)
    have b326 := hb (x 3 4)
    have b327 := hb (x 3 12)
    clear * - r325 b326 b327 d316
    omega
  have d328 : (x 1 2).toNat = 0 := by
    have r329 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e330 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e331 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b332 := hb (x 0 3)
    have b333 := hb (x 1 2)
    have b334 := hb (x 2 13)
    have b335 := hb (x 3 12)
    clear * - r329 e330 e331 b332 b333 b334 b335 d316 d179 g0
    omega
  have d336 : (x 1 2 && x 1 11).toNat = 0 := by
    have r337 := hand1 (x 1 2) (x 1 11)
    have b338 := hb (x 1 2)
    have b339 := hb (x 1 2 && x 1 11)
    clear * - r337 b338 b339 d328
    omega
  have d340 : (x 1 3).toNat = 0 := by
    have r341 : (x 1 2).toNat = (x 1 3).toNat := congrArg Bool.toNat (h23 1)
    have b342 := hb (x 1 2)
    have b343 := hb (x 1 3)
    clear * - r341 b342 b343 d328
    omega
  have d344 : (x 1 3 && x 1 10).toNat = 0 := by
    have r345 := hand1 (x 1 3) (x 1 10)
    have b346 := hb (x 1 3)
    have b347 := hb (x 1 3 && x 1 10)
    clear * - r345 b346 b347 d340
    omega
  have d348 : (x 1 11).toNat = 0 := by
    have r349 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
    have b350 := hb (x 1 3)
    have b351 := hb (x 1 11)
    clear * - r349 b350 b351 d340
    omega
  have d352 : (x 1 10).toNat = 0 := by
    have r353 : (x 1 10).toNat ≤ (x 1 2).toNat := himp _ _ (hp10 1)
    have b354 := hb (x 1 2)
    have b355 := hb (x 1 10)
    clear * - r353 b354 b355 d328
    omega
  have d356 : (x 1 6).toNat = 0 := by
    have r357 : (x 1 6).toNat ≤ (x 1 14).toNat := himp _ _ (hp6 1)
    have b358 := hb (x 1 6)
    have b359 := hb (x 1 14)
    clear * - r357 b358 b359 d171
    omega
  have d360 : (x 1 12).toNat = 0 := by
    have r361 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e362 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e363 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b364 := hb (x (-2) 3)
    have b365 := hb (x (-1) 2)
    have b366 := hb (x 0 13)
    have b367 := hb (x 1 12)
    clear * - r361 e362 e363 b364 b365 b366 b367 d142 d73
    omega
  have d368 : (x (-1) 2).toNat = 0 := by
    have r369 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e370 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e371 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b372 := hb (x (-2) 3)
    have b373 := hb (x (-1) 2)
    have b374 := hb (x 0 13)
    have b375 := hb (x 1 12)
    clear * - r369 e370 e371 b372 b373 b374 b375 d360 d142 d73
    omega
  have d376 : (x (-1) 3).toNat = 0 := by
    have r377 : (x (-1) 2).toNat = (x (-1) 3).toNat := congrArg Bool.toNat (h23 (-1))
    have b378 := hb (x (-1) 2)
    have b379 := hb (x (-1) 3)
    clear * - r377 b378 b379 d368
    omega
  have d380 : (x (-1) 3 && x (-1) 10).toNat = 0 := by
    have r381 := hand1 (x (-1) 3) (x (-1) 10)
    have b382 := hb (x (-1) 3)
    have b383 := hb (x (-1) 3 && x (-1) 10)
    clear * - r381 b382 b383 d376
    omega
  have d384 : (x (-1) 11).toNat = 0 := by
    have r385 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
    have b386 := hb (x (-1) 3)
    have b387 := hb (x (-1) 11)
    clear * - r385 b386 b387 d376
    omega
  have d388 : (x (-1) 10).toNat = 0 := by
    have r389 : (x (-1) 10).toNat ≤ (x (-1) 2).toNat := himp _ _ (hp10 (-1))
    have b390 := hb (x (-1) 2)
    have b391 := hb (x (-1) 10)
    clear * - r389 b390 b391 d368
    omega
  have d392 : (x (-3) 1).toNat = 0 := by
    have r393 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b394 := hb (x (-3) 1)
    have b395 := hb (x (-2) 14)
    clear * - r393 b394 b395 d126
    omega
  have d396 : (x (-3) 1 && x (-3) 12).toNat = 0 := by
    have r397 := hand1 (x (-3) 1) (x (-3) 12)
    have b398 := hb (x (-3) 1)
    have b399 := hb (x (-3) 1 && x (-3) 12)
    clear * - r397 b398 b399 d392
    omega
  have d400 : (x (-3) 14).toNat = 0 := by
    have r401 : (x (-3) 1).toNat = (x (-3) 14).toNat := congrArg Bool.toNat (h114 (-3))
    have b402 := hb (x (-3) 1)
    have b403 := hb (x (-3) 14)
    clear * - r401 b402 b403 d392
    omega
  have d404 : (x (-3) 7 && x (-3) 14).toNat = 0 := by
    have r405 := hand2 (x (-3) 7) (x (-3) 14)
    have b406 := hb (x (-3) 14)
    have b407 := hb (x (-3) 7 && x (-3) 14)
    clear * - r405 b406 b407 d400
    omega
  have d408 : (x (-3) 6).toNat = 0 := by
    have r409 : (x (-3) 6).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp6 (-3))
    have b410 := hb (x (-3) 6)
    have b411 := hb (x (-3) 14)
    clear * - r409 b410 b411 d400
    omega
  have d412 : (x (-4) 1).toNat = 1 := by
    have r413 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b414 := hb (x (-4) 1)
    have b415 := hb (x (-3) 14)
    clear * - r413 b414 b415 d400
    omega
  have d416 : (x (-4) 14).toNat = 1 := by
    have r417 : (x (-4) 1).toNat = (x (-4) 14).toNat := congrArg Bool.toNat (h114 (-4))
    have b418 := hb (x (-4) 1)
    have b419 := hb (x (-4) 14)
    clear * - r417 b418 b419 d412
    omega
  have d420 : (x (-5) 1).toNat = 0 := by
    have r421 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b422 := hb (x (-5) 1)
    have b423 := hb (x (-4) 14)
    clear * - r421 b422 b423 d416
    omega
  have d424 : (x (-5) 1 && x (-5) 11).toNat = 0 := by
    have r425 := hand1 (x (-5) 1) (x (-5) 11)
    have b426 := hb (x (-5) 1)
    have b427 := hb (x (-5) 1 && x (-5) 11)
    clear * - r425 b426 b427 d420
    omega
  have d428 : (x (-5) 14).toNat = 0 := by
    have r429 : (x (-5) 1).toNat = (x (-5) 14).toNat := congrArg Bool.toNat (h114 (-5))
    have b430 := hb (x (-5) 1)
    have b431 := hb (x (-5) 14)
    clear * - r429 b430 b431 d420
    omega
  have d432 : (x (-5) 3 && x (-5) 14).toNat = 0 := by
    have r433 := hand2 (x (-5) 3) (x (-5) 14)
    have b434 := hb (x (-5) 14)
    have b435 := hb (x (-5) 3 && x (-5) 14)
    clear * - r433 b434 b435 d428
    omega
  have d436 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
    have r437 := hand2 (x (-5) 4) (x (-5) 14)
    have b438 := hb (x (-5) 14)
    have b439 := hb (x (-5) 4 && x (-5) 14)
    clear * - r437 b438 b439 d428
    omega
  have d440 : (x (-5) 7 && x (-5) 14).toNat = 0 := by
    have r441 := hand2 (x (-5) 7) (x (-5) 14)
    have b442 := hb (x (-5) 14)
    have b443 := hb (x (-5) 7 && x (-5) 14)
    clear * - r441 b442 b443 d428
    omega
  have d444 : (x (-5) 2).toNat = 0 := by
    have r445 : (x (-5) 2).toNat ≤ (x (-5) 14).toNat := himp _ _ (hp2 (-5))
    have b446 := hb (x (-5) 2)
    have b447 := hb (x (-5) 14)
    clear * - r445 b446 b447 d428
    omega
  have d448 : (x (-5) 2 && x (-5) 11).toNat = 0 := by
    have r449 := hand1 (x (-5) 2) (x (-5) 11)
    have b450 := hb (x (-5) 2)
    have b451 := hb (x (-5) 2 && x (-5) 11)
    clear * - r449 b450 b451 d444
    omega
  have d452 : (x (-5) 3).toNat = 0 := by
    have r453 : (x (-5) 2).toNat = (x (-5) 3).toNat := congrArg Bool.toNat (h23 (-5))
    have b454 := hb (x (-5) 2)
    have b455 := hb (x (-5) 3)
    clear * - r453 b454 b455 d444
    omega
  have d456 : (x (-5) 10).toNat = 0 := by
    have r457 : (x (-5) 10).toNat ≤ (x (-5) 2).toNat := himp _ _ (hp10 (-5))
    have b458 := hb (x (-5) 2)
    have b459 := hb (x (-5) 10)
    clear * - r457 b458 b459 d444
    omega
  have d460 : (x (-6) 1).toNat = 1 := by
    have r461 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b462 := hb (x (-6) 1)
    have b463 := hb (x (-5) 14)
    clear * - r461 b462 b463 d428
    omega
  have d464 : (x (-6) 14).toNat = 1 := by
    have r465 : (x (-6) 1).toNat = (x (-6) 14).toNat := congrArg Bool.toNat (h114 (-6))
    have b466 := hb (x (-6) 1)
    have b467 := hb (x (-6) 14)
    clear * - r465 b466 b467 d460
    omega
  have d468 : (x (-7) 1).toNat = 0 := by
    have r469 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b470 := hb (x (-7) 1)
    have b471 := hb (x (-6) 14)
    clear * - r469 b470 b471 d464
    omega
  have d472 : (x (-7) 1 && x (-7) 12).toNat = 0 := by
    have r473 := hand1 (x (-7) 1) (x (-7) 12)
    have b474 := hb (x (-7) 1)
    have b475 := hb (x (-7) 1 && x (-7) 12)
    clear * - r473 b474 b475 d468
    omega
  have d476 : (x (-7) 14).toNat = 0 := by
    have r477 : (x (-7) 1).toNat = (x (-7) 14).toNat := congrArg Bool.toNat (h114 (-7))
    have b478 := hb (x (-7) 1)
    have b479 := hb (x (-7) 14)
    clear * - r477 b478 b479 d468
    omega
  have d480 : (x (-7) 7 && x (-7) 14).toNat = 0 := by
    have r481 := hand2 (x (-7) 7) (x (-7) 14)
    have b482 := hb (x (-7) 14)
    have b483 := hb (x (-7) 7 && x (-7) 14)
    clear * - r481 b482 b483 d476
    omega
  have d484 : (x (-7) 2).toNat = 0 := by
    have r485 : (x (-7) 2).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp2 (-7))
    have b486 := hb (x (-7) 2)
    have b487 := hb (x (-7) 14)
    clear * - r485 b486 b487 d476
    omega
  have d488 : (x (-7) 2 && x (-7) 12).toNat = 0 := by
    have r489 := hand1 (x (-7) 2) (x (-7) 12)
    have b490 := hb (x (-7) 2)
    have b491 := hb (x (-7) 2 && x (-7) 12)
    clear * - r489 b490 b491 d484
    omega
  have d492 : (x (-7) 3).toNat = 0 := by
    have r493 : (x (-7) 2).toNat = (x (-7) 3).toNat := congrArg Bool.toNat (h23 (-7))
    have b494 := hb (x (-7) 2)
    have b495 := hb (x (-7) 3)
    clear * - r493 b494 b495 d484
    omega
  have d496 : (x (-7) 3 && x (-7) 13).toNat = 0 := by
    have r497 := hand1 (x (-7) 3) (x (-7) 13)
    have b498 := hb (x (-7) 3)
    have b499 := hb (x (-7) 3 && x (-7) 13)
    clear * - r497 b498 b499 d492
    omega
  have d500 : (x (-7) 11).toNat = 0 := by
    have r501 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
    have b502 := hb (x (-7) 3)
    have b503 := hb (x (-7) 11)
    clear * - r501 b502 b503 d492
    omega
  have d504 : (x (-8) 1).toNat = 1 := by
    have r505 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b506 := hb (x (-8) 1)
    have b507 := hb (x (-7) 14)
    clear * - r505 b506 b507 d476
    omega
  have d508 : (x (-8) 14).toNat = 1 := by
    have r509 : (x (-8) 1).toNat = (x (-8) 14).toNat := congrArg Bool.toNat (h114 (-8))
    have b510 := hb (x (-8) 1)
    have b511 := hb (x (-8) 14)
    clear * - r509 b510 b511 d504
    omega
  have d512 : (x (-9) 1).toNat = 0 := by
    have r513 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b514 := hb (x (-9) 1)
    have b515 := hb (x (-8) 14)
    clear * - r513 b514 b515 d508
    omega
  have d516 : (x (-9) 1 && x (-9) 12).toNat = 0 := by
    have r517 := hand1 (x (-9) 1) (x (-9) 12)
    have b518 := hb (x (-9) 1)
    have b519 := hb (x (-9) 1 && x (-9) 12)
    clear * - r517 b518 b519 d512
    omega
  have d520 : (x (-9) 14).toNat = 0 := by
    have r521 : (x (-9) 1).toNat = (x (-9) 14).toNat := congrArg Bool.toNat (h114 (-9))
    have b522 := hb (x (-9) 1)
    have b523 := hb (x (-9) 14)
    clear * - r521 b522 b523 d512
    omega
  have d524 : (x (-9) 3 && x (-9) 14).toNat = 0 := by
    have r525 := hand2 (x (-9) 3) (x (-9) 14)
    have b526 := hb (x (-9) 14)
    have b527 := hb (x (-9) 3 && x (-9) 14)
    clear * - r525 b526 b527 d520
    omega
  have d528 : (x (-9) 4 && x (-9) 14).toNat = 0 := by
    have r529 := hand2 (x (-9) 4) (x (-9) 14)
    have b530 := hb (x (-9) 14)
    have b531 := hb (x (-9) 4 && x (-9) 14)
    clear * - r529 b530 b531 d520
    omega
  have d532 : (x (-9) 6).toNat = 0 := by
    have r533 : (x (-9) 6).toNat ≤ (x (-9) 14).toNat := himp _ _ (hp6 (-9))
    have b534 := hb (x (-9) 6)
    have b535 := hb (x (-9) 14)
    clear * - r533 b534 b535 d520
    omega
  have d536 : (x (-9) 2).toNat = 0 := by
    have r537 : (x (-9) 2).toNat ≤ (x (-9) 14).toNat := himp _ _ (hp2 (-9))
    have b538 := hb (x (-9) 2)
    have b539 := hb (x (-9) 14)
    clear * - r537 b538 b539 d520
    omega
  have d540 : (x (-9) 3).toNat = 0 := by
    have r541 : (x (-9) 2).toNat = (x (-9) 3).toNat := congrArg Bool.toNat (h23 (-9))
    have b542 := hb (x (-9) 2)
    have b543 := hb (x (-9) 3)
    clear * - r541 b542 b543 d536
    omega
  have d544 : (x (-9) 11).toNat = 0 := by
    have r545 : (x (-9) 11).toNat ≤ (x (-9) 3).toNat := himp _ _ (hp11 (-9))
    have b546 := hb (x (-9) 3)
    have b547 := hb (x (-9) 11)
    clear * - r545 b546 b547 d540
    omega
  have d548 : (x (-9) 13).toNat = 0 := by
    have r549 : (x (-9) 13).toNat ≤ (x (-9) 1).toNat := himp _ _ (hp13 (-9))
    have b550 := hb (x (-9) 1)
    have b551 := hb (x (-9) 13)
    clear * - r549 b550 b551 d512
    omega
  have d552 : (x (-9) 5).toNat = 0 := by
    have r553 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
    have b554 := hb (x (-9) 5)
    have b555 := hb (x (-9) 13)
    clear * - r553 b554 b555 d548
    omega
  have d556 : (x (-9) 9).toNat = 0 := by
    have r557 : (x (-9) 9).toNat ≤ (x (-9) 1).toNat := himp _ _ (hp9 (-9))
    have b558 := hb (x (-9) 1)
    have b559 := hb (x (-9) 9)
    clear * - r557 b558 b559 d512
    omega
  have d560 : (x (-7) 13).toNat = 0 := by
    have r561 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
    have b562 := hb (x (-7) 1)
    have b563 := hb (x (-7) 13)
    clear * - r561 b562 b563 d468
    omega
  have d564 : (x (-7) 4 && x (-7) 13).toNat = 0 := by
    have r565 := hand2 (x (-7) 4) (x (-7) 13)
    have b566 := hb (x (-7) 13)
    have b567 := hb (x (-7) 4 && x (-7) 13)
    clear * - r565 b566 b567 d560
    omega
  have d568 : (x (-7) 9).toNat = 0 := by
    have r569 : (x (-7) 9).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp9 (-7))
    have b570 := hb (x (-7) 1)
    have b571 := hb (x (-7) 9)
    clear * - r569 b570 b571 d468
    omega
  have d572 : (x (-5) 13).toNat = 0 := by
    have r573 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
    have b574 := hb (x (-5) 1)
    have b575 := hb (x (-5) 13)
    clear * - r573 b574 b575 d420
    omega
  have d576 : (x (-5) 5).toNat = 0 := by
    have r577 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
    have b578 := hb (x (-5) 5)
    have b579 := hb (x (-5) 13)
    clear * - r577 b578 b579 d572
    omega
  have d580 : (x (-5) 5 && x (-5) 12).toNat = 0 := by
    have r581 := hand1 (x (-5) 5) (x (-5) 12)
    have b582 := hb (x (-5) 5)
    have b583 := hb (x (-5) 5 && x (-5) 12)
    clear * - r581 b582 b583 d576
    omega
  have d584 : (x (-5) 9).toNat = 0 := by
    have r585 : (x (-5) 9).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp9 (-5))
    have b586 := hb (x (-5) 1)
    have b587 := hb (x (-5) 9)
    clear * - r585 b586 b587 d420
    omega
  have d588 : (x (-3) 13).toNat = 0 := by
    have r589 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
    have b590 := hb (x (-3) 1)
    have b591 := hb (x (-3) 13)
    clear * - r589 b590 b591 d392
    omega
  have d592 : (x (-3) 5).toNat = 0 := by
    have r593 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
    have b594 := hb (x (-3) 5)
    have b595 := hb (x (-3) 13)
    clear * - r593 b594 b595 d588
    omega
  have d596 : (x (-3) 5 && x (-3) 12).toNat = 0 := by
    have r597 := hand1 (x (-3) 5) (x (-3) 12)
    have b598 := hb (x (-3) 5)
    have b599 := hb (x (-3) 5 && x (-3) 12)
    clear * - r597 b598 b599 d592
    omega
  have d600 : (x (-3) 9).toNat = 0 := by
    have r601 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
    have b602 := hb (x (-3) 1)
    have b603 := hb (x (-3) 9)
    clear * - r601 b602 b603 d392
    omega
  have d604 : (x (-3) 11).toNat = 0 := by
    have r605 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
    have b606 := hb (x (-3) 3)
    have b607 := hb (x (-3) 11)
    clear * - r605 b606 b607 d93
    omega
  have d608 : (x (-4) 4).toNat = 1 := by
    have r609 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b610 := hb (x (-4) 4)
    have b611 := hb (x 0 11)
    have b612 := hb (x (-1) 1 && x (-1) 12)
    have b613 := hb (x (-2) 2 && x (-2) 13)
    have b614 := hb (x (-3) 3 && x (-3) 14)
    clear * - r609 b610 b611 b612 b613 b614 d17 d159 d65 d101
    omega
  have d615 : (x (-4) 12).toNat = 1 := by
    have r616 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
    have b617 := hb (x (-4) 4)
    have b618 := hb (x (-4) 12)
    clear * - r616 b617 b618 d608
    omega
  have d619 : (x (-6) 2).toNat = 0 := by
    have r620 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e621 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e622 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b623 := hb (x (-7) 3)
    have b624 := hb (x (-6) 2)
    have b625 := hb (x (-5) 13)
    have b626 := hb (x (-4) 12)
    clear * - r620 e621 e622 b623 b624 b625 b626 d615 d572 d492
    omega
  have d627 : (x (-6) 2 && x (-6) 12).toNat = 0 := by
    have r628 := hand1 (x (-6) 2) (x (-6) 12)
    have b629 := hb (x (-6) 2)
    have b630 := hb (x (-6) 2 && x (-6) 12)
    clear * - r628 b629 b630 d619
    omega
  have d631 : (x (-6) 3).toNat = 0 := by
    have r632 : (x (-6) 2).toNat = (x (-6) 3).toNat := congrArg Bool.toNat (h23 (-6))
    have b633 := hb (x (-6) 2)
    have b634 := hb (x (-6) 3)
    clear * - r632 b633 b634 d619
    omega
  have d635 : (x (-6) 3 && x (-6) 12).toNat = 0 := by
    have r636 := hand1 (x (-6) 3) (x (-6) 12)
    have b637 := hb (x (-6) 3)
    have b638 := hb (x (-6) 3 && x (-6) 12)
    clear * - r636 b637 b638 d631
    omega
  have d639 : (x (-6) 11).toNat = 0 := by
    have r640 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
    have b641 := hb (x (-6) 3)
    have b642 := hb (x (-6) 11)
    clear * - r640 b641 b642 d631
    omega
  have d643 : (x (-6) 1 && x (-6) 11).toNat = 0 := by
    have r644 := hand2 (x (-6) 1) (x (-6) 11)
    have b645 := hb (x (-6) 11)
    have b646 := hb (x (-6) 1 && x (-6) 11)
    clear * - r644 b645 b646 d639
    omega
  have d647 : (x (-6) 10).toNat = 0 := by
    have r648 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
    have b649 := hb (x (-6) 2)
    have b650 := hb (x (-6) 10)
    clear * - r648 b649 b650 d619
    omega
  have d651 : (x 4 8).toNat = 0 := by
    have r652 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e653 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e654 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e655 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e656 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e657 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e658 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b659 := hb (x (-3) 7)
    have b660 := hb (x (-2) 6)
    have b661 := hb (x (-1) 5)
    have b662 := hb (x 0 4)
    have b663 := hb (x 1 11)
    have b664 := hb (x 2 10)
    have b665 := hb (x 3 9)
    have b666 := hb (x 4 8)
    clear * - r652 e653 e654 e655 e656 e657 e658 b659 b660 b661 b662 b663 b664 b665 b666 d224 d348 g1 d49
    omega
  have d667 : (x 2 10).toNat = 0 := by
    have r668 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e669 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e670 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e671 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e672 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e673 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e674 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b675 := hb (x (-3) 7)
    have b676 := hb (x (-2) 6)
    have b677 := hb (x (-1) 5)
    have b678 := hb (x 0 4)
    have b679 := hb (x 1 11)
    have b680 := hb (x 2 10)
    have b681 := hb (x 3 9)
    have b682 := hb (x 4 8)
    clear * - r668 e669 e670 e671 e672 e673 e674 b675 b676 b677 b678 b679 b680 b681 b682 d651 d224 d348 g1 d49
    omega
  have d683 : (x 2 1 && x 2 10).toNat = 0 := by
    have r684 := hand2 (x 2 1) (x 2 10)
    have b685 := hb (x 2 10)
    have b686 := hb (x 2 1 && x 2 10)
    clear * - r684 b685 b686 d667
    omega
  have d687 : (x (-2) 5 && x (-2) 14).toNat = 1 := by
    have r688 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b689 := hb (x (-3) 6)
    have b690 := hb (x 3 9)
    have b691 := hb (x 2 1 && x 2 10)
    have b692 := hb (x 1 2 && x 1 11)
    have b693 := hb (x 0 3 && x 0 12)
    have b694 := hb (x (-1) 4 && x (-1) 13)
    have b695 := hb (x (-2) 5 && x (-2) 14)
    clear * - r688 b689 b690 b691 b692 b693 b694 b695 d224 d683 d336 d1 d45 d408
    omega
  have d696 : (x (-2) 5).toNat = 1 := by
    have r697 := hand1 (x (-2) 5) (x (-2) 14)
    have b698 := hb (x (-2) 5)
    have b699 := hb (x (-2) 5 && x (-2) 14)
    clear * - r697 b698 b699 d687
    omega
  have d700 : (x (-2) 13).toNat = 1 := by
    have r701 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
    have b702 := hb (x (-2) 5)
    have b703 := hb (x (-2) 13)
    clear * - r701 b702 b703 d696
    omega
  have d704 : (x (-1) 12).toNat = 0 := by
    have r705 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e706 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e707 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b708 := hb (x (-4) 3)
    have b709 := hb (x (-3) 2)
    have b710 := hb (x (-2) 13)
    have b711 := hb (x (-1) 12)
    clear * - r705 e706 e707 b708 b709 b710 b711 d700 d109
    omega
  have d712 : (x (-1) 4).toNat = 0 := by
    have r713 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
    have b714 := hb (x (-1) 4)
    have b715 := hb (x (-1) 12)
    clear * - r713 b714 b715 d704
    omega
  have d716 : (x (-4) 3).toNat = 0 := by
    have r717 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e718 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e719 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b720 := hb (x (-4) 3)
    have b721 := hb (x (-3) 2)
    have b722 := hb (x (-2) 13)
    have b723 := hb (x (-1) 12)
    clear * - r717 e718 e719 b720 b721 b722 b723 d704 d700 d109
    omega
  have d724 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
    have r725 := hand1 (x (-4) 3) (x (-4) 14)
    have b726 := hb (x (-4) 3)
    have b727 := hb (x (-4) 3 && x (-4) 14)
    clear * - r725 b726 b727 d716
    omega
  have d728 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
    have r729 := hand1 (x (-4) 3) (x (-4) 13)
    have b730 := hb (x (-4) 3)
    have b731 := hb (x (-4) 3 && x (-4) 13)
    clear * - r729 b730 b731 d716
    omega
  have d732 : (x (-6) 5).toNat = 1 := by
    have r733 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b734 := hb (x (-6) 5)
    have b735 := hb (x (-1) 10)
    have b736 := hb (x (-2) 1 && x (-2) 11)
    have b737 := hb (x (-3) 2 && x (-3) 12)
    have b738 := hb (x (-4) 3 && x (-4) 13)
    have b739 := hb (x (-5) 4 && x (-5) 14)
    clear * - r733 b734 b735 b736 b737 b738 b739 d388 d81 d117 d728 d436
    omega
  have d740 : (x (-6) 13).toNat = 1 := by
    have r741 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
    have b742 := hb (x (-6) 5)
    have b743 := hb (x (-6) 13)
    clear * - r741 b742 b743 d732
    omega
  have d744 : (x (-5) 12).toNat = 0 := by
    have r745 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e746 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
    have e747 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
    have b748 := hb (x (-8) 3)
    have b749 := hb (x (-7) 2)
    have b750 := hb (x (-6) 13)
    have b751 := hb (x (-5) 12)
    clear * - r745 e746 e747 b748 b749 b750 b751 d740 d484
    omega
  have d752 : (x (-5) 4).toNat = 0 := by
    have r753 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
    have b754 := hb (x (-5) 4)
    have b755 := hb (x (-5) 12)
    clear * - r753 b754 b755 d744
    omega
  have d756 : (x (-2) 1 && x (-2) 12).toNat = 1 := by
    have r757 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b758 := hb (x (-5) 4)
    have b759 := hb (x (-1) 11)
    have b760 := hb (x (-2) 1 && x (-2) 12)
    have b761 := hb (x (-3) 2 && x (-3) 13)
    have b762 := hb (x (-4) 3 && x (-4) 14)
    clear * - r757 b758 b759 b760 b761 b762 d384 d113 d724 d752
    omega
  have d763 : (x (-2) 12).toNat = 1 := by
    have r764 := hand2 (x (-2) 1) (x (-2) 12)
    have b765 := hb (x (-2) 12)
    have b766 := hb (x (-2) 1 && x (-2) 12)
    clear * - r764 b765 b766 d756
    omega
  have d767 : (x (-4) 2).toNat = 0 := by
    have r768 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e769 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
    have e770 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
    have b771 := hb (x (-5) 3)
    have b772 := hb (x (-4) 2)
    have b773 := hb (x (-3) 13)
    have b774 := hb (x (-2) 12)
    clear * - r768 e769 e770 b771 b772 b773 b774 d763 d588 d452
    omega
  have d775 : (x (-4) 2 && x (-4) 13).toNat = 0 := by
    have r776 := hand1 (x (-4) 2) (x (-4) 13)
    have b777 := hb (x (-4) 2)
    have b778 := hb (x (-4) 2 && x (-4) 13)
    clear * - r776 b777 b778 d767
    omega
  have d779 : (x (-6) 4).toNat = 1 := by
    have r780 : 1 ≤ (x (-2) 11).toNat + (x (-3) 1 && x (-3) 12).toNat + (x (-4) 2 && x (-4) 13).toNat + (x (-5) 3 && x (-5) 14).toNat + (x (-6) 4).toNat := by have q := hcov11 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b781 := hb (x (-6) 4)
    have b782 := hb (x (-2) 11)
    have b783 := hb (x (-3) 1 && x (-3) 12)
    have b784 := hb (x (-4) 2 && x (-4) 13)
    have b785 := hb (x (-5) 3 && x (-5) 14)
    clear * - r780 b781 b782 b783 b784 b785 d77 d396 d775 d432
    omega
  have d786 : (x (-6) 12).toNat = 1 := by
    have r787 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
    have b788 := hb (x (-6) 4)
    have b789 := hb (x (-6) 12)
    clear * - r787 b788 b789 d779
    omega
  have d790 : (x (-8) 2).toNat = 0 := by
    have r791 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e792 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
    have e793 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
    have b794 := hb (x (-9) 3)
    have b795 := hb (x (-8) 2)
    have b796 := hb (x (-7) 13)
    have b797 := hb (x (-6) 12)
    clear * - r791 e792 e793 b794 b795 b796 b797 d786 d560 d540
    omega
  have d798 : (x (-8) 2 && x (-8) 13).toNat = 0 := by
    have r799 := hand1 (x (-8) 2) (x (-8) 13)
    have b800 := hb (x (-8) 2)
    have b801 := hb (x (-8) 2 && x (-8) 13)
    clear * - r799 b800 b801 d790
    omega
  have d802 : (x (-10) 4).toNat = 1 := by
    have r803 : 1 ≤ (x (-6) 11).toNat + (x (-7) 1 && x (-7) 12).toNat + (x (-8) 2 && x (-8) 13).toNat + (x (-9) 3 && x (-9) 14).toNat + (x (-10) 4).toNat := by have q := hcov11 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b804 := hb (x (-10) 4)
    have b805 := hb (x (-6) 11)
    have b806 := hb (x (-7) 1 && x (-7) 12)
    have b807 := hb (x (-8) 2 && x (-8) 13)
    have b808 := hb (x (-9) 3 && x (-9) 14)
    clear * - r803 b804 b805 b806 b807 b808 d639 d472 d798 d524
    omega
  have d809 : (x (-8) 3).toNat = 0 := by
    have r810 : (x (-8) 2).toNat = (x (-8) 3).toNat := congrArg Bool.toNat (h23 (-8))
    have b811 := hb (x (-8) 2)
    have b812 := hb (x (-8) 3)
    clear * - r810 b811 b812 d790
    omega
  have d813 : (x (-8) 3 && x (-8) 13).toNat = 0 := by
    have r814 := hand1 (x (-8) 3) (x (-8) 13)
    have b815 := hb (x (-8) 3)
    have b816 := hb (x (-8) 3 && x (-8) 13)
    clear * - r814 b815 b816 d809
    omega
  have d817 : (x (-10) 5).toNat = 1 := by
    have r818 : 1 ≤ (x (-5) 10).toNat + (x (-6) 1 && x (-6) 11).toNat + (x (-7) 2 && x (-7) 12).toNat + (x (-8) 3 && x (-8) 13).toNat + (x (-9) 4 && x (-9) 14).toNat + (x (-10) 5).toNat := by have q := hcov10 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b819 := hb (x (-10) 5)
    have b820 := hb (x (-5) 10)
    have b821 := hb (x (-6) 1 && x (-6) 11)
    have b822 := hb (x (-7) 2 && x (-7) 12)
    have b823 := hb (x (-8) 3 && x (-8) 13)
    have b824 := hb (x (-9) 4 && x (-9) 14)
    clear * - r818 b819 b820 b821 b822 b823 b824 d456 d643 d488 d813 d528
    omega
  have d825 : (x (-10) 13).toNat = 1 := by
    have r826 : (x (-10) 5).toNat ≤ (x (-10) 13).toNat := himp _ _ (hp5 (-10))
    have b827 := hb (x (-10) 5)
    have b828 := hb (x (-10) 13)
    clear * - r826 b827 b828 d817
    omega
  have d829 : (x (-9) 12).toNat = 0 := by
    have r830 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e831 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
    have e832 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
    have b833 := hb (x (-12) 3)
    have b834 := hb (x (-11) 2)
    have b835 := hb (x (-10) 13)
    have b836 := hb (x (-9) 12)
    clear * - r830 e831 e832 b833 b834 b835 b836 d825
    omega
  have d837 : (x (-11) 2).toNat = 0 := by
    have r838 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e839 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
    have e840 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
    have b841 := hb (x (-12) 3)
    have b842 := hb (x (-11) 2)
    have b843 := hb (x (-10) 13)
    have b844 := hb (x (-9) 12)
    clear * - r838 e839 e840 b841 b842 b843 b844 d829 d825
    omega
  have d845 : (x (-11) 3).toNat = 0 := by
    have r846 : (x (-11) 2).toNat = (x (-11) 3).toNat := congrArg Bool.toNat (h23 (-11))
    have b847 := hb (x (-11) 2)
    have b848 := hb (x (-11) 3)
    clear * - r846 b847 b848 d837
    omega
  have d849 : (x (-11) 3 && x (-11) 14).toNat = 0 := by
    have r850 := hand1 (x (-11) 3) (x (-11) 14)
    have b851 := hb (x (-11) 3)
    have b852 := hb (x (-11) 3 && x (-11) 14)
    clear * - r850 b851 b852 d845
    omega
  have d853 : (x (-11) 11).toNat = 0 := by
    have r854 : (x (-11) 11).toNat ≤ (x (-11) 3).toNat := himp _ _ (hp11 (-11))
    have b855 := hb (x (-11) 3)
    have b856 := hb (x (-11) 11)
    clear * - r854 b855 b856 d845
    omega
  have d857 : (x (-8) 11).toNat = 0 := by
    have r858 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
    have b859 := hb (x (-8) 3)
    have b860 := hb (x (-8) 11)
    clear * - r858 b859 b860 d809
    omega
  have d861 : (x (-8) 10).toNat = 0 := by
    have r862 : (x (-8) 10).toNat ≤ (x (-8) 2).toNat := himp _ _ (hp10 (-8))
    have b863 := hb (x (-8) 2)
    have b864 := hb (x (-8) 10)
    clear * - r862 b863 b864 d790
    omega
  have d865 : (x (-4) 10).toNat = 0 := by
    have r866 : (x (-4) 10).toNat ≤ (x (-4) 2).toNat := himp _ _ (hp10 (-4))
    have b867 := hb (x (-4) 2)
    have b868 := hb (x (-4) 10)
    clear * - r866 b867 b868 d767
    omega
  have d869 : (x (-4) 1 && x (-4) 10).toNat = 0 := by
    have r870 := hand2 (x (-4) 1) (x (-4) 10)
    have b871 := hb (x (-4) 10)
    have b872 := hb (x (-4) 1 && x (-4) 10)
    clear * - r870 b871 b872 d865
    omega
  have d873 : (x (-8) 5 && x (-8) 14).toNat = 1 := by
    have r874 : 1 ≤ (x (-3) 9).toNat + (x (-4) 1 && x (-4) 10).toNat + (x (-5) 2 && x (-5) 11).toNat + (x (-6) 3 && x (-6) 12).toNat + (x (-7) 4 && x (-7) 13).toNat + (x (-8) 5 && x (-8) 14).toNat + (x (-9) 6).toNat := by have q := hcov9 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b875 := hb (x (-9) 6)
    have b876 := hb (x (-3) 9)
    have b877 := hb (x (-4) 1 && x (-4) 10)
    have b878 := hb (x (-5) 2 && x (-5) 11)
    have b879 := hb (x (-6) 3 && x (-6) 12)
    have b880 := hb (x (-7) 4 && x (-7) 13)
    have b881 := hb (x (-8) 5 && x (-8) 14)
    clear * - r874 b875 b876 b877 b878 b879 b880 b881 d600 d869 d448 d635 d564 d532
    omega
  have d882 : (x (-8) 5).toNat = 1 := by
    have r883 := hand1 (x (-8) 5) (x (-8) 14)
    have b884 := hb (x (-8) 5)
    have b885 := hb (x (-8) 5 && x (-8) 14)
    clear * - r883 b884 b885 d873
    omega
  have d886 : (x (-8) 13).toNat = 1 := by
    have r887 : (x (-8) 5).toNat ≤ (x (-8) 13).toNat := himp _ _ (hp5 (-8))
    have b888 := hb (x (-8) 5)
    have b889 := hb (x (-8) 13)
    clear * - r887 b888 b889 d882
    omega
  have d890 : (x (-7) 12).toNat = 0 := by
    have r891 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e892 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
    have e893 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
    have b894 := hb (x (-10) 3)
    have b895 := hb (x (-9) 2)
    have b896 := hb (x (-8) 13)
    have b897 := hb (x (-7) 12)
    clear * - r891 e892 e893 b894 b895 b896 b897 d886 d536
    omega
  have d898 : (x (-10) 3).toNat = 0 := by
    have r899 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e900 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
    have e901 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
    have b902 := hb (x (-10) 3)
    have b903 := hb (x (-9) 2)
    have b904 := hb (x (-8) 13)
    have b905 := hb (x (-7) 12)
    clear * - r899 e900 e901 b902 b903 b904 b905 d890 d886 d536
    omega
  have d906 : (x (-10) 2).toNat = 0 := by
    have r907 : (x (-10) 2).toNat = (x (-10) 3).toNat := congrArg Bool.toNat (h23 (-10))
    have b908 := hb (x (-10) 2)
    have b909 := hb (x (-10) 3)
    clear * - r907 b908 b909 d898
    omega
  have d910 : (x (-10) 2 && x (-10) 13).toNat = 0 := by
    have r911 := hand1 (x (-10) 2) (x (-10) 13)
    have b912 := hb (x (-10) 2)
    have b913 := hb (x (-10) 2 && x (-10) 13)
    clear * - r911 b912 b913 d906
    omega
  have d914 : (x (-12) 4).toNat = 1 := by
    have r915 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := by have q := hcov11 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b916 := hb (x (-12) 4)
    have b917 := hb (x (-8) 11)
    have b918 := hb (x (-9) 1 && x (-9) 12)
    have b919 := hb (x (-10) 2 && x (-10) 13)
    have b920 := hb (x (-11) 3 && x (-11) 14)
    clear * - r915 b916 b917 b918 b919 b920 d857 d516 d910 d849
    omega
  have d921 : (x (-10) 10).toNat = 0 := by
    have r922 : (x (-10) 10).toNat ≤ (x (-10) 2).toNat := himp _ _ (hp10 (-10))
    have b923 := hb (x (-10) 2)
    have b924 := hb (x (-10) 10)
    clear * - r922 b923 b924 d906
    omega
  have d925 : (x (-8) 4 && x (-8) 14).toNat = 1 := by
    have r926 : 1 ≤ (x (-4) 10).toNat + (x (-5) 1 && x (-5) 11).toNat + (x (-6) 2 && x (-6) 12).toNat + (x (-7) 3 && x (-7) 13).toNat + (x (-8) 4 && x (-8) 14).toNat + (x (-9) 5).toNat := by have q := hcov10 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b927 := hb (x (-9) 5)
    have b928 := hb (x (-4) 10)
    have b929 := hb (x (-5) 1 && x (-5) 11)
    have b930 := hb (x (-6) 2 && x (-6) 12)
    have b931 := hb (x (-7) 3 && x (-7) 13)
    have b932 := hb (x (-8) 4 && x (-8) 14)
    clear * - r926 b927 b928 b929 b930 b931 b932 d865 d424 d627 d496 d552
    omega
  have d933 : (x (-8) 4).toNat = 1 := by
    have r934 := hand1 (x (-8) 4) (x (-8) 14)
    have b935 := hb (x (-8) 4)
    have b936 := hb (x (-8) 4 && x (-8) 14)
    clear * - r934 b935 b936 d925
    omega
  have d937 : (x (-4) 11).toNat = 0 := by
    have r938 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
    have b939 := hb (x (-4) 3)
    have b940 := hb (x (-4) 11)
    clear * - r938 b939 b940 d716
    omega
  have d941 : (x (-4) 4 && x (-4) 11).toNat = 0 := by
    have r942 := hand2 (x (-4) 4) (x (-4) 11)
    have b943 := hb (x (-4) 11)
    have b944 := hb (x (-4) 4 && x (-4) 11)
    clear * - r942 b943 b944 d937
    omega
  have d945 : (x (-2) 4 && x (-2) 14).toNat = 1 := by
    have r946 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b947 := hb (x (-3) 5)
    have b948 := hb (x 2 10)
    have b949 := hb (x 1 1 && x 1 11)
    have b950 := hb (x 0 2 && x 0 12)
    have b951 := hb (x (-1) 3 && x (-1) 13)
    have b952 := hb (x (-2) 4 && x (-2) 14)
    clear * - r946 b947 b948 b949 b950 b951 b952 d667 d196 d9 d41 d592
    omega
  have d953 : (x (-2) 4).toNat = 1 := by
    have r954 := hand1 (x (-2) 4) (x (-2) 14)
    have b955 := hb (x (-2) 4)
    have b956 := hb (x (-2) 4 && x (-2) 14)
    clear * - r954 b955 b956 d945
    omega
  have d957 : (x (-2) 6).toNat = 0 := by
    have r958 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e959 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e960 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e961 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e962 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e963 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e964 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b965 := hb (x (-3) 7)
    have b966 := hb (x (-2) 6)
    have b967 := hb (x (-1) 5)
    have b968 := hb (x 0 4)
    have b969 := hb (x 1 11)
    have b970 := hb (x 2 10)
    have b971 := hb (x 3 9)
    have b972 := hb (x 4 8)
    clear * - r958 e959 e960 e961 e962 e963 e964 b965 b966 b967 b968 b969 b970 b971 b972 d651 d224 d667 d348 g1 d49
    omega
  have d973 : (x (-2) 6 && x (-2) 13).toNat = 0 := by
    have r974 := hand1 (x (-2) 6) (x (-2) 13)
    have b975 := hb (x (-2) 6)
    have b976 := hb (x (-2) 6 && x (-2) 13)
    clear * - r974 b975 b976 d957
    omega
  have d977 : (x 3 8).toNat = 0 := by
    have r978 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e979 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
    have e980 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
    have e981 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
    have e982 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
    have e983 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
    have e984 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
    have b985 := hb (x (-4) 7)
    have b986 := hb (x (-3) 6)
    have b987 := hb (x (-2) 5)
    have b988 := hb (x (-1) 4)
    have b989 := hb (x 0 11)
    have b990 := hb (x 1 10)
    have b991 := hb (x 2 9)
    have b992 := hb (x 3 8)
    clear * - r978 e979 e980 e981 e982 e983 e984 b985 b986 b987 b988 b989 b990 b991 b992 d352 d17 d712 d696 d408
    omega
  have d993 : (x 2 9).toNat = 0 := by
    have r994 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e995 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
    have e996 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
    have e997 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
    have e998 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
    have e999 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
    have e1000 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
    have b1001 := hb (x (-4) 7)
    have b1002 := hb (x (-3) 6)
    have b1003 := hb (x (-2) 5)
    have b1004 := hb (x (-1) 4)
    have b1005 := hb (x 0 11)
    have b1006 := hb (x 1 10)
    have b1007 := hb (x 2 9)
    have b1008 := hb (x 3 8)
    clear * - r994 e995 e996 e997 e998 e999 e1000 b1001 b1002 b1003 b1004 b1005 b1006 b1007 b1008 d977 d352 d17 d712 d696 d408
    omega
  have d1009 : (x 2 2 && x 2 9).toNat = 0 := by
    have r1010 := hand2 (x 2 2) (x 2 9)
    have b1011 := hb (x 2 9)
    have b1012 := hb (x 2 2 && x 2 9)
    clear * - r1010 b1011 b1012 d993
    omega
  have d1013 : (x 2 8).toNat = 0 := by
    have r1014 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1015 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
    have e1016 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
    have e1017 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
    have e1018 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
    have e1019 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
    have e1020 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
    have b1021 := hb (x (-5) 7)
    have b1022 := hb (x (-4) 6)
    have b1023 := hb (x (-3) 5)
    have b1024 := hb (x (-2) 4)
    have b1025 := hb (x (-1) 11)
    have b1026 := hb (x 0 10)
    have b1027 := hb (x 1 9)
    have b1028 := hb (x 2 8)
    clear * - r1014 e1015 e1016 e1017 e1018 e1019 e1020 b1021 b1022 b1023 b1024 b1025 b1026 b1027 b1028 d204 d25 d384 d953 d592
    omega
  have d1029 : (x (-4) 6).toNat = 0 := by
    have r1030 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1031 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
    have e1032 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
    have e1033 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
    have e1034 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
    have e1035 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
    have e1036 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
    have b1037 := hb (x (-5) 7)
    have b1038 := hb (x (-4) 6)
    have b1039 := hb (x (-3) 5)
    have b1040 := hb (x (-2) 4)
    have b1041 := hb (x (-1) 11)
    have b1042 := hb (x 0 10)
    have b1043 := hb (x 1 9)
    have b1044 := hb (x 2 8)
    clear * - r1030 e1031 e1032 e1033 e1034 e1035 e1036 b1037 b1038 b1039 b1040 b1041 b1042 b1043 b1044 d1013 d204 d25 d384 d953 d592
    omega
  have d1045 : (x (-4) 6 && x (-4) 13).toNat = 0 := by
    have r1046 := hand1 (x (-4) 6) (x (-4) 13)
    have b1047 := hb (x (-4) 6)
    have b1048 := hb (x (-4) 6 && x (-4) 13)
    clear * - r1046 b1047 b1048 d1029
    omega
  have d1049 : (x 0 8).toNat = 0 := by
    have r1050 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1051 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e1052 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e1053 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e1054 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e1055 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e1056 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b1057 := hb (x (-7) 7)
    have b1058 := hb (x (-6) 6)
    have b1059 := hb (x (-5) 5)
    have b1060 := hb (x (-4) 4)
    have b1061 := hb (x (-3) 11)
    have b1062 := hb (x (-2) 10)
    have b1063 := hb (x (-1) 9)
    have b1064 := hb (x 0 8)
    clear * - r1050 e1051 e1052 e1053 e1054 e1055 e1056 b1057 b1058 b1059 b1060 b1061 b1062 b1063 b1064 d167 d89 d604 d608 d576
    omega
  have d1065 : (x (-6) 6).toNat = 0 := by
    have r1066 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1067 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e1068 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e1069 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e1070 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e1071 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e1072 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b1073 := hb (x (-7) 7)
    have b1074 := hb (x (-6) 6)
    have b1075 := hb (x (-5) 5)
    have b1076 := hb (x (-4) 4)
    have b1077 := hb (x (-3) 11)
    have b1078 := hb (x (-2) 10)
    have b1079 := hb (x (-1) 9)
    have b1080 := hb (x 0 8)
    clear * - r1066 e1067 e1068 e1069 e1070 e1071 e1072 b1073 b1074 b1075 b1076 b1077 b1078 b1079 b1080 d1049 d167 d89 d604 d608 d576
    omega
  have d1081 : (x (-6) 6 && x (-6) 13).toNat = 0 := by
    have r1082 := hand1 (x (-6) 6) (x (-6) 13)
    have b1083 := hb (x (-6) 6)
    have b1084 := hb (x (-6) 6 && x (-6) 13)
    clear * - r1082 b1083 b1084 d1065
    omega
  have d1085 : (x (-4) 8).toNat = 0 := by
    have r1086 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1087 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
    have e1088 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
    have e1089 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
    have e1090 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
    have e1091 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
    have e1092 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
    have b1093 := hb (x (-11) 7)
    have b1094 := hb (x (-10) 6)
    have b1095 := hb (x (-9) 5)
    have b1096 := hb (x (-8) 4)
    have b1097 := hb (x (-7) 11)
    have b1098 := hb (x (-6) 10)
    have b1099 := hb (x (-5) 9)
    have b1100 := hb (x (-4) 8)
    clear * - r1086 e1087 e1088 e1089 e1090 e1091 e1092 b1093 b1094 b1095 b1096 b1097 b1098 b1099 b1100 d584 d647 d500 d933 d552
    omega
  have d1101 : (x (-6) 8).toNat = 0 := by
    have r1102 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1103 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
    have e1104 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
    have e1105 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
    have e1106 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
    have e1107 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
    have e1108 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
    have b1109 := hb (x (-13) 7)
    have b1110 := hb (x (-12) 6)
    have b1111 := hb (x (-11) 5)
    have b1112 := hb (x (-10) 4)
    have b1113 := hb (x (-9) 11)
    have b1114 := hb (x (-8) 10)
    have b1115 := hb (x (-7) 9)
    have b1116 := hb (x (-6) 8)
    clear * - r1102 e1103 e1104 e1105 e1106 e1107 e1108 b1109 b1110 b1111 b1112 b1113 b1114 b1115 b1116 d568 d861 d544 d802
    omega
  have d1117 : (x (-8) 8).toNat = 0 := by
    have r1118 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1119 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
    have e1120 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
    have e1121 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
    have e1122 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
    have e1123 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
    have e1124 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
    have b1125 := hb (x (-15) 7)
    have b1126 := hb (x (-14) 6)
    have b1127 := hb (x (-13) 5)
    have b1128 := hb (x (-12) 4)
    have b1129 := hb (x (-11) 11)
    have b1130 := hb (x (-10) 10)
    have b1131 := hb (x (-9) 9)
    have b1132 := hb (x (-8) 8)
    clear * - r1118 e1119 e1120 e1121 e1122 e1123 e1124 b1125 b1126 b1127 b1128 b1129 b1130 b1131 b1132 d556 d921 d853 d914
    omega
  have d1133 : (x 4 7).toNat = 1 := by
    have r1134 : 1 ≤ (x 4 7).toNat + (x 3 1 && x 3 8).toNat + (x 2 2 && x 2 9).toNat + (x 1 3 && x 1 10).toNat + (x 0 4 && x 0 11).toNat + (x (-1) 5 && x (-1) 12).toNat + (x (-2) 6 && x (-2) 13).toNat + (x (-3) 7 && x (-3) 14).toNat + (x (-4) 8).toNat := by have q := hcov7 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1135 := hb (x (-4) 8)
    have b1136 := hb (x 4 7)
    have b1137 := hb (x 3 1 && x 3 8)
    have b1138 := hb (x 2 2 && x 2 9)
    have b1139 := hb (x 1 3 && x 1 10)
    have b1140 := hb (x 0 4 && x 0 11)
    have b1141 := hb (x (-1) 5 && x (-1) 12)
    have b1142 := hb (x (-2) 6 && x (-2) 13)
    have b1143 := hb (x (-3) 7 && x (-3) 14)
    clear * - r1134 b1135 b1136 b1137 b1138 b1139 b1140 b1141 b1142 b1143 d220 d1009 d344 d21 d53 d973 d404 d1085
    omega
  have d1144 : (x 11 8).toNat = 0 := by
    have r1145 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1146 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e1147 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e1148 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e1149 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e1150 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e1151 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have b1152 := hb (x 4 7)
    have b1153 := hb (x 5 6)
    have b1154 := hb (x 6 5)
    have b1155 := hb (x 7 4)
    have b1156 := hb (x 8 11)
    have b1157 := hb (x 9 10)
    have b1158 := hb (x 10 9)
    have b1159 := hb (x 11 8)
    clear * - r1145 e1146 e1147 e1148 e1149 e1150 e1151 b1152 b1153 b1154 b1155 b1156 b1157 b1158 b1159 d280 d296 d1133
    omega
  have d1160 : (x 10 9).toNat = 0 := by
    have r1161 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1162 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e1163 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e1164 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e1165 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e1166 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e1167 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have b1168 := hb (x 4 7)
    have b1169 := hb (x 5 6)
    have b1170 := hb (x 6 5)
    have b1171 := hb (x 7 4)
    have b1172 := hb (x 8 11)
    have b1173 := hb (x 9 10)
    have b1174 := hb (x 10 9)
    have b1175 := hb (x 11 8)
    clear * - r1161 e1162 e1163 e1164 e1165 e1166 e1167 b1168 b1169 b1170 b1171 b1172 b1173 b1174 b1175 d1144 d280 d296 d1133
    omega
  have d1176 : (x 8 11).toNat = 0 := by
    have r1177 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1178 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e1179 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e1180 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e1181 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e1182 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e1183 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have b1184 := hb (x 4 7)
    have b1185 := hb (x 5 6)
    have b1186 := hb (x 6 5)
    have b1187 := hb (x 7 4)
    have b1188 := hb (x 8 11)
    have b1189 := hb (x 9 10)
    have b1190 := hb (x 10 9)
    have b1191 := hb (x 11 8)
    clear * - r1177 e1178 e1179 e1180 e1181 e1182 e1183 b1184 b1185 b1186 b1187 b1188 b1189 b1190 b1191 d1144 d1160 d280 d296 d1133
    omega
  have d1192 : (x 8 1 && x 8 11).toNat = 0 := by
    have r1193 := hand2 (x 8 1) (x 8 11)
    have b1194 := hb (x 8 11)
    have b1195 := hb (x 8 1 && x 8 11)
    clear * - r1193 b1194 b1195 d1176
    omega
  have d1196 : (x 2 7).toNat = 1 := by
    have r1197 : 1 ≤ (x 2 7).toNat + (x 1 1 && x 1 8).toNat + (x 0 2 && x 0 9).toNat + (x (-1) 3 && x (-1) 10).toNat + (x (-2) 4 && x (-2) 11).toNat + (x (-3) 5 && x (-3) 12).toNat + (x (-4) 6 && x (-4) 13).toNat + (x (-5) 7 && x (-5) 14).toNat + (x (-6) 8).toNat := by have q := hcov7 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1198 := hb (x (-6) 8)
    have b1199 := hb (x 2 7)
    have b1200 := hb (x 1 1 && x 1 8)
    have b1201 := hb (x 0 2 && x 0 9)
    have b1202 := hb (x (-1) 3 && x (-1) 10)
    have b1203 := hb (x (-2) 4 && x (-2) 11)
    have b1204 := hb (x (-3) 5 && x (-3) 12)
    have b1205 := hb (x (-4) 6 && x (-4) 13)
    have b1206 := hb (x (-5) 7 && x (-5) 14)
    clear * - r1197 b1198 b1199 b1200 b1201 b1202 b1203 b1204 b1205 b1206 d200 d13 d380 d85 d596 d1045 d440 d1101
    omega
  have d1207 : (x 9 8).toNat = 0 := by
    have r1208 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1209 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
    have e1210 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
    have e1211 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
    have e1212 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
    have e1213 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
    have e1214 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
    have b1215 := hb (x 2 7)
    have b1216 := hb (x 3 6)
    have b1217 := hb (x 4 5)
    have b1218 := hb (x 5 4)
    have b1219 := hb (x 6 11)
    have b1220 := hb (x 7 10)
    have b1221 := hb (x 8 9)
    have b1222 := hb (x 9 8)
    clear * - r1208 e1209 e1210 e1211 e1212 e1213 e1214 b1215 b1216 b1217 b1218 b1219 b1220 b1221 b1222 d292 d312 d1196
    omega
  have d1223 : (x 8 9).toNat = 0 := by
    have r1224 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1225 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
    have e1226 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
    have e1227 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
    have e1228 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
    have e1229 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
    have e1230 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
    have b1231 := hb (x 2 7)
    have b1232 := hb (x 3 6)
    have b1233 := hb (x 4 5)
    have b1234 := hb (x 5 4)
    have b1235 := hb (x 6 11)
    have b1236 := hb (x 7 10)
    have b1237 := hb (x 8 9)
    have b1238 := hb (x 9 8)
    clear * - r1224 e1225 e1226 e1227 e1228 e1229 e1230 b1231 b1232 b1233 b1234 b1235 b1236 b1237 b1238 d1207 d292 d312 d1196
    omega
  have d1239 : (x 6 11).toNat = 0 := by
    have r1240 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1241 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
    have e1242 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
    have e1243 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
    have e1244 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
    have e1245 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
    have e1246 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
    have b1247 := hb (x 2 7)
    have b1248 := hb (x 3 6)
    have b1249 := hb (x 4 5)
    have b1250 := hb (x 5 4)
    have b1251 := hb (x 6 11)
    have b1252 := hb (x 7 10)
    have b1253 := hb (x 8 9)
    have b1254 := hb (x 9 8)
    clear * - r1240 e1241 e1242 e1243 e1244 e1245 e1246 b1247 b1248 b1249 b1250 b1251 b1252 b1253 b1254 d1207 d1223 d292 d312 d1196
    omega
  have d1255 : (x 6 1 && x 6 11).toNat = 0 := by
    have r1256 := hand2 (x 6 1) (x 6 11)
    have b1257 := hb (x 6 11)
    have b1258 := hb (x 6 1 && x 6 11)
    clear * - r1256 b1257 b1258 d1239
    omega
  have d1259 : (x 5 4).toNat = 0 := by
    have r1260 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1261 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
    have e1262 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
    have e1263 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
    have e1264 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
    have e1265 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
    have e1266 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
    have b1267 := hb (x 2 7)
    have b1268 := hb (x 3 6)
    have b1269 := hb (x 4 5)
    have b1270 := hb (x 5 4)
    have b1271 := hb (x 6 11)
    have b1272 := hb (x 7 10)
    have b1273 := hb (x 8 9)
    have b1274 := hb (x 9 8)
    clear * - r1260 e1261 e1262 e1263 e1264 e1265 e1266 b1267 b1268 b1269 b1270 b1271 b1272 b1273 b1274 d1207 d1223 d292 d1239 d312 d1196
    omega
  have d1275 : (x 4 5).toNat = 0 := by
    have r1276 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1277 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
    have e1278 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
    have e1279 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
    have e1280 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
    have e1281 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
    have e1282 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
    have b1283 := hb (x 2 7)
    have b1284 := hb (x 3 6)
    have b1285 := hb (x 4 5)
    have b1286 := hb (x 5 4)
    have b1287 := hb (x 6 11)
    have b1288 := hb (x 7 10)
    have b1289 := hb (x 8 9)
    have b1290 := hb (x 9 8)
    clear * - r1276 e1277 e1278 e1279 e1280 e1281 e1282 b1283 b1284 b1285 b1286 b1287 b1288 b1289 b1290 d1207 d1223 d292 d1239 d1259 d312 d1196
    omega
  have d1291 : (x 6 3 && x 6 13).toNat = 1 := by
    have r1292 : 1 ≤ (x 9 10).toNat + (x 8 1 && x 8 11).toNat + (x 7 2 && x 7 12).toNat + (x 6 3 && x 6 13).toNat + (x 5 4 && x 5 14).toNat + (x 4 5).toNat := by have q := hcov10 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1293 := hb (x 4 5)
    have b1294 := hb (x 9 10)
    have b1295 := hb (x 8 1 && x 8 11)
    have b1296 := hb (x 7 2 && x 7 12)
    have b1297 := hb (x 6 3 && x 6 13)
    have b1298 := hb (x 5 4 && x 5 14)
    clear * - r1292 b1293 b1294 b1295 b1296 b1297 b1298 d280 d1192 d288 d240 d1275
    omega
  have d1299 : (x 6 13).toNat = 1 := by
    have r1300 := hand2 (x 6 3) (x 6 13)
    have b1301 := hb (x 6 13)
    have b1302 := hb (x 6 3 && x 6 13)
    clear * - r1300 b1301 b1302 d1291
    omega
  have d1303 : (x 7 12).toNat = 0 := by
    have r1304 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1305 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e1306 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b1307 := hb (x 4 3)
    have b1308 := hb (x 5 2)
    have b1309 := hb (x 6 13)
    have b1310 := hb (x 7 12)
    clear * - r1304 e1305 e1306 b1307 b1308 b1309 b1310 d1299 d300
    omega
  have d1311 : (x 4 3).toNat = 0 := by
    have r1312 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1313 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e1314 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b1315 := hb (x 4 3)
    have b1316 := hb (x 5 2)
    have b1317 := hb (x 6 13)
    have b1318 := hb (x 7 12)
    clear * - r1312 e1313 e1314 b1315 b1316 b1317 b1318 d1303 d1299 d300
    omega
  have d1319 : (x 4 3 && x 4 13).toNat = 0 := by
    have r1320 := hand1 (x 4 3) (x 4 13)
    have b1321 := hb (x 4 3)
    have b1322 := hb (x 4 3 && x 4 13)
    clear * - r1320 b1321 b1322 d1311
    omega
  have d1323 : (x 2 5).toNat = 1 := by
    have r1324 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1325 := hb (x 2 5)
    have b1326 := hb (x 7 10)
    have b1327 := hb (x 6 1 && x 6 11)
    have b1328 := hb (x 5 2 && x 5 12)
    have b1329 := hb (x 4 3 && x 4 13)
    have b1330 := hb (x 3 4 && x 3 14)
    clear * - r1324 b1325 b1326 b1327 b1328 b1329 b1330 d292 d1255 d304 d1319 d212
    omega
  have d1331 : (x 7 8).toNat = 0 := by
    have r1332 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1333 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e1334 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e1335 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e1336 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e1337 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e1338 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b1339 := hb (x 0 7)
    have b1340 := hb (x 1 6)
    have b1341 := hb (x 2 5)
    have b1342 := hb (x 3 4)
    have b1343 := hb (x 4 11)
    have b1344 := hb (x 5 10)
    have b1345 := hb (x 6 9)
    have b1346 := hb (x 7 8)
    clear * - r1332 e1333 e1334 e1335 e1336 e1337 e1338 b1339 b1340 b1341 b1342 b1343 b1344 b1345 b1346 d308 d324 d1323 d356
    omega
  have d1347 : (x 6 9).toNat = 0 := by
    have r1348 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1349 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e1350 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e1351 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e1352 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e1353 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e1354 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b1355 := hb (x 0 7)
    have b1356 := hb (x 1 6)
    have b1357 := hb (x 2 5)
    have b1358 := hb (x 3 4)
    have b1359 := hb (x 4 11)
    have b1360 := hb (x 5 10)
    have b1361 := hb (x 6 9)
    have b1362 := hb (x 7 8)
    clear * - r1348 e1349 e1350 e1351 e1352 e1353 e1354 b1355 b1356 b1357 b1358 b1359 b1360 b1361 b1362 d1331 d308 d324 d1323 d356
    omega
  have d1363 : (x 4 11).toNat = 0 := by
    have r1364 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1365 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e1366 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e1367 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e1368 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e1369 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e1370 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b1371 := hb (x 0 7)
    have b1372 := hb (x 1 6)
    have b1373 := hb (x 2 5)
    have b1374 := hb (x 3 4)
    have b1375 := hb (x 4 11)
    have b1376 := hb (x 5 10)
    have b1377 := hb (x 6 9)
    have b1378 := hb (x 7 8)
    clear * - r1364 e1365 e1366 e1367 e1368 e1369 e1370 b1371 b1372 b1373 b1374 b1375 b1376 b1377 b1378 d1331 d1347 d308 d324 d1323 d356
    omega
  have d1379 : (x 0 7).toNat = 0 := by
    have r1380 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1381 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e1382 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e1383 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e1384 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e1385 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e1386 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b1387 := hb (x 0 7)
    have b1388 := hb (x 1 6)
    have b1389 := hb (x 2 5)
    have b1390 := hb (x 3 4)
    have b1391 := hb (x 4 11)
    have b1392 := hb (x 5 10)
    have b1393 := hb (x 6 9)
    have b1394 := hb (x 7 8)
    clear * - r1380 e1381 e1382 e1383 e1384 e1385 e1386 b1387 b1388 b1389 b1390 b1391 b1392 b1393 b1394 d1331 d1347 d308 d1363 d324 d1323 d356
    omega
  have r1395 : 1 ≤ (x 0 7).toNat + (x (-1) 1 && x (-1) 8).toNat + (x (-2) 2 && x (-2) 9).toNat + (x (-3) 3 && x (-3) 10).toNat + (x (-4) 4 && x (-4) 11).toNat + (x (-5) 5 && x (-5) 12).toNat + (x (-6) 6 && x (-6) 13).toNat + (x (-7) 7 && x (-7) 14).toNat + (x (-8) 8).toNat := by have q := hcov7 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have b1396 := hb (x (-8) 8)
  have b1397 := hb (x 0 7)
  have b1398 := hb (x (-1) 1 && x (-1) 8)
  have b1399 := hb (x (-2) 2 && x (-2) 9)
  have b1400 := hb (x (-3) 3 && x (-3) 10)
  have b1401 := hb (x (-4) 4 && x (-4) 11)
  have b1402 := hb (x (-5) 5 && x (-5) 12)
  have b1403 := hb (x (-6) 6 && x (-6) 13)
  have b1404 := hb (x (-7) 7 && x (-7) 14)
  linarith only [r1395, b1396, b1397, b1398, b1399, b1400, b1401, b1402, b1403, b1404, d1379, d163, d69, d105, d941, d580, d1081, d480, d1117]

theorem cycle_power_fifteen_tight_type_sequence_shape_rules_core_v30_41 (x : ℤ → Fin 16 → Bool)
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
    (h114 : ∀ p, x p 1 = x p 14)
    (h23 : ∀ p, x p 2 = x p 3)
    (g0 : (x 0 3).toNat = 0) (g1 : (x 0 4).toNat = 1) : False := cycle_power_fifteen_tight_type_sequence_shape_rules_core_v30_41_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 h114 h23 g0 g1
