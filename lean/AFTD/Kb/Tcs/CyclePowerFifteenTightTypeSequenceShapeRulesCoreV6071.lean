import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_shape_rules_core_v60_71

Topic: combinatorics   Node: c81c3a571ede

Provenance: helper lemma. Research thread RT-1, open case k = 15 (m = 4) of OP-205 (arXiv:2610.15635, Theorems 1.3-1.4: eq(C_n^k) for k+1 = 2^m, n even, (k+1) not dividing n). Experiment 9757: on the integer window [-24, 24] the layer-free tight-class model leaves 13 class types at the centre, none with an island; on [-32, 32] the six types {0,15}, {0,1,14,15}, {0..3,12..15}, {0..7,12..15}, {0..3,8..15}, {0..15}.

Window refutation for k = 15: in the layer-free tight-class model on the integer line (x p j: the class starting at p contains p + j; inner count 3 per vertex, distances 14, 12, 8 covered exactly once, the other distances covered, classes closed under the tight-class parent map), with x p 1 = x p 14 and x p 2 = x p 3 everywhere, the class at 0 cannot have bit 6 = 0 and bit 7 = 1.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_shape_rules_core_v60_71_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 6).toNat = 0) (g1 : (x 0 7).toNat = 1) : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d4008 : (x 0 6 && x 0 12).toNat = 0 := by
    have r4009 := hand1 (x 0 6) (x 0 12)
    have b4010 := hb (x 0 6)
    have b4011 := hb (x 0 6 && x 0 12)
    clear * - r4009 b4010 b4011 g0
    omega
  have d4012 : (x 7 8).toNat = 0 := by
    have r4013 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e4014 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e4015 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e4016 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e4017 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e4018 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e4019 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b4020 := hb (x 0 7)
    have b4021 := hb (x 1 6)
    have b4022 := hb (x 2 5)
    have b4023 := hb (x 3 4)
    have b4024 := hb (x 4 11)
    have b4025 := hb (x 5 10)
    have b4026 := hb (x 6 9)
    have b4027 := hb (x 7 8)
    clear * - r4013 e4014 e4015 e4016 e4017 e4018 e4019 b4020 b4021 b4022 b4023 b4024 b4025 b4026 b4027 g1
    omega
  have d4028 : (x 7 1 && x 7 8).toNat = 0 := by
    have r4029 := hand2 (x 7 1) (x 7 8)
    have b4030 := hb (x 7 8)
    have b4031 := hb (x 7 1 && x 7 8)
    clear * - r4029 b4030 b4031 d4012
    omega
  have d4032 : (x 7 2 && x 7 8).toNat = 0 := by
    have r4033 := hand2 (x 7 2) (x 7 8)
    have b4034 := hb (x 7 8)
    have b4035 := hb (x 7 2 && x 7 8)
    clear * - r4033 b4034 b4035 d4012
    omega
  have d4036 : (x 7 4 && x 7 8).toNat = 0 := by
    have r4037 := hand2 (x 7 4) (x 7 8)
    have b4038 := hb (x 7 8)
    have b4039 := hb (x 7 4 && x 7 8)
    clear * - r4037 b4038 b4039 d4012
    omega
  have d4040 : (x 6 9).toNat = 0 := by
    have r4041 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e4042 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e4043 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e4044 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e4045 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e4046 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e4047 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b4048 := hb (x 0 7)
    have b4049 := hb (x 1 6)
    have b4050 := hb (x 2 5)
    have b4051 := hb (x 3 4)
    have b4052 := hb (x 4 11)
    have b4053 := hb (x 5 10)
    have b4054 := hb (x 6 9)
    have b4055 := hb (x 7 8)
    clear * - r4041 e4042 e4043 e4044 e4045 e4046 e4047 b4048 b4049 b4050 b4051 b4052 b4053 b4054 b4055 d4012 g1
    omega
  have d4056 : (x 6 2 && x 6 9).toNat = 0 := by
    have r4057 := hand2 (x 6 2) (x 6 9)
    have b4058 := hb (x 6 9)
    have b4059 := hb (x 6 2 && x 6 9)
    clear * - r4057 b4058 b4059 d4040
    omega
  have d4060 : (x 6 3 && x 6 9).toNat = 0 := by
    have r4061 := hand2 (x 6 3) (x 6 9)
    have b4062 := hb (x 6 9)
    have b4063 := hb (x 6 3 && x 6 9)
    clear * - r4061 b4062 b4063 d4040
    omega
  have d4064 : (x 6 5 && x 6 9).toNat = 0 := by
    have r4065 := hand2 (x 6 5) (x 6 9)
    have b4066 := hb (x 6 9)
    have b4067 := hb (x 6 5 && x 6 9)
    clear * - r4065 b4066 b4067 d4040
    omega
  have d4068 : (x 5 10).toNat = 0 := by
    have r4069 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e4070 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e4071 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e4072 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e4073 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e4074 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e4075 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b4076 := hb (x 0 7)
    have b4077 := hb (x 1 6)
    have b4078 := hb (x 2 5)
    have b4079 := hb (x 3 4)
    have b4080 := hb (x 4 11)
    have b4081 := hb (x 5 10)
    have b4082 := hb (x 6 9)
    have b4083 := hb (x 7 8)
    clear * - r4069 e4070 e4071 e4072 e4073 e4074 e4075 b4076 b4077 b4078 b4079 b4080 b4081 b4082 b4083 d4012 d4040 g1
    omega
  have d4084 : (x 5 1 && x 5 10).toNat = 0 := by
    have r4085 := hand2 (x 5 1) (x 5 10)
    have b4086 := hb (x 5 10)
    have b4087 := hb (x 5 1 && x 5 10)
    clear * - r4085 b4086 b4087 d4068
    omega
  have d4088 : (x 5 3 && x 5 10).toNat = 0 := by
    have r4089 := hand2 (x 5 3) (x 5 10)
    have b4090 := hb (x 5 10)
    have b4091 := hb (x 5 3 && x 5 10)
    clear * - r4089 b4090 b4091 d4068
    omega
  have d4092 : (x 5 4 && x 5 10).toNat = 0 := by
    have r4093 := hand2 (x 5 4) (x 5 10)
    have b4094 := hb (x 5 10)
    have b4095 := hb (x 5 4 && x 5 10)
    clear * - r4093 b4094 b4095 d4068
    omega
  have d4096 : (x 5 6 && x 5 10).toNat = 0 := by
    have r4097 := hand2 (x 5 6) (x 5 10)
    have b4098 := hb (x 5 10)
    have b4099 := hb (x 5 6 && x 5 10)
    clear * - r4097 b4098 b4099 d4068
    omega
  have d4100 : (x 4 11).toNat = 0 := by
    have r4101 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e4102 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e4103 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e4104 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e4105 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e4106 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e4107 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b4108 := hb (x 0 7)
    have b4109 := hb (x 1 6)
    have b4110 := hb (x 2 5)
    have b4111 := hb (x 3 4)
    have b4112 := hb (x 4 11)
    have b4113 := hb (x 5 10)
    have b4114 := hb (x 6 9)
    have b4115 := hb (x 7 8)
    clear * - r4101 e4102 e4103 e4104 e4105 e4106 e4107 b4108 b4109 b4110 b4111 b4112 b4113 b4114 b4115 d4012 d4040 d4068 g1
    omega
  have d4116 : (x 4 2 && x 4 11).toNat = 0 := by
    have r4117 := hand2 (x 4 2) (x 4 11)
    have b4118 := hb (x 4 11)
    have b4119 := hb (x 4 2 && x 4 11)
    clear * - r4117 b4118 b4119 d4100
    omega
  have d4120 : (x 4 4 && x 4 11).toNat = 0 := by
    have r4121 := hand2 (x 4 4) (x 4 11)
    have b4122 := hb (x 4 11)
    have b4123 := hb (x 4 4 && x 4 11)
    clear * - r4121 b4122 b4123 d4100
    omega
  have d4124 : (x 4 5 && x 4 11).toNat = 0 := by
    have r4125 := hand2 (x 4 5) (x 4 11)
    have b4126 := hb (x 4 11)
    have b4127 := hb (x 4 5 && x 4 11)
    clear * - r4125 b4126 b4127 d4100
    omega
  have d4128 : (x 4 7 && x 4 11).toNat = 0 := by
    have r4129 := hand2 (x 4 7) (x 4 11)
    have b4130 := hb (x 4 11)
    have b4131 := hb (x 4 7 && x 4 11)
    clear * - r4129 b4130 b4131 d4100
    omega
  have d4132 : (x 3 4).toNat = 0 := by
    have r4133 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e4134 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e4135 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e4136 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e4137 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e4138 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e4139 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b4140 := hb (x 0 7)
    have b4141 := hb (x 1 6)
    have b4142 := hb (x 2 5)
    have b4143 := hb (x 3 4)
    have b4144 := hb (x 4 11)
    have b4145 := hb (x 5 10)
    have b4146 := hb (x 6 9)
    have b4147 := hb (x 7 8)
    clear * - r4133 e4134 e4135 e4136 e4137 e4138 e4139 b4140 b4141 b4142 b4143 b4144 b4145 b4146 b4147 d4012 d4040 d4068 d4100 g1
    omega
  have d4148 : (x 3 4 && x 3 14).toNat = 0 := by
    have r4149 := hand1 (x 3 4) (x 3 14)
    have b4150 := hb (x 3 4)
    have b4151 := hb (x 3 4 && x 3 14)
    clear * - r4149 b4150 b4151 d4132
    omega
  have d4152 : (x 3 4 && x 3 13).toNat = 0 := by
    have r4153 := hand1 (x 3 4) (x 3 13)
    have b4154 := hb (x 3 4)
    have b4155 := hb (x 3 4 && x 3 13)
    clear * - r4153 b4154 b4155 d4132
    omega
  have d4156 : (x 3 4 && x 3 10).toNat = 0 := by
    have r4157 := hand1 (x 3 4) (x 3 10)
    have b4158 := hb (x 3 4)
    have b4159 := hb (x 3 4 && x 3 10)
    clear * - r4157 b4158 b4159 d4132
    omega
  have d4160 : (x 3 4 && x 3 9).toNat = 0 := by
    have r4161 := hand1 (x 3 4) (x 3 9)
    have b4162 := hb (x 3 4)
    have b4163 := hb (x 3 4 && x 3 9)
    clear * - r4161 b4162 b4163 d4132
    omega
  have d4164 : (x 3 4 && x 3 8).toNat = 0 := by
    have r4165 := hand1 (x 3 4) (x 3 8)
    have b4166 := hb (x 3 4)
    have b4167 := hb (x 3 4 && x 3 8)
    clear * - r4165 b4166 b4167 d4132
    omega
  have d4168 : (x 2 5).toNat = 0 := by
    have r4169 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e4170 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e4171 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e4172 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e4173 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e4174 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e4175 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b4176 := hb (x 0 7)
    have b4177 := hb (x 1 6)
    have b4178 := hb (x 2 5)
    have b4179 := hb (x 3 4)
    have b4180 := hb (x 4 11)
    have b4181 := hb (x 5 10)
    have b4182 := hb (x 6 9)
    have b4183 := hb (x 7 8)
    clear * - r4169 e4170 e4171 e4172 e4173 e4174 e4175 b4176 b4177 b4178 b4179 b4180 b4181 b4182 b4183 d4012 d4040 d4068 d4100 d4132 g1
    omega
  have d4184 : (x 2 5 && x 2 14).toNat = 0 := by
    have r4185 := hand1 (x 2 5) (x 2 14)
    have b4186 := hb (x 2 5)
    have b4187 := hb (x 2 5 && x 2 14)
    clear * - r4185 b4186 b4187 d4168
    omega
  have d4188 : (x 2 5 && x 2 11).toNat = 0 := by
    have r4189 := hand1 (x 2 5) (x 2 11)
    have b4190 := hb (x 2 5)
    have b4191 := hb (x 2 5 && x 2 11)
    clear * - r4189 b4190 b4191 d4168
    omega
  have d4192 : (x 2 5 && x 2 10).toNat = 0 := by
    have r4193 := hand1 (x 2 5) (x 2 10)
    have b4194 := hb (x 2 5)
    have b4195 := hb (x 2 5 && x 2 10)
    clear * - r4193 b4194 b4195 d4168
    omega
  have d4196 : (x 2 5 && x 2 9).toNat = 0 := by
    have r4197 := hand1 (x 2 5) (x 2 9)
    have b4198 := hb (x 2 5)
    have b4199 := hb (x 2 5 && x 2 9)
    clear * - r4197 b4198 b4199 d4168
    omega
  have d4200 : (x 1 6).toNat = 0 := by
    have r4201 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e4202 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e4203 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e4204 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e4205 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e4206 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e4207 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b4208 := hb (x 0 7)
    have b4209 := hb (x 1 6)
    have b4210 := hb (x 2 5)
    have b4211 := hb (x 3 4)
    have b4212 := hb (x 4 11)
    have b4213 := hb (x 5 10)
    have b4214 := hb (x 6 9)
    have b4215 := hb (x 7 8)
    clear * - r4201 e4202 e4203 e4204 e4205 e4206 e4207 b4208 b4209 b4210 b4211 b4212 b4213 b4214 b4215 d4012 d4040 d4068 d4100 d4132 d4168 g1
    omega
  have d4216 : (x 1 6 && x 1 12).toNat = 0 := by
    have r4217 := hand1 (x 1 6) (x 1 12)
    have b4218 := hb (x 1 6)
    have b4219 := hb (x 1 6 && x 1 12)
    clear * - r4217 b4218 b4219 d4200
    omega
  have d4220 : (x 1 6 && x 1 11).toNat = 0 := by
    have r4221 := hand1 (x 1 6) (x 1 11)
    have b4222 := hb (x 1 6)
    have b4223 := hb (x 1 6 && x 1 11)
    clear * - r4221 b4222 b4223 d4200
    omega
  have d4224 : (x 1 6 && x 1 10).toNat = 0 := by
    have r4225 := hand1 (x 1 6) (x 1 10)
    have b4226 := hb (x 1 6)
    have b4227 := hb (x 1 6 && x 1 10)
    clear * - r4225 b4226 b4227 d4200
    omega
  cases h4228 : x 0 1
  · have f4229 : (x 0 1).toNat = 0 := by rw [h4228]; rfl
    have d4230 : (x 0 14).toNat = 0 := by
      have r4231 : (x 0 1).toNat = (x 0 14).toNat := congrArg Bool.toNat (h114 0)
      have b4232 := hb (x 0 1)
      have b4233 := hb (x 0 14)
      clear * - r4231 b4232 b4233 f4229
      omega
    have d4234 : (x 0 13).toNat = 0 := by
      have r4235 : (x 0 13).toNat ≤ (x 0 1).toNat := himp _ _ (hp13 0)
      have b4236 := hb (x 0 1)
      have b4237 := hb (x 0 13)
      clear * - r4235 b4236 b4237 f4229
      omega
    have d4238 : (x 0 3 && x 0 13).toNat = 0 := by
      have r4239 := hand2 (x 0 3) (x 0 13)
      have b4240 := hb (x 0 13)
      have b4241 := hb (x 0 3 && x 0 13)
      clear * - r4239 b4240 b4241 d4234
      omega
    have d4242 : (x 0 7 && x 0 13).toNat = 0 := by
      have r4243 := hand2 (x 0 7) (x 0 13)
      have b4244 := hb (x 0 13)
      have b4245 := hb (x 0 7 && x 0 13)
      clear * - r4243 b4244 b4245 d4234
      omega
    have d4246 : (x 0 9).toNat = 0 := by
      have r4247 : (x 0 9).toNat ≤ (x 0 1).toNat := himp _ _ (hp9 0)
      have b4248 := hb (x 0 1)
      have b4249 := hb (x 0 9)
      clear * - r4247 b4248 b4249 f4229
      omega
    have d4250 : (x 0 2).toNat = 0 := by
      have r4251 : (x 0 2).toNat ≤ (x 0 14).toNat := himp _ _ (hp2 0)
      have b4252 := hb (x 0 2)
      have b4253 := hb (x 0 14)
      clear * - r4251 b4252 b4253 d4230
      omega
    have d4254 : (x 0 3).toNat = 0 := by
      have r4255 : (x 0 2).toNat = (x 0 3).toNat := congrArg Bool.toNat (h23 0)
      have b4256 := hb (x 0 2)
      have b4257 := hb (x 0 3)
      clear * - r4255 b4256 b4257 d4250
      omega
    have d4258 : (x 0 11).toNat = 0 := by
      have r4259 : (x 0 11).toNat ≤ (x 0 3).toNat := himp _ _ (hp11 0)
      have b4260 := hb (x 0 3)
      have b4261 := hb (x 0 11)
      clear * - r4259 b4260 b4261 d4254
      omega
    have d4262 : (x 0 7 && x 0 11).toNat = 0 := by
      have r4263 := hand2 (x 0 7) (x 0 11)
      have b4264 := hb (x 0 11)
      have b4265 := hb (x 0 7 && x 0 11)
      clear * - r4263 b4264 b4265 d4258
      omega
    have d4266 : (x 1 14).toNat = 1 := by
      have r4267 : (x 1 14).toNat + (x 0 1).toNat = 1 := by have q := hd14 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4268 := hb (x 0 1)
      have b4269 := hb (x 1 14)
      clear * - r4267 b4268 b4269 f4229
      omega
    have d4270 : (x 1 1).toNat = 1 := by
      have r4271 : (x 1 1).toNat = (x 1 14).toNat := congrArg Bool.toNat (h114 1)
      have b4272 := hb (x 1 1)
      have b4273 := hb (x 1 14)
      clear * - r4271 b4272 b4273 d4266
      omega
    have d4274 : (x 2 14).toNat = 0 := by
      have r4275 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4276 := hb (x 1 1)
      have b4277 := hb (x 2 14)
      clear * - r4275 b4276 b4277 d4270
      omega
    have d4278 : (x 2 1).toNat = 0 := by
      have r4279 : (x 2 1).toNat = (x 2 14).toNat := congrArg Bool.toNat (h114 2)
      have b4280 := hb (x 2 1)
      have b4281 := hb (x 2 14)
      clear * - r4279 b4280 b4281 d4274
      omega
    have d4282 : (x 2 1 && x 2 11).toNat = 0 := by
      have r4283 := hand1 (x 2 1) (x 2 11)
      have b4284 := hb (x 2 1)
      have b4285 := hb (x 2 1 && x 2 11)
      clear * - r4283 b4284 b4285 d4278
      omega
    have d4286 : (x 2 13).toNat = 0 := by
      have r4287 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
      have b4288 := hb (x 2 1)
      have b4289 := hb (x 2 13)
      clear * - r4287 b4288 b4289 d4278
      omega
    have d4290 : (x 2 7 && x 2 13).toNat = 0 := by
      have r4291 := hand2 (x 2 7) (x 2 13)
      have b4292 := hb (x 2 13)
      have b4293 := hb (x 2 7 && x 2 13)
      clear * - r4291 b4292 b4293 d4286
      omega
    have d4294 : (x 2 9 && x 2 13).toNat = 0 := by
      have r4295 := hand2 (x 2 9) (x 2 13)
      have b4296 := hb (x 2 13)
      have b4297 := hb (x 2 9 && x 2 13)
      clear * - r4295 b4296 b4297 d4286
      omega
    have d4298 : (x 2 9).toNat = 0 := by
      have r4299 : (x 2 9).toNat ≤ (x 2 1).toNat := himp _ _ (hp9 2)
      have b4300 := hb (x 2 1)
      have b4301 := hb (x 2 9)
      clear * - r4299 b4300 b4301 d4278
      omega
    have d4302 : (x 3 14).toNat = 1 := by
      have r4303 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4304 := hb (x 2 1)
      have b4305 := hb (x 3 14)
      clear * - r4303 b4304 b4305 d4278
      omega
    have d4306 : (x 3 1).toNat = 1 := by
      have r4307 : (x 3 1).toNat = (x 3 14).toNat := congrArg Bool.toNat (h114 3)
      have b4308 := hb (x 3 1)
      have b4309 := hb (x 3 14)
      clear * - r4307 b4308 b4309 d4302
      omega
    have d4310 : (x 4 14).toNat = 0 := by
      have r4311 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4312 := hb (x 3 1)
      have b4313 := hb (x 4 14)
      clear * - r4311 b4312 b4313 d4306
      omega
    have d4314 : (x 4 1).toNat = 0 := by
      have r4315 : (x 4 1).toNat = (x 4 14).toNat := congrArg Bool.toNat (h114 4)
      have b4316 := hb (x 4 1)
      have b4317 := hb (x 4 14)
      clear * - r4315 b4316 b4317 d4310
      omega
    have d4318 : (x 4 13).toNat = 0 := by
      have r4319 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
      have b4320 := hb (x 4 1)
      have b4321 := hb (x 4 13)
      clear * - r4319 b4320 b4321 d4314
      omega
    have d4322 : (x 4 5).toNat = 0 := by
      have r4323 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
      have b4324 := hb (x 4 5)
      have b4325 := hb (x 4 13)
      clear * - r4323 b4324 b4325 d4318
      omega
    have d4326 : (x 4 9).toNat = 0 := by
      have r4327 : (x 4 9).toNat ≤ (x 4 1).toNat := himp _ _ (hp9 4)
      have b4328 := hb (x 4 1)
      have b4329 := hb (x 4 9)
      clear * - r4327 b4328 b4329 d4314
      omega
    have d4330 : (x 4 3 && x 4 9).toNat = 0 := by
      have r4331 := hand2 (x 4 3) (x 4 9)
      have b4332 := hb (x 4 9)
      have b4333 := hb (x 4 3 && x 4 9)
      clear * - r4331 b4332 b4333 d4326
      omega
    have d4334 : (x 5 14).toNat = 1 := by
      have r4335 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4336 := hb (x 4 1)
      have b4337 := hb (x 5 14)
      clear * - r4335 b4336 b4337 d4314
      omega
    have d4338 : (x 5 1).toNat = 1 := by
      have r4339 : (x 5 1).toNat = (x 5 14).toNat := congrArg Bool.toNat (h114 5)
      have b4340 := hb (x 5 1)
      have b4341 := hb (x 5 14)
      clear * - r4339 b4340 b4341 d4334
      omega
    have d4342 : (x 6 14).toNat = 0 := by
      have r4343 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4344 := hb (x 5 1)
      have b4345 := hb (x 6 14)
      clear * - r4343 b4344 b4345 d4338
      omega
    have d4346 : (x 6 1).toNat = 0 := by
      have r4347 : (x 6 1).toNat = (x 6 14).toNat := congrArg Bool.toNat (h114 6)
      have b4348 := hb (x 6 1)
      have b4349 := hb (x 6 14)
      clear * - r4347 b4348 b4349 d4342
      omega
    have d4350 : (x 6 1 && x 6 10).toNat = 0 := by
      have r4351 := hand1 (x 6 1) (x 6 10)
      have b4352 := hb (x 6 1)
      have b4353 := hb (x 6 1 && x 6 10)
      clear * - r4351 b4352 b4353 d4346
      omega
    have d4354 : (x 6 1 && x 6 7).toNat = 0 := by
      have r4355 := hand1 (x 6 1) (x 6 7)
      have b4356 := hb (x 6 1)
      have b4357 := hb (x 6 1 && x 6 7)
      clear * - r4355 b4356 b4357 d4346
      omega
    have d4358 : (x 6 13).toNat = 0 := by
      have r4359 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
      have b4360 := hb (x 6 1)
      have b4361 := hb (x 6 13)
      clear * - r4359 b4360 b4361 d4346
      omega
    have d4362 : (x 6 3 && x 6 13).toNat = 0 := by
      have r4363 := hand2 (x 6 3) (x 6 13)
      have b4364 := hb (x 6 13)
      have b4365 := hb (x 6 3 && x 6 13)
      clear * - r4363 b4364 b4365 d4358
      omega
    have d4366 : (x 6 5).toNat = 0 := by
      have r4367 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
      have b4368 := hb (x 6 5)
      have b4369 := hb (x 6 13)
      clear * - r4367 b4368 b4369 d4358
      omega
    have d4370 : (x 7 14).toNat = 1 := by
      have r4371 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4372 := hb (x 6 1)
      have b4373 := hb (x 7 14)
      clear * - r4371 b4372 b4373 d4346
      omega
    have d4374 : (x 7 1).toNat = 1 := by
      have r4375 : (x 7 1).toNat = (x 7 14).toNat := congrArg Bool.toNat (h114 7)
      have b4376 := hb (x 7 1)
      have b4377 := hb (x 7 14)
      clear * - r4375 b4376 b4377 d4370
      omega
    have d4378 : (x 8 14).toNat = 0 := by
      have r4379 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4380 := hb (x 7 1)
      have b4381 := hb (x 8 14)
      clear * - r4379 b4380 b4381 d4374
      omega
    have d4382 : (x 8 1).toNat = 0 := by
      have r4383 : (x 8 1).toNat = (x 8 14).toNat := congrArg Bool.toNat (h114 8)
      have b4384 := hb (x 8 1)
      have b4385 := hb (x 8 14)
      clear * - r4383 b4384 b4385 d4378
      omega
    have d4386 : (x 8 1 && x 8 11).toNat = 0 := by
      have r4387 := hand1 (x 8 1) (x 8 11)
      have b4388 := hb (x 8 1)
      have b4389 := hb (x 8 1 && x 8 11)
      clear * - r4387 b4388 b4389 d4382
      omega
    have d4390 : (x 8 1 && x 8 7).toNat = 0 := by
      have r4391 := hand1 (x 8 1) (x 8 7)
      have b4392 := hb (x 8 1)
      have b4393 := hb (x 8 1 && x 8 7)
      clear * - r4391 b4392 b4393 d4382
      omega
    have d4394 : (x 8 13).toNat = 0 := by
      have r4395 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
      have b4396 := hb (x 8 1)
      have b4397 := hb (x 8 13)
      clear * - r4395 b4396 b4397 d4382
      omega
    have d4398 : (x 8 5).toNat = 0 := by
      have r4399 : (x 8 5).toNat ≤ (x 8 13).toNat := himp _ _ (hp5 8)
      have b4400 := hb (x 8 5)
      have b4401 := hb (x 8 13)
      clear * - r4399 b4400 b4401 d4394
      omega
    have d4402 : (x 9 14).toNat = 1 := by
      have r4403 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4404 := hb (x 8 1)
      have b4405 := hb (x 9 14)
      clear * - r4403 b4404 b4405 d4382
      omega
    have d4406 : (x 9 1).toNat = 1 := by
      have r4407 : (x 9 1).toNat = (x 9 14).toNat := congrArg Bool.toNat (h114 9)
      have b4408 := hb (x 9 1)
      have b4409 := hb (x 9 14)
      clear * - r4407 b4408 b4409 d4402
      omega
    have d4410 : (x 10 14).toNat = 0 := by
      have r4411 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4412 := hb (x 9 1)
      have b4413 := hb (x 10 14)
      clear * - r4411 b4412 b4413 d4406
      omega
    have d4414 : (x 10 1).toNat = 0 := by
      have r4415 : (x 10 1).toNat = (x 10 14).toNat := congrArg Bool.toNat (h114 10)
      have b4416 := hb (x 10 1)
      have b4417 := hb (x 10 14)
      clear * - r4415 b4416 b4417 d4410
      omega
    have d4418 : (x 10 13).toNat = 0 := by
      have r4419 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
      have b4420 := hb (x 10 1)
      have b4421 := hb (x 10 13)
      clear * - r4419 b4420 b4421 d4414
      omega
    have d4422 : (x 10 3 && x 10 13).toNat = 0 := by
      have r4423 := hand2 (x 10 3) (x 10 13)
      have b4424 := hb (x 10 13)
      have b4425 := hb (x 10 3 && x 10 13)
      clear * - r4423 b4424 b4425 d4418
      omega
    have d4426 : (x 10 5).toNat = 0 := by
      have r4427 : (x 10 5).toNat ≤ (x 10 13).toNat := himp _ _ (hp5 10)
      have b4428 := hb (x 10 5)
      have b4429 := hb (x 10 13)
      clear * - r4427 b4428 b4429 d4418
      omega
    have d4430 : (x 10 9).toNat = 0 := by
      have r4431 : (x 10 9).toNat ≤ (x 10 1).toNat := himp _ _ (hp9 10)
      have b4432 := hb (x 10 1)
      have b4433 := hb (x 10 9)
      clear * - r4431 b4432 b4433 d4414
      omega
    have d4434 : (x 10 2).toNat = 0 := by
      have r4435 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
      have b4436 := hb (x 10 2)
      have b4437 := hb (x 10 14)
      clear * - r4435 b4436 b4437 d4410
      omega
    have d4438 : (x 10 3).toNat = 0 := by
      have r4439 : (x 10 2).toNat = (x 10 3).toNat := congrArg Bool.toNat (h23 10)
      have b4440 := hb (x 10 2)
      have b4441 := hb (x 10 3)
      clear * - r4439 b4440 b4441 d4434
      omega
    have d4442 : (x 8 2).toNat = 0 := by
      have r4443 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
      have b4444 := hb (x 8 2)
      have b4445 := hb (x 8 14)
      clear * - r4443 b4444 b4445 d4378
      omega
    have d4446 : (x 8 3).toNat = 0 := by
      have r4447 : (x 8 2).toNat = (x 8 3).toNat := congrArg Bool.toNat (h23 8)
      have b4448 := hb (x 8 2)
      have b4449 := hb (x 8 3)
      clear * - r4447 b4448 b4449 d4442
      omega
    have d4450 : (x 8 3 && x 8 7).toNat = 0 := by
      have r4451 := hand1 (x 8 3) (x 8 7)
      have b4452 := hb (x 8 3)
      have b4453 := hb (x 8 3 && x 8 7)
      clear * - r4451 b4452 b4453 d4446
      omega
    have d4454 : (x 8 11).toNat = 0 := by
      have r4455 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
      have b4456 := hb (x 8 3)
      have b4457 := hb (x 8 11)
      clear * - r4455 b4456 b4457 d4446
      omega
    have d4458 : (x 6 2).toNat = 0 := by
      have r4459 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
      have b4460 := hb (x 6 2)
      have b4461 := hb (x 6 14)
      clear * - r4459 b4460 b4461 d4342
      omega
    have d4462 : (x 6 3).toNat = 0 := by
      have r4463 : (x 6 2).toNat = (x 6 3).toNat := congrArg Bool.toNat (h23 6)
      have b4464 := hb (x 6 2)
      have b4465 := hb (x 6 3)
      clear * - r4463 b4464 b4465 d4458
      omega
    have d4466 : (x 6 10).toNat = 0 := by
      have r4467 : (x 6 10).toNat ≤ (x 6 2).toNat := himp _ _ (hp10 6)
      have b4468 := hb (x 6 2)
      have b4469 := hb (x 6 10)
      clear * - r4467 b4468 b4469 d4458
      omega
    have d4470 : (x 4 2).toNat = 0 := by
      have r4471 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
      have b4472 := hb (x 4 2)
      have b4473 := hb (x 4 14)
      clear * - r4471 b4472 b4473 d4310
      omega
    have d4474 : (x 4 3).toNat = 0 := by
      have r4475 : (x 4 2).toNat = (x 4 3).toNat := congrArg Bool.toNat (h23 4)
      have b4476 := hb (x 4 2)
      have b4477 := hb (x 4 3)
      clear * - r4475 b4476 b4477 d4470
      omega
    have d4478 : (x 4 3 && x 4 12).toNat = 0 := by
      have r4479 := hand1 (x 4 3) (x 4 12)
      have b4480 := hb (x 4 3)
      have b4481 := hb (x 4 3 && x 4 12)
      clear * - r4479 b4480 b4481 d4474
      omega
    have d4482 : (x 4 3 && x 4 7).toNat = 0 := by
      have r4483 := hand1 (x 4 3) (x 4 7)
      have b4484 := hb (x 4 3)
      have b4485 := hb (x 4 3 && x 4 7)
      clear * - r4483 b4484 b4485 d4474
      omega
    have d4486 : (x 2 6).toNat = 0 := by
      have r4487 : (x 2 6).toNat ≤ (x 2 14).toNat := himp _ _ (hp6 2)
      have b4488 := hb (x 2 6)
      have b4489 := hb (x 2 14)
      clear * - r4487 b4488 b4489 d4274
      omega
    have d4490 : (x 2 2).toNat = 0 := by
      have r4491 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
      have b4492 := hb (x 2 2)
      have b4493 := hb (x 2 14)
      clear * - r4491 b4492 b4493 d4274
      omega
    have d4494 : (x 2 3).toNat = 0 := by
      have r4495 : (x 2 2).toNat = (x 2 3).toNat := congrArg Bool.toNat (h23 2)
      have b4496 := hb (x 2 2)
      have b4497 := hb (x 2 3)
      clear * - r4495 b4496 b4497 d4490
      omega
    have d4498 : (x 2 11).toNat = 0 := by
      have r4499 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
      have b4500 := hb (x 2 3)
      have b4501 := hb (x 2 11)
      clear * - r4499 b4500 b4501 d4494
      omega
    have d4502 : (x (-1) 1).toNat = 1 := by
      have r4503 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4504 := hb (x (-1) 1)
      have b4505 := hb (x 0 14)
      clear * - r4503 b4504 b4505 d4230
      omega
    have d4506 : (x (-1) 14).toNat = 1 := by
      have r4507 : (x (-1) 1).toNat = (x (-1) 14).toNat := congrArg Bool.toNat (h114 (-1))
      have b4508 := hb (x (-1) 1)
      have b4509 := hb (x (-1) 14)
      clear * - r4507 b4508 b4509 d4502
      omega
    have d4510 : (x (-2) 1).toNat = 0 := by
      have r4511 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4512 := hb (x (-2) 1)
      have b4513 := hb (x (-1) 14)
      clear * - r4511 b4512 b4513 d4506
      omega
    have d4514 : (x (-2) 14).toNat = 0 := by
      have r4515 : (x (-2) 1).toNat = (x (-2) 14).toNat := congrArg Bool.toNat (h114 (-2))
      have b4516 := hb (x (-2) 1)
      have b4517 := hb (x (-2) 14)
      clear * - r4515 b4516 b4517 d4510
      omega
    have d4518 : (x (-2) 2).toNat = 0 := by
      have r4519 : (x (-2) 2).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp2 (-2))
      have b4520 := hb (x (-2) 2)
      have b4521 := hb (x (-2) 14)
      clear * - r4519 b4520 b4521 d4514
      omega
    have d4522 : (x (-2) 2 && x (-2) 11).toNat = 0 := by
      have r4523 := hand1 (x (-2) 2) (x (-2) 11)
      have b4524 := hb (x (-2) 2)
      have b4525 := hb (x (-2) 2 && x (-2) 11)
      clear * - r4523 b4524 b4525 d4518
      omega
    have d4526 : (x (-2) 3).toNat = 0 := by
      have r4527 : (x (-2) 2).toNat = (x (-2) 3).toNat := congrArg Bool.toNat (h23 (-2))
      have b4528 := hb (x (-2) 2)
      have b4529 := hb (x (-2) 3)
      clear * - r4527 b4528 b4529 d4518
      omega
    have d4530 : (x (-2) 11).toNat = 0 := by
      have r4531 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
      have b4532 := hb (x (-2) 3)
      have b4533 := hb (x (-2) 11)
      clear * - r4531 b4532 b4533 d4526
      omega
    have d4534 : (x (-2) 10).toNat = 0 := by
      have r4535 : (x (-2) 10).toNat ≤ (x (-2) 2).toNat := himp _ _ (hp10 (-2))
      have b4536 := hb (x (-2) 2)
      have b4537 := hb (x (-2) 10)
      clear * - r4535 b4536 b4537 d4518
      omega
    have d4538 : (x (-2) 13).toNat = 0 := by
      have r4539 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
      have b4540 := hb (x (-2) 1)
      have b4541 := hb (x (-2) 13)
      clear * - r4539 b4540 b4541 d4510
      omega
    have d4542 : (x (-2) 9 && x (-2) 13).toNat = 0 := by
      have r4543 := hand2 (x (-2) 9) (x (-2) 13)
      have b4544 := hb (x (-2) 13)
      have b4545 := hb (x (-2) 9 && x (-2) 13)
      clear * - r4543 b4544 b4545 d4538
      omega
    have d4546 : (x (-2) 5).toNat = 0 := by
      have r4547 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
      have b4548 := hb (x (-2) 5)
      have b4549 := hb (x (-2) 13)
      clear * - r4547 b4548 b4549 d4538
      omega
    have d4550 : (x (-2) 9).toNat = 0 := by
      have r4551 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
      have b4552 := hb (x (-2) 1)
      have b4553 := hb (x (-2) 9)
      clear * - r4551 b4552 b4553 d4510
      omega
    have d4554 : (x (-3) 1).toNat = 1 := by
      have r4555 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4556 := hb (x (-3) 1)
      have b4557 := hb (x (-2) 14)
      clear * - r4555 b4556 b4557 d4514
      omega
    have d4558 : (x (-3) 14).toNat = 1 := by
      have r4559 : (x (-3) 1).toNat = (x (-3) 14).toNat := congrArg Bool.toNat (h114 (-3))
      have b4560 := hb (x (-3) 1)
      have b4561 := hb (x (-3) 14)
      clear * - r4559 b4560 b4561 d4554
      omega
    have d4562 : (x (-4) 1).toNat = 0 := by
      have r4563 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4564 := hb (x (-4) 1)
      have b4565 := hb (x (-3) 14)
      clear * - r4563 b4564 b4565 d4558
      omega
    have d4566 : (x (-4) 14).toNat = 0 := by
      have r4567 : (x (-4) 1).toNat = (x (-4) 14).toNat := congrArg Bool.toNat (h114 (-4))
      have b4568 := hb (x (-4) 1)
      have b4569 := hb (x (-4) 14)
      clear * - r4567 b4568 b4569 d4562
      omega
    have d4570 : (x (-4) 2).toNat = 0 := by
      have r4571 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
      have b4572 := hb (x (-4) 2)
      have b4573 := hb (x (-4) 14)
      clear * - r4571 b4572 b4573 d4566
      omega
    have d4574 : (x (-4) 3).toNat = 0 := by
      have r4575 : (x (-4) 2).toNat = (x (-4) 3).toNat := congrArg Bool.toNat (h23 (-4))
      have b4576 := hb (x (-4) 2)
      have b4577 := hb (x (-4) 3)
      clear * - r4575 b4576 b4577 d4570
      omega
    have d4578 : (x (-4) 11).toNat = 0 := by
      have r4579 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
      have b4580 := hb (x (-4) 3)
      have b4581 := hb (x (-4) 11)
      clear * - r4579 b4580 b4581 d4574
      omega
    have d4582 : (x (-4) 13).toNat = 0 := by
      have r4583 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
      have b4584 := hb (x (-4) 1)
      have b4585 := hb (x (-4) 13)
      clear * - r4583 b4584 b4585 d4562
      omega
    have d4586 : (x (-4) 4 && x (-4) 13).toNat = 0 := by
      have r4587 := hand2 (x (-4) 4) (x (-4) 13)
      have b4588 := hb (x (-4) 13)
      have b4589 := hb (x (-4) 4 && x (-4) 13)
      clear * - r4587 b4588 b4589 d4582
      omega
    have d4590 : (x (-5) 1).toNat = 1 := by
      have r4591 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4592 := hb (x (-5) 1)
      have b4593 := hb (x (-4) 14)
      clear * - r4591 b4592 b4593 d4566
      omega
    have d4594 : (x (-5) 14).toNat = 1 := by
      have r4595 : (x (-5) 1).toNat = (x (-5) 14).toNat := congrArg Bool.toNat (h114 (-5))
      have b4596 := hb (x (-5) 1)
      have b4597 := hb (x (-5) 14)
      clear * - r4595 b4596 b4597 d4590
      omega
    have d4598 : (x (-6) 1).toNat = 0 := by
      have r4599 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4600 := hb (x (-6) 1)
      have b4601 := hb (x (-5) 14)
      clear * - r4599 b4600 b4601 d4594
      omega
    have d4602 : (x (-6) 14).toNat = 0 := by
      have r4603 : (x (-6) 1).toNat = (x (-6) 14).toNat := congrArg Bool.toNat (h114 (-6))
      have b4604 := hb (x (-6) 1)
      have b4605 := hb (x (-6) 14)
      clear * - r4603 b4604 b4605 d4598
      omega
    have d4606 : (x (-6) 6).toNat = 0 := by
      have r4607 : (x (-6) 6).toNat ≤ (x (-6) 14).toNat := himp _ _ (hp6 (-6))
      have b4608 := hb (x (-6) 6)
      have b4609 := hb (x (-6) 14)
      clear * - r4607 b4608 b4609 d4602
      omega
    have d4610 : (x (-6) 2).toNat = 0 := by
      have r4611 : (x (-6) 2).toNat ≤ (x (-6) 14).toNat := himp _ _ (hp2 (-6))
      have b4612 := hb (x (-6) 2)
      have b4613 := hb (x (-6) 14)
      clear * - r4611 b4612 b4613 d4602
      omega
    have d4614 : (x (-6) 13).toNat = 0 := by
      have r4615 : (x (-6) 13).toNat ≤ (x (-6) 1).toNat := himp _ _ (hp13 (-6))
      have b4616 := hb (x (-6) 1)
      have b4617 := hb (x (-6) 13)
      clear * - r4615 b4616 b4617 d4598
      omega
    have d4618 : (x (-7) 1).toNat = 1 := by
      have r4619 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4620 := hb (x (-7) 1)
      have b4621 := hb (x (-6) 14)
      clear * - r4619 b4620 b4621 d4602
      omega
    have d4622 : (x (-7) 14).toNat = 1 := by
      have r4623 : (x (-7) 1).toNat = (x (-7) 14).toNat := congrArg Bool.toNat (h114 (-7))
      have b4624 := hb (x (-7) 1)
      have b4625 := hb (x (-7) 14)
      clear * - r4623 b4624 b4625 d4618
      omega
    have d4626 : (x (-8) 1).toNat = 0 := by
      have r4627 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4628 := hb (x (-8) 1)
      have b4629 := hb (x (-7) 14)
      clear * - r4627 b4628 b4629 d4622
      omega
    have d4630 : (x (-8) 14).toNat = 0 := by
      have r4631 : (x (-8) 1).toNat = (x (-8) 14).toNat := congrArg Bool.toNat (h114 (-8))
      have b4632 := hb (x (-8) 1)
      have b4633 := hb (x (-8) 14)
      clear * - r4631 b4632 b4633 d4626
      omega
    have d4634 : (x (-8) 2).toNat = 0 := by
      have r4635 : (x (-8) 2).toNat ≤ (x (-8) 14).toNat := himp _ _ (hp2 (-8))
      have b4636 := hb (x (-8) 2)
      have b4637 := hb (x (-8) 14)
      clear * - r4635 b4636 b4637 d4630
      omega
    have d4638 : (x (-8) 3).toNat = 0 := by
      have r4639 : (x (-8) 2).toNat = (x (-8) 3).toNat := congrArg Bool.toNat (h23 (-8))
      have b4640 := hb (x (-8) 2)
      have b4641 := hb (x (-8) 3)
      clear * - r4639 b4640 b4641 d4634
      omega
    have r4642 : (x 6 1).toNat + (x 5 2).toNat + (x 4 3).toNat + (x 3 4).toNat + (x 2 5).toNat + (x 1 6).toNat + (x 0 7).toNat + (x (-1) 8).toNat + (x (-2) 9).toNat + (x (-3) 10).toNat + (x (-4) 11).toNat + (x (-5) 12).toNat + (x (-6) 13).toNat + (x (-7) 14).toNat = 3 := by have q := hcount 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r4643 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r4644 : (x 8 1).toNat + (x 7 2).toNat + (x 6 3).toNat + (x 5 4).toNat + (x 4 5).toNat + (x 3 6).toNat + (x 2 7).toNat + (x 1 8).toNat + (x 0 9).toNat + (x (-1) 10).toNat + (x (-2) 11).toNat + (x (-3) 12).toNat + (x (-4) 13).toNat + (x (-5) 14).toNat = 3 := by have q := hcount 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r4645 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r4646 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r4647 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e4648 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e4649 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e4650 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e4651 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e4652 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e4653 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have r4654 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e4655 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e4656 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e4657 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e4658 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e4659 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e4660 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have r4661 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e4662 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e4663 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e4664 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e4665 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e4666 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e4667 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have r4668 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e4669 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
    have e4670 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
    have e4671 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
    have e4672 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
    have e4673 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
    have e4674 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
    have r4675 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e4676 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
    have e4677 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
    have r4678 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e4679 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e4680 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have r4681 : (x (-7) 2).toNat = (x (-7) 3).toNat := congrArg Bool.toNat (h23 (-7))
    have r4682 : (x 5 2).toNat = (x 5 3).toNat := congrArg Bool.toNat (h23 5)
    have r4683 : 1 ≤ (x 7 4).toNat + (x 6 1 && x 6 5).toNat + (x 5 2 && x 5 6).toNat + (x 4 3 && x 4 7).toNat + (x 3 4 && x 3 8).toNat + (x 2 5 && x 2 9).toNat + (x 1 6 && x 1 10).toNat + (x 0 7 && x 0 11).toNat + (x (-1) 8 && x (-1) 12).toNat + (x (-2) 9 && x (-2) 13).toNat + (x (-3) 10 && x (-3) 14).toNat + (x (-4) 11).toNat := by have q := hcov4 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e4684 : (x 6 1 && x 6 5).toNat = (x 6 5).toNat := handr _ _ (fun h => hp13 6 (hp5 6 (h)))
    have e4685 : (x (-3) 10 && x (-3) 14).toNat = (x (-3) 10).toNat := handl _ _ (fun h => hp2 (-3) (hp10 (-3) (h)))
    have r4686 : 1 ≤ (x 11 4).toNat + (x 10 1 && x 10 5).toNat + (x 9 2 && x 9 6).toNat + (x 8 3 && x 8 7).toNat + (x 7 4 && x 7 8).toNat + (x 6 5 && x 6 9).toNat + (x 5 6 && x 5 10).toNat + (x 4 7 && x 4 11).toNat + (x 3 8 && x 3 12).toNat + (x 2 9 && x 2 13).toNat + (x 1 10 && x 1 14).toNat + (x 0 11).toNat := by have q := hcov4 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e4687 : (x 10 1 && x 10 5).toNat = (x 10 5).toNat := handr _ _ (fun h => hp13 10 (hp5 10 (h)))
    have e4688 : (x 1 10 && x 1 14).toNat = (x 1 10).toNat := handl _ _ (fun h => hp2 1 (hp10 1 (h)))
    have r4689 : 1 ≤ (x 7 6).toNat + (x 6 1 && x 6 7).toNat + (x 5 2 && x 5 8).toNat + (x 4 3 && x 4 9).toNat + (x 3 4 && x 3 10).toNat + (x 2 5 && x 2 11).toNat + (x 1 6 && x 1 12).toNat + (x 0 7 && x 0 13).toNat + (x (-1) 8 && x (-1) 14).toNat + (x (-2) 9).toNat := by have q := hcov6 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r4690 : 1 ≤ (x 9 6).toNat + (x 8 1 && x 8 7).toNat + (x 7 2 && x 7 8).toNat + (x 6 3 && x 6 9).toNat + (x 5 4 && x 5 10).toNat + (x 4 5 && x 4 11).toNat + (x 3 6 && x 3 12).toNat + (x 2 7 && x 2 13).toNat + (x 1 8 && x 1 14).toNat + (x 0 9).toNat := by have q := hcov6 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r4691 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r4692 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r4693 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r4694 : 1 ≤ (x 9 10).toNat + (x 8 1 && x 8 11).toNat + (x 7 2 && x 7 12).toNat + (x 6 3 && x 6 13).toNat + (x 5 4 && x 5 14).toNat + (x 4 5).toNat := by have q := hcov10 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r4695 : 1 ≤ (x 13 10).toNat + (x 12 1 && x 12 11).toNat + (x 11 2 && x 11 12).toNat + (x 10 3 && x 10 13).toNat + (x 9 4 && x 9 14).toNat + (x 8 5).toNat := by have q := hcov10 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r4696 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
    have r4697 := hand2 (x 5 2) (x 5 6)
    have r4698 := hand1 (x (-1) 8) (x (-1) 12)
    have r4699 := hand1 (x 9 2) (x 9 6)
    have r4700 := hand1 (x 3 8) (x 3 12)
    have r4701 := hand2 (x 5 2) (x 5 8)
    have r4702 := hand1 (x (-1) 8) (x (-1) 14)
    have r4703 := hand1 (x 3 6) (x 3 12)
    have r4704 := hand1 (x 1 8) (x 1 14)
    have r4705 := hand2 (x (-1) 1) (x (-1) 10)
    have r4706 := hand2 (x (-3) 3) (x (-3) 12)
    have r4707 := hand1 (x (-5) 5) (x (-5) 14)
    have r4708 := hand2 (x 5 2) (x 5 11)
    have r4709 := hand2 (x 1 2) (x 1 12)
    have r4710 := hand1 (x (-1) 4) (x (-1) 14)
    have r4711 := hand1 (x 7 2) (x 7 12)
    have r4712 := hand1 (x 5 4) (x 5 14)
    have r4713 := hand1 (x 12 1) (x 12 11)
    have r4714 := hand1 (x 11 2) (x 11 12)
    have r4715 := hand1 (x 9 4) (x 9 14)
    have b4716 := hb (x (-8) 3)
    have b4717 := hb (x (-7) 2)
    have b4718 := hb (x (-7) 3)
    have b4719 := hb (x (-7) 7)
    have b4720 := hb (x (-7) 14)
    have b4721 := hb (x (-6) 2)
    have b4722 := hb (x (-6) 6)
    have b4723 := hb (x (-6) 13)
    have b4724 := hb (x (-6) 14)
    have b4725 := hb (x (-5) 5)
    have b4726 := hb (x (-5) 12)
    have b4727 := hb (x (-5) 13)
    have b4728 := hb (x (-5) 14)
    have b4729 := hb (x (-4) 4)
    have b4730 := hb (x (-4) 11)
    have b4731 := hb (x (-4) 12)
    have b4732 := hb (x (-4) 13)
    have b4733 := hb (x (-3) 10)
    have b4734 := hb (x (-3) 11)
    have b4735 := hb (x (-3) 12)
    have b4736 := hb (x (-3) 14)
    have b4737 := hb (x (-2) 5)
    have b4738 := hb (x (-2) 9)
    have b4739 := hb (x (-2) 10)
    have b4740 := hb (x (-2) 11)
    have b4741 := hb (x (-2) 13)
    have b4742 := hb (x (-1) 4)
    have b4743 := hb (x (-1) 8)
    have b4744 := hb (x (-1) 9)
    have b4745 := hb (x (-1) 10)
    have b4746 := hb (x (-1) 12)
    have b4747 := hb (x (-1) 14)
    have b4748 := hb (x 0 7)
    have b4749 := hb (x 0 8)
    have b4750 := hb (x 0 9)
    have b4751 := hb (x 0 11)
    have b4752 := hb (x 0 13)
    have b4753 := hb (x 1 6)
    have b4754 := hb (x 1 7)
    have b4755 := hb (x 1 8)
    have b4756 := hb (x 1 10)
    have b4757 := hb (x 1 12)
    have b4758 := hb (x 2 5)
    have b4759 := hb (x 2 6)
    have b4760 := hb (x 2 7)
    have b4761 := hb (x 2 9)
    have b4762 := hb (x 2 11)
    have b4763 := hb (x 3 4)
    have b4764 := hb (x 3 5)
    have b4765 := hb (x 3 6)
    have b4766 := hb (x 3 8)
    have b4767 := hb (x 3 10)
    have b4768 := hb (x 4 3)
    have b4769 := hb (x 4 4)
    have b4770 := hb (x 4 5)
    have b4771 := hb (x 4 7)
    have b4772 := hb (x 4 9)
    have b4773 := hb (x 5 2)
    have b4774 := hb (x 5 3)
    have b4775 := hb (x 5 4)
    have b4776 := hb (x 5 6)
    have b4777 := hb (x 5 8)
    have b4778 := hb (x 5 11)
    have b4779 := hb (x 6 1)
    have b4780 := hb (x 6 2)
    have b4781 := hb (x 6 3)
    have b4782 := hb (x 6 5)
    have b4783 := hb (x 6 7)
    have b4784 := hb (x 6 10)
    have b4785 := hb (x 7 1)
    have b4786 := hb (x 7 2)
    have b4787 := hb (x 7 4)
    have b4788 := hb (x 7 6)
    have b4789 := hb (x 7 9)
    have b4790 := hb (x 8 1)
    have b4791 := hb (x 8 3)
    have b4792 := hb (x 8 5)
    have b4793 := hb (x 8 7)
    have b4794 := hb (x 8 8)
    have b4795 := hb (x 8 11)
    have b4796 := hb (x 9 2)
    have b4797 := hb (x 9 4)
    have b4798 := hb (x 9 6)
    have b4799 := hb (x 9 10)
    have b4800 := hb (x 10 1)
    have b4801 := hb (x 10 3)
    have b4802 := hb (x 10 5)
    have b4803 := hb (x 10 9)
    have b4804 := hb (x 11 2)
    have b4805 := hb (x 11 4)
    have b4806 := hb (x 11 8)
    have b4807 := hb (x 12 1)
    have b4808 := hb (x 12 11)
    have b4809 := hb (x 13 10)
    have b4810 := hb (x 14 9)
    have b4811 := hb (x 15 8)
    have b4812 := hb (x 5 2 && x 5 6)
    have b4813 := hb (x 4 3 && x 4 7)
    have b4814 := hb (x 3 4 && x 3 8)
    have b4815 := hb (x 2 5 && x 2 9)
    have b4816 := hb (x 1 6 && x 1 10)
    have b4817 := hb (x 0 7 && x 0 11)
    have b4818 := hb (x (-1) 8 && x (-1) 12)
    have b4819 := hb (x (-2) 9 && x (-2) 13)
    have b4820 := hb (x 9 2 && x 9 6)
    have b4821 := hb (x 8 3 && x 8 7)
    have b4822 := hb (x 7 4 && x 7 8)
    have b4823 := hb (x 6 5 && x 6 9)
    have b4824 := hb (x 5 6 && x 5 10)
    have b4825 := hb (x 4 7 && x 4 11)
    have b4826 := hb (x 3 8 && x 3 12)
    have b4827 := hb (x 2 9 && x 2 13)
    have b4828 := hb (x 6 1 && x 6 7)
    have b4829 := hb (x 5 2 && x 5 8)
    have b4830 := hb (x 4 3 && x 4 9)
    have b4831 := hb (x 3 4 && x 3 10)
    have b4832 := hb (x 2 5 && x 2 11)
    have b4833 := hb (x 1 6 && x 1 12)
    have b4834 := hb (x 0 7 && x 0 13)
    have b4835 := hb (x (-1) 8 && x (-1) 14)
    have b4836 := hb (x 8 1 && x 8 7)
    have b4837 := hb (x 7 2 && x 7 8)
    have b4838 := hb (x 6 3 && x 6 9)
    have b4839 := hb (x 5 4 && x 5 10)
    have b4840 := hb (x 4 5 && x 4 11)
    have b4841 := hb (x 3 6 && x 3 12)
    have b4842 := hb (x 2 7 && x 2 13)
    have b4843 := hb (x 1 8 && x 1 14)
    have b4844 := hb (x (-1) 1 && x (-1) 10)
    have b4845 := hb (x (-2) 2 && x (-2) 11)
    have b4846 := hb (x (-3) 3 && x (-3) 12)
    have b4847 := hb (x (-4) 4 && x (-4) 13)
    have b4848 := hb (x (-5) 5 && x (-5) 14)
    have b4849 := hb (x 6 1 && x 6 10)
    have b4850 := hb (x 5 2 && x 5 11)
    have b4851 := hb (x 4 3 && x 4 12)
    have b4852 := hb (x 3 4 && x 3 13)
    have b4853 := hb (x 2 5 && x 2 14)
    have b4854 := hb (x 2 1 && x 2 11)
    have b4855 := hb (x 1 2 && x 1 12)
    have b4856 := hb (x 0 3 && x 0 13)
    have b4857 := hb (x (-1) 4 && x (-1) 14)
    have b4858 := hb (x 8 1 && x 8 11)
    have b4859 := hb (x 7 2 && x 7 12)
    have b4860 := hb (x 6 3 && x 6 13)
    have b4861 := hb (x 5 4 && x 5 14)
    have b4862 := hb (x 12 1 && x 12 11)
    have b4863 := hb (x 11 2 && x 11 12)
    have b4864 := hb (x 10 3 && x 10 13)
    have b4865 := hb (x 9 4 && x 9 14)
    linarith only [r4642, r4643, r4644, r4645, r4646, r4647, e4648, e4649, e4650, e4651, e4652, e4653, r4654, e4655, e4656, e4657, e4658, e4659, e4660, r4661, e4662, e4663, e4664, e4665, e4666, e4667, r4668, e4669, e4670, e4671, e4672, e4673, e4674, r4675, e4676, e4677, r4678, e4679, e4680, r4681, r4682, r4683, e4684, e4685, r4686, e4687, e4688, r4689, r4690, r4691, r4692, r4693, r4694, r4695, r4696, r4697, r4698, r4699, r4700, r4701, r4702, r4703, r4704, r4705, r4706, r4707, r4708, r4709, r4710, r4711, r4712, r4713, r4714, r4715, b4716, b4717, b4718, b4719, b4720, b4721, b4722, b4723, b4724, b4725, b4726, b4727, b4728, b4729, b4730, b4731, b4732, b4733, b4734, b4735, b4736, b4737, b4738, b4739, b4740, b4741, b4742, b4743, b4744, b4745, b4746, b4747, b4748, b4749, b4750, b4751, b4752, b4753, b4754, b4755, b4756, b4757, b4758, b4759, b4760, b4761, b4762, b4763, b4764, b4765, b4766, b4767, b4768, b4769, b4770, b4771, b4772, b4773, b4774, b4775, b4776, b4777, b4778, b4779, b4780, b4781, b4782, b4783, b4784, b4785, b4786, b4787, b4788, b4789, b4790, b4791, b4792, b4793, b4794, b4795, b4796, b4797, b4798, b4799, b4800, b4801, b4802, b4803, b4804, b4805, b4806, b4807, b4808, b4809, b4810, b4811, b4812, b4813, b4814, b4815, b4816, b4817, b4818, b4819, b4820, b4821, b4822, b4823, b4824, b4825, b4826, b4827, b4828, b4829, b4830, b4831, b4832, b4833, b4834, b4835, b4836, b4837, b4838, b4839, b4840, b4841, b4842, b4843, b4844, b4845, b4846, b4847, b4848, b4849, b4850, b4851, b4852, b4853, b4854, b4855, b4856, b4857, b4858, b4859, b4860, b4861, b4862, b4863, b4864, b4865, d4638, d4622, d4610, d4606, d4614, d4602, d4594, d4578, d4582, d4558, d4546, d4550, d4534, d4530, d4538, d4506, g1, d4246, d4258, d4234, d4200, d4168, d4486, d4298, d4498, d4132, d4474, d4322, d4326, d4346, d4458, d4462, d4366, d4466, d4374, d4382, d4446, d4398, d4454, d4414, d4438, d4426, d4430, d4482, d4164, d4196, d4224, d4262, d4542, d4450, d4036, d4064, d4096, d4128, d4294, d4354, d4330, d4156, d4188, d4216, d4242, d4390, d4032, d4060, d4092, d4124, d4290, d4522, d4586, d4350, d4478, d4152, d4184, d4282, d4238, d4386, d4362, d4422]
  · have f4866 : (x 0 1).toNat = 1 := by rw [h4228]; rfl
    have d4867 : (x 0 14).toNat = 1 := by
      have r4868 : (x 0 1).toNat = (x 0 14).toNat := congrArg Bool.toNat (h114 0)
      have b4869 := hb (x 0 1)
      have b4870 := hb (x 0 14)
      clear * - r4868 b4869 b4870 f4866
      omega
    have d4871 : (x 1 14).toNat = 0 := by
      have r4872 : (x 1 14).toNat + (x 0 1).toNat = 1 := by have q := hd14 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4873 := hb (x 0 1)
      have b4874 := hb (x 1 14)
      clear * - r4872 b4873 b4874 f4866
      omega
    have d4875 : (x 1 3 && x 1 14).toNat = 0 := by
      have r4876 := hand2 (x 1 3) (x 1 14)
      have b4877 := hb (x 1 14)
      have b4878 := hb (x 1 3 && x 1 14)
      clear * - r4876 b4877 b4878 d4871
      omega
    have d4879 : (x 1 5 && x 1 14).toNat = 0 := by
      have r4880 := hand2 (x 1 5) (x 1 14)
      have b4881 := hb (x 1 14)
      have b4882 := hb (x 1 5 && x 1 14)
      clear * - r4880 b4881 b4882 d4871
      omega
    have d4883 : (x 1 7 && x 1 14).toNat = 0 := by
      have r4884 := hand2 (x 1 7) (x 1 14)
      have b4885 := hb (x 1 14)
      have b4886 := hb (x 1 7 && x 1 14)
      clear * - r4884 b4885 b4886 d4871
      omega
    have d4887 : (x 1 1).toNat = 0 := by
      have r4888 : (x 1 1).toNat = (x 1 14).toNat := congrArg Bool.toNat (h114 1)
      have b4889 := hb (x 1 1)
      have b4890 := hb (x 1 14)
      clear * - r4888 b4889 b4890 d4871
      omega
    have d4891 : (x 1 1 && x 1 12).toNat = 0 := by
      have r4892 := hand1 (x 1 1) (x 1 12)
      have b4893 := hb (x 1 1)
      have b4894 := hb (x 1 1 && x 1 12)
      clear * - r4892 b4893 b4894 d4887
      omega
    have d4895 : (x 1 13).toNat = 0 := by
      have r4896 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
      have b4897 := hb (x 1 1)
      have b4898 := hb (x 1 13)
      clear * - r4896 b4897 b4898 d4887
      omega
    have d4899 : (x 1 5).toNat = 0 := by
      have r4900 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
      have b4901 := hb (x 1 5)
      have b4902 := hb (x 1 13)
      clear * - r4900 b4901 b4902 d4895
      omega
    have d4903 : (x 1 5 && x 1 11).toNat = 0 := by
      have r4904 := hand1 (x 1 5) (x 1 11)
      have b4905 := hb (x 1 5)
      have b4906 := hb (x 1 5 && x 1 11)
      clear * - r4904 b4905 b4906 d4899
      omega
    have d4907 : (x 2 14).toNat = 1 := by
      have r4908 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4909 := hb (x 1 1)
      have b4910 := hb (x 2 14)
      clear * - r4908 b4909 b4910 d4887
      omega
    have d4911 : (x 2 1).toNat = 1 := by
      have r4912 : (x 2 1).toNat = (x 2 14).toNat := congrArg Bool.toNat (h114 2)
      have b4913 := hb (x 2 1)
      have b4914 := hb (x 2 14)
      clear * - r4912 b4913 b4914 d4907
      omega
    have d4915 : (x 3 14).toNat = 0 := by
      have r4916 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4917 := hb (x 2 1)
      have b4918 := hb (x 3 14)
      clear * - r4916 b4917 b4918 d4911
      omega
    have d4919 : (x 3 1).toNat = 0 := by
      have r4920 : (x 3 1).toNat = (x 3 14).toNat := congrArg Bool.toNat (h114 3)
      have b4921 := hb (x 3 1)
      have b4922 := hb (x 3 14)
      clear * - r4920 b4921 b4922 d4915
      omega
    have d4923 : (x 3 1 && x 3 12).toNat = 0 := by
      have r4924 := hand1 (x 3 1) (x 3 12)
      have b4925 := hb (x 3 1)
      have b4926 := hb (x 3 1 && x 3 12)
      clear * - r4924 b4925 b4926 d4919
      omega
    have d4927 : (x 3 1 && x 3 6).toNat = 0 := by
      have r4928 := hand1 (x 3 1) (x 3 6)
      have b4929 := hb (x 3 1)
      have b4930 := hb (x 3 1 && x 3 6)
      clear * - r4928 b4929 b4930 d4919
      omega
    have d4931 : (x 3 13).toNat = 0 := by
      have r4932 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
      have b4933 := hb (x 3 1)
      have b4934 := hb (x 3 13)
      clear * - r4932 b4933 b4934 d4919
      omega
    have d4935 : (x 3 5).toNat = 0 := by
      have r4936 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
      have b4937 := hb (x 3 5)
      have b4938 := hb (x 3 13)
      clear * - r4936 b4937 b4938 d4931
      omega
    have d4939 : (x 3 5 && x 3 12).toNat = 0 := by
      have r4940 := hand1 (x 3 5) (x 3 12)
      have b4941 := hb (x 3 5)
      have b4942 := hb (x 3 5 && x 3 12)
      clear * - r4940 b4941 b4942 d4935
      omega
    have d4943 : (x 3 9).toNat = 0 := by
      have r4944 : (x 3 9).toNat ≤ (x 3 1).toNat := himp _ _ (hp9 3)
      have b4945 := hb (x 3 1)
      have b4946 := hb (x 3 9)
      clear * - r4944 b4945 b4946 d4919
      omega
    have d4947 : (x 3 3 && x 3 9).toNat = 0 := by
      have r4948 := hand2 (x 3 3) (x 3 9)
      have b4949 := hb (x 3 9)
      have b4950 := hb (x 3 3 && x 3 9)
      clear * - r4948 b4949 b4950 d4943
      omega
    have d4951 : (x 4 14).toNat = 1 := by
      have r4952 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4953 := hb (x 3 1)
      have b4954 := hb (x 4 14)
      clear * - r4952 b4953 b4954 d4919
      omega
    have d4955 : (x 4 1).toNat = 1 := by
      have r4956 : (x 4 1).toNat = (x 4 14).toNat := congrArg Bool.toNat (h114 4)
      have b4957 := hb (x 4 1)
      have b4958 := hb (x 4 14)
      clear * - r4956 b4957 b4958 d4951
      omega
    have d4959 : (x 5 14).toNat = 0 := by
      have r4960 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4961 := hb (x 4 1)
      have b4962 := hb (x 5 14)
      clear * - r4960 b4961 b4962 d4955
      omega
    have d4963 : (x 5 1).toNat = 0 := by
      have r4964 : (x 5 1).toNat = (x 5 14).toNat := congrArg Bool.toNat (h114 5)
      have b4965 := hb (x 5 1)
      have b4966 := hb (x 5 14)
      clear * - r4964 b4965 b4966 d4959
      omega
    have d4967 : (x 5 1 && x 5 7).toNat = 0 := by
      have r4968 := hand1 (x 5 1) (x 5 7)
      have b4969 := hb (x 5 1)
      have b4970 := hb (x 5 1 && x 5 7)
      clear * - r4968 b4969 b4970 d4963
      omega
    have d4971 : (x 5 9).toNat = 0 := by
      have r4972 : (x 5 9).toNat ≤ (x 5 1).toNat := himp _ _ (hp9 5)
      have b4973 := hb (x 5 1)
      have b4974 := hb (x 5 9)
      clear * - r4972 b4973 b4974 d4963
      omega
    have d4975 : (x 6 14).toNat = 1 := by
      have r4976 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4977 := hb (x 5 1)
      have b4978 := hb (x 6 14)
      clear * - r4976 b4977 b4978 d4963
      omega
    have d4979 : (x 6 1).toNat = 1 := by
      have r4980 : (x 6 1).toNat = (x 6 14).toNat := congrArg Bool.toNat (h114 6)
      have b4981 := hb (x 6 1)
      have b4982 := hb (x 6 14)
      clear * - r4980 b4981 b4982 d4975
      omega
    have d4983 : (x 7 14).toNat = 0 := by
      have r4984 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4985 := hb (x 6 1)
      have b4986 := hb (x 7 14)
      clear * - r4984 b4985 b4986 d4979
      omega
    have d4987 : (x 7 4 && x 7 14).toNat = 0 := by
      have r4988 := hand2 (x 7 4) (x 7 14)
      have b4989 := hb (x 7 14)
      have b4990 := hb (x 7 4 && x 7 14)
      clear * - r4988 b4989 b4990 d4983
      omega
    have d4991 : (x 7 1).toNat = 0 := by
      have r4992 : (x 7 1).toNat = (x 7 14).toNat := congrArg Bool.toNat (h114 7)
      have b4993 := hb (x 7 1)
      have b4994 := hb (x 7 14)
      clear * - r4992 b4993 b4994 d4983
      omega
    have d4995 : (x 7 13).toNat = 0 := by
      have r4996 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
      have b4997 := hb (x 7 1)
      have b4998 := hb (x 7 13)
      clear * - r4996 b4997 b4998 d4991
      omega
    have d4999 : (x 7 5).toNat = 0 := by
      have r5000 : (x 7 5).toNat ≤ (x 7 13).toNat := himp _ _ (hp5 7)
      have b5001 := hb (x 7 5)
      have b5002 := hb (x 7 13)
      clear * - r5000 b5001 b5002 d4995
      omega
    have d5003 : (x 7 9).toNat = 0 := by
      have r5004 : (x 7 9).toNat ≤ (x 7 1).toNat := himp _ _ (hp9 7)
      have b5005 := hb (x 7 1)
      have b5006 := hb (x 7 9)
      clear * - r5004 b5005 b5006 d4991
      omega
    have d5007 : (x 8 14).toNat = 1 := by
      have r5008 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5009 := hb (x 7 1)
      have b5010 := hb (x 8 14)
      clear * - r5008 b5009 b5010 d4991
      omega
    have d5011 : (x 8 1).toNat = 1 := by
      have r5012 : (x 8 1).toNat = (x 8 14).toNat := congrArg Bool.toNat (h114 8)
      have b5013 := hb (x 8 1)
      have b5014 := hb (x 8 14)
      clear * - r5012 b5013 b5014 d5007
      omega
    have d5015 : (x 9 14).toNat = 0 := by
      have r5016 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5017 := hb (x 8 1)
      have b5018 := hb (x 9 14)
      clear * - r5016 b5017 b5018 d5011
      omega
    have d5019 : (x 9 3 && x 9 14).toNat = 0 := by
      have r5020 := hand2 (x 9 3) (x 9 14)
      have b5021 := hb (x 9 14)
      have b5022 := hb (x 9 3 && x 9 14)
      clear * - r5020 b5021 b5022 d5015
      omega
    have d5023 : (x 9 1).toNat = 0 := by
      have r5024 : (x 9 1).toNat = (x 9 14).toNat := congrArg Bool.toNat (h114 9)
      have b5025 := hb (x 9 1)
      have b5026 := hb (x 9 14)
      clear * - r5024 b5025 b5026 d5015
      omega
    have d5027 : (x 10 14).toNat = 1 := by
      have r5028 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5029 := hb (x 9 1)
      have b5030 := hb (x 10 14)
      clear * - r5028 b5029 b5030 d5023
      omega
    have d5031 : (x 10 1).toNat = 1 := by
      have r5032 : (x 10 1).toNat = (x 10 14).toNat := congrArg Bool.toNat (h114 10)
      have b5033 := hb (x 10 1)
      have b5034 := hb (x 10 14)
      clear * - r5032 b5033 b5034 d5027
      omega
    have d5035 : (x 9 6).toNat = 0 := by
      have r5036 : (x 9 6).toNat ≤ (x 9 14).toNat := himp _ _ (hp6 9)
      have b5037 := hb (x 9 6)
      have b5038 := hb (x 9 14)
      clear * - r5036 b5037 b5038 d5015
      omega
    have d5039 : (x 9 2 && x 9 6).toNat = 0 := by
      have r5040 := hand2 (x 9 2) (x 9 6)
      have b5041 := hb (x 9 6)
      have b5042 := hb (x 9 2 && x 9 6)
      clear * - r5040 b5041 b5042 d5035
      omega
    have d5043 : (x 9 2).toNat = 0 := by
      have r5044 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
      have b5045 := hb (x 9 2)
      have b5046 := hb (x 9 14)
      clear * - r5044 b5045 b5046 d5015
      omega
    have d5047 : (x 9 2 && x 9 12).toNat = 0 := by
      have r5048 := hand1 (x 9 2) (x 9 12)
      have b5049 := hb (x 9 2)
      have b5050 := hb (x 9 2 && x 9 12)
      clear * - r5048 b5049 b5050 d5043
      omega
    have d5051 : (x 9 3).toNat = 0 := by
      have r5052 : (x 9 2).toNat = (x 9 3).toNat := congrArg Bool.toNat (h23 9)
      have b5053 := hb (x 9 2)
      have b5054 := hb (x 9 3)
      clear * - r5052 b5053 b5054 d5043
      omega
    have d5055 : (x 7 6).toNat = 0 := by
      have r5056 : (x 7 6).toNat ≤ (x 7 14).toNat := himp _ _ (hp6 7)
      have b5057 := hb (x 7 6)
      have b5058 := hb (x 7 14)
      clear * - r5056 b5057 b5058 d4983
      omega
    have d5059 : (x 7 2).toNat = 0 := by
      have r5060 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
      have b5061 := hb (x 7 2)
      have b5062 := hb (x 7 14)
      clear * - r5060 b5061 b5062 d4983
      omega
    have d5063 : (x 7 10).toNat = 0 := by
      have r5064 : (x 7 10).toNat ≤ (x 7 2).toNat := himp _ _ (hp10 7)
      have b5065 := hb (x 7 2)
      have b5066 := hb (x 7 10)
      clear * - r5064 b5065 b5066 d5059
      omega
    have d5067 : (x 5 6).toNat = 0 := by
      have r5068 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
      have b5069 := hb (x 5 6)
      have b5070 := hb (x 5 14)
      clear * - r5068 b5069 b5070 d4959
      omega
    have d5071 : (x 5 2).toNat = 0 := by
      have r5072 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
      have b5073 := hb (x 5 2)
      have b5074 := hb (x 5 14)
      clear * - r5072 b5073 b5074 d4959
      omega
    have d5075 : (x 5 2 && x 5 12).toNat = 0 := by
      have r5076 := hand1 (x 5 2) (x 5 12)
      have b5077 := hb (x 5 2)
      have b5078 := hb (x 5 2 && x 5 12)
      clear * - r5076 b5077 b5078 d5071
      omega
    have d5079 : (x 5 2 && x 5 11).toNat = 0 := by
      have r5080 := hand1 (x 5 2) (x 5 11)
      have b5081 := hb (x 5 2)
      have b5082 := hb (x 5 2 && x 5 11)
      clear * - r5080 b5081 b5082 d5071
      omega
    have d5083 : (x 5 2 && x 5 8).toNat = 0 := by
      have r5084 := hand1 (x 5 2) (x 5 8)
      have b5085 := hb (x 5 2)
      have b5086 := hb (x 5 2 && x 5 8)
      clear * - r5084 b5085 b5086 d5071
      omega
    have d5087 : (x 5 2 && x 5 7).toNat = 0 := by
      have r5088 := hand1 (x 5 2) (x 5 7)
      have b5089 := hb (x 5 2)
      have b5090 := hb (x 5 2 && x 5 7)
      clear * - r5088 b5089 b5090 d5071
      omega
    have d5091 : (x 5 3).toNat = 0 := by
      have r5092 : (x 5 2).toNat = (x 5 3).toNat := congrArg Bool.toNat (h23 5)
      have b5093 := hb (x 5 2)
      have b5094 := hb (x 5 3)
      clear * - r5092 b5093 b5094 d5071
      omega
    have d5095 : (x 5 11).toNat = 0 := by
      have r5096 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
      have b5097 := hb (x 5 3)
      have b5098 := hb (x 5 11)
      clear * - r5096 b5097 b5098 d5091
      omega
    have d5099 : (x 3 6).toNat = 0 := by
      have r5100 : (x 3 6).toNat ≤ (x 3 14).toNat := himp _ _ (hp6 3)
      have b5101 := hb (x 3 6)
      have b5102 := hb (x 3 14)
      clear * - r5100 b5101 b5102 d4915
      omega
    have d5103 : (x 3 2).toNat = 0 := by
      have r5104 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
      have b5105 := hb (x 3 2)
      have b5106 := hb (x 3 14)
      clear * - r5104 b5105 b5106 d4915
      omega
    have d5107 : (x 3 3).toNat = 0 := by
      have r5108 : (x 3 2).toNat = (x 3 3).toNat := congrArg Bool.toNat (h23 3)
      have b5109 := hb (x 3 2)
      have b5110 := hb (x 3 3)
      clear * - r5108 b5109 b5110 d5103
      omega
    have d5111 : (x 3 3 && x 3 12).toNat = 0 := by
      have r5112 := hand1 (x 3 3) (x 3 12)
      have b5113 := hb (x 3 3)
      have b5114 := hb (x 3 3 && x 3 12)
      clear * - r5112 b5113 b5114 d5107
      omega
    have d5115 : (x 3 11).toNat = 0 := by
      have r5116 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
      have b5117 := hb (x 3 3)
      have b5118 := hb (x 3 11)
      clear * - r5116 b5117 b5118 d5107
      omega
    have d5119 : (x 1 2).toNat = 0 := by
      have r5120 : (x 1 2).toNat ≤ (x 1 14).toNat := himp _ _ (hp2 1)
      have b5121 := hb (x 1 2)
      have b5122 := hb (x 1 14)
      clear * - r5120 b5121 b5122 d4871
      omega
    have d5123 : (x 1 3).toNat = 0 := by
      have r5124 : (x 1 2).toNat = (x 1 3).toNat := congrArg Bool.toNat (h23 1)
      have b5125 := hb (x 1 2)
      have b5126 := hb (x 1 3)
      clear * - r5124 b5125 b5126 d5119
      omega
    have d5127 : (x 1 3 && x 1 8).toNat = 0 := by
      have r5128 := hand1 (x 1 3) (x 1 8)
      have b5129 := hb (x 1 3)
      have b5130 := hb (x 1 3 && x 1 8)
      clear * - r5128 b5129 b5130 d5123
      omega
    have d5131 : (x 1 3 && x 1 7).toNat = 0 := by
      have r5132 := hand1 (x 1 3) (x 1 7)
      have b5133 := hb (x 1 3)
      have b5134 := hb (x 1 3 && x 1 7)
      clear * - r5132 b5133 b5134 d5123
      omega
    have d5135 : (x 1 11).toNat = 0 := by
      have r5136 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
      have b5137 := hb (x 1 3)
      have b5138 := hb (x 1 11)
      clear * - r5136 b5137 b5138 d5123
      omega
    have d5139 : (x 1 10).toNat = 0 := by
      have r5140 : (x 1 10).toNat ≤ (x 1 2).toNat := himp _ _ (hp10 1)
      have b5141 := hb (x 1 2)
      have b5142 := hb (x 1 10)
      clear * - r5140 b5141 b5142 d5119
      omega
    have d5143 : (x (-1) 1).toNat = 0 := by
      have r5144 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5145 := hb (x (-1) 1)
      have b5146 := hb (x 0 14)
      clear * - r5144 b5145 b5146 d4867
      omega
    have d5147 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
      have r5148 := hand1 (x (-1) 1) (x (-1) 12)
      have b5149 := hb (x (-1) 1)
      have b5150 := hb (x (-1) 1 && x (-1) 12)
      clear * - r5148 b5149 b5150 d5143
      omega
    have d5151 : (x (-1) 14).toNat = 0 := by
      have r5152 : (x (-1) 1).toNat = (x (-1) 14).toNat := congrArg Bool.toNat (h114 (-1))
      have b5153 := hb (x (-1) 1)
      have b5154 := hb (x (-1) 14)
      clear * - r5152 b5153 b5154 d5143
      omega
    have d5155 : (x (-1) 3 && x (-1) 14).toNat = 0 := by
      have r5156 := hand2 (x (-1) 3) (x (-1) 14)
      have b5157 := hb (x (-1) 14)
      have b5158 := hb (x (-1) 3 && x (-1) 14)
      clear * - r5156 b5157 b5158 d5151
      omega
    have d5159 : (x (-1) 8 && x (-1) 14).toNat = 0 := by
      have r5160 := hand2 (x (-1) 8) (x (-1) 14)
      have b5161 := hb (x (-1) 14)
      have b5162 := hb (x (-1) 8 && x (-1) 14)
      clear * - r5160 b5161 b5162 d5151
      omega
    have d5163 : (x (-1) 2).toNat = 0 := by
      have r5164 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
      have b5165 := hb (x (-1) 2)
      have b5166 := hb (x (-1) 14)
      clear * - r5164 b5165 b5166 d5151
      omega
    have d5167 : (x (-1) 2 && x (-1) 12).toNat = 0 := by
      have r5168 := hand1 (x (-1) 2) (x (-1) 12)
      have b5169 := hb (x (-1) 2)
      have b5170 := hb (x (-1) 2 && x (-1) 12)
      clear * - r5168 b5169 b5170 d5163
      omega
    have d5171 : (x (-1) 10).toNat = 0 := by
      have r5172 : (x (-1) 10).toNat ≤ (x (-1) 2).toNat := himp _ _ (hp10 (-1))
      have b5173 := hb (x (-1) 2)
      have b5174 := hb (x (-1) 10)
      clear * - r5172 b5173 b5174 d5163
      omega
    have d5175 : (x (-1) 5 && x (-1) 10).toNat = 0 := by
      have r5176 := hand2 (x (-1) 5) (x (-1) 10)
      have b5177 := hb (x (-1) 10)
      have b5178 := hb (x (-1) 5 && x (-1) 10)
      clear * - r5176 b5177 b5178 d5171
      omega
    have d5179 : (x (-1) 13).toNat = 0 := by
      have r5180 : (x (-1) 13).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp13 (-1))
      have b5181 := hb (x (-1) 1)
      have b5182 := hb (x (-1) 13)
      clear * - r5180 b5181 b5182 d5143
      omega
    have d5183 : (x (-1) 7 && x (-1) 13).toNat = 0 := by
      have r5184 := hand2 (x (-1) 7) (x (-1) 13)
      have b5185 := hb (x (-1) 13)
      have b5186 := hb (x (-1) 7 && x (-1) 13)
      clear * - r5184 b5185 b5186 d5179
      omega
    have d5187 : (x (-1) 8 && x (-1) 13).toNat = 0 := by
      have r5188 := hand2 (x (-1) 8) (x (-1) 13)
      have b5189 := hb (x (-1) 13)
      have b5190 := hb (x (-1) 8 && x (-1) 13)
      clear * - r5188 b5189 b5190 d5179
      omega
    have d5191 : (x (-1) 5).toNat = 0 := by
      have r5192 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
      have b5193 := hb (x (-1) 5)
      have b5194 := hb (x (-1) 13)
      clear * - r5192 b5193 b5194 d5179
      omega
    have d5195 : (x (-1) 5 && x (-1) 9).toNat = 0 := by
      have r5196 := hand1 (x (-1) 5) (x (-1) 9)
      have b5197 := hb (x (-1) 5)
      have b5198 := hb (x (-1) 5 && x (-1) 9)
      clear * - r5196 b5197 b5198 d5191
      omega
    have d5199 : (x (-1) 9).toNat = 0 := by
      have r5200 : (x (-1) 9).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp9 (-1))
      have b5201 := hb (x (-1) 1)
      have b5202 := hb (x (-1) 9)
      clear * - r5200 b5201 b5202 d5143
      omega
    have d5203 : (x (-2) 1).toNat = 1 := by
      have r5204 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5205 := hb (x (-2) 1)
      have b5206 := hb (x (-1) 14)
      clear * - r5204 b5205 b5206 d5151
      omega
    have d5207 : (x (-2) 14).toNat = 1 := by
      have r5208 : (x (-2) 1).toNat = (x (-2) 14).toNat := congrArg Bool.toNat (h114 (-2))
      have b5209 := hb (x (-2) 1)
      have b5210 := hb (x (-2) 14)
      clear * - r5208 b5209 b5210 d5203
      omega
    have d5211 : (x (-3) 1).toNat = 0 := by
      have r5212 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5213 := hb (x (-3) 1)
      have b5214 := hb (x (-2) 14)
      clear * - r5212 b5213 b5214 d5207
      omega
    have d5215 : (x (-3) 1 && x (-3) 12).toNat = 0 := by
      have r5216 := hand1 (x (-3) 1) (x (-3) 12)
      have b5217 := hb (x (-3) 1)
      have b5218 := hb (x (-3) 1 && x (-3) 12)
      clear * - r5216 b5217 b5218 d5211
      omega
    have d5219 : (x (-3) 14).toNat = 0 := by
      have r5220 : (x (-3) 1).toNat = (x (-3) 14).toNat := congrArg Bool.toNat (h114 (-3))
      have b5221 := hb (x (-3) 1)
      have b5222 := hb (x (-3) 14)
      clear * - r5220 b5221 b5222 d5211
      omega
    have d5223 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
      have r5224 := hand2 (x (-3) 3) (x (-3) 14)
      have b5225 := hb (x (-3) 14)
      have b5226 := hb (x (-3) 3 && x (-3) 14)
      clear * - r5224 b5225 b5226 d5219
      omega
    have d5227 : (x (-3) 4 && x (-3) 14).toNat = 0 := by
      have r5228 := hand2 (x (-3) 4) (x (-3) 14)
      have b5229 := hb (x (-3) 14)
      have b5230 := hb (x (-3) 4 && x (-3) 14)
      clear * - r5228 b5229 b5230 d5219
      omega
    have d5231 : (x (-3) 2).toNat = 0 := by
      have r5232 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
      have b5233 := hb (x (-3) 2)
      have b5234 := hb (x (-3) 14)
      clear * - r5232 b5233 b5234 d5219
      omega
    have d5235 : (x (-3) 3).toNat = 0 := by
      have r5236 : (x (-3) 2).toNat = (x (-3) 3).toNat := congrArg Bool.toNat (h23 (-3))
      have b5237 := hb (x (-3) 2)
      have b5238 := hb (x (-3) 3)
      clear * - r5236 b5237 b5238 d5231
      omega
    have d5239 : (x (-3) 11).toNat = 0 := by
      have r5240 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
      have b5241 := hb (x (-3) 3)
      have b5242 := hb (x (-3) 11)
      clear * - r5240 b5241 b5242 d5235
      omega
    have d5243 : (x (-3) 7 && x (-3) 11).toNat = 0 := by
      have r5244 := hand2 (x (-3) 7) (x (-3) 11)
      have b5245 := hb (x (-3) 11)
      have b5246 := hb (x (-3) 7 && x (-3) 11)
      clear * - r5244 b5245 b5246 d5239
      omega
    have d5247 : (x (-3) 10).toNat = 0 := by
      have r5248 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
      have b5249 := hb (x (-3) 2)
      have b5250 := hb (x (-3) 10)
      clear * - r5248 b5249 b5250 d5231
      omega
    have d5251 : (x (-3) 13).toNat = 0 := by
      have r5252 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
      have b5253 := hb (x (-3) 1)
      have b5254 := hb (x (-3) 13)
      clear * - r5252 b5253 b5254 d5211
      omega
    have d5255 : (x (-3) 9).toNat = 0 := by
      have r5256 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
      have b5257 := hb (x (-3) 1)
      have b5258 := hb (x (-3) 9)
      clear * - r5256 b5257 b5258 d5211
      omega
    have d5259 : (x (-4) 1).toNat = 1 := by
      have r5260 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5261 := hb (x (-4) 1)
      have b5262 := hb (x (-3) 14)
      clear * - r5260 b5261 b5262 d5219
      omega
    have d5263 : (x (-4) 14).toNat = 1 := by
      have r5264 : (x (-4) 1).toNat = (x (-4) 14).toNat := congrArg Bool.toNat (h114 (-4))
      have b5265 := hb (x (-4) 1)
      have b5266 := hb (x (-4) 14)
      clear * - r5264 b5265 b5266 d5259
      omega
    have d5267 : (x (-5) 1).toNat = 0 := by
      have r5268 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5269 := hb (x (-5) 1)
      have b5270 := hb (x (-4) 14)
      clear * - r5268 b5269 b5270 d5263
      omega
    have d5271 : (x (-5) 1 && x (-5) 14).toNat = 0 := by
      have r5272 := hand1 (x (-5) 1) (x (-5) 14)
      have b5273 := hb (x (-5) 1)
      have b5274 := hb (x (-5) 1 && x (-5) 14)
      clear * - r5272 b5273 b5274 d5267
      omega
    have d5275 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
      have r5276 := hand1 (x (-5) 1) (x (-5) 12)
      have b5277 := hb (x (-5) 1)
      have b5278 := hb (x (-5) 1 && x (-5) 12)
      clear * - r5276 b5277 b5278 d5267
      omega
    have d5279 : (x (-5) 1 && x (-5) 11).toNat = 0 := by
      have r5280 := hand1 (x (-5) 1) (x (-5) 11)
      have b5281 := hb (x (-5) 1)
      have b5282 := hb (x (-5) 1 && x (-5) 11)
      clear * - r5280 b5281 b5282 d5267
      omega
    have d5283 : (x (-5) 14).toNat = 0 := by
      have r5284 : (x (-5) 1).toNat = (x (-5) 14).toNat := congrArg Bool.toNat (h114 (-5))
      have b5285 := hb (x (-5) 1)
      have b5286 := hb (x (-5) 14)
      clear * - r5284 b5285 b5286 d5267
      omega
    have d5287 : (x (-5) 3 && x (-5) 14).toNat = 0 := by
      have r5288 := hand2 (x (-5) 3) (x (-5) 14)
      have b5289 := hb (x (-5) 14)
      have b5290 := hb (x (-5) 3 && x (-5) 14)
      clear * - r5288 b5289 b5290 d5283
      omega
    have d5291 : (x (-5) 9 && x (-5) 14).toNat = 0 := by
      have r5292 := hand2 (x (-5) 9) (x (-5) 14)
      have b5293 := hb (x (-5) 14)
      have b5294 := hb (x (-5) 9 && x (-5) 14)
      clear * - r5292 b5293 b5294 d5283
      omega
    have d5295 : (x (-5) 6).toNat = 0 := by
      have r5296 : (x (-5) 6).toNat ≤ (x (-5) 14).toNat := himp _ _ (hp6 (-5))
      have b5297 := hb (x (-5) 6)
      have b5298 := hb (x (-5) 14)
      clear * - r5296 b5297 b5298 d5283
      omega
    have d5299 : (x (-5) 2).toNat = 0 := by
      have r5300 : (x (-5) 2).toNat ≤ (x (-5) 14).toNat := himp _ _ (hp2 (-5))
      have b5301 := hb (x (-5) 2)
      have b5302 := hb (x (-5) 14)
      clear * - r5300 b5301 b5302 d5283
      omega
    have d5303 : (x (-5) 3).toNat = 0 := by
      have r5304 : (x (-5) 2).toNat = (x (-5) 3).toNat := congrArg Bool.toNat (h23 (-5))
      have b5305 := hb (x (-5) 2)
      have b5306 := hb (x (-5) 3)
      clear * - r5304 b5305 b5306 d5299
      omega
    have d5307 : (x (-5) 11).toNat = 0 := by
      have r5308 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
      have b5309 := hb (x (-5) 3)
      have b5310 := hb (x (-5) 11)
      clear * - r5308 b5309 b5310 d5303
      omega
    have d5311 : (x (-5) 13).toNat = 0 := by
      have r5312 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
      have b5313 := hb (x (-5) 1)
      have b5314 := hb (x (-5) 13)
      clear * - r5312 b5313 b5314 d5267
      omega
    have d5315 : (x (-5) 9 && x (-5) 13).toNat = 0 := by
      have r5316 := hand2 (x (-5) 9) (x (-5) 13)
      have b5317 := hb (x (-5) 13)
      have b5318 := hb (x (-5) 9 && x (-5) 13)
      clear * - r5316 b5317 b5318 d5311
      omega
    have d5319 : (x (-5) 5).toNat = 0 := by
      have r5320 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
      have b5321 := hb (x (-5) 5)
      have b5322 := hb (x (-5) 13)
      clear * - r5320 b5321 b5322 d5311
      omega
    have d5323 : (x (-5) 9).toNat = 0 := by
      have r5324 : (x (-5) 9).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp9 (-5))
      have b5325 := hb (x (-5) 1)
      have b5326 := hb (x (-5) 9)
      clear * - r5324 b5325 b5326 d5267
      omega
    have d5327 : (x (-6) 1).toNat = 1 := by
      have r5328 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5329 := hb (x (-6) 1)
      have b5330 := hb (x (-5) 14)
      clear * - r5328 b5329 b5330 d5283
      omega
    have d5331 : (x (-6) 14).toNat = 1 := by
      have r5332 : (x (-6) 1).toNat = (x (-6) 14).toNat := congrArg Bool.toNat (h114 (-6))
      have b5333 := hb (x (-6) 1)
      have b5334 := hb (x (-6) 14)
      clear * - r5332 b5333 b5334 d5327
      omega
    have d5335 : (x (-7) 1).toNat = 0 := by
      have r5336 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5337 := hb (x (-7) 1)
      have b5338 := hb (x (-6) 14)
      clear * - r5336 b5337 b5338 d5331
      omega
    have d5339 : (x (-7) 14).toNat = 0 := by
      have r5340 : (x (-7) 1).toNat = (x (-7) 14).toNat := congrArg Bool.toNat (h114 (-7))
      have b5341 := hb (x (-7) 1)
      have b5342 := hb (x (-7) 14)
      clear * - r5340 b5341 b5342 d5335
      omega
    have d5343 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
      have r5344 := hand2 (x (-7) 3) (x (-7) 14)
      have b5345 := hb (x (-7) 14)
      have b5346 := hb (x (-7) 3 && x (-7) 14)
      clear * - r5344 b5345 b5346 d5339
      omega
    have d5347 : (x (-7) 2).toNat = 0 := by
      have r5348 : (x (-7) 2).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp2 (-7))
      have b5349 := hb (x (-7) 2)
      have b5350 := hb (x (-7) 14)
      clear * - r5348 b5349 b5350 d5339
      omega
    have d5351 : (x (-7) 3).toNat = 0 := by
      have r5352 : (x (-7) 2).toNat = (x (-7) 3).toNat := congrArg Bool.toNat (h23 (-7))
      have b5353 := hb (x (-7) 2)
      have b5354 := hb (x (-7) 3)
      clear * - r5352 b5353 b5354 d5347
      omega
    have d5355 : (x (-7) 3 && x (-7) 13).toNat = 0 := by
      have r5356 := hand1 (x (-7) 3) (x (-7) 13)
      have b5357 := hb (x (-7) 3)
      have b5358 := hb (x (-7) 3 && x (-7) 13)
      clear * - r5356 b5357 b5358 d5351
      omega
    have d5359 : (x (-7) 11).toNat = 0 := by
      have r5360 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
      have b5361 := hb (x (-7) 3)
      have b5362 := hb (x (-7) 11)
      clear * - r5360 b5361 b5362 d5351
      omega
    have d5363 : (x (-7) 13).toNat = 0 := by
      have r5364 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
      have b5365 := hb (x (-7) 1)
      have b5366 := hb (x (-7) 13)
      clear * - r5364 b5365 b5366 d5335
      omega
    have d5367 : (x (-8) 1).toNat = 1 := by
      have r5368 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5369 := hb (x (-8) 1)
      have b5370 := hb (x (-7) 14)
      clear * - r5368 b5369 b5370 d5339
      omega
    have d5371 : (x (-8) 14).toNat = 1 := by
      have r5372 : (x (-8) 1).toNat = (x (-8) 14).toNat := congrArg Bool.toNat (h114 (-8))
      have b5373 := hb (x (-8) 1)
      have b5374 := hb (x (-8) 14)
      clear * - r5372 b5373 b5374 d5367
      omega
    have d5375 : (x (-9) 1).toNat = 0 := by
      have r5376 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5377 := hb (x (-9) 1)
      have b5378 := hb (x (-8) 14)
      clear * - r5376 b5377 b5378 d5371
      omega
    have d5379 : (x (-9) 14).toNat = 0 := by
      have r5380 : (x (-9) 1).toNat = (x (-9) 14).toNat := congrArg Bool.toNat (h114 (-9))
      have b5381 := hb (x (-9) 1)
      have b5382 := hb (x (-9) 14)
      clear * - r5380 b5381 b5382 d5375
      omega
    have d5383 : (x (-9) 13).toNat = 0 := by
      have r5384 : (x (-9) 13).toNat ≤ (x (-9) 1).toNat := himp _ _ (hp13 (-9))
      have b5385 := hb (x (-9) 1)
      have b5386 := hb (x (-9) 13)
      clear * - r5384 b5385 b5386 d5375
      omega
    have d5387 : (x (-9) 5).toNat = 0 := by
      have r5388 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
      have b5389 := hb (x (-9) 5)
      have b5390 := hb (x (-9) 13)
      clear * - r5388 b5389 b5390 d5383
      omega
    have d5391 : (x (-10) 1).toNat = 1 := by
      have r5392 : (x (-9) 14).toNat + (x (-10) 1).toNat = 1 := by have q := hd14 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5393 := hb (x (-10) 1)
      have b5394 := hb (x (-9) 14)
      clear * - r5392 b5393 b5394 d5379
      omega
    have d5395 : (x (-10) 14).toNat = 1 := by
      have r5396 : (x (-10) 1).toNat = (x (-10) 14).toNat := congrArg Bool.toNat (h114 (-10))
      have b5397 := hb (x (-10) 1)
      have b5398 := hb (x (-10) 14)
      clear * - r5396 b5397 b5398 d5391
      omega
    have d5399 : (x 2 4 && x 2 13).toNat = 1 := by
      have r5400 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5401 := hb (x 0 6)
      have b5402 := hb (x 6 9)
      have b5403 := hb (x 5 1 && x 5 10)
      have b5404 := hb (x 4 2 && x 4 11)
      have b5405 := hb (x 3 3 && x 3 12)
      have b5406 := hb (x 2 4 && x 2 13)
      have b5407 := hb (x 1 5 && x 1 14)
      clear * - r5400 b5401 b5402 b5403 b5404 b5405 b5406 b5407 d4040 d4084 d4116 d5111 d4879 g0
      omega
    have d5408 : (x 2 13).toNat = 1 := by
      have r5409 := hand2 (x 2 4) (x 2 13)
      have b5410 := hb (x 2 13)
      have b5411 := hb (x 2 4 && x 2 13)
      clear * - r5409 b5410 b5411 d5399
      omega
    have d5412 : (x 3 12).toNat = 0 := by
      have r5413 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5414 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
      have e5415 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
      have b5416 := hb (x 0 3)
      have b5417 := hb (x 1 2)
      have b5418 := hb (x 2 13)
      have b5419 := hb (x 3 12)
      clear * - r5413 e5414 e5415 b5416 b5417 b5418 b5419 d5408 d5119
      omega
    have d5420 : (x 3 8 && x 3 12).toNat = 0 := by
      have r5421 := hand2 (x 3 8) (x 3 12)
      have b5422 := hb (x 3 12)
      have b5423 := hb (x 3 8 && x 3 12)
      clear * - r5421 b5422 b5423 d5412
      omega
    have d5424 : (x 0 3).toNat = 0 := by
      have r5425 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5426 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
      have e5427 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
      have b5428 := hb (x 0 3)
      have b5429 := hb (x 1 2)
      have b5430 := hb (x 2 13)
      have b5431 := hb (x 3 12)
      clear * - r5425 e5426 e5427 b5428 b5429 b5430 b5431 d5412 d5408 d5119
      omega
    have d5432 : (x 0 2).toNat = 0 := by
      have r5433 : (x 0 2).toNat = (x 0 3).toNat := congrArg Bool.toNat (h23 0)
      have b5434 := hb (x 0 2)
      have b5435 := hb (x 0 3)
      clear * - r5433 b5434 b5435 d5424
      omega
    have d5436 : (x 0 2 && x 0 13).toNat = 0 := by
      have r5437 := hand1 (x 0 2) (x 0 13)
      have b5438 := hb (x 0 2)
      have b5439 := hb (x 0 2 && x 0 13)
      clear * - r5437 b5438 b5439 d5432
      omega
    have d5440 : (x 0 11).toNat = 0 := by
      have r5441 : (x 0 11).toNat ≤ (x 0 3).toNat := himp _ _ (hp11 0)
      have b5442 := hb (x 0 3)
      have b5443 := hb (x 0 11)
      clear * - r5441 b5442 b5443 d5424
      omega
    have d5444 : (x 0 1 && x 0 11).toNat = 0 := by
      have r5445 := hand2 (x 0 1) (x 0 11)
      have b5446 := hb (x 0 11)
      have b5447 := hb (x 0 1 && x 0 11)
      clear * - r5445 b5446 b5447 d5440
      omega
    have d5448 : (x 2 4).toNat = 1 := by
      have r5449 := hand1 (x 2 4) (x 2 13)
      have b5450 := hb (x 2 4)
      have b5451 := hb (x 2 4 && x 2 13)
      clear * - r5449 b5450 b5451 d5399
      omega
    have d5452 : (x 6 8).toNat = 0 := by
      have r5453 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5454 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e5455 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e5456 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e5457 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e5458 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e5459 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b5460 := hb (x (-1) 7)
      have b5461 := hb (x 0 6)
      have b5462 := hb (x 1 5)
      have b5463 := hb (x 2 4)
      have b5464 := hb (x 3 11)
      have b5465 := hb (x 4 10)
      have b5466 := hb (x 5 9)
      have b5467 := hb (x 6 8)
      clear * - r5453 e5454 e5455 e5456 e5457 e5458 e5459 b5460 b5461 b5462 b5463 b5464 b5465 b5466 b5467 d4971 d5115 d5448 d4899 g0
      omega
    have d5468 : (x 4 10).toNat = 0 := by
      have r5469 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5470 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e5471 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e5472 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e5473 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e5474 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e5475 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b5476 := hb (x (-1) 7)
      have b5477 := hb (x 0 6)
      have b5478 := hb (x 1 5)
      have b5479 := hb (x 2 4)
      have b5480 := hb (x 3 11)
      have b5481 := hb (x 4 10)
      have b5482 := hb (x 5 9)
      have b5483 := hb (x 6 8)
      clear * - r5469 e5470 e5471 e5472 e5473 e5474 e5475 b5476 b5477 b5478 b5479 b5480 b5481 b5482 b5483 d5452 d4971 d5115 d5448 d4899 g0
      omega
    have d5484 : (x (-1) 7).toNat = 0 := by
      have r5485 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5486 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e5487 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e5488 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e5489 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e5490 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e5491 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b5492 := hb (x (-1) 7)
      have b5493 := hb (x 0 6)
      have b5494 := hb (x 1 5)
      have b5495 := hb (x 2 4)
      have b5496 := hb (x 3 11)
      have b5497 := hb (x 4 10)
      have b5498 := hb (x 5 9)
      have b5499 := hb (x 6 8)
      clear * - r5485 e5486 e5487 e5488 e5489 e5490 e5491 b5492 b5493 b5494 b5495 b5496 b5497 b5498 b5499 d5452 d4971 d5468 d5115 d5448 d4899 g0
      omega
    cases h5500 : x 0 12
    · have f5501 : (x 0 12).toNat = 0 := by rw [h5500]; rfl
      have d5502 : (x 0 7 && x 0 12).toNat = 0 := by
        have r5503 := hand2 (x 0 7) (x 0 12)
        have b5504 := hb (x 0 12)
        have b5505 := hb (x 0 7 && x 0 12)
        clear * - r5503 b5504 b5505 f5501
        omega
      have d5506 : (x 0 4).toNat = 0 := by
        have r5507 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
        have b5508 := hb (x 0 4)
        have b5509 := hb (x 0 12)
        clear * - r5507 b5508 b5509 f5501
        omega
      have d5510 : (x 0 4 && x 0 8).toNat = 0 := by
        have r5511 := hand1 (x 0 4) (x 0 8)
        have b5512 := hb (x 0 4)
        have b5513 := hb (x 0 4 && x 0 8)
        clear * - r5511 b5512 b5513 d5506
        omega
      have d5514 : (x (-2) 2).toNat = 1 := by
        have r5515 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5516 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
        have e5517 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
        have b5518 := hb (x (-3) 3)
        have b5519 := hb (x (-2) 2)
        have b5520 := hb (x (-1) 13)
        have b5521 := hb (x 0 12)
        clear * - r5515 e5516 e5517 b5518 b5519 b5520 b5521 f5501 d5179 d5235
        omega
      have d5522 : (x (-2) 3).toNat = 1 := by
        have r5523 : (x (-2) 2).toNat = (x (-2) 3).toNat := congrArg Bool.toNat (h23 (-2))
        have b5524 := hb (x (-2) 2)
        have b5525 := hb (x (-2) 3)
        clear * - r5523 b5524 b5525 d5514
        omega
      have d5526 : (x 1 12).toNat = 0 := by
        have r5527 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5528 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e5529 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b5530 := hb (x (-2) 3)
        have b5531 := hb (x (-1) 2)
        have b5532 := hb (x 0 13)
        have b5533 := hb (x 1 12)
        clear * - r5527 e5528 e5529 b5530 b5531 b5532 b5533 d5163 d5522
        omega
      have d5534 : (x 0 13).toNat = 0 := by
        have r5535 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5536 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e5537 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b5538 := hb (x (-2) 3)
        have b5539 := hb (x (-1) 2)
        have b5540 := hb (x 0 13)
        have b5541 := hb (x 1 12)
        clear * - r5535 e5536 e5537 b5538 b5539 b5540 b5541 d5526 d5163 d5522
        omega
      have d5542 : (x 0 7 && x 0 13).toNat = 0 := by
        have r5543 := hand2 (x 0 7) (x 0 13)
        have b5544 := hb (x 0 13)
        have b5545 := hb (x 0 7 && x 0 13)
        clear * - r5543 b5544 b5545 d5534
        omega
      have d5546 : (x 2 2 && x 2 13).toNat = 1 := by
        have r5547 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b5548 := hb (x 0 4)
        have b5549 := hb (x 4 11)
        have b5550 := hb (x 3 1 && x 3 12)
        have b5551 := hb (x 2 2 && x 2 13)
        have b5552 := hb (x 1 3 && x 1 14)
        clear * - r5547 b5548 b5549 b5550 b5551 b5552 d4100 d4923 d4875 d5506
        omega
      have d5553 : (x 2 2).toNat = 1 := by
        have r5554 := hand1 (x 2 2) (x 2 13)
        have b5555 := hb (x 2 2)
        have b5556 := hb (x 2 2 && x 2 13)
        clear * - r5554 b5555 b5556 d5546
        omega
      have d5557 : (x 2 3).toNat = 1 := by
        have r5558 : (x 2 2).toNat = (x 2 3).toNat := congrArg Bool.toNat (h23 2)
        have b5559 := hb (x 2 2)
        have b5560 := hb (x 2 3)
        clear * - r5558 b5559 b5560 d5553
        omega
      have d5561 : (x 5 12).toNat = 0 := by
        have r5562 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5563 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e5564 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b5565 := hb (x 2 3)
        have b5566 := hb (x 3 2)
        have b5567 := hb (x 4 13)
        have b5568 := hb (x 5 12)
        clear * - r5562 e5563 e5564 b5565 b5566 b5567 b5568 d5103 d5557
        omega
      have d5569 : (x 4 13).toNat = 0 := by
        have r5570 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5571 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e5572 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b5573 := hb (x 2 3)
        have b5574 := hb (x 3 2)
        have b5575 := hb (x 4 13)
        have b5576 := hb (x 5 12)
        clear * - r5570 e5571 e5572 b5573 b5574 b5575 b5576 d5561 d5103 d5557
        omega
      have d5577 : (x 4 3 && x 4 13).toNat = 0 := by
        have r5578 := hand2 (x 4 3) (x 4 13)
        have b5579 := hb (x 4 13)
        have b5580 := hb (x 4 3 && x 4 13)
        clear * - r5578 b5579 b5580 d5569
        omega
      have d5581 : (x 4 12).toNat = 0 := by
        have r5582 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5583 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e5584 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b5585 := hb (x 1 3)
        have b5586 := hb (x 2 2)
        have b5587 := hb (x 3 13)
        have b5588 := hb (x 4 12)
        clear * - r5582 e5583 e5584 b5585 b5586 b5587 b5588 d4931 d5553 d5123
        omega
      have d5589 : (x 4 3 && x 4 12).toNat = 0 := by
        have r5590 := hand2 (x 4 3) (x 4 12)
        have b5591 := hb (x 4 12)
        have b5592 := hb (x 4 3 && x 4 12)
        clear * - r5590 b5591 b5592 d5581
        omega
      have d5593 : (x 4 4).toNat = 0 := by
        have r5594 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
        have b5595 := hb (x 4 4)
        have b5596 := hb (x 4 12)
        clear * - r5594 b5595 b5596 d5581
        omega
      have d5597 : (x 6 1 && x 6 11).toNat = 1 := by
        have r5598 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b5599 := hb (x 2 5)
        have b5600 := hb (x 7 10)
        have b5601 := hb (x 6 1 && x 6 11)
        have b5602 := hb (x 5 2 && x 5 12)
        have b5603 := hb (x 4 3 && x 4 13)
        have b5604 := hb (x 3 4 && x 3 14)
        clear * - r5598 b5599 b5600 b5601 b5602 b5603 b5604 d5063 d5075 d5577 d4148 d4168
        omega
      have d5605 : (x 6 11).toNat = 1 := by
        have r5606 := hand2 (x 6 1) (x 6 11)
        have b5607 := hb (x 6 11)
        have b5608 := hb (x 6 1 && x 6 11)
        clear * - r5606 b5607 b5608 d5597
        omega
      have d5609 : (x 6 3).toNat = 1 := by
        have r5610 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
        have b5611 := hb (x 6 3)
        have b5612 := hb (x 6 11)
        clear * - r5610 b5611 b5612 d5605
        omega
      have d5613 : (x 6 2).toNat = 1 := by
        have r5614 : (x 6 2).toNat = (x 6 3).toNat := congrArg Bool.toNat (h23 6)
        have b5615 := hb (x 6 2)
        have b5616 := hb (x 6 3)
        clear * - r5614 b5615 b5616 d5609
        omega
      have d5617 : (x 8 12).toNat = 0 := by
        have r5618 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5619 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e5620 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have b5621 := hb (x 5 3)
        have b5622 := hb (x 6 2)
        have b5623 := hb (x 7 13)
        have b5624 := hb (x 8 12)
        clear * - r5618 e5619 e5620 b5621 b5622 b5623 b5624 d4995 d5613 d5091
        omega
      have d5625 : (x 8 4).toNat = 0 := by
        have r5626 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
        have b5627 := hb (x 8 4)
        have b5628 := hb (x 8 12)
        clear * - r5626 b5627 b5628 d5617
        omega
      have d5629 : (x 9 12).toNat = 0 := by
        have r5630 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5631 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
        have e5632 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
        have b5633 := hb (x 6 3)
        have b5634 := hb (x 7 2)
        have b5635 := hb (x 8 13)
        have b5636 := hb (x 9 12)
        clear * - r5630 e5631 e5632 b5633 b5634 b5635 b5636 d5059 d5609
        omega
      have d5637 : (x 9 4).toNat = 0 := by
        have r5638 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
        have b5639 := hb (x 9 4)
        have b5640 := hb (x 9 12)
        clear * - r5638 b5639 b5640 d5629
        omega
      have d5641 : (x 8 13).toNat = 0 := by
        have r5642 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5643 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
        have e5644 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
        have b5645 := hb (x 6 3)
        have b5646 := hb (x 7 2)
        have b5647 := hb (x 8 13)
        have b5648 := hb (x 9 12)
        clear * - r5642 e5643 e5644 b5645 b5646 b5647 b5648 d5629 d5059 d5609
        omega
      have d5649 : (x 8 3 && x 8 13).toNat = 0 := by
        have r5650 := hand2 (x 8 3) (x 8 13)
        have b5651 := hb (x 8 13)
        have b5652 := hb (x 8 3 && x 8 13)
        clear * - r5650 b5651 b5652 d5641
        omega
      have d5653 : (x 8 5).toNat = 0 := by
        have r5654 : (x 8 5).toNat ≤ (x 8 13).toNat := himp _ _ (hp5 8)
        have b5655 := hb (x 8 5)
        have b5656 := hb (x 8 13)
        clear * - r5654 b5655 b5656 d5641
        omega
      have d5657 : (x 6 1 && x 6 10).toNat = 1 := by
        have r5658 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b5659 := hb (x 1 6)
        have b5660 := hb (x 7 9)
        have b5661 := hb (x 6 1 && x 6 10)
        have b5662 := hb (x 5 2 && x 5 11)
        have b5663 := hb (x 4 3 && x 4 12)
        have b5664 := hb (x 3 4 && x 3 13)
        have b5665 := hb (x 2 5 && x 2 14)
        clear * - r5658 b5659 b5660 b5661 b5662 b5663 b5664 b5665 d5003 d5079 d5589 d4152 d4184 d4200
        omega
      have d5666 : (x 6 10).toNat = 1 := by
        have r5667 := hand2 (x 6 1) (x 6 10)
        have b5668 := hb (x 6 10)
        have b5669 := hb (x 6 1 && x 6 10)
        clear * - r5667 b5668 b5669 d5657
        omega
      have d5670 : (x 8 8).toNat = 0 := by
        have r5671 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5672 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e5673 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e5674 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e5675 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e5676 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e5677 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b5678 := hb (x 1 7)
        have b5679 := hb (x 2 6)
        have b5680 := hb (x 3 5)
        have b5681 := hb (x 4 4)
        have b5682 := hb (x 5 11)
        have b5683 := hb (x 6 10)
        have b5684 := hb (x 7 9)
        have b5685 := hb (x 8 8)
        clear * - r5671 e5672 e5673 e5674 e5675 e5676 e5677 b5678 b5679 b5680 b5681 b5682 b5683 b5684 b5685 d5003 d5666 d5095 d5593 d4935
        omega
      have d5686 : (x 2 6).toNat = 0 := by
        have r5687 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5688 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e5689 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e5690 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e5691 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e5692 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e5693 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b5694 := hb (x 1 7)
        have b5695 := hb (x 2 6)
        have b5696 := hb (x 3 5)
        have b5697 := hb (x 4 4)
        have b5698 := hb (x 5 11)
        have b5699 := hb (x 6 10)
        have b5700 := hb (x 7 9)
        have b5701 := hb (x 8 8)
        clear * - r5687 e5688 e5689 e5690 e5691 e5692 e5693 b5694 b5695 b5696 b5697 b5698 b5699 b5700 b5701 d5670 d5003 d5666 d5095 d5593 d4935
        omega
      have d5702 : (x 2 6 && x 2 13).toNat = 0 := by
        have r5703 := hand1 (x 2 6) (x 2 13)
        have b5704 := hb (x 2 6)
        have b5705 := hb (x 2 6 && x 2 13)
        clear * - r5703 b5704 b5705 d5686
        omega
      have d5706 : (x 2 2 && x 2 6).toNat = 0 := by
        have r5707 := hand2 (x 2 2) (x 2 6)
        have b5708 := hb (x 2 6)
        have b5709 := hb (x 2 2 && x 2 6)
        clear * - r5707 b5708 b5709 d5686
        omega
      have r5710 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r5711 : (x 6 1).toNat + (x 5 2).toNat + (x 4 3).toNat + (x 3 4).toNat + (x 2 5).toNat + (x 1 6).toNat + (x 0 7).toNat + (x (-1) 8).toNat + (x (-2) 9).toNat + (x (-3) 10).toNat + (x (-4) 11).toNat + (x (-5) 12).toNat + (x (-6) 13).toNat + (x (-7) 14).toNat = 3 := by have q := hcount 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r5712 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r5713 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r5714 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5715 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
      have e5716 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
      have e5717 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
      have e5718 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
      have e5719 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
      have e5720 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
      have r5721 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5722 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
      have e5723 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
      have e5724 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
      have e5725 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
      have e5726 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
      have e5727 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
      have r5728 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5729 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
      have e5730 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
      have e5731 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
      have e5732 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
      have e5733 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
      have e5734 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
      have r5735 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5736 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e5737 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e5738 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e5739 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e5740 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e5741 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have r5742 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5743 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
      have e5744 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
      have r5745 : 1 ≤ (x 11 4).toNat + (x 10 1 && x 10 5).toNat + (x 9 2 && x 9 6).toNat + (x 8 3 && x 8 7).toNat + (x 7 4 && x 7 8).toNat + (x 6 5 && x 6 9).toNat + (x 5 6 && x 5 10).toNat + (x 4 7 && x 4 11).toNat + (x 3 8 && x 3 12).toNat + (x 2 9 && x 2 13).toNat + (x 1 10 && x 1 14).toNat + (x 0 11).toNat := by have q := hcov4 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5746 : (x 10 1 && x 10 5).toNat = (x 10 5).toNat := handr _ _ (fun h => hp13 10 (hp5 10 (h)))
      have e5747 : (x 1 10 && x 1 14).toNat = (x 1 10).toNat := handl _ _ (fun h => hp2 1 (hp10 1 (h)))
      have r5748 : 1 ≤ (x 7 5).toNat + (x 6 1 && x 6 6).toNat + (x 5 2 && x 5 7).toNat + (x 4 3 && x 4 8).toNat + (x 3 4 && x 3 9).toNat + (x 2 5 && x 2 10).toNat + (x 1 6 && x 1 11).toNat + (x 0 7 && x 0 12).toNat + (x (-1) 8 && x (-1) 13).toNat + (x (-2) 9 && x (-2) 14).toNat + (x (-3) 10).toNat := by have q := hcov5 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r5749 : 1 ≤ (x 7 6).toNat + (x 6 1 && x 6 7).toNat + (x 5 2 && x 5 8).toNat + (x 4 3 && x 4 9).toNat + (x 3 4 && x 3 10).toNat + (x 2 5 && x 2 11).toNat + (x 1 6 && x 1 12).toNat + (x 0 7 && x 0 13).toNat + (x (-1) 8 && x (-1) 14).toNat + (x (-2) 9).toNat := by have q := hcov6 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r5750 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := by have q := hcov7 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r5751 : 1 ≤ (x 11 10).toNat + (x 10 1 && x 10 11).toNat + (x 9 2 && x 9 12).toNat + (x 8 3 && x 8 13).toNat + (x 7 4 && x 7 14).toNat + (x 6 5).toNat := by have q := hcov10 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r5752 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r5753 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r5754 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r5755 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
      have r5756 := hand1 (x (-2) 6) (x (-2) 10)
      have r5757 := hand2 (x (-2) 6) (x (-2) 10)
      have r5758 := hand1 (x (-4) 8) (x (-4) 12)
      have r5759 := hand1 (x 8 3) (x 8 7)
      have r5760 := hand1 (x 2 9) (x 2 13)
      have r5761 := hand2 (x 6 1) (x 6 6)
      have r5762 := hand1 (x 4 3) (x 4 8)
      have r5763 := hand1 (x (-2) 9) (x (-2) 14)
      have r5764 := hand2 (x 6 1) (x 6 7)
      have r5765 := hand1 (x 4 3) (x 4 9)
      have r5766 := hand2 (x 10 1) (x 10 11)
      have r5767 := hand2 (x (-6) 2) (x (-6) 13)
      have r5768 := hand2 (x (-2) 2) (x (-2) 13)
      have r5769 := hand1 (x 11 1) (x 11 12)
      have r5770 := hand1 (x 10 2) (x 10 13)
      have b5771 := hb (x (-10) 14)
      have b5772 := hb (x (-9) 13)
      have b5773 := hb (x (-8) 4)
      have b5774 := hb (x (-8) 12)
      have b5775 := hb (x (-7) 7)
      have b5776 := hb (x (-7) 11)
      have b5777 := hb (x (-7) 14)
      have b5778 := hb (x (-6) 6)
      have b5779 := hb (x (-6) 10)
      have b5780 := hb (x (-6) 13)
      have b5781 := hb (x (-5) 5)
      have b5782 := hb (x (-5) 9)
      have b5783 := hb (x (-5) 12)
      have b5784 := hb (x (-4) 4)
      have b5785 := hb (x (-4) 8)
      have b5786 := hb (x (-4) 11)
      have b5787 := hb (x (-3) 7)
      have b5788 := hb (x (-3) 10)
      have b5789 := hb (x (-3) 11)
      have b5790 := hb (x (-3) 14)
      have b5791 := hb (x (-2) 6)
      have b5792 := hb (x (-2) 9)
      have b5793 := hb (x (-2) 10)
      have b5794 := hb (x (-2) 13)
      have b5795 := hb (x (-2) 14)
      have b5796 := hb (x (-1) 5)
      have b5797 := hb (x (-1) 8)
      have b5798 := hb (x (-1) 9)
      have b5799 := hb (x (-1) 12)
      have b5800 := hb (x (-1) 13)
      have b5801 := hb (x 0 4)
      have b5802 := hb (x 0 7)
      have b5803 := hb (x 0 8)
      have b5804 := hb (x 0 11)
      have b5805 := hb (x 0 12)
      have b5806 := hb (x 1 3)
      have b5807 := hb (x 1 6)
      have b5808 := hb (x 1 10)
      have b5809 := hb (x 1 11)
      have b5810 := hb (x 2 2)
      have b5811 := hb (x 2 5)
      have b5812 := hb (x 2 9)
      have b5813 := hb (x 2 10)
      have b5814 := hb (x 3 1)
      have b5815 := hb (x 3 4)
      have b5816 := hb (x 3 5)
      have b5817 := hb (x 3 8)
      have b5818 := hb (x 3 9)
      have b5819 := hb (x 4 3)
      have b5820 := hb (x 4 4)
      have b5821 := hb (x 4 7)
      have b5822 := hb (x 4 8)
      have b5823 := hb (x 5 2)
      have b5824 := hb (x 5 6)
      have b5825 := hb (x 5 7)
      have b5826 := hb (x 6 1)
      have b5827 := hb (x 6 5)
      have b5828 := hb (x 6 6)
      have b5829 := hb (x 6 7)
      have b5830 := hb (x 7 4)
      have b5831 := hb (x 7 5)
      have b5832 := hb (x 7 6)
      have b5833 := hb (x 8 3)
      have b5834 := hb (x 8 4)
      have b5835 := hb (x 8 5)
      have b5836 := hb (x 8 7)
      have b5837 := hb (x 9 2)
      have b5838 := hb (x 9 3)
      have b5839 := hb (x 9 4)
      have b5840 := hb (x 9 6)
      have b5841 := hb (x 10 1)
      have b5842 := hb (x 10 2)
      have b5843 := hb (x 10 5)
      have b5844 := hb (x 10 11)
      have b5845 := hb (x 11 1)
      have b5846 := hb (x 11 4)
      have b5847 := hb (x 11 10)
      have b5848 := hb (x 12 9)
      have b5849 := hb (x 12 11)
      have b5850 := hb (x 13 8)
      have b5851 := hb (x 13 10)
      have b5852 := hb (x 14 9)
      have b5853 := hb (x 15 8)
      have b5854 := hb (x 2 2 && x 2 6)
      have b5855 := hb (x 1 3 && x 1 7)
      have b5856 := hb (x 0 4 && x 0 8)
      have b5857 := hb (x (-1) 5 && x (-1) 9)
      have b5858 := hb (x (-2) 6 && x (-2) 10)
      have b5859 := hb (x (-3) 7 && x (-3) 11)
      have b5860 := hb (x (-4) 8 && x (-4) 12)
      have b5861 := hb (x (-5) 9 && x (-5) 13)
      have b5862 := hb (x 9 2 && x 9 6)
      have b5863 := hb (x 8 3 && x 8 7)
      have b5864 := hb (x 7 4 && x 7 8)
      have b5865 := hb (x 6 5 && x 6 9)
      have b5866 := hb (x 5 6 && x 5 10)
      have b5867 := hb (x 4 7 && x 4 11)
      have b5868 := hb (x 3 8 && x 3 12)
      have b5869 := hb (x 2 9 && x 2 13)
      have b5870 := hb (x 6 1 && x 6 6)
      have b5871 := hb (x 5 2 && x 5 7)
      have b5872 := hb (x 4 3 && x 4 8)
      have b5873 := hb (x 3 4 && x 3 9)
      have b5874 := hb (x 2 5 && x 2 10)
      have b5875 := hb (x 1 6 && x 1 11)
      have b5876 := hb (x 0 7 && x 0 12)
      have b5877 := hb (x (-1) 8 && x (-1) 13)
      have b5878 := hb (x (-2) 9 && x (-2) 14)
      have b5879 := hb (x 6 1 && x 6 7)
      have b5880 := hb (x 5 2 && x 5 8)
      have b5881 := hb (x 4 3 && x 4 9)
      have b5882 := hb (x 3 4 && x 3 10)
      have b5883 := hb (x 2 5 && x 2 11)
      have b5884 := hb (x 1 6 && x 1 12)
      have b5885 := hb (x 0 7 && x 0 13)
      have b5886 := hb (x (-1) 8 && x (-1) 14)
      have b5887 := hb (x 7 1 && x 7 8)
      have b5888 := hb (x 6 2 && x 6 9)
      have b5889 := hb (x 5 3 && x 5 10)
      have b5890 := hb (x 4 4 && x 4 11)
      have b5891 := hb (x 3 5 && x 3 12)
      have b5892 := hb (x 2 6 && x 2 13)
      have b5893 := hb (x 1 7 && x 1 14)
      have b5894 := hb (x 10 1 && x 10 11)
      have b5895 := hb (x 9 2 && x 9 12)
      have b5896 := hb (x 8 3 && x 8 13)
      have b5897 := hb (x 7 4 && x 7 14)
      have b5898 := hb (x (-5) 1 && x (-5) 12)
      have b5899 := hb (x (-6) 2 && x (-6) 13)
      have b5900 := hb (x (-7) 3 && x (-7) 14)
      have b5901 := hb (x (-1) 1 && x (-1) 12)
      have b5902 := hb (x (-2) 2 && x (-2) 13)
      have b5903 := hb (x (-3) 3 && x (-3) 14)
      have b5904 := hb (x 11 1 && x 11 12)
      have b5905 := hb (x 10 2 && x 10 13)
      have b5906 := hb (x 9 3 && x 9 14)
      linarith only [r5710, r5711, r5712, r5713, r5714, e5715, e5716, e5717, e5718, e5719, e5720, r5721, e5722, e5723, e5724, e5725, e5726, e5727, r5728, e5729, e5730, e5731, e5732, e5733, e5734, r5735, e5736, e5737, e5738, e5739, e5740, e5741, r5742, e5743, e5744, r5745, e5746, e5747, r5748, r5749, r5750, r5751, r5752, r5753, r5754, r5755, r5756, r5757, r5758, r5759, r5760, r5761, r5762, r5763, r5764, r5765, r5766, r5767, r5768, r5769, r5770, b5771, b5772, b5773, b5774, b5775, b5776, b5777, b5778, b5779, b5780, b5781, b5782, b5783, b5784, b5785, b5786, b5787, b5788, b5789, b5790, b5791, b5792, b5793, b5794, b5795, b5796, b5797, b5798, b5799, b5800, b5801, b5802, b5803, b5804, b5805, b5806, b5807, b5808, b5809, b5810, b5811, b5812, b5813, b5814, b5815, b5816, b5817, b5818, b5819, b5820, b5821, b5822, b5823, b5824, b5825, b5826, b5827, b5828, b5829, b5830, b5831, b5832, b5833, b5834, b5835, b5836, b5837, b5838, b5839, b5840, b5841, b5842, b5843, b5844, b5845, b5846, b5847, b5848, b5849, b5850, b5851, b5852, b5853, b5854, b5855, b5856, b5857, b5858, b5859, b5860, b5861, b5862, b5863, b5864, b5865, b5866, b5867, b5868, b5869, b5870, b5871, b5872, b5873, b5874, b5875, b5876, b5877, b5878, b5879, b5880, b5881, b5882, b5883, b5884, b5885, b5886, b5887, b5888, b5889, b5890, b5891, b5892, b5893, b5894, b5895, b5896, b5897, b5898, b5899, b5900, b5901, b5902, b5903, b5904, b5905, b5906, d5395, d5383, d5359, d5339, d5319, d5323, d5247, d5239, d5219, d5207, d5191, d5199, d5179, d5506, g1, d5440, f5501, d5123, d4200, d5139, d5135, d5553, d4168, d4919, d4132, d4935, d4943, d5593, d5071, d5067, d4979, d4999, d5055, d5625, d5653, d5043, d5051, d5637, d5035, d5031, d5706, d5131, d5510, d5195, d5243, d5315, d5039, d4036, d4064, d4096, d4128, d5420, d5087, d4160, d4192, d4220, d5502, d5187, d5083, d4156, d4188, d4216, d5542, d5159, d4028, d4056, d4088, d4120, d4939, d5702, d4883, d5047, d5649, d4987, d5275, d5343, d5147, d5223, d5019]
    · have f5907 : (x 0 12).toNat = 1 := by rw [h5500]; rfl
      have d5908 : (x (-2) 2).toNat = 0 := by
        have r5909 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5910 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
        have e5911 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
        have b5912 := hb (x (-3) 3)
        have b5913 := hb (x (-2) 2)
        have b5914 := hb (x (-1) 13)
        have b5915 := hb (x 0 12)
        clear * - r5909 e5910 e5911 b5912 b5913 b5914 b5915 f5907 d5179 d5235
        omega
      have d5916 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
        have r5917 := hand1 (x (-2) 2) (x (-2) 13)
        have b5918 := hb (x (-2) 2)
        have b5919 := hb (x (-2) 2 && x (-2) 13)
        clear * - r5917 b5918 b5919 d5908
        omega
      have d5920 : (x (-2) 3).toNat = 0 := by
        have r5921 : (x (-2) 2).toNat = (x (-2) 3).toNat := congrArg Bool.toNat (h23 (-2))
        have b5922 := hb (x (-2) 2)
        have b5923 := hb (x (-2) 3)
        clear * - r5921 b5922 b5923 d5908
        omega
      have d5924 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
        have r5925 := hand1 (x (-2) 3) (x (-2) 13)
        have b5926 := hb (x (-2) 3)
        have b5927 := hb (x (-2) 3 && x (-2) 13)
        clear * - r5925 b5926 b5927 d5920
        omega
      have d5928 : (x (-2) 11).toNat = 0 := by
        have r5929 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
        have b5930 := hb (x (-2) 3)
        have b5931 := hb (x (-2) 11)
        clear * - r5929 b5930 b5931 d5920
        omega
      have d5932 : (x (-2) 6 && x (-2) 11).toNat = 0 := by
        have r5933 := hand2 (x (-2) 6) (x (-2) 11)
        have b5934 := hb (x (-2) 11)
        have b5935 := hb (x (-2) 6 && x (-2) 11)
        clear * - r5933 b5934 b5935 d5928
        omega
      have d5936 : (x (-2) 10).toNat = 0 := by
        have r5937 : (x (-2) 10).toNat ≤ (x (-2) 2).toNat := himp _ _ (hp10 (-2))
        have b5938 := hb (x (-2) 2)
        have b5939 := hb (x (-2) 10)
        clear * - r5937 b5938 b5939 d5908
        omega
      have d5940 : (x (-4) 4).toNat = 1 := by
        have r5941 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b5942 := hb (x (-4) 4)
        have b5943 := hb (x 0 11)
        have b5944 := hb (x (-1) 1 && x (-1) 12)
        have b5945 := hb (x (-2) 2 && x (-2) 13)
        have b5946 := hb (x (-3) 3 && x (-3) 14)
        clear * - r5941 b5942 b5943 b5944 b5945 b5946 d5440 d5147 d5916 d5223
        omega
      have d5947 : (x (-4) 12).toNat = 1 := by
        have r5948 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
        have b5949 := hb (x (-4) 4)
        have b5950 := hb (x (-4) 12)
        clear * - r5948 b5949 b5950 d5940
        omega
      have d5951 : (x (-6) 2).toNat = 0 := by
        have r5952 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5953 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e5954 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have b5955 := hb (x (-7) 3)
        have b5956 := hb (x (-6) 2)
        have b5957 := hb (x (-5) 13)
        have b5958 := hb (x (-4) 12)
        clear * - r5952 e5953 e5954 b5955 b5956 b5957 b5958 d5947 d5311 d5351
        omega
      have d5959 : (x (-6) 2 && x (-6) 12).toNat = 0 := by
        have r5960 := hand1 (x (-6) 2) (x (-6) 12)
        have b5961 := hb (x (-6) 2)
        have b5962 := hb (x (-6) 2 && x (-6) 12)
        clear * - r5960 b5961 b5962 d5951
        omega
      have d5963 : (x (-6) 3).toNat = 0 := by
        have r5964 : (x (-6) 2).toNat = (x (-6) 3).toNat := congrArg Bool.toNat (h23 (-6))
        have b5965 := hb (x (-6) 2)
        have b5966 := hb (x (-6) 3)
        clear * - r5964 b5965 b5966 d5951
        omega
      have d5967 : (x (-6) 10).toNat = 0 := by
        have r5968 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
        have b5969 := hb (x (-6) 2)
        have b5970 := hb (x (-6) 10)
        clear * - r5968 b5969 b5970 d5951
        omega
      have d5971 : (x (-4) 13).toNat = 1 := by
        have r5972 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b5973 := hb (x (-6) 2)
        have b5974 := hb (x (-4) 13)
        have b5975 := hb (x (-5) 1 && x (-5) 14)
        clear * - r5972 b5973 b5974 b5975 d5271 d5951
        omega
      have d5976 : (x (-3) 12).toNat = 0 := by
        have r5977 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5978 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
        have e5979 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
        have b5980 := hb (x (-6) 3)
        have b5981 := hb (x (-5) 2)
        have b5982 := hb (x (-4) 13)
        have b5983 := hb (x (-3) 12)
        clear * - r5977 e5978 e5979 b5980 b5981 b5982 b5983 d5971 d5299 d5963
        omega
      have d5984 : (x (-3) 7 && x (-3) 12).toNat = 0 := by
        have r5985 := hand2 (x (-3) 7) (x (-3) 12)
        have b5986 := hb (x (-3) 12)
        have b5987 := hb (x (-3) 7 && x (-3) 12)
        clear * - r5985 b5986 b5987 d5976
        omega
      have d5988 : (x (-3) 4).toNat = 0 := by
        have r5989 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
        have b5990 := hb (x (-3) 4)
        have b5991 := hb (x (-3) 12)
        clear * - r5989 b5990 b5991 d5976
        omega
      have d5992 : (x (-4) 5).toNat = 1 := by
        have r5993 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b5994 := hb (x (-4) 5)
        have b5995 := hb (x 1 10)
        have b5996 := hb (x 0 1 && x 0 11)
        have b5997 := hb (x (-1) 2 && x (-1) 12)
        have b5998 := hb (x (-2) 3 && x (-2) 13)
        have b5999 := hb (x (-3) 4 && x (-3) 14)
        clear * - r5993 b5994 b5995 b5996 b5997 b5998 b5999 d5139 d5444 d5167 d5924 d5227
        omega
      have d6000 : (x 1 8).toNat = 0 := by
        have r6001 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6002 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
        have e6003 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
        have e6004 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
        have e6005 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
        have e6006 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
        have e6007 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
        have b6008 := hb (x (-6) 7)
        have b6009 := hb (x (-5) 6)
        have b6010 := hb (x (-4) 5)
        have b6011 := hb (x (-3) 4)
        have b6012 := hb (x (-2) 11)
        have b6013 := hb (x (-1) 10)
        have b6014 := hb (x 0 9)
        have b6015 := hb (x 1 8)
        clear * - r6001 e6002 e6003 e6004 e6005 e6006 e6007 b6008 b6009 b6010 b6011 b6012 b6013 b6014 b6015 d5171 d5928 d5988 d5992 d5295
        omega
      have d6016 : (x 0 9).toNat = 0 := by
        have r6017 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6018 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
        have e6019 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
        have e6020 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
        have e6021 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
        have e6022 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
        have e6023 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
        have b6024 := hb (x (-6) 7)
        have b6025 := hb (x (-5) 6)
        have b6026 := hb (x (-4) 5)
        have b6027 := hb (x (-3) 4)
        have b6028 := hb (x (-2) 11)
        have b6029 := hb (x (-1) 10)
        have b6030 := hb (x 0 9)
        have b6031 := hb (x 1 8)
        clear * - r6017 e6018 e6019 e6020 e6021 e6022 e6023 b6024 b6025 b6026 b6027 b6028 b6029 b6030 b6031 d6000 d5171 d5928 d5988 d5992 d5295
        omega
      have d6032 : (x 0 4 && x 0 9).toNat = 0 := by
        have r6033 := hand2 (x 0 4) (x 0 9)
        have b6034 := hb (x 0 9)
        have b6035 := hb (x 0 4 && x 0 9)
        clear * - r6033 b6034 b6035 d6016
        omega
      have d6036 : (x 0 8).toNat = 0 := by
        have r6037 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6038 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
        have e6039 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
        have e6040 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
        have e6041 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
        have e6042 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
        have e6043 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
        have b6044 := hb (x (-7) 7)
        have b6045 := hb (x (-6) 6)
        have b6046 := hb (x (-5) 5)
        have b6047 := hb (x (-4) 4)
        have b6048 := hb (x (-3) 11)
        have b6049 := hb (x (-2) 10)
        have b6050 := hb (x (-1) 9)
        have b6051 := hb (x 0 8)
        clear * - r6037 e6038 e6039 e6040 e6041 e6042 e6043 b6044 b6045 b6046 b6047 b6048 b6049 b6050 b6051 d5199 d5936 d5239 d5940 d5319
        omega
      have r6052 : (x 5 1).toNat + (x 4 2).toNat + (x 3 3).toNat + (x 2 4).toNat + (x 1 5).toNat + (x 0 6).toNat + (x (-1) 7).toNat + (x (-2) 8).toNat + (x (-3) 9).toNat + (x (-4) 10).toNat + (x (-5) 11).toNat + (x (-6) 12).toNat + (x (-7) 13).toNat + (x (-8) 14).toNat = 3 := by have q := hcount 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r6053 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r6054 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6055 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
      have e6056 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
      have e6057 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
      have e6058 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
      have e6059 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
      have e6060 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
      have r6061 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6062 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e6063 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e6064 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e6065 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e6066 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e6067 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have r6068 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6069 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
      have e6070 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
      have e6071 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
      have e6072 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
      have e6073 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
      have e6074 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
      have r6075 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6076 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e6077 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e6078 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e6079 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e6080 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e6081 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have r6082 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6083 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e6084 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have r6085 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6086 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e6087 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have r6088 : (x 4 2).toNat = (x 4 3).toNat := congrArg Bool.toNat (h23 4)
      have r6089 : 1 ≤ (x 4 5).toNat + (x 3 1 && x 3 6).toNat + (x 2 2 && x 2 7).toNat + (x 1 3 && x 1 8).toNat + (x 0 4 && x 0 9).toNat + (x (-1) 5 && x (-1) 10).toNat + (x (-2) 6 && x (-2) 11).toNat + (x (-3) 7 && x (-3) 12).toNat + (x (-4) 8 && x (-4) 13).toNat + (x (-5) 9 && x (-5) 14).toNat + (x (-6) 10).toNat := by have q := hcov5 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r6090 : 1 ≤ (x 6 6).toNat + (x 5 1 && x 5 7).toNat + (x 4 2 && x 4 8).toNat + (x 3 3 && x 3 9).toNat + (x 2 4 && x 2 10).toNat + (x 1 5 && x 1 11).toNat + (x 0 6 && x 0 12).toNat + (x (-1) 7 && x (-1) 13).toNat + (x (-2) 8 && x (-2) 14).toNat + (x (-3) 9).toNat := by have q := hcov6 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r6091 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := by have q := hcov7 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r6092 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r6093 : 1 ≤ (x (-4) 10).toNat + (x (-5) 1 && x (-5) 11).toNat + (x (-6) 2 && x (-6) 12).toNat + (x (-7) 3 && x (-7) 13).toNat + (x (-8) 4 && x (-8) 14).toNat + (x (-9) 5).toNat := by have q := hcov10 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r6094 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r6095 : 1 ≤ (x (-2) 11).toNat + (x (-3) 1 && x (-3) 12).toNat + (x (-4) 2 && x (-4) 13).toNat + (x (-5) 3 && x (-5) 14).toNat + (x (-6) 4).toNat := by have q := hcov11 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r6096 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := by have q := hcov11 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r6097 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r6098 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
      have r6099 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
      have r6100 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
      have r6101 := hand2 (x 2 2) (x 2 7)
      have r6102 := hand1 (x (-4) 8) (x (-4) 13)
      have r6103 := hand2 (x 4 2) (x 4 8)
      have r6104 := hand2 (x 2 4) (x 2 10)
      have r6105 := hand1 (x (-2) 8) (x (-2) 14)
      have r6106 := hand1 (x 2 6) (x 2 13)
      have r6107 := hand2 (x 6 1) (x 6 10)
      have r6108 := hand1 (x 4 3) (x 4 12)
      have r6109 := hand1 (x (-8) 4) (x (-8) 14)
      have r6110 := hand2 (x 6 1) (x 6 11)
      have r6111 := hand2 (x 4 3) (x 4 13)
      have r6112 := hand1 (x (-4) 2) (x (-4) 13)
      have r6113 := hand1 (x 11 1) (x 11 12)
      have r6114 := hand1 (x 10 2) (x 10 13)
      have b6115 := hb (x (-11) 7)
      have b6116 := hb (x (-10) 6)
      have b6117 := hb (x (-9) 5)
      have b6118 := hb (x (-8) 4)
      have b6119 := hb (x (-8) 14)
      have b6120 := hb (x (-7) 11)
      have b6121 := hb (x (-7) 13)
      have b6122 := hb (x (-6) 4)
      have b6123 := hb (x (-6) 10)
      have b6124 := hb (x (-6) 12)
      have b6125 := hb (x (-5) 3)
      have b6126 := hb (x (-5) 9)
      have b6127 := hb (x (-5) 11)
      have b6128 := hb (x (-4) 2)
      have b6129 := hb (x (-4) 8)
      have b6130 := hb (x (-4) 10)
      have b6131 := hb (x (-3) 9)
      have b6132 := hb (x (-3) 13)
      have b6133 := hb (x (-2) 4)
      have b6134 := hb (x (-2) 8)
      have b6135 := hb (x (-2) 11)
      have b6136 := hb (x (-2) 12)
      have b6137 := hb (x (-2) 14)
      have b6138 := hb (x (-1) 7)
      have b6139 := hb (x (-1) 13)
      have b6140 := hb (x 0 6)
      have b6141 := hb (x 0 8)
      have b6142 := hb (x 0 12)
      have b6143 := hb (x 1 5)
      have b6144 := hb (x 1 6)
      have b6145 := hb (x 1 7)
      have b6146 := hb (x 1 11)
      have b6147 := hb (x 2 3)
      have b6148 := hb (x 2 4)
      have b6149 := hb (x 2 5)
      have b6150 := hb (x 2 6)
      have b6151 := hb (x 2 7)
      have b6152 := hb (x 2 10)
      have b6153 := hb (x 2 11)
      have b6154 := hb (x 3 2)
      have b6155 := hb (x 3 3)
      have b6156 := hb (x 3 5)
      have b6157 := hb (x 3 6)
      have b6158 := hb (x 3 9)
      have b6159 := hb (x 4 2)
      have b6160 := hb (x 4 3)
      have b6161 := hb (x 4 4)
      have b6162 := hb (x 4 5)
      have b6163 := hb (x 4 8)
      have b6164 := hb (x 4 13)
      have b6165 := hb (x 5 1)
      have b6166 := hb (x 5 4)
      have b6167 := hb (x 5 7)
      have b6168 := hb (x 5 11)
      have b6169 := hb (x 5 12)
      have b6170 := hb (x 6 6)
      have b6171 := hb (x 6 10)
      have b6172 := hb (x 6 11)
      have b6173 := hb (x 7 5)
      have b6174 := hb (x 7 9)
      have b6175 := hb (x 7 10)
      have b6176 := hb (x 8 4)
      have b6177 := hb (x 8 7)
      have b6178 := hb (x 8 8)
      have b6179 := hb (x 8 9)
      have b6180 := hb (x 9 3)
      have b6181 := hb (x 9 6)
      have b6182 := hb (x 9 8)
      have b6183 := hb (x 10 2)
      have b6184 := hb (x 10 5)
      have b6185 := hb (x 11 1)
      have b6186 := hb (x 11 4)
      have b6187 := hb (x 12 11)
      have b6188 := hb (x 13 10)
      have b6189 := hb (x 14 9)
      have b6190 := hb (x 15 8)
      have b6191 := hb (x 3 1 && x 3 6)
      have b6192 := hb (x 2 2 && x 2 7)
      have b6193 := hb (x 1 3 && x 1 8)
      have b6194 := hb (x 0 4 && x 0 9)
      have b6195 := hb (x (-1) 5 && x (-1) 10)
      have b6196 := hb (x (-2) 6 && x (-2) 11)
      have b6197 := hb (x (-3) 7 && x (-3) 12)
      have b6198 := hb (x (-4) 8 && x (-4) 13)
      have b6199 := hb (x (-5) 9 && x (-5) 14)
      have b6200 := hb (x 5 1 && x 5 7)
      have b6201 := hb (x 4 2 && x 4 8)
      have b6202 := hb (x 3 3 && x 3 9)
      have b6203 := hb (x 2 4 && x 2 10)
      have b6204 := hb (x 1 5 && x 1 11)
      have b6205 := hb (x 0 6 && x 0 12)
      have b6206 := hb (x (-1) 7 && x (-1) 13)
      have b6207 := hb (x (-2) 8 && x (-2) 14)
      have b6208 := hb (x 7 1 && x 7 8)
      have b6209 := hb (x 6 2 && x 6 9)
      have b6210 := hb (x 5 3 && x 5 10)
      have b6211 := hb (x 4 4 && x 4 11)
      have b6212 := hb (x 3 5 && x 3 12)
      have b6213 := hb (x 2 6 && x 2 13)
      have b6214 := hb (x 1 7 && x 1 14)
      have b6215 := hb (x 6 1 && x 6 10)
      have b6216 := hb (x 5 2 && x 5 11)
      have b6217 := hb (x 4 3 && x 4 12)
      have b6218 := hb (x 3 4 && x 3 13)
      have b6219 := hb (x 2 5 && x 2 14)
      have b6220 := hb (x (-5) 1 && x (-5) 11)
      have b6221 := hb (x (-6) 2 && x (-6) 12)
      have b6222 := hb (x (-7) 3 && x (-7) 13)
      have b6223 := hb (x (-8) 4 && x (-8) 14)
      have b6224 := hb (x 6 1 && x 6 11)
      have b6225 := hb (x 5 2 && x 5 12)
      have b6226 := hb (x 4 3 && x 4 13)
      have b6227 := hb (x 3 4 && x 3 14)
      have b6228 := hb (x (-3) 1 && x (-3) 12)
      have b6229 := hb (x (-4) 2 && x (-4) 13)
      have b6230 := hb (x (-5) 3 && x (-5) 14)
      have b6231 := hb (x 1 1 && x 1 12)
      have b6232 := hb (x 0 2 && x 0 13)
      have b6233 := hb (x (-1) 3 && x (-1) 14)
      have b6234 := hb (x 11 1 && x 11 12)
      have b6235 := hb (x 10 2 && x 10 13)
      have b6236 := hb (x 9 3 && x 9 14)
      linarith only [r6052, r6053, r6054, e6055, e6056, e6057, e6058, e6059, e6060, r6061, e6062, e6063, e6064, e6065, e6066, e6067, r6068, e6069, e6070, e6071, e6072, e6073, e6074, r6075, e6076, e6077, e6078, e6079, e6080, e6081, r6082, e6083, e6084, r6085, e6086, e6087, r6088, r6089, r6090, r6091, r6092, r6093, r6094, r6095, r6096, r6097, r6098, r6099, r6100, r6101, r6102, r6103, r6104, r6105, r6106, r6107, r6108, r6109, r6110, r6111, r6112, r6113, r6114, b6115, b6116, b6117, b6118, b6119, b6120, b6121, b6122, b6123, b6124, b6125, b6126, b6127, b6128, b6129, b6130, b6131, b6132, b6133, b6134, b6135, b6136, b6137, b6138, b6139, b6140, b6141, b6142, b6143, b6144, b6145, b6146, b6147, b6148, b6149, b6150, b6151, b6152, b6153, b6154, b6155, b6156, b6157, b6158, b6159, b6160, b6161, b6162, b6163, b6164, b6165, b6166, b6167, b6168, b6169, b6170, b6171, b6172, b6173, b6174, b6175, b6176, b6177, b6178, b6179, b6180, b6181, b6182, b6183, b6184, b6185, b6186, b6187, b6188, b6189, b6190, b6191, b6192, b6193, b6194, b6195, b6196, b6197, b6198, b6199, b6200, b6201, b6202, b6203, b6204, b6205, b6206, b6207, b6208, b6209, b6210, b6211, b6212, b6213, b6214, b6215, b6216, b6217, b6218, b6219, b6220, b6221, b6222, b6223, b6224, b6225, b6226, b6227, b6228, b6229, b6230, b6231, b6232, b6233, b6234, b6235, b6236, d5387, d5371, d5359, d5363, d5967, d5303, d5323, d5307, d5255, d5251, d5928, d5207, d5484, d5179, g0, d6036, f5907, d4899, d4200, d5135, d5448, d4168, d5103, d5107, d4935, d5099, d4943, d4963, d5095, d4999, d5003, d5063, d5051, d5035, d4927, d5127, d6032, d5175, d5932, d5984, d5291, d4967, d4947, d4903, d4008, d5183, d4028, d4056, d4088, d4120, d4939, d4883, d5079, d4152, d4184, d5279, d5959, d5355, d5075, d4148, d5215, d5287, d4891, d5436, d5155, d5019]

theorem cycle_power_fifteen_tight_type_sequence_shape_rules_core_v60_71 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 6).toNat = 0) (g1 : (x 0 7).toNat = 1) : False := cycle_power_fifteen_tight_type_sequence_shape_rules_core_v60_71_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 h114 h23 g0 g1
