import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_shape_rules_core_v50_61

Topic: combinatorics   Node: efd0b0f904bf

Provenance: helper lemma. Research thread RT-1, open case k = 15 (m = 4) of OP-205 (arXiv:2610.15635, Theorems 1.3-1.4: eq(C_n^k) for k+1 = 2^m, n even, (k+1) not dividing n). Experiment 9757: on the integer window [-24, 24] the layer-free tight-class model leaves 13 class types at the centre, none with an island; on [-32, 32] the six types {0,15}, {0,1,14,15}, {0..3,12..15}, {0..7,12..15}, {0..3,8..15}, {0..15}.

Window refutation for k = 15: in the layer-free tight-class model on the integer line (x p j: the class starting at p contains p + j; inner count 3 per vertex, distances 14, 12, 8 covered exactly once, the other distances covered, classes closed under the tight-class parent map), with x p 1 = x p 14 and x p 2 = x p 3 everywhere, the class at 0 cannot have bit 5 = 0 and bit 6 = 1.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_shape_rules_core_v50_61_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 5).toNat = 0) (g1 : (x 0 6).toNat = 1) : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d3029 : (x 0 5 && x 0 14).toNat = 0 := by
    have r3030 := hand1 (x 0 5) (x 0 14)
    have b3031 := hb (x 0 5)
    have b3032 := hb (x 0 5 && x 0 14)
    clear * - r3030 b3031 b3032 g0
    omega
  have d3033 : (x 0 5 && x 0 12).toNat = 0 := by
    have r3034 := hand1 (x 0 5) (x 0 12)
    have b3035 := hb (x 0 5)
    have b3036 := hb (x 0 5 && x 0 12)
    clear * - r3034 b3035 b3036 g0
    omega
  have d3037 : (x 0 5 && x 0 6).toNat = 0 := by
    have r3038 := hand1 (x 0 5) (x 0 6)
    have b3039 := hb (x 0 5)
    have b3040 := hb (x 0 5 && x 0 6)
    clear * - r3038 b3039 b3040 g0
    omega
  have d3041 : (x 0 14).toNat = 1 := by
    have r3042 : (x 0 6).toNat ≤ (x 0 14).toNat := himp _ _ (hp6 0)
    have b3043 := hb (x 0 6)
    have b3044 := hb (x 0 14)
    clear * - r3042 b3043 b3044 g1
    omega
  have d3045 : (x 0 1).toNat = 1 := by
    have r3046 : (x 0 1).toNat = (x 0 14).toNat := congrArg Bool.toNat (h114 0)
    have b3047 := hb (x 0 1)
    have b3048 := hb (x 0 14)
    clear * - r3046 b3047 b3048 d3041
    omega
  have d3049 : (x 1 14).toNat = 0 := by
    have r3050 : (x 1 14).toNat + (x 0 1).toNat = 1 := by have q := hd14 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b3051 := hb (x 0 1)
    have b3052 := hb (x 1 14)
    clear * - r3050 b3051 b3052 d3045
    omega
  have d3053 : (x 1 1).toNat = 0 := by
    have r3054 : (x 1 1).toNat = (x 1 14).toNat := congrArg Bool.toNat (h114 1)
    have b3055 := hb (x 1 1)
    have b3056 := hb (x 1 14)
    clear * - r3054 b3055 b3056 d3049
    omega
  have d3057 : (x 1 13).toNat = 0 := by
    have r3058 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
    have b3059 := hb (x 1 1)
    have b3060 := hb (x 1 13)
    clear * - r3058 b3059 b3060 d3053
    omega
  have d3061 : (x 1 4 && x 1 13).toNat = 0 := by
    have r3062 := hand2 (x 1 4) (x 1 13)
    have b3063 := hb (x 1 13)
    have b3064 := hb (x 1 4 && x 1 13)
    clear * - r3062 b3063 b3064 d3057
    omega
  have d3065 : (x 1 7 && x 1 13).toNat = 0 := by
    have r3066 := hand2 (x 1 7) (x 1 13)
    have b3067 := hb (x 1 13)
    have b3068 := hb (x 1 7 && x 1 13)
    clear * - r3066 b3067 b3068 d3057
    omega
  have d3069 : (x 1 9 && x 1 13).toNat = 0 := by
    have r3070 := hand2 (x 1 9) (x 1 13)
    have b3071 := hb (x 1 13)
    have b3072 := hb (x 1 9 && x 1 13)
    clear * - r3070 b3071 b3072 d3057
    omega
  have d3073 : (x 1 5).toNat = 0 := by
    have r3074 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
    have b3075 := hb (x 1 5)
    have b3076 := hb (x 1 13)
    clear * - r3074 b3075 b3076 d3057
    omega
  have d3077 : (x 1 5 && x 1 11).toNat = 0 := by
    have r3078 := hand1 (x 1 5) (x 1 11)
    have b3079 := hb (x 1 5)
    have b3080 := hb (x 1 5 && x 1 11)
    clear * - r3078 b3079 b3080 d3073
    omega
  have d3081 : (x 1 4 && x 1 5).toNat = 0 := by
    have r3082 := hand2 (x 1 4) (x 1 5)
    have b3083 := hb (x 1 5)
    have b3084 := hb (x 1 4 && x 1 5)
    clear * - r3082 b3083 b3084 d3073
    omega
  have d3085 : (x 1 9).toNat = 0 := by
    have r3086 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
    have b3087 := hb (x 1 1)
    have b3088 := hb (x 1 9)
    clear * - r3086 b3087 b3088 d3053
    omega
  have d3089 : (x 2 14).toNat = 1 := by
    have r3090 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b3091 := hb (x 1 1)
    have b3092 := hb (x 2 14)
    clear * - r3090 b3091 b3092 d3053
    omega
  have d3093 : (x 2 1).toNat = 1 := by
    have r3094 : (x 2 1).toNat = (x 2 14).toNat := congrArg Bool.toNat (h114 2)
    have b3095 := hb (x 2 1)
    have b3096 := hb (x 2 14)
    clear * - r3094 b3095 b3096 d3089
    omega
  have d3097 : (x 3 14).toNat = 0 := by
    have r3098 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b3099 := hb (x 2 1)
    have b3100 := hb (x 3 14)
    clear * - r3098 b3099 b3100 d3093
    omega
  have d3101 : (x 3 1).toNat = 0 := by
    have r3102 : (x 3 1).toNat = (x 3 14).toNat := congrArg Bool.toNat (h114 3)
    have b3103 := hb (x 3 1)
    have b3104 := hb (x 3 14)
    clear * - r3102 b3103 b3104 d3097
    omega
  have d3105 : (x 3 13).toNat = 0 := by
    have r3106 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
    have b3107 := hb (x 3 1)
    have b3108 := hb (x 3 13)
    clear * - r3106 b3107 b3108 d3101
    omega
  have d3109 : (x 3 3 && x 3 13).toNat = 0 := by
    have r3110 := hand2 (x 3 3) (x 3 13)
    have b3111 := hb (x 3 13)
    have b3112 := hb (x 3 3 && x 3 13)
    clear * - r3110 b3111 b3112 d3105
    omega
  have d3113 : (x 3 5).toNat = 0 := by
    have r3114 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
    have b3115 := hb (x 3 5)
    have b3116 := hb (x 3 13)
    clear * - r3114 b3115 b3116 d3105
    omega
  have d3117 : (x 3 5 && x 3 11).toNat = 0 := by
    have r3118 := hand1 (x 3 5) (x 3 11)
    have b3119 := hb (x 3 5)
    have b3120 := hb (x 3 5 && x 3 11)
    clear * - r3118 b3119 b3120 d3113
    omega
  have d3121 : (x 3 9).toNat = 0 := by
    have r3122 : (x 3 9).toNat ≤ (x 3 1).toNat := himp _ _ (hp9 3)
    have b3123 := hb (x 3 1)
    have b3124 := hb (x 3 9)
    clear * - r3122 b3123 b3124 d3101
    omega
  have d3125 : (x 3 2 && x 3 9).toNat = 0 := by
    have r3126 := hand2 (x 3 2) (x 3 9)
    have b3127 := hb (x 3 9)
    have b3128 := hb (x 3 2 && x 3 9)
    clear * - r3126 b3127 b3128 d3121
    omega
  have d3129 : (x 3 3 && x 3 9).toNat = 0 := by
    have r3130 := hand2 (x 3 3) (x 3 9)
    have b3131 := hb (x 3 9)
    have b3132 := hb (x 3 3 && x 3 9)
    clear * - r3130 b3131 b3132 d3121
    omega
  have d3133 : (x 4 14).toNat = 1 := by
    have r3134 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b3135 := hb (x 3 1)
    have b3136 := hb (x 4 14)
    clear * - r3134 b3135 b3136 d3101
    omega
  have d3137 : (x 4 1).toNat = 1 := by
    have r3138 : (x 4 1).toNat = (x 4 14).toNat := congrArg Bool.toNat (h114 4)
    have b3139 := hb (x 4 1)
    have b3140 := hb (x 4 14)
    clear * - r3138 b3139 b3140 d3133
    omega
  have d3141 : (x 5 14).toNat = 0 := by
    have r3142 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b3143 := hb (x 4 1)
    have b3144 := hb (x 5 14)
    clear * - r3142 b3143 b3144 d3137
    omega
  have d3145 : (x 5 1).toNat = 0 := by
    have r3146 : (x 5 1).toNat = (x 5 14).toNat := congrArg Bool.toNat (h114 5)
    have b3147 := hb (x 5 1)
    have b3148 := hb (x 5 14)
    clear * - r3146 b3147 b3148 d3141
    omega
  have d3149 : (x 5 1 && x 5 11).toNat = 0 := by
    have r3150 := hand1 (x 5 1) (x 5 11)
    have b3151 := hb (x 5 1)
    have b3152 := hb (x 5 1 && x 5 11)
    clear * - r3150 b3151 b3152 d3145
    omega
  have d3153 : (x 5 1 && x 5 7).toNat = 0 := by
    have r3154 := hand1 (x 5 1) (x 5 7)
    have b3155 := hb (x 5 1)
    have b3156 := hb (x 5 1 && x 5 7)
    clear * - r3154 b3155 b3156 d3145
    omega
  have d3157 : (x 5 13).toNat = 0 := by
    have r3158 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
    have b3159 := hb (x 5 1)
    have b3160 := hb (x 5 13)
    clear * - r3158 b3159 b3160 d3145
    omega
  have d3161 : (x 5 5).toNat = 0 := by
    have r3162 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
    have b3163 := hb (x 5 5)
    have b3164 := hb (x 5 13)
    clear * - r3162 b3163 b3164 d3157
    omega
  have d3165 : (x 5 5 && x 5 9).toNat = 0 := by
    have r3166 := hand1 (x 5 5) (x 5 9)
    have b3167 := hb (x 5 5)
    have b3168 := hb (x 5 5 && x 5 9)
    clear * - r3166 b3167 b3168 d3161
    omega
  have d3169 : (x 5 9).toNat = 0 := by
    have r3170 : (x 5 9).toNat ≤ (x 5 1).toNat := himp _ _ (hp9 5)
    have b3171 := hb (x 5 1)
    have b3172 := hb (x 5 9)
    clear * - r3170 b3171 b3172 d3145
    omega
  have d3173 : (x 5 3 && x 5 9).toNat = 0 := by
    have r3174 := hand2 (x 5 3) (x 5 9)
    have b3175 := hb (x 5 9)
    have b3176 := hb (x 5 3 && x 5 9)
    clear * - r3174 b3175 b3176 d3169
    omega
  have d3177 : (x 6 14).toNat = 1 := by
    have r3178 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b3179 := hb (x 5 1)
    have b3180 := hb (x 6 14)
    clear * - r3178 b3179 b3180 d3145
    omega
  have d3181 : (x 6 1).toNat = 1 := by
    have r3182 : (x 6 1).toNat = (x 6 14).toNat := congrArg Bool.toNat (h114 6)
    have b3183 := hb (x 6 1)
    have b3184 := hb (x 6 14)
    clear * - r3182 b3183 b3184 d3177
    omega
  have d3185 : (x 7 14).toNat = 0 := by
    have r3186 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b3187 := hb (x 6 1)
    have b3188 := hb (x 7 14)
    clear * - r3186 b3187 b3188 d3181
    omega
  have d3189 : (x 7 3 && x 7 14).toNat = 0 := by
    have r3190 := hand2 (x 7 3) (x 7 14)
    have b3191 := hb (x 7 14)
    have b3192 := hb (x 7 3 && x 7 14)
    clear * - r3190 b3191 b3192 d3185
    omega
  have d3193 : (x 7 1).toNat = 0 := by
    have r3194 : (x 7 1).toNat = (x 7 14).toNat := congrArg Bool.toNat (h114 7)
    have b3195 := hb (x 7 1)
    have b3196 := hb (x 7 14)
    clear * - r3194 b3195 b3196 d3185
    omega
  have d3197 : (x 7 1 && x 7 7).toNat = 0 := by
    have r3198 := hand1 (x 7 1) (x 7 7)
    have b3199 := hb (x 7 1)
    have b3200 := hb (x 7 1 && x 7 7)
    clear * - r3198 b3199 b3200 d3193
    omega
  have d3201 : (x 7 13).toNat = 0 := by
    have r3202 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
    have b3203 := hb (x 7 1)
    have b3204 := hb (x 7 13)
    clear * - r3202 b3203 b3204 d3193
    omega
  have d3205 : (x 7 5).toNat = 0 := by
    have r3206 : (x 7 5).toNat ≤ (x 7 13).toNat := himp _ _ (hp5 7)
    have b3207 := hb (x 7 5)
    have b3208 := hb (x 7 13)
    clear * - r3206 b3207 b3208 d3201
    omega
  have d3209 : (x 7 9).toNat = 0 := by
    have r3210 : (x 7 9).toNat ≤ (x 7 1).toNat := himp _ _ (hp9 7)
    have b3211 := hb (x 7 1)
    have b3212 := hb (x 7 9)
    clear * - r3210 b3211 b3212 d3193
    omega
  have d3213 : (x 8 14).toNat = 1 := by
    have r3214 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b3215 := hb (x 7 1)
    have b3216 := hb (x 8 14)
    clear * - r3214 b3215 b3216 d3193
    omega
  have d3217 : (x 8 1).toNat = 1 := by
    have r3218 : (x 8 1).toNat = (x 8 14).toNat := congrArg Bool.toNat (h114 8)
    have b3219 := hb (x 8 1)
    have b3220 := hb (x 8 14)
    clear * - r3218 b3219 b3220 d3213
    omega
  have d3221 : (x 9 14).toNat = 0 := by
    have r3222 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b3223 := hb (x 8 1)
    have b3224 := hb (x 9 14)
    clear * - r3222 b3223 b3224 d3217
    omega
  have d3225 : (x 9 1).toNat = 0 := by
    have r3226 : (x 9 1).toNat = (x 9 14).toNat := congrArg Bool.toNat (h114 9)
    have b3227 := hb (x 9 1)
    have b3228 := hb (x 9 14)
    clear * - r3226 b3227 b3228 d3221
    omega
  have d3229 : (x 9 1 && x 9 12).toNat = 0 := by
    have r3230 := hand1 (x 9 1) (x 9 12)
    have b3231 := hb (x 9 1)
    have b3232 := hb (x 9 1 && x 9 12)
    clear * - r3230 b3231 b3232 d3225
    omega
  have d3233 : (x 9 13).toNat = 0 := by
    have r3234 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
    have b3235 := hb (x 9 1)
    have b3236 := hb (x 9 13)
    clear * - r3234 b3235 b3236 d3225
    omega
  have d3237 : (x 9 3 && x 9 13).toNat = 0 := by
    have r3238 := hand2 (x 9 3) (x 9 13)
    have b3239 := hb (x 9 13)
    have b3240 := hb (x 9 3 && x 9 13)
    clear * - r3238 b3239 b3240 d3233
    omega
  have d3241 : (x 9 5).toNat = 0 := by
    have r3242 : (x 9 5).toNat ≤ (x 9 13).toNat := himp _ _ (hp5 9)
    have b3243 := hb (x 9 5)
    have b3244 := hb (x 9 13)
    clear * - r3242 b3243 b3244 d3233
    omega
  have d3245 : (x 9 2).toNat = 0 := by
    have r3246 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
    have b3247 := hb (x 9 2)
    have b3248 := hb (x 9 14)
    clear * - r3246 b3247 b3248 d3221
    omega
  have d3249 : (x 9 3).toNat = 0 := by
    have r3250 : (x 9 2).toNat = (x 9 3).toNat := congrArg Bool.toNat (h23 9)
    have b3251 := hb (x 9 2)
    have b3252 := hb (x 9 3)
    clear * - r3250 b3251 b3252 d3245
    omega
  have d3253 : (x 7 2).toNat = 0 := by
    have r3254 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
    have b3255 := hb (x 7 2)
    have b3256 := hb (x 7 14)
    clear * - r3254 b3255 b3256 d3185
    omega
  have d3257 : (x 7 3).toNat = 0 := by
    have r3258 : (x 7 2).toNat = (x 7 3).toNat := congrArg Bool.toNat (h23 7)
    have b3259 := hb (x 7 2)
    have b3260 := hb (x 7 3)
    clear * - r3258 b3259 b3260 d3253
    omega
  have d3261 : (x 7 3 && x 7 7).toNat = 0 := by
    have r3262 := hand1 (x 7 3) (x 7 7)
    have b3263 := hb (x 7 3)
    have b3264 := hb (x 7 3 && x 7 7)
    clear * - r3262 b3263 b3264 d3257
    omega
  have d3265 : (x 5 2).toNat = 0 := by
    have r3266 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
    have b3267 := hb (x 5 2)
    have b3268 := hb (x 5 14)
    clear * - r3266 b3267 b3268 d3141
    omega
  have d3269 : (x 5 3).toNat = 0 := by
    have r3270 : (x 5 2).toNat = (x 5 3).toNat := congrArg Bool.toNat (h23 5)
    have b3271 := hb (x 5 2)
    have b3272 := hb (x 5 3)
    clear * - r3270 b3271 b3272 d3265
    omega
  have d3273 : (x 5 11).toNat = 0 := by
    have r3274 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
    have b3275 := hb (x 5 3)
    have b3276 := hb (x 5 11)
    clear * - r3274 b3275 b3276 d3269
    omega
  have d3277 : (x 3 2).toNat = 0 := by
    have r3278 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
    have b3279 := hb (x 3 2)
    have b3280 := hb (x 3 14)
    clear * - r3278 b3279 b3280 d3097
    omega
  have d3281 : (x 3 2 && x 3 11).toNat = 0 := by
    have r3282 := hand1 (x 3 2) (x 3 11)
    have b3283 := hb (x 3 2)
    have b3284 := hb (x 3 2 && x 3 11)
    clear * - r3282 b3283 b3284 d3277
    omega
  have d3285 : (x 3 2 && x 3 3).toNat = 0 := by
    have r3286 := hand1 (x 3 2) (x 3 3)
    have b3287 := hb (x 3 2)
    have b3288 := hb (x 3 2 && x 3 3)
    clear * - r3286 b3287 b3288 d3277
    omega
  have d3289 : (x 3 3).toNat = 0 := by
    have r3290 : (x 3 2).toNat = (x 3 3).toNat := congrArg Bool.toNat (h23 3)
    have b3291 := hb (x 3 2)
    have b3292 := hb (x 3 3)
    clear * - r3290 b3291 b3292 d3277
    omega
  have d3293 : (x 3 11).toNat = 0 := by
    have r3294 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
    have b3295 := hb (x 3 3)
    have b3296 := hb (x 3 11)
    clear * - r3294 b3295 b3296 d3289
    omega
  have d3297 : (x 3 7 && x 3 11).toNat = 0 := by
    have r3298 := hand2 (x 3 7) (x 3 11)
    have b3299 := hb (x 3 11)
    have b3300 := hb (x 3 7 && x 3 11)
    clear * - r3298 b3299 b3300 d3293
    omega
  have d3301 : (x 1 2).toNat = 0 := by
    have r3302 : (x 1 2).toNat ≤ (x 1 14).toNat := himp _ _ (hp2 1)
    have b3303 := hb (x 1 2)
    have b3304 := hb (x 1 14)
    clear * - r3302 b3303 b3304 d3049
    omega
  have d3305 : (x 1 3).toNat = 0 := by
    have r3306 : (x 1 2).toNat = (x 1 3).toNat := congrArg Bool.toNat (h23 1)
    have b3307 := hb (x 1 2)
    have b3308 := hb (x 1 3)
    clear * - r3306 b3307 b3308 d3301
    omega
  have d3309 : (x 1 3 && x 1 7).toNat = 0 := by
    have r3310 := hand1 (x 1 3) (x 1 7)
    have b3311 := hb (x 1 3)
    have b3312 := hb (x 1 3 && x 1 7)
    clear * - r3310 b3311 b3312 d3305
    omega
  have d3313 : (x 1 11).toNat = 0 := by
    have r3314 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
    have b3315 := hb (x 1 3)
    have b3316 := hb (x 1 11)
    clear * - r3314 b3315 b3316 d3305
    omega
  have d3317 : (x 1 4 && x 1 11).toNat = 0 := by
    have r3318 := hand2 (x 1 4) (x 1 11)
    have b3319 := hb (x 1 11)
    have b3320 := hb (x 1 4 && x 1 11)
    clear * - r3318 b3319 b3320 d3313
    omega
  have d3321 : (x (-1) 1).toNat = 0 := by
    have r3322 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b3323 := hb (x (-1) 1)
    have b3324 := hb (x 0 14)
    clear * - r3322 b3323 b3324 d3041
    omega
  have d3325 : (x (-1) 1 && x (-1) 11).toNat = 0 := by
    have r3326 := hand1 (x (-1) 1) (x (-1) 11)
    have b3327 := hb (x (-1) 1)
    have b3328 := hb (x (-1) 1 && x (-1) 11)
    clear * - r3326 b3327 b3328 d3321
    omega
  have d3329 : (x (-1) 14).toNat = 0 := by
    have r3330 : (x (-1) 1).toNat = (x (-1) 14).toNat := congrArg Bool.toNat (h114 (-1))
    have b3331 := hb (x (-1) 1)
    have b3332 := hb (x (-1) 14)
    clear * - r3330 b3331 b3332 d3321
    omega
  have d3333 : (x (-1) 6).toNat = 0 := by
    have r3334 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
    have b3335 := hb (x (-1) 6)
    have b3336 := hb (x (-1) 14)
    clear * - r3334 b3335 b3336 d3329
    omega
  have d3337 : (x (-1) 6 && x (-1) 13).toNat = 0 := by
    have r3338 := hand1 (x (-1) 6) (x (-1) 13)
    have b3339 := hb (x (-1) 6)
    have b3340 := hb (x (-1) 6 && x (-1) 13)
    clear * - r3338 b3339 b3340 d3333
    omega
  have d3341 : (x (-1) 6 && x (-1) 7).toNat = 0 := by
    have r3342 := hand1 (x (-1) 6) (x (-1) 7)
    have b3343 := hb (x (-1) 6)
    have b3344 := hb (x (-1) 6 && x (-1) 7)
    clear * - r3342 b3343 b3344 d3333
    omega
  have d3345 : (x (-1) 2).toNat = 0 := by
    have r3346 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
    have b3347 := hb (x (-1) 2)
    have b3348 := hb (x (-1) 14)
    clear * - r3346 b3347 b3348 d3329
    omega
  have d3349 : (x (-1) 3).toNat = 0 := by
    have r3350 : (x (-1) 2).toNat = (x (-1) 3).toNat := congrArg Bool.toNat (h23 (-1))
    have b3351 := hb (x (-1) 2)
    have b3352 := hb (x (-1) 3)
    clear * - r3350 b3351 b3352 d3345
    omega
  have d3353 : (x (-1) 11).toNat = 0 := by
    have r3354 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
    have b3355 := hb (x (-1) 3)
    have b3356 := hb (x (-1) 11)
    clear * - r3354 b3355 b3356 d3349
    omega
  have d3357 : (x (-1) 13).toNat = 0 := by
    have r3358 : (x (-1) 13).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp13 (-1))
    have b3359 := hb (x (-1) 1)
    have b3360 := hb (x (-1) 13)
    clear * - r3358 b3359 b3360 d3321
    omega
  have d3361 : (x (-1) 7 && x (-1) 13).toNat = 0 := by
    have r3362 := hand2 (x (-1) 7) (x (-1) 13)
    have b3363 := hb (x (-1) 13)
    have b3364 := hb (x (-1) 7 && x (-1) 13)
    clear * - r3362 b3363 b3364 d3357
    omega
  have d3365 : (x (-1) 5).toNat = 0 := by
    have r3366 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
    have b3367 := hb (x (-1) 5)
    have b3368 := hb (x (-1) 13)
    clear * - r3366 b3367 b3368 d3357
    omega
  have d3369 : (x (-1) 5 && x (-1) 9).toNat = 0 := by
    have r3370 := hand1 (x (-1) 5) (x (-1) 9)
    have b3371 := hb (x (-1) 5)
    have b3372 := hb (x (-1) 5 && x (-1) 9)
    clear * - r3370 b3371 b3372 d3365
    omega
  have d3373 : (x (-1) 9).toNat = 0 := by
    have r3374 : (x (-1) 9).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp9 (-1))
    have b3375 := hb (x (-1) 1)
    have b3376 := hb (x (-1) 9)
    clear * - r3374 b3375 b3376 d3321
    omega
  have d3377 : (x (-2) 1).toNat = 1 := by
    have r3378 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b3379 := hb (x (-2) 1)
    have b3380 := hb (x (-1) 14)
    clear * - r3378 b3379 b3380 d3329
    omega
  have d3381 : (x (-2) 14).toNat = 1 := by
    have r3382 : (x (-2) 1).toNat = (x (-2) 14).toNat := congrArg Bool.toNat (h114 (-2))
    have b3383 := hb (x (-2) 1)
    have b3384 := hb (x (-2) 14)
    clear * - r3382 b3383 b3384 d3377
    omega
  have d3385 : (x (-3) 1).toNat = 0 := by
    have r3386 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b3387 := hb (x (-3) 1)
    have b3388 := hb (x (-2) 14)
    clear * - r3386 b3387 b3388 d3381
    omega
  have d3389 : (x (-3) 14).toNat = 0 := by
    have r3390 : (x (-3) 1).toNat = (x (-3) 14).toNat := congrArg Bool.toNat (h114 (-3))
    have b3391 := hb (x (-3) 1)
    have b3392 := hb (x (-3) 14)
    clear * - r3390 b3391 b3392 d3385
    omega
  have d3393 : (x (-3) 2).toNat = 0 := by
    have r3394 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
    have b3395 := hb (x (-3) 2)
    have b3396 := hb (x (-3) 14)
    clear * - r3394 b3395 b3396 d3389
    omega
  have d3397 : (x (-3) 3).toNat = 0 := by
    have r3398 : (x (-3) 2).toNat = (x (-3) 3).toNat := congrArg Bool.toNat (h23 (-3))
    have b3399 := hb (x (-3) 2)
    have b3400 := hb (x (-3) 3)
    clear * - r3398 b3399 b3400 d3393
    omega
  have d3401 : (x (-3) 3 && x (-3) 13).toNat = 0 := by
    have r3402 := hand1 (x (-3) 3) (x (-3) 13)
    have b3403 := hb (x (-3) 3)
    have b3404 := hb (x (-3) 3 && x (-3) 13)
    clear * - r3402 b3403 b3404 d3397
    omega
  have d3405 : (x (-3) 11).toNat = 0 := by
    have r3406 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
    have b3407 := hb (x (-3) 3)
    have b3408 := hb (x (-3) 11)
    clear * - r3406 b3407 b3408 d3397
    omega
  have d3409 : (x (-3) 7 && x (-3) 11).toNat = 0 := by
    have r3410 := hand2 (x (-3) 7) (x (-3) 11)
    have b3411 := hb (x (-3) 11)
    have b3412 := hb (x (-3) 7 && x (-3) 11)
    clear * - r3410 b3411 b3412 d3405
    omega
  have d3413 : (x (-3) 13).toNat = 0 := by
    have r3414 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
    have b3415 := hb (x (-3) 1)
    have b3416 := hb (x (-3) 13)
    clear * - r3414 b3415 b3416 d3385
    omega
  have d3417 : (x (-3) 9).toNat = 0 := by
    have r3418 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
    have b3419 := hb (x (-3) 1)
    have b3420 := hb (x (-3) 9)
    clear * - r3418 b3419 b3420 d3385
    omega
  have d3421 : (x (-3) 8 && x (-3) 9).toNat = 0 := by
    have r3422 := hand2 (x (-3) 8) (x (-3) 9)
    have b3423 := hb (x (-3) 9)
    have b3424 := hb (x (-3) 8 && x (-3) 9)
    clear * - r3422 b3423 b3424 d3417
    omega
  have d3425 : (x (-4) 1).toNat = 1 := by
    have r3426 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b3427 := hb (x (-4) 1)
    have b3428 := hb (x (-3) 14)
    clear * - r3426 b3427 b3428 d3389
    omega
  have d3429 : (x (-4) 14).toNat = 1 := by
    have r3430 : (x (-4) 1).toNat = (x (-4) 14).toNat := congrArg Bool.toNat (h114 (-4))
    have b3431 := hb (x (-4) 1)
    have b3432 := hb (x (-4) 14)
    clear * - r3430 b3431 b3432 d3425
    omega
  have d3433 : (x (-5) 1).toNat = 0 := by
    have r3434 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b3435 := hb (x (-5) 1)
    have b3436 := hb (x (-4) 14)
    clear * - r3434 b3435 b3436 d3429
    omega
  have d3437 : (x (-5) 1 && x (-5) 11).toNat = 0 := by
    have r3438 := hand1 (x (-5) 1) (x (-5) 11)
    have b3439 := hb (x (-5) 1)
    have b3440 := hb (x (-5) 1 && x (-5) 11)
    clear * - r3438 b3439 b3440 d3433
    omega
  have d3441 : (x (-5) 14).toNat = 0 := by
    have r3442 : (x (-5) 1).toNat = (x (-5) 14).toNat := congrArg Bool.toNat (h114 (-5))
    have b3443 := hb (x (-5) 1)
    have b3444 := hb (x (-5) 14)
    clear * - r3442 b3443 b3444 d3433
    omega
  have d3445 : (x (-5) 2).toNat = 0 := by
    have r3446 : (x (-5) 2).toNat ≤ (x (-5) 14).toNat := himp _ _ (hp2 (-5))
    have b3447 := hb (x (-5) 2)
    have b3448 := hb (x (-5) 14)
    clear * - r3446 b3447 b3448 d3441
    omega
  have d3449 : (x (-5) 3).toNat = 0 := by
    have r3450 : (x (-5) 2).toNat = (x (-5) 3).toNat := congrArg Bool.toNat (h23 (-5))
    have b3451 := hb (x (-5) 2)
    have b3452 := hb (x (-5) 3)
    clear * - r3450 b3451 b3452 d3445
    omega
  have d3453 : (x (-5) 11).toNat = 0 := by
    have r3454 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
    have b3455 := hb (x (-5) 3)
    have b3456 := hb (x (-5) 11)
    clear * - r3454 b3455 b3456 d3449
    omega
  have d3457 : (x (-5) 10 && x (-5) 11).toNat = 0 := by
    have r3458 := hand2 (x (-5) 10) (x (-5) 11)
    have b3459 := hb (x (-5) 11)
    have b3460 := hb (x (-5) 10 && x (-5) 11)
    clear * - r3458 b3459 b3460 d3453
    omega
  have d3461 : (x (-5) 10).toNat = 0 := by
    have r3462 : (x (-5) 10).toNat ≤ (x (-5) 2).toNat := himp _ _ (hp10 (-5))
    have b3463 := hb (x (-5) 2)
    have b3464 := hb (x (-5) 10)
    clear * - r3462 b3463 b3464 d3445
    omega
  have d3465 : (x (-5) 13).toNat = 0 := by
    have r3466 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
    have b3467 := hb (x (-5) 1)
    have b3468 := hb (x (-5) 13)
    clear * - r3466 b3467 b3468 d3433
    omega
  have d3469 : (x (-5) 9 && x (-5) 13).toNat = 0 := by
    have r3470 := hand2 (x (-5) 9) (x (-5) 13)
    have b3471 := hb (x (-5) 13)
    have b3472 := hb (x (-5) 9 && x (-5) 13)
    clear * - r3470 b3471 b3472 d3465
    omega
  have d3473 : (x (-5) 5).toNat = 0 := by
    have r3474 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
    have b3475 := hb (x (-5) 5)
    have b3476 := hb (x (-5) 13)
    clear * - r3474 b3475 b3476 d3465
    omega
  have d3477 : (x (-5) 9).toNat = 0 := by
    have r3478 : (x (-5) 9).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp9 (-5))
    have b3479 := hb (x (-5) 1)
    have b3480 := hb (x (-5) 9)
    clear * - r3478 b3479 b3480 d3433
    omega
  have d3481 : (x (-6) 1).toNat = 1 := by
    have r3482 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b3483 := hb (x (-6) 1)
    have b3484 := hb (x (-5) 14)
    clear * - r3482 b3483 b3484 d3441
    omega
  have d3485 : (x (-6) 14).toNat = 1 := by
    have r3486 : (x (-6) 1).toNat = (x (-6) 14).toNat := congrArg Bool.toNat (h114 (-6))
    have b3487 := hb (x (-6) 1)
    have b3488 := hb (x (-6) 14)
    clear * - r3486 b3487 b3488 d3481
    omega
  have d3489 : (x (-7) 1).toNat = 0 := by
    have r3490 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b3491 := hb (x (-7) 1)
    have b3492 := hb (x (-6) 14)
    clear * - r3490 b3491 b3492 d3485
    omega
  have d3493 : (x (-7) 14).toNat = 0 := by
    have r3494 : (x (-7) 1).toNat = (x (-7) 14).toNat := congrArg Bool.toNat (h114 (-7))
    have b3495 := hb (x (-7) 1)
    have b3496 := hb (x (-7) 14)
    clear * - r3494 b3495 b3496 d3489
    omega
  have d3497 : (x (-7) 2).toNat = 0 := by
    have r3498 : (x (-7) 2).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp2 (-7))
    have b3499 := hb (x (-7) 2)
    have b3500 := hb (x (-7) 14)
    clear * - r3498 b3499 b3500 d3493
    omega
  have d3501 : (x (-7) 3).toNat = 0 := by
    have r3502 : (x (-7) 2).toNat = (x (-7) 3).toNat := congrArg Bool.toNat (h23 (-7))
    have b3503 := hb (x (-7) 2)
    have b3504 := hb (x (-7) 3)
    clear * - r3502 b3503 b3504 d3497
    omega
  have d3505 : (x (-7) 3 && x (-7) 13).toNat = 0 := by
    have r3506 := hand1 (x (-7) 3) (x (-7) 13)
    have b3507 := hb (x (-7) 3)
    have b3508 := hb (x (-7) 3 && x (-7) 13)
    clear * - r3506 b3507 b3508 d3501
    omega
  have d3509 : (x (-7) 11).toNat = 0 := by
    have r3510 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
    have b3511 := hb (x (-7) 3)
    have b3512 := hb (x (-7) 11)
    clear * - r3510 b3511 b3512 d3501
    omega
  have d3513 : (x (-7) 13).toNat = 0 := by
    have r3514 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
    have b3515 := hb (x (-7) 1)
    have b3516 := hb (x (-7) 13)
    clear * - r3514 b3515 b3516 d3489
    omega
  have d3517 : (x (-7) 12 && x (-7) 13).toNat = 0 := by
    have r3518 := hand2 (x (-7) 12) (x (-7) 13)
    have b3519 := hb (x (-7) 13)
    have b3520 := hb (x (-7) 12 && x (-7) 13)
    clear * - r3518 b3519 b3520 d3513
    omega
  have d3521 : (x (-8) 1).toNat = 1 := by
    have r3522 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b3523 := hb (x (-8) 1)
    have b3524 := hb (x (-7) 14)
    clear * - r3522 b3523 b3524 d3493
    omega
  have d3525 : (x (-8) 14).toNat = 1 := by
    have r3526 : (x (-8) 1).toNat = (x (-8) 14).toNat := congrArg Bool.toNat (h114 (-8))
    have b3527 := hb (x (-8) 1)
    have b3528 := hb (x (-8) 14)
    clear * - r3526 b3527 b3528 d3521
    omega
  have d3529 : (x (-9) 1).toNat = 0 := by
    have r3530 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b3531 := hb (x (-9) 1)
    have b3532 := hb (x (-8) 14)
    clear * - r3530 b3531 b3532 d3525
    omega
  have d3533 : (x (-9) 14).toNat = 0 := by
    have r3534 : (x (-9) 1).toNat = (x (-9) 14).toNat := congrArg Bool.toNat (h114 (-9))
    have b3535 := hb (x (-9) 1)
    have b3536 := hb (x (-9) 14)
    clear * - r3534 b3535 b3536 d3529
    omega
  have d3537 : (x (-9) 13).toNat = 0 := by
    have r3538 : (x (-9) 13).toNat ≤ (x (-9) 1).toNat := himp _ _ (hp13 (-9))
    have b3539 := hb (x (-9) 1)
    have b3540 := hb (x (-9) 13)
    clear * - r3538 b3539 b3540 d3529
    omega
  have d3541 : (x (-9) 5).toNat = 0 := by
    have r3542 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
    have b3543 := hb (x (-9) 5)
    have b3544 := hb (x (-9) 13)
    clear * - r3542 b3543 b3544 d3537
    omega
  have d3545 : (x (-10) 1).toNat = 1 := by
    have r3546 : (x (-9) 14).toNat + (x (-10) 1).toNat = 1 := by have q := hd14 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b3547 := hb (x (-10) 1)
    have b3548 := hb (x (-9) 14)
    clear * - r3546 b3547 b3548 d3533
    omega
  have d3549 : (x (-10) 14).toNat = 1 := by
    have r3550 : (x (-10) 1).toNat = (x (-10) 14).toNat := congrArg Bool.toNat (h114 (-10))
    have b3551 := hb (x (-10) 1)
    have b3552 := hb (x (-10) 14)
    clear * - r3550 b3551 b3552 d3545
    omega
  have d3553 : (x 6 8).toNat = 0 := by
    have r3554 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e3555 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e3556 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e3557 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e3558 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e3559 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e3560 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b3561 := hb (x (-1) 7)
    have b3562 := hb (x 0 6)
    have b3563 := hb (x 1 5)
    have b3564 := hb (x 2 4)
    have b3565 := hb (x 3 11)
    have b3566 := hb (x 4 10)
    have b3567 := hb (x 5 9)
    have b3568 := hb (x 6 8)
    clear * - r3554 e3555 e3556 e3557 e3558 e3559 e3560 b3561 b3562 b3563 b3564 b3565 b3566 b3567 b3568 d3169 d3293 d3073 g1
    omega
  have d3569 : (x 6 2 && x 6 8).toNat = 0 := by
    have r3570 := hand2 (x 6 2) (x 6 8)
    have b3571 := hb (x 6 8)
    have b3572 := hb (x 6 2 && x 6 8)
    clear * - r3570 b3571 b3572 d3553
    omega
  have d3573 : (x 6 4 && x 6 8).toNat = 0 := by
    have r3574 := hand2 (x 6 4) (x 6 8)
    have b3575 := hb (x 6 8)
    have b3576 := hb (x 6 4 && x 6 8)
    clear * - r3574 b3575 b3576 d3553
    omega
  have d3577 : (x 4 10).toNat = 0 := by
    have r3578 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e3579 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e3580 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e3581 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e3582 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e3583 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e3584 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b3585 := hb (x (-1) 7)
    have b3586 := hb (x 0 6)
    have b3587 := hb (x 1 5)
    have b3588 := hb (x 2 4)
    have b3589 := hb (x 3 11)
    have b3590 := hb (x 4 10)
    have b3591 := hb (x 5 9)
    have b3592 := hb (x 6 8)
    clear * - r3578 e3579 e3580 e3581 e3582 e3583 e3584 b3585 b3586 b3587 b3588 b3589 b3590 b3591 b3592 d3553 d3169 d3293 d3073 g1
    omega
  have d3593 : (x 4 1 && x 4 10).toNat = 0 := by
    have r3594 := hand2 (x 4 1) (x 4 10)
    have b3595 := hb (x 4 10)
    have b3596 := hb (x 4 1 && x 4 10)
    clear * - r3594 b3595 b3596 d3577
    omega
  have d3597 : (x 2 3 && x 2 12).toNat = 1 := by
    have r3598 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b3599 := hb (x (-1) 6)
    have b3600 := hb (x 5 9)
    have b3601 := hb (x 4 1 && x 4 10)
    have b3602 := hb (x 3 2 && x 3 11)
    have b3603 := hb (x 2 3 && x 2 12)
    have b3604 := hb (x 1 4 && x 1 13)
    have b3605 := hb (x 0 5 && x 0 14)
    clear * - r3598 b3599 b3600 b3601 b3602 b3603 b3604 b3605 d3169 d3593 d3281 d3061 d3029 d3333
    omega
  have d3606 : (x 2 12).toNat = 1 := by
    have r3607 := hand2 (x 2 3) (x 2 12)
    have b3608 := hb (x 2 12)
    have b3609 := hb (x 2 3 && x 2 12)
    clear * - r3607 b3608 b3609 d3597
    omega
  have d3610 : (x 0 2).toNat = 0 := by
    have r3611 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e3612 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e3613 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b3614 := hb (x (-1) 3)
    have b3615 := hb (x 0 2)
    have b3616 := hb (x 1 13)
    have b3617 := hb (x 2 12)
    clear * - r3611 e3612 e3613 b3614 b3615 b3616 b3617 d3606 d3057 d3349
    omega
  have d3618 : (x 0 10).toNat = 0 := by
    have r3619 : (x 0 10).toNat ≤ (x 0 2).toNat := himp _ _ (hp10 0)
    have b3620 := hb (x 0 2)
    have b3621 := hb (x 0 10)
    clear * - r3619 b3620 b3621 d3610
    omega
  have d3622 : (x 2 3).toNat = 1 := by
    have r3623 := hand1 (x 2 3) (x 2 12)
    have b3624 := hb (x 2 3)
    have b3625 := hb (x 2 3 && x 2 12)
    clear * - r3623 b3624 b3625 d3597
    omega
  have d3626 : (x 2 2).toNat = 1 := by
    have r3627 : (x 2 2).toNat = (x 2 3).toNat := congrArg Bool.toNat (h23 2)
    have b3628 := hb (x 2 2)
    have b3629 := hb (x 2 3)
    clear * - r3627 b3628 b3629 d3622
    omega
  have d3630 : (x 4 12).toNat = 0 := by
    have r3631 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e3632 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e3633 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b3634 := hb (x 1 3)
    have b3635 := hb (x 2 2)
    have b3636 := hb (x 3 13)
    have b3637 := hb (x 4 12)
    clear * - r3631 e3632 e3633 b3634 b3635 b3636 b3637 d3105 d3626 d3305
    omega
  have d3638 : (x 4 2 && x 4 12).toNat = 0 := by
    have r3639 := hand2 (x 4 2) (x 4 12)
    have b3640 := hb (x 4 12)
    have b3641 := hb (x 4 2 && x 4 12)
    clear * - r3639 b3640 b3641 d3630
    omega
  have d3642 : (x 4 4).toNat = 0 := by
    have r3643 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
    have b3644 := hb (x 4 4)
    have b3645 := hb (x 4 12)
    clear * - r3643 b3644 b3645 d3630
    omega
  have d3646 : (x 4 4 && x 4 10).toNat = 0 := by
    have r3647 := hand1 (x 4 4) (x 4 10)
    have b3648 := hb (x 4 4)
    have b3649 := hb (x 4 4 && x 4 10)
    clear * - r3647 b3648 b3649 d3642
    omega
  have d3650 : (x 4 6 && x 4 10).toNat = 0 := by
    have r3651 := hand2 (x 4 6) (x 4 10)
    have b3652 := hb (x 4 10)
    have b3653 := hb (x 4 6 && x 4 10)
    clear * - r3651 b3652 b3653 d3577
    omega
  have d3654 : (x 2 4).toNat = 0 := by
    have r3655 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e3656 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e3657 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e3658 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e3659 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e3660 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e3661 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b3662 := hb (x (-1) 7)
    have b3663 := hb (x 0 6)
    have b3664 := hb (x 1 5)
    have b3665 := hb (x 2 4)
    have b3666 := hb (x 3 11)
    have b3667 := hb (x 4 10)
    have b3668 := hb (x 5 9)
    have b3669 := hb (x 6 8)
    clear * - r3655 e3656 e3657 e3658 e3659 e3660 e3661 b3662 b3663 b3664 b3665 b3666 b3667 b3668 b3669 d3553 d3169 d3577 d3293 d3073 g1
    omega
  have d3670 : (x 2 4 && x 2 14).toNat = 0 := by
    have r3671 := hand1 (x 2 4) (x 2 14)
    have b3672 := hb (x 2 4)
    have b3673 := hb (x 2 4 && x 2 14)
    clear * - r3671 b3672 b3673 d3654
    omega
  have d3674 : (x 6 10).toNat = 1 := by
    have r3675 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b3676 := hb (x 1 5)
    have b3677 := hb (x 6 10)
    have b3678 := hb (x 5 1 && x 5 11)
    have b3679 := hb (x 4 2 && x 4 12)
    have b3680 := hb (x 3 3 && x 3 13)
    have b3681 := hb (x 2 4 && x 2 14)
    clear * - r3675 b3676 b3677 b3678 b3679 b3680 b3681 d3149 d3638 d3109 d3670 d3073
    omega
  have d3682 : (x 6 2).toNat = 1 := by
    have r3683 : (x 6 10).toNat ≤ (x 6 2).toNat := himp _ _ (hp10 6)
    have b3684 := hb (x 6 2)
    have b3685 := hb (x 6 10)
    clear * - r3683 b3684 b3685 d3674
    omega
  have d3686 : (x 6 3).toNat = 1 := by
    have r3687 : (x 6 2).toNat = (x 6 3).toNat := congrArg Bool.toNat (h23 6)
    have b3688 := hb (x 6 2)
    have b3689 := hb (x 6 3)
    clear * - r3687 b3688 b3689 d3682
    omega
  have d3690 : (x 9 12).toNat = 0 := by
    have r3691 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e3692 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e3693 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b3694 := hb (x 6 3)
    have b3695 := hb (x 7 2)
    have b3696 := hb (x 8 13)
    have b3697 := hb (x 9 12)
    clear * - r3691 e3692 e3693 b3694 b3695 b3696 b3697 d3253 d3686
    omega
  have d3698 : (x 8 13).toNat = 0 := by
    have r3699 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e3700 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e3701 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b3702 := hb (x 6 3)
    have b3703 := hb (x 7 2)
    have b3704 := hb (x 8 13)
    have b3705 := hb (x 9 12)
    clear * - r3699 e3700 e3701 b3702 b3703 b3704 b3705 d3690 d3253 d3686
    omega
  have d3706 : (x 8 2 && x 8 13).toNat = 0 := by
    have r3707 := hand2 (x 8 2) (x 8 13)
    have b3708 := hb (x 8 13)
    have b3709 := hb (x 8 2 && x 8 13)
    clear * - r3707 b3708 b3709 d3698
    omega
  have d3710 : (x 8 12).toNat = 0 := by
    have r3711 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e3712 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e3713 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b3714 := hb (x 5 3)
    have b3715 := hb (x 6 2)
    have b3716 := hb (x 7 13)
    have b3717 := hb (x 8 12)
    clear * - r3711 e3712 e3713 b3714 b3715 b3716 b3717 d3201 d3682 d3269
    omega
  have d3718 : (x 8 4).toNat = 0 := by
    have r3719 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
    have b3720 := hb (x 8 4)
    have b3721 := hb (x 8 12)
    clear * - r3719 b3720 b3721 d3710
    omega
  have d3722 : (x 8 4 && x 8 14).toNat = 0 := by
    have r3723 := hand1 (x 8 4) (x 8 14)
    have b3724 := hb (x 8 4)
    have b3725 := hb (x 8 4 && x 8 14)
    clear * - r3723 b3724 b3725 d3718
    omega
  have d3726 : (x 8 8).toNat = 0 := by
    have r3727 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e3728 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e3729 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e3730 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e3731 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e3732 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e3733 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have b3734 := hb (x 1 7)
    have b3735 := hb (x 2 6)
    have b3736 := hb (x 3 5)
    have b3737 := hb (x 4 4)
    have b3738 := hb (x 5 11)
    have b3739 := hb (x 6 10)
    have b3740 := hb (x 7 9)
    have b3741 := hb (x 8 8)
    clear * - r3727 e3728 e3729 e3730 e3731 e3732 e3733 b3734 b3735 b3736 b3737 b3738 b3739 b3740 b3741 d3209 d3674 d3273 d3642 d3113
    omega
  have d3742 : (x 2 6).toNat = 0 := by
    have r3743 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e3744 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e3745 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e3746 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e3747 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e3748 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e3749 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have b3750 := hb (x 1 7)
    have b3751 := hb (x 2 6)
    have b3752 := hb (x 3 5)
    have b3753 := hb (x 4 4)
    have b3754 := hb (x 5 11)
    have b3755 := hb (x 6 10)
    have b3756 := hb (x 7 9)
    have b3757 := hb (x 8 8)
    clear * - r3743 e3744 e3745 e3746 e3747 e3748 e3749 b3750 b3751 b3752 b3753 b3754 b3755 b3756 b3757 d3726 d3209 d3674 d3273 d3642 d3113
    omega
  have d3758 : (x 2 6 && x 2 12).toNat = 0 := by
    have r3759 := hand1 (x 2 6) (x 2 12)
    have b3760 := hb (x 2 6)
    have b3761 := hb (x 2 6 && x 2 12)
    clear * - r3759 b3760 b3761 d3742
    omega
  have d3762 : (x 2 2 && x 2 6).toNat = 0 := by
    have r3763 := hand2 (x 2 2) (x 2 6)
    have b3764 := hb (x 2 6)
    have b3765 := hb (x 2 2 && x 2 6)
    clear * - r3763 b3764 b3765 d3742
    omega
  have d3766 : (x 2 4 && x 2 10).toNat = 0 := by
    have r3767 := hand1 (x 2 4) (x 2 10)
    have b3768 := hb (x 2 4)
    have b3769 := hb (x 2 4 && x 2 10)
    clear * - r3767 b3768 b3769 d3654
    omega
  have d3770 : (x 2 3 && x 2 4).toNat = 0 := by
    have r3771 := hand2 (x 2 3) (x 2 4)
    have b3772 := hb (x 2 4)
    have b3773 := hb (x 2 3 && x 2 4)
    clear * - r3771 b3772 b3773 d3654
    omega
  have d3774 : (x (-1) 7).toNat = 0 := by
    have r3775 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e3776 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e3777 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e3778 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e3779 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e3780 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e3781 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b3782 := hb (x (-1) 7)
    have b3783 := hb (x 0 6)
    have b3784 := hb (x 1 5)
    have b3785 := hb (x 2 4)
    have b3786 := hb (x 3 11)
    have b3787 := hb (x 4 10)
    have b3788 := hb (x 5 9)
    have b3789 := hb (x 6 8)
    clear * - r3775 e3776 e3777 e3778 e3779 e3780 e3781 b3782 b3783 b3784 b3785 b3786 b3787 b3788 b3789 d3553 d3169 d3577 d3293 d3654 d3073 g1
    omega
  have r3790 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r3791 : (x 4 1).toNat + (x 3 2).toNat + (x 2 3).toNat + (x 1 4).toNat + (x 0 5).toNat + (x (-1) 6).toNat + (x (-2) 7).toNat + (x (-3) 8).toNat + (x (-4) 9).toNat + (x (-5) 10).toNat + (x (-6) 11).toNat + (x (-7) 12).toNat + (x (-8) 13).toNat + (x (-9) 14).toNat = 3 := by have q := hcount 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r3792 : (x 5 1).toNat + (x 4 2).toNat + (x 3 3).toNat + (x 2 4).toNat + (x 1 5).toNat + (x 0 6).toNat + (x (-1) 7).toNat + (x (-2) 8).toNat + (x (-3) 9).toNat + (x (-4) 10).toNat + (x (-5) 11).toNat + (x (-6) 12).toNat + (x (-7) 13).toNat + (x (-8) 14).toNat = 3 := by have q := hcount 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r3793 : (x 9 1).toNat + (x 8 2).toNat + (x 7 3).toNat + (x 6 4).toNat + (x 5 5).toNat + (x 4 6).toNat + (x 3 7).toNat + (x 2 8).toNat + (x 1 9).toNat + (x 0 10).toNat + (x (-1) 11).toNat + (x (-2) 12).toNat + (x (-3) 13).toNat + (x (-4) 14).toNat = 3 := by have q := hcount 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r3794 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r3795 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e3796 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
  have e3797 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
  have e3798 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
  have e3799 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
  have e3800 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
  have e3801 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
  have r3802 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e3803 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
  have e3804 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
  have e3805 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
  have e3806 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
  have e3807 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
  have e3808 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
  have r3809 : (x 10 2).toNat = (x 10 3).toNat := congrArg Bool.toNat (h23 10)
  have r3810 : 1 ≤ (x 5 1).toNat + (x 4 1 && x 4 2).toNat + (x 3 2 && x 3 3).toNat + (x 2 3 && x 2 4).toNat + (x 1 4 && x 1 5).toNat + (x 0 5 && x 0 6).toNat + (x (-1) 6 && x (-1) 7).toNat + (x (-2) 7 && x (-2) 8).toNat + (x (-3) 8 && x (-3) 9).toNat + (x (-4) 9 && x (-4) 10).toNat + (x (-5) 10 && x (-5) 11).toNat + (x (-6) 11 && x (-6) 12).toNat + (x (-7) 12 && x (-7) 13).toNat + (x (-8) 13 && x (-8) 14).toNat + (x (-9) 14).toNat := by have q := hcov1 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r3811 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e3812 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
  have e3813 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
  have r3814 : 1 ≤ (x 10 4).toNat + (x 9 1 && x 9 5).toNat + (x 8 2 && x 8 6).toNat + (x 7 3 && x 7 7).toNat + (x 6 4 && x 6 8).toNat + (x 5 5 && x 5 9).toNat + (x 4 6 && x 4 10).toNat + (x 3 7 && x 3 11).toNat + (x 2 8 && x 2 12).toNat + (x 1 9 && x 1 13).toNat + (x 0 10 && x 0 14).toNat + (x (-1) 11).toNat := by have q := hcov4 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e3815 : (x 9 1 && x 9 5).toNat = (x 9 5).toNat := handr _ _ (fun h => hp13 9 (hp5 9 (h)))
  have e3816 : (x 0 10 && x 0 14).toNat = (x 0 10).toNat := handl _ _ (fun h => hp2 0 (hp10 0 (h)))
  have r3817 : 1 ≤ (x 6 6).toNat + (x 5 1 && x 5 7).toNat + (x 4 2 && x 4 8).toNat + (x 3 3 && x 3 9).toNat + (x 2 4 && x 2 10).toNat + (x 1 5 && x 1 11).toNat + (x 0 6 && x 0 12).toNat + (x (-1) 7 && x (-1) 13).toNat + (x (-2) 8 && x (-2) 14).toNat + (x (-3) 9).toNat := by have q := hcov6 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r3818 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r3819 : 1 ≤ (x 5 7).toNat + (x 4 1 && x 4 8).toNat + (x 3 2 && x 3 9).toNat + (x 2 3 && x 2 10).toNat + (x 1 4 && x 1 11).toNat + (x 0 5 && x 0 12).toNat + (x (-1) 6 && x (-1) 13).toNat + (x (-2) 7 && x (-2) 14).toNat + (x (-3) 8).toNat := by have q := hcov7 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r3820 : 1 ≤ (x (-4) 10).toNat + (x (-5) 1 && x (-5) 11).toNat + (x (-6) 2 && x (-6) 12).toNat + (x (-7) 3 && x (-7) 13).toNat + (x (-8) 4 && x (-8) 14).toNat + (x (-9) 5).toNat := by have q := hcov10 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r3821 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r3822 : 1 ≤ (x 12 10).toNat + (x 11 1 && x 11 11).toNat + (x 10 2 && x 10 12).toNat + (x 9 3 && x 9 13).toNat + (x 8 4 && x 8 14).toNat + (x 7 5).toNat := by have q := hcov10 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r3823 : 1 ≤ (x 10 11).toNat + (x 9 1 && x 9 12).toNat + (x 8 2 && x 8 13).toNat + (x 7 3 && x 7 14).toNat + (x 6 4).toNat := by have q := hcov11 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r3824 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
  have r3825 : (x 10 11).toNat ≤ (x 10 3).toNat := himp _ _ (hp11 10)
  have r3826 := hand2 (x 4 1) (x 4 2)
  have r3827 := hand2 (x (-2) 7) (x (-2) 8)
  have r3828 := hand1 (x (-4) 9) (x (-4) 10)
  have r3829 := hand1 (x (-6) 11) (x (-6) 12)
  have r3830 := hand1 (x (-8) 13) (x (-8) 14)
  have r3831 := hand1 (x 0 4) (x 0 8)
  have r3832 := hand1 (x (-2) 6) (x (-2) 10)
  have r3833 := hand1 (x (-4) 8) (x (-4) 12)
  have r3834 := hand1 (x 8 2) (x 8 6)
  have r3835 := hand1 (x 2 8) (x 2 12)
  have r3836 := hand1 (x 4 2) (x 4 8)
  have r3837 := hand2 (x 0 6) (x 0 12)
  have r3838 := hand1 (x (-2) 8) (x (-2) 14)
  have r3839 := hand1 (x 0 8) (x 0 14)
  have r3840 := hand2 (x 4 1) (x 4 8)
  have r3841 := hand2 (x 2 3) (x 2 10)
  have r3842 := hand1 (x (-2) 7) (x (-2) 14)
  have r3843 := hand2 (x (-6) 2) (x (-6) 12)
  have r3844 := hand1 (x (-8) 4) (x (-8) 14)
  have r3845 := hand2 (x (-2) 2) (x (-2) 12)
  have r3846 := hand1 (x (-4) 4) (x (-4) 14)
  have r3847 := hand1 (x 11 1) (x 11 11)
  have r3848 := hand1 (x 10 2) (x 10 12)
  have b3849 := hb (x (-10) 14)
  have b3850 := hb (x (-9) 5)
  have b3851 := hb (x (-9) 13)
  have b3852 := hb (x (-9) 14)
  have b3853 := hb (x (-8) 4)
  have b3854 := hb (x (-8) 12)
  have b3855 := hb (x (-8) 13)
  have b3856 := hb (x (-8) 14)
  have b3857 := hb (x (-7) 7)
  have b3858 := hb (x (-7) 11)
  have b3859 := hb (x (-7) 12)
  have b3860 := hb (x (-7) 13)
  have b3861 := hb (x (-6) 6)
  have b3862 := hb (x (-6) 10)
  have b3863 := hb (x (-6) 11)
  have b3864 := hb (x (-6) 12)
  have b3865 := hb (x (-5) 5)
  have b3866 := hb (x (-5) 9)
  have b3867 := hb (x (-5) 10)
  have b3868 := hb (x (-5) 11)
  have b3869 := hb (x (-4) 4)
  have b3870 := hb (x (-4) 8)
  have b3871 := hb (x (-4) 9)
  have b3872 := hb (x (-4) 10)
  have b3873 := hb (x (-4) 14)
  have b3874 := hb (x (-3) 7)
  have b3875 := hb (x (-3) 8)
  have b3876 := hb (x (-3) 9)
  have b3877 := hb (x (-3) 11)
  have b3878 := hb (x (-3) 13)
  have b3879 := hb (x (-2) 6)
  have b3880 := hb (x (-2) 7)
  have b3881 := hb (x (-2) 8)
  have b3882 := hb (x (-2) 10)
  have b3883 := hb (x (-2) 12)
  have b3884 := hb (x (-2) 14)
  have b3885 := hb (x (-1) 5)
  have b3886 := hb (x (-1) 6)
  have b3887 := hb (x (-1) 7)
  have b3888 := hb (x (-1) 9)
  have b3889 := hb (x (-1) 11)
  have b3890 := hb (x (-1) 13)
  have b3891 := hb (x 0 4)
  have b3892 := hb (x 0 5)
  have b3893 := hb (x 0 6)
  have b3894 := hb (x 0 8)
  have b3895 := hb (x 0 10)
  have b3896 := hb (x 0 12)
  have b3897 := hb (x 1 3)
  have b3898 := hb (x 1 4)
  have b3899 := hb (x 1 5)
  have b3900 := hb (x 1 9)
  have b3901 := hb (x 1 11)
  have b3902 := hb (x 2 2)
  have b3903 := hb (x 2 3)
  have b3904 := hb (x 2 4)
  have b3905 := hb (x 2 8)
  have b3906 := hb (x 2 10)
  have b3907 := hb (x 3 1)
  have b3908 := hb (x 3 2)
  have b3909 := hb (x 3 3)
  have b3910 := hb (x 3 5)
  have b3911 := hb (x 3 7)
  have b3912 := hb (x 3 9)
  have b3913 := hb (x 4 1)
  have b3914 := hb (x 4 2)
  have b3915 := hb (x 4 4)
  have b3916 := hb (x 4 6)
  have b3917 := hb (x 4 8)
  have b3918 := hb (x 5 1)
  have b3919 := hb (x 5 5)
  have b3920 := hb (x 5 7)
  have b3921 := hb (x 6 4)
  have b3922 := hb (x 6 6)
  have b3923 := hb (x 7 3)
  have b3924 := hb (x 7 5)
  have b3925 := hb (x 7 7)
  have b3926 := hb (x 8 2)
  have b3927 := hb (x 8 4)
  have b3928 := hb (x 8 6)
  have b3929 := hb (x 9 1)
  have b3930 := hb (x 9 3)
  have b3931 := hb (x 9 5)
  have b3932 := hb (x 10 2)
  have b3933 := hb (x 10 3)
  have b3934 := hb (x 10 4)
  have b3935 := hb (x 10 11)
  have b3936 := hb (x 11 1)
  have b3937 := hb (x 11 11)
  have b3938 := hb (x 12 10)
  have b3939 := hb (x 13 9)
  have b3940 := hb (x 14 8)
  have b3941 := hb (x 4 1 && x 4 2)
  have b3942 := hb (x 3 2 && x 3 3)
  have b3943 := hb (x 2 3 && x 2 4)
  have b3944 := hb (x 1 4 && x 1 5)
  have b3945 := hb (x 0 5 && x 0 6)
  have b3946 := hb (x (-1) 6 && x (-1) 7)
  have b3947 := hb (x (-2) 7 && x (-2) 8)
  have b3948 := hb (x (-3) 8 && x (-3) 9)
  have b3949 := hb (x (-4) 9 && x (-4) 10)
  have b3950 := hb (x (-5) 10 && x (-5) 11)
  have b3951 := hb (x (-6) 11 && x (-6) 12)
  have b3952 := hb (x (-7) 12 && x (-7) 13)
  have b3953 := hb (x (-8) 13 && x (-8) 14)
  have b3954 := hb (x 2 2 && x 2 6)
  have b3955 := hb (x 1 3 && x 1 7)
  have b3956 := hb (x 0 4 && x 0 8)
  have b3957 := hb (x (-1) 5 && x (-1) 9)
  have b3958 := hb (x (-2) 6 && x (-2) 10)
  have b3959 := hb (x (-3) 7 && x (-3) 11)
  have b3960 := hb (x (-4) 8 && x (-4) 12)
  have b3961 := hb (x (-5) 9 && x (-5) 13)
  have b3962 := hb (x 8 2 && x 8 6)
  have b3963 := hb (x 7 3 && x 7 7)
  have b3964 := hb (x 6 4 && x 6 8)
  have b3965 := hb (x 5 5 && x 5 9)
  have b3966 := hb (x 4 6 && x 4 10)
  have b3967 := hb (x 3 7 && x 3 11)
  have b3968 := hb (x 2 8 && x 2 12)
  have b3969 := hb (x 1 9 && x 1 13)
  have b3970 := hb (x 5 1 && x 5 7)
  have b3971 := hb (x 4 2 && x 4 8)
  have b3972 := hb (x 3 3 && x 3 9)
  have b3973 := hb (x 2 4 && x 2 10)
  have b3974 := hb (x 1 5 && x 1 11)
  have b3975 := hb (x 0 6 && x 0 12)
  have b3976 := hb (x (-1) 7 && x (-1) 13)
  have b3977 := hb (x (-2) 8 && x (-2) 14)
  have b3978 := hb (x 7 1 && x 7 7)
  have b3979 := hb (x 6 2 && x 6 8)
  have b3980 := hb (x 5 3 && x 5 9)
  have b3981 := hb (x 4 4 && x 4 10)
  have b3982 := hb (x 3 5 && x 3 11)
  have b3983 := hb (x 2 6 && x 2 12)
  have b3984 := hb (x 1 7 && x 1 13)
  have b3985 := hb (x 0 8 && x 0 14)
  have b3986 := hb (x 4 1 && x 4 8)
  have b3987 := hb (x 3 2 && x 3 9)
  have b3988 := hb (x 2 3 && x 2 10)
  have b3989 := hb (x 1 4 && x 1 11)
  have b3990 := hb (x 0 5 && x 0 12)
  have b3991 := hb (x (-1) 6 && x (-1) 13)
  have b3992 := hb (x (-2) 7 && x (-2) 14)
  have b3993 := hb (x (-5) 1 && x (-5) 11)
  have b3994 := hb (x (-6) 2 && x (-6) 12)
  have b3995 := hb (x (-7) 3 && x (-7) 13)
  have b3996 := hb (x (-8) 4 && x (-8) 14)
  have b3997 := hb (x (-1) 1 && x (-1) 11)
  have b3998 := hb (x (-2) 2 && x (-2) 12)
  have b3999 := hb (x (-3) 3 && x (-3) 13)
  have b4000 := hb (x (-4) 4 && x (-4) 14)
  have b4001 := hb (x 11 1 && x 11 11)
  have b4002 := hb (x 10 2 && x 10 12)
  have b4003 := hb (x 9 3 && x 9 13)
  have b4004 := hb (x 8 4 && x 8 14)
  have b4005 := hb (x 9 1 && x 9 12)
  have b4006 := hb (x 8 2 && x 8 13)
  have b4007 := hb (x 7 3 && x 7 14)
  linarith only [r3790, r3791, r3792, r3793, r3794, r3795, e3796, e3797, e3798, e3799, e3800, e3801, r3802, e3803, e3804, e3805, e3806, e3807, e3808, r3809, r3810, r3811, e3812, e3813, r3814, e3815, e3816, r3817, r3818, r3819, r3820, r3821, r3822, r3823, r3824, r3825, r3826, r3827, r3828, r3829, r3830, r3831, r3832, r3833, r3834, r3835, r3836, r3837, r3838, r3839, r3840, r3841, r3842, r3843, r3844, r3845, r3846, r3847, r3848, b3849, b3850, b3851, b3852, b3853, b3854, b3855, b3856, b3857, b3858, b3859, b3860, b3861, b3862, b3863, b3864, b3865, b3866, b3867, b3868, b3869, b3870, b3871, b3872, b3873, b3874, b3875, b3876, b3877, b3878, b3879, b3880, b3881, b3882, b3883, b3884, b3885, b3886, b3887, b3888, b3889, b3890, b3891, b3892, b3893, b3894, b3895, b3896, b3897, b3898, b3899, b3900, b3901, b3902, b3903, b3904, b3905, b3906, b3907, b3908, b3909, b3910, b3911, b3912, b3913, b3914, b3915, b3916, b3917, b3918, b3919, b3920, b3921, b3922, b3923, b3924, b3925, b3926, b3927, b3928, b3929, b3930, b3931, b3932, b3933, b3934, b3935, b3936, b3937, b3938, b3939, b3940, b3941, b3942, b3943, b3944, b3945, b3946, b3947, b3948, b3949, b3950, b3951, b3952, b3953, b3954, b3955, b3956, b3957, b3958, b3959, b3960, b3961, b3962, b3963, b3964, b3965, b3966, b3967, b3968, b3969, b3970, b3971, b3972, b3973, b3974, b3975, b3976, b3977, b3978, b3979, b3980, b3981, b3982, b3983, b3984, b3985, b3986, b3987, b3988, b3989, b3990, b3991, b3992, b3993, b3994, b3995, b3996, b3997, b3998, b3999, b4000, b4001, b4002, b4003, b4004, b4005, b4006, b4007, d3549, d3541, d3537, d3533, d3525, d3509, d3513, d3473, d3477, d3461, d3453, d3429, d3417, d3405, d3413, d3381, d3365, d3333, d3774, d3373, d3353, d3357, g0, g1, d3618, d3305, d3073, d3085, d3313, d3626, d3622, d3654, d3101, d3277, d3289, d3113, d3121, d3137, d3642, d3145, d3161, d3257, d3205, d3718, d3225, d3249, d3241, d3285, d3770, d3081, d3037, d3341, d3421, d3457, d3517, d3762, d3309, d3369, d3409, d3469, d3261, d3573, d3165, d3650, d3297, d3069, d3153, d3129, d3766, d3077, d3361, d3197, d3569, d3173, d3646, d3117, d3758, d3065, d3125, d3317, d3033, d3337, d3437, d3505, d3325, d3401, d3237, d3722, d3229, d3706, d3189]

theorem cycle_power_fifteen_tight_type_sequence_shape_rules_core_v50_61 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 5).toNat = 0) (g1 : (x 0 6).toNat = 1) : False := cycle_power_fifteen_tight_type_sequence_shape_rules_core_v50_61_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 h114 h23 g0 g1
