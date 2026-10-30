import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_shape_rules_core_v111_120

Topic: combinatorics   Node: 738055395e14

Provenance: helper lemma. Research thread RT-1, open case k = 15 (m = 4) of OP-205 (arXiv:2610.15635, Theorems 1.3-1.4: eq(C_n^k) for k+1 = 2^m, n even, (k+1) not dividing n). Experiment 9757: on the integer window [-24, 24] the layer-free tight-class model leaves 13 class types at the centre, none with an island; on [-32, 32] the six types {0,15}, {0,1,14,15}, {0..3,12..15}, {0..7,12..15}, {0..3,8..15}, {0..15}.

Window refutation for k = 15: in the layer-free tight-class model on the integer line (x p j: the class starting at p contains p + j; inner count 3 per vertex, distances 14, 12, 8 covered exactly once, the other distances covered, classes closed under the tight-class parent map), with x p 1 = x p 14 and x p 2 = x p 3 everywhere, the class at 0 cannot have bit 11 = 1 and bit 12 = 0.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_shape_rules_core_v111_120_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 11).toNat = 1) (g1 : (x 0 12).toNat = 0) : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d10984 : (x 0 3 && x 0 12).toNat = 0 := by
    have r10985 := hand2 (x 0 3) (x 0 12)
    have b10986 := hb (x 0 12)
    have b10987 := hb (x 0 3 && x 0 12)
    clear * - r10985 b10986 b10987 g1
    omega
  have d10988 : (x 0 3).toNat = 1 := by
    have r10989 : (x 0 11).toNat ≤ (x 0 3).toNat := himp _ _ (hp11 0)
    have b10990 := hb (x 0 3)
    have b10991 := hb (x 0 11)
    clear * - r10989 b10990 b10991 g0
    omega
  have d10992 : (x 0 2).toNat = 1 := by
    have r10993 : (x 0 2).toNat = (x 0 3).toNat := congrArg Bool.toNat (h23 0)
    have b10994 := hb (x 0 2)
    have b10995 := hb (x 0 3)
    clear * - r10993 b10994 b10995 d10988
    omega
  have d10996 : (x 0 4).toNat = 0 := by
    have r10997 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
    have b10998 := hb (x 0 4)
    have b10999 := hb (x 0 12)
    clear * - r10997 b10998 b10999 g1
    omega
  have d11000 : (x 0 4 && x 0 11).toNat = 0 := by
    have r11001 := hand1 (x 0 4) (x 0 11)
    have b11002 := hb (x 0 4)
    have b11003 := hb (x 0 4 && x 0 11)
    clear * - r11001 b11002 b11003 d10996
    omega
  have d11004 : (x 0 14).toNat = 1 := by
    have r11005 : (x 0 2).toNat ≤ (x 0 14).toNat := himp _ _ (hp2 0)
    have b11006 := hb (x 0 2)
    have b11007 := hb (x 0 14)
    clear * - r11005 b11006 b11007 d10992
    omega
  have d11008 : (x 0 1).toNat = 1 := by
    have r11009 : (x 0 1).toNat = (x 0 14).toNat := congrArg Bool.toNat (h114 0)
    have b11010 := hb (x 0 1)
    have b11011 := hb (x 0 14)
    clear * - r11009 b11010 b11011 d11004
    omega
  have d11012 : (x 1 14).toNat = 0 := by
    have r11013 : (x 1 14).toNat + (x 0 1).toNat = 1 := by have q := hd14 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11014 := hb (x 0 1)
    have b11015 := hb (x 1 14)
    clear * - r11013 b11014 b11015 d11008
    omega
  have d11016 : (x 1 3 && x 1 14).toNat = 0 := by
    have r11017 := hand2 (x 1 3) (x 1 14)
    have b11018 := hb (x 1 14)
    have b11019 := hb (x 1 3 && x 1 14)
    clear * - r11017 b11018 b11019 d11012
    omega
  have d11020 : (x 1 7 && x 1 14).toNat = 0 := by
    have r11021 := hand2 (x 1 7) (x 1 14)
    have b11022 := hb (x 1 14)
    have b11023 := hb (x 1 7 && x 1 14)
    clear * - r11021 b11022 b11023 d11012
    omega
  have d11024 : (x 1 1).toNat = 0 := by
    have r11025 : (x 1 1).toNat = (x 1 14).toNat := congrArg Bool.toNat (h114 1)
    have b11026 := hb (x 1 1)
    have b11027 := hb (x 1 14)
    clear * - r11025 b11026 b11027 d11012
    omega
  have d11028 : (x 1 13).toNat = 0 := by
    have r11029 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
    have b11030 := hb (x 1 1)
    have b11031 := hb (x 1 13)
    clear * - r11029 b11030 b11031 d11024
    omega
  have d11032 : (x 1 5).toNat = 0 := by
    have r11033 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
    have b11034 := hb (x 1 5)
    have b11035 := hb (x 1 13)
    clear * - r11033 b11034 b11035 d11028
    omega
  have d11036 : (x 1 5 && x 1 12).toNat = 0 := by
    have r11037 := hand1 (x 1 5) (x 1 12)
    have b11038 := hb (x 1 5)
    have b11039 := hb (x 1 5 && x 1 12)
    clear * - r11037 b11038 b11039 d11032
    omega
  have d11040 : (x 2 14).toNat = 1 := by
    have r11041 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11042 := hb (x 1 1)
    have b11043 := hb (x 2 14)
    clear * - r11041 b11042 b11043 d11024
    omega
  have d11044 : (x 2 1).toNat = 1 := by
    have r11045 : (x 2 1).toNat = (x 2 14).toNat := congrArg Bool.toNat (h114 2)
    have b11046 := hb (x 2 1)
    have b11047 := hb (x 2 14)
    clear * - r11045 b11046 b11047 d11040
    omega
  have d11048 : (x 3 14).toNat = 0 := by
    have r11049 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11050 := hb (x 2 1)
    have b11051 := hb (x 3 14)
    clear * - r11049 b11050 b11051 d11044
    omega
  have d11052 : (x 3 3 && x 3 14).toNat = 0 := by
    have r11053 := hand2 (x 3 3) (x 3 14)
    have b11054 := hb (x 3 14)
    have b11055 := hb (x 3 3 && x 3 14)
    clear * - r11053 b11054 b11055 d11048
    omega
  have d11056 : (x 3 1).toNat = 0 := by
    have r11057 : (x 3 1).toNat = (x 3 14).toNat := congrArg Bool.toNat (h114 3)
    have b11058 := hb (x 3 1)
    have b11059 := hb (x 3 14)
    clear * - r11057 b11058 b11059 d11048
    omega
  have d11060 : (x 3 1 && x 3 12).toNat = 0 := by
    have r11061 := hand1 (x 3 1) (x 3 12)
    have b11062 := hb (x 3 1)
    have b11063 := hb (x 3 1 && x 3 12)
    clear * - r11061 b11062 b11063 d11056
    omega
  have d11064 : (x 3 1 && x 3 8).toNat = 0 := by
    have r11065 := hand1 (x 3 1) (x 3 8)
    have b11066 := hb (x 3 1)
    have b11067 := hb (x 3 1 && x 3 8)
    clear * - r11065 b11066 b11067 d11056
    omega
  have d11068 : (x 3 13).toNat = 0 := by
    have r11069 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
    have b11070 := hb (x 3 1)
    have b11071 := hb (x 3 13)
    clear * - r11069 b11070 b11071 d11056
    omega
  have d11072 : (x 3 3 && x 3 13).toNat = 0 := by
    have r11073 := hand2 (x 3 3) (x 3 13)
    have b11074 := hb (x 3 13)
    have b11075 := hb (x 3 3 && x 3 13)
    clear * - r11073 b11074 b11075 d11068
    omega
  have d11076 : (x 3 5).toNat = 0 := by
    have r11077 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
    have b11078 := hb (x 3 5)
    have b11079 := hb (x 3 13)
    clear * - r11077 b11078 b11079 d11068
    omega
  have d11080 : (x 3 5 && x 3 12).toNat = 0 := by
    have r11081 := hand1 (x 3 5) (x 3 12)
    have b11082 := hb (x 3 5)
    have b11083 := hb (x 3 5 && x 3 12)
    clear * - r11081 b11082 b11083 d11076
    omega
  have d11084 : (x 3 9).toNat = 0 := by
    have r11085 : (x 3 9).toNat ≤ (x 3 1).toNat := himp _ _ (hp9 3)
    have b11086 := hb (x 3 1)
    have b11087 := hb (x 3 9)
    clear * - r11085 b11086 b11087 d11056
    omega
  have d11088 : (x 4 14).toNat = 1 := by
    have r11089 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11090 := hb (x 3 1)
    have b11091 := hb (x 4 14)
    clear * - r11089 b11090 b11091 d11056
    omega
  have d11092 : (x 4 1).toNat = 1 := by
    have r11093 : (x 4 1).toNat = (x 4 14).toNat := congrArg Bool.toNat (h114 4)
    have b11094 := hb (x 4 1)
    have b11095 := hb (x 4 14)
    clear * - r11093 b11094 b11095 d11088
    omega
  have d11096 : (x 5 14).toNat = 0 := by
    have r11097 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11098 := hb (x 4 1)
    have b11099 := hb (x 5 14)
    clear * - r11097 b11098 b11099 d11092
    omega
  have d11100 : (x 5 4 && x 5 14).toNat = 0 := by
    have r11101 := hand2 (x 5 4) (x 5 14)
    have b11102 := hb (x 5 14)
    have b11103 := hb (x 5 4 && x 5 14)
    clear * - r11101 b11102 b11103 d11096
    omega
  have d11104 : (x 5 1).toNat = 0 := by
    have r11105 : (x 5 1).toNat = (x 5 14).toNat := congrArg Bool.toNat (h114 5)
    have b11106 := hb (x 5 1)
    have b11107 := hb (x 5 14)
    clear * - r11105 b11106 b11107 d11096
    omega
  have d11108 : (x 5 1 && x 5 12).toNat = 0 := by
    have r11109 := hand1 (x 5 1) (x 5 12)
    have b11110 := hb (x 5 1)
    have b11111 := hb (x 5 1 && x 5 12)
    clear * - r11109 b11110 b11111 d11104
    omega
  have d11112 : (x 5 1 && x 5 11).toNat = 0 := by
    have r11113 := hand1 (x 5 1) (x 5 11)
    have b11114 := hb (x 5 1)
    have b11115 := hb (x 5 1 && x 5 11)
    clear * - r11113 b11114 b11115 d11104
    omega
  have d11116 : (x 5 1 && x 5 8).toNat = 0 := by
    have r11117 := hand1 (x 5 1) (x 5 8)
    have b11118 := hb (x 5 1)
    have b11119 := hb (x 5 1 && x 5 8)
    clear * - r11117 b11118 b11119 d11104
    omega
  have d11120 : (x 5 13).toNat = 0 := by
    have r11121 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
    have b11122 := hb (x 5 1)
    have b11123 := hb (x 5 13)
    clear * - r11121 b11122 b11123 d11104
    omega
  have d11124 : (x 5 4 && x 5 13).toNat = 0 := by
    have r11125 := hand2 (x 5 4) (x 5 13)
    have b11126 := hb (x 5 13)
    have b11127 := hb (x 5 4 && x 5 13)
    clear * - r11125 b11126 b11127 d11120
    omega
  have d11128 : (x 5 5).toNat = 0 := by
    have r11129 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
    have b11130 := hb (x 5 5)
    have b11131 := hb (x 5 13)
    clear * - r11129 b11130 b11131 d11120
    omega
  have d11132 : (x 6 14).toNat = 1 := by
    have r11133 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11134 := hb (x 5 1)
    have b11135 := hb (x 6 14)
    clear * - r11133 b11134 b11135 d11104
    omega
  have d11136 : (x 6 1).toNat = 1 := by
    have r11137 : (x 6 1).toNat = (x 6 14).toNat := congrArg Bool.toNat (h114 6)
    have b11138 := hb (x 6 1)
    have b11139 := hb (x 6 14)
    clear * - r11137 b11138 b11139 d11132
    omega
  have d11140 : (x 7 14).toNat = 0 := by
    have r11141 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11142 := hb (x 6 1)
    have b11143 := hb (x 7 14)
    clear * - r11141 b11142 b11143 d11136
    omega
  have d11144 : (x 7 3 && x 7 14).toNat = 0 := by
    have r11145 := hand2 (x 7 3) (x 7 14)
    have b11146 := hb (x 7 14)
    have b11147 := hb (x 7 3 && x 7 14)
    clear * - r11145 b11146 b11147 d11140
    omega
  have d11148 : (x 7 1).toNat = 0 := by
    have r11149 : (x 7 1).toNat = (x 7 14).toNat := congrArg Bool.toNat (h114 7)
    have b11150 := hb (x 7 1)
    have b11151 := hb (x 7 14)
    clear * - r11149 b11150 b11151 d11140
    omega
  have d11152 : (x 7 1 && x 7 8).toNat = 0 := by
    have r11153 := hand1 (x 7 1) (x 7 8)
    have b11154 := hb (x 7 1)
    have b11155 := hb (x 7 1 && x 7 8)
    clear * - r11153 b11154 b11155 d11148
    omega
  have d11156 : (x 7 13).toNat = 0 := by
    have r11157 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
    have b11158 := hb (x 7 1)
    have b11159 := hb (x 7 13)
    clear * - r11157 b11158 b11159 d11148
    omega
  have d11160 : (x 7 3 && x 7 13).toNat = 0 := by
    have r11161 := hand2 (x 7 3) (x 7 13)
    have b11162 := hb (x 7 13)
    have b11163 := hb (x 7 3 && x 7 13)
    clear * - r11161 b11162 b11163 d11156
    omega
  have d11164 : (x 7 5).toNat = 0 := by
    have r11165 : (x 7 5).toNat ≤ (x 7 13).toNat := himp _ _ (hp5 7)
    have b11166 := hb (x 7 5)
    have b11167 := hb (x 7 13)
    clear * - r11165 b11166 b11167 d11156
    omega
  have d11168 : (x 7 9).toNat = 0 := by
    have r11169 : (x 7 9).toNat ≤ (x 7 1).toNat := himp _ _ (hp9 7)
    have b11170 := hb (x 7 1)
    have b11171 := hb (x 7 9)
    clear * - r11169 b11170 b11171 d11148
    omega
  have d11172 : (x 8 14).toNat = 1 := by
    have r11173 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11174 := hb (x 7 1)
    have b11175 := hb (x 8 14)
    clear * - r11173 b11174 b11175 d11148
    omega
  have d11176 : (x 8 1).toNat = 1 := by
    have r11177 : (x 8 1).toNat = (x 8 14).toNat := congrArg Bool.toNat (h114 8)
    have b11178 := hb (x 8 1)
    have b11179 := hb (x 8 14)
    clear * - r11177 b11178 b11179 d11172
    omega
  have d11180 : (x 9 14).toNat = 0 := by
    have r11181 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11182 := hb (x 8 1)
    have b11183 := hb (x 9 14)
    clear * - r11181 b11182 b11183 d11176
    omega
  have d11184 : (x 9 3 && x 9 14).toNat = 0 := by
    have r11185 := hand2 (x 9 3) (x 9 14)
    have b11186 := hb (x 9 14)
    have b11187 := hb (x 9 3 && x 9 14)
    clear * - r11185 b11186 b11187 d11180
    omega
  have d11188 : (x 9 1).toNat = 0 := by
    have r11189 : (x 9 1).toNat = (x 9 14).toNat := congrArg Bool.toNat (h114 9)
    have b11190 := hb (x 9 1)
    have b11191 := hb (x 9 14)
    clear * - r11189 b11190 b11191 d11180
    omega
  have d11192 : (x 9 1 && x 9 12).toNat = 0 := by
    have r11193 := hand1 (x 9 1) (x 9 12)
    have b11194 := hb (x 9 1)
    have b11195 := hb (x 9 1 && x 9 12)
    clear * - r11193 b11194 b11195 d11188
    omega
  have d11196 : (x 9 1 && x 9 11).toNat = 0 := by
    have r11197 := hand1 (x 9 1) (x 9 11)
    have b11198 := hb (x 9 1)
    have b11199 := hb (x 9 1 && x 9 11)
    clear * - r11197 b11198 b11199 d11188
    omega
  have d11200 : (x 9 9).toNat = 0 := by
    have r11201 : (x 9 9).toNat ≤ (x 9 1).toNat := himp _ _ (hp9 9)
    have b11202 := hb (x 9 1)
    have b11203 := hb (x 9 9)
    clear * - r11201 b11202 b11203 d11188
    omega
  have d11204 : (x 9 6).toNat = 0 := by
    have r11205 : (x 9 6).toNat ≤ (x 9 14).toNat := himp _ _ (hp6 9)
    have b11206 := hb (x 9 6)
    have b11207 := hb (x 9 14)
    clear * - r11205 b11206 b11207 d11180
    omega
  have d11208 : (x 9 2).toNat = 0 := by
    have r11209 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
    have b11210 := hb (x 9 2)
    have b11211 := hb (x 9 14)
    clear * - r11209 b11210 b11211 d11180
    omega
  have d11212 : (x 9 3).toNat = 0 := by
    have r11213 : (x 9 2).toNat = (x 9 3).toNat := congrArg Bool.toNat (h23 9)
    have b11214 := hb (x 9 2)
    have b11215 := hb (x 9 3)
    clear * - r11213 b11214 b11215 d11208
    omega
  have d11216 : (x 9 11).toNat = 0 := by
    have r11217 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
    have b11218 := hb (x 9 3)
    have b11219 := hb (x 9 11)
    clear * - r11217 b11218 b11219 d11212
    omega
  have d11220 : (x 9 10).toNat = 0 := by
    have r11221 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
    have b11222 := hb (x 9 2)
    have b11223 := hb (x 9 10)
    clear * - r11221 b11222 b11223 d11208
    omega
  have d11224 : (x 7 6).toNat = 0 := by
    have r11225 : (x 7 6).toNat ≤ (x 7 14).toNat := himp _ _ (hp6 7)
    have b11226 := hb (x 7 6)
    have b11227 := hb (x 7 14)
    clear * - r11225 b11226 b11227 d11140
    omega
  have d11228 : (x 7 2).toNat = 0 := by
    have r11229 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
    have b11230 := hb (x 7 2)
    have b11231 := hb (x 7 14)
    clear * - r11229 b11230 b11231 d11140
    omega
  have d11232 : (x 7 2 && x 7 12).toNat = 0 := by
    have r11233 := hand1 (x 7 2) (x 7 12)
    have b11234 := hb (x 7 2)
    have b11235 := hb (x 7 2 && x 7 12)
    clear * - r11233 b11234 b11235 d11228
    omega
  have d11236 : (x 7 2 && x 7 11).toNat = 0 := by
    have r11237 := hand1 (x 7 2) (x 7 11)
    have b11238 := hb (x 7 2)
    have b11239 := hb (x 7 2 && x 7 11)
    clear * - r11237 b11238 b11239 d11228
    omega
  have d11240 : (x 7 10).toNat = 0 := by
    have r11241 : (x 7 10).toNat ≤ (x 7 2).toNat := himp _ _ (hp10 7)
    have b11242 := hb (x 7 2)
    have b11243 := hb (x 7 10)
    clear * - r11241 b11242 b11243 d11228
    omega
  have d11244 : (x 5 6).toNat = 0 := by
    have r11245 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
    have b11246 := hb (x 5 6)
    have b11247 := hb (x 5 14)
    clear * - r11245 b11246 b11247 d11096
    omega
  have d11248 : (x 5 2).toNat = 0 := by
    have r11249 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
    have b11250 := hb (x 5 2)
    have b11251 := hb (x 5 14)
    clear * - r11249 b11250 b11251 d11096
    omega
  have d11252 : (x 5 3).toNat = 0 := by
    have r11253 : (x 5 2).toNat = (x 5 3).toNat := congrArg Bool.toNat (h23 5)
    have b11254 := hb (x 5 2)
    have b11255 := hb (x 5 3)
    clear * - r11253 b11254 b11255 d11248
    omega
  have d11256 : (x 5 3 && x 5 10).toNat = 0 := by
    have r11257 := hand1 (x 5 3) (x 5 10)
    have b11258 := hb (x 5 3)
    have b11259 := hb (x 5 3 && x 5 10)
    clear * - r11257 b11258 b11259 d11252
    omega
  have d11260 : (x 5 11).toNat = 0 := by
    have r11261 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
    have b11262 := hb (x 5 3)
    have b11263 := hb (x 5 11)
    clear * - r11261 b11262 b11263 d11252
    omega
  have d11264 : (x 5 10).toNat = 0 := by
    have r11265 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
    have b11266 := hb (x 5 2)
    have b11267 := hb (x 5 10)
    clear * - r11265 b11266 b11267 d11248
    omega
  have d11268 : (x 3 6).toNat = 0 := by
    have r11269 : (x 3 6).toNat ≤ (x 3 14).toNat := himp _ _ (hp6 3)
    have b11270 := hb (x 3 6)
    have b11271 := hb (x 3 14)
    clear * - r11269 b11270 b11271 d11048
    omega
  have d11272 : (x 3 2).toNat = 0 := by
    have r11273 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
    have b11274 := hb (x 3 2)
    have b11275 := hb (x 3 14)
    clear * - r11273 b11274 b11275 d11048
    omega
  have d11276 : (x 3 3).toNat = 0 := by
    have r11277 : (x 3 2).toNat = (x 3 3).toNat := congrArg Bool.toNat (h23 3)
    have b11278 := hb (x 3 2)
    have b11279 := hb (x 3 3)
    clear * - r11277 b11278 b11279 d11272
    omega
  have d11280 : (x 3 3 && x 3 10).toNat = 0 := by
    have r11281 := hand1 (x 3 3) (x 3 10)
    have b11282 := hb (x 3 3)
    have b11283 := hb (x 3 3 && x 3 10)
    clear * - r11281 b11282 b11283 d11276
    omega
  have d11284 : (x 3 10).toNat = 0 := by
    have r11285 : (x 3 10).toNat ≤ (x 3 2).toNat := himp _ _ (hp10 3)
    have b11286 := hb (x 3 2)
    have b11287 := hb (x 3 10)
    clear * - r11285 b11286 b11287 d11272
    omega
  have d11288 : (x 1 6).toNat = 0 := by
    have r11289 : (x 1 6).toNat ≤ (x 1 14).toNat := himp _ _ (hp6 1)
    have b11290 := hb (x 1 6)
    have b11291 := hb (x 1 14)
    clear * - r11289 b11290 b11291 d11012
    omega
  have d11292 : (x 1 2).toNat = 0 := by
    have r11293 : (x 1 2).toNat ≤ (x 1 14).toNat := himp _ _ (hp2 1)
    have b11294 := hb (x 1 2)
    have b11295 := hb (x 1 14)
    clear * - r11293 b11294 b11295 d11012
    omega
  have d11296 : (x 1 2 && x 1 12).toNat = 0 := by
    have r11297 := hand1 (x 1 2) (x 1 12)
    have b11298 := hb (x 1 2)
    have b11299 := hb (x 1 2 && x 1 12)
    clear * - r11297 b11298 b11299 d11292
    omega
  have d11300 : (x 1 2 && x 1 11).toNat = 0 := by
    have r11301 := hand1 (x 1 2) (x 1 11)
    have b11302 := hb (x 1 2)
    have b11303 := hb (x 1 2 && x 1 11)
    clear * - r11301 b11302 b11303 d11292
    omega
  have d11304 : (x 1 3).toNat = 0 := by
    have r11305 : (x 1 2).toNat = (x 1 3).toNat := congrArg Bool.toNat (h23 1)
    have b11306 := hb (x 1 2)
    have b11307 := hb (x 1 3)
    clear * - r11305 b11306 b11307 d11292
    omega
  have d11308 : (x 1 3 && x 1 10).toNat = 0 := by
    have r11309 := hand1 (x 1 3) (x 1 10)
    have b11310 := hb (x 1 3)
    have b11311 := hb (x 1 3 && x 1 10)
    clear * - r11309 b11310 b11311 d11304
    omega
  have d11312 : (x 1 11).toNat = 0 := by
    have r11313 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
    have b11314 := hb (x 1 3)
    have b11315 := hb (x 1 11)
    clear * - r11313 b11314 b11315 d11304
    omega
  have d11316 : (x 1 10).toNat = 0 := by
    have r11317 : (x 1 10).toNat ≤ (x 1 2).toNat := himp _ _ (hp10 1)
    have b11318 := hb (x 1 2)
    have b11319 := hb (x 1 10)
    clear * - r11317 b11318 b11319 d11292
    omega
  have d11320 : (x (-1) 1).toNat = 0 := by
    have r11321 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11322 := hb (x (-1) 1)
    have b11323 := hb (x 0 14)
    clear * - r11321 b11322 b11323 d11004
    omega
  have d11324 : (x (-1) 14).toNat = 0 := by
    have r11325 : (x (-1) 1).toNat = (x (-1) 14).toNat := congrArg Bool.toNat (h114 (-1))
    have b11326 := hb (x (-1) 1)
    have b11327 := hb (x (-1) 14)
    clear * - r11325 b11326 b11327 d11320
    omega
  have d11328 : (x (-1) 4 && x (-1) 14).toNat = 0 := by
    have r11329 := hand2 (x (-1) 4) (x (-1) 14)
    have b11330 := hb (x (-1) 14)
    have b11331 := hb (x (-1) 4 && x (-1) 14)
    clear * - r11329 b11330 b11331 d11324
    omega
  have d11332 : (x (-1) 7 && x (-1) 14).toNat = 0 := by
    have r11333 := hand2 (x (-1) 7) (x (-1) 14)
    have b11334 := hb (x (-1) 14)
    have b11335 := hb (x (-1) 7 && x (-1) 14)
    clear * - r11333 b11334 b11335 d11324
    omega
  have d11336 : (x (-1) 6).toNat = 0 := by
    have r11337 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
    have b11338 := hb (x (-1) 6)
    have b11339 := hb (x (-1) 14)
    clear * - r11337 b11338 b11339 d11324
    omega
  have d11340 : (x (-1) 2).toNat = 0 := by
    have r11341 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
    have b11342 := hb (x (-1) 2)
    have b11343 := hb (x (-1) 14)
    clear * - r11341 b11342 b11343 d11324
    omega
  have d11344 : (x (-1) 3).toNat = 0 := by
    have r11345 : (x (-1) 2).toNat = (x (-1) 3).toNat := congrArg Bool.toNat (h23 (-1))
    have b11346 := hb (x (-1) 2)
    have b11347 := hb (x (-1) 3)
    clear * - r11345 b11346 b11347 d11340
    omega
  have d11348 : (x (-1) 13).toNat = 0 := by
    have r11349 : (x (-1) 13).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp13 (-1))
    have b11350 := hb (x (-1) 1)
    have b11351 := hb (x (-1) 13)
    clear * - r11349 b11350 b11351 d11320
    omega
  have d11352 : (x (-1) 4 && x (-1) 13).toNat = 0 := by
    have r11353 := hand2 (x (-1) 4) (x (-1) 13)
    have b11354 := hb (x (-1) 13)
    have b11355 := hb (x (-1) 4 && x (-1) 13)
    clear * - r11353 b11354 b11355 d11348
    omega
  have d11356 : (x (-1) 5).toNat = 0 := by
    have r11357 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
    have b11358 := hb (x (-1) 5)
    have b11359 := hb (x (-1) 13)
    clear * - r11357 b11358 b11359 d11348
    omega
  have d11360 : (x (-1) 5 && x (-1) 12).toNat = 0 := by
    have r11361 := hand1 (x (-1) 5) (x (-1) 12)
    have b11362 := hb (x (-1) 5)
    have b11363 := hb (x (-1) 5 && x (-1) 12)
    clear * - r11361 b11362 b11363 d11356
    omega
  have d11364 : (x (-1) 9).toNat = 0 := by
    have r11365 : (x (-1) 9).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp9 (-1))
    have b11366 := hb (x (-1) 1)
    have b11367 := hb (x (-1) 9)
    clear * - r11365 b11366 b11367 d11320
    omega
  have d11368 : (x (-2) 1).toNat = 1 := by
    have r11369 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11370 := hb (x (-2) 1)
    have b11371 := hb (x (-1) 14)
    clear * - r11369 b11370 b11371 d11324
    omega
  have d11372 : (x (-2) 14).toNat = 1 := by
    have r11373 : (x (-2) 1).toNat = (x (-2) 14).toNat := congrArg Bool.toNat (h114 (-2))
    have b11374 := hb (x (-2) 1)
    have b11375 := hb (x (-2) 14)
    clear * - r11373 b11374 b11375 d11368
    omega
  have d11376 : (x (-3) 1).toNat = 0 := by
    have r11377 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11378 := hb (x (-3) 1)
    have b11379 := hb (x (-2) 14)
    clear * - r11377 b11378 b11379 d11372
    omega
  have d11380 : (x (-3) 1 && x (-3) 11).toNat = 0 := by
    have r11381 := hand1 (x (-3) 1) (x (-3) 11)
    have b11382 := hb (x (-3) 1)
    have b11383 := hb (x (-3) 1 && x (-3) 11)
    clear * - r11381 b11382 b11383 d11376
    omega
  have d11384 : (x (-3) 14).toNat = 0 := by
    have r11385 : (x (-3) 1).toNat = (x (-3) 14).toNat := congrArg Bool.toNat (h114 (-3))
    have b11386 := hb (x (-3) 1)
    have b11387 := hb (x (-3) 14)
    clear * - r11385 b11386 b11387 d11376
    omega
  have d11388 : (x (-3) 7 && x (-3) 14).toNat = 0 := by
    have r11389 := hand2 (x (-3) 7) (x (-3) 14)
    have b11390 := hb (x (-3) 14)
    have b11391 := hb (x (-3) 7 && x (-3) 14)
    clear * - r11389 b11390 b11391 d11384
    omega
  have d11392 : (x (-3) 6).toNat = 0 := by
    have r11393 : (x (-3) 6).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp6 (-3))
    have b11394 := hb (x (-3) 6)
    have b11395 := hb (x (-3) 14)
    clear * - r11393 b11394 b11395 d11384
    omega
  have d11396 : (x (-3) 2).toNat = 0 := by
    have r11397 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
    have b11398 := hb (x (-3) 2)
    have b11399 := hb (x (-3) 14)
    clear * - r11397 b11398 b11399 d11384
    omega
  have d11400 : (x (-3) 3).toNat = 0 := by
    have r11401 : (x (-3) 2).toNat = (x (-3) 3).toNat := congrArg Bool.toNat (h23 (-3))
    have b11402 := hb (x (-3) 2)
    have b11403 := hb (x (-3) 3)
    clear * - r11401 b11402 b11403 d11396
    omega
  have d11404 : (x (-3) 11).toNat = 0 := by
    have r11405 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
    have b11406 := hb (x (-3) 3)
    have b11407 := hb (x (-3) 11)
    clear * - r11405 b11406 b11407 d11400
    omega
  have d11408 : (x (-3) 9).toNat = 0 := by
    have r11409 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
    have b11410 := hb (x (-3) 1)
    have b11411 := hb (x (-3) 9)
    clear * - r11409 b11410 b11411 d11376
    omega
  have d11412 : (x (-4) 1).toNat = 1 := by
    have r11413 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11414 := hb (x (-4) 1)
    have b11415 := hb (x (-3) 14)
    clear * - r11413 b11414 b11415 d11384
    omega
  have d11416 : (x (-4) 14).toNat = 1 := by
    have r11417 : (x (-4) 1).toNat = (x (-4) 14).toNat := congrArg Bool.toNat (h114 (-4))
    have b11418 := hb (x (-4) 1)
    have b11419 := hb (x (-4) 14)
    clear * - r11417 b11418 b11419 d11412
    omega
  have d11420 : (x (-5) 1).toNat = 0 := by
    have r11421 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11422 := hb (x (-5) 1)
    have b11423 := hb (x (-4) 14)
    clear * - r11421 b11422 b11423 d11416
    omega
  have d11424 : (x (-5) 1 && x (-5) 11).toNat = 0 := by
    have r11425 := hand1 (x (-5) 1) (x (-5) 11)
    have b11426 := hb (x (-5) 1)
    have b11427 := hb (x (-5) 1 && x (-5) 11)
    clear * - r11425 b11426 b11427 d11420
    omega
  have d11428 : (x (-5) 14).toNat = 0 := by
    have r11429 : (x (-5) 1).toNat = (x (-5) 14).toNat := congrArg Bool.toNat (h114 (-5))
    have b11430 := hb (x (-5) 1)
    have b11431 := hb (x (-5) 14)
    clear * - r11429 b11430 b11431 d11420
    omega
  have d11432 : (x (-5) 2).toNat = 0 := by
    have r11433 : (x (-5) 2).toNat ≤ (x (-5) 14).toNat := himp _ _ (hp2 (-5))
    have b11434 := hb (x (-5) 2)
    have b11435 := hb (x (-5) 14)
    clear * - r11433 b11434 b11435 d11428
    omega
  have d11436 : (x (-5) 3).toNat = 0 := by
    have r11437 : (x (-5) 2).toNat = (x (-5) 3).toNat := congrArg Bool.toNat (h23 (-5))
    have b11438 := hb (x (-5) 2)
    have b11439 := hb (x (-5) 3)
    clear * - r11437 b11438 b11439 d11432
    omega
  have d11440 : (x (-5) 3 && x (-5) 13).toNat = 0 := by
    have r11441 := hand1 (x (-5) 3) (x (-5) 13)
    have b11442 := hb (x (-5) 3)
    have b11443 := hb (x (-5) 3 && x (-5) 13)
    clear * - r11441 b11442 b11443 d11436
    omega
  have d11444 : (x (-5) 11).toNat = 0 := by
    have r11445 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
    have b11446 := hb (x (-5) 3)
    have b11447 := hb (x (-5) 11)
    clear * - r11445 b11446 b11447 d11436
    omega
  have d11448 : (x (-5) 13).toNat = 0 := by
    have r11449 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
    have b11450 := hb (x (-5) 1)
    have b11451 := hb (x (-5) 13)
    clear * - r11449 b11450 b11451 d11420
    omega
  have d11452 : (x (-5) 5).toNat = 0 := by
    have r11453 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
    have b11454 := hb (x (-5) 5)
    have b11455 := hb (x (-5) 13)
    clear * - r11453 b11454 b11455 d11448
    omega
  have d11456 : (x (-5) 9).toNat = 0 := by
    have r11457 : (x (-5) 9).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp9 (-5))
    have b11458 := hb (x (-5) 1)
    have b11459 := hb (x (-5) 9)
    clear * - r11457 b11458 b11459 d11420
    omega
  have d11460 : (x (-6) 1).toNat = 1 := by
    have r11461 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11462 := hb (x (-6) 1)
    have b11463 := hb (x (-5) 14)
    clear * - r11461 b11462 b11463 d11428
    omega
  have d11464 : (x (-6) 14).toNat = 1 := by
    have r11465 : (x (-6) 1).toNat = (x (-6) 14).toNat := congrArg Bool.toNat (h114 (-6))
    have b11466 := hb (x (-6) 1)
    have b11467 := hb (x (-6) 14)
    clear * - r11465 b11466 b11467 d11460
    omega
  have d11468 : (x (-7) 1).toNat = 0 := by
    have r11469 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11470 := hb (x (-7) 1)
    have b11471 := hb (x (-6) 14)
    clear * - r11469 b11470 b11471 d11464
    omega
  have d11472 : (x (-7) 14).toNat = 0 := by
    have r11473 : (x (-7) 1).toNat = (x (-7) 14).toNat := congrArg Bool.toNat (h114 (-7))
    have b11474 := hb (x (-7) 1)
    have b11475 := hb (x (-7) 14)
    clear * - r11473 b11474 b11475 d11468
    omega
  have d11476 : (x (-7) 2).toNat = 0 := by
    have r11477 : (x (-7) 2).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp2 (-7))
    have b11478 := hb (x (-7) 2)
    have b11479 := hb (x (-7) 14)
    clear * - r11477 b11478 b11479 d11472
    omega
  have d11480 : (x (-7) 3).toNat = 0 := by
    have r11481 : (x (-7) 2).toNat = (x (-7) 3).toNat := congrArg Bool.toNat (h23 (-7))
    have b11482 := hb (x (-7) 2)
    have b11483 := hb (x (-7) 3)
    clear * - r11481 b11482 b11483 d11476
    omega
  have d11484 : (x (-7) 3 && x (-7) 13).toNat = 0 := by
    have r11485 := hand1 (x (-7) 3) (x (-7) 13)
    have b11486 := hb (x (-7) 3)
    have b11487 := hb (x (-7) 3 && x (-7) 13)
    clear * - r11485 b11486 b11487 d11480
    omega
  have d11488 : (x (-7) 11).toNat = 0 := by
    have r11489 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
    have b11490 := hb (x (-7) 3)
    have b11491 := hb (x (-7) 11)
    clear * - r11489 b11490 b11491 d11480
    omega
  have d11492 : (x (-7) 13).toNat = 0 := by
    have r11493 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
    have b11494 := hb (x (-7) 1)
    have b11495 := hb (x (-7) 13)
    clear * - r11493 b11494 b11495 d11468
    omega
  have d11496 : (x (-7) 5).toNat = 0 := by
    have r11497 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
    have b11498 := hb (x (-7) 5)
    have b11499 := hb (x (-7) 13)
    clear * - r11497 b11498 b11499 d11492
    omega
  have d11500 : (x (-8) 1).toNat = 1 := by
    have r11501 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11502 := hb (x (-8) 1)
    have b11503 := hb (x (-7) 14)
    clear * - r11501 b11502 b11503 d11472
    omega
  have d11504 : (x (-8) 14).toNat = 1 := by
    have r11505 : (x (-8) 1).toNat = (x (-8) 14).toNat := congrArg Bool.toNat (h114 (-8))
    have b11506 := hb (x (-8) 1)
    have b11507 := hb (x (-8) 14)
    clear * - r11505 b11506 b11507 d11500
    omega
  have d11508 : (x (-9) 1).toNat = 0 := by
    have r11509 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11510 := hb (x (-9) 1)
    have b11511 := hb (x (-8) 14)
    clear * - r11509 b11510 b11511 d11504
    omega
  have d11512 : (x (-9) 13).toNat = 0 := by
    have r11513 : (x (-9) 13).toNat ≤ (x (-9) 1).toNat := himp _ _ (hp13 (-9))
    have b11514 := hb (x (-9) 1)
    have b11515 := hb (x (-9) 13)
    clear * - r11513 b11514 b11515 d11508
    omega
  have d11516 : (x (-9) 5).toNat = 0 := by
    have r11517 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
    have b11518 := hb (x (-9) 5)
    have b11519 := hb (x (-9) 13)
    clear * - r11517 b11518 b11519 d11512
    omega
  have d11520 : (x 3 12).toNat = 0 := by
    have r11521 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11522 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e11523 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b11524 := hb (x 0 3)
    have b11525 := hb (x 1 2)
    have b11526 := hb (x 2 13)
    have b11527 := hb (x 3 12)
    clear * - r11521 e11522 e11523 b11524 b11525 b11526 b11527 d11292 d10988
    omega
  have d11528 : (x 3 4).toNat = 0 := by
    have r11529 : (x 3 4).toNat ≤ (x 3 12).toNat := himp _ _ (hp4 3)
    have b11530 := hb (x 3 4)
    have b11531 := hb (x 3 12)
    clear * - r11529 b11530 b11531 d11520
    omega
  have d11532 : (x 2 13).toNat = 0 := by
    have r11533 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11534 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e11535 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b11536 := hb (x 0 3)
    have b11537 := hb (x 1 2)
    have b11538 := hb (x 2 13)
    have b11539 := hb (x 3 12)
    clear * - r11533 e11534 e11535 b11536 b11537 b11538 b11539 d11520 d11292 d10988
    omega
  have d11540 : (x 2 2 && x 2 13).toNat = 0 := by
    have r11541 := hand2 (x 2 2) (x 2 13)
    have b11542 := hb (x 2 13)
    have b11543 := hb (x 2 2 && x 2 13)
    clear * - r11541 b11542 b11543 d11532
    omega
  have d11544 : (x 2 6 && x 2 13).toNat = 0 := by
    have r11545 := hand2 (x 2 6) (x 2 13)
    have b11546 := hb (x 2 13)
    have b11547 := hb (x 2 6 && x 2 13)
    clear * - r11545 b11546 b11547 d11532
    omega
  have d11548 : (x 2 5).toNat = 0 := by
    have r11549 : (x 2 5).toNat ≤ (x 2 13).toNat := himp _ _ (hp5 2)
    have b11550 := hb (x 2 5)
    have b11551 := hb (x 2 13)
    clear * - r11549 b11550 b11551 d11532
    omega
  have d11552 : (x 2 12).toNat = 0 := by
    have r11553 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11554 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e11555 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b11556 := hb (x (-1) 3)
    have b11557 := hb (x 0 2)
    have b11558 := hb (x 1 13)
    have b11559 := hb (x 2 12)
    clear * - r11553 e11554 e11555 b11556 b11557 b11558 b11559 d11028 d10992 d11344
    omega
  have d11560 : (x 2 4).toNat = 0 := by
    have r11561 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
    have b11562 := hb (x 2 4)
    have b11563 := hb (x 2 12)
    clear * - r11561 b11562 b11563 d11552
    omega
  have d11564 : (x 2 4 && x 2 14).toNat = 0 := by
    have r11565 := hand1 (x 2 4) (x 2 14)
    have b11566 := hb (x 2 4)
    have b11567 := hb (x 2 4 && x 2 14)
    clear * - r11565 b11566 b11567 d11560
    omega
  have d11568 : (x 2 4 && x 2 11).toNat = 0 := by
    have r11569 := hand1 (x 2 4) (x 2 11)
    have b11570 := hb (x 2 4)
    have b11571 := hb (x 2 4 && x 2 11)
    clear * - r11569 b11570 b11571 d11560
    omega
  have d11572 : (x (-2) 2).toNat = 1 := by
    have r11573 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11574 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e11575 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b11576 := hb (x (-3) 3)
    have b11577 := hb (x (-2) 2)
    have b11578 := hb (x (-1) 13)
    have b11579 := hb (x 0 12)
    clear * - r11573 e11574 e11575 b11576 b11577 b11578 b11579 g1 d11348 d11400
    omega
  have d11580 : (x (-2) 3).toNat = 1 := by
    have r11581 : (x (-2) 2).toNat = (x (-2) 3).toNat := congrArg Bool.toNat (h23 (-2))
    have b11582 := hb (x (-2) 2)
    have b11583 := hb (x (-2) 3)
    clear * - r11581 b11582 b11583 d11572
    omega
  have d11584 : (x 1 12).toNat = 0 := by
    have r11585 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11586 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e11587 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b11588 := hb (x (-2) 3)
    have b11589 := hb (x (-1) 2)
    have b11590 := hb (x 0 13)
    have b11591 := hb (x 1 12)
    clear * - r11585 e11586 e11587 b11588 b11589 b11590 b11591 d11340 d11580
    omega
  have d11592 : (x 1 4).toNat = 0 := by
    have r11593 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
    have b11594 := hb (x 1 4)
    have b11595 := hb (x 1 12)
    clear * - r11593 b11594 b11595 d11584
    omega
  have d11596 : (x 0 13).toNat = 0 := by
    have r11597 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11598 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e11599 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b11600 := hb (x (-2) 3)
    have b11601 := hb (x (-1) 2)
    have b11602 := hb (x 0 13)
    have b11603 := hb (x 1 12)
    clear * - r11597 e11598 e11599 b11600 b11601 b11602 b11603 d11584 d11340 d11580
    omega
  have d11604 : (x 0 3 && x 0 13).toNat = 0 := by
    have r11605 := hand2 (x 0 3) (x 0 13)
    have b11606 := hb (x 0 13)
    have b11607 := hb (x 0 3 && x 0 13)
    clear * - r11605 b11606 b11607 d11596
    omega
  have d11608 : (x 0 6 && x 0 13).toNat = 0 := by
    have r11609 := hand2 (x 0 6) (x 0 13)
    have b11610 := hb (x 0 13)
    have b11611 := hb (x 0 6 && x 0 13)
    clear * - r11609 b11610 b11611 d11596
    omega
  have d11612 : (x 0 5).toNat = 0 := by
    have r11613 : (x 0 5).toNat ≤ (x 0 13).toNat := himp _ _ (hp5 0)
    have b11614 := hb (x 0 5)
    have b11615 := hb (x 0 13)
    clear * - r11613 b11614 b11615 d11596
    omega
  have d11616 : (x 4 11).toNat = 1 := by
    have r11617 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11618 := hb (x 0 4)
    have b11619 := hb (x 4 11)
    have b11620 := hb (x 3 1 && x 3 12)
    have b11621 := hb (x 2 2 && x 2 13)
    have b11622 := hb (x 1 3 && x 1 14)
    clear * - r11617 b11618 b11619 b11620 b11621 b11622 d11060 d11540 d11016 d10996
    omega
  have d11623 : (x 4 3).toNat = 1 := by
    have r11624 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
    have b11625 := hb (x 4 3)
    have b11626 := hb (x 4 11)
    clear * - r11624 b11625 b11626 d11616
    omega
  have d11627 : (x 4 2).toNat = 1 := by
    have r11628 : (x 4 2).toNat = (x 4 3).toNat := congrArg Bool.toNat (h23 4)
    have b11629 := hb (x 4 2)
    have b11630 := hb (x 4 3)
    clear * - r11628 b11629 b11630 d11623
    omega
  have d11631 : (x 6 12).toNat = 0 := by
    have r11632 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11633 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e11634 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b11635 := hb (x 3 3)
    have b11636 := hb (x 4 2)
    have b11637 := hb (x 5 13)
    have b11638 := hb (x 6 12)
    clear * - r11632 e11633 e11634 b11635 b11636 b11637 b11638 d11120 d11627 d11276
    omega
  have d11639 : (x 6 3 && x 6 12).toNat = 0 := by
    have r11640 := hand2 (x 6 3) (x 6 12)
    have b11641 := hb (x 6 12)
    have b11642 := hb (x 6 3 && x 6 12)
    clear * - r11640 b11641 b11642 d11631
    omega
  have d11643 : (x 6 4).toNat = 0 := by
    have r11644 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
    have b11645 := hb (x 6 4)
    have b11646 := hb (x 6 12)
    clear * - r11644 b11645 b11646 d11631
    omega
  have d11647 : (x 6 4 && x 6 14).toNat = 0 := by
    have r11648 := hand1 (x 6 4) (x 6 14)
    have b11649 := hb (x 6 4)
    have b11650 := hb (x 6 4 && x 6 14)
    clear * - r11648 b11649 b11650 d11643
    omega
  have d11651 : (x 7 12).toNat = 0 := by
    have r11652 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11653 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e11654 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b11655 := hb (x 4 3)
    have b11656 := hb (x 5 2)
    have b11657 := hb (x 6 13)
    have b11658 := hb (x 7 12)
    clear * - r11652 e11653 e11654 b11655 b11656 b11657 b11658 d11248 d11623
    omega
  have d11659 : (x 7 4).toNat = 0 := by
    have r11660 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
    have b11661 := hb (x 7 4)
    have b11662 := hb (x 7 12)
    clear * - r11660 b11661 b11662 d11651
    omega
  have d11663 : (x 6 13).toNat = 0 := by
    have r11664 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11665 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e11666 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b11667 := hb (x 4 3)
    have b11668 := hb (x 5 2)
    have b11669 := hb (x 6 13)
    have b11670 := hb (x 7 12)
    clear * - r11664 e11665 e11666 b11667 b11668 b11669 b11670 d11651 d11248 d11623
    omega
  have d11671 : (x 6 3 && x 6 13).toNat = 0 := by
    have r11672 := hand2 (x 6 3) (x 6 13)
    have b11673 := hb (x 6 13)
    have b11674 := hb (x 6 3 && x 6 13)
    clear * - r11672 b11673 b11674 d11663
    omega
  have d11675 : (x 6 5).toNat = 0 := by
    have r11676 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
    have b11677 := hb (x 6 5)
    have b11678 := hb (x 6 13)
    clear * - r11676 b11677 b11678 d11663
    omega
  have d11679 : (x 7 8).toNat = 0 := by
    have r11680 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11681 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e11682 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e11683 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e11684 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e11685 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e11686 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b11687 := hb (x 0 7)
    have b11688 := hb (x 1 6)
    have b11689 := hb (x 2 5)
    have b11690 := hb (x 3 4)
    have b11691 := hb (x 4 11)
    have b11692 := hb (x 5 10)
    have b11693 := hb (x 6 9)
    have b11694 := hb (x 7 8)
    clear * - r11680 e11681 e11682 e11683 e11684 e11685 e11686 b11687 b11688 b11689 b11690 b11691 b11692 b11693 b11694 d11264 d11616 d11528 d11548 d11288
    omega
  have d11695 : (x 6 9).toNat = 0 := by
    have r11696 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11697 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e11698 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e11699 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e11700 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e11701 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e11702 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b11703 := hb (x 0 7)
    have b11704 := hb (x 1 6)
    have b11705 := hb (x 2 5)
    have b11706 := hb (x 3 4)
    have b11707 := hb (x 4 11)
    have b11708 := hb (x 5 10)
    have b11709 := hb (x 6 9)
    have b11710 := hb (x 7 8)
    clear * - r11696 e11697 e11698 e11699 e11700 e11701 e11702 b11703 b11704 b11705 b11706 b11707 b11708 b11709 b11710 d11679 d11264 d11616 d11528 d11548 d11288
    omega
  have d11711 : (x 6 2 && x 6 9).toNat = 0 := by
    have r11712 := hand2 (x 6 2) (x 6 9)
    have b11713 := hb (x 6 9)
    have b11714 := hb (x 6 2 && x 6 9)
    clear * - r11712 b11713 b11714 d11695
    omega
  have d11715 : (x 3 8).toNat = 0 := by
    have r11716 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11717 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
    have e11718 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
    have e11719 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
    have e11720 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
    have e11721 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
    have e11722 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
    have b11723 := hb (x (-4) 7)
    have b11724 := hb (x (-3) 6)
    have b11725 := hb (x (-2) 5)
    have b11726 := hb (x (-1) 4)
    have b11727 := hb (x 0 11)
    have b11728 := hb (x 1 10)
    have b11729 := hb (x 2 9)
    have b11730 := hb (x 3 8)
    clear * - r11716 e11717 e11718 e11719 e11720 e11721 e11722 b11723 b11724 b11725 b11726 b11727 b11728 b11729 b11730 d11316 g0 d11392
    omega
  have d11731 : (x 2 9).toNat = 0 := by
    have r11732 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11733 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
    have e11734 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
    have e11735 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
    have e11736 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
    have e11737 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
    have e11738 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
    have b11739 := hb (x (-4) 7)
    have b11740 := hb (x (-3) 6)
    have b11741 := hb (x (-2) 5)
    have b11742 := hb (x (-1) 4)
    have b11743 := hb (x 0 11)
    have b11744 := hb (x 1 10)
    have b11745 := hb (x 2 9)
    have b11746 := hb (x 3 8)
    clear * - r11732 e11733 e11734 e11735 e11736 e11737 e11738 b11739 b11740 b11741 b11742 b11743 b11744 b11745 b11746 d11715 d11316 g0 d11392
    omega
  have d11747 : (x 2 2 && x 2 9).toNat = 0 := by
    have r11748 := hand2 (x 2 2) (x 2 9)
    have b11749 := hb (x 2 9)
    have b11750 := hb (x 2 2 && x 2 9)
    clear * - r11748 b11749 b11750 d11731
    omega
  have d11751 : (x (-1) 4).toNat = 0 := by
    have r11752 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11753 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
    have e11754 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
    have e11755 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
    have e11756 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
    have e11757 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
    have e11758 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
    have b11759 := hb (x (-4) 7)
    have b11760 := hb (x (-3) 6)
    have b11761 := hb (x (-2) 5)
    have b11762 := hb (x (-1) 4)
    have b11763 := hb (x 0 11)
    have b11764 := hb (x 1 10)
    have b11765 := hb (x 2 9)
    have b11766 := hb (x 3 8)
    clear * - r11752 e11753 e11754 e11755 e11756 e11757 e11758 b11759 b11760 b11761 b11762 b11763 b11764 b11765 b11766 d11715 d11731 d11316 g0 d11392
    omega
  have d11767 : (x (-2) 5).toNat = 0 := by
    have r11768 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11769 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
    have e11770 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
    have e11771 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
    have e11772 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
    have e11773 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
    have e11774 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
    have b11775 := hb (x (-4) 7)
    have b11776 := hb (x (-3) 6)
    have b11777 := hb (x (-2) 5)
    have b11778 := hb (x (-1) 4)
    have b11779 := hb (x 0 11)
    have b11780 := hb (x 1 10)
    have b11781 := hb (x 2 9)
    have b11782 := hb (x 3 8)
    clear * - r11768 e11769 e11770 e11771 e11772 e11773 e11774 b11775 b11776 b11777 b11778 b11779 b11780 b11781 b11782 d11715 d11731 d11316 g0 d11751 d11392
    omega
  have d11783 : (x (-2) 5 && x (-2) 14).toNat = 0 := by
    have r11784 := hand1 (x (-2) 5) (x (-2) 14)
    have b11785 := hb (x (-2) 5)
    have b11786 := hb (x (-2) 5 && x (-2) 14)
    clear * - r11784 b11785 b11786 d11767
    omega
  have d11787 : (x 2 1 && x 2 10).toNat = 1 := by
    have r11788 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11789 := hb (x (-3) 6)
    have b11790 := hb (x 3 9)
    have b11791 := hb (x 2 1 && x 2 10)
    have b11792 := hb (x 1 2 && x 1 11)
    have b11793 := hb (x 0 3 && x 0 12)
    have b11794 := hb (x (-1) 4 && x (-1) 13)
    have b11795 := hb (x (-2) 5 && x (-2) 14)
    clear * - r11788 b11789 b11790 b11791 b11792 b11793 b11794 b11795 d11084 d11300 d10984 d11352 d11783 d11392
    omega
  have d11796 : (x 2 10).toNat = 1 := by
    have r11797 := hand2 (x 2 1) (x 2 10)
    have b11798 := hb (x 2 10)
    have b11799 := hb (x 2 1 && x 2 10)
    clear * - r11797 b11798 b11799 d11787
    omega
  have d11800 : (x 2 2).toNat = 1 := by
    have r11801 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
    have b11802 := hb (x 2 2)
    have b11803 := hb (x 2 10)
    clear * - r11801 b11802 b11803 d11796
    omega
  have d11804 : (x 2 3).toNat = 1 := by
    have r11805 : (x 2 2).toNat = (x 2 3).toNat := congrArg Bool.toNat (h23 2)
    have b11806 := hb (x 2 2)
    have b11807 := hb (x 2 3)
    clear * - r11805 b11806 b11807 d11800
    omega
  have d11808 : (x 5 12).toNat = 0 := by
    have r11809 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11810 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e11811 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b11812 := hb (x 2 3)
    have b11813 := hb (x 3 2)
    have b11814 := hb (x 4 13)
    have b11815 := hb (x 5 12)
    clear * - r11809 e11810 e11811 b11812 b11813 b11814 b11815 d11272 d11804
    omega
  have d11816 : (x 5 4).toNat = 0 := by
    have r11817 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
    have b11818 := hb (x 5 4)
    have b11819 := hb (x 5 12)
    clear * - r11817 b11818 b11819 d11808
    omega
  have d11820 : (x 4 13).toNat = 0 := by
    have r11821 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11822 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e11823 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b11824 := hb (x 2 3)
    have b11825 := hb (x 3 2)
    have b11826 := hb (x 4 13)
    have b11827 := hb (x 5 12)
    clear * - r11821 e11822 e11823 b11824 b11825 b11826 b11827 d11808 d11272 d11804
    omega
  have d11828 : (x 4 2 && x 4 13).toNat = 0 := by
    have r11829 := hand2 (x 4 2) (x 4 13)
    have b11830 := hb (x 4 13)
    have b11831 := hb (x 4 2 && x 4 13)
    clear * - r11829 b11830 b11831 d11820
    omega
  have d11832 : (x 6 11).toNat = 1 := by
    have r11833 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := by have q := hcov11 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11834 := hb (x 2 4)
    have b11835 := hb (x 6 11)
    have b11836 := hb (x 5 1 && x 5 12)
    have b11837 := hb (x 4 2 && x 4 13)
    have b11838 := hb (x 3 3 && x 3 14)
    clear * - r11833 b11834 b11835 b11836 b11837 b11838 d11108 d11828 d11052 d11560
    omega
  have d11839 : (x 6 3).toNat = 1 := by
    have r11840 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
    have b11841 := hb (x 6 3)
    have b11842 := hb (x 6 11)
    clear * - r11840 b11841 b11842 d11832
    omega
  have d11843 : (x 6 2).toNat = 1 := by
    have r11844 : (x 6 2).toNat = (x 6 3).toNat := congrArg Bool.toNat (h23 6)
    have b11845 := hb (x 6 2)
    have b11846 := hb (x 6 3)
    clear * - r11844 b11845 b11846 d11839
    omega
  have d11847 : (x 8 12).toNat = 0 := by
    have r11848 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11849 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e11850 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b11851 := hb (x 5 3)
    have b11852 := hb (x 6 2)
    have b11853 := hb (x 7 13)
    have b11854 := hb (x 8 12)
    clear * - r11848 e11849 e11850 b11851 b11852 b11853 b11854 d11156 d11843 d11252
    omega
  have d11855 : (x 8 2 && x 8 12).toNat = 0 := by
    have r11856 := hand2 (x 8 2) (x 8 12)
    have b11857 := hb (x 8 12)
    have b11858 := hb (x 8 2 && x 8 12)
    clear * - r11856 b11857 b11858 d11847
    omega
  have d11859 : (x 10 10).toNat = 1 := by
    have r11860 : 1 ≤ (x 10 10).toNat + (x 9 1 && x 9 11).toNat + (x 8 2 && x 8 12).toNat + (x 7 3 && x 7 13).toNat + (x 6 4 && x 6 14).toNat + (x 5 5).toNat := by have q := hcov10 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11861 := hb (x 5 5)
    have b11862 := hb (x 10 10)
    have b11863 := hb (x 9 1 && x 9 11)
    have b11864 := hb (x 8 2 && x 8 12)
    have b11865 := hb (x 7 3 && x 7 13)
    have b11866 := hb (x 6 4 && x 6 14)
    clear * - r11860 b11861 b11862 b11863 b11864 b11865 b11866 d11196 d11855 d11160 d11647 d11128
    omega
  have d11867 : (x 12 8).toNat = 0 := by
    have r11868 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11869 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
    have e11870 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
    have e11871 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
    have e11872 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
    have e11873 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
    have e11874 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
    have b11875 := hb (x 5 7)
    have b11876 := hb (x 6 6)
    have b11877 := hb (x 7 5)
    have b11878 := hb (x 8 4)
    have b11879 := hb (x 9 11)
    have b11880 := hb (x 10 10)
    have b11881 := hb (x 11 9)
    have b11882 := hb (x 12 8)
    clear * - r11868 e11869 e11870 e11871 e11872 e11873 e11874 b11875 b11876 b11877 b11878 b11879 b11880 b11881 b11882 d11859 d11216 d11164
    omega
  have d11883 : (x 11 9).toNat = 0 := by
    have r11884 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11885 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
    have e11886 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
    have e11887 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
    have e11888 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
    have e11889 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
    have e11890 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
    have b11891 := hb (x 5 7)
    have b11892 := hb (x 6 6)
    have b11893 := hb (x 7 5)
    have b11894 := hb (x 8 4)
    have b11895 := hb (x 9 11)
    have b11896 := hb (x 10 10)
    have b11897 := hb (x 11 9)
    have b11898 := hb (x 12 8)
    clear * - r11884 e11885 e11886 e11887 e11888 e11889 e11890 b11891 b11892 b11893 b11894 b11895 b11896 b11897 b11898 d11867 d11859 d11216 d11164
    omega
  have d11899 : (x 8 4).toNat = 0 := by
    have r11900 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11901 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
    have e11902 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
    have e11903 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
    have e11904 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
    have e11905 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
    have e11906 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
    have b11907 := hb (x 5 7)
    have b11908 := hb (x 6 6)
    have b11909 := hb (x 7 5)
    have b11910 := hb (x 8 4)
    have b11911 := hb (x 9 11)
    have b11912 := hb (x 10 10)
    have b11913 := hb (x 11 9)
    have b11914 := hb (x 12 8)
    clear * - r11900 e11901 e11902 e11903 e11904 e11905 e11906 b11907 b11908 b11909 b11910 b11911 b11912 b11913 b11914 d11867 d11883 d11859 d11216 d11164
    omega
  have d11915 : (x 9 12).toNat = 0 := by
    have r11916 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11917 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e11918 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b11919 := hb (x 6 3)
    have b11920 := hb (x 7 2)
    have b11921 := hb (x 8 13)
    have b11922 := hb (x 9 12)
    clear * - r11916 e11917 e11918 b11919 b11920 b11921 b11922 d11228 d11839
    omega
  have d11923 : (x 9 4).toNat = 0 := by
    have r11924 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
    have b11925 := hb (x 9 4)
    have b11926 := hb (x 9 12)
    clear * - r11924 b11925 b11926 d11915
    omega
  have d11927 : (x 8 13).toNat = 0 := by
    have r11928 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11929 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e11930 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b11931 := hb (x 6 3)
    have b11932 := hb (x 7 2)
    have b11933 := hb (x 8 13)
    have b11934 := hb (x 9 12)
    clear * - r11928 e11929 e11930 b11931 b11932 b11933 b11934 d11915 d11228 d11839
    omega
  have d11935 : (x 8 2 && x 8 13).toNat = 0 := by
    have r11936 := hand2 (x 8 2) (x 8 13)
    have b11937 := hb (x 8 13)
    have b11938 := hb (x 8 2 && x 8 13)
    clear * - r11936 b11937 b11938 d11927
    omega
  have d11939 : (x 10 11).toNat = 1 := by
    have r11940 : 1 ≤ (x 10 11).toNat + (x 9 1 && x 9 12).toNat + (x 8 2 && x 8 13).toNat + (x 7 3 && x 7 14).toNat + (x 6 4).toNat := by have q := hcov11 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11941 := hb (x 6 4)
    have b11942 := hb (x 10 11)
    have b11943 := hb (x 9 1 && x 9 12)
    have b11944 := hb (x 8 2 && x 8 13)
    have b11945 := hb (x 7 3 && x 7 14)
    clear * - r11940 b11941 b11942 b11943 b11944 b11945 d11192 d11935 d11144 d11643
    omega
  have d11946 : (x 13 8).toNat = 0 := by
    have r11947 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11948 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
    have e11949 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
    have e11950 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
    have e11951 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
    have e11952 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
    have e11953 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
    have b11954 := hb (x 6 7)
    have b11955 := hb (x 7 6)
    have b11956 := hb (x 8 5)
    have b11957 := hb (x 9 4)
    have b11958 := hb (x 10 11)
    have b11959 := hb (x 11 10)
    have b11960 := hb (x 12 9)
    have b11961 := hb (x 13 8)
    clear * - r11947 e11948 e11949 e11950 e11951 e11952 e11953 b11954 b11955 b11956 b11957 b11958 b11959 b11960 b11961 d11939 d11923 d11224
    omega
  have d11962 : (x 12 9).toNat = 0 := by
    have r11963 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11964 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
    have e11965 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
    have e11966 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
    have e11967 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
    have e11968 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
    have e11969 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
    have b11970 := hb (x 6 7)
    have b11971 := hb (x 7 6)
    have b11972 := hb (x 8 5)
    have b11973 := hb (x 9 4)
    have b11974 := hb (x 10 11)
    have b11975 := hb (x 11 10)
    have b11976 := hb (x 12 9)
    have b11977 := hb (x 13 8)
    clear * - r11963 e11964 e11965 e11966 e11967 e11968 e11969 b11970 b11971 b11972 b11973 b11974 b11975 b11976 b11977 d11946 d11939 d11923 d11224
    omega
  have d11978 : (x 11 10).toNat = 0 := by
    have r11979 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11980 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
    have e11981 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
    have e11982 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
    have e11983 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
    have e11984 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
    have e11985 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
    have b11986 := hb (x 6 7)
    have b11987 := hb (x 7 6)
    have b11988 := hb (x 8 5)
    have b11989 := hb (x 9 4)
    have b11990 := hb (x 10 11)
    have b11991 := hb (x 11 10)
    have b11992 := hb (x 12 9)
    have b11993 := hb (x 13 8)
    clear * - r11979 e11980 e11981 e11982 e11983 e11984 e11985 b11986 b11987 b11988 b11989 b11990 b11991 b11992 b11993 d11946 d11962 d11939 d11923 d11224
    omega
  have d11994 : (x 8 5).toNat = 0 := by
    have r11995 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11996 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
    have e11997 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
    have e11998 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
    have e11999 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
    have e12000 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
    have e12001 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
    have b12002 := hb (x 6 7)
    have b12003 := hb (x 7 6)
    have b12004 := hb (x 8 5)
    have b12005 := hb (x 9 4)
    have b12006 := hb (x 10 11)
    have b12007 := hb (x 11 10)
    have b12008 := hb (x 12 9)
    have b12009 := hb (x 13 8)
    clear * - r11995 e11996 e11997 e11998 e11999 e12000 e12001 b12002 b12003 b12004 b12005 b12006 b12007 b12008 b12009 d11946 d11962 d11978 d11939 d11923 d11224
    omega
  have d12010 : (x 6 7).toNat = 0 := by
    have r12011 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12012 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
    have e12013 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
    have e12014 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
    have e12015 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
    have e12016 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
    have e12017 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
    have b12018 := hb (x 6 7)
    have b12019 := hb (x 7 6)
    have b12020 := hb (x 8 5)
    have b12021 := hb (x 9 4)
    have b12022 := hb (x 10 11)
    have b12023 := hb (x 11 10)
    have b12024 := hb (x 12 9)
    have b12025 := hb (x 13 8)
    clear * - r12011 e12012 e12013 e12014 e12015 e12016 e12017 b12018 b12019 b12020 b12021 b12022 b12023 b12024 b12025 d11946 d11962 d11978 d11939 d11923 d11994 d11224
    omega
  have d12026 : (x 9 8).toNat = 0 := by
    have r12027 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12028 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
    have e12029 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
    have e12030 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
    have e12031 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
    have e12032 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
    have e12033 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
    have b12034 := hb (x 2 7)
    have b12035 := hb (x 3 6)
    have b12036 := hb (x 4 5)
    have b12037 := hb (x 5 4)
    have b12038 := hb (x 6 11)
    have b12039 := hb (x 7 10)
    have b12040 := hb (x 8 9)
    have b12041 := hb (x 9 8)
    clear * - r12027 e12028 e12029 e12030 e12031 e12032 e12033 b12034 b12035 b12036 b12037 b12038 b12039 b12040 b12041 d11240 d11832 d11816 d11268
    omega
  have d12042 : (x 8 9).toNat = 0 := by
    have r12043 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12044 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
    have e12045 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
    have e12046 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
    have e12047 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
    have e12048 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
    have e12049 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
    have b12050 := hb (x 2 7)
    have b12051 := hb (x 3 6)
    have b12052 := hb (x 4 5)
    have b12053 := hb (x 5 4)
    have b12054 := hb (x 6 11)
    have b12055 := hb (x 7 10)
    have b12056 := hb (x 8 9)
    have b12057 := hb (x 9 8)
    clear * - r12043 e12044 e12045 e12046 e12047 e12048 e12049 b12050 b12051 b12052 b12053 b12054 b12055 b12056 b12057 d12026 d11240 d11832 d11816 d11268
    omega
  have d12058 : (x 4 5).toNat = 0 := by
    have r12059 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12060 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
    have e12061 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
    have e12062 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
    have e12063 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
    have e12064 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
    have e12065 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
    have b12066 := hb (x 2 7)
    have b12067 := hb (x 3 6)
    have b12068 := hb (x 4 5)
    have b12069 := hb (x 5 4)
    have b12070 := hb (x 6 11)
    have b12071 := hb (x 7 10)
    have b12072 := hb (x 8 9)
    have b12073 := hb (x 9 8)
    clear * - r12059 e12060 e12061 e12062 e12063 e12064 e12065 b12066 b12067 b12068 b12069 b12070 b12071 b12072 b12073 d12026 d12042 d11240 d11832 d11816 d11268
    omega
  have d12074 : (x 4 5 && x 4 14).toNat = 0 := by
    have r12075 := hand1 (x 4 5) (x 4 14)
    have b12076 := hb (x 4 5)
    have b12077 := hb (x 4 5 && x 4 14)
    clear * - r12075 b12076 b12077 d12058
    omega
  have d12078 : (x 8 1 && x 8 10).toNat = 1 := by
    have r12079 : 1 ≤ (x 9 9).toNat + (x 8 1 && x 8 10).toNat + (x 7 2 && x 7 11).toNat + (x 6 3 && x 6 12).toNat + (x 5 4 && x 5 13).toNat + (x 4 5 && x 4 14).toNat + (x 3 6).toNat := by have q := hcov9 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12080 := hb (x 3 6)
    have b12081 := hb (x 9 9)
    have b12082 := hb (x 8 1 && x 8 10)
    have b12083 := hb (x 7 2 && x 7 11)
    have b12084 := hb (x 6 3 && x 6 12)
    have b12085 := hb (x 5 4 && x 5 13)
    have b12086 := hb (x 4 5 && x 4 14)
    clear * - r12079 b12080 b12081 b12082 b12083 b12084 b12085 b12086 d11200 d11236 d11639 d11124 d12074 d11268
    omega
  have d12087 : (x 8 10).toNat = 1 := by
    have r12088 := hand2 (x 8 1) (x 8 10)
    have b12089 := hb (x 8 10)
    have b12090 := hb (x 8 1 && x 8 10)
    clear * - r12088 b12089 b12090 d12078
    omega
  have d12091 : (x 8 2).toNat = 1 := by
    have r12092 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
    have b12093 := hb (x 8 2)
    have b12094 := hb (x 8 10)
    clear * - r12092 b12093 b12094 d12087
    omega
  have d12095 : (x 8 3).toNat = 1 := by
    have r12096 : (x 8 2).toNat = (x 8 3).toNat := congrArg Bool.toNat (h23 8)
    have b12097 := hb (x 8 2)
    have b12098 := hb (x 8 3)
    clear * - r12096 b12097 b12098 d12091
    omega
  have d12099 : (x 11 12).toNat = 0 := by
    have r12100 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12101 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e12102 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b12103 := hb (x 8 3)
    have b12104 := hb (x 9 2)
    have b12105 := hb (x 10 13)
    have b12106 := hb (x 11 12)
    clear * - r12100 e12101 e12102 b12103 b12104 b12105 b12106 d11208 d12095
    omega
  have d12107 : (x 11 1 && x 11 12).toNat = 0 := by
    have r12108 := hand2 (x 11 1) (x 11 12)
    have b12109 := hb (x 11 12)
    have b12110 := hb (x 11 1 && x 11 12)
    clear * - r12108 b12109 b12110 d12099
    omega
  have d12111 : (x 11 4).toNat = 0 := by
    have r12112 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
    have b12113 := hb (x 11 4)
    have b12114 := hb (x 11 12)
    clear * - r12112 b12113 b12114 d12099
    omega
  have d12115 : (x 10 13).toNat = 0 := by
    have r12116 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12117 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e12118 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b12119 := hb (x 8 3)
    have b12120 := hb (x 9 2)
    have b12121 := hb (x 10 13)
    have b12122 := hb (x 11 12)
    clear * - r12116 e12117 e12118 b12119 b12120 b12121 b12122 d12099 d11208 d12095
    omega
  have d12123 : (x 10 2 && x 10 13).toNat = 0 := by
    have r12124 := hand2 (x 10 2) (x 10 13)
    have b12125 := hb (x 10 13)
    have b12126 := hb (x 10 2 && x 10 13)
    clear * - r12124 b12125 b12126 d12115
    omega
  have d12127 : (x 12 11).toNat = 1 := by
    have r12128 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12129 := hb (x 8 4)
    have b12130 := hb (x 12 11)
    have b12131 := hb (x 11 1 && x 11 12)
    have b12132 := hb (x 10 2 && x 10 13)
    have b12133 := hb (x 9 3 && x 9 14)
    clear * - r12128 b12129 b12130 b12131 b12132 b12133 d12107 d12123 d11184 d11899
    omega
  have d12134 : (x 15 8).toNat = 0 := by
    have r12135 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12136 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
    have e12137 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
    have e12138 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
    have e12139 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
    have e12140 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
    have e12141 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
    have b12142 := hb (x 8 7)
    have b12143 := hb (x 9 6)
    have b12144 := hb (x 10 5)
    have b12145 := hb (x 11 4)
    have b12146 := hb (x 12 11)
    have b12147 := hb (x 13 10)
    have b12148 := hb (x 14 9)
    have b12149 := hb (x 15 8)
    clear * - r12135 e12136 e12137 e12138 e12139 e12140 e12141 b12142 b12143 b12144 b12145 b12146 b12147 b12148 b12149 d12127 d12111 d11204
    omega
  have d12150 : (x 14 9).toNat = 0 := by
    have r12151 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12152 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
    have e12153 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
    have e12154 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
    have e12155 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
    have e12156 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
    have e12157 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
    have b12158 := hb (x 8 7)
    have b12159 := hb (x 9 6)
    have b12160 := hb (x 10 5)
    have b12161 := hb (x 11 4)
    have b12162 := hb (x 12 11)
    have b12163 := hb (x 13 10)
    have b12164 := hb (x 14 9)
    have b12165 := hb (x 15 8)
    clear * - r12151 e12152 e12153 e12154 e12155 e12156 e12157 b12158 b12159 b12160 b12161 b12162 b12163 b12164 b12165 d12134 d12127 d12111 d11204
    omega
  have d12166 : (x 13 10).toNat = 0 := by
    have r12167 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12168 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
    have e12169 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
    have e12170 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
    have e12171 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
    have e12172 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
    have e12173 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
    have b12174 := hb (x 8 7)
    have b12175 := hb (x 9 6)
    have b12176 := hb (x 10 5)
    have b12177 := hb (x 11 4)
    have b12178 := hb (x 12 11)
    have b12179 := hb (x 13 10)
    have b12180 := hb (x 14 9)
    have b12181 := hb (x 15 8)
    clear * - r12167 e12168 e12169 e12170 e12171 e12172 e12173 b12174 b12175 b12176 b12177 b12178 b12179 b12180 b12181 d12134 d12150 d12127 d12111 d11204
    omega
  have d12182 : (x 10 5).toNat = 0 := by
    have r12183 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12184 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
    have e12185 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
    have e12186 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
    have e12187 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
    have e12188 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
    have e12189 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
    have b12190 := hb (x 8 7)
    have b12191 := hb (x 9 6)
    have b12192 := hb (x 10 5)
    have b12193 := hb (x 11 4)
    have b12194 := hb (x 12 11)
    have b12195 := hb (x 13 10)
    have b12196 := hb (x 14 9)
    have b12197 := hb (x 15 8)
    clear * - r12183 e12184 e12185 e12186 e12187 e12188 e12189 b12190 b12191 b12192 b12193 b12194 b12195 b12196 b12197 d12134 d12150 d12166 d12127 d12111 d11204
    omega
  have d12198 : (x 8 7).toNat = 0 := by
    have r12199 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12200 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
    have e12201 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
    have e12202 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
    have e12203 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
    have e12204 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
    have e12205 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
    have b12206 := hb (x 8 7)
    have b12207 := hb (x 9 6)
    have b12208 := hb (x 10 5)
    have b12209 := hb (x 11 4)
    have b12210 := hb (x 12 11)
    have b12211 := hb (x 13 10)
    have b12212 := hb (x 14 9)
    have b12213 := hb (x 15 8)
    clear * - r12199 e12200 e12201 e12202 e12203 e12204 e12205 b12206 b12207 b12208 b12209 b12210 b12211 b12212 b12213 d12134 d12150 d12166 d12127 d12111 d12182 d11204
    omega
  have d12214 : (x 8 1 && x 8 11).toNat = 1 := by
    have r12215 : 1 ≤ (x 9 10).toNat + (x 8 1 && x 8 11).toNat + (x 7 2 && x 7 12).toNat + (x 6 3 && x 6 13).toNat + (x 5 4 && x 5 14).toNat + (x 4 5).toNat := by have q := hcov10 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12216 := hb (x 4 5)
    have b12217 := hb (x 9 10)
    have b12218 := hb (x 8 1 && x 8 11)
    have b12219 := hb (x 7 2 && x 7 12)
    have b12220 := hb (x 6 3 && x 6 13)
    have b12221 := hb (x 5 4 && x 5 14)
    clear * - r12215 b12216 b12217 b12218 b12219 b12220 b12221 d11220 d11232 d11671 d11100 d12058
    omega
  have d12222 : (x 8 11).toNat = 1 := by
    have r12223 := hand2 (x 8 1) (x 8 11)
    have b12224 := hb (x 8 11)
    have b12225 := hb (x 8 1 && x 8 11)
    clear * - r12223 b12224 b12225 d12214
    omega
  have d12226 : (x 11 8).toNat = 0 := by
    have r12227 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12228 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e12229 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e12230 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e12231 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e12232 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e12233 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have b12234 := hb (x 4 7)
    have b12235 := hb (x 5 6)
    have b12236 := hb (x 6 5)
    have b12237 := hb (x 7 4)
    have b12238 := hb (x 8 11)
    have b12239 := hb (x 9 10)
    have b12240 := hb (x 10 9)
    have b12241 := hb (x 11 8)
    clear * - r12227 e12228 e12229 e12230 e12231 e12232 e12233 b12234 b12235 b12236 b12237 b12238 b12239 b12240 b12241 d11220 d12222 d11659 d11675 d11244
    omega
  have d12242 : (x 10 9).toNat = 0 := by
    have r12243 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12244 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e12245 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e12246 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e12247 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e12248 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e12249 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have b12250 := hb (x 4 7)
    have b12251 := hb (x 5 6)
    have b12252 := hb (x 6 5)
    have b12253 := hb (x 7 4)
    have b12254 := hb (x 8 11)
    have b12255 := hb (x 9 10)
    have b12256 := hb (x 10 9)
    have b12257 := hb (x 11 8)
    clear * - r12243 e12244 e12245 e12246 e12247 e12248 e12249 b12250 b12251 b12252 b12253 b12254 b12255 b12256 b12257 d12226 d11220 d12222 d11659 d11675 d11244
    omega
  have d12258 : (x 4 7).toNat = 0 := by
    have r12259 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12260 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e12261 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e12262 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e12263 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e12264 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e12265 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have b12266 := hb (x 4 7)
    have b12267 := hb (x 5 6)
    have b12268 := hb (x 6 5)
    have b12269 := hb (x 7 4)
    have b12270 := hb (x 8 11)
    have b12271 := hb (x 9 10)
    have b12272 := hb (x 10 9)
    have b12273 := hb (x 11 8)
    clear * - r12259 e12260 e12261 e12262 e12263 e12264 e12265 b12266 b12267 b12268 b12269 b12270 b12271 b12272 b12273 d12226 d12242 d11220 d12222 d11659 d11675 d11244
    omega
  have d12274 : (x 4 12).toNat = 0 := by
    have r12275 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12276 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e12277 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b12278 := hb (x 1 3)
    have b12279 := hb (x 2 2)
    have b12280 := hb (x 3 13)
    have b12281 := hb (x 4 12)
    clear * - r12275 e12276 e12277 b12278 b12279 b12280 b12281 d11068 d11800 d11304
    omega
  have d12282 : (x 4 2 && x 4 12).toNat = 0 := by
    have r12283 := hand2 (x 4 2) (x 4 12)
    have b12284 := hb (x 4 12)
    have b12285 := hb (x 4 2 && x 4 12)
    clear * - r12283 b12284 b12285 d12274
    omega
  have d12286 : (x 6 10).toNat = 1 := by
    have r12287 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12288 := hb (x 1 5)
    have b12289 := hb (x 6 10)
    have b12290 := hb (x 5 1 && x 5 11)
    have b12291 := hb (x 4 2 && x 4 12)
    have b12292 := hb (x 3 3 && x 3 13)
    have b12293 := hb (x 2 4 && x 2 14)
    clear * - r12287 b12288 b12289 b12290 b12291 b12292 b12293 d11112 d12282 d11072 d11564 d11032
    omega
  have d12294 : (x 8 8).toNat = 0 := by
    have r12295 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12296 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e12297 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e12298 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e12299 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e12300 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e12301 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have b12302 := hb (x 1 7)
    have b12303 := hb (x 2 6)
    have b12304 := hb (x 3 5)
    have b12305 := hb (x 4 4)
    have b12306 := hb (x 5 11)
    have b12307 := hb (x 6 10)
    have b12308 := hb (x 7 9)
    have b12309 := hb (x 8 8)
    clear * - r12295 e12296 e12297 e12298 e12299 e12300 e12301 b12302 b12303 b12304 b12305 b12306 b12307 b12308 b12309 d11168 d12286 d11260 d11076
    omega
  have d12310 : (x 4 4).toNat = 0 := by
    have r12311 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12312 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e12313 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e12314 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e12315 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e12316 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e12317 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have b12318 := hb (x 1 7)
    have b12319 := hb (x 2 6)
    have b12320 := hb (x 3 5)
    have b12321 := hb (x 4 4)
    have b12322 := hb (x 5 11)
    have b12323 := hb (x 6 10)
    have b12324 := hb (x 7 9)
    have b12325 := hb (x 8 8)
    clear * - r12311 e12312 e12313 e12314 e12315 e12316 e12317 b12318 b12319 b12320 b12321 b12322 b12323 b12324 b12325 d12294 d11168 d12286 d11260 d11076
    omega
  have d12326 : (x 4 4 && x 4 11).toNat = 0 := by
    have r12327 := hand1 (x 4 4) (x 4 11)
    have b12328 := hb (x 4 4)
    have b12329 := hb (x 4 4 && x 4 11)
    clear * - r12327 b12328 b12329 d12310
    omega
  have d12330 : (x 4 8).toNat = 0 := by
    have r12331 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12332 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e12333 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e12334 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e12335 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e12336 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e12337 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b12338 := hb (x (-3) 7)
    have b12339 := hb (x (-2) 6)
    have b12340 := hb (x (-1) 5)
    have b12341 := hb (x 0 4)
    have b12342 := hb (x 1 11)
    have b12343 := hb (x 2 10)
    have b12344 := hb (x 3 9)
    have b12345 := hb (x 4 8)
    clear * - r12331 e12332 e12333 e12334 e12335 e12336 e12337 b12338 b12339 b12340 b12341 b12342 b12343 b12344 b12345 d11084 d11796 d11312 d10996 d11356
    omega
  have d12346 : (x (-2) 6).toNat = 0 := by
    have r12347 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12348 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e12349 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e12350 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e12351 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e12352 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e12353 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b12354 := hb (x (-3) 7)
    have b12355 := hb (x (-2) 6)
    have b12356 := hb (x (-1) 5)
    have b12357 := hb (x 0 4)
    have b12358 := hb (x 1 11)
    have b12359 := hb (x 2 10)
    have b12360 := hb (x 3 9)
    have b12361 := hb (x 4 8)
    clear * - r12347 e12348 e12349 e12350 e12351 e12352 e12353 b12354 b12355 b12356 b12357 b12358 b12359 b12360 b12361 d12330 d11084 d11796 d11312 d10996 d11356
    omega
  have d12362 : (x (-2) 6 && x (-2) 13).toNat = 0 := by
    have r12363 := hand1 (x (-2) 6) (x (-2) 13)
    have b12364 := hb (x (-2) 6)
    have b12365 := hb (x (-2) 6 && x (-2) 13)
    clear * - r12363 b12364 b12365 d12346
    omega
  have d12366 : (x 2 1 && x 2 11).toNat = 1 := by
    have r12367 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12368 := hb (x (-2) 5)
    have b12369 := hb (x 3 10)
    have b12370 := hb (x 2 1 && x 2 11)
    have b12371 := hb (x 1 2 && x 1 12)
    have b12372 := hb (x 0 3 && x 0 13)
    have b12373 := hb (x (-1) 4 && x (-1) 14)
    clear * - r12367 b12368 b12369 b12370 b12371 b12372 b12373 d11284 d11296 d11604 d11328 d11767
    omega
  have d12374 : (x 2 11).toNat = 1 := by
    have r12375 := hand2 (x 2 1) (x 2 11)
    have b12376 := hb (x 2 11)
    have b12377 := hb (x 2 1 && x 2 11)
    clear * - r12375 b12376 b12377 d12366
    omega
  have d12378 : (x 5 8).toNat = 0 := by
    have r12379 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12380 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e12381 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e12382 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e12383 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e12384 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e12385 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b12386 := hb (x (-2) 7)
    have b12387 := hb (x (-1) 6)
    have b12388 := hb (x 0 5)
    have b12389 := hb (x 1 4)
    have b12390 := hb (x 2 11)
    have b12391 := hb (x 3 10)
    have b12392 := hb (x 4 9)
    have b12393 := hb (x 5 8)
    clear * - r12379 e12380 e12381 e12382 e12383 e12384 e12385 b12386 b12387 b12388 b12389 b12390 b12391 b12392 b12393 d11284 d12374 d11592 d11612 d11336
    omega
  have d12394 : (x 4 9).toNat = 0 := by
    have r12395 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12396 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e12397 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e12398 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e12399 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e12400 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e12401 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b12402 := hb (x (-2) 7)
    have b12403 := hb (x (-1) 6)
    have b12404 := hb (x 0 5)
    have b12405 := hb (x 1 4)
    have b12406 := hb (x 2 11)
    have b12407 := hb (x 3 10)
    have b12408 := hb (x 4 9)
    have b12409 := hb (x 5 8)
    clear * - r12395 e12396 e12397 e12398 e12399 e12400 e12401 b12402 b12403 b12404 b12405 b12406 b12407 b12408 b12409 d12378 d11284 d12374 d11592 d11612 d11336
    omega
  have d12410 : (x 4 2 && x 4 9).toNat = 0 := by
    have r12411 := hand2 (x 4 2) (x 4 9)
    have b12412 := hb (x 4 9)
    have b12413 := hb (x 4 2 && x 4 9)
    clear * - r12411 b12412 b12413 d12394
    omega
  have d12414 : (x 0 8).toNat = 1 := by
    have r12415 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := by have q := hcov7 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12416 := hb (x 0 8)
    have b12417 := hb (x 8 7)
    have b12418 := hb (x 7 1 && x 7 8)
    have b12419 := hb (x 6 2 && x 6 9)
    have b12420 := hb (x 5 3 && x 5 10)
    have b12421 := hb (x 4 4 && x 4 11)
    have b12422 := hb (x 3 5 && x 3 12)
    have b12423 := hb (x 2 6 && x 2 13)
    have b12424 := hb (x 1 7 && x 1 14)
    clear * - r12415 b12416 b12417 b12418 b12419 b12420 b12421 b12422 b12423 b12424 d12198 d11152 d11711 d11256 d12326 d11080 d11544 d11020
    omega
  have d12425 : (x (-2) 10).toNat = 0 := by
    have r12426 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12427 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e12428 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e12429 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e12430 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e12431 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e12432 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b12433 := hb (x (-7) 7)
    have b12434 := hb (x (-6) 6)
    have b12435 := hb (x (-5) 5)
    have b12436 := hb (x (-4) 4)
    have b12437 := hb (x (-3) 11)
    have b12438 := hb (x (-2) 10)
    have b12439 := hb (x (-1) 9)
    have b12440 := hb (x 0 8)
    clear * - r12426 e12427 e12428 e12429 e12430 e12431 e12432 b12433 b12434 b12435 b12436 b12437 b12438 b12439 b12440 d12414 d11364 d11404 d11452
    omega
  have d12441 : (x (-2) 8).toNat = 1 := by
    have r12442 : 1 ≤ (x 6 7).toNat + (x 5 1 && x 5 8).toNat + (x 4 2 && x 4 9).toNat + (x 3 3 && x 3 10).toNat + (x 2 4 && x 2 11).toNat + (x 1 5 && x 1 12).toNat + (x 0 6 && x 0 13).toNat + (x (-1) 7 && x (-1) 14).toNat + (x (-2) 8).toNat := by have q := hcov7 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12443 := hb (x (-2) 8)
    have b12444 := hb (x 6 7)
    have b12445 := hb (x 5 1 && x 5 8)
    have b12446 := hb (x 4 2 && x 4 9)
    have b12447 := hb (x 3 3 && x 3 10)
    have b12448 := hb (x 2 4 && x 2 11)
    have b12449 := hb (x 1 5 && x 1 12)
    have b12450 := hb (x 0 6 && x 0 13)
    have b12451 := hb (x (-1) 7 && x (-1) 14)
    clear * - r12442 b12443 b12444 b12445 b12446 b12447 b12448 b12449 b12450 b12451 d12010 d11116 d12410 d11280 d11568 d11036 d11608 d11332
    omega
  have d12452 : (x (-4) 10).toNat = 0 := by
    have r12453 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12454 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
    have e12455 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
    have e12456 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
    have e12457 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
    have e12458 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
    have e12459 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
    have b12460 := hb (x (-9) 7)
    have b12461 := hb (x (-8) 6)
    have b12462 := hb (x (-7) 5)
    have b12463 := hb (x (-6) 4)
    have b12464 := hb (x (-5) 11)
    have b12465 := hb (x (-4) 10)
    have b12466 := hb (x (-3) 9)
    have b12467 := hb (x (-2) 8)
    clear * - r12453 e12454 e12455 e12456 e12457 e12458 e12459 b12460 b12461 b12462 b12463 b12464 b12465 b12466 b12467 d12441 d11408 d11444 d11496
    omega
  have d12468 : (x (-6) 4).toNat = 0 := by
    have r12469 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12470 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
    have e12471 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
    have e12472 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
    have e12473 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
    have e12474 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
    have e12475 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
    have b12476 := hb (x (-9) 7)
    have b12477 := hb (x (-8) 6)
    have b12478 := hb (x (-7) 5)
    have b12479 := hb (x (-6) 4)
    have b12480 := hb (x (-5) 11)
    have b12481 := hb (x (-4) 10)
    have b12482 := hb (x (-3) 9)
    have b12483 := hb (x (-2) 8)
    clear * - r12469 e12470 e12471 e12472 e12473 e12474 e12475 b12476 b12477 b12478 b12479 b12480 b12481 b12482 b12483 d12441 d11408 d12452 d11444 d11496
    omega
  have d12484 : (x (-6) 4 && x (-6) 14).toNat = 0 := by
    have r12485 := hand1 (x (-6) 4) (x (-6) 14)
    have b12486 := hb (x (-6) 4)
    have b12487 := hb (x (-6) 4 && x (-6) 14)
    clear * - r12485 b12486 b12487 d12468
    omega
  have d12488 : (x (-4) 2 && x (-4) 12).toNat = 1 := by
    have r12489 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12490 := hb (x (-7) 5)
    have b12491 := hb (x (-2) 10)
    have b12492 := hb (x (-3) 1 && x (-3) 11)
    have b12493 := hb (x (-4) 2 && x (-4) 12)
    have b12494 := hb (x (-5) 3 && x (-5) 13)
    have b12495 := hb (x (-6) 4 && x (-6) 14)
    clear * - r12489 b12490 b12491 b12492 b12493 b12494 b12495 d12425 d11380 d11440 d12484 d11496
    omega
  have d12496 : (x (-4) 12).toNat = 1 := by
    have r12497 := hand2 (x (-4) 2) (x (-4) 12)
    have b12498 := hb (x (-4) 12)
    have b12499 := hb (x (-4) 2 && x (-4) 12)
    clear * - r12497 b12498 b12499 d12488
    omega
  have d12500 : (x (-6) 2).toNat = 0 := by
    have r12501 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12502 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e12503 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b12504 := hb (x (-7) 3)
    have b12505 := hb (x (-6) 2)
    have b12506 := hb (x (-5) 13)
    have b12507 := hb (x (-4) 12)
    clear * - r12501 e12502 e12503 b12504 b12505 b12506 b12507 d12496 d11448 d11480
    omega
  have d12508 : (x (-6) 2 && x (-6) 12).toNat = 0 := by
    have r12509 := hand1 (x (-6) 2) (x (-6) 12)
    have b12510 := hb (x (-6) 2)
    have b12511 := hb (x (-6) 2 && x (-6) 12)
    clear * - r12509 b12510 b12511 d12500
    omega
  have d12512 : (x (-8) 4 && x (-8) 14).toNat = 1 := by
    have r12513 : 1 ≤ (x (-4) 10).toNat + (x (-5) 1 && x (-5) 11).toNat + (x (-6) 2 && x (-6) 12).toNat + (x (-7) 3 && x (-7) 13).toNat + (x (-8) 4 && x (-8) 14).toNat + (x (-9) 5).toNat := by have q := hcov10 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12514 := hb (x (-9) 5)
    have b12515 := hb (x (-4) 10)
    have b12516 := hb (x (-5) 1 && x (-5) 11)
    have b12517 := hb (x (-6) 2 && x (-6) 12)
    have b12518 := hb (x (-7) 3 && x (-7) 13)
    have b12519 := hb (x (-8) 4 && x (-8) 14)
    clear * - r12513 b12514 b12515 b12516 b12517 b12518 b12519 d12452 d11424 d12508 d11484 d11516
    omega
  have d12520 : (x (-8) 4).toNat = 1 := by
    have r12521 := hand1 (x (-8) 4) (x (-8) 14)
    have b12522 := hb (x (-8) 4)
    have b12523 := hb (x (-8) 4 && x (-8) 14)
    clear * - r12521 b12522 b12523 d12512
    omega
  have d12524 : (x (-4) 8).toNat = 0 := by
    have r12525 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12526 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
    have e12527 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
    have e12528 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
    have e12529 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
    have e12530 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
    have e12531 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
    have b12532 := hb (x (-11) 7)
    have b12533 := hb (x (-10) 6)
    have b12534 := hb (x (-9) 5)
    have b12535 := hb (x (-8) 4)
    have b12536 := hb (x (-7) 11)
    have b12537 := hb (x (-6) 10)
    have b12538 := hb (x (-5) 9)
    have b12539 := hb (x (-4) 8)
    clear * - r12525 e12526 e12527 e12528 e12529 e12530 e12531 b12532 b12533 b12534 b12535 b12536 b12537 b12538 b12539 d11456 d11488 d12520 d11516
    omega
  have r12540 : 1 ≤ (x 4 7).toNat + (x 3 1 && x 3 8).toNat + (x 2 2 && x 2 9).toNat + (x 1 3 && x 1 10).toNat + (x 0 4 && x 0 11).toNat + (x (-1) 5 && x (-1) 12).toNat + (x (-2) 6 && x (-2) 13).toNat + (x (-3) 7 && x (-3) 14).toNat + (x (-4) 8).toNat := by have q := hcov7 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have b12541 := hb (x (-4) 8)
  have b12542 := hb (x 4 7)
  have b12543 := hb (x 3 1 && x 3 8)
  have b12544 := hb (x 2 2 && x 2 9)
  have b12545 := hb (x 1 3 && x 1 10)
  have b12546 := hb (x 0 4 && x 0 11)
  have b12547 := hb (x (-1) 5 && x (-1) 12)
  have b12548 := hb (x (-2) 6 && x (-2) 13)
  have b12549 := hb (x (-3) 7 && x (-3) 14)
  linarith only [r12540, b12541, b12542, b12543, b12544, b12545, b12546, b12547, b12548, b12549, d12258, d11064, d11747, d11308, d11000, d11360, d12362, d11388, d12524]

theorem cycle_power_fifteen_tight_type_sequence_shape_rules_core_v111_120 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 11).toNat = 1) (g1 : (x 0 12).toNat = 0) : False := cycle_power_fifteen_tight_type_sequence_shape_rules_core_v111_120_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 h114 h23 g0 g1
