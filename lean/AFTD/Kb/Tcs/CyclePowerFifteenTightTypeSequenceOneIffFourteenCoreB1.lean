import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b1

Topic: combinatorics   Node: d6ee6db13271

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core: under the layer-free tight-cover constraints for k = 15 and 9 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b1_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 13).toNat = 0)
    (g1 : (x (-1) 13).toNat = 0)
    (g2 : (x 0 2).toNat = 1)
    (g3 : (x 0 13).toNat = 0)
    (g4 : (x 0 1 && x 0 12).toNat = 0)
    (g5 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g6 : (x 0 2 && x 0 13).toNat = 0)
    (g7 : (x (-3) 1 && x (-3) 14).toNat = 0)
    (g8 : (x 0 1 && x 0 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d19014 : (x 2 12).toNat = 0 := by
    have r19015 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := hd12 2
    have e19016 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e19017 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b19018 := hb (x (-1) 3)
    have b19019 := hb (x 0 2)
    have b19020 := hb (x 1 13)
    have b19021 := hb (x 2 12)
    clear * - r19015 e19016 e19017 b19018 b19019 b19020 b19021 g2
    omega
  have d19022 : (x 2 1 && x 2 12).toNat = 0 := by
    have r19023 := hand2 (x 2 1) (x 2 12)
    have b19024 := hb (x 2 12)
    have b19025 := hb (x 2 1 && x 2 12)
    clear * - r19023 b19024 b19025 d19014
    omega
  have d19026 : (x 1 13).toNat = 0 := by
    have r19027 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := hd12 2
    have e19028 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e19029 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b19030 := hb (x (-1) 3)
    have b19031 := hb (x 0 2)
    have b19032 := hb (x 1 13)
    have b19033 := hb (x 2 12)
    clear * - r19027 e19028 e19029 b19030 b19031 b19032 b19033 d19014 g2
    omega
  have d19034 : (x 1 2 && x 1 13).toNat = 0 := by
    have r19035 := hand2 (x 1 2) (x 1 13)
    have b19036 := hb (x 1 13)
    have b19037 := hb (x 1 2 && x 1 13)
    clear * - r19035 b19036 b19037 d19026
    omega
  have d19038 : (x (-1) 2).toNat = 1 := by
    have r19039 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := hcov13 1
    have b19040 := hb (x (-1) 2)
    have b19041 := hb (x 1 13)
    have b19042 := hb (x 0 1 && x 0 14)
    clear * - r19039 b19040 b19041 b19042 d19026 g8
    omega
  have d19043 : (x (-1) 14).toNat = 1 := by
    have r19044 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
    have b19045 := hb (x (-1) 2)
    have b19046 := hb (x (-1) 14)
    clear * - r19044 b19045 b19046 d19038
    omega
  have d19047 : (x (-2) 1).toNat = 0 := by
    have r19048 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := hd14 (-1)
    have b19049 := hb (x (-2) 1)
    have b19050 := hb (x (-1) 14)
    clear * - r19048 b19049 b19050 d19043
    omega
  have d19051 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
    have r19052 := hand1 (x (-2) 1) (x (-2) 14)
    have b19053 := hb (x (-2) 1)
    have b19054 := hb (x (-2) 1 && x (-2) 14)
    clear * - r19052 b19053 b19054 d19047
    omega
  have d19055 : (x (-3) 2).toNat = 1 := by
    have r19056 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := hcov13 (-1)
    have b19057 := hb (x (-3) 2)
    have b19058 := hb (x (-1) 13)
    have b19059 := hb (x (-2) 1 && x (-2) 14)
    clear * - r19056 b19057 b19058 b19059 g1 d19051
    omega
  have d19060 : (x (-3) 14).toNat = 1 := by
    have r19061 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
    have b19062 := hb (x (-3) 2)
    have b19063 := hb (x (-3) 14)
    clear * - r19061 b19062 b19063 d19055
    omega
  have d19064 : (x (-4) 1).toNat = 0 := by
    have r19065 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := hd14 (-3)
    have b19066 := hb (x (-4) 1)
    have b19067 := hb (x (-3) 14)
    clear * - r19065 b19066 b19067 d19060
    omega
  have d19068 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
    have r19069 := hand1 (x (-4) 1) (x (-4) 14)
    have b19070 := hb (x (-4) 1)
    have b19071 := hb (x (-4) 1 && x (-4) 14)
    clear * - r19069 b19070 b19071 d19064
    omega
  have d19072 : (x (-5) 2).toNat = 1 := by
    have r19073 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := hcov13 (-3)
    have b19074 := hb (x (-5) 2)
    have b19075 := hb (x (-3) 13)
    have b19076 := hb (x (-4) 1 && x (-4) 14)
    clear * - r19073 b19074 b19075 b19076 g0 d19068
    omega
  have d19077 : (x (-4) 13).toNat = 0 := by
    have r19078 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
    have b19079 := hb (x (-4) 1)
    have b19080 := hb (x (-4) 13)
    clear * - r19078 b19079 b19080 d19064
    omega
  have d19081 : (x (-2) 13).toNat = 0 := by
    have r19082 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
    have b19083 := hb (x (-2) 1)
    have b19084 := hb (x (-2) 13)
    clear * - r19082 b19083 b19084 d19047
    omega
  have d19085 : (x (-4) 2).toNat = 1 := by
    have r19086 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := hcov13 (-2)
    have b19087 := hb (x (-4) 2)
    have b19088 := hb (x (-2) 13)
    have b19089 := hb (x (-3) 1 && x (-3) 14)
    clear * - r19086 b19087 b19088 b19089 d19081 g7
    omega
  have d19090 : (x (-1) 3).toNat = 0 := by
    have r19091 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := hd12 2
    have e19092 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e19093 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b19094 := hb (x (-1) 3)
    have b19095 := hb (x 0 2)
    have b19096 := hb (x 1 13)
    have b19097 := hb (x 2 12)
    clear * - r19091 e19092 e19093 b19094 b19095 b19096 b19097 d19014 d19026 g2
    omega
  have d19098 : (x (-1) 3 && x (-1) 14).toNat = 0 := by
    have r19099 := hand1 (x (-1) 3) (x (-1) 14)
    have b19100 := hb (x (-1) 3)
    have b19101 := hb (x (-1) 3 && x (-1) 14)
    clear * - r19099 b19100 b19101 d19090
    omega
  have d19102 : (x 1 12).toNat = 0 := by
    have r19103 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
    have e19104 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e19105 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b19106 := hb (x (-2) 3)
    have b19107 := hb (x (-1) 2)
    have b19108 := hb (x 0 13)
    have b19109 := hb (x 1 12)
    clear * - r19103 e19104 e19105 b19106 b19107 b19108 b19109 g3 d19038
    omega
  have d19110 : (x 1 1 && x 1 12).toNat = 0 := by
    have r19111 := hand2 (x 1 1) (x 1 12)
    have b19112 := hb (x 1 12)
    have b19113 := hb (x 1 1 && x 1 12)
    clear * - r19111 b19112 b19113 d19102
    omega
  have d19114 : (x (-2) 3).toNat = 0 := by
    have r19115 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
    have e19116 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e19117 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b19118 := hb (x (-2) 3)
    have b19119 := hb (x (-1) 2)
    have b19120 := hb (x 0 13)
    have b19121 := hb (x 1 12)
    clear * - r19115 e19116 e19117 b19118 b19119 b19120 b19121 d19102 g3 d19038
    omega
  have d19122 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
    have r19123 := hand1 (x (-2) 3) (x (-2) 14)
    have b19124 := hb (x (-2) 3)
    have b19125 := hb (x (-2) 3 && x (-2) 14)
    clear * - r19123 b19124 b19125 d19114
    omega
  have d19126 : (x (-1) 12).toNat = 0 := by
    have r19127 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
    have e19128 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e19129 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b19130 := hb (x (-4) 3)
    have b19131 := hb (x (-3) 2)
    have b19132 := hb (x (-2) 13)
    have b19133 := hb (x (-1) 12)
    clear * - r19127 e19128 e19129 b19130 b19131 b19132 b19133 d19081 d19055
    omega
  have d19134 : (x (-1) 4).toNat = 0 := by
    have r19135 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
    have b19136 := hb (x (-1) 4)
    have b19137 := hb (x (-1) 12)
    clear * - r19135 b19136 b19137 d19126
    omega
  have d19138 : (x (-2) 12).toNat = 0 := by
    have r19139 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := hd12 (-2)
    have e19140 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
    have e19141 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
    have b19142 := hb (x (-5) 3)
    have b19143 := hb (x (-4) 2)
    have b19144 := hb (x (-3) 13)
    have b19145 := hb (x (-2) 12)
    clear * - r19139 e19140 e19141 b19142 b19143 b19144 b19145 g0 d19085
    omega
  have d19146 : (x (-2) 4).toNat = 0 := by
    have r19147 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
    have b19148 := hb (x (-2) 4)
    have b19149 := hb (x (-2) 12)
    clear * - r19147 b19148 b19149 d19138
    omega
  have d19150 : (x (-3) 12).toNat = 0 := by
    have r19151 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := hd12 (-3)
    have e19152 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
    have e19153 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
    have b19154 := hb (x (-6) 3)
    have b19155 := hb (x (-5) 2)
    have b19156 := hb (x (-4) 13)
    have b19157 := hb (x (-3) 12)
    clear * - r19151 e19152 e19153 b19154 b19155 b19156 b19157 d19077 d19072
    omega
  have d19158 : (x (-3) 4).toNat = 0 := by
    have r19159 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
    have b19160 := hb (x (-3) 4)
    have b19161 := hb (x (-3) 12)
    clear * - r19159 b19160 b19161 d19150
    omega
  have d19162 : (x 2 11).toNat = 1 := by
    have r19163 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := hcov11 2
    have b19164 := hb (x (-2) 4)
    have b19165 := hb (x 2 11)
    have b19166 := hb (x 1 1 && x 1 12)
    have b19167 := hb (x 0 2 && x 0 13)
    have b19168 := hb (x (-1) 3 && x (-1) 14)
    clear * - r19163 b19164 b19165 b19166 b19167 b19168 d19110 g6 d19098 d19146
    omega
  have d19169 : (x 2 3).toNat = 1 := by
    have r19170 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
    have b19171 := hb (x 2 3)
    have b19172 := hb (x 2 11)
    clear * - r19170 b19171 b19172 d19162
    omega
  have d19173 : (x 5 12).toNat = 0 := by
    have r19174 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
    have e19175 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e19176 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b19177 := hb (x 2 3)
    have b19178 := hb (x 3 2)
    have b19179 := hb (x 4 13)
    have b19180 := hb (x 5 12)
    clear * - r19174 e19175 e19176 b19177 b19178 b19179 b19180 d19169
    omega
  have d19181 : (x 4 13).toNat = 0 := by
    have r19182 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
    have e19183 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e19184 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b19185 := hb (x 2 3)
    have b19186 := hb (x 3 2)
    have b19187 := hb (x 4 13)
    have b19188 := hb (x 5 12)
    clear * - r19182 e19183 e19184 b19185 b19186 b19187 b19188 d19173 d19169
    omega
  have d19189 : (x 3 2).toNat = 0 := by
    have r19190 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
    have e19191 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e19192 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b19193 := hb (x 2 3)
    have b19194 := hb (x 3 2)
    have b19195 := hb (x 4 13)
    have b19196 := hb (x 5 12)
    clear * - r19190 e19191 e19192 b19193 b19194 b19195 b19196 d19173 d19181 d19169
    omega
  have d19197 : (x 1 11).toNat = 1 := by
    have r19198 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := hcov11 1
    have b19199 := hb (x (-3) 4)
    have b19200 := hb (x 1 11)
    have b19201 := hb (x 0 1 && x 0 12)
    have b19202 := hb (x (-1) 2 && x (-1) 13)
    have b19203 := hb (x (-2) 3 && x (-2) 14)
    clear * - r19198 b19199 b19200 b19201 b19202 b19203 g4 g5 d19122 d19158
    omega
  have d19204 : (x 1 3).toNat = 1 := by
    have r19205 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
    have b19206 := hb (x 1 3)
    have b19207 := hb (x 1 11)
    clear * - r19205 b19206 b19207 d19197
    omega
  have d19208 : (x 4 12).toNat = 0 := by
    have r19209 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
    have e19210 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e19211 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b19212 := hb (x 1 3)
    have b19213 := hb (x 2 2)
    have b19214 := hb (x 3 13)
    have b19215 := hb (x 4 12)
    clear * - r19209 e19210 e19211 b19212 b19213 b19214 b19215 d19204
    omega
  have d19216 : (x 3 13).toNat = 0 := by
    have r19217 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
    have e19218 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e19219 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b19220 := hb (x 1 3)
    have b19221 := hb (x 2 2)
    have b19222 := hb (x 3 13)
    have b19223 := hb (x 4 12)
    clear * - r19217 e19218 e19219 b19220 b19221 b19222 b19223 d19208 d19204
    omega
  have d19224 : (x 2 2).toNat = 0 := by
    have r19225 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
    have e19226 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e19227 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b19228 := hb (x 1 3)
    have b19229 := hb (x 2 2)
    have b19230 := hb (x 3 13)
    have b19231 := hb (x 4 12)
    clear * - r19225 e19226 e19227 b19228 b19229 b19230 b19231 d19208 d19216 d19204
    omega
  have d19232 : (x 3 1 && x 3 14).toNat = 1 := by
    have r19233 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
    have b19234 := hb (x 2 2)
    have b19235 := hb (x 4 13)
    have b19236 := hb (x 3 1 && x 3 14)
    clear * - r19233 b19234 b19235 b19236 d19181 d19224
    omega
  have d19237 : (x 3 14).toNat = 1 := by
    have r19238 := hand2 (x 3 1) (x 3 14)
    have b19239 := hb (x 3 14)
    have b19240 := hb (x 3 1 && x 3 14)
    clear * - r19238 b19239 b19240 d19232
    omega
  have d19241 : (x 2 1).toNat = 0 := by
    have r19242 : (x 3 14).toNat + (x 2 1).toNat = 1 := hd14 3
    have b19243 := hb (x 2 1)
    have b19244 := hb (x 3 14)
    clear * - r19242 b19243 b19244 d19237
    omega
  have d19245 : (x 2 1 && x 2 14).toNat = 0 := by
    have r19246 := hand1 (x 2 1) (x 2 14)
    have b19247 := hb (x 2 1)
    have b19248 := hb (x 2 1 && x 2 14)
    clear * - r19246 b19247 b19248 d19241
    omega
  have d19249 : (x 1 2).toNat = 1 := by
    have r19250 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := hcov13 3
    have b19251 := hb (x 1 2)
    have b19252 := hb (x 3 13)
    have b19253 := hb (x 2 1 && x 2 14)
    clear * - r19250 b19251 b19252 b19253 d19216 d19245
    omega
  have d19254 : (x 3 12).toNat = 0 := by
    have r19255 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := hd12 3
    have e19256 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e19257 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b19258 := hb (x 0 3)
    have b19259 := hb (x 1 2)
    have b19260 := hb (x 2 13)
    have b19261 := hb (x 3 12)
    clear * - r19255 e19256 e19257 b19258 b19259 b19260 b19261 d19249
    omega
  have d19262 : (x 2 13).toNat = 0 := by
    have r19263 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := hd12 3
    have e19264 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e19265 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b19266 := hb (x 0 3)
    have b19267 := hb (x 1 2)
    have b19268 := hb (x 2 13)
    have b19269 := hb (x 3 12)
    clear * - r19263 e19264 e19265 b19266 b19267 b19268 b19269 d19254 d19249
    omega
  have d19270 : (x 0 3).toNat = 0 := by
    have r19271 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := hd12 3
    have e19272 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e19273 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b19274 := hb (x 0 3)
    have b19275 := hb (x 1 2)
    have b19276 := hb (x 2 13)
    have b19277 := hb (x 3 12)
    clear * - r19271 e19272 e19273 b19274 b19275 b19276 b19277 d19254 d19262 d19249
    omega
  have d19278 : (x 0 3 && x 0 14).toNat = 0 := by
    have r19279 := hand1 (x 0 3) (x 0 14)
    have b19280 := hb (x 0 3)
    have b19281 := hb (x 0 3 && x 0 14)
    clear * - r19279 b19280 b19281 d19270
    omega
  have d19282 : (x 3 11).toNat = 1 := by
    have r19283 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := hcov11 3
    have b19284 := hb (x (-1) 4)
    have b19285 := hb (x 3 11)
    have b19286 := hb (x 2 1 && x 2 12)
    have b19287 := hb (x 1 2 && x 1 13)
    have b19288 := hb (x 0 3 && x 0 14)
    clear * - r19283 b19284 b19285 b19286 b19287 b19288 d19022 d19034 d19278 d19134
    omega
  have d19289 : (x 3 3).toNat = 1 := by
    have r19290 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
    have b19291 := hb (x 3 3)
    have b19292 := hb (x 3 11)
    clear * - r19290 b19291 b19292 d19282
    omega
  have d19293 : (x 6 12).toNat = 0 := by
    have r19294 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
    have e19295 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e19296 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b19297 := hb (x 3 3)
    have b19298 := hb (x 4 2)
    have b19299 := hb (x 5 13)
    have b19300 := hb (x 6 12)
    clear * - r19294 e19295 e19296 b19297 b19298 b19299 b19300 d19289
    omega
  have d19301 : (x 5 13).toNat = 0 := by
    have r19302 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
    have e19303 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e19304 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b19305 := hb (x 3 3)
    have b19306 := hb (x 4 2)
    have b19307 := hb (x 5 13)
    have b19308 := hb (x 6 12)
    clear * - r19302 e19303 e19304 b19305 b19306 b19307 b19308 d19293 d19289
    omega
  have d19309 : (x 4 1 && x 4 14).toNat = 1 := by
    have r19310 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := hcov13 5
    have b19311 := hb (x 3 2)
    have b19312 := hb (x 5 13)
    have b19313 := hb (x 4 1 && x 4 14)
    clear * - r19310 b19311 b19312 b19313 d19301 d19189
    omega
  have d19314 : (x 4 14).toNat = 1 := by
    have r19315 := hand2 (x 4 1) (x 4 14)
    have b19316 := hb (x 4 14)
    have b19317 := hb (x 4 1 && x 4 14)
    clear * - r19315 b19316 b19317 d19309
    omega
  have d19318 : (x 3 1).toNat = 0 := by
    have r19319 : (x 4 14).toNat + (x 3 1).toNat = 1 := hd14 4
    have b19320 := hb (x 3 1)
    have b19321 := hb (x 4 14)
    clear * - r19319 b19320 b19321 d19314
    omega
  have r19322 := hand1 (x 3 1) (x 3 14)
  have b19323 := hb (x 3 1)
  have b19324 := hb (x 3 1 && x 3 14)
  linarith only [r19322, b19323, b19324, d19232, d19318]

theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b1 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 13).toNat = 0)
    (g1 : (x (-1) 13).toNat = 0)
    (g2 : (x 0 2).toNat = 1)
    (g3 : (x 0 13).toNat = 0)
    (g4 : (x 0 1 && x 0 12).toNat = 0)
    (g5 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g6 : (x 0 2 && x 0 13).toNat = 0)
    (g7 : (x (-3) 1 && x (-3) 14).toNat = 0)
    (g8 : (x 0 1 && x 0 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b1_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8
