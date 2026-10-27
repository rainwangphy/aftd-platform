import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_four_iff_five_core_b01

Topic: combinatorics   Node: b64590a1baf8

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_four_iff_five_core: under the layer-free tight-cover constraints for k = 15 and 51 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_four_iff_five_core_b01_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-2) 7).toNat = 0)
    (g1 : (x (-2) 11).toNat = 0)
    (g2 : (x (-1) 6).toNat = 0)
    (g3 : (x (-1) 10).toNat = 0)
    (g4 : (x 0 2).toNat = 1)
    (g5 : (x 0 3).toNat = 0)
    (g6 : (x 0 4).toNat = 0)
    (g7 : (x 0 5).toNat = 1)
    (g8 : (x 0 11).toNat = 0)
    (g9 : (x 1 2).toNat = 0)
    (g10 : (x 1 4).toNat = 0)
    (g11 : (x 1 6).toNat = 0)
    (g12 : (x 1 10).toNat = 0)
    (g13 : (x 3 10).toNat = 0)
    (g14 : (x 4 9).toNat = 0)
    (g15 : (x (-1) 10 && x (-1) 13).toNat = 0)
    (g16 : (x (-2) 11 && x (-2) 14).toNat = 0)
    (g17 : (x 0 4 && x 0 8).toNat = 0)
    (g18 : (x 0 4 && x 0 9).toNat = 0)
    (g19 : (x (-1) 5 && x (-1) 10).toNat = 0)
    (g20 : (x (-2) 6 && x (-2) 11).toNat = 0)
    (g21 : (x 1 4 && x 1 9).toNat = 0)
    (g22 : (x (-1) 6 && x (-1) 11).toNat = 0)
    (g23 : (x (-2) 7 && x (-2) 12).toNat = 0)
    (g24 : (x 1 9 && x 1 14).toNat = 0)
    (g25 : (x 5 8 && x 5 13).toNat = 0)
    (g26 : (x 4 9 && x 4 14).toNat = 0)
    (g27 : (x 1 7 && x 1 14).toNat = 0)
    (g28 : (x (-1) 2 && x (-1) 11).toNat = 0)
    (g29 : (x (-2) 3 && x (-2) 12).toNat = 0)
    (g30 : (x 1 1 && x 1 10).toNat = 0)
    (g31 : (x 0 2 && x 0 11).toNat = 0)
    (g32 : (x 1 2 && x 1 11).toNat = 0)
    (g33 : (x 0 3 && x 0 12).toNat = 0)
    (g34 : (x 3 1 && x 3 10).toNat = 0)
    (g35 : (x 2 2 && x 2 11).toNat = 0)
    (g36 : (x 1 3 && x 1 12).toNat = 0)
    (g37 : (x 0 4 && x 0 13).toNat = 0)
    (g38 : (x 1 5 && x 1 14).toNat = 0)
    (g39 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g40 : (x 0 1 && x 0 11).toNat = 0)
    (g41 : (x (-1) 2 && x (-1) 12).toNat = 0)
    (g42 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g43 : (x 2 1 && x 2 11).toNat = 0)
    (g44 : (x 1 2 && x 1 12).toNat = 0)
    (g45 : (x 0 3 && x 0 13).toNat = 0)
    (g46 : (x 0 4 && x 0 14).toNat = 0)
    (g47 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g48 : (x (-2) 3 && x (-2) 14).toNat = 0)
    (g49 : (x 1 2 && x 1 13).toNat = 0)
    (g50 : (x 0 3 && x 0 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d2018 : (x 0 14).toNat = 1 := by
    have r2019 : (x 0 2).toNat ≤ (x 0 14).toNat := himp _ _ (hp2 0)
    have b2020 := hb (x 0 2)
    have b2021 := hb (x 0 14)
    clear * - r2019 b2020 b2021 g4
    omega
  have d2022 : (x (-1) 1).toNat = 0 := by
    have r2023 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2024 := hb (x (-1) 1)
    have b2025 := hb (x 0 14)
    clear * - r2023 b2024 b2025 d2018
    omega
  have d2026 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
    have r2027 := hand1 (x (-1) 1) (x (-1) 12)
    have b2028 := hb (x (-1) 1)
    have b2029 := hb (x (-1) 1 && x (-1) 12)
    clear * - r2027 b2028 b2029 d2022
    omega
  have d2030 : (x (-1) 1 && x (-1) 11).toNat = 0 := by
    have r2031 := hand1 (x (-1) 1) (x (-1) 11)
    have b2032 := hb (x (-1) 1)
    have b2033 := hb (x (-1) 1 && x (-1) 11)
    clear * - r2031 b2032 b2033 d2022
    omega
  have d2034 : (x (-1) 1 && x (-1) 8).toNat = 0 := by
    have r2035 := hand1 (x (-1) 1) (x (-1) 8)
    have b2036 := hb (x (-1) 1)
    have b2037 := hb (x (-1) 1 && x (-1) 8)
    clear * - r2035 b2036 b2037 d2022
    omega
  have d2038 : (x (-1) 13).toNat = 0 := by
    have r2039 : (x (-1) 13).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp13 (-1))
    have b2040 := hb (x (-1) 1)
    have b2041 := hb (x (-1) 13)
    clear * - r2039 b2040 b2041 d2022
    omega
  have d2042 : (x (-1) 4 && x (-1) 13).toNat = 0 := by
    have r2043 := hand2 (x (-1) 4) (x (-1) 13)
    have b2044 := hb (x (-1) 13)
    have b2045 := hb (x (-1) 4 && x (-1) 13)
    clear * - r2043 b2044 b2045 d2038
    omega
  have d2046 : (x (-1) 5).toNat = 0 := by
    have r2047 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
    have b2048 := hb (x (-1) 5)
    have b2049 := hb (x (-1) 13)
    clear * - r2047 b2048 b2049 d2038
    omega
  have d2050 : (x (-1) 5 && x (-1) 14).toNat = 0 := by
    have r2051 := hand1 (x (-1) 5) (x (-1) 14)
    have b2052 := hb (x (-1) 5)
    have b2053 := hb (x (-1) 5 && x (-1) 14)
    clear * - r2051 b2052 b2053 d2046
    omega
  have d2054 : (x (-1) 5 && x (-1) 9).toNat = 0 := by
    have r2055 := hand1 (x (-1) 5) (x (-1) 9)
    have b2056 := hb (x (-1) 5)
    have b2057 := hb (x (-1) 5 && x (-1) 9)
    clear * - r2055 b2056 b2057 d2046
    omega
  have d2058 : (x (-1) 9).toNat = 0 := by
    have r2059 : (x (-1) 9).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp9 (-1))
    have b2060 := hb (x (-1) 1)
    have b2061 := hb (x (-1) 9)
    clear * - r2059 b2060 b2061 d2022
    omega
  have d2062 : (x 2 12).toNat = 0 := by
    have r2063 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2064 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e2065 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b2066 := hb (x (-1) 3)
    have b2067 := hb (x 0 2)
    have b2068 := hb (x 1 13)
    have b2069 := hb (x 2 12)
    clear * - r2063 e2064 e2065 b2066 b2067 b2068 b2069 g4
    omega
  have d2070 : (x 2 1 && x 2 12).toNat = 0 := by
    have r2071 := hand2 (x 2 1) (x 2 12)
    have b2072 := hb (x 2 12)
    have b2073 := hb (x 2 1 && x 2 12)
    clear * - r2071 b2072 b2073 d2062
    omega
  have d2074 : (x 2 2 && x 2 12).toNat = 0 := by
    have r2075 := hand2 (x 2 2) (x 2 12)
    have b2076 := hb (x 2 12)
    have b2077 := hb (x 2 2 && x 2 12)
    clear * - r2075 b2076 b2077 d2062
    omega
  have d2078 : (x 2 4).toNat = 0 := by
    have r2079 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
    have b2080 := hb (x 2 4)
    have b2081 := hb (x 2 12)
    clear * - r2079 b2080 b2081 d2062
    omega
  have d2082 : (x 2 4 && x 2 13).toNat = 0 := by
    have r2083 := hand1 (x 2 4) (x 2 13)
    have b2084 := hb (x 2 4)
    have b2085 := hb (x 2 4 && x 2 13)
    clear * - r2083 b2084 b2085 d2078
    omega
  have d2086 : (x 1 13).toNat = 0 := by
    have r2087 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2088 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e2089 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b2090 := hb (x (-1) 3)
    have b2091 := hb (x 0 2)
    have b2092 := hb (x 1 13)
    have b2093 := hb (x 2 12)
    clear * - r2087 e2088 e2089 b2090 b2091 b2092 b2093 d2062 g4
    omega
  have d2094 : (x 1 3 && x 1 13).toNat = 0 := by
    have r2095 := hand2 (x 1 3) (x 1 13)
    have b2096 := hb (x 1 13)
    have b2097 := hb (x 1 3 && x 1 13)
    clear * - r2095 b2096 b2097 d2086
    omega
  have d2098 : (x 1 5).toNat = 0 := by
    have r2099 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
    have b2100 := hb (x 1 5)
    have b2101 := hb (x 1 13)
    clear * - r2099 b2100 b2101 d2086
    omega
  have d2102 : (x (-1) 3).toNat = 0 := by
    have r2103 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2104 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e2105 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b2106 := hb (x (-1) 3)
    have b2107 := hb (x 0 2)
    have b2108 := hb (x 1 13)
    have b2109 := hb (x 2 12)
    clear * - r2103 e2104 e2105 b2106 b2107 b2108 b2109 d2062 d2086 g4
    omega
  have d2110 : (x (-1) 3 && x (-1) 12).toNat = 0 := by
    have r2111 := hand1 (x (-1) 3) (x (-1) 12)
    have b2112 := hb (x (-1) 3)
    have b2113 := hb (x (-1) 3 && x (-1) 12)
    clear * - r2111 b2112 b2113 d2102
    omega
  have d2114 : (x (-1) 11).toNat = 0 := by
    have r2115 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
    have b2116 := hb (x (-1) 3)
    have b2117 := hb (x (-1) 11)
    clear * - r2115 b2116 b2117 d2102
    omega
  have d2118 : (x (-2) 6).toNat = 1 := by
    have r2119 : 1 ≤ (x 4 9).toNat + (x 3 1 && x 3 10).toNat + (x 2 2 && x 2 11).toNat + (x 1 3 && x 1 12).toNat + (x 0 4 && x 0 13).toNat + (x (-1) 5 && x (-1) 14).toNat + (x (-2) 6).toNat := by have q := hcov9 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2120 := hb (x (-2) 6)
    have b2121 := hb (x 4 9)
    have b2122 := hb (x 3 1 && x 3 10)
    have b2123 := hb (x 2 2 && x 2 11)
    have b2124 := hb (x 1 3 && x 1 12)
    have b2125 := hb (x 0 4 && x 0 13)
    have b2126 := hb (x (-1) 5 && x (-1) 14)
    clear * - r2119 b2120 b2121 b2122 b2123 b2124 b2125 b2126 g14 g34 g35 g36 g37 d2050
    omega
  have d2127 : (x (-2) 14).toNat = 1 := by
    have r2128 : (x (-2) 6).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp6 (-2))
    have b2129 := hb (x (-2) 6)
    have b2130 := hb (x (-2) 14)
    clear * - r2128 b2129 b2130 d2118
    omega
  have d2131 : (x (-3) 1).toNat = 0 := by
    have r2132 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2133 := hb (x (-3) 1)
    have b2134 := hb (x (-2) 14)
    clear * - r2132 b2133 b2134 d2127
    omega
  have d2135 : (x (-3) 1 && x (-3) 12).toNat = 0 := by
    have r2136 := hand1 (x (-3) 1) (x (-3) 12)
    have b2137 := hb (x (-3) 1)
    have b2138 := hb (x (-3) 1 && x (-3) 12)
    clear * - r2136 b2137 b2138 d2131
    omega
  have d2139 : (x (-3) 13).toNat = 0 := by
    have r2140 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
    have b2141 := hb (x (-3) 1)
    have b2142 := hb (x (-3) 13)
    clear * - r2140 b2141 b2142 d2131
    omega
  have d2143 : (x (-3) 2 && x (-3) 13).toNat = 0 := by
    have r2144 := hand2 (x (-3) 2) (x (-3) 13)
    have b2145 := hb (x (-3) 13)
    have b2146 := hb (x (-3) 2 && x (-3) 13)
    clear * - r2144 b2145 b2146 d2139
    omega
  have d2147 : (x (-3) 3 && x (-3) 13).toNat = 0 := by
    have r2148 := hand2 (x (-3) 3) (x (-3) 13)
    have b2149 := hb (x (-3) 13)
    have b2150 := hb (x (-3) 3 && x (-3) 13)
    clear * - r2148 b2149 b2150 d2139
    omega
  have d2151 : (x (-3) 4 && x (-3) 13).toNat = 0 := by
    have r2152 := hand2 (x (-3) 4) (x (-3) 13)
    have b2153 := hb (x (-3) 13)
    have b2154 := hb (x (-3) 4 && x (-3) 13)
    clear * - r2152 b2153 b2154 d2139
    omega
  have d2155 : (x (-3) 8 && x (-3) 13).toNat = 0 := by
    have r2156 := hand2 (x (-3) 8) (x (-3) 13)
    have b2157 := hb (x (-3) 13)
    have b2158 := hb (x (-3) 8 && x (-3) 13)
    clear * - r2156 b2157 b2158 d2139
    omega
  have d2159 : (x (-3) 5).toNat = 0 := by
    have r2160 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
    have b2161 := hb (x (-3) 5)
    have b2162 := hb (x (-3) 13)
    clear * - r2160 b2161 b2162 d2139
    omega
  have d2163 : (x (-3) 5 && x (-3) 14).toNat = 0 := by
    have r2164 := hand1 (x (-3) 5) (x (-3) 14)
    have b2165 := hb (x (-3) 5)
    have b2166 := hb (x (-3) 5 && x (-3) 14)
    clear * - r2164 b2165 b2166 d2159
    omega
  have d2167 : (x 4 8).toNat = 0 := by
    have r2168 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2169 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e2170 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e2171 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e2172 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e2173 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e2174 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b2175 := hb (x (-3) 7)
    have b2176 := hb (x (-2) 6)
    have b2177 := hb (x (-1) 5)
    have b2178 := hb (x 0 4)
    have b2179 := hb (x 1 11)
    have b2180 := hb (x 2 10)
    have b2181 := hb (x 3 9)
    have b2182 := hb (x 4 8)
    clear * - r2168 e2169 e2170 e2171 e2172 e2173 e2174 b2175 b2176 b2177 b2178 b2179 b2180 b2181 b2182 g6 d2046 d2118
    omega
  have d2183 : (x 4 8 && x 4 14).toNat = 0 := by
    have r2184 := hand1 (x 4 8) (x 4 14)
    have b2185 := hb (x 4 8)
    have b2186 := hb (x 4 8 && x 4 14)
    clear * - r2184 b2185 b2186 d2167
    omega
  have d2187 : (x 4 5 && x 4 8).toNat = 0 := by
    have r2188 := hand2 (x 4 5) (x 4 8)
    have b2189 := hb (x 4 8)
    have b2190 := hb (x 4 5 && x 4 8)
    clear * - r2188 b2189 b2190 d2167
    omega
  have d2191 : (x 3 9).toNat = 0 := by
    have r2192 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2193 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e2194 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e2195 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e2196 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e2197 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e2198 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b2199 := hb (x (-3) 7)
    have b2200 := hb (x (-2) 6)
    have b2201 := hb (x (-1) 5)
    have b2202 := hb (x 0 4)
    have b2203 := hb (x 1 11)
    have b2204 := hb (x 2 10)
    have b2205 := hb (x 3 9)
    have b2206 := hb (x 4 8)
    clear * - r2192 e2193 e2194 e2195 e2196 e2197 e2198 b2199 b2200 b2201 b2202 b2203 b2204 b2205 b2206 d2167 g6 d2046 d2118
    omega
  have d2207 : (x 3 6 && x 3 9).toNat = 0 := by
    have r2208 := hand2 (x 3 6) (x 3 9)
    have b2209 := hb (x 3 9)
    have b2210 := hb (x 3 6 && x 3 9)
    clear * - r2208 b2209 b2210 d2191
    omega
  have d2211 : (x 2 10).toNat = 0 := by
    have r2212 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2213 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e2214 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e2215 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e2216 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e2217 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e2218 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b2219 := hb (x (-3) 7)
    have b2220 := hb (x (-2) 6)
    have b2221 := hb (x (-1) 5)
    have b2222 := hb (x 0 4)
    have b2223 := hb (x 1 11)
    have b2224 := hb (x 2 10)
    have b2225 := hb (x 3 9)
    have b2226 := hb (x 4 8)
    clear * - r2212 e2213 e2214 e2215 e2216 e2217 e2218 b2219 b2220 b2221 b2222 b2223 b2224 b2225 b2226 d2167 d2191 g6 d2046 d2118
    omega
  have d2227 : (x 2 1 && x 2 10).toNat = 0 := by
    have r2228 := hand2 (x 2 1) (x 2 10)
    have b2229 := hb (x 2 10)
    have b2230 := hb (x 2 1 && x 2 10)
    clear * - r2228 b2229 b2230 d2211
    omega
  have d2231 : (x 2 7 && x 2 10).toNat = 0 := by
    have r2232 := hand2 (x 2 7) (x 2 10)
    have b2233 := hb (x 2 10)
    have b2234 := hb (x 2 7 && x 2 10)
    clear * - r2232 b2233 b2234 d2211
    omega
  have d2235 : (x 1 11).toNat = 0 := by
    have r2236 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2237 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e2238 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e2239 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e2240 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e2241 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e2242 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b2243 := hb (x (-3) 7)
    have b2244 := hb (x (-2) 6)
    have b2245 := hb (x (-1) 5)
    have b2246 := hb (x 0 4)
    have b2247 := hb (x 1 11)
    have b2248 := hb (x 2 10)
    have b2249 := hb (x 3 9)
    have b2250 := hb (x 4 8)
    clear * - r2236 e2237 e2238 e2239 e2240 e2241 e2242 b2243 b2244 b2245 b2246 b2247 b2248 b2249 b2250 d2167 d2191 d2211 g6 d2046 d2118
    omega
  have d2251 : (x 1 8 && x 1 11).toNat = 0 := by
    have r2252 := hand2 (x 1 8) (x 1 11)
    have b2253 := hb (x 1 11)
    have b2254 := hb (x 1 8 && x 1 11)
    clear * - r2252 b2253 b2254 d2235
    omega
  have d2255 : (x (-3) 7).toNat = 0 := by
    have r2256 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2257 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e2258 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e2259 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e2260 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e2261 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e2262 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b2263 := hb (x (-3) 7)
    have b2264 := hb (x (-2) 6)
    have b2265 := hb (x (-1) 5)
    have b2266 := hb (x 0 4)
    have b2267 := hb (x 1 11)
    have b2268 := hb (x 2 10)
    have b2269 := hb (x 3 9)
    have b2270 := hb (x 4 8)
    clear * - r2256 e2257 e2258 e2259 e2260 e2261 e2262 b2263 b2264 b2265 b2266 b2267 b2268 b2269 b2270 d2167 d2191 d2211 d2235 g6 d2046 d2118
    omega
  have d2271 : (x (-3) 7 && x (-3) 12).toNat = 0 := by
    have r2272 := hand1 (x (-3) 7) (x (-3) 12)
    have b2273 := hb (x (-3) 7)
    have b2274 := hb (x (-3) 7 && x (-3) 12)
    clear * - r2272 b2273 b2274 d2255
    omega
  have d2275 : (x (-3) 7 && x (-3) 11).toNat = 0 := by
    have r2276 := hand1 (x (-3) 7) (x (-3) 11)
    have b2277 := hb (x (-3) 7)
    have b2278 := hb (x (-3) 7 && x (-3) 11)
    clear * - r2276 b2277 b2278 d2255
    omega
  cases h2279 : x 0 6
  · have f2280 : (x 0 6).toNat = 0 := by rw [h2279]; rfl
    cases h2281 : x 0 8
    · have f2282 : (x 0 8).toNat = 0 := by rw [h2281]; rfl
      cases h2283 : x 0 9
      · have f2284 : (x 0 9).toNat = 0 := by rw [h2283]; rfl
        have d2285 : (x 0 9 && x 0 12).toNat = 0 := by
          have r2286 := hand1 (x 0 9) (x 0 12)
          have b2287 := hb (x 0 9)
          have b2288 := hb (x 0 9 && x 0 12)
          clear * - r2286 b2287 b2288 f2284
          omega
        cases h2289 : x 0 7
        · have f2290 : (x 0 7).toNat = 0 := by rw [h2289]; rfl
          cases h2291 : x 0 10
          · have f2292 : (x 0 10).toNat = 0 := by rw [h2291]; rfl
            have d2293 : (x 0 5 && x 0 10).toNat = 0 := by
              have r2294 := hand2 (x 0 5) (x 0 10)
              have b2295 := hb (x 0 10)
              have b2296 := hb (x 0 5 && x 0 10)
              clear * - r2294 b2295 b2296 f2292
              omega
            cases h2297 : x 0 12
            · have f2298 : (x 0 12).toNat = 0 := by rw [h2297]; rfl
              have d2299 : (x 0 1 && x 0 12).toNat = 0 := by
                have r2300 := hand2 (x 0 1) (x 0 12)
                have b2301 := hb (x 0 12)
                have b2302 := hb (x 0 1 && x 0 12)
                clear * - r2300 b2301 b2302 f2298
                omega
              have d2303 : (x (-3) 4).toNat = 1 := by
                have r2304 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b2305 := hb (x (-3) 4)
                have b2306 := hb (x 1 11)
                have b2307 := hb (x 0 1 && x 0 12)
                have b2308 := hb (x (-1) 2 && x (-1) 13)
                have b2309 := hb (x (-2) 3 && x (-2) 14)
                clear * - r2304 b2305 b2306 b2307 b2308 b2309 d2235 d2299 g47 g48
                omega
              have d2310 : (x (-3) 12).toNat = 1 := by
                have r2311 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
                have b2312 := hb (x (-3) 4)
                have b2313 := hb (x (-3) 12)
                clear * - r2311 b2312 b2313 d2303
                omega
              have d2314 : (x (-4) 13).toNat = 0 := by
                have r2315 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2316 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                have e2317 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                have b2318 := hb (x (-6) 3)
                have b2319 := hb (x (-5) 2)
                have b2320 := hb (x (-4) 13)
                have b2321 := hb (x (-3) 12)
                clear * - r2315 e2316 e2317 b2318 b2319 b2320 b2321 d2310
                omega
              have d2322 : (x (-4) 5).toNat = 0 := by
                have r2323 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
                have b2324 := hb (x (-4) 5)
                have b2325 := hb (x (-4) 13)
                clear * - r2323 b2324 b2325 d2314
                omega
              have d2326 : (x (-5) 2).toNat = 0 := by
                have r2327 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2328 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                have e2329 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                have b2330 := hb (x (-6) 3)
                have b2331 := hb (x (-5) 2)
                have b2332 := hb (x (-4) 13)
                have b2333 := hb (x (-3) 12)
                clear * - r2327 e2328 e2329 b2330 b2331 b2332 b2333 d2310 d2314
                omega
              have d2334 : (x (-4) 1 && x (-4) 14).toNat = 1 := by
                have r2335 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b2336 := hb (x (-5) 2)
                have b2337 := hb (x (-3) 13)
                have b2338 := hb (x (-4) 1 && x (-4) 14)
                clear * - r2335 b2336 b2337 b2338 d2139 d2326
                omega
              have d2339 : (x (-4) 1).toNat = 1 := by
                have r2340 := hand1 (x (-4) 1) (x (-4) 14)
                have b2341 := hb (x (-4) 1)
                have b2342 := hb (x (-4) 1 && x (-4) 14)
                clear * - r2340 b2341 b2342 d2334
                omega
              have d2343 : (x (-3) 14).toNat = 0 := by
                have r2344 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b2345 := hb (x (-4) 1)
                have b2346 := hb (x (-3) 14)
                clear * - r2344 b2345 b2346 d2339
                omega
              have d2347 : (x (-3) 4 && x (-3) 14).toNat = 0 := by
                have r2348 := hand2 (x (-3) 4) (x (-3) 14)
                have b2349 := hb (x (-3) 14)
                have b2350 := hb (x (-3) 4 && x (-3) 14)
                clear * - r2348 b2349 b2350 d2343
                omega
              have r2351 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b2352 := hb (x (-4) 5)
              have b2353 := hb (x 1 10)
              have b2354 := hb (x 0 1 && x 0 11)
              have b2355 := hb (x (-1) 2 && x (-1) 12)
              have b2356 := hb (x (-2) 3 && x (-2) 13)
              have b2357 := hb (x (-3) 4 && x (-3) 14)
              linarith only [r2351, b2352, b2353, b2354, b2355, b2356, b2357, g12, g40, g41, g42, d2347, d2322]
            · have f2358 : (x 0 12).toNat = 1 := by rw [h2297]; rfl
              have d2359 : (x (-2) 2).toNat = 0 := by
                have r2360 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2361 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
                have e2362 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
                have b2363 := hb (x (-3) 3)
                have b2364 := hb (x (-2) 2)
                have b2365 := hb (x (-1) 13)
                have b2366 := hb (x 0 12)
                clear * - r2360 e2361 e2362 b2363 b2364 b2365 b2366 f2358 d2038
                omega
              have d2367 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
                have r2368 := hand1 (x (-2) 2) (x (-2) 13)
                have b2369 := hb (x (-2) 2)
                have b2370 := hb (x (-2) 2 && x (-2) 13)
                clear * - r2368 b2369 b2370 d2359
                omega
              have d2371 : (x (-2) 2 && x (-2) 12).toNat = 0 := by
                have r2372 := hand1 (x (-2) 2) (x (-2) 12)
                have b2373 := hb (x (-2) 2)
                have b2374 := hb (x (-2) 2 && x (-2) 12)
                clear * - r2372 b2373 b2374 d2359
                omega
              have d2375 : (x (-2) 2 && x (-2) 9).toNat = 0 := by
                have r2376 := hand1 (x (-2) 2) (x (-2) 9)
                have b2377 := hb (x (-2) 2)
                have b2378 := hb (x (-2) 2 && x (-2) 9)
                clear * - r2376 b2377 b2378 d2359
                omega
              have d2379 : (x (-2) 10).toNat = 0 := by
                have r2380 : (x (-2) 10).toNat ≤ (x (-2) 2).toNat := himp _ _ (hp10 (-2))
                have b2381 := hb (x (-2) 2)
                have b2382 := hb (x (-2) 10)
                clear * - r2380 b2381 b2382 d2359
                omega
              have d2383 : (x (-2) 6 && x (-2) 10).toNat = 0 := by
                have r2384 := hand2 (x (-2) 6) (x (-2) 10)
                have b2385 := hb (x (-2) 10)
                have b2386 := hb (x (-2) 6 && x (-2) 10)
                clear * - r2384 b2385 b2386 d2379
                omega
              have d2387 : (x (-3) 3).toNat = 0 := by
                have r2388 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2389 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
                have e2390 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
                have b2391 := hb (x (-3) 3)
                have b2392 := hb (x (-2) 2)
                have b2393 := hb (x (-1) 13)
                have b2394 := hb (x 0 12)
                clear * - r2388 e2389 e2390 b2391 b2392 b2393 b2394 f2358 d2038 d2359
                omega
              have d2395 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
                have r2396 := hand1 (x (-3) 3) (x (-3) 14)
                have b2397 := hb (x (-3) 3)
                have b2398 := hb (x (-3) 3 && x (-3) 14)
                clear * - r2396 b2397 b2398 d2387
                omega
              have d2399 : (x (-3) 3 && x (-3) 10).toNat = 0 := by
                have r2400 := hand1 (x (-3) 3) (x (-3) 10)
                have b2401 := hb (x (-3) 3)
                have b2402 := hb (x (-3) 3 && x (-3) 10)
                clear * - r2400 b2401 b2402 d2387
                omega
              have d2403 : (x (-3) 11).toNat = 0 := by
                have r2404 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
                have b2405 := hb (x (-3) 3)
                have b2406 := hb (x (-3) 11)
                clear * - r2404 b2405 b2406 d2387
                omega
              have d2407 : (x (-4) 4).toNat = 1 := by
                have r2408 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b2409 := hb (x (-4) 4)
                have b2410 := hb (x 0 11)
                have b2411 := hb (x (-1) 1 && x (-1) 12)
                have b2412 := hb (x (-2) 2 && x (-2) 13)
                have b2413 := hb (x (-3) 3 && x (-3) 14)
                clear * - r2408 b2409 b2410 b2411 b2412 b2413 g8 d2026 d2367 d2395
                omega
              have d2414 : (x (-4) 12).toNat = 1 := by
                have r2415 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
                have b2416 := hb (x (-4) 4)
                have b2417 := hb (x (-4) 12)
                clear * - r2415 b2416 b2417 d2407
                omega
              have d2418 : (x (-5) 13).toNat = 0 := by
                have r2419 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2420 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                have e2421 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                have b2422 := hb (x (-7) 3)
                have b2423 := hb (x (-6) 2)
                have b2424 := hb (x (-5) 13)
                have b2425 := hb (x (-4) 12)
                clear * - r2419 e2420 e2421 b2422 b2423 b2424 b2425 d2414
                omega
              have d2426 : (x (-5) 9 && x (-5) 13).toNat = 0 := by
                have r2427 := hand2 (x (-5) 9) (x (-5) 13)
                have b2428 := hb (x (-5) 13)
                have b2429 := hb (x (-5) 9 && x (-5) 13)
                clear * - r2427 b2428 b2429 d2418
                omega
              have d2430 : (x (-5) 5).toNat = 0 := by
                have r2431 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
                have b2432 := hb (x (-5) 5)
                have b2433 := hb (x (-5) 13)
                clear * - r2431 b2432 b2433 d2418
                omega
              have d2434 : (x (-5) 5 && x (-5) 12).toNat = 0 := by
                have r2435 := hand1 (x (-5) 5) (x (-5) 12)
                have b2436 := hb (x (-5) 5)
                have b2437 := hb (x (-5) 5 && x (-5) 12)
                clear * - r2435 b2436 b2437 d2430
                omega
              have d2438 : (x (-6) 2).toNat = 0 := by
                have r2439 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2440 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                have e2441 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                have b2442 := hb (x (-7) 3)
                have b2443 := hb (x (-6) 2)
                have b2444 := hb (x (-5) 13)
                have b2445 := hb (x (-4) 12)
                clear * - r2439 e2440 e2441 b2442 b2443 b2444 b2445 d2414 d2418
                omega
              have d2446 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
                have r2447 := hand1 (x (-6) 2) (x (-6) 13)
                have b2448 := hb (x (-6) 2)
                have b2449 := hb (x (-6) 2 && x (-6) 13)
                clear * - r2447 b2448 b2449 d2438
                omega
              have d2450 : (x (-6) 10).toNat = 0 := by
                have r2451 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
                have b2452 := hb (x (-6) 2)
                have b2453 := hb (x (-6) 10)
                clear * - r2451 b2452 b2453 d2438
                omega
              have d2454 : (x (-7) 3).toNat = 0 := by
                have r2455 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2456 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                have e2457 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                have b2458 := hb (x (-7) 3)
                have b2459 := hb (x (-6) 2)
                have b2460 := hb (x (-5) 13)
                have b2461 := hb (x (-4) 12)
                clear * - r2455 e2456 e2457 b2458 b2459 b2460 b2461 d2414 d2418 d2438
                omega
              have d2462 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
                have r2463 := hand1 (x (-7) 3) (x (-7) 14)
                have b2464 := hb (x (-7) 3)
                have b2465 := hb (x (-7) 3 && x (-7) 14)
                clear * - r2463 b2464 b2465 d2454
                omega
              have d2466 : (x (-7) 11).toNat = 0 := by
                have r2467 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
                have b2468 := hb (x (-7) 3)
                have b2469 := hb (x (-7) 11)
                clear * - r2467 b2468 b2469 d2454
                omega
              have d2470 : (x (-4) 4 && x (-4) 14).toNat = 1 := by
                have r2471 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b2472 := hb (x (-5) 5)
                have b2473 := hb (x 0 10)
                have b2474 := hb (x (-1) 1 && x (-1) 11)
                have b2475 := hb (x (-2) 2 && x (-2) 12)
                have b2476 := hb (x (-3) 3 && x (-3) 13)
                have b2477 := hb (x (-4) 4 && x (-4) 14)
                clear * - r2471 b2472 b2473 b2474 b2475 b2476 b2477 f2292 d2030 d2371 d2147 d2430
                omega
              have d2478 : (x (-4) 14).toNat = 1 := by
                have r2479 := hand2 (x (-4) 4) (x (-4) 14)
                have b2480 := hb (x (-4) 14)
                have b2481 := hb (x (-4) 4 && x (-4) 14)
                clear * - r2479 b2480 b2481 d2470
                omega
              have d2482 : (x (-5) 1).toNat = 0 := by
                have r2483 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b2484 := hb (x (-5) 1)
                have b2485 := hb (x (-4) 14)
                clear * - r2483 b2484 b2485 d2478
                omega
              have d2486 : (x (-5) 1 && x (-5) 14).toNat = 0 := by
                have r2487 := hand1 (x (-5) 1) (x (-5) 14)
                have b2488 := hb (x (-5) 1)
                have b2489 := hb (x (-5) 1 && x (-5) 14)
                clear * - r2487 b2488 b2489 d2482
                omega
              have d2490 : (x (-4) 13).toNat = 1 := by
                have r2491 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b2492 := hb (x (-6) 2)
                have b2493 := hb (x (-4) 13)
                have b2494 := hb (x (-5) 1 && x (-5) 14)
                clear * - r2491 b2492 b2493 b2494 d2486 d2438
                omega
              have d2495 : (x (-4) 1).toNat = 1 := by
                have r2496 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
                have b2497 := hb (x (-4) 1)
                have b2498 := hb (x (-4) 13)
                clear * - r2496 b2497 b2498 d2490
                omega
              have d2499 : (x (-3) 14).toNat = 0 := by
                have r2500 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b2501 := hb (x (-4) 1)
                have b2502 := hb (x (-3) 14)
                clear * - r2500 b2501 b2502 d2495
                omega
              have d2503 : (x (-3) 6).toNat = 0 := by
                have r2504 : (x (-3) 6).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp6 (-3))
                have b2505 := hb (x (-3) 6)
                have b2506 := hb (x (-3) 14)
                clear * - r2504 b2505 b2506 d2499
                omega
              have d2507 : (x (-3) 2).toNat = 0 := by
                have r2508 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
                have b2509 := hb (x (-3) 2)
                have b2510 := hb (x (-3) 14)
                clear * - r2508 b2509 b2510 d2499
                omega
              have d2511 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
                have r2512 := hand1 (x (-3) 2) (x (-3) 12)
                have b2513 := hb (x (-3) 2)
                have b2514 := hb (x (-3) 2 && x (-3) 12)
                clear * - r2512 b2513 b2514 d2507
                omega
              have d2515 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
                have r2516 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b2517 := hb (x (-3) 2)
                have b2518 := hb (x (-1) 13)
                have b2519 := hb (x (-2) 1 && x (-2) 14)
                clear * - r2516 b2517 b2518 b2519 d2038 d2507
                omega
              have d2520 : (x (-2) 1).toNat = 1 := by
                have r2521 := hand1 (x (-2) 1) (x (-2) 14)
                have b2522 := hb (x (-2) 1)
                have b2523 := hb (x (-2) 1 && x (-2) 14)
                clear * - r2521 b2522 b2523 d2515
                omega
              have d2524 : (x (-1) 14).toNat = 0 := by
                have r2525 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b2526 := hb (x (-2) 1)
                have b2527 := hb (x (-1) 14)
                clear * - r2525 b2526 b2527 d2520
                omega
              have d2528 : (x (-1) 4 && x (-1) 14).toNat = 0 := by
                have r2529 := hand2 (x (-1) 4) (x (-1) 14)
                have b2530 := hb (x (-1) 14)
                have b2531 := hb (x (-1) 4 && x (-1) 14)
                clear * - r2529 b2530 b2531 d2524
                omega
              have d2532 : (x (-2) 5).toNat = 1 := by
                have r2533 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b2534 := hb (x (-2) 5)
                have b2535 := hb (x 3 10)
                have b2536 := hb (x 2 1 && x 2 11)
                have b2537 := hb (x 1 2 && x 1 12)
                have b2538 := hb (x 0 3 && x 0 13)
                have b2539 := hb (x (-1) 4 && x (-1) 14)
                clear * - r2533 b2534 b2535 b2536 b2537 b2538 b2539 g13 g43 g44 g45 d2528
                omega
              have d2540 : (x (-2) 13).toNat = 1 := by
                have r2541 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
                have b2542 := hb (x (-2) 5)
                have b2543 := hb (x (-2) 13)
                clear * - r2541 b2542 b2543 d2532
                omega
              have d2544 : (x (-1) 12).toNat = 0 := by
                have r2545 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2546 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                have e2547 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                have b2548 := hb (x (-4) 3)
                have b2549 := hb (x (-3) 2)
                have b2550 := hb (x (-2) 13)
                have b2551 := hb (x (-1) 12)
                clear * - r2545 e2546 e2547 b2548 b2549 b2550 b2551 d2540 d2507
                omega
              have d2552 : (x (-1) 4).toNat = 0 := by
                have r2553 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
                have b2554 := hb (x (-1) 4)
                have b2555 := hb (x (-1) 12)
                clear * - r2553 b2554 b2555 d2544
                omega
              have d2556 : (x 3 11).toNat = 1 := by
                have r2557 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b2558 := hb (x (-1) 4)
                have b2559 := hb (x 3 11)
                have b2560 := hb (x 2 1 && x 2 12)
                have b2561 := hb (x 1 2 && x 1 13)
                have b2562 := hb (x 0 3 && x 0 14)
                clear * - r2557 b2558 b2559 b2560 b2561 b2562 d2070 g49 g50 d2552
                omega
              have d2563 : (x 3 3).toNat = 1 := by
                have r2564 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
                have b2565 := hb (x 3 3)
                have b2566 := hb (x 3 11)
                clear * - r2564 b2565 b2566 d2556
                omega
              have d2567 : (x 6 12).toNat = 0 := by
                have r2568 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2569 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                have e2570 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                have b2571 := hb (x 3 3)
                have b2572 := hb (x 4 2)
                have b2573 := hb (x 5 13)
                have b2574 := hb (x 6 12)
                clear * - r2568 e2569 e2570 b2571 b2572 b2573 b2574 d2563
                omega
              have d2575 : (x 6 5 && x 6 12).toNat = 0 := by
                have r2576 := hand2 (x 6 5) (x 6 12)
                have b2577 := hb (x 6 12)
                have b2578 := hb (x 6 5 && x 6 12)
                clear * - r2576 b2577 b2578 d2567
                omega
              have d2579 : (x 6 6 && x 6 12).toNat = 0 := by
                have r2580 := hand2 (x 6 6) (x 6 12)
                have b2581 := hb (x 6 12)
                have b2582 := hb (x 6 6 && x 6 12)
                clear * - r2580 b2581 b2582 d2567
                omega
              have d2583 : (x 6 7 && x 6 12).toNat = 0 := by
                have r2584 := hand2 (x 6 7) (x 6 12)
                have b2585 := hb (x 6 12)
                have b2586 := hb (x 6 7 && x 6 12)
                clear * - r2584 b2585 b2586 d2567
                omega
              have d2587 : (x 6 4).toNat = 0 := by
                have r2588 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
                have b2589 := hb (x 6 4)
                have b2590 := hb (x 6 12)
                clear * - r2588 b2589 b2590 d2567
                omega
              have d2591 : (x 6 4 && x 6 14).toNat = 0 := by
                have r2592 := hand1 (x 6 4) (x 6 14)
                have b2593 := hb (x 6 4)
                have b2594 := hb (x 6 4 && x 6 14)
                clear * - r2592 b2593 b2594 d2587
                omega
              have d2595 : (x 6 4 && x 6 13).toNat = 0 := by
                have r2596 := hand1 (x 6 4) (x 6 13)
                have b2597 := hb (x 6 4)
                have b2598 := hb (x 6 4 && x 6 13)
                clear * - r2596 b2597 b2598 d2587
                omega
              have d2599 : (x 5 13).toNat = 0 := by
                have r2600 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2601 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                have e2602 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                have b2603 := hb (x 3 3)
                have b2604 := hb (x 4 2)
                have b2605 := hb (x 5 13)
                have b2606 := hb (x 6 12)
                clear * - r2600 e2601 e2602 b2603 b2604 b2605 b2606 d2567 d2563
                omega
              have d2607 : (x 5 6 && x 5 13).toNat = 0 := by
                have r2608 := hand2 (x 5 6) (x 5 13)
                have b2609 := hb (x 5 13)
                have b2610 := hb (x 5 6 && x 5 13)
                clear * - r2608 b2609 b2610 d2599
                omega
              have d2611 : (x 5 7 && x 5 13).toNat = 0 := by
                have r2612 := hand2 (x 5 7) (x 5 13)
                have b2613 := hb (x 5 13)
                have b2614 := hb (x 5 7 && x 5 13)
                clear * - r2612 b2613 b2614 d2599
                omega
              have d2615 : (x 5 5).toNat = 0 := by
                have r2616 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
                have b2617 := hb (x 5 5)
                have b2618 := hb (x 5 13)
                clear * - r2616 b2617 b2618 d2599
                omega
              have d2619 : (x 5 5 && x 5 14).toNat = 0 := by
                have r2620 := hand1 (x 5 5) (x 5 14)
                have b2621 := hb (x 5 5)
                have b2622 := hb (x 5 5 && x 5 14)
                clear * - r2620 b2621 b2622 d2615
                omega
              have d2623 : (x 4 2).toNat = 0 := by
                have r2624 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2625 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                have e2626 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                have b2627 := hb (x 3 3)
                have b2628 := hb (x 4 2)
                have b2629 := hb (x 5 13)
                have b2630 := hb (x 6 12)
                clear * - r2624 e2625 e2626 b2627 b2628 b2629 b2630 d2567 d2599 d2563
                omega
              have d2631 : (x 4 10).toNat = 0 := by
                have r2632 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
                have b2633 := hb (x 4 2)
                have b2634 := hb (x 4 10)
                clear * - r2632 b2633 b2634 d2623
                omega
              have d2635 : (x 3 1 && x 3 11).toNat = 1 := by
                have r2636 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b2637 := hb (x (-1) 5)
                have b2638 := hb (x 4 10)
                have b2639 := hb (x 3 1 && x 3 11)
                have b2640 := hb (x 2 2 && x 2 12)
                have b2641 := hb (x 1 3 && x 1 13)
                have b2642 := hb (x 0 4 && x 0 14)
                clear * - r2636 b2637 b2638 b2639 b2640 b2641 b2642 d2631 d2074 d2094 g46 d2046
                omega
              have d2643 : (x 3 1).toNat = 1 := by
                have r2644 := hand1 (x 3 1) (x 3 11)
                have b2645 := hb (x 3 1)
                have b2646 := hb (x 3 1 && x 3 11)
                clear * - r2644 b2645 b2646 d2635
                omega
              have d2647 : (x 4 14).toNat = 0 := by
                have r2648 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b2649 := hb (x 3 1)
                have b2650 := hb (x 4 14)
                clear * - r2648 b2649 b2650 d2643
                omega
              have d2651 : (x 4 1 && x 4 14).toNat = 0 := by
                have r2652 := hand2 (x 4 1) (x 4 14)
                have b2653 := hb (x 4 14)
                have b2654 := hb (x 4 1 && x 4 14)
                clear * - r2652 b2653 b2654 d2647
                omega
              have d2655 : (x 3 2).toNat = 1 := by
                have r2656 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b2657 := hb (x 3 2)
                have b2658 := hb (x 5 13)
                have b2659 := hb (x 4 1 && x 4 14)
                clear * - r2656 b2657 b2658 b2659 d2599 d2651
                omega
              have d2660 : (x 3 14).toNat = 1 := by
                have r2661 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
                have b2662 := hb (x 3 2)
                have b2663 := hb (x 3 14)
                clear * - r2661 b2662 b2663 d2655
                omega
              have d2664 : (x 2 1).toNat = 0 := by
                have r2665 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b2666 := hb (x 2 1)
                have b2667 := hb (x 3 14)
                clear * - r2665 b2666 b2667 d2660
                omega
              have d2668 : (x 2 1 && x 2 14).toNat = 0 := by
                have r2669 := hand1 (x 2 1) (x 2 14)
                have b2670 := hb (x 2 1)
                have b2671 := hb (x 2 1 && x 2 14)
                clear * - r2669 b2670 b2671 d2664
                omega
              have d2672 : (x 3 13).toNat = 1 := by
                have r2673 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b2674 := hb (x 1 2)
                have b2675 := hb (x 3 13)
                have b2676 := hb (x 2 1 && x 2 14)
                clear * - r2673 b2674 b2675 b2676 d2668 g9
                omega
              have d2677 : (x 4 12).toNat = 0 := by
                have r2678 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2679 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e2680 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b2681 := hb (x 1 3)
                have b2682 := hb (x 2 2)
                have b2683 := hb (x 3 13)
                have b2684 := hb (x 4 12)
                clear * - r2678 e2679 e2680 b2681 b2682 b2683 b2684 d2672
                omega
              have d2685 : (x 4 4).toNat = 0 := by
                have r2686 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
                have b2687 := hb (x 4 4)
                have b2688 := hb (x 4 12)
                clear * - r2686 b2687 b2688 d2677
                omega
              have d2689 : (x 2 2).toNat = 0 := by
                have r2690 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2691 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e2692 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b2693 := hb (x 1 3)
                have b2694 := hb (x 2 2)
                have b2695 := hb (x 3 13)
                have b2696 := hb (x 4 12)
                clear * - r2690 e2691 e2692 b2693 b2694 b2695 b2696 d2677 d2672
                omega
              have d2697 : (x 2 2 && x 2 7).toNat = 0 := by
                have r2698 := hand1 (x 2 2) (x 2 7)
                have b2699 := hb (x 2 2)
                have b2700 := hb (x 2 2 && x 2 7)
                clear * - r2698 b2699 b2700 d2689
                omega
              have d2701 : (x 2 2 && x 2 6).toNat = 0 := by
                have r2702 := hand1 (x 2 2) (x 2 6)
                have b2703 := hb (x 2 2)
                have b2704 := hb (x 2 2 && x 2 6)
                clear * - r2702 b2703 b2704 d2689
                omega
              have d2705 : (x 1 3).toNat = 0 := by
                have r2706 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2707 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e2708 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b2709 := hb (x 1 3)
                have b2710 := hb (x 2 2)
                have b2711 := hb (x 3 13)
                have b2712 := hb (x 4 12)
                clear * - r2706 e2707 e2708 b2709 b2710 b2711 b2712 d2677 d2672 d2689
                omega
              have d2713 : (x 1 3 && x 1 8).toNat = 0 := by
                have r2714 := hand1 (x 1 3) (x 1 8)
                have b2715 := hb (x 1 3)
                have b2716 := hb (x 1 3 && x 1 8)
                clear * - r2714 b2715 b2716 d2705
                omega
              have d2717 : (x 1 3 && x 1 7).toNat = 0 := by
                have r2718 := hand1 (x 1 3) (x 1 7)
                have b2719 := hb (x 1 3)
                have b2720 := hb (x 1 3 && x 1 7)
                clear * - r2718 b2719 b2720 d2705
                omega
              have d2721 : (x 2 9).toNat = 0 := by
                have r2722 : (x 2 9).toNat ≤ (x 2 1).toNat := himp _ _ (hp9 2)
                have b2723 := hb (x 2 1)
                have b2724 := hb (x 2 9)
                clear * - r2722 b2723 b2724 d2664
                omega
              have d2725 : (x 5 12).toNat = 0 := by
                have r2726 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2727 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                have e2728 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                have b2729 := hb (x 2 3)
                have b2730 := hb (x 3 2)
                have b2731 := hb (x 4 13)
                have b2732 := hb (x 5 12)
                clear * - r2726 e2727 e2728 b2729 b2730 b2731 b2732 d2655
                omega
              have d2733 : (x 5 6 && x 5 12).toNat = 0 := by
                have r2734 := hand2 (x 5 6) (x 5 12)
                have b2735 := hb (x 5 12)
                have b2736 := hb (x 5 6 && x 5 12)
                clear * - r2734 b2735 b2736 d2725
                omega
              have d2737 : (x 5 4).toNat = 0 := by
                have r2738 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
                have b2739 := hb (x 5 4)
                have b2740 := hb (x 5 12)
                clear * - r2738 b2739 b2740 d2725
                omega
              have d2741 : (x 5 4 && x 5 7).toNat = 0 := by
                have r2742 := hand1 (x 5 4) (x 5 7)
                have b2743 := hb (x 5 4)
                have b2744 := hb (x 5 4 && x 5 7)
                clear * - r2742 b2743 b2744 d2737
                omega
              have d2745 : (x 4 13).toNat = 0 := by
                have r2746 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2747 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                have e2748 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                have b2749 := hb (x 2 3)
                have b2750 := hb (x 3 2)
                have b2751 := hb (x 4 13)
                have b2752 := hb (x 5 12)
                clear * - r2746 e2747 e2748 b2749 b2750 b2751 b2752 d2725 d2655
                omega
              have d2753 : (x 4 7 && x 4 13).toNat = 0 := by
                have r2754 := hand2 (x 4 7) (x 4 13)
                have b2755 := hb (x 4 13)
                have b2756 := hb (x 4 7 && x 4 13)
                clear * - r2754 b2755 b2756 d2745
                omega
              have d2757 : (x 4 5).toNat = 0 := by
                have r2758 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
                have b2759 := hb (x 4 5)
                have b2760 := hb (x 4 13)
                clear * - r2758 b2759 b2760 d2745
                omega
              have d2761 : (x 2 3).toNat = 0 := by
                have r2762 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2763 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                have e2764 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                have b2765 := hb (x 2 3)
                have b2766 := hb (x 3 2)
                have b2767 := hb (x 4 13)
                have b2768 := hb (x 5 12)
                clear * - r2762 e2763 e2764 b2765 b2766 b2767 b2768 d2725 d2745 d2655
                omega
              have d2769 : (x 2 3 && x 2 8).toNat = 0 := by
                have r2770 := hand1 (x 2 3) (x 2 8)
                have b2771 := hb (x 2 3)
                have b2772 := hb (x 2 3 && x 2 8)
                clear * - r2770 b2771 b2772 d2761
                omega
              have d2773 : (x 4 7 && x 4 14).toNat = 0 := by
                have r2774 := hand2 (x 4 7) (x 4 14)
                have b2775 := hb (x 4 14)
                have b2776 := hb (x 4 7 && x 4 14)
                clear * - r2774 b2775 b2776 d2647
                omega
              have d2777 : (x 4 6).toNat = 0 := by
                have r2778 : (x 4 6).toNat ≤ (x 4 14).toNat := himp _ _ (hp6 4)
                have b2779 := hb (x 4 6)
                have b2780 := hb (x 4 14)
                clear * - r2778 b2779 b2780 d2647
                omega
              have d2781 : (x 4 1 && x 4 6).toNat = 0 := by
                have r2782 := hand2 (x 4 1) (x 4 6)
                have b2783 := hb (x 4 6)
                have b2784 := hb (x 4 1 && x 4 6)
                clear * - r2782 b2783 b2784 d2777
                omega
              have d2785 : (x (-4) 3).toNat = 0 := by
                have r2786 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2787 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                have e2788 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                have b2789 := hb (x (-4) 3)
                have b2790 := hb (x (-3) 2)
                have b2791 := hb (x (-2) 13)
                have b2792 := hb (x (-1) 12)
                clear * - r2786 e2787 e2788 b2789 b2790 b2791 b2792 d2544 d2540 d2507
                omega
              have d2793 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
                have r2794 := hand1 (x (-4) 3) (x (-4) 14)
                have b2795 := hb (x (-4) 3)
                have b2796 := hb (x (-4) 3 && x (-4) 14)
                clear * - r2794 b2795 b2796 d2785
                omega
              have d2797 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
                have r2798 := hand1 (x (-4) 3) (x (-4) 13)
                have b2799 := hb (x (-4) 3)
                have b2800 := hb (x (-4) 3 && x (-4) 13)
                clear * - r2798 b2799 b2800 d2785
                omega
              have d2801 : (x (-4) 11).toNat = 0 := by
                have r2802 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
                have b2803 := hb (x (-4) 3)
                have b2804 := hb (x (-4) 11)
                clear * - r2802 b2803 b2804 d2785
                omega
              have d2805 : (x (-4) 4 && x (-4) 11).toNat = 0 := by
                have r2806 := hand2 (x (-4) 4) (x (-4) 11)
                have b2807 := hb (x (-4) 11)
                have b2808 := hb (x (-4) 4 && x (-4) 11)
                clear * - r2806 b2807 b2808 d2801
                omega
              have d2809 : (x (-3) 12).toNat = 0 := by
                have r2810 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2811 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                have e2812 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                have b2813 := hb (x (-6) 3)
                have b2814 := hb (x (-5) 2)
                have b2815 := hb (x (-4) 13)
                have b2816 := hb (x (-3) 12)
                clear * - r2810 e2811 e2812 b2813 b2814 b2815 b2816 d2490
                omega
              have d2817 : (x (-5) 2).toNat = 0 := by
                have r2818 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2819 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                have e2820 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                have b2821 := hb (x (-6) 3)
                have b2822 := hb (x (-5) 2)
                have b2823 := hb (x (-4) 13)
                have b2824 := hb (x (-3) 12)
                clear * - r2818 e2819 e2820 b2821 b2822 b2823 b2824 d2809 d2490
                omega
              have d2825 : (x (-5) 10).toNat = 0 := by
                have r2826 : (x (-5) 10).toNat ≤ (x (-5) 2).toNat := himp _ _ (hp10 (-5))
                have b2827 := hb (x (-5) 2)
                have b2828 := hb (x (-5) 10)
                clear * - r2826 b2827 b2828 d2817
                omega
              have d2829 : (x (-6) 3).toNat = 0 := by
                have r2830 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2831 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                have e2832 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                have b2833 := hb (x (-6) 3)
                have b2834 := hb (x (-5) 2)
                have b2835 := hb (x (-4) 13)
                have b2836 := hb (x (-3) 12)
                clear * - r2830 e2831 e2832 b2833 b2834 b2835 b2836 d2809 d2490 d2817
                omega
              have d2837 : (x (-6) 11).toNat = 0 := by
                have r2838 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
                have b2839 := hb (x (-6) 3)
                have b2840 := hb (x (-6) 11)
                clear * - r2838 b2839 b2840 d2829
                omega
              have d2841 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
                have r2842 := hand1 (x (-5) 1) (x (-5) 12)
                have b2843 := hb (x (-5) 1)
                have b2844 := hb (x (-5) 1 && x (-5) 12)
                clear * - r2842 b2843 b2844 d2482
                omega
              have d2845 : (x (-8) 4).toNat = 1 := by
                have r2846 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b2847 := hb (x (-8) 4)
                have b2848 := hb (x (-4) 11)
                have b2849 := hb (x (-5) 1 && x (-5) 12)
                have b2850 := hb (x (-6) 2 && x (-6) 13)
                have b2851 := hb (x (-7) 3 && x (-7) 14)
                clear * - r2846 b2847 b2848 b2849 b2850 b2851 d2801 d2841 d2446 d2462
                omega
              have d2852 : (x (-8) 12).toNat = 1 := by
                have r2853 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
                have b2854 := hb (x (-8) 4)
                have b2855 := hb (x (-8) 12)
                clear * - r2853 b2854 b2855 d2845
                omega
              have d2856 : (x (-9) 13).toNat = 0 := by
                have r2857 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2858 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
                have e2859 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
                have b2860 := hb (x (-11) 3)
                have b2861 := hb (x (-10) 2)
                have b2862 := hb (x (-9) 13)
                have b2863 := hb (x (-8) 12)
                clear * - r2857 e2858 e2859 b2860 b2861 b2862 b2863 d2852
                omega
              have d2864 : (x (-9) 5).toNat = 0 := by
                have r2865 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
                have b2866 := hb (x (-9) 5)
                have b2867 := hb (x (-9) 13)
                clear * - r2865 b2866 b2867 d2856
                omega
              have d2868 : (x (-10) 2).toNat = 0 := by
                have r2869 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2870 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
                have e2871 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
                have b2872 := hb (x (-11) 3)
                have b2873 := hb (x (-10) 2)
                have b2874 := hb (x (-9) 13)
                have b2875 := hb (x (-8) 12)
                clear * - r2869 e2870 e2871 b2872 b2873 b2874 b2875 d2852 d2856
                omega
              have d2876 : (x (-10) 2 && x (-10) 13).toNat = 0 := by
                have r2877 := hand1 (x (-10) 2) (x (-10) 13)
                have b2878 := hb (x (-10) 2)
                have b2879 := hb (x (-10) 2 && x (-10) 13)
                clear * - r2877 b2878 b2879 d2868
                omega
              have d2880 : (x (-10) 2 && x (-10) 12).toNat = 0 := by
                have r2881 := hand1 (x (-10) 2) (x (-10) 12)
                have b2882 := hb (x (-10) 2)
                have b2883 := hb (x (-10) 2 && x (-10) 12)
                clear * - r2881 b2882 b2883 d2868
                omega
              have d2884 : (x (-10) 10).toNat = 0 := by
                have r2885 : (x (-10) 10).toNat ≤ (x (-10) 2).toNat := himp _ _ (hp10 (-10))
                have b2886 := hb (x (-10) 2)
                have b2887 := hb (x (-10) 10)
                clear * - r2885 b2886 b2887 d2868
                omega
              have d2888 : (x (-11) 3).toNat = 0 := by
                have r2889 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2890 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
                have e2891 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
                have b2892 := hb (x (-11) 3)
                have b2893 := hb (x (-10) 2)
                have b2894 := hb (x (-9) 13)
                have b2895 := hb (x (-8) 12)
                clear * - r2889 e2890 e2891 b2892 b2893 b2894 b2895 d2852 d2856 d2868
                omega
              have d2896 : (x (-11) 3 && x (-11) 14).toNat = 0 := by
                have r2897 := hand1 (x (-11) 3) (x (-11) 14)
                have b2898 := hb (x (-11) 3)
                have b2899 := hb (x (-11) 3 && x (-11) 14)
                clear * - r2897 b2898 b2899 d2888
                omega
              have d2900 : (x (-11) 3 && x (-11) 13).toNat = 0 := by
                have r2901 := hand1 (x (-11) 3) (x (-11) 13)
                have b2902 := hb (x (-11) 3)
                have b2903 := hb (x (-11) 3 && x (-11) 13)
                clear * - r2901 b2902 b2903 d2888
                omega
              have d2904 : (x (-11) 11).toNat = 0 := by
                have r2905 : (x (-11) 11).toNat ≤ (x (-11) 3).toNat := himp _ _ (hp11 (-11))
                have b2906 := hb (x (-11) 3)
                have b2907 := hb (x (-11) 11)
                clear * - r2905 b2906 b2907 d2888
                omega
              have d2908 : (x (-5) 9).toNat = 0 := by
                have r2909 : (x (-5) 9).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp9 (-5))
                have b2910 := hb (x (-5) 1)
                have b2911 := hb (x (-5) 9)
                clear * - r2909 b2910 b2911 d2482
                omega
              have d2912 : (x (-5) 9 && x (-5) 14).toNat = 0 := by
                have r2913 := hand1 (x (-5) 9) (x (-5) 14)
                have b2914 := hb (x (-5) 9)
                have b2915 := hb (x (-5) 9 && x (-5) 14)
                clear * - r2913 b2914 b2915 d2908
                omega
              have d2916 : (x 3 8).toNat = 0 := by
                have r2917 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2918 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
                have e2919 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
                have e2920 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
                have e2921 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
                have e2922 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
                have e2923 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
                have b2924 := hb (x (-4) 7)
                have b2925 := hb (x (-3) 6)
                have b2926 := hb (x (-2) 5)
                have b2927 := hb (x (-1) 4)
                have b2928 := hb (x 0 11)
                have b2929 := hb (x 1 10)
                have b2930 := hb (x 2 9)
                have b2931 := hb (x 3 8)
                clear * - r2917 e2918 e2919 e2920 e2921 e2922 e2923 b2924 b2925 b2926 b2927 b2928 b2929 b2930 b2931 d2721 g12 g8 d2552 d2532 d2503
                omega
              have d2932 : (x 3 8 && x 3 14).toNat = 0 := by
                have r2933 := hand1 (x 3 8) (x 3 14)
                have b2934 := hb (x 3 8)
                have b2935 := hb (x 3 8 && x 3 14)
                clear * - r2933 b2934 b2935 d2916
                omega
              have d2936 : (x (-6) 6).toNat = 0 := by
                have r2937 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2938 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                have e2939 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                have e2940 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                have e2941 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                have e2942 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                have e2943 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                have b2944 := hb (x (-7) 7)
                have b2945 := hb (x (-6) 6)
                have b2946 := hb (x (-5) 5)
                have b2947 := hb (x (-4) 4)
                have b2948 := hb (x (-3) 11)
                have b2949 := hb (x (-2) 10)
                have b2950 := hb (x (-1) 9)
                have b2951 := hb (x 0 8)
                clear * - r2937 e2938 e2939 e2940 e2941 e2942 e2943 b2944 b2945 b2946 b2947 b2948 b2949 b2950 b2951 f2282 d2058 d2379 d2403 d2407 d2430
                omega
              have d2952 : (x (-6) 6 && x (-6) 13).toNat = 0 := by
                have r2953 := hand1 (x (-6) 6) (x (-6) 13)
                have b2954 := hb (x (-6) 6)
                have b2955 := hb (x (-6) 6 && x (-6) 13)
                clear * - r2953 b2954 b2955 d2936
                omega
              have d2956 : (x (-7) 7).toNat = 0 := by
                have r2957 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2958 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                have e2959 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                have e2960 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                have e2961 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                have e2962 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                have e2963 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                have b2964 := hb (x (-7) 7)
                have b2965 := hb (x (-6) 6)
                have b2966 := hb (x (-5) 5)
                have b2967 := hb (x (-4) 4)
                have b2968 := hb (x (-3) 11)
                have b2969 := hb (x (-2) 10)
                have b2970 := hb (x (-1) 9)
                have b2971 := hb (x 0 8)
                clear * - r2957 e2958 e2959 e2960 e2961 e2962 e2963 b2964 b2965 b2966 b2967 b2968 b2969 b2970 b2971 f2282 d2058 d2379 d2403 d2407 d2430 d2936
                omega
              have d2972 : (x (-7) 7 && x (-7) 14).toNat = 0 := by
                have r2973 := hand1 (x (-7) 7) (x (-7) 14)
                have b2974 := hb (x (-7) 7)
                have b2975 := hb (x (-7) 7 && x (-7) 14)
                clear * - r2973 b2974 b2975 d2956
                omega
              have d2976 : (x (-4) 8).toNat = 0 := by
                have r2977 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2978 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
                have e2979 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
                have e2980 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
                have e2981 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
                have e2982 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
                have e2983 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
                have b2984 := hb (x (-11) 7)
                have b2985 := hb (x (-10) 6)
                have b2986 := hb (x (-9) 5)
                have b2987 := hb (x (-8) 4)
                have b2988 := hb (x (-7) 11)
                have b2989 := hb (x (-6) 10)
                have b2990 := hb (x (-5) 9)
                have b2991 := hb (x (-4) 8)
                clear * - r2977 e2978 e2979 e2980 e2981 e2982 e2983 b2984 b2985 b2986 b2987 b2988 b2989 b2990 b2991 d2908 d2450 d2466 d2845 d2864
                omega
              have d2992 : (x (-4) 8 && x (-4) 13).toNat = 0 := by
                have r2993 := hand1 (x (-4) 8) (x (-4) 13)
                have b2994 := hb (x (-4) 8)
                have b2995 := hb (x (-4) 8 && x (-4) 13)
                clear * - r2993 b2994 b2995 d2976
                omega
              have d2996 : (x (-4) 8 && x (-4) 12).toNat = 0 := by
                have r2997 := hand1 (x (-4) 8) (x (-4) 12)
                have b2998 := hb (x (-4) 8)
                have b2999 := hb (x (-4) 8 && x (-4) 12)
                clear * - r2997 b2998 b2999 d2976
                omega
              have d3000 : (x (-8) 8).toNat = 1 := by
                have r3001 : 1 ≤ (x 0 7).toNat + (x (-1) 1 && x (-1) 8).toNat + (x (-2) 2 && x (-2) 9).toNat + (x (-3) 3 && x (-3) 10).toNat + (x (-4) 4 && x (-4) 11).toNat + (x (-5) 5 && x (-5) 12).toNat + (x (-6) 6 && x (-6) 13).toNat + (x (-7) 7 && x (-7) 14).toNat + (x (-8) 8).toNat := by have q := hcov7 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b3002 := hb (x (-8) 8)
                have b3003 := hb (x 0 7)
                have b3004 := hb (x (-1) 1 && x (-1) 8)
                have b3005 := hb (x (-2) 2 && x (-2) 9)
                have b3006 := hb (x (-3) 3 && x (-3) 10)
                have b3007 := hb (x (-4) 4 && x (-4) 11)
                have b3008 := hb (x (-5) 5 && x (-5) 12)
                have b3009 := hb (x (-6) 6 && x (-6) 13)
                have b3010 := hb (x (-7) 7 && x (-7) 14)
                clear * - r3001 b3002 b3003 b3004 b3005 b3006 b3007 b3008 b3009 b3010 f2290 d2034 d2375 d2399 d2805 d2434 d2952 d2972
                omega
              have d3011 : (x (-9) 9).toNat = 0 := by
                have r3012 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3013 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
                have e3014 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
                have e3015 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
                have e3016 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
                have e3017 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
                have e3018 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
                have b3019 := hb (x (-15) 7)
                have b3020 := hb (x (-14) 6)
                have b3021 := hb (x (-13) 5)
                have b3022 := hb (x (-12) 4)
                have b3023 := hb (x (-11) 11)
                have b3024 := hb (x (-10) 10)
                have b3025 := hb (x (-9) 9)
                have b3026 := hb (x (-8) 8)
                clear * - r3012 e3013 e3014 e3015 e3016 e3017 e3018 b3019 b3020 b3021 b3022 b3023 b3024 b3025 b3026 d3000 d2884 d2904
                omega
              have d3027 : (x (-12) 4).toNat = 0 := by
                have r3028 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3029 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
                have e3030 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
                have e3031 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
                have e3032 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
                have e3033 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
                have e3034 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
                have b3035 := hb (x (-15) 7)
                have b3036 := hb (x (-14) 6)
                have b3037 := hb (x (-13) 5)
                have b3038 := hb (x (-12) 4)
                have b3039 := hb (x (-11) 11)
                have b3040 := hb (x (-10) 10)
                have b3041 := hb (x (-9) 9)
                have b3042 := hb (x (-8) 8)
                clear * - r3028 e3029 e3030 e3031 e3032 e3033 e3034 b3035 b3036 b3037 b3038 b3039 b3040 b3041 b3042 d3000 d3011 d2884 d2904
                omega
              have d3043 : (x (-12) 4 && x (-12) 14).toNat = 0 := by
                have r3044 := hand1 (x (-12) 4) (x (-12) 14)
                have b3045 := hb (x (-12) 4)
                have b3046 := hb (x (-12) 4 && x (-12) 14)
                clear * - r3044 b3045 b3046 d3027
                omega
              have d3047 : (x (-13) 5).toNat = 0 := by
                have r3048 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3049 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
                have e3050 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
                have e3051 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
                have e3052 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
                have e3053 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
                have e3054 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
                have b3055 := hb (x (-15) 7)
                have b3056 := hb (x (-14) 6)
                have b3057 := hb (x (-13) 5)
                have b3058 := hb (x (-12) 4)
                have b3059 := hb (x (-11) 11)
                have b3060 := hb (x (-10) 10)
                have b3061 := hb (x (-9) 9)
                have b3062 := hb (x (-8) 8)
                clear * - r3048 e3049 e3050 e3051 e3052 e3053 e3054 b3055 b3056 b3057 b3058 b3059 b3060 b3061 b3062 d3000 d3011 d2884 d2904 d3027
                omega
              have d3063 : (x 3 1 && x 3 6).toNat = 1 := by
                have r3064 : 1 ≤ (x 4 5).toNat + (x 3 1 && x 3 6).toNat + (x 2 2 && x 2 7).toNat + (x 1 3 && x 1 8).toNat + (x 0 4 && x 0 9).toNat + (x (-1) 5 && x (-1) 10).toNat + (x (-2) 6 && x (-2) 11).toNat + (x (-3) 7 && x (-3) 12).toNat + (x (-4) 8 && x (-4) 13).toNat + (x (-5) 9 && x (-5) 14).toNat + (x (-6) 10).toNat := by have q := hcov5 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b3065 := hb (x (-6) 10)
                have b3066 := hb (x 4 5)
                have b3067 := hb (x 3 1 && x 3 6)
                have b3068 := hb (x 2 2 && x 2 7)
                have b3069 := hb (x 1 3 && x 1 8)
                have b3070 := hb (x 0 4 && x 0 9)
                have b3071 := hb (x (-1) 5 && x (-1) 10)
                have b3072 := hb (x (-2) 6 && x (-2) 11)
                have b3073 := hb (x (-3) 7 && x (-3) 12)
                have b3074 := hb (x (-4) 8 && x (-4) 13)
                have b3075 := hb (x (-5) 9 && x (-5) 14)
                clear * - r3064 b3065 b3066 b3067 b3068 b3069 b3070 b3071 b3072 b3073 b3074 b3075 d2757 d2697 d2713 g18 g19 g20 d2271 d2992 d2912 d2450
                omega
              have d3076 : (x 3 6).toNat = 1 := by
                have r3077 := hand2 (x 3 1) (x 3 6)
                have b3078 := hb (x 3 6)
                have b3079 := hb (x 3 1 && x 3 6)
                clear * - r3077 b3078 b3079 d3063
                omega
              have d3080 : (x 9 8).toNat = 0 := by
                have r3081 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3082 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                have e3083 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                have e3084 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                have e3085 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                have e3086 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                have e3087 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                have b3088 := hb (x 2 7)
                have b3089 := hb (x 3 6)
                have b3090 := hb (x 4 5)
                have b3091 := hb (x 5 4)
                have b3092 := hb (x 6 11)
                have b3093 := hb (x 7 10)
                have b3094 := hb (x 8 9)
                have b3095 := hb (x 9 8)
                clear * - r3081 e3082 e3083 e3084 e3085 e3086 e3087 b3088 b3089 b3090 b3091 b3092 b3093 b3094 b3095 d2737 d2757 d3076
                omega
              have d3096 : (x 9 2 && x 9 8).toNat = 0 := by
                have r3097 := hand2 (x 9 2) (x 9 8)
                have b3098 := hb (x 9 8)
                have b3099 := hb (x 9 2 && x 9 8)
                clear * - r3097 b3098 b3099 d3080
                omega
              have d3100 : (x 8 9).toNat = 0 := by
                have r3101 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3102 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                have e3103 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                have e3104 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                have e3105 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                have e3106 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                have e3107 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                have b3108 := hb (x 2 7)
                have b3109 := hb (x 3 6)
                have b3110 := hb (x 4 5)
                have b3111 := hb (x 5 4)
                have b3112 := hb (x 6 11)
                have b3113 := hb (x 7 10)
                have b3114 := hb (x 8 9)
                have b3115 := hb (x 9 8)
                clear * - r3101 e3102 e3103 e3104 e3105 e3106 e3107 b3108 b3109 b3110 b3111 b3112 b3113 b3114 b3115 d3080 d2737 d2757 d3076
                omega
              have d3116 : (x 8 3 && x 8 9).toNat = 0 := by
                have r3117 := hand2 (x 8 3) (x 8 9)
                have b3118 := hb (x 8 9)
                have b3119 := hb (x 8 3 && x 8 9)
                clear * - r3117 b3118 b3119 d3100
                omega
              have d3120 : (x 7 10).toNat = 0 := by
                have r3121 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3122 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                have e3123 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                have e3124 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                have e3125 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                have e3126 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                have e3127 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                have b3128 := hb (x 2 7)
                have b3129 := hb (x 3 6)
                have b3130 := hb (x 4 5)
                have b3131 := hb (x 5 4)
                have b3132 := hb (x 6 11)
                have b3133 := hb (x 7 10)
                have b3134 := hb (x 8 9)
                have b3135 := hb (x 9 8)
                clear * - r3121 e3122 e3123 e3124 e3125 e3126 e3127 b3128 b3129 b3130 b3131 b3132 b3133 b3134 b3135 d3080 d3100 d2737 d2757 d3076
                omega
              have d3136 : (x 7 4 && x 7 10).toNat = 0 := by
                have r3137 := hand2 (x 7 4) (x 7 10)
                have b3138 := hb (x 7 10)
                have b3139 := hb (x 7 4 && x 7 10)
                clear * - r3137 b3138 b3139 d3120
                omega
              have d3140 : (x 6 11).toNat = 0 := by
                have r3141 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3142 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                have e3143 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                have e3144 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                have e3145 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                have e3146 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                have e3147 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                have b3148 := hb (x 2 7)
                have b3149 := hb (x 3 6)
                have b3150 := hb (x 4 5)
                have b3151 := hb (x 5 4)
                have b3152 := hb (x 6 11)
                have b3153 := hb (x 7 10)
                have b3154 := hb (x 8 9)
                have b3155 := hb (x 9 8)
                clear * - r3141 e3142 e3143 e3144 e3145 e3146 e3147 b3148 b3149 b3150 b3151 b3152 b3153 b3154 b3155 d3080 d3100 d3120 d2737 d2757 d3076
                omega
              have d3156 : (x 6 5 && x 6 11).toNat = 0 := by
                have r3157 := hand2 (x 6 5) (x 6 11)
                have b3158 := hb (x 6 11)
                have b3159 := hb (x 6 5 && x 6 11)
                clear * - r3157 b3158 b3159 d3140
                omega
              have d3160 : (x 3 5).toNat = 1 := by
                have r3161 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3162 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
                have e3163 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
                have b3164 := hb (x (-7) 11)
                have b3165 := hb (x (-6) 10)
                have b3166 := hb (x 3 5)
                have b3167 := hb (x 4 4)
                have b3168 := hb (x 2 2 && x 2 6)
                have b3169 := hb (x 1 3 && x 1 7)
                have b3170 := hb (x 0 4 && x 0 8)
                have b3171 := hb (x (-1) 5 && x (-1) 9)
                have b3172 := hb (x (-2) 6 && x (-2) 10)
                have b3173 := hb (x (-3) 7 && x (-3) 11)
                have b3174 := hb (x (-4) 8 && x (-4) 12)
                have b3175 := hb (x (-5) 9 && x (-5) 13)
                clear * - r3161 e3162 e3163 b3164 b3165 b3166 b3167 b3168 b3169 b3170 b3171 b3172 b3173 b3174 b3175 d2685 d2701 d2717 g17 d2054 d2383 d2275 d2996 d2426 d2450 d2466
                omega
              have d3176 : (x 8 8).toNat = 0 := by
                have r3177 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3178 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e3179 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e3180 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e3181 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e3182 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e3183 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b3184 := hb (x 1 7)
                have b3185 := hb (x 2 6)
                have b3186 := hb (x 3 5)
                have b3187 := hb (x 4 4)
                have b3188 := hb (x 5 11)
                have b3189 := hb (x 6 10)
                have b3190 := hb (x 7 9)
                have b3191 := hb (x 8 8)
                clear * - r3177 e3178 e3179 e3180 e3181 e3182 e3183 b3184 b3185 b3186 b3187 b3188 b3189 b3190 b3191 d2685 d3160
                omega
              have d3192 : (x 7 9).toNat = 0 := by
                have r3193 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3194 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e3195 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e3196 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e3197 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e3198 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e3199 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b3200 := hb (x 1 7)
                have b3201 := hb (x 2 6)
                have b3202 := hb (x 3 5)
                have b3203 := hb (x 4 4)
                have b3204 := hb (x 5 11)
                have b3205 := hb (x 6 10)
                have b3206 := hb (x 7 9)
                have b3207 := hb (x 8 8)
                clear * - r3193 e3194 e3195 e3196 e3197 e3198 e3199 b3200 b3201 b3202 b3203 b3204 b3205 b3206 b3207 d3176 d2685 d3160
                omega
              have d3208 : (x 6 10).toNat = 0 := by
                have r3209 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3210 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e3211 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e3212 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e3213 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e3214 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e3215 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b3216 := hb (x 1 7)
                have b3217 := hb (x 2 6)
                have b3218 := hb (x 3 5)
                have b3219 := hb (x 4 4)
                have b3220 := hb (x 5 11)
                have b3221 := hb (x 6 10)
                have b3222 := hb (x 7 9)
                have b3223 := hb (x 8 8)
                clear * - r3209 e3210 e3211 e3212 e3213 e3214 e3215 b3216 b3217 b3218 b3219 b3220 b3221 b3222 b3223 d3176 d3192 d2685 d3160
                omega
              have d3224 : (x 5 11).toNat = 0 := by
                have r3225 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3226 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e3227 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e3228 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e3229 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e3230 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e3231 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b3232 := hb (x 1 7)
                have b3233 := hb (x 2 6)
                have b3234 := hb (x 3 5)
                have b3235 := hb (x 4 4)
                have b3236 := hb (x 5 11)
                have b3237 := hb (x 6 10)
                have b3238 := hb (x 7 9)
                have b3239 := hb (x 8 8)
                clear * - r3225 e3226 e3227 e3228 e3229 e3230 e3231 b3232 b3233 b3234 b3235 b3236 b3237 b3238 b3239 d3176 d3192 d3208 d2685 d3160
                omega
              have d3240 : (x 2 6).toNat = 0 := by
                have r3241 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3242 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e3243 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e3244 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e3245 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e3246 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e3247 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b3248 := hb (x 1 7)
                have b3249 := hb (x 2 6)
                have b3250 := hb (x 3 5)
                have b3251 := hb (x 4 4)
                have b3252 := hb (x 5 11)
                have b3253 := hb (x 6 10)
                have b3254 := hb (x 7 9)
                have b3255 := hb (x 8 8)
                clear * - r3241 e3242 e3243 e3244 e3245 e3246 e3247 b3248 b3249 b3250 b3251 b3252 b3253 b3254 b3255 d3176 d3192 d3208 d3224 d2685 d3160
                omega
              have d3256 : (x 1 7).toNat = 0 := by
                have r3257 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3258 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e3259 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e3260 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e3261 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e3262 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e3263 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b3264 := hb (x 1 7)
                have b3265 := hb (x 2 6)
                have b3266 := hb (x 3 5)
                have b3267 := hb (x 4 4)
                have b3268 := hb (x 5 11)
                have b3269 := hb (x 6 10)
                have b3270 := hb (x 7 9)
                have b3271 := hb (x 8 8)
                clear * - r3257 e3258 e3259 e3260 e3261 e3262 e3263 b3264 b3265 b3266 b3267 b3268 b3269 b3270 b3271 d3176 d3192 d3208 d3224 d2685 d3160 d3240
                omega
              have d3272 : (x (-10) 14).toNat = 0 := by
                have r3273 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b3274 := hb (x (-10) 14)
                have b3275 := hb (x (-9) 13)
                have b3276 := hb (x (-8) 12)
                have b3277 := hb (x (-7) 11)
                have b3278 := hb (x (-6) 10)
                have b3279 := hb (x (-5) 9)
                have b3280 := hb (x (-4) 8)
                have b3281 := hb (x (-3) 7)
                have b3282 := hb (x (-2) 6)
                have b3283 := hb (x (-1) 5)
                have b3284 := hb (x 0 4)
                have b3285 := hb (x 1 3)
                have b3286 := hb (x 2 2)
                have b3287 := hb (x 3 1)
                clear * - r3273 b3274 b3275 b3276 b3277 b3278 b3279 b3280 b3281 b3282 b3283 b3284 b3285 b3286 b3287 d2643 d2689 d2705 g6 d2046 d2118 d2255 d2976 d2908 d2450 d2466 d2852 d2856
                omega
              have d3288 : (x (-10) 1 && x (-10) 14).toNat = 0 := by
                have r3289 := hand2 (x (-10) 1) (x (-10) 14)
                have b3290 := hb (x (-10) 14)
                have b3291 := hb (x (-10) 1 && x (-10) 14)
                clear * - r3289 b3290 b3291 d3272
                omega
              have d3292 : (x (-11) 2).toNat = 1 := by
                have r3293 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b3294 := hb (x (-11) 2)
                have b3295 := hb (x (-9) 13)
                have b3296 := hb (x (-10) 1 && x (-10) 14)
                clear * - r3293 b3294 b3295 b3296 d2856 d3288
                omega
              have d3297 : (x (-9) 12).toNat = 0 := by
                have r3298 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3299 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
                have e3300 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
                have b3301 := hb (x (-12) 3)
                have b3302 := hb (x (-11) 2)
                have b3303 := hb (x (-10) 13)
                have b3304 := hb (x (-9) 12)
                clear * - r3298 e3299 e3300 b3301 b3302 b3303 b3304 d3292
                omega
              have d3305 : (x (-9) 1 && x (-9) 12).toNat = 0 := by
                have r3306 := hand2 (x (-9) 1) (x (-9) 12)
                have b3307 := hb (x (-9) 12)
                have b3308 := hb (x (-9) 1 && x (-9) 12)
                clear * - r3306 b3307 b3308 d3297
                omega
              have d3309 : (x (-8) 11).toNat = 1 := by
                have r3310 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := by have q := hcov11 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b3311 := hb (x (-12) 4)
                have b3312 := hb (x (-8) 11)
                have b3313 := hb (x (-9) 1 && x (-9) 12)
                have b3314 := hb (x (-10) 2 && x (-10) 13)
                have b3315 := hb (x (-11) 3 && x (-11) 14)
                clear * - r3310 b3311 b3312 b3313 b3314 b3315 d3305 d2876 d2896 d3027
                omega
              have d3316 : (x (-8) 3).toNat = 1 := by
                have r3317 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
                have b3318 := hb (x (-8) 3)
                have b3319 := hb (x (-8) 11)
                clear * - r3317 b3318 b3319 d3309
                omega
              have d3320 : (x (-5) 12).toNat = 0 := by
                have r3321 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3322 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                have e3323 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                have b3324 := hb (x (-8) 3)
                have b3325 := hb (x (-7) 2)
                have b3326 := hb (x (-6) 13)
                have b3327 := hb (x (-5) 12)
                clear * - r3321 e3322 e3323 b3324 b3325 b3326 b3327 d3316
                omega
              have d3328 : (x (-5) 4).toNat = 0 := by
                have r3329 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
                have b3330 := hb (x (-5) 4)
                have b3331 := hb (x (-5) 12)
                clear * - r3329 b3330 b3331 d3320
                omega
              have d3332 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
                have r3333 := hand1 (x (-5) 4) (x (-5) 14)
                have b3334 := hb (x (-5) 4)
                have b3335 := hb (x (-5) 4 && x (-5) 14)
                clear * - r3333 b3334 b3335 d3328
                omega
              have d3336 : (x (-6) 5).toNat = 1 := by
                have r3337 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b3338 := hb (x (-6) 5)
                have b3339 := hb (x (-1) 10)
                have b3340 := hb (x (-2) 1 && x (-2) 11)
                have b3341 := hb (x (-3) 2 && x (-3) 12)
                have b3342 := hb (x (-4) 3 && x (-4) 13)
                have b3343 := hb (x (-5) 4 && x (-5) 14)
                clear * - r3337 b3338 b3339 b3340 b3341 b3342 b3343 g3 g39 d2511 d2797 d3332
                omega
              have d3344 : (x (-6) 13).toNat = 1 := by
                have r3345 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
                have b3346 := hb (x (-6) 5)
                have b3347 := hb (x (-6) 13)
                clear * - r3345 b3346 b3347 d3336
                omega
              have d3348 : (x (-6) 1).toNat = 1 := by
                have r3349 : (x (-6) 13).toNat ≤ (x (-6) 1).toNat := himp _ _ (hp13 (-6))
                have b3350 := hb (x (-6) 1)
                have b3351 := hb (x (-6) 13)
                clear * - r3349 b3350 b3351 d3344
                omega
              have d3352 : (x (-5) 14).toNat = 0 := by
                have r3353 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b3354 := hb (x (-6) 1)
                have b3355 := hb (x (-5) 14)
                clear * - r3353 b3354 b3355 d3348
                omega
              have d3356 : (x (-5) 3 && x (-5) 14).toNat = 0 := by
                have r3357 := hand2 (x (-5) 3) (x (-5) 14)
                have b3358 := hb (x (-5) 14)
                have b3359 := hb (x (-5) 3 && x (-5) 14)
                clear * - r3357 b3358 b3359 d3352
                omega
              have d3360 : (x (-2) 1 && x (-2) 12).toNat = 1 := by
                have r3361 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b3362 := hb (x (-5) 4)
                have b3363 := hb (x (-1) 11)
                have b3364 := hb (x (-2) 1 && x (-2) 12)
                have b3365 := hb (x (-3) 2 && x (-3) 13)
                have b3366 := hb (x (-4) 3 && x (-4) 14)
                clear * - r3361 b3362 b3363 b3364 b3365 b3366 d2114 d2143 d2793 d3328
                omega
              have d3367 : (x (-2) 12).toNat = 1 := by
                have r3368 := hand2 (x (-2) 1) (x (-2) 12)
                have b3369 := hb (x (-2) 12)
                have b3370 := hb (x (-2) 1 && x (-2) 12)
                clear * - r3368 b3369 b3370 d3360
                omega
              have d3371 : (x (-4) 2).toNat = 0 := by
                have r3372 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3373 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                have e3374 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                have b3375 := hb (x (-5) 3)
                have b3376 := hb (x (-4) 2)
                have b3377 := hb (x (-3) 13)
                have b3378 := hb (x (-2) 12)
                clear * - r3372 e3373 e3374 b3375 b3376 b3377 b3378 d3367 d2139
                omega
              have d3379 : (x (-4) 2 && x (-4) 13).toNat = 0 := by
                have r3380 := hand1 (x (-4) 2) (x (-4) 13)
                have b3381 := hb (x (-4) 2)
                have b3382 := hb (x (-4) 2 && x (-4) 13)
                clear * - r3380 b3381 b3382 d3371
                omega
              have d3383 : (x (-6) 4).toNat = 1 := by
                have r3384 : 1 ≤ (x (-2) 11).toNat + (x (-3) 1 && x (-3) 12).toNat + (x (-4) 2 && x (-4) 13).toNat + (x (-5) 3 && x (-5) 14).toNat + (x (-6) 4).toNat := by have q := hcov11 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b3385 := hb (x (-6) 4)
                have b3386 := hb (x (-2) 11)
                have b3387 := hb (x (-3) 1 && x (-3) 12)
                have b3388 := hb (x (-4) 2 && x (-4) 13)
                have b3389 := hb (x (-5) 3 && x (-5) 14)
                clear * - r3384 b3385 b3386 b3387 b3388 b3389 g1 d2135 d3379 d3356
                omega
              have d3390 : (x (-6) 12).toNat = 1 := by
                have r3391 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
                have b3392 := hb (x (-6) 4)
                have b3393 := hb (x (-6) 12)
                clear * - r3391 b3392 b3393 d3383
                omega
              have d3394 : (x (-7) 13).toNat = 0 := by
                have r3395 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3396 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
                have e3397 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
                have b3398 := hb (x (-9) 3)
                have b3399 := hb (x (-8) 2)
                have b3400 := hb (x (-7) 13)
                have b3401 := hb (x (-6) 12)
                clear * - r3395 e3396 e3397 b3398 b3399 b3400 b3401 d3390
                omega
              have d3402 : (x (-8) 2).toNat = 0 := by
                have r3403 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3404 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
                have e3405 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
                have b3406 := hb (x (-9) 3)
                have b3407 := hb (x (-8) 2)
                have b3408 := hb (x (-7) 13)
                have b3409 := hb (x (-6) 12)
                clear * - r3403 e3404 e3405 b3406 b3407 b3408 b3409 d3390 d3394
                omega
              have d3410 : (x (-8) 10).toNat = 0 := by
                have r3411 : (x (-8) 10).toNat ≤ (x (-8) 2).toNat := himp _ _ (hp10 (-8))
                have b3412 := hb (x (-8) 2)
                have b3413 := hb (x (-8) 10)
                clear * - r3411 b3412 b3413 d3402
                omega
              have d3414 : (x (-9) 1 && x (-9) 11).toNat = 1 := by
                have r3415 : 1 ≤ (x (-8) 10).toNat + (x (-9) 1 && x (-9) 11).toNat + (x (-10) 2 && x (-10) 12).toNat + (x (-11) 3 && x (-11) 13).toNat + (x (-12) 4 && x (-12) 14).toNat + (x (-13) 5).toNat := by have q := hcov10 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b3416 := hb (x (-13) 5)
                have b3417 := hb (x (-8) 10)
                have b3418 := hb (x (-9) 1 && x (-9) 11)
                have b3419 := hb (x (-10) 2 && x (-10) 12)
                have b3420 := hb (x (-11) 3 && x (-11) 13)
                have b3421 := hb (x (-12) 4 && x (-12) 14)
                clear * - r3415 b3416 b3417 b3418 b3419 b3420 b3421 d3410 d2880 d2900 d3043 d3047
                omega
              have d3422 : (x (-9) 1).toNat = 1 := by
                have r3423 := hand1 (x (-9) 1) (x (-9) 11)
                have b3424 := hb (x (-9) 1)
                have b3425 := hb (x (-9) 1 && x (-9) 11)
                clear * - r3423 b3424 b3425 d3414
                omega
              have d3426 : (x (-8) 14).toNat = 0 := by
                have r3427 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b3428 := hb (x (-9) 1)
                have b3429 := hb (x (-8) 14)
                clear * - r3427 b3428 b3429 d3422
                omega
              have d3430 : (x (-8) 1 && x (-8) 14).toNat = 0 := by
                have r3431 := hand2 (x (-8) 1) (x (-8) 14)
                have b3432 := hb (x (-8) 14)
                have b3433 := hb (x (-8) 1 && x (-8) 14)
                clear * - r3431 b3432 b3433 d3426
                omega
              have d3434 : (x (-9) 2).toNat = 1 := by
                have r3435 : 1 ≤ (x (-7) 13).toNat + (x (-8) 1 && x (-8) 14).toNat + (x (-9) 2).toNat := by have q := hcov13 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b3436 := hb (x (-9) 2)
                have b3437 := hb (x (-7) 13)
                have b3438 := hb (x (-8) 1 && x (-8) 14)
                clear * - r3435 b3436 b3437 b3438 d3394 d3430
                omega
              have d3439 : (x (-9) 14).toNat = 1 := by
                have r3440 : (x (-9) 2).toNat ≤ (x (-9) 14).toNat := himp _ _ (hp2 (-9))
                have b3441 := hb (x (-9) 2)
                have b3442 := hb (x (-9) 14)
                clear * - r3440 b3441 b3442 d3434
                omega
              have d3443 : (x 4 1).toNat = 0 := by
                have r3444 : (x 4 1).toNat + (x 3 2).toNat + (x 2 3).toNat + (x 1 4).toNat + (x 0 5).toNat + (x (-1) 6).toNat + (x (-2) 7).toNat + (x (-3) 8).toNat + (x (-4) 9).toNat + (x (-5) 10).toNat + (x (-6) 11).toNat + (x (-7) 12).toNat + (x (-8) 13).toNat + (x (-9) 14).toNat = 3 := by have q := hcount 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b3445 := hb (x (-9) 14)
                have b3446 := hb (x (-8) 13)
                have b3447 := hb (x (-7) 12)
                have b3448 := hb (x (-6) 11)
                have b3449 := hb (x (-5) 10)
                have b3450 := hb (x (-4) 9)
                have b3451 := hb (x (-3) 8)
                have b3452 := hb (x (-2) 7)
                have b3453 := hb (x (-1) 6)
                have b3454 := hb (x 0 5)
                have b3455 := hb (x 1 4)
                have b3456 := hb (x 2 3)
                have b3457 := hb (x 3 2)
                have b3458 := hb (x 4 1)
                clear * - r3444 b3445 b3446 b3447 b3448 b3449 b3450 b3451 b3452 b3453 b3454 b3455 b3456 b3457 b3458 d2655 d2761 g10 g7 g2 g0 d2825 d2837 d3439
                omega
              have d3459 : (x (-3) 8).toNat = 0 := by
                have r3460 : (x 4 1).toNat + (x 3 2).toNat + (x 2 3).toNat + (x 1 4).toNat + (x 0 5).toNat + (x (-1) 6).toNat + (x (-2) 7).toNat + (x (-3) 8).toNat + (x (-4) 9).toNat + (x (-5) 10).toNat + (x (-6) 11).toNat + (x (-7) 12).toNat + (x (-8) 13).toNat + (x (-9) 14).toNat = 3 := by have q := hcount 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b3461 := hb (x (-9) 14)
                have b3462 := hb (x (-8) 13)
                have b3463 := hb (x (-7) 12)
                have b3464 := hb (x (-6) 11)
                have b3465 := hb (x (-5) 10)
                have b3466 := hb (x (-4) 9)
                have b3467 := hb (x (-3) 8)
                have b3468 := hb (x (-2) 7)
                have b3469 := hb (x (-1) 6)
                have b3470 := hb (x 0 5)
                have b3471 := hb (x 1 4)
                have b3472 := hb (x 2 3)
                have b3473 := hb (x 3 2)
                have b3474 := hb (x 4 1)
                clear * - r3460 b3461 b3462 b3463 b3464 b3465 b3466 b3467 b3468 b3469 b3470 b3471 b3472 b3473 b3474 d3443 d2655 d2761 g10 g7 g2 g0 d2825 d2837 d3439
                omega
              have d3475 : (x (-4) 9).toNat = 0 := by
                have r3476 : (x 4 1).toNat + (x 3 2).toNat + (x 2 3).toNat + (x 1 4).toNat + (x 0 5).toNat + (x (-1) 6).toNat + (x (-2) 7).toNat + (x (-3) 8).toNat + (x (-4) 9).toNat + (x (-5) 10).toNat + (x (-6) 11).toNat + (x (-7) 12).toNat + (x (-8) 13).toNat + (x (-9) 14).toNat = 3 := by have q := hcount 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b3477 := hb (x (-9) 14)
                have b3478 := hb (x (-8) 13)
                have b3479 := hb (x (-7) 12)
                have b3480 := hb (x (-6) 11)
                have b3481 := hb (x (-5) 10)
                have b3482 := hb (x (-4) 9)
                have b3483 := hb (x (-3) 8)
                have b3484 := hb (x (-2) 7)
                have b3485 := hb (x (-1) 6)
                have b3486 := hb (x 0 5)
                have b3487 := hb (x 1 4)
                have b3488 := hb (x 2 3)
                have b3489 := hb (x 3 2)
                have b3490 := hb (x 4 1)
                clear * - r3476 b3477 b3478 b3479 b3480 b3481 b3482 b3483 b3484 b3485 b3486 b3487 b3488 b3489 b3490 d3443 d2655 d2761 g10 g7 g2 g0 d3459 d2825 d2837 d3439
                omega
              have d3491 : (x (-4) 9 && x (-4) 14).toNat = 0 := by
                have r3492 := hand1 (x (-4) 9) (x (-4) 14)
                have b3493 := hb (x (-4) 9)
                have b3494 := hb (x (-4) 9 && x (-4) 14)
                clear * - r3492 b3493 b3494 d3475
                omega
              have d3495 : (x 3 2 && x 3 7).toNat = 1 := by
                have r3496 : 1 ≤ (x 5 5).toNat + (x 4 1 && x 4 6).toNat + (x 3 2 && x 3 7).toNat + (x 2 3 && x 2 8).toNat + (x 1 4 && x 1 9).toNat + (x 0 5 && x 0 10).toNat + (x (-1) 6 && x (-1) 11).toNat + (x (-2) 7 && x (-2) 12).toNat + (x (-3) 8 && x (-3) 13).toNat + (x (-4) 9 && x (-4) 14).toNat + (x (-5) 10).toNat := by have q := hcov5 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b3497 := hb (x (-5) 10)
                have b3498 := hb (x 5 5)
                have b3499 := hb (x 4 1 && x 4 6)
                have b3500 := hb (x 3 2 && x 3 7)
                have b3501 := hb (x 2 3 && x 2 8)
                have b3502 := hb (x 1 4 && x 1 9)
                have b3503 := hb (x 0 5 && x 0 10)
                have b3504 := hb (x (-1) 6 && x (-1) 11)
                have b3505 := hb (x (-2) 7 && x (-2) 12)
                have b3506 := hb (x (-3) 8 && x (-3) 13)
                have b3507 := hb (x (-4) 9 && x (-4) 14)
                clear * - r3496 b3497 b3498 b3499 b3500 b3501 b3502 b3503 b3504 b3505 b3506 b3507 d2615 d2781 d2769 g21 d2293 g22 g23 d2155 d3491 d2825
                omega
              have d3508 : (x 3 7).toNat = 1 := by
                have r3509 := hand2 (x 3 2) (x 3 7)
                have b3510 := hb (x 3 7)
                have b3511 := hb (x 3 2 && x 3 7)
                clear * - r3509 b3510 b3511 d3495
                omega
              have d3512 : (x 10 8).toNat = 0 := by
                have r3513 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3514 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                have e3515 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                have e3516 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                have e3517 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                have e3518 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                have e3519 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                have b3520 := hb (x 3 7)
                have b3521 := hb (x 4 6)
                have b3522 := hb (x 5 5)
                have b3523 := hb (x 6 4)
                have b3524 := hb (x 7 11)
                have b3525 := hb (x 8 10)
                have b3526 := hb (x 9 9)
                have b3527 := hb (x 10 8)
                clear * - r3513 e3514 e3515 e3516 e3517 e3518 e3519 b3520 b3521 b3522 b3523 b3524 b3525 b3526 b3527 d2587 d2615 d2777 d3508
                omega
              have d3528 : (x 10 1 && x 10 8).toNat = 0 := by
                have r3529 := hand2 (x 10 1) (x 10 8)
                have b3530 := hb (x 10 8)
                have b3531 := hb (x 10 1 && x 10 8)
                clear * - r3529 b3530 b3531 d3512
                omega
              have d3532 : (x 10 2 && x 10 8).toNat = 0 := by
                have r3533 := hand2 (x 10 2) (x 10 8)
                have b3534 := hb (x 10 8)
                have b3535 := hb (x 10 2 && x 10 8)
                clear * - r3533 b3534 b3535 d3512
                omega
              have d3536 : (x 10 3 && x 10 8).toNat = 0 := by
                have r3537 := hand2 (x 10 3) (x 10 8)
                have b3538 := hb (x 10 8)
                have b3539 := hb (x 10 3 && x 10 8)
                clear * - r3537 b3538 b3539 d3512
                omega
              have d3540 : (x 9 9).toNat = 0 := by
                have r3541 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3542 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                have e3543 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                have e3544 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                have e3545 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                have e3546 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                have e3547 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                have b3548 := hb (x 3 7)
                have b3549 := hb (x 4 6)
                have b3550 := hb (x 5 5)
                have b3551 := hb (x 6 4)
                have b3552 := hb (x 7 11)
                have b3553 := hb (x 8 10)
                have b3554 := hb (x 9 9)
                have b3555 := hb (x 10 8)
                clear * - r3541 e3542 e3543 e3544 e3545 e3546 e3547 b3548 b3549 b3550 b3551 b3552 b3553 b3554 b3555 d3512 d2587 d2615 d2777 d3508
                omega
              have d3556 : (x 9 2 && x 9 9).toNat = 0 := by
                have r3557 := hand2 (x 9 2) (x 9 9)
                have b3558 := hb (x 9 9)
                have b3559 := hb (x 9 2 && x 9 9)
                clear * - r3557 b3558 b3559 d3540
                omega
              have d3560 : (x 9 3 && x 9 9).toNat = 0 := by
                have r3561 := hand2 (x 9 3) (x 9 9)
                have b3562 := hb (x 9 9)
                have b3563 := hb (x 9 3 && x 9 9)
                clear * - r3561 b3562 b3563 d3540
                omega
              have d3564 : (x 9 4 && x 9 9).toNat = 0 := by
                have r3565 := hand2 (x 9 4) (x 9 9)
                have b3566 := hb (x 9 9)
                have b3567 := hb (x 9 4 && x 9 9)
                clear * - r3565 b3566 b3567 d3540
                omega
              have d3568 : (x 8 10).toNat = 0 := by
                have r3569 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3570 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                have e3571 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                have e3572 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                have e3573 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                have e3574 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                have e3575 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                have b3576 := hb (x 3 7)
                have b3577 := hb (x 4 6)
                have b3578 := hb (x 5 5)
                have b3579 := hb (x 6 4)
                have b3580 := hb (x 7 11)
                have b3581 := hb (x 8 10)
                have b3582 := hb (x 9 9)
                have b3583 := hb (x 10 8)
                clear * - r3569 e3570 e3571 e3572 e3573 e3574 e3575 b3576 b3577 b3578 b3579 b3580 b3581 b3582 b3583 d3512 d3540 d2587 d2615 d2777 d3508
                omega
              have d3584 : (x 8 3 && x 8 10).toNat = 0 := by
                have r3585 := hand2 (x 8 3) (x 8 10)
                have b3586 := hb (x 8 10)
                have b3587 := hb (x 8 3 && x 8 10)
                clear * - r3585 b3586 b3587 d3568
                omega
              have d3588 : (x 8 4 && x 8 10).toNat = 0 := by
                have r3589 := hand2 (x 8 4) (x 8 10)
                have b3590 := hb (x 8 10)
                have b3591 := hb (x 8 4 && x 8 10)
                clear * - r3589 b3590 b3591 d3568
                omega
              have d3592 : (x 8 5 && x 8 10).toNat = 0 := by
                have r3593 := hand2 (x 8 5) (x 8 10)
                have b3594 := hb (x 8 10)
                have b3595 := hb (x 8 5 && x 8 10)
                clear * - r3593 b3594 b3595 d3568
                omega
              have d3596 : (x 7 11).toNat = 0 := by
                have r3597 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3598 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                have e3599 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                have e3600 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                have e3601 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                have e3602 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                have e3603 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                have b3604 := hb (x 3 7)
                have b3605 := hb (x 4 6)
                have b3606 := hb (x 5 5)
                have b3607 := hb (x 6 4)
                have b3608 := hb (x 7 11)
                have b3609 := hb (x 8 10)
                have b3610 := hb (x 9 9)
                have b3611 := hb (x 10 8)
                clear * - r3597 e3598 e3599 e3600 e3601 e3602 e3603 b3604 b3605 b3606 b3607 b3608 b3609 b3610 b3611 d3512 d3540 d3568 d2587 d2615 d2777 d3508
                omega
              have d3612 : (x 7 4 && x 7 11).toNat = 0 := by
                have r3613 := hand2 (x 7 4) (x 7 11)
                have b3614 := hb (x 7 11)
                have b3615 := hb (x 7 4 && x 7 11)
                clear * - r3613 b3614 b3615 d3596
                omega
              have d3616 : (x 11 7).toNat = 1 := by
                have r3617 : 1 ≤ (x 11 7).toNat + (x 10 1 && x 10 8).toNat + (x 9 2 && x 9 9).toNat + (x 8 3 && x 8 10).toNat + (x 7 4 && x 7 11).toNat + (x 6 5 && x 6 12).toNat + (x 5 6 && x 5 13).toNat + (x 4 7 && x 4 14).toNat + (x 3 8).toNat := by have q := hcov7 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b3618 := hb (x 3 8)
                have b3619 := hb (x 11 7)
                have b3620 := hb (x 10 1 && x 10 8)
                have b3621 := hb (x 9 2 && x 9 9)
                have b3622 := hb (x 8 3 && x 8 10)
                have b3623 := hb (x 7 4 && x 7 11)
                have b3624 := hb (x 6 5 && x 6 12)
                have b3625 := hb (x 5 6 && x 5 13)
                have b3626 := hb (x 4 7 && x 4 14)
                clear * - r3617 b3618 b3619 b3620 b3621 b3622 b3623 b3624 b3625 b3626 d3528 d3556 d3584 d3612 d2575 d2607 d2773 d2916
                omega
              have d3627 : (x 18 8).toNat = 0 := by
                have r3628 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3629 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
                have e3630 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
                have e3631 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
                have e3632 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
                have e3633 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
                have e3634 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
                have b3635 := hb (x 11 7)
                have b3636 := hb (x 12 6)
                have b3637 := hb (x 13 5)
                have b3638 := hb (x 14 4)
                have b3639 := hb (x 15 11)
                have b3640 := hb (x 16 10)
                have b3641 := hb (x 17 9)
                have b3642 := hb (x 18 8)
                clear * - r3628 e3629 e3630 e3631 e3632 e3633 e3634 b3635 b3636 b3637 b3638 b3639 b3640 b3641 b3642 d3616
                omega
              have d3643 : (x 17 9).toNat = 0 := by
                have r3644 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3645 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
                have e3646 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
                have e3647 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
                have e3648 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
                have e3649 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
                have e3650 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
                have b3651 := hb (x 11 7)
                have b3652 := hb (x 12 6)
                have b3653 := hb (x 13 5)
                have b3654 := hb (x 14 4)
                have b3655 := hb (x 15 11)
                have b3656 := hb (x 16 10)
                have b3657 := hb (x 17 9)
                have b3658 := hb (x 18 8)
                clear * - r3644 e3645 e3646 e3647 e3648 e3649 e3650 b3651 b3652 b3653 b3654 b3655 b3656 b3657 b3658 d3627 d3616
                omega
              have d3659 : (x 16 10).toNat = 0 := by
                have r3660 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3661 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
                have e3662 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
                have e3663 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
                have e3664 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
                have e3665 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
                have e3666 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
                have b3667 := hb (x 11 7)
                have b3668 := hb (x 12 6)
                have b3669 := hb (x 13 5)
                have b3670 := hb (x 14 4)
                have b3671 := hb (x 15 11)
                have b3672 := hb (x 16 10)
                have b3673 := hb (x 17 9)
                have b3674 := hb (x 18 8)
                clear * - r3660 e3661 e3662 e3663 e3664 e3665 e3666 b3667 b3668 b3669 b3670 b3671 b3672 b3673 b3674 d3627 d3643 d3616
                omega
              have d3675 : (x 15 11).toNat = 0 := by
                have r3676 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3677 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
                have e3678 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
                have e3679 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
                have e3680 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
                have e3681 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
                have e3682 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
                have b3683 := hb (x 11 7)
                have b3684 := hb (x 12 6)
                have b3685 := hb (x 13 5)
                have b3686 := hb (x 14 4)
                have b3687 := hb (x 15 11)
                have b3688 := hb (x 16 10)
                have b3689 := hb (x 17 9)
                have b3690 := hb (x 18 8)
                clear * - r3676 e3677 e3678 e3679 e3680 e3681 e3682 b3683 b3684 b3685 b3686 b3687 b3688 b3689 b3690 d3627 d3643 d3659 d3616
                omega
              have d3691 : (x 14 4).toNat = 0 := by
                have r3692 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3693 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
                have e3694 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
                have e3695 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
                have e3696 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
                have e3697 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
                have e3698 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
                have b3699 := hb (x 11 7)
                have b3700 := hb (x 12 6)
                have b3701 := hb (x 13 5)
                have b3702 := hb (x 14 4)
                have b3703 := hb (x 15 11)
                have b3704 := hb (x 16 10)
                have b3705 := hb (x 17 9)
                have b3706 := hb (x 18 8)
                clear * - r3692 e3693 e3694 e3695 e3696 e3697 e3698 b3699 b3700 b3701 b3702 b3703 b3704 b3705 b3706 d3627 d3643 d3659 d3675 d3616
                omega
              have d3707 : (x 13 5).toNat = 0 := by
                have r3708 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3709 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
                have e3710 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
                have e3711 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
                have e3712 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
                have e3713 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
                have e3714 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
                have b3715 := hb (x 11 7)
                have b3716 := hb (x 12 6)
                have b3717 := hb (x 13 5)
                have b3718 := hb (x 14 4)
                have b3719 := hb (x 15 11)
                have b3720 := hb (x 16 10)
                have b3721 := hb (x 17 9)
                have b3722 := hb (x 18 8)
                clear * - r3708 e3709 e3710 e3711 e3712 e3713 e3714 b3715 b3716 b3717 b3718 b3719 b3720 b3721 b3722 d3627 d3643 d3659 d3675 d3691 d3616
                omega
              have d3723 : (x 12 6).toNat = 0 := by
                have r3724 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3725 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
                have e3726 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
                have e3727 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
                have e3728 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
                have e3729 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
                have e3730 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
                have b3731 := hb (x 11 7)
                have b3732 := hb (x 12 6)
                have b3733 := hb (x 13 5)
                have b3734 := hb (x 14 4)
                have b3735 := hb (x 15 11)
                have b3736 := hb (x 16 10)
                have b3737 := hb (x 17 9)
                have b3738 := hb (x 18 8)
                clear * - r3724 e3725 e3726 e3727 e3728 e3729 e3730 b3731 b3732 b3733 b3734 b3735 b3736 b3737 b3738 d3627 d3643 d3659 d3675 d3691 d3707 d3616
                omega
              have d3739 : (x 12 1 && x 12 6).toNat = 0 := by
                have r3740 := hand2 (x 12 1) (x 12 6)
                have b3741 := hb (x 12 6)
                have b3742 := hb (x 12 1 && x 12 6)
                clear * - r3740 b3741 b3742 d3723
                omega
              have d3743 : (x 7 5 && x 7 11).toNat = 0 := by
                have r3744 := hand2 (x 7 5) (x 7 11)
                have b3745 := hb (x 7 11)
                have b3746 := hb (x 7 5 && x 7 11)
                clear * - r3744 b3745 b3746 d3596
                omega
              have d3747 : (x 11 1 && x 11 7).toNat = 1 := by
                have r3748 : 1 ≤ (x 12 6).toNat + (x 11 1 && x 11 7).toNat + (x 10 2 && x 10 8).toNat + (x 9 3 && x 9 9).toNat + (x 8 4 && x 8 10).toNat + (x 7 5 && x 7 11).toNat + (x 6 6 && x 6 12).toNat + (x 5 7 && x 5 13).toNat + (x 4 8 && x 4 14).toNat + (x 3 9).toNat := by have q := hcov6 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b3749 := hb (x 3 9)
                have b3750 := hb (x 12 6)
                have b3751 := hb (x 11 1 && x 11 7)
                have b3752 := hb (x 10 2 && x 10 8)
                have b3753 := hb (x 9 3 && x 9 9)
                have b3754 := hb (x 8 4 && x 8 10)
                have b3755 := hb (x 7 5 && x 7 11)
                have b3756 := hb (x 6 6 && x 6 12)
                have b3757 := hb (x 5 7 && x 5 13)
                have b3758 := hb (x 4 8 && x 4 14)
                clear * - r3748 b3749 b3750 b3751 b3752 b3753 b3754 b3755 b3756 b3757 b3758 d3723 d3532 d3560 d3588 d3743 d2579 d2611 d2183 d2191
                omega
              have d3759 : (x 11 1).toNat = 1 := by
                have r3760 := hand1 (x 11 1) (x 11 7)
                have b3761 := hb (x 11 1)
                have b3762 := hb (x 11 1 && x 11 7)
                clear * - r3760 b3761 b3762 d3747
                omega
              have d3763 : (x 10 2).toNat = 0 := by
                have r3764 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b3765 := hb (x (-2) 14)
                have b3766 := hb (x (-1) 13)
                have b3767 := hb (x 0 12)
                have b3768 := hb (x 1 11)
                have b3769 := hb (x 2 10)
                have b3770 := hb (x 3 9)
                have b3771 := hb (x 4 8)
                have b3772 := hb (x 5 7)
                have b3773 := hb (x 6 6)
                have b3774 := hb (x 7 5)
                have b3775 := hb (x 8 4)
                have b3776 := hb (x 9 3)
                have b3777 := hb (x 10 2)
                have b3778 := hb (x 11 1)
                clear * - r3764 b3765 b3766 b3767 b3768 b3769 b3770 b3771 b3772 b3773 b3774 b3775 b3776 b3777 b3778 d3759 d2167 d2191 d2211 d2235 f2358 d2038 d2127
                omega
              have d3779 : (x 10 10).toNat = 0 := by
                have r3780 : (x 10 10).toNat ≤ (x 10 2).toNat := himp _ _ (hp10 10)
                have b3781 := hb (x 10 2)
                have b3782 := hb (x 10 10)
                clear * - r3780 b3781 b3782 d3763
                omega
              have d3783 : (x 9 3).toNat = 0 := by
                have r3784 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b3785 := hb (x (-2) 14)
                have b3786 := hb (x (-1) 13)
                have b3787 := hb (x 0 12)
                have b3788 := hb (x 1 11)
                have b3789 := hb (x 2 10)
                have b3790 := hb (x 3 9)
                have b3791 := hb (x 4 8)
                have b3792 := hb (x 5 7)
                have b3793 := hb (x 6 6)
                have b3794 := hb (x 7 5)
                have b3795 := hb (x 8 4)
                have b3796 := hb (x 9 3)
                have b3797 := hb (x 10 2)
                have b3798 := hb (x 11 1)
                clear * - r3784 b3785 b3786 b3787 b3788 b3789 b3790 b3791 b3792 b3793 b3794 b3795 b3796 b3797 b3798 d3759 d3763 d2167 d2191 d2211 d2235 f2358 d2038 d2127
                omega
              have d3799 : (x 9 11).toNat = 0 := by
                have r3800 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
                have b3801 := hb (x 9 3)
                have b3802 := hb (x 9 11)
                clear * - r3800 b3801 b3802 d3783
                omega
              have d3803 : (x 9 1 && x 9 11).toNat = 0 := by
                have r3804 := hand2 (x 9 1) (x 9 11)
                have b3805 := hb (x 9 11)
                have b3806 := hb (x 9 1 && x 9 11)
                clear * - r3804 b3805 b3806 d3799
                omega
              have d3807 : (x 8 4).toNat = 0 := by
                have r3808 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b3809 := hb (x (-2) 14)
                have b3810 := hb (x (-1) 13)
                have b3811 := hb (x 0 12)
                have b3812 := hb (x 1 11)
                have b3813 := hb (x 2 10)
                have b3814 := hb (x 3 9)
                have b3815 := hb (x 4 8)
                have b3816 := hb (x 5 7)
                have b3817 := hb (x 6 6)
                have b3818 := hb (x 7 5)
                have b3819 := hb (x 8 4)
                have b3820 := hb (x 9 3)
                have b3821 := hb (x 10 2)
                have b3822 := hb (x 11 1)
                clear * - r3808 b3809 b3810 b3811 b3812 b3813 b3814 b3815 b3816 b3817 b3818 b3819 b3820 b3821 b3822 d3759 d3763 d3783 d2167 d2191 d2211 d2235 f2358 d2038 d2127
                omega
              have d3823 : (x 8 1 && x 8 4).toNat = 0 := by
                have r3824 := hand2 (x 8 1) (x 8 4)
                have b3825 := hb (x 8 4)
                have b3826 := hb (x 8 1 && x 8 4)
                clear * - r3824 b3825 b3826 d3807
                omega
              have d3827 : (x 7 5).toNat = 0 := by
                have r3828 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b3829 := hb (x (-2) 14)
                have b3830 := hb (x (-1) 13)
                have b3831 := hb (x 0 12)
                have b3832 := hb (x 1 11)
                have b3833 := hb (x 2 10)
                have b3834 := hb (x 3 9)
                have b3835 := hb (x 4 8)
                have b3836 := hb (x 5 7)
                have b3837 := hb (x 6 6)
                have b3838 := hb (x 7 5)
                have b3839 := hb (x 8 4)
                have b3840 := hb (x 9 3)
                have b3841 := hb (x 10 2)
                have b3842 := hb (x 11 1)
                clear * - r3828 b3829 b3830 b3831 b3832 b3833 b3834 b3835 b3836 b3837 b3838 b3839 b3840 b3841 b3842 d3759 d3763 d3783 d3807 d2167 d2191 d2211 d2235 f2358 d2038 d2127
                omega
              have d3843 : (x 7 2 && x 7 5).toNat = 0 := by
                have r3844 := hand2 (x 7 2) (x 7 5)
                have b3845 := hb (x 7 5)
                have b3846 := hb (x 7 2 && x 7 5)
                clear * - r3844 b3845 b3846 d3827
                omega
              have d3847 : (x 6 3 && x 6 6).toNat = 1 := by
                have r3848 : 1 ≤ (x 9 3).toNat + (x 8 1 && x 8 4).toNat + (x 7 2 && x 7 5).toNat + (x 6 3 && x 6 6).toNat + (x 5 4 && x 5 7).toNat + (x 4 5 && x 4 8).toNat + (x 3 6 && x 3 9).toNat + (x 2 7 && x 2 10).toNat + (x 1 8 && x 1 11).toNat + (x 0 9 && x 0 12).toNat + (x (-1) 10 && x (-1) 13).toNat + (x (-2) 11 && x (-2) 14).toNat + (x (-3) 12).toNat := by have q := hcov3 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b3849 := hb (x (-3) 12)
                have b3850 := hb (x 9 3)
                have b3851 := hb (x 8 1 && x 8 4)
                have b3852 := hb (x 7 2 && x 7 5)
                have b3853 := hb (x 6 3 && x 6 6)
                have b3854 := hb (x 5 4 && x 5 7)
                have b3855 := hb (x 4 5 && x 4 8)
                have b3856 := hb (x 3 6 && x 3 9)
                have b3857 := hb (x 2 7 && x 2 10)
                have b3858 := hb (x 1 8 && x 1 11)
                have b3859 := hb (x 0 9 && x 0 12)
                have b3860 := hb (x (-1) 10 && x (-1) 13)
                have b3861 := hb (x (-2) 11 && x (-2) 14)
                clear * - r3848 b3849 b3850 b3851 b3852 b3853 b3854 b3855 b3856 b3857 b3858 b3859 b3860 b3861 d3783 d3823 d3843 d2741 d2187 d2207 d2231 d2251 d2285 g15 g16 d2809
                omega
              have d3862 : (x 6 6).toNat = 1 := by
                have r3863 := hand2 (x 6 3) (x 6 6)
                have b3864 := hb (x 6 6)
                have b3865 := hb (x 6 3 && x 6 6)
                clear * - r3863 b3864 b3865 d3847
                omega
              have d3866 : (x 6 14).toNat = 1 := by
                have r3867 : (x 6 6).toNat ≤ (x 6 14).toNat := himp _ _ (hp6 6)
                have b3868 := hb (x 6 6)
                have b3869 := hb (x 6 14)
                clear * - r3867 b3868 b3869 d3862
                omega
              have d3870 : (x 5 1).toNat = 0 := by
                have r3871 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b3872 := hb (x 5 1)
                have b3873 := hb (x 6 14)
                clear * - r3871 b3872 b3873 d3866
                omega
              have d3874 : (x 5 1 && x 5 14).toNat = 0 := by
                have r3875 := hand1 (x 5 1) (x 5 14)
                have b3876 := hb (x 5 1)
                have b3877 := hb (x 5 1 && x 5 14)
                clear * - r3875 b3876 b3877 d3870
                omega
              have d3878 : (x 6 13).toNat = 1 := by
                have r3879 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b3880 := hb (x 4 2)
                have b3881 := hb (x 6 13)
                have b3882 := hb (x 5 1 && x 5 14)
                clear * - r3879 b3880 b3881 b3882 d3874 d2623
                omega
              have d3883 : (x 6 1).toNat = 1 := by
                have r3884 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
                have b3885 := hb (x 6 1)
                have b3886 := hb (x 6 13)
                clear * - r3884 b3885 b3886 d3878
                omega
              have d3887 : (x 7 14).toNat = 0 := by
                have r3888 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b3889 := hb (x 6 1)
                have b3890 := hb (x 7 14)
                clear * - r3888 b3889 b3890 d3883
                omega
              have d3891 : (x 7 1 && x 7 14).toNat = 0 := by
                have r3892 := hand2 (x 7 1) (x 7 14)
                have b3893 := hb (x 7 14)
                have b3894 := hb (x 7 1 && x 7 14)
                clear * - r3892 b3893 b3894 d3887
                omega
              have d3895 : (x 7 6).toNat = 0 := by
                have r3896 : (x 7 6).toNat ≤ (x 7 14).toNat := himp _ _ (hp6 7)
                have b3897 := hb (x 7 6)
                have b3898 := hb (x 7 14)
                clear * - r3896 b3897 b3898 d3887
                omega
              have d3899 : (x 7 6 && x 7 11).toNat = 0 := by
                have r3900 := hand1 (x 7 6) (x 7 11)
                have b3901 := hb (x 7 6)
                have b3902 := hb (x 7 6 && x 7 11)
                clear * - r3900 b3901 b3902 d3895
                omega
              have d3903 : (x 11 2 && x 11 7).toNat = 1 := by
                have r3904 : 1 ≤ (x 13 5).toNat + (x 12 1 && x 12 6).toNat + (x 11 2 && x 11 7).toNat + (x 10 3 && x 10 8).toNat + (x 9 4 && x 9 9).toNat + (x 8 5 && x 8 10).toNat + (x 7 6 && x 7 11).toNat + (x 6 7 && x 6 12).toNat + (x 5 8 && x 5 13).toNat + (x 4 9 && x 4 14).toNat + (x 3 10).toNat := by have q := hcov5 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b3905 := hb (x 3 10)
                have b3906 := hb (x 13 5)
                have b3907 := hb (x 12 1 && x 12 6)
                have b3908 := hb (x 11 2 && x 11 7)
                have b3909 := hb (x 10 3 && x 10 8)
                have b3910 := hb (x 9 4 && x 9 9)
                have b3911 := hb (x 8 5 && x 8 10)
                have b3912 := hb (x 7 6 && x 7 11)
                have b3913 := hb (x 6 7 && x 6 12)
                have b3914 := hb (x 5 8 && x 5 13)
                have b3915 := hb (x 4 9 && x 4 14)
                clear * - r3904 b3905 b3906 b3907 b3908 b3909 b3910 b3911 b3912 b3913 b3914 b3915 d3707 d3739 d3536 d3564 d3592 d3899 d2583 g25 g26 g13
                omega
              have d3916 : (x 11 2).toNat = 1 := by
                have r3917 := hand1 (x 11 2) (x 11 7)
                have b3918 := hb (x 11 2)
                have b3919 := hb (x 11 2 && x 11 7)
                clear * - r3917 b3918 b3919 d3903
                omega
              have d3920 : (x 11 14).toNat = 1 := by
                have r3921 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
                have b3922 := hb (x 11 2)
                have b3923 := hb (x 11 14)
                clear * - r3921 b3922 b3923 d3916
                omega
              have d3924 : (x 10 1).toNat = 0 := by
                have r3925 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b3926 := hb (x 10 1)
                have b3927 := hb (x 11 14)
                clear * - r3925 b3926 b3927 d3920
                omega
              have d3928 : (x 10 1 && x 10 7).toNat = 0 := by
                have r3929 := hand1 (x 10 1) (x 10 7)
                have b3930 := hb (x 10 1)
                have b3931 := hb (x 10 1 && x 10 7)
                clear * - r3929 b3930 b3931 d3924
                omega
              have d3932 : (x 11 6).toNat = 1 := by
                have r3933 : 1 ≤ (x 11 6).toNat + (x 10 1 && x 10 7).toNat + (x 9 2 && x 9 8).toNat + (x 8 3 && x 8 9).toNat + (x 7 4 && x 7 10).toNat + (x 6 5 && x 6 11).toNat + (x 5 6 && x 5 12).toNat + (x 4 7 && x 4 13).toNat + (x 3 8 && x 3 14).toNat + (x 2 9).toNat := by have q := hcov6 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b3934 := hb (x 2 9)
                have b3935 := hb (x 11 6)
                have b3936 := hb (x 10 1 && x 10 7)
                have b3937 := hb (x 9 2 && x 9 8)
                have b3938 := hb (x 8 3 && x 8 9)
                have b3939 := hb (x 7 4 && x 7 10)
                have b3940 := hb (x 6 5 && x 6 11)
                have b3941 := hb (x 5 6 && x 5 12)
                have b3942 := hb (x 4 7 && x 4 13)
                have b3943 := hb (x 3 8 && x 3 14)
                clear * - r3933 b3934 b3935 b3936 b3937 b3938 b3939 b3940 b3941 b3942 b3943 d3928 d3096 d3116 d3136 d3156 d2733 d2753 d2932 d2721
                omega
              have d3944 : (x 17 8).toNat = 0 := by
                have r3945 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3946 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
                have e3947 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
                have e3948 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
                have e3949 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
                have e3950 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
                have e3951 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
                have b3952 := hb (x 10 7)
                have b3953 := hb (x 11 6)
                have b3954 := hb (x 12 5)
                have b3955 := hb (x 13 4)
                have b3956 := hb (x 14 11)
                have b3957 := hb (x 15 10)
                have b3958 := hb (x 16 9)
                have b3959 := hb (x 17 8)
                clear * - r3945 e3946 e3947 e3948 e3949 e3950 e3951 b3952 b3953 b3954 b3955 b3956 b3957 b3958 b3959 d3932
                omega
              have d3960 : (x 16 9).toNat = 0 := by
                have r3961 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3962 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
                have e3963 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
                have e3964 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
                have e3965 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
                have e3966 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
                have e3967 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
                have b3968 := hb (x 10 7)
                have b3969 := hb (x 11 6)
                have b3970 := hb (x 12 5)
                have b3971 := hb (x 13 4)
                have b3972 := hb (x 14 11)
                have b3973 := hb (x 15 10)
                have b3974 := hb (x 16 9)
                have b3975 := hb (x 17 8)
                clear * - r3961 e3962 e3963 e3964 e3965 e3966 e3967 b3968 b3969 b3970 b3971 b3972 b3973 b3974 b3975 d3944 d3932
                omega
              have d3976 : (x 15 10).toNat = 0 := by
                have r3977 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3978 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
                have e3979 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
                have e3980 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
                have e3981 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
                have e3982 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
                have e3983 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
                have b3984 := hb (x 10 7)
                have b3985 := hb (x 11 6)
                have b3986 := hb (x 12 5)
                have b3987 := hb (x 13 4)
                have b3988 := hb (x 14 11)
                have b3989 := hb (x 15 10)
                have b3990 := hb (x 16 9)
                have b3991 := hb (x 17 8)
                clear * - r3977 e3978 e3979 e3980 e3981 e3982 e3983 b3984 b3985 b3986 b3987 b3988 b3989 b3990 b3991 d3944 d3960 d3932
                omega
              have d3992 : (x 14 11).toNat = 0 := by
                have r3993 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e3994 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
                have e3995 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
                have e3996 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
                have e3997 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
                have e3998 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
                have e3999 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
                have b4000 := hb (x 10 7)
                have b4001 := hb (x 11 6)
                have b4002 := hb (x 12 5)
                have b4003 := hb (x 13 4)
                have b4004 := hb (x 14 11)
                have b4005 := hb (x 15 10)
                have b4006 := hb (x 16 9)
                have b4007 := hb (x 17 8)
                clear * - r3993 e3994 e3995 e3996 e3997 e3998 e3999 b4000 b4001 b4002 b4003 b4004 b4005 b4006 b4007 d3944 d3960 d3976 d3932
                omega
              have d4008 : (x 14 1 && x 14 11).toNat = 0 := by
                have r4009 := hand2 (x 14 1) (x 14 11)
                have b4010 := hb (x 14 11)
                have b4011 := hb (x 14 1 && x 14 11)
                clear * - r4009 b4010 b4011 d3992
                omega
              have d4012 : (x 10 13).toNat = 0 := by
                have r4013 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
                have b4014 := hb (x 10 1)
                have b4015 := hb (x 10 13)
                clear * - r4013 b4014 b4015 d3924
                omega
              have d4016 : (x 10 5).toNat = 0 := by
                have r4017 : (x 10 5).toNat ≤ (x 10 13).toNat := himp _ _ (hp5 10)
                have b4018 := hb (x 10 5)
                have b4019 := hb (x 10 13)
                clear * - r4017 b4018 b4019 d4012
                omega
              have d4020 : (x 10 9).toNat = 0 := by
                have r4021 : (x 10 9).toNat ≤ (x 10 1).toNat := himp _ _ (hp9 10)
                have b4022 := hb (x 10 1)
                have b4023 := hb (x 10 9)
                clear * - r4021 b4022 b4023 d3924
                omega
              have d4024 : (x 13 12).toNat = 0 := by
                have r4025 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4026 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
                have e4027 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
                have b4028 := hb (x 10 3)
                have b4029 := hb (x 11 2)
                have b4030 := hb (x 12 13)
                have b4031 := hb (x 13 12)
                clear * - r4025 e4026 e4027 b4028 b4029 b4030 b4031 d3916
                omega
              have d4032 : (x 13 2 && x 13 12).toNat = 0 := by
                have r4033 := hand2 (x 13 2) (x 13 12)
                have b4034 := hb (x 13 12)
                have b4035 := hb (x 13 2 && x 13 12)
                clear * - r4033 b4034 b4035 d4024
                omega
              have d4036 : (x 12 13).toNat = 0 := by
                have r4037 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4038 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
                have e4039 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
                have b4040 := hb (x 10 3)
                have b4041 := hb (x 11 2)
                have b4042 := hb (x 12 13)
                have b4043 := hb (x 13 12)
                clear * - r4037 e4038 e4039 b4040 b4041 b4042 b4043 d4024 d3916
                omega
              have d4044 : (x 12 3 && x 12 13).toNat = 0 := by
                have r4045 := hand2 (x 12 3) (x 12 13)
                have b4046 := hb (x 12 13)
                have b4047 := hb (x 12 3 && x 12 13)
                clear * - r4045 b4046 b4047 d4036
                omega
              have d4048 : (x 11 4 && x 11 14).toNat = 1 := by
                have r4049 : 1 ≤ (x 15 10).toNat + (x 14 1 && x 14 11).toNat + (x 13 2 && x 13 12).toNat + (x 12 3 && x 12 13).toNat + (x 11 4 && x 11 14).toNat + (x 10 5).toNat := by have q := hcov10 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4050 := hb (x 10 5)
                have b4051 := hb (x 15 10)
                have b4052 := hb (x 14 1 && x 14 11)
                have b4053 := hb (x 13 2 && x 13 12)
                have b4054 := hb (x 12 3 && x 12 13)
                have b4055 := hb (x 11 4 && x 11 14)
                clear * - r4049 b4050 b4051 b4052 b4053 b4054 b4055 d3976 d4008 d4032 d4044 d4016
                omega
              have d4056 : (x 11 4).toNat = 1 := by
                have r4057 := hand1 (x 11 4) (x 11 14)
                have b4058 := hb (x 11 4)
                have b4059 := hb (x 11 4 && x 11 14)
                clear * - r4057 b4058 b4059 d4048
                omega
              have d4060 : (x 11 12).toNat = 1 := by
                have r4061 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
                have b4062 := hb (x 11 4)
                have b4063 := hb (x 11 12)
                clear * - r4061 b4062 b4063 d4056
                omega
              have d4064 : (x 9 2).toNat = 0 := by
                have r4065 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4066 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                have e4067 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                have b4068 := hb (x 8 3)
                have b4069 := hb (x 9 2)
                have b4070 := hb (x 10 13)
                have b4071 := hb (x 11 12)
                clear * - r4065 e4066 e4067 b4068 b4069 b4070 b4071 d4060 d4012
                omega
              have d4072 : (x 9 10).toNat = 0 := by
                have r4073 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
                have b4074 := hb (x 9 2)
                have b4075 := hb (x 9 10)
                clear * - r4073 b4074 b4075 d4064
                omega
              have d4076 : (x 9 1 && x 9 10).toNat = 0 := by
                have r4077 := hand2 (x 9 1) (x 9 10)
                have b4078 := hb (x 9 10)
                have b4079 := hb (x 9 1 && x 9 10)
                clear * - r4077 b4078 b4079 d4072
                omega
              have d4080 : (x 8 3).toNat = 0 := by
                have r4081 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4082 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                have e4083 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                have b4084 := hb (x 8 3)
                have b4085 := hb (x 9 2)
                have b4086 := hb (x 10 13)
                have b4087 := hb (x 11 12)
                clear * - r4081 e4082 e4083 b4084 b4085 b4086 b4087 d4060 d4012 d4064
                omega
              have d4088 : (x 8 11).toNat = 0 := by
                have r4089 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
                have b4090 := hb (x 8 3)
                have b4091 := hb (x 8 11)
                clear * - r4089 b4090 b4091 d4080
                omega
              have d4092 : (x 8 2 && x 8 11).toNat = 0 := by
                have r4093 := hand2 (x 8 2) (x 8 11)
                have b4094 := hb (x 8 11)
                have b4095 := hb (x 8 2 && x 8 11)
                clear * - r4093 b4094 b4095 d4088
                omega
              have d4096 : (x 7 3 && x 7 12).toNat = 1 := by
                have r4097 : 1 ≤ (x 10 9).toNat + (x 9 1 && x 9 10).toNat + (x 8 2 && x 8 11).toNat + (x 7 3 && x 7 12).toNat + (x 6 4 && x 6 13).toNat + (x 5 5 && x 5 14).toNat + (x 4 6).toNat := by have q := hcov9 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4098 := hb (x 4 6)
                have b4099 := hb (x 10 9)
                have b4100 := hb (x 9 1 && x 9 10)
                have b4101 := hb (x 8 2 && x 8 11)
                have b4102 := hb (x 7 3 && x 7 12)
                have b4103 := hb (x 6 4 && x 6 13)
                have b4104 := hb (x 5 5 && x 5 14)
                clear * - r4097 b4098 b4099 b4100 b4101 b4102 b4103 b4104 d4020 d4076 d4092 d2595 d2619 d2777
                omega
              have d4105 : (x 7 3).toNat = 1 := by
                have r4106 := hand1 (x 7 3) (x 7 12)
                have b4107 := hb (x 7 3)
                have b4108 := hb (x 7 3 && x 7 12)
                clear * - r4106 b4107 b4108 d4096
                omega
              have d4109 : (x 10 12).toNat = 0 := by
                have r4110 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4111 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                have e4112 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                have b4113 := hb (x 7 3)
                have b4114 := hb (x 8 2)
                have b4115 := hb (x 9 13)
                have b4116 := hb (x 10 12)
                clear * - r4110 e4111 e4112 b4113 b4114 b4115 b4116 d4105
                omega
              have d4117 : (x 9 13).toNat = 0 := by
                have r4118 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4119 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                have e4120 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                have b4121 := hb (x 7 3)
                have b4122 := hb (x 8 2)
                have b4123 := hb (x 9 13)
                have b4124 := hb (x 10 12)
                clear * - r4118 e4119 e4120 b4121 b4122 b4123 b4124 d4109 d4105
                omega
              have d4125 : (x 8 2).toNat = 0 := by
                have r4126 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4127 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                have e4128 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                have b4129 := hb (x 7 3)
                have b4130 := hb (x 8 2)
                have b4131 := hb (x 9 13)
                have b4132 := hb (x 10 12)
                clear * - r4126 e4127 e4128 b4129 b4130 b4131 b4132 d4109 d4117 d4105
                omega
              have d4133 : (x 8 2 && x 8 12).toNat = 0 := by
                have r4134 := hand1 (x 8 2) (x 8 12)
                have b4135 := hb (x 8 2)
                have b4136 := hb (x 8 2 && x 8 12)
                clear * - r4134 b4135 b4136 d4125
                omega
              have d4137 : (x 7 3 && x 7 13).toNat = 1 := by
                have r4138 : 1 ≤ (x 10 10).toNat + (x 9 1 && x 9 11).toNat + (x 8 2 && x 8 12).toNat + (x 7 3 && x 7 13).toNat + (x 6 4 && x 6 14).toNat + (x 5 5).toNat := by have q := hcov10 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4139 := hb (x 5 5)
                have b4140 := hb (x 10 10)
                have b4141 := hb (x 9 1 && x 9 11)
                have b4142 := hb (x 8 2 && x 8 12)
                have b4143 := hb (x 7 3 && x 7 13)
                have b4144 := hb (x 6 4 && x 6 14)
                clear * - r4138 b4139 b4140 b4141 b4142 b4143 b4144 d3779 d3803 d4133 d2591 d2615
                omega
              have d4145 : (x 7 13).toNat = 1 := by
                have r4146 := hand2 (x 7 3) (x 7 13)
                have b4147 := hb (x 7 13)
                have b4148 := hb (x 7 3 && x 7 13)
                clear * - r4146 b4147 b4148 d4137
                omega
              have d4149 : (x 7 1).toNat = 1 := by
                have r4150 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
                have b4151 := hb (x 7 1)
                have b4152 := hb (x 7 13)
                clear * - r4150 b4151 b4152 d4145
                omega
              have d4153 : (x 8 14).toNat = 0 := by
                have r4154 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4155 := hb (x 7 1)
                have b4156 := hb (x 8 14)
                clear * - r4154 b4155 b4156 d4149
                omega
              have d4157 : (x 8 1 && x 8 14).toNat = 0 := by
                have r4158 := hand2 (x 8 1) (x 8 14)
                have b4159 := hb (x 8 14)
                have b4160 := hb (x 8 1 && x 8 14)
                clear * - r4158 b4159 b4160 d4153
                omega
              have d4161 : (x 7 2).toNat = 1 := by
                have r4162 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4163 := hb (x 7 2)
                have b4164 := hb (x 9 13)
                have b4165 := hb (x 8 1 && x 8 14)
                clear * - r4162 b4163 b4164 b4165 d4117 d4157
                omega
              have d4166 : (x 9 12).toNat = 0 := by
                have r4167 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4168 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                have e4169 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                have b4170 := hb (x 6 3)
                have b4171 := hb (x 7 2)
                have b4172 := hb (x 8 13)
                have b4173 := hb (x 9 12)
                clear * - r4167 e4168 e4169 b4170 b4171 b4172 b4173 d4161
                omega
              have d4174 : (x 8 13).toNat = 0 := by
                have r4175 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e4176 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                have e4177 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                have b4178 := hb (x 6 3)
                have b4179 := hb (x 7 2)
                have b4180 := hb (x 8 13)
                have b4181 := hb (x 9 12)
                clear * - r4175 e4176 e4177 b4178 b4179 b4180 b4181 d4166 d4161
                omega
              have d4182 : (x 6 2).toNat = 1 := by
                have r4183 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b4184 := hb (x 6 2)
                have b4185 := hb (x 8 13)
                have b4186 := hb (x 7 1 && x 7 14)
                clear * - r4183 b4184 b4185 b4186 d4174 d3891
                omega
              have r4187 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b4188 := hb (x (-6) 14)
              have b4189 := hb (x (-5) 13)
              have b4190 := hb (x (-4) 12)
              have b4191 := hb (x (-3) 11)
              have b4192 := hb (x (-2) 10)
              have b4193 := hb (x (-1) 9)
              have b4194 := hb (x 0 8)
              have b4195 := hb (x 1 7)
              have b4196 := hb (x 2 6)
              have b4197 := hb (x 3 5)
              have b4198 := hb (x 4 4)
              have b4199 := hb (x 5 3)
              have b4200 := hb (x 6 2)
              have b4201 := hb (x 7 1)
              linarith only [r4187, b4188, b4189, b4190, b4191, b4192, b4193, b4194, b4195, b4196, b4197, b4198, b4199, b4200, b4201, d4149, d4182, d2685, d3160, d3240, d3256, f2282, d2058, d2379, d2403, d2414, d2418]
          · have f4202 : (x 0 10).toNat = 1 := by rw [h2291]; rfl
            have d4203 : (x 2 8).toNat = 0 := by
              have r4204 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e4205 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
              have e4206 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
              have e4207 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
              have e4208 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
              have e4209 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
              have e4210 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
              have b4211 := hb (x (-5) 7)
              have b4212 := hb (x (-4) 6)
              have b4213 := hb (x (-3) 5)
              have b4214 := hb (x (-2) 4)
              have b4215 := hb (x (-1) 11)
              have b4216 := hb (x 0 10)
              have b4217 := hb (x 1 9)
              have b4218 := hb (x 2 8)
              clear * - r4204 e4205 e4206 e4207 e4208 e4209 e4210 b4211 b4212 b4213 b4214 b4215 b4216 b4217 b4218 f4202 d2114 d2159
              omega
            have d4219 : (x 1 9).toNat = 0 := by
              have r4220 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e4221 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
              have e4222 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
              have e4223 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
              have e4224 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
              have e4225 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
              have e4226 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
              have b4227 := hb (x (-5) 7)
              have b4228 := hb (x (-4) 6)
              have b4229 := hb (x (-3) 5)
              have b4230 := hb (x (-2) 4)
              have b4231 := hb (x (-1) 11)
              have b4232 := hb (x 0 10)
              have b4233 := hb (x 1 9)
              have b4234 := hb (x 2 8)
              clear * - r4220 e4221 e4222 e4223 e4224 e4225 e4226 b4227 b4228 b4229 b4230 b4231 b4232 b4233 b4234 d4203 f4202 d2114 d2159
              omega
            have d4235 : (x (-2) 4).toNat = 0 := by
              have r4236 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e4237 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
              have e4238 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
              have e4239 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
              have e4240 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
              have e4241 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
              have e4242 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
              have b4243 := hb (x (-5) 7)
              have b4244 := hb (x (-4) 6)
              have b4245 := hb (x (-3) 5)
              have b4246 := hb (x (-2) 4)
              have b4247 := hb (x (-1) 11)
              have b4248 := hb (x 0 10)
              have b4249 := hb (x 1 9)
              have b4250 := hb (x 2 8)
              clear * - r4236 e4237 e4238 e4239 e4240 e4241 e4242 b4243 b4244 b4245 b4246 b4247 b4248 b4249 b4250 d4203 d4219 f4202 d2114 d2159
              omega
            have d4251 : (x (-2) 4 && x (-2) 13).toNat = 0 := by
              have r4252 := hand1 (x (-2) 4) (x (-2) 13)
              have b4253 := hb (x (-2) 4)
              have b4254 := hb (x (-2) 4 && x (-2) 13)
              clear * - r4252 b4253 b4254 d4235
              omega
            have d4255 : (x (-4) 6).toNat = 0 := by
              have r4256 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e4257 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
              have e4258 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
              have e4259 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
              have e4260 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
              have e4261 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
              have e4262 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
              have b4263 := hb (x (-5) 7)
              have b4264 := hb (x (-4) 6)
              have b4265 := hb (x (-3) 5)
              have b4266 := hb (x (-2) 4)
              have b4267 := hb (x (-1) 11)
              have b4268 := hb (x 0 10)
              have b4269 := hb (x 1 9)
              have b4270 := hb (x 2 8)
              clear * - r4256 e4257 e4258 e4259 e4260 e4261 e4262 b4263 b4264 b4265 b4266 b4267 b4268 b4269 b4270 d4203 d4219 f4202 d2114 d4235 d2159
              omega
            have d4271 : (x 2 9).toNat = 1 := by
              have r4272 : 1 ≤ (x 2 9).toNat + (x 1 1 && x 1 10).toNat + (x 0 2 && x 0 11).toNat + (x (-1) 3 && x (-1) 12).toNat + (x (-2) 4 && x (-2) 13).toNat + (x (-3) 5 && x (-3) 14).toNat + (x (-4) 6).toNat := by have q := hcov9 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b4273 := hb (x (-4) 6)
              have b4274 := hb (x 2 9)
              have b4275 := hb (x 1 1 && x 1 10)
              have b4276 := hb (x 0 2 && x 0 11)
              have b4277 := hb (x (-1) 3 && x (-1) 12)
              have b4278 := hb (x (-2) 4 && x (-2) 13)
              have b4279 := hb (x (-3) 5 && x (-3) 14)
              clear * - r4272 b4273 b4274 b4275 b4276 b4277 b4278 b4279 g30 g31 d2110 d4251 d2163 d4255
              omega
            have d4280 : (x 2 1).toNat = 1 := by
              have r4281 : (x 2 9).toNat ≤ (x 2 1).toNat := himp _ _ (hp9 2)
              have b4282 := hb (x 2 1)
              have b4283 := hb (x 2 9)
              clear * - r4281 b4282 b4283 d4271
              omega
            have d4284 : (x 3 14).toNat = 0 := by
              have r4285 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b4286 := hb (x 2 1)
              have b4287 := hb (x 3 14)
              clear * - r4285 b4286 b4287 d4280
              omega
            have d4288 : (x 3 2).toNat = 0 := by
              have r4289 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
              have b4290 := hb (x 3 2)
              have b4291 := hb (x 3 14)
              clear * - r4289 b4290 b4291 d4284
              omega
            have d4292 : (x 3 8).toNat = 0 := by
              have r4293 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e4294 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
              have e4295 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
              have e4296 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
              have e4297 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
              have e4298 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
              have e4299 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
              have b4300 := hb (x (-4) 7)
              have b4301 := hb (x (-3) 6)
              have b4302 := hb (x (-2) 5)
              have b4303 := hb (x (-1) 4)
              have b4304 := hb (x 0 11)
              have b4305 := hb (x 1 10)
              have b4306 := hb (x 2 9)
              have b4307 := hb (x 3 8)
              clear * - r4293 e4294 e4295 e4296 e4297 e4298 e4299 b4300 b4301 b4302 b4303 b4304 b4305 b4306 b4307 d4271 g12 g8
              omega
            have d4308 : (x (-1) 4).toNat = 0 := by
              have r4309 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e4310 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
              have e4311 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
              have e4312 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
              have e4313 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
              have e4314 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
              have e4315 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
              have b4316 := hb (x (-4) 7)
              have b4317 := hb (x (-3) 6)
              have b4318 := hb (x (-2) 5)
              have b4319 := hb (x (-1) 4)
              have b4320 := hb (x 0 11)
              have b4321 := hb (x 1 10)
              have b4322 := hb (x 2 9)
              have b4323 := hb (x 3 8)
              clear * - r4309 e4310 e4311 e4312 e4313 e4314 e4315 b4316 b4317 b4318 b4319 b4320 b4321 b4322 b4323 d4292 d4271 g12 g8
              omega
            have d4324 : (x 3 11).toNat = 1 := by
              have r4325 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b4326 := hb (x (-1) 4)
              have b4327 := hb (x 3 11)
              have b4328 := hb (x 2 1 && x 2 12)
              have b4329 := hb (x 1 2 && x 1 13)
              have b4330 := hb (x 0 3 && x 0 14)
              clear * - r4325 b4326 b4327 b4328 b4329 b4330 d2070 g49 g50 d4308
              omega
            have d4331 : (x 3 3).toNat = 1 := by
              have r4332 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
              have b4333 := hb (x 3 3)
              have b4334 := hb (x 3 11)
              clear * - r4332 b4333 b4334 d4324
              omega
            have d4335 : (x 6 12).toNat = 0 := by
              have r4336 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e4337 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
              have e4338 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
              have b4339 := hb (x 3 3)
              have b4340 := hb (x 4 2)
              have b4341 := hb (x 5 13)
              have b4342 := hb (x 6 12)
              clear * - r4336 e4337 e4338 b4339 b4340 b4341 b4342 d4331
              omega
            have d4343 : (x 5 13).toNat = 0 := by
              have r4344 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e4345 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
              have e4346 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
              have b4347 := hb (x 3 3)
              have b4348 := hb (x 4 2)
              have b4349 := hb (x 5 13)
              have b4350 := hb (x 6 12)
              clear * - r4344 e4345 e4346 b4347 b4348 b4349 b4350 d4335 d4331
              omega
            have d4351 : (x 4 1 && x 4 14).toNat = 1 := by
              have r4352 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b4353 := hb (x 3 2)
              have b4354 := hb (x 5 13)
              have b4355 := hb (x 4 1 && x 4 14)
              clear * - r4352 b4353 b4354 b4355 d4343 d4288
              omega
            have d4356 : (x 4 14).toNat = 1 := by
              have r4357 := hand2 (x 4 1) (x 4 14)
              have b4358 := hb (x 4 14)
              have b4359 := hb (x 4 1 && x 4 14)
              clear * - r4357 b4358 b4359 d4351
              omega
            have d4360 : (x 3 1).toNat = 0 := by
              have r4361 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b4362 := hb (x 3 1)
              have b4363 := hb (x 4 14)
              clear * - r4361 b4362 b4363 d4356
              omega
            have d4364 : (x 3 1 && x 3 11).toNat = 0 := by
              have r4365 := hand1 (x 3 1) (x 3 11)
              have b4366 := hb (x 3 1)
              have b4367 := hb (x 3 1 && x 3 11)
              clear * - r4365 b4366 b4367 d4360
              omega
            have d4368 : (x 4 10).toNat = 1 := by
              have r4369 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b4370 := hb (x (-1) 5)
              have b4371 := hb (x 4 10)
              have b4372 := hb (x 3 1 && x 3 11)
              have b4373 := hb (x 2 2 && x 2 12)
              have b4374 := hb (x 1 3 && x 1 13)
              have b4375 := hb (x 0 4 && x 0 14)
              clear * - r4369 b4370 b4371 b4372 b4373 b4374 b4375 d4364 d2074 d2094 g46 d2046
              omega
            have d4376 : (x 4 2).toNat = 1 := by
              have r4377 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
              have b4378 := hb (x 4 2)
              have b4379 := hb (x 4 10)
              clear * - r4377 b4378 b4379 d4368
              omega
            have r4380 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e4381 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
            have e4382 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
            have b4383 := hb (x 3 3)
            have b4384 := hb (x 4 2)
            have b4385 := hb (x 5 13)
            have b4386 := hb (x 6 12)
            linarith only [r4380, e4381, e4382, b4383, b4384, b4385, b4386, d4335, d4343, d4376, d4331]
        · have f4387 : (x 0 7).toNat = 1 := by rw [h2289]; rfl
          have d4388 : (x 7 8).toNat = 0 := by
            have r4389 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e4390 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
            have e4391 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
            have e4392 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
            have e4393 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
            have e4394 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
            have e4395 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
            have b4396 := hb (x 0 7)
            have b4397 := hb (x 1 6)
            have b4398 := hb (x 2 5)
            have b4399 := hb (x 3 4)
            have b4400 := hb (x 4 11)
            have b4401 := hb (x 5 10)
            have b4402 := hb (x 6 9)
            have b4403 := hb (x 7 8)
            clear * - r4389 e4390 e4391 e4392 e4393 e4394 e4395 b4396 b4397 b4398 b4399 b4400 b4401 b4402 b4403 g11 f4387
            omega
          have d4404 : (x 7 1 && x 7 8).toNat = 0 := by
            have r4405 := hand2 (x 7 1) (x 7 8)
            have b4406 := hb (x 7 8)
            have b4407 := hb (x 7 1 && x 7 8)
            clear * - r4405 b4406 b4407 d4388
            omega
          have d4408 : (x 7 3 && x 7 8).toNat = 0 := by
            have r4409 := hand2 (x 7 3) (x 7 8)
            have b4410 := hb (x 7 8)
            have b4411 := hb (x 7 3 && x 7 8)
            clear * - r4409 b4410 b4411 d4388
            omega
          have d4412 : (x 6 9).toNat = 0 := by
            have r4413 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e4414 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
            have e4415 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
            have e4416 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
            have e4417 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
            have e4418 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
            have e4419 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
            have b4420 := hb (x 0 7)
            have b4421 := hb (x 1 6)
            have b4422 := hb (x 2 5)
            have b4423 := hb (x 3 4)
            have b4424 := hb (x 4 11)
            have b4425 := hb (x 5 10)
            have b4426 := hb (x 6 9)
            have b4427 := hb (x 7 8)
            clear * - r4413 e4414 e4415 e4416 e4417 e4418 e4419 b4420 b4421 b4422 b4423 b4424 b4425 b4426 b4427 d4388 g11 f4387
            omega
          have d4428 : (x 6 2 && x 6 9).toNat = 0 := by
            have r4429 := hand2 (x 6 2) (x 6 9)
            have b4430 := hb (x 6 9)
            have b4431 := hb (x 6 2 && x 6 9)
            clear * - r4429 b4430 b4431 d4412
            omega
          have d4432 : (x 6 4 && x 6 9).toNat = 0 := by
            have r4433 := hand2 (x 6 4) (x 6 9)
            have b4434 := hb (x 6 9)
            have b4435 := hb (x 6 4 && x 6 9)
            clear * - r4433 b4434 b4435 d4412
            omega
          have d4436 : (x 5 10).toNat = 0 := by
            have r4437 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e4438 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
            have e4439 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
            have e4440 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
            have e4441 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
            have e4442 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
            have e4443 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
            have b4444 := hb (x 0 7)
            have b4445 := hb (x 1 6)
            have b4446 := hb (x 2 5)
            have b4447 := hb (x 3 4)
            have b4448 := hb (x 4 11)
            have b4449 := hb (x 5 10)
            have b4450 := hb (x 6 9)
            have b4451 := hb (x 7 8)
            clear * - r4437 e4438 e4439 e4440 e4441 e4442 e4443 b4444 b4445 b4446 b4447 b4448 b4449 b4450 b4451 d4388 d4412 g11 f4387
            omega
          have d4452 : (x 5 1 && x 5 10).toNat = 0 := by
            have r4453 := hand2 (x 5 1) (x 5 10)
            have b4454 := hb (x 5 10)
            have b4455 := hb (x 5 1 && x 5 10)
            clear * - r4453 b4454 b4455 d4436
            omega
          have d4456 : (x 5 3 && x 5 10).toNat = 0 := by
            have r4457 := hand2 (x 5 3) (x 5 10)
            have b4458 := hb (x 5 10)
            have b4459 := hb (x 5 3 && x 5 10)
            clear * - r4457 b4458 b4459 d4436
            omega
          have d4460 : (x 5 5 && x 5 10).toNat = 0 := by
            have r4461 := hand2 (x 5 5) (x 5 10)
            have b4462 := hb (x 5 10)
            have b4463 := hb (x 5 5 && x 5 10)
            clear * - r4461 b4462 b4463 d4436
            omega
          have d4464 : (x 4 11).toNat = 0 := by
            have r4465 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e4466 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
            have e4467 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
            have e4468 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
            have e4469 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
            have e4470 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
            have e4471 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
            have b4472 := hb (x 0 7)
            have b4473 := hb (x 1 6)
            have b4474 := hb (x 2 5)
            have b4475 := hb (x 3 4)
            have b4476 := hb (x 4 11)
            have b4477 := hb (x 5 10)
            have b4478 := hb (x 6 9)
            have b4479 := hb (x 7 8)
            clear * - r4465 e4466 e4467 e4468 e4469 e4470 e4471 b4472 b4473 b4474 b4475 b4476 b4477 b4478 b4479 d4388 d4412 d4436 g11 f4387
            omega
          have d4480 : (x 4 2 && x 4 11).toNat = 0 := by
            have r4481 := hand2 (x 4 2) (x 4 11)
            have b4482 := hb (x 4 11)
            have b4483 := hb (x 4 2 && x 4 11)
            clear * - r4481 b4482 b4483 d4464
            omega
          have d4484 : (x 3 3 && x 3 12).toNat = 1 := by
            have r4485 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b4486 := hb (x 0 6)
            have b4487 := hb (x 6 9)
            have b4488 := hb (x 5 1 && x 5 10)
            have b4489 := hb (x 4 2 && x 4 11)
            have b4490 := hb (x 3 3 && x 3 12)
            have b4491 := hb (x 2 4 && x 2 13)
            have b4492 := hb (x 1 5 && x 1 14)
            clear * - r4485 b4486 b4487 b4488 b4489 b4490 b4491 b4492 d4412 d4452 d4480 d2082 g38 f2280
            omega
          have d4493 : (x 3 12).toNat = 1 := by
            have r4494 := hand2 (x 3 3) (x 3 12)
            have b4495 := hb (x 3 12)
            have b4496 := hb (x 3 3 && x 3 12)
            clear * - r4494 b4495 b4496 d4484
            omega
          have d4497 : (x 2 13).toNat = 0 := by
            have r4498 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e4499 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
            have e4500 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
            have b4501 := hb (x 0 3)
            have b4502 := hb (x 1 2)
            have b4503 := hb (x 2 13)
            have b4504 := hb (x 3 12)
            clear * - r4498 e4499 e4500 b4501 b4502 b4503 b4504 d4493 g9 g5
            omega
          have d4505 : (x 2 6 && x 2 13).toNat = 0 := by
            have r4506 := hand2 (x 2 6) (x 2 13)
            have b4507 := hb (x 2 13)
            have b4508 := hb (x 2 6 && x 2 13)
            clear * - r4506 b4507 b4508 d4497
            omega
          have d4509 : (x 2 8 && x 2 13).toNat = 0 := by
            have r4510 := hand2 (x 2 8) (x 2 13)
            have b4511 := hb (x 2 13)
            have b4512 := hb (x 2 8 && x 2 13)
            clear * - r4510 b4511 b4512 d4497
            omega
          have d4513 : (x 2 5).toNat = 0 := by
            have r4514 : (x 2 5).toNat ≤ (x 2 13).toNat := himp _ _ (hp5 2)
            have b4515 := hb (x 2 5)
            have b4516 := hb (x 2 13)
            clear * - r4514 b4515 b4516 d4497
            omega
          have d4517 : (x 2 5 && x 2 14).toNat = 0 := by
            have r4518 := hand1 (x 2 5) (x 2 14)
            have b4519 := hb (x 2 5)
            have b4520 := hb (x 2 5 && x 2 14)
            clear * - r4518 b4519 b4520 d4513
            omega
          have d4521 : (x 3 3).toNat = 1 := by
            have r4522 := hand1 (x 3 3) (x 3 12)
            have b4523 := hb (x 3 3)
            have b4524 := hb (x 3 3 && x 3 12)
            clear * - r4522 b4523 b4524 d4484
            omega
          have d4525 : (x 6 12).toNat = 0 := by
            have r4526 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e4527 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
            have e4528 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
            have b4529 := hb (x 3 3)
            have b4530 := hb (x 4 2)
            have b4531 := hb (x 5 13)
            have b4532 := hb (x 6 12)
            clear * - r4526 e4527 e4528 b4529 b4530 b4531 b4532 d4521
            omega
          have d4533 : (x 6 1 && x 6 12).toNat = 0 := by
            have r4534 := hand2 (x 6 1) (x 6 12)
            have b4535 := hb (x 6 12)
            have b4536 := hb (x 6 1 && x 6 12)
            clear * - r4534 b4535 b4536 d4525
            omega
          have d4537 : (x 6 4).toNat = 0 := by
            have r4538 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
            have b4539 := hb (x 6 4)
            have b4540 := hb (x 6 12)
            clear * - r4538 b4539 b4540 d4525
            omega
          have d4541 : (x 5 13).toNat = 0 := by
            have r4542 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e4543 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
            have e4544 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
            have b4545 := hb (x 3 3)
            have b4546 := hb (x 4 2)
            have b4547 := hb (x 5 13)
            have b4548 := hb (x 6 12)
            clear * - r4542 e4543 e4544 b4545 b4546 b4547 b4548 d4525 d4521
            omega
          have d4549 : (x 5 2 && x 5 13).toNat = 0 := by
            have r4550 := hand2 (x 5 2) (x 5 13)
            have b4551 := hb (x 5 13)
            have b4552 := hb (x 5 2 && x 5 13)
            clear * - r4550 b4551 b4552 d4541
            omega
          have d4553 : (x 5 5).toNat = 0 := by
            have r4554 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
            have b4555 := hb (x 5 5)
            have b4556 := hb (x 5 13)
            clear * - r4554 b4555 b4556 d4541
            omega
          have d4557 : (x 4 2).toNat = 0 := by
            have r4558 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e4559 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
            have e4560 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
            have b4561 := hb (x 3 3)
            have b4562 := hb (x 4 2)
            have b4563 := hb (x 5 13)
            have b4564 := hb (x 6 12)
            clear * - r4558 e4559 e4560 b4561 b4562 b4563 b4564 d4525 d4541 d4521
            omega
          have d4565 : (x 4 10).toNat = 0 := by
            have r4566 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
            have b4567 := hb (x 4 2)
            have b4568 := hb (x 4 10)
            clear * - r4566 b4567 b4568 d4557
            omega
          have d4569 : (x 3 1 && x 3 11).toNat = 1 := by
            have r4570 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b4571 := hb (x (-1) 5)
            have b4572 := hb (x 4 10)
            have b4573 := hb (x 3 1 && x 3 11)
            have b4574 := hb (x 2 2 && x 2 12)
            have b4575 := hb (x 1 3 && x 1 13)
            have b4576 := hb (x 0 4 && x 0 14)
            clear * - r4570 b4571 b4572 b4573 b4574 b4575 b4576 d4565 d2074 d2094 g46 d2046
            omega
          have d4577 : (x 3 1).toNat = 1 := by
            have r4578 := hand1 (x 3 1) (x 3 11)
            have b4579 := hb (x 3 1)
            have b4580 := hb (x 3 1 && x 3 11)
            clear * - r4578 b4579 b4580 d4569
            omega
          have d4581 : (x 4 14).toNat = 0 := by
            have r4582 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b4583 := hb (x 3 1)
            have b4584 := hb (x 4 14)
            clear * - r4582 b4583 b4584 d4577
            omega
          have d4585 : (x 4 1 && x 4 14).toNat = 0 := by
            have r4586 := hand2 (x 4 1) (x 4 14)
            have b4587 := hb (x 4 14)
            have b4588 := hb (x 4 1 && x 4 14)
            clear * - r4586 b4587 b4588 d4581
            omega
          have d4589 : (x 3 2).toNat = 1 := by
            have r4590 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b4591 := hb (x 3 2)
            have b4592 := hb (x 5 13)
            have b4593 := hb (x 4 1 && x 4 14)
            clear * - r4590 b4591 b4592 b4593 d4541 d4585
            omega
          have d4594 : (x 3 14).toNat = 1 := by
            have r4595 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
            have b4596 := hb (x 3 2)
            have b4597 := hb (x 3 14)
            clear * - r4595 b4596 b4597 d4589
            omega
          have d4598 : (x 2 1).toNat = 0 := by
            have r4599 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b4600 := hb (x 2 1)
            have b4601 := hb (x 3 14)
            clear * - r4599 b4600 b4601 d4594
            omega
          have d4602 : (x 2 1 && x 2 14).toNat = 0 := by
            have r4603 := hand1 (x 2 1) (x 2 14)
            have b4604 := hb (x 2 1)
            have b4605 := hb (x 2 1 && x 2 14)
            clear * - r4603 b4604 b4605 d4598
            omega
          have d4606 : (x 3 13).toNat = 1 := by
            have r4607 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b4608 := hb (x 1 2)
            have b4609 := hb (x 3 13)
            have b4610 := hb (x 2 1 && x 2 14)
            clear * - r4607 b4608 b4609 b4610 d4602 g9
            omega
          have d4611 : (x 4 12).toNat = 0 := by
            have r4612 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e4613 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e4614 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b4615 := hb (x 1 3)
            have b4616 := hb (x 2 2)
            have b4617 := hb (x 3 13)
            have b4618 := hb (x 4 12)
            clear * - r4612 e4613 e4614 b4615 b4616 b4617 b4618 d4606
            omega
          have d4619 : (x 4 3 && x 4 12).toNat = 0 := by
            have r4620 := hand2 (x 4 3) (x 4 12)
            have b4621 := hb (x 4 12)
            have b4622 := hb (x 4 3 && x 4 12)
            clear * - r4620 b4621 b4622 d4611
            omega
          have d4623 : (x 4 4).toNat = 0 := by
            have r4624 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
            have b4625 := hb (x 4 4)
            have b4626 := hb (x 4 12)
            clear * - r4624 b4625 b4626 d4611
            omega
          have d4627 : (x 4 4 && x 4 11).toNat = 0 := by
            have r4628 := hand1 (x 4 4) (x 4 11)
            have b4629 := hb (x 4 4)
            have b4630 := hb (x 4 4 && x 4 11)
            clear * - r4628 b4629 b4630 d4623
            omega
          have d4631 : (x 2 9).toNat = 0 := by
            have r4632 : (x 2 9).toNat ≤ (x 2 1).toNat := himp _ _ (hp9 2)
            have b4633 := hb (x 2 1)
            have b4634 := hb (x 2 9)
            clear * - r4632 b4633 b4634 d4598
            omega
          have d4635 : (x 4 3 && x 4 14).toNat = 0 := by
            have r4636 := hand2 (x 4 3) (x 4 14)
            have b4637 := hb (x 4 14)
            have b4638 := hb (x 4 3 && x 4 14)
            clear * - r4636 b4637 b4638 d4581
            omega
          have d4639 : (x 4 6).toNat = 0 := by
            have r4640 : (x 4 6).toNat ≤ (x 4 14).toNat := himp _ _ (hp6 4)
            have b4641 := hb (x 4 6)
            have b4642 := hb (x 4 14)
            clear * - r4640 b4641 b4642 d4581
            omega
          have d4643 : (x 4 6 && x 4 11).toNat = 0 := by
            have r4644 := hand1 (x 4 6) (x 4 11)
            have b4645 := hb (x 4 6)
            have b4646 := hb (x 4 6 && x 4 11)
            clear * - r4644 b4645 b4646 d4639
            omega
          have d4647 : (x 3 4).toNat = 0 := by
            have r4648 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e4649 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
            have e4650 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
            have e4651 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
            have e4652 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
            have e4653 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
            have e4654 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
            have b4655 := hb (x 0 7)
            have b4656 := hb (x 1 6)
            have b4657 := hb (x 2 5)
            have b4658 := hb (x 3 4)
            have b4659 := hb (x 4 11)
            have b4660 := hb (x 5 10)
            have b4661 := hb (x 6 9)
            have b4662 := hb (x 7 8)
            clear * - r4648 e4649 e4650 e4651 e4652 e4653 e4654 b4655 b4656 b4657 b4658 b4659 b4660 b4661 b4662 d4388 d4412 d4436 d4464 d4513 g11 f4387
            omega
          have d4663 : (x 3 4 && x 3 13).toNat = 0 := by
            have r4664 := hand1 (x 3 4) (x 3 13)
            have b4665 := hb (x 3 4)
            have b4666 := hb (x 3 4 && x 3 13)
            clear * - r4664 b4665 b4666 d4647
            omega
          have d4667 : (x 7 11).toNat = 1 := by
            have r4668 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b4669 := hb (x 3 4)
            have b4670 := hb (x 7 11)
            have b4671 := hb (x 6 1 && x 6 12)
            have b4672 := hb (x 5 2 && x 5 13)
            have b4673 := hb (x 4 3 && x 4 14)
            clear * - r4668 b4669 b4670 b4671 b4672 b4673 d4533 d4549 d4635 d4647
            omega
          have d4674 : (x 7 3).toNat = 1 := by
            have r4675 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
            have b4676 := hb (x 7 3)
            have b4677 := hb (x 7 11)
            clear * - r4675 b4676 b4677 d4667
            omega
          have d4678 : (x 10 12).toNat = 0 := by
            have r4679 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e4680 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
            have e4681 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
            have b4682 := hb (x 7 3)
            have b4683 := hb (x 8 2)
            have b4684 := hb (x 9 13)
            have b4685 := hb (x 10 12)
            clear * - r4679 e4680 e4681 b4682 b4683 b4684 b4685 d4674
            omega
          have d4686 : (x 9 13).toNat = 0 := by
            have r4687 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e4688 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
            have e4689 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
            have b4690 := hb (x 7 3)
            have b4691 := hb (x 8 2)
            have b4692 := hb (x 9 13)
            have b4693 := hb (x 10 12)
            clear * - r4687 e4688 e4689 b4690 b4691 b4692 b4693 d4678 d4674
            omega
          have d4694 : (x 8 2).toNat = 0 := by
            have r4695 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e4696 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
            have e4697 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
            have b4698 := hb (x 7 3)
            have b4699 := hb (x 8 2)
            have b4700 := hb (x 9 13)
            have b4701 := hb (x 10 12)
            clear * - r4695 e4696 e4697 b4698 b4699 b4700 b4701 d4678 d4686 d4674
            omega
          have d4702 : (x 8 2 && x 8 7).toNat = 0 := by
            have r4703 := hand1 (x 8 2) (x 8 7)
            have b4704 := hb (x 8 2)
            have b4705 := hb (x 8 2 && x 8 7)
            clear * - r4703 b4704 b4705 d4694
            omega
          have d4706 : (x 8 10).toNat = 0 := by
            have r4707 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
            have b4708 := hb (x 8 2)
            have b4709 := hb (x 8 10)
            clear * - r4707 b4708 b4709 d4694
            omega
          have d4710 : (x 10 8).toNat = 0 := by
            have r4711 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e4712 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
            have e4713 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
            have e4714 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
            have e4715 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
            have e4716 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
            have e4717 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
            have b4718 := hb (x 3 7)
            have b4719 := hb (x 4 6)
            have b4720 := hb (x 5 5)
            have b4721 := hb (x 6 4)
            have b4722 := hb (x 7 11)
            have b4723 := hb (x 8 10)
            have b4724 := hb (x 9 9)
            have b4725 := hb (x 10 8)
            clear * - r4711 e4712 e4713 e4714 e4715 e4716 e4717 b4718 b4719 b4720 b4721 b4722 b4723 b4724 b4725 d4706 d4667 d4537 d4553 d4639
            omega
          have d4726 : (x 9 9).toNat = 0 := by
            have r4727 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e4728 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
            have e4729 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
            have e4730 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
            have e4731 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
            have e4732 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
            have e4733 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
            have b4734 := hb (x 3 7)
            have b4735 := hb (x 4 6)
            have b4736 := hb (x 5 5)
            have b4737 := hb (x 6 4)
            have b4738 := hb (x 7 11)
            have b4739 := hb (x 8 10)
            have b4740 := hb (x 9 9)
            have b4741 := hb (x 10 8)
            clear * - r4727 e4728 e4729 e4730 e4731 e4732 e4733 b4734 b4735 b4736 b4737 b4738 b4739 b4740 b4741 d4710 d4706 d4667 d4537 d4553 d4639
            omega
          have d4742 : (x 3 7).toNat = 0 := by
            have r4743 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e4744 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
            have e4745 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
            have e4746 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
            have e4747 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
            have e4748 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
            have e4749 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
            have b4750 := hb (x 3 7)
            have b4751 := hb (x 4 6)
            have b4752 := hb (x 5 5)
            have b4753 := hb (x 6 4)
            have b4754 := hb (x 7 11)
            have b4755 := hb (x 8 10)
            have b4756 := hb (x 9 9)
            have b4757 := hb (x 10 8)
            clear * - r4743 e4744 e4745 e4746 e4747 e4748 e4749 b4750 b4751 b4752 b4753 b4754 b4755 b4756 b4757 d4710 d4726 d4706 d4667 d4537 d4553 d4639
            omega
          have d4758 : (x 3 7 && x 3 12).toNat = 0 := by
            have r4759 := hand1 (x 3 7) (x 3 12)
            have b4760 := hb (x 3 7)
            have b4761 := hb (x 3 7 && x 3 12)
            clear * - r4759 b4760 b4761 d4742
            omega
          have r4762 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4763 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
          have e4764 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
          have e4765 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
          have e4766 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
          have e4767 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
          have e4768 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
          have r4769 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4770 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e4771 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e4772 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e4773 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e4774 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e4775 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have r4776 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4777 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
          have e4778 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
          have e4779 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
          have e4780 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
          have e4781 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
          have e4782 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
          have r4783 : 1 ≤ (x 10 5).toNat + (x 9 1 && x 9 6).toNat + (x 8 2 && x 8 7).toNat + (x 7 3 && x 7 8).toNat + (x 6 4 && x 6 9).toNat + (x 5 5 && x 5 10).toNat + (x 4 6 && x 4 11).toNat + (x 3 7 && x 3 12).toNat + (x 2 8 && x 2 13).toNat + (x 1 9 && x 1 14).toNat + (x 0 10).toNat := by have q := hcov5 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r4784 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := by have q := hcov7 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r4785 : 1 ≤ (x 2 9).toNat + (x 1 1 && x 1 10).toNat + (x 0 2 && x 0 11).toNat + (x (-1) 3 && x (-1) 12).toNat + (x (-2) 4 && x (-2) 13).toNat + (x (-3) 5 && x (-3) 14).toNat + (x (-4) 6).toNat := by have q := hcov9 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r4786 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r4787 := hand2 (x 9 1) (x 9 6)
          have r4788 := hand1 (x 3 5) (x 3 12)
          have r4789 := hand1 (x (-2) 4) (x (-2) 13)
          have r4790 := hand2 (x 6 1) (x 6 10)
          have r4791 := hand2 (x 5 2) (x 5 11)
          linarith only [r4762, e4763, e4764, e4765, e4766, e4767, e4768, r4769, e4770, e4771, e4772, e4773, e4774, e4775, r4776, e4777, e4778, e4779, e4780, e4781, e4782, r4783, r4784, r4785, r4786, r4787, r4788, r4789, r4790, r4791, d2159, d2114, f2282, g11, d4631, d4623, d4702, d4408, d4432, d4460, d4643, d4758, d4509, g24, d4404, d4428, d4456, d4627, d4505, g27, g30, g31, d2110, d2163, d4619, d4663, d4517]
      · have f4845 : (x 0 9).toNat = 1 := by rw [h2283]; rfl
        have d4846 : (x 1 8).toNat = 0 := by
          have r4847 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4848 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e4849 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e4850 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e4851 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e4852 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e4853 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b4854 := hb (x (-6) 7)
          have b4855 := hb (x (-5) 6)
          have b4856 := hb (x (-4) 5)
          have b4857 := hb (x (-3) 4)
          have b4858 := hb (x (-2) 11)
          have b4859 := hb (x (-1) 10)
          have b4860 := hb (x 0 9)
          have b4861 := hb (x 1 8)
          clear * - r4847 e4848 e4849 e4850 e4851 e4852 e4853 b4854 b4855 b4856 b4857 b4858 b4859 b4860 b4861 f4845 g3 g1
          omega
        have d4862 : (x (-3) 4).toNat = 0 := by
          have r4863 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4864 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e4865 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e4866 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e4867 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e4868 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e4869 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b4870 := hb (x (-6) 7)
          have b4871 := hb (x (-5) 6)
          have b4872 := hb (x (-4) 5)
          have b4873 := hb (x (-3) 4)
          have b4874 := hb (x (-2) 11)
          have b4875 := hb (x (-1) 10)
          have b4876 := hb (x 0 9)
          have b4877 := hb (x 1 8)
          clear * - r4863 e4864 e4865 e4866 e4867 e4868 e4869 b4870 b4871 b4872 b4873 b4874 b4875 b4876 b4877 d4846 f4845 g3 g1
          omega
        have d4878 : (x (-3) 4 && x (-3) 14).toNat = 0 := by
          have r4879 := hand1 (x (-3) 4) (x (-3) 14)
          have b4880 := hb (x (-3) 4)
          have b4881 := hb (x (-3) 4 && x (-3) 14)
          clear * - r4879 b4880 b4881 d4862
          omega
        have d4882 : (x (-4) 5).toNat = 1 := by
          have r4883 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4884 := hb (x (-4) 5)
          have b4885 := hb (x 1 10)
          have b4886 := hb (x 0 1 && x 0 11)
          have b4887 := hb (x (-1) 2 && x (-1) 12)
          have b4888 := hb (x (-2) 3 && x (-2) 13)
          have b4889 := hb (x (-3) 4 && x (-3) 14)
          clear * - r4883 b4884 b4885 b4886 b4887 b4888 b4889 g12 g40 g41 g42 d4878
          omega
        have r4890 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e4891 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
        have e4892 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
        have e4893 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
        have e4894 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
        have e4895 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
        have e4896 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
        have b4897 := hb (x (-6) 7)
        have b4898 := hb (x (-5) 6)
        have b4899 := hb (x (-4) 5)
        have b4900 := hb (x (-3) 4)
        have b4901 := hb (x (-2) 11)
        have b4902 := hb (x (-1) 10)
        have b4903 := hb (x 0 9)
        have b4904 := hb (x 1 8)
        linarith only [r4890, e4891, e4892, e4893, e4894, e4895, e4896, b4897, b4898, b4899, b4900, b4901, b4902, b4903, b4904, d4846, f4845, g3, g1, d4862, d4882]
    · have f4905 : (x 0 8).toNat = 1 := by rw [h2281]; rfl
      have d4906 : (x (-2) 10).toNat = 0 := by
        have r4907 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e4908 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
        have e4909 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
        have e4910 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
        have e4911 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
        have e4912 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
        have e4913 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
        have b4914 := hb (x (-7) 7)
        have b4915 := hb (x (-6) 6)
        have b4916 := hb (x (-5) 5)
        have b4917 := hb (x (-4) 4)
        have b4918 := hb (x (-3) 11)
        have b4919 := hb (x (-2) 10)
        have b4920 := hb (x (-1) 9)
        have b4921 := hb (x 0 8)
        clear * - r4907 e4908 e4909 e4910 e4911 e4912 e4913 b4914 b4915 b4916 b4917 b4918 b4919 b4920 b4921 f4905 d2058
        omega
      have d4922 : (x (-3) 11).toNat = 0 := by
        have r4923 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e4924 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
        have e4925 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
        have e4926 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
        have e4927 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
        have e4928 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
        have e4929 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
        have b4930 := hb (x (-7) 7)
        have b4931 := hb (x (-6) 6)
        have b4932 := hb (x (-5) 5)
        have b4933 := hb (x (-4) 4)
        have b4934 := hb (x (-3) 11)
        have b4935 := hb (x (-2) 10)
        have b4936 := hb (x (-1) 9)
        have b4937 := hb (x 0 8)
        clear * - r4923 e4924 e4925 e4926 e4927 e4928 e4929 b4930 b4931 b4932 b4933 b4934 b4935 b4936 b4937 f4905 d2058 d4906
        omega
      have d4938 : (x (-4) 4).toNat = 0 := by
        have r4939 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e4940 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
        have e4941 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
        have e4942 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
        have e4943 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
        have e4944 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
        have e4945 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
        have b4946 := hb (x (-7) 7)
        have b4947 := hb (x (-6) 6)
        have b4948 := hb (x (-5) 5)
        have b4949 := hb (x (-4) 4)
        have b4950 := hb (x (-3) 11)
        have b4951 := hb (x (-2) 10)
        have b4952 := hb (x (-1) 9)
        have b4953 := hb (x 0 8)
        clear * - r4939 e4940 e4941 e4942 e4943 e4944 e4945 b4946 b4947 b4948 b4949 b4950 b4951 b4952 b4953 f4905 d2058 d4906 d4922
        omega
      have d4954 : (x (-4) 4 && x (-4) 14).toNat = 0 := by
        have r4955 := hand1 (x (-4) 4) (x (-4) 14)
        have b4956 := hb (x (-4) 4)
        have b4957 := hb (x (-4) 4 && x (-4) 14)
        clear * - r4955 b4956 b4957 d4938
        omega
      have d4958 : (x (-5) 5).toNat = 0 := by
        have r4959 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e4960 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
        have e4961 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
        have e4962 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
        have e4963 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
        have e4964 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
        have e4965 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
        have b4966 := hb (x (-7) 7)
        have b4967 := hb (x (-6) 6)
        have b4968 := hb (x (-5) 5)
        have b4969 := hb (x (-4) 4)
        have b4970 := hb (x (-3) 11)
        have b4971 := hb (x (-2) 10)
        have b4972 := hb (x (-1) 9)
        have b4973 := hb (x 0 8)
        clear * - r4959 e4960 e4961 e4962 e4963 e4964 e4965 b4966 b4967 b4968 b4969 b4970 b4971 b4972 b4973 f4905 d2058 d4906 d4922 d4938
        omega
      have r4974 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e4975 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e4976 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e4977 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e4978 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e4979 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e4980 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have r4981 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e4982 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e4983 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e4984 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e4985 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e4986 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e4987 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have r4988 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e4989 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
      have e4990 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
      have e4991 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
      have e4992 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
      have e4993 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
      have e4994 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
      have r4995 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e4996 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e4997 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have r4998 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r4999 : 1 ≤ (x 2 9).toNat + (x 1 1 && x 1 10).toNat + (x 0 2 && x 0 11).toNat + (x (-1) 3 && x (-1) 12).toNat + (x (-2) 4 && x (-2) 13).toNat + (x (-3) 5 && x (-3) 14).toNat + (x (-4) 6).toNat := by have q := hcov9 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r5000 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r5001 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r5002 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r5003 := hand2 (x 0 1) (x 0 10)
      have r5004 := hand1 (x (-4) 5) (x (-4) 14)
      have r5005 := hand1 (x (-2) 4) (x (-2) 13)
      have r5006 := hand1 (x (-2) 5) (x (-2) 14)
      have r5007 := hand1 (x (-2) 2) (x (-2) 12)
      have r5008 := hand2 (x 0 1) (x 0 12)
      linarith only [r4974, e4975, e4976, e4977, e4978, e4979, e4980, r4981, e4982, e4983, e4984, e4985, e4986, e4987, r4988, e4989, e4990, e4991, e4992, e4993, e4994, r4995, e4996, e4997, r4998, r4999, r5000, r5001, r5002, r5003, r5004, r5005, r5006, r5007, r5008, d4958, d2159, g1, g3, d2114, d2038, g8, g12, d2235, d2191, g28, g29, d2151, g30, g31, d2110, d2163, d2227, g32, g33, d2042, d2030, d2147, d4954, g47, g48]
  · have f5062 : (x 0 6).toNat = 1 := by rw [h2279]; rfl
    have d5063 : (x 6 8).toNat = 0 := by
      have r5064 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5065 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e5066 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e5067 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e5068 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e5069 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e5070 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b5071 := hb (x (-1) 7)
      have b5072 := hb (x 0 6)
      have b5073 := hb (x 1 5)
      have b5074 := hb (x 2 4)
      have b5075 := hb (x 3 11)
      have b5076 := hb (x 4 10)
      have b5077 := hb (x 5 9)
      have b5078 := hb (x 6 8)
      clear * - r5064 e5065 e5066 e5067 e5068 e5069 e5070 b5071 b5072 b5073 b5074 b5075 b5076 b5077 b5078 d2078 d2098 f5062
      omega
    have d5079 : (x 5 9).toNat = 0 := by
      have r5080 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5081 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e5082 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e5083 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e5084 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e5085 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e5086 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b5087 := hb (x (-1) 7)
      have b5088 := hb (x 0 6)
      have b5089 := hb (x 1 5)
      have b5090 := hb (x 2 4)
      have b5091 := hb (x 3 11)
      have b5092 := hb (x 4 10)
      have b5093 := hb (x 5 9)
      have b5094 := hb (x 6 8)
      clear * - r5080 e5081 e5082 e5083 e5084 e5085 e5086 b5087 b5088 b5089 b5090 b5091 b5092 b5093 b5094 d5063 d2078 d2098 f5062
      omega
    have d5095 : (x 4 10).toNat = 0 := by
      have r5096 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5097 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e5098 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e5099 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e5100 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e5101 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e5102 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b5103 := hb (x (-1) 7)
      have b5104 := hb (x 0 6)
      have b5105 := hb (x 1 5)
      have b5106 := hb (x 2 4)
      have b5107 := hb (x 3 11)
      have b5108 := hb (x 4 10)
      have b5109 := hb (x 5 9)
      have b5110 := hb (x 6 8)
      clear * - r5096 e5097 e5098 e5099 e5100 e5101 e5102 b5103 b5104 b5105 b5106 b5107 b5108 b5109 b5110 d5063 d5079 d2078 d2098 f5062
      omega
    have d5111 : (x 3 1 && x 3 11).toNat = 1 := by
      have r5112 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5113 := hb (x (-1) 5)
      have b5114 := hb (x 4 10)
      have b5115 := hb (x 3 1 && x 3 11)
      have b5116 := hb (x 2 2 && x 2 12)
      have b5117 := hb (x 1 3 && x 1 13)
      have b5118 := hb (x 0 4 && x 0 14)
      clear * - r5112 b5113 b5114 b5115 b5116 b5117 b5118 d5095 d2074 d2094 g46 d2046
      omega
    have d5119 : (x 3 11).toNat = 1 := by
      have r5120 := hand2 (x 3 1) (x 3 11)
      have b5121 := hb (x 3 11)
      have b5122 := hb (x 3 1 && x 3 11)
      clear * - r5120 b5121 b5122 d5111
      omega
    have r5123 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e5124 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e5125 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e5126 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e5127 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e5128 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e5129 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b5130 := hb (x (-1) 7)
    have b5131 := hb (x 0 6)
    have b5132 := hb (x 1 5)
    have b5133 := hb (x 2 4)
    have b5134 := hb (x 3 11)
    have b5135 := hb (x 4 10)
    have b5136 := hb (x 5 9)
    have b5137 := hb (x 6 8)
    linarith only [r5123, e5124, e5125, e5126, e5127, e5128, e5129, b5130, b5131, b5132, b5133, b5134, b5135, b5136, b5137, d5063, d5079, d5095, d5119, d2078, d2098, f5062]

theorem cycle_power_fifteen_tight_type_sequence_four_iff_five_core_b01 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-2) 7).toNat = 0)
    (g1 : (x (-2) 11).toNat = 0)
    (g2 : (x (-1) 6).toNat = 0)
    (g3 : (x (-1) 10).toNat = 0)
    (g4 : (x 0 2).toNat = 1)
    (g5 : (x 0 3).toNat = 0)
    (g6 : (x 0 4).toNat = 0)
    (g7 : (x 0 5).toNat = 1)
    (g8 : (x 0 11).toNat = 0)
    (g9 : (x 1 2).toNat = 0)
    (g10 : (x 1 4).toNat = 0)
    (g11 : (x 1 6).toNat = 0)
    (g12 : (x 1 10).toNat = 0)
    (g13 : (x 3 10).toNat = 0)
    (g14 : (x 4 9).toNat = 0)
    (g15 : (x (-1) 10 && x (-1) 13).toNat = 0)
    (g16 : (x (-2) 11 && x (-2) 14).toNat = 0)
    (g17 : (x 0 4 && x 0 8).toNat = 0)
    (g18 : (x 0 4 && x 0 9).toNat = 0)
    (g19 : (x (-1) 5 && x (-1) 10).toNat = 0)
    (g20 : (x (-2) 6 && x (-2) 11).toNat = 0)
    (g21 : (x 1 4 && x 1 9).toNat = 0)
    (g22 : (x (-1) 6 && x (-1) 11).toNat = 0)
    (g23 : (x (-2) 7 && x (-2) 12).toNat = 0)
    (g24 : (x 1 9 && x 1 14).toNat = 0)
    (g25 : (x 5 8 && x 5 13).toNat = 0)
    (g26 : (x 4 9 && x 4 14).toNat = 0)
    (g27 : (x 1 7 && x 1 14).toNat = 0)
    (g28 : (x (-1) 2 && x (-1) 11).toNat = 0)
    (g29 : (x (-2) 3 && x (-2) 12).toNat = 0)
    (g30 : (x 1 1 && x 1 10).toNat = 0)
    (g31 : (x 0 2 && x 0 11).toNat = 0)
    (g32 : (x 1 2 && x 1 11).toNat = 0)
    (g33 : (x 0 3 && x 0 12).toNat = 0)
    (g34 : (x 3 1 && x 3 10).toNat = 0)
    (g35 : (x 2 2 && x 2 11).toNat = 0)
    (g36 : (x 1 3 && x 1 12).toNat = 0)
    (g37 : (x 0 4 && x 0 13).toNat = 0)
    (g38 : (x 1 5 && x 1 14).toNat = 0)
    (g39 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g40 : (x 0 1 && x 0 11).toNat = 0)
    (g41 : (x (-1) 2 && x (-1) 12).toNat = 0)
    (g42 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g43 : (x 2 1 && x 2 11).toNat = 0)
    (g44 : (x 1 2 && x 1 12).toNat = 0)
    (g45 : (x 0 3 && x 0 13).toNat = 0)
    (g46 : (x 0 4 && x 0 14).toNat = 0)
    (g47 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g48 : (x (-2) 3 && x (-2) 14).toNat = 0)
    (g49 : (x 1 2 && x 1 13).toNat = 0)
    (g50 : (x 0 3 && x 0 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_four_iff_five_core_b01_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50
