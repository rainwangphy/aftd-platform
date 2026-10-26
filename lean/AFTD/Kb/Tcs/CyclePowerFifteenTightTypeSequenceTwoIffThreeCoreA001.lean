import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a001

Topic: combinatorics   Node: a8dfbb383c1c

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP; the same generator on the same window refutes x(0,2) != x(0,3) (a case-split tree of 109 + 3 nodes).

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_two_iff_three_core: under the layer-free tight-cover constraints for k = 15 and 30 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a001_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 5).toNat = 0)
    (g1 : (x (-3) 9).toNat = 0)
    (g2 : (x (-3) 11).toNat = 0)
    (g3 : (x (-3) 13).toNat = 0)
    (g4 : (x (-1) 3).toNat = 0)
    (g5 : (x (-1) 5).toNat = 0)
    (g6 : (x (-1) 9).toNat = 0)
    (g7 : (x (-1) 11).toNat = 0)
    (g8 : (x 0 2).toNat = 1)
    (g9 : (x 0 8).toNat = 1)
    (g10 : (x 0 11).toNat = 0)
    (g11 : (x 1 5).toNat = 0)
    (g12 : (x 1 13).toNat = 0)
    (g13 : (x 2 4).toNat = 0)
    (g14 : (x (-1) 3 && x (-1) 7).toNat = 0)
    (g15 : (x (-3) 5 && x (-3) 9).toNat = 0)
    (g16 : (x (-3) 4 && x (-3) 9).toNat = 0)
    (g17 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g18 : (x 0 2 && x 0 12).toNat = 0)
    (g19 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g20 : (x 2 2 && x 2 12).toNat = 0)
    (g21 : (x 1 3 && x 1 13).toNat = 0)
    (g22 : (x 0 4 && x 0 14).toNat = 0)
    (g23 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g24 : (x (-3) 3 && x (-3) 14).toNat = 0)
    (g25 : (x 0 1 && x 0 12).toNat = 0)
    (g26 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g27 : (x 2 1 && x 2 12).toNat = 0)
    (g28 : (x 1 2 && x 1 13).toNat = 0)
    (g29 : (x 0 3 && x 0 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d8024 : (x (-2) 10).toNat = 0 := by
    have r8025 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8026 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e8027 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e8028 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e8029 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e8030 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e8031 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b8032 := hb (x (-7) 7)
    have b8033 := hb (x (-6) 6)
    have b8034 := hb (x (-5) 5)
    have b8035 := hb (x (-4) 4)
    have b8036 := hb (x (-3) 11)
    have b8037 := hb (x (-2) 10)
    have b8038 := hb (x (-1) 9)
    have b8039 := hb (x 0 8)
    clear * - r8025 e8026 e8027 e8028 e8029 e8030 e8031 b8032 b8033 b8034 b8035 b8036 b8037 b8038 b8039 g9 g6 g2
    omega
  have d8040 : (x (-4) 4).toNat = 0 := by
    have r8041 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8042 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e8043 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e8044 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e8045 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e8046 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e8047 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b8048 := hb (x (-7) 7)
    have b8049 := hb (x (-6) 6)
    have b8050 := hb (x (-5) 5)
    have b8051 := hb (x (-4) 4)
    have b8052 := hb (x (-3) 11)
    have b8053 := hb (x (-2) 10)
    have b8054 := hb (x (-1) 9)
    have b8055 := hb (x 0 8)
    clear * - r8041 e8042 e8043 e8044 e8045 e8046 e8047 b8048 b8049 b8050 b8051 b8052 b8053 b8054 b8055 g9 g6 d8024 g2
    omega
  have d8056 : (x (-2) 2 && x (-2) 13).toNat = 1 := by
    have r8057 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8058 := hb (x (-4) 4)
    have b8059 := hb (x 0 11)
    have b8060 := hb (x (-1) 1 && x (-1) 12)
    have b8061 := hb (x (-2) 2 && x (-2) 13)
    have b8062 := hb (x (-3) 3 && x (-3) 14)
    clear * - r8057 b8058 b8059 b8060 b8061 b8062 g10 g23 g24 d8040
    omega
  have d8063 : (x (-2) 13).toNat = 1 := by
    have r8064 := hand2 (x (-2) 2) (x (-2) 13)
    have b8065 := hb (x (-2) 13)
    have b8066 := hb (x (-2) 2 && x (-2) 13)
    clear * - r8064 b8065 b8066 d8056
    omega
  have d8067 : (x (-2) 1).toNat = 1 := by
    have r8068 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
    have b8069 := hb (x (-2) 1)
    have b8070 := hb (x (-2) 13)
    clear * - r8068 b8069 b8070 d8063
    omega
  have d8071 : (x (-1) 14).toNat = 0 := by
    have r8072 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8073 := hb (x (-2) 1)
    have b8074 := hb (x (-1) 14)
    clear * - r8072 b8073 b8074 d8067
    omega
  have d8075 : (x (-1) 2).toNat = 0 := by
    have r8076 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
    have b8077 := hb (x (-1) 2)
    have b8078 := hb (x (-1) 14)
    clear * - r8076 b8077 b8078 d8071
    omega
  have d8079 : (x (-1) 2 && x (-1) 7).toNat = 0 := by
    have r8080 := hand1 (x (-1) 2) (x (-1) 7)
    have b8081 := hb (x (-1) 2)
    have b8082 := hb (x (-1) 2 && x (-1) 7)
    clear * - r8080 b8081 b8082 d8075
    omega
  have d8083 : (x 0 1 && x 0 14).toNat = 1 := by
    have r8084 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8085 := hb (x (-1) 2)
    have b8086 := hb (x 1 13)
    have b8087 := hb (x 0 1 && x 0 14)
    clear * - r8084 b8085 b8086 b8087 g12 d8075
    omega
  have d8088 : (x 0 1).toNat = 1 := by
    have r8089 := hand1 (x 0 1) (x 0 14)
    have b8090 := hb (x 0 1)
    have b8091 := hb (x 0 1 && x 0 14)
    clear * - r8089 b8090 b8091 d8083
    omega
  have d8092 : (x 1 14).toNat = 0 := by
    have r8093 : (x 1 14).toNat + (x 0 1).toNat = 1 := by have q := hd14 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8094 := hb (x 0 1)
    have b8095 := hb (x 1 14)
    clear * - r8093 b8094 b8095 d8088
    omega
  have d8096 : (x 1 2).toNat = 0 := by
    have r8097 : (x 1 2).toNat ≤ (x 1 14).toNat := himp _ _ (hp2 1)
    have b8098 := hb (x 1 2)
    have b8099 := hb (x 1 14)
    clear * - r8097 b8098 b8099 d8092
    omega
  have d8100 : (x (-1) 12).toNat = 0 := by
    have r8101 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8102 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e8103 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b8104 := hb (x (-4) 3)
    have b8105 := hb (x (-3) 2)
    have b8106 := hb (x (-2) 13)
    have b8107 := hb (x (-1) 12)
    clear * - r8101 e8102 e8103 b8104 b8105 b8106 b8107 d8063
    omega
  have d8108 : (x (-1) 4).toNat = 0 := by
    have r8109 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
    have b8110 := hb (x (-1) 4)
    have b8111 := hb (x (-1) 12)
    clear * - r8109 b8110 b8111 d8100
    omega
  have d8112 : (x 3 11).toNat = 1 := by
    have r8113 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8114 := hb (x (-1) 4)
    have b8115 := hb (x 3 11)
    have b8116 := hb (x 2 1 && x 2 12)
    have b8117 := hb (x 1 2 && x 1 13)
    have b8118 := hb (x 0 3 && x 0 14)
    clear * - r8113 b8114 b8115 b8116 b8117 b8118 g27 g28 g29 d8108
    omega
  have d8119 : (x 3 3).toNat = 1 := by
    have r8120 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
    have b8121 := hb (x 3 3)
    have b8122 := hb (x 3 11)
    clear * - r8120 b8121 b8122 d8112
    omega
  have d8123 : (x 6 12).toNat = 0 := by
    have r8124 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8125 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e8126 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b8127 := hb (x 3 3)
    have b8128 := hb (x 4 2)
    have b8129 := hb (x 5 13)
    have b8130 := hb (x 6 12)
    clear * - r8124 e8125 e8126 b8127 b8128 b8129 b8130 d8119
    omega
  have d8131 : (x 5 13).toNat = 0 := by
    have r8132 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8133 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e8134 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b8135 := hb (x 3 3)
    have b8136 := hb (x 4 2)
    have b8137 := hb (x 5 13)
    have b8138 := hb (x 6 12)
    clear * - r8132 e8133 e8134 b8135 b8136 b8137 b8138 d8123 d8119
    omega
  have d8139 : (x 4 2).toNat = 0 := by
    have r8140 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8141 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e8142 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b8143 := hb (x 3 3)
    have b8144 := hb (x 4 2)
    have b8145 := hb (x 5 13)
    have b8146 := hb (x 6 12)
    clear * - r8140 e8141 e8142 b8143 b8144 b8145 b8146 d8123 d8131 d8119
    omega
  have d8147 : (x 4 10).toNat = 0 := by
    have r8148 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
    have b8149 := hb (x 4 2)
    have b8150 := hb (x 4 10)
    clear * - r8148 b8149 b8150 d8139
    omega
  have d8151 : (x 3 1 && x 3 11).toNat = 1 := by
    have r8152 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8153 := hb (x (-1) 5)
    have b8154 := hb (x 4 10)
    have b8155 := hb (x 3 1 && x 3 11)
    have b8156 := hb (x 2 2 && x 2 12)
    have b8157 := hb (x 1 3 && x 1 13)
    have b8158 := hb (x 0 4 && x 0 14)
    clear * - r8152 b8153 b8154 b8155 b8156 b8157 b8158 d8147 g20 g21 g22 g5
    omega
  have d8159 : (x 3 1).toNat = 1 := by
    have r8160 := hand1 (x 3 1) (x 3 11)
    have b8161 := hb (x 3 1)
    have b8162 := hb (x 3 1 && x 3 11)
    clear * - r8160 b8161 b8162 d8151
    omega
  have d8163 : (x 4 14).toNat = 0 := by
    have r8164 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8165 := hb (x 3 1)
    have b8166 := hb (x 4 14)
    clear * - r8164 b8165 b8166 d8159
    omega
  have d8167 : (x 4 1 && x 4 14).toNat = 0 := by
    have r8168 := hand2 (x 4 1) (x 4 14)
    have b8169 := hb (x 4 14)
    have b8170 := hb (x 4 1 && x 4 14)
    clear * - r8168 b8169 b8170 d8163
    omega
  have d8171 : (x 3 2).toNat = 1 := by
    have r8172 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8173 := hb (x 3 2)
    have b8174 := hb (x 5 13)
    have b8175 := hb (x 4 1 && x 4 14)
    clear * - r8172 b8173 b8174 b8175 d8131 d8167
    omega
  have d8176 : (x 3 14).toNat = 1 := by
    have r8177 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
    have b8178 := hb (x 3 2)
    have b8179 := hb (x 3 14)
    clear * - r8177 b8178 b8179 d8171
    omega
  have d8180 : (x 2 1).toNat = 0 := by
    have r8181 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8182 := hb (x 2 1)
    have b8183 := hb (x 3 14)
    clear * - r8181 b8182 b8183 d8176
    omega
  have d8184 : (x 2 1 && x 2 14).toNat = 0 := by
    have r8185 := hand1 (x 2 1) (x 2 14)
    have b8186 := hb (x 2 1)
    have b8187 := hb (x 2 1 && x 2 14)
    clear * - r8185 b8186 b8187 d8180
    omega
  have d8188 : (x 3 13).toNat = 1 := by
    have r8189 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8190 := hb (x 1 2)
    have b8191 := hb (x 3 13)
    have b8192 := hb (x 2 1 && x 2 14)
    clear * - r8189 b8190 b8191 b8192 d8184 d8096
    omega
  have d8193 : (x 4 12).toNat = 0 := by
    have r8194 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8195 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e8196 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b8197 := hb (x 1 3)
    have b8198 := hb (x 2 2)
    have b8199 := hb (x 3 13)
    have b8200 := hb (x 4 12)
    clear * - r8194 e8195 e8196 b8197 b8198 b8199 b8200 d8188
    omega
  have d8201 : (x 2 2).toNat = 0 := by
    have r8202 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8203 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e8204 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b8205 := hb (x 1 3)
    have b8206 := hb (x 2 2)
    have b8207 := hb (x 3 13)
    have b8208 := hb (x 4 12)
    clear * - r8202 e8203 e8204 b8205 b8206 b8207 b8208 d8193 d8188
    omega
  have d8209 : (x 2 10).toNat = 0 := by
    have r8210 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
    have b8211 := hb (x 2 2)
    have b8212 := hb (x 2 10)
    clear * - r8210 b8211 b8212 d8201
    omega
  have d8213 : (x 1 3).toNat = 0 := by
    have r8214 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8215 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e8216 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b8217 := hb (x 1 3)
    have b8218 := hb (x 2 2)
    have b8219 := hb (x 3 13)
    have b8220 := hb (x 4 12)
    clear * - r8214 e8215 e8216 b8217 b8218 b8219 b8220 d8193 d8188 d8201
    omega
  have d8221 : (x 1 11).toNat = 0 := by
    have r8222 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
    have b8223 := hb (x 1 3)
    have b8224 := hb (x 1 11)
    clear * - r8222 b8223 b8224 d8213
    omega
  have d8225 : (x 1 1 && x 1 11).toNat = 0 := by
    have r8226 := hand2 (x 1 1) (x 1 11)
    have b8227 := hb (x 1 11)
    have b8228 := hb (x 1 1 && x 1 11)
    clear * - r8226 b8227 b8228 d8221
    omega
  have d8229 : (x (-2) 4 && x (-2) 14).toNat = 1 := by
    have r8230 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8231 := hb (x (-3) 5)
    have b8232 := hb (x 2 10)
    have b8233 := hb (x 1 1 && x 1 11)
    have b8234 := hb (x 0 2 && x 0 12)
    have b8235 := hb (x (-1) 3 && x (-1) 13)
    have b8236 := hb (x (-2) 4 && x (-2) 14)
    clear * - r8230 b8231 b8232 b8233 b8234 b8235 b8236 d8209 d8225 g18 g19 g0
    omega
  have d8237 : (x (-2) 4).toNat = 1 := by
    have r8238 := hand1 (x (-2) 4) (x (-2) 14)
    have b8239 := hb (x (-2) 4)
    have b8240 := hb (x (-2) 4 && x (-2) 14)
    clear * - r8238 b8239 b8240 d8229
    omega
  have d8241 : (x (-2) 12).toNat = 1 := by
    have r8242 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
    have b8243 := hb (x (-2) 4)
    have b8244 := hb (x (-2) 12)
    clear * - r8242 b8243 b8244 d8237
    omega
  have d8245 : (x (-4) 2).toNat = 0 := by
    have r8246 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8247 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
    have e8248 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
    have b8249 := hb (x (-5) 3)
    have b8250 := hb (x (-4) 2)
    have b8251 := hb (x (-3) 13)
    have b8252 := hb (x (-2) 12)
    clear * - r8246 e8247 e8248 b8249 b8250 b8251 b8252 d8241 g3
    omega
  have d8253 : (x (-4) 2 && x (-4) 12).toNat = 0 := by
    have r8254 := hand1 (x (-4) 2) (x (-4) 12)
    have b8255 := hb (x (-4) 2)
    have b8256 := hb (x (-4) 2 && x (-4) 12)
    clear * - r8254 b8255 b8256 d8245
    omega
  have d8257 : (x (-4) 10).toNat = 0 := by
    have r8258 : (x (-4) 10).toNat ≤ (x (-4) 2).toNat := himp _ _ (hp10 (-4))
    have b8259 := hb (x (-4) 2)
    have b8260 := hb (x (-4) 10)
    clear * - r8258 b8259 b8260 d8245
    omega
  have d8261 : (x (-4) 5 && x (-4) 10).toNat = 0 := by
    have r8262 := hand2 (x (-4) 5) (x (-4) 10)
    have b8263 := hb (x (-4) 10)
    have b8264 := hb (x (-4) 5 && x (-4) 10)
    clear * - r8262 b8263 b8264 d8257
    omega
  have d8265 : (x (-4) 6 && x (-4) 10).toNat = 0 := by
    have r8266 := hand2 (x (-4) 6) (x (-4) 10)
    have b8267 := hb (x (-4) 10)
    have b8268 := hb (x (-4) 6 && x (-4) 10)
    clear * - r8266 b8267 b8268 d8257
    omega
  have d8269 : (x (-5) 3).toNat = 0 := by
    have r8270 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8271 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
    have e8272 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
    have b8273 := hb (x (-5) 3)
    have b8274 := hb (x (-4) 2)
    have b8275 := hb (x (-3) 13)
    have b8276 := hb (x (-2) 12)
    clear * - r8270 e8271 e8272 b8273 b8274 b8275 b8276 d8241 g3 d8245
    omega
  have d8277 : (x (-5) 3 && x (-5) 13).toNat = 0 := by
    have r8278 := hand1 (x (-5) 3) (x (-5) 13)
    have b8279 := hb (x (-5) 3)
    have b8280 := hb (x (-5) 3 && x (-5) 13)
    clear * - r8278 b8279 b8280 d8269
    omega
  have d8281 : (x (-5) 11).toNat = 0 := by
    have r8282 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
    have b8283 := hb (x (-5) 3)
    have b8284 := hb (x (-5) 11)
    clear * - r8282 b8283 b8284 d8269
    omega
  have d8285 : (x (-5) 6 && x (-5) 11).toNat = 0 := by
    have r8286 := hand2 (x (-5) 6) (x (-5) 11)
    have b8287 := hb (x (-5) 11)
    have b8288 := hb (x (-5) 6 && x (-5) 11)
    clear * - r8286 b8287 b8288 d8281
    omega
  have d8289 : (x (-5) 7 && x (-5) 11).toNat = 0 := by
    have r8290 := hand2 (x (-5) 7) (x (-5) 11)
    have b8291 := hb (x (-5) 11)
    have b8292 := hb (x (-5) 7 && x (-5) 11)
    clear * - r8290 b8291 b8292 d8281
    omega
  have d8293 : (x 2 8).toNat = 0 := by
    have r8294 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8295 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
    have e8296 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
    have e8297 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
    have e8298 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
    have e8299 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
    have e8300 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
    have b8301 := hb (x (-5) 7)
    have b8302 := hb (x (-4) 6)
    have b8303 := hb (x (-3) 5)
    have b8304 := hb (x (-2) 4)
    have b8305 := hb (x (-1) 11)
    have b8306 := hb (x 0 10)
    have b8307 := hb (x 1 9)
    have b8308 := hb (x 2 8)
    clear * - r8294 e8295 e8296 e8297 e8298 e8299 e8300 b8301 b8302 b8303 b8304 b8305 b8306 b8307 b8308 g7 d8237 g0
    omega
  have d8309 : (x 1 9).toNat = 0 := by
    have r8310 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8311 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
    have e8312 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
    have e8313 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
    have e8314 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
    have e8315 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
    have e8316 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
    have b8317 := hb (x (-5) 7)
    have b8318 := hb (x (-4) 6)
    have b8319 := hb (x (-3) 5)
    have b8320 := hb (x (-2) 4)
    have b8321 := hb (x (-1) 11)
    have b8322 := hb (x 0 10)
    have b8323 := hb (x 1 9)
    have b8324 := hb (x 2 8)
    clear * - r8310 e8311 e8312 e8313 e8314 e8315 e8316 b8317 b8318 b8319 b8320 b8321 b8322 b8323 b8324 d8293 g7 d8237 g0
    omega
  have d8325 : (x 0 10).toNat = 0 := by
    have r8326 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8327 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
    have e8328 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
    have e8329 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
    have e8330 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
    have e8331 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
    have e8332 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
    have b8333 := hb (x (-5) 7)
    have b8334 := hb (x (-4) 6)
    have b8335 := hb (x (-3) 5)
    have b8336 := hb (x (-2) 4)
    have b8337 := hb (x (-1) 11)
    have b8338 := hb (x 0 10)
    have b8339 := hb (x 1 9)
    have b8340 := hb (x 2 8)
    clear * - r8326 e8327 e8328 e8329 e8330 e8331 e8332 b8333 b8334 b8335 b8336 b8337 b8338 b8339 b8340 d8293 d8309 g7 d8237 g0
    omega
  have d8341 : (x (-4) 6).toNat = 0 := by
    have r8342 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8343 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
    have e8344 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
    have e8345 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
    have e8346 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
    have e8347 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
    have e8348 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
    have b8349 := hb (x (-5) 7)
    have b8350 := hb (x (-4) 6)
    have b8351 := hb (x (-3) 5)
    have b8352 := hb (x (-2) 4)
    have b8353 := hb (x (-1) 11)
    have b8354 := hb (x 0 10)
    have b8355 := hb (x 1 9)
    have b8356 := hb (x 2 8)
    clear * - r8342 e8343 e8344 e8345 e8346 e8347 e8348 b8349 b8350 b8351 b8352 b8353 b8354 b8355 b8356 d8293 d8309 d8325 g7 d8237 g0
    omega
  have d8357 : (x (-5) 7).toNat = 0 := by
    have r8358 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8359 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
    have e8360 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
    have e8361 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
    have e8362 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
    have e8363 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
    have e8364 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
    have b8365 := hb (x (-5) 7)
    have b8366 := hb (x (-4) 6)
    have b8367 := hb (x (-3) 5)
    have b8368 := hb (x (-2) 4)
    have b8369 := hb (x (-1) 11)
    have b8370 := hb (x 0 10)
    have b8371 := hb (x 1 9)
    have b8372 := hb (x 2 8)
    clear * - r8358 e8359 e8360 e8361 e8362 e8363 e8364 b8365 b8366 b8367 b8368 b8369 b8370 b8371 b8372 d8293 d8309 d8325 g7 d8237 g0 d8341
    omega
  have d8373 : (x 6 8).toNat = 0 := by
    have r8374 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8375 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e8376 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e8377 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e8378 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e8379 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e8380 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b8381 := hb (x (-1) 7)
    have b8382 := hb (x 0 6)
    have b8383 := hb (x 1 5)
    have b8384 := hb (x 2 4)
    have b8385 := hb (x 3 11)
    have b8386 := hb (x 4 10)
    have b8387 := hb (x 5 9)
    have b8388 := hb (x 6 8)
    clear * - r8374 e8375 e8376 e8377 e8378 e8379 e8380 b8381 b8382 b8383 b8384 b8385 b8386 b8387 b8388 d8147 d8112 g13 g11
    omega
  have d8389 : (x 5 9).toNat = 0 := by
    have r8390 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8391 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e8392 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e8393 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e8394 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e8395 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e8396 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b8397 := hb (x (-1) 7)
    have b8398 := hb (x 0 6)
    have b8399 := hb (x 1 5)
    have b8400 := hb (x 2 4)
    have b8401 := hb (x 3 11)
    have b8402 := hb (x 4 10)
    have b8403 := hb (x 5 9)
    have b8404 := hb (x 6 8)
    clear * - r8390 e8391 e8392 e8393 e8394 e8395 e8396 b8397 b8398 b8399 b8400 b8401 b8402 b8403 b8404 d8373 d8147 d8112 g13 g11
    omega
  have d8405 : (x 0 6).toNat = 0 := by
    have r8406 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8407 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e8408 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e8409 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e8410 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e8411 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e8412 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b8413 := hb (x (-1) 7)
    have b8414 := hb (x 0 6)
    have b8415 := hb (x 1 5)
    have b8416 := hb (x 2 4)
    have b8417 := hb (x 3 11)
    have b8418 := hb (x 4 10)
    have b8419 := hb (x 5 9)
    have b8420 := hb (x 6 8)
    clear * - r8406 e8407 e8408 e8409 e8410 e8411 e8412 b8413 b8414 b8415 b8416 b8417 b8418 b8419 b8420 d8373 d8389 d8147 d8112 g13 g11
    omega
  have d8421 : (x 0 1 && x 0 6).toNat = 0 := by
    have r8422 := hand2 (x 0 1) (x 0 6)
    have b8423 := hb (x 0 6)
    have b8424 := hb (x 0 1 && x 0 6)
    clear * - r8422 b8423 b8424 d8405
    omega
  have d8425 : (x 0 2 && x 0 6).toNat = 0 := by
    have r8426 := hand2 (x 0 2) (x 0 6)
    have b8427 := hb (x 0 6)
    have b8428 := hb (x 0 2 && x 0 6)
    clear * - r8426 b8427 b8428 d8405
    omega
  have r8429 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r8430 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r8431 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e8432 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
  have e8433 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
  have e8434 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
  have e8435 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
  have e8436 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
  have e8437 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
  have r8438 : 1 ≤ (x 2 4).toNat + (x 1 1 && x 1 5).toNat + (x 0 2 && x 0 6).toNat + (x (-1) 3 && x (-1) 7).toNat + (x (-2) 4 && x (-2) 8).toNat + (x (-3) 5 && x (-3) 9).toNat + (x (-4) 6 && x (-4) 10).toNat + (x (-5) 7 && x (-5) 11).toNat + (x (-6) 8 && x (-6) 12).toNat + (x (-7) 9 && x (-7) 13).toNat + (x (-8) 10 && x (-8) 14).toNat + (x (-9) 11).toNat := by have q := hcov4 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e8439 : (x 1 1 && x 1 5).toNat = (x 1 5).toNat := handr _ _ (fun h => hp13 1 (hp5 1 (h)))
  have e8440 : (x (-8) 10 && x (-8) 14).toNat = (x (-8) 10).toNat := handl _ _ (fun h => hp2 (-8) (hp10 (-8) (h)))
  have r8441 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := by have q := hcov5 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r8442 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r8443 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r8444 : 1 ≤ (x (-11) 13).toNat + (x (-12) 1 && x (-12) 14).toNat + (x (-13) 2).toNat := by have q := hcov13 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r8445 : (x (-13) 2).toNat ≤ (x (-13) 14).toNat := himp _ _ (hp2 (-13))
  have r8446 := hand2 (x (-2) 4) (x (-2) 8)
  have r8447 := hand1 (x (-6) 8) (x (-6) 12)
  have r8448 := hand1 (x (-7) 9) (x (-7) 13)
  have r8449 := hand2 (x (-2) 3) (x (-2) 8)
  have r8450 := hand1 (x (-6) 7) (x (-6) 12)
  have r8451 := hand1 (x (-7) 8) (x (-7) 13)
  have r8452 := hand1 (x (-8) 9) (x (-8) 14)
  have r8453 := hand1 (x (-6) 4) (x (-6) 14)
  have r8454 := hand1 (x (-2) 3) (x (-2) 14)
  have r8455 := hand2 (x (-12) 1) (x (-12) 14)
  linarith only [r8429, r8430, r8431, e8432, e8433, e8434, e8435, e8436, e8437, r8438, e8439, e8440, r8441, r8442, r8443, r8444, r8445, r8446, r8447, r8448, r8449, r8450, r8451, r8452, r8453, r8454, r8455, d8357, d8281, d8341, d8257, g0, g1, d8237, d8024, d8075, g4, d8088, g8, g11, d8221, g13, d8425, g14, g15, d8265, d8289, d8421, d8079, g16, d8261, d8285, g17, d8253, d8277, g25, g26]

theorem cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 5).toNat = 0)
    (g1 : (x (-3) 9).toNat = 0)
    (g2 : (x (-3) 11).toNat = 0)
    (g3 : (x (-3) 13).toNat = 0)
    (g4 : (x (-1) 3).toNat = 0)
    (g5 : (x (-1) 5).toNat = 0)
    (g6 : (x (-1) 9).toNat = 0)
    (g7 : (x (-1) 11).toNat = 0)
    (g8 : (x 0 2).toNat = 1)
    (g9 : (x 0 8).toNat = 1)
    (g10 : (x 0 11).toNat = 0)
    (g11 : (x 1 5).toNat = 0)
    (g12 : (x 1 13).toNat = 0)
    (g13 : (x 2 4).toNat = 0)
    (g14 : (x (-1) 3 && x (-1) 7).toNat = 0)
    (g15 : (x (-3) 5 && x (-3) 9).toNat = 0)
    (g16 : (x (-3) 4 && x (-3) 9).toNat = 0)
    (g17 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g18 : (x 0 2 && x 0 12).toNat = 0)
    (g19 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g20 : (x 2 2 && x 2 12).toNat = 0)
    (g21 : (x 1 3 && x 1 13).toNat = 0)
    (g22 : (x 0 4 && x 0 14).toNat = 0)
    (g23 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g24 : (x (-3) 3 && x (-3) 14).toNat = 0)
    (g25 : (x 0 1 && x 0 12).toNat = 0)
    (g26 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g27 : (x 2 1 && x 2 12).toNat = 0)
    (g28 : (x 1 2 && x 1 13).toNat = 0)
    (g29 : (x 0 3 && x 0 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a001_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29
