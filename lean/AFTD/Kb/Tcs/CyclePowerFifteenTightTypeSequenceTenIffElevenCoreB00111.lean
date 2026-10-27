import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b00111

Topic: combinatorics   Node: 0fa4a25466b0

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core: under the layer-free tight-cover constraints for k = 15 and 8 fixed bits of the class-type sequence near position 0, the constraints are contradictory. Its module also proves the sibling branches cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b00110000000001, cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b0011000000001, cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b001100000001, cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b00110000001, cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b0011000001, cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b001100001, cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b00110001, cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b0011001, cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b001101.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b00110000000001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 1 5).toNat = 0)
    (g1 : (x 1 7).toNat = 0)
    (g2 : (x 2 3).toNat = 1)
    (g3 : (x 2 4).toNat = 0)
    (g4 : (x 3 2).toNat = 0)
    (g5 : (x 3 5).toNat = 0)
    (g6 : (x 3 13).toNat = 0)
    (g7 : (x 5 2).toNat = 0)
    (g8 : (x 6 4).toNat = 0)
    (g9 : (x 6 5).toNat = 0)
    (g10 : (x 3 3 && x 3 13).toNat = 0)
    (g11 : (x 2 4 && x 2 14).toNat = 0)
    (g12 : (x 7 2 && x 7 12).toNat = 0)
    (g13 : (x 6 3 && x 6 13).toNat = 0)
    (g14 : (x 5 4 && x 5 14).toNat = 0)
    (g15 : (x 7 4 && x 7 14).toNat = 0)
    (g16 : (x 3 3 && x 3 14).toNat = 0)
    (g17 : (x 7 1 && x 7 12).toNat = 0)
    (g18 : (x 6 2 && x 6 13).toNat = 0)
    (g19 : (x 5 3 && x 5 14).toNat = 0)
    (g20 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d7939 : (x 5 12).toNat = 0 := by
    have r7940 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7941 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e7942 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b7943 := hb (x 2 3)
    have b7944 := hb (x 3 2)
    have b7945 := hb (x 4 13)
    have b7946 := hb (x 5 12)
    clear * - r7940 e7941 e7942 b7943 b7944 b7945 b7946 g4 g2
    omega
  have d7947 : (x 5 1 && x 5 12).toNat = 0 := by
    have r7948 := hand2 (x 5 1) (x 5 12)
    have b7949 := hb (x 5 12)
    have b7950 := hb (x 5 1 && x 5 12)
    clear * - r7948 b7949 b7950 d7939
    omega
  have d7951 : (x 4 13).toNat = 0 := by
    have r7952 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7953 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e7954 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b7955 := hb (x 2 3)
    have b7956 := hb (x 3 2)
    have b7957 := hb (x 4 13)
    have b7958 := hb (x 5 12)
    clear * - r7952 e7953 e7954 b7955 b7956 b7957 b7958 d7939 g4 g2
    omega
  have d7959 : (x 4 2 && x 4 13).toNat = 0 := by
    have r7960 := hand2 (x 4 2) (x 4 13)
    have b7961 := hb (x 4 13)
    have b7962 := hb (x 4 2 && x 4 13)
    clear * - r7960 b7961 b7962 d7951
    omega
  have d7963 : (x 4 5).toNat = 0 := by
    have r7964 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
    have b7965 := hb (x 4 5)
    have b7966 := hb (x 4 13)
    clear * - r7964 b7965 b7966 d7951
    omega
  have d7967 : (x 2 2).toNat = 1 := by
    have r7968 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7969 := hb (x 2 2)
    have b7970 := hb (x 4 13)
    have b7971 := hb (x 3 1 && x 3 14)
    clear * - r7968 b7969 b7970 b7971 d7951 g20
    omega
  have d7972 : (x 4 12).toNat = 0 := by
    have r7973 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7974 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e7975 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b7976 := hb (x 1 3)
    have b7977 := hb (x 2 2)
    have b7978 := hb (x 3 13)
    have b7979 := hb (x 4 12)
    clear * - r7973 e7974 e7975 b7976 b7977 b7978 b7979 g6 d7967
    omega
  have d7980 : (x 4 2 && x 4 12).toNat = 0 := by
    have r7981 := hand2 (x 4 2) (x 4 12)
    have b7982 := hb (x 4 12)
    have b7983 := hb (x 4 2 && x 4 12)
    clear * - r7981 b7982 b7983 d7972
    omega
  have d7984 : (x 4 4).toNat = 0 := by
    have r7985 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
    have b7986 := hb (x 4 4)
    have b7987 := hb (x 4 12)
    clear * - r7985 b7986 b7987 d7972
    omega
  have d7988 : (x 8 11).toNat = 1 := by
    have r7989 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7990 := hb (x 4 4)
    have b7991 := hb (x 8 11)
    have b7992 := hb (x 7 1 && x 7 12)
    have b7993 := hb (x 6 2 && x 6 13)
    have b7994 := hb (x 5 3 && x 5 14)
    clear * - r7989 b7990 b7991 b7992 b7993 b7994 g17 g18 g19 d7984
    omega
  have d7995 : (x 8 3).toNat = 1 := by
    have r7996 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
    have b7997 := hb (x 8 3)
    have b7998 := hb (x 8 11)
    clear * - r7996 b7997 b7998 d7988
    omega
  have d7999 : (x 11 12).toNat = 0 := by
    have r8000 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8001 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e8002 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b8003 := hb (x 8 3)
    have b8004 := hb (x 9 2)
    have b8005 := hb (x 10 13)
    have b8006 := hb (x 11 12)
    clear * - r8000 e8001 e8002 b8003 b8004 b8005 b8006 d7995
    omega
  have d8007 : (x 11 1 && x 11 12).toNat = 0 := by
    have r8008 := hand2 (x 11 1) (x 11 12)
    have b8009 := hb (x 11 12)
    have b8010 := hb (x 11 1 && x 11 12)
    clear * - r8008 b8009 b8010 d7999
    omega
  have d8011 : (x 11 2 && x 11 12).toNat = 0 := by
    have r8012 := hand2 (x 11 2) (x 11 12)
    have b8013 := hb (x 11 12)
    have b8014 := hb (x 11 2 && x 11 12)
    clear * - r8012 b8013 b8014 d7999
    omega
  have d8015 : (x 11 5 && x 11 12).toNat = 0 := by
    have r8016 := hand2 (x 11 5) (x 11 12)
    have b8017 := hb (x 11 12)
    have b8018 := hb (x 11 5 && x 11 12)
    clear * - r8016 b8017 b8018 d7999
    omega
  have d8019 : (x 11 4).toNat = 0 := by
    have r8020 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
    have b8021 := hb (x 11 4)
    have b8022 := hb (x 11 12)
    clear * - r8020 b8021 b8022 d7999
    omega
  have d8023 : (x 11 4 && x 11 14).toNat = 0 := by
    have r8024 := hand1 (x 11 4) (x 11 14)
    have b8025 := hb (x 11 4)
    have b8026 := hb (x 11 4 && x 11 14)
    clear * - r8024 b8025 b8026 d8019
    omega
  have d8027 : (x 10 13).toNat = 0 := by
    have r8028 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8029 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e8030 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b8031 := hb (x 8 3)
    have b8032 := hb (x 9 2)
    have b8033 := hb (x 10 13)
    have b8034 := hb (x 11 12)
    clear * - r8028 e8029 e8030 b8031 b8032 b8033 b8034 d7999 d7995
    omega
  have d8035 : (x 10 2 && x 10 13).toNat = 0 := by
    have r8036 := hand2 (x 10 2) (x 10 13)
    have b8037 := hb (x 10 13)
    have b8038 := hb (x 10 2 && x 10 13)
    clear * - r8036 b8037 b8038 d8027
    omega
  have d8039 : (x 10 3 && x 10 13).toNat = 0 := by
    have r8040 := hand2 (x 10 3) (x 10 13)
    have b8041 := hb (x 10 13)
    have b8042 := hb (x 10 3 && x 10 13)
    clear * - r8040 b8041 b8042 d8027
    omega
  have d8043 : (x 10 6 && x 10 13).toNat = 0 := by
    have r8044 := hand2 (x 10 6) (x 10 13)
    have b8045 := hb (x 10 13)
    have b8046 := hb (x 10 6 && x 10 13)
    clear * - r8044 b8045 b8046 d8027
    omega
  have d8047 : (x 10 5).toNat = 0 := by
    have r8048 : (x 10 5).toNat ≤ (x 10 13).toNat := himp _ _ (hp5 10)
    have b8049 := hb (x 10 5)
    have b8050 := hb (x 10 13)
    clear * - r8048 b8049 b8050 d8027
    omega
  have d8051 : (x 9 2).toNat = 0 := by
    have r8052 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8053 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e8054 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b8055 := hb (x 8 3)
    have b8056 := hb (x 9 2)
    have b8057 := hb (x 10 13)
    have b8058 := hb (x 11 12)
    clear * - r8052 e8053 e8054 b8055 b8056 b8057 b8058 d7999 d8027 d7995
    omega
  have d8059 : (x 9 2 && x 9 12).toNat = 0 := by
    have r8060 := hand1 (x 9 2) (x 9 12)
    have b8061 := hb (x 9 2)
    have b8062 := hb (x 9 2 && x 9 12)
    clear * - r8060 b8061 b8062 d8051
    omega
  have d8063 : (x 9 10).toNat = 0 := by
    have r8064 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
    have b8065 := hb (x 9 2)
    have b8066 := hb (x 9 10)
    clear * - r8064 b8065 b8066 d8051
    omega
  have d8067 : (x 6 11).toNat = 1 := by
    have r8068 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := by have q := hcov11 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8069 := hb (x 2 4)
    have b8070 := hb (x 6 11)
    have b8071 := hb (x 5 1 && x 5 12)
    have b8072 := hb (x 4 2 && x 4 13)
    have b8073 := hb (x 3 3 && x 3 14)
    clear * - r8068 b8069 b8070 b8071 b8072 b8073 d7947 d7959 g16 g3
    omega
  have d8074 : (x 6 3).toNat = 1 := by
    have r8075 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
    have b8076 := hb (x 6 3)
    have b8077 := hb (x 6 11)
    clear * - r8075 b8076 b8077 d8067
    omega
  have d8078 : (x 9 12).toNat = 0 := by
    have r8079 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8080 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e8081 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b8082 := hb (x 6 3)
    have b8083 := hb (x 7 2)
    have b8084 := hb (x 8 13)
    have b8085 := hb (x 9 12)
    clear * - r8079 e8080 e8081 b8082 b8083 b8084 b8085 d8074
    omega
  have d8086 : (x 9 1 && x 9 12).toNat = 0 := by
    have r8087 := hand2 (x 9 1) (x 9 12)
    have b8088 := hb (x 9 12)
    have b8089 := hb (x 9 1 && x 9 12)
    clear * - r8087 b8088 b8089 d8078
    omega
  have d8090 : (x 9 4).toNat = 0 := by
    have r8091 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
    have b8092 := hb (x 9 4)
    have b8093 := hb (x 9 12)
    clear * - r8091 b8092 b8093 d8078
    omega
  have d8094 : (x 9 4 && x 9 14).toNat = 0 := by
    have r8095 := hand1 (x 9 4) (x 9 14)
    have b8096 := hb (x 9 4)
    have b8097 := hb (x 9 4 && x 9 14)
    clear * - r8095 b8096 b8097 d8090
    omega
  have d8098 : (x 8 13).toNat = 0 := by
    have r8099 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8100 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e8101 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b8102 := hb (x 6 3)
    have b8103 := hb (x 7 2)
    have b8104 := hb (x 8 13)
    have b8105 := hb (x 9 12)
    clear * - r8099 e8100 e8101 b8102 b8103 b8104 b8105 d8078 d8074
    omega
  have d8106 : (x 8 2 && x 8 13).toNat = 0 := by
    have r8107 := hand2 (x 8 2) (x 8 13)
    have b8108 := hb (x 8 13)
    have b8109 := hb (x 8 2 && x 8 13)
    clear * - r8107 b8108 b8109 d8098
    omega
  have d8110 : (x 8 3 && x 8 13).toNat = 0 := by
    have r8111 := hand2 (x 8 3) (x 8 13)
    have b8112 := hb (x 8 13)
    have b8113 := hb (x 8 3 && x 8 13)
    clear * - r8111 b8112 b8113 d8098
    omega
  have d8114 : (x 8 5).toNat = 0 := by
    have r8115 : (x 8 5).toNat ≤ (x 8 13).toNat := himp _ _ (hp5 8)
    have b8116 := hb (x 8 5)
    have b8117 := hb (x 8 13)
    clear * - r8115 b8116 b8117 d8098
    omega
  have d8118 : (x 8 1 && x 8 11).toNat = 1 := by
    have r8119 : 1 ≤ (x 9 10).toNat + (x 8 1 && x 8 11).toNat + (x 7 2 && x 7 12).toNat + (x 6 3 && x 6 13).toNat + (x 5 4 && x 5 14).toNat + (x 4 5).toNat := by have q := hcov10 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8120 := hb (x 4 5)
    have b8121 := hb (x 9 10)
    have b8122 := hb (x 8 1 && x 8 11)
    have b8123 := hb (x 7 2 && x 7 12)
    have b8124 := hb (x 6 3 && x 6 13)
    have b8125 := hb (x 5 4 && x 5 14)
    clear * - r8119 b8120 b8121 b8122 b8123 b8124 b8125 d8063 g12 g13 g14 d7963
    omega
  have d8126 : (x 8 1).toNat = 1 := by
    have r8127 := hand1 (x 8 1) (x 8 11)
    have b8128 := hb (x 8 1)
    have b8129 := hb (x 8 1 && x 8 11)
    clear * - r8127 b8128 b8129 d8118
    omega
  have d8130 : (x 9 14).toNat = 0 := by
    have r8131 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8132 := hb (x 8 1)
    have b8133 := hb (x 9 14)
    clear * - r8131 b8132 b8133 d8126
    omega
  have d8134 : (x 9 1 && x 9 14).toNat = 0 := by
    have r8135 := hand2 (x 9 1) (x 9 14)
    have b8136 := hb (x 9 14)
    have b8137 := hb (x 9 1 && x 9 14)
    clear * - r8135 b8136 b8137 d8130
    omega
  have d8138 : (x 8 2).toNat = 1 := by
    have r8139 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8140 := hb (x 8 2)
    have b8141 := hb (x 10 13)
    have b8142 := hb (x 9 1 && x 9 14)
    clear * - r8139 b8140 b8141 b8142 d8027 d8134
    omega
  have d8143 : (x 8 14).toNat = 1 := by
    have r8144 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
    have b8145 := hb (x 8 2)
    have b8146 := hb (x 8 14)
    clear * - r8144 b8145 b8146 d8138
    omega
  have d8147 : (x 7 1).toNat = 0 := by
    have r8148 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8149 := hb (x 7 1)
    have b8150 := hb (x 8 14)
    clear * - r8148 b8149 b8150 d8143
    omega
  have d8151 : (x 7 1 && x 7 14).toNat = 0 := by
    have r8152 := hand1 (x 7 1) (x 7 14)
    have b8153 := hb (x 7 1)
    have b8154 := hb (x 7 1 && x 7 14)
    clear * - r8152 b8153 b8154 d8147
    omega
  have d8155 : (x 6 2).toNat = 1 := by
    have r8156 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8157 := hb (x 6 2)
    have b8158 := hb (x 8 13)
    have b8159 := hb (x 7 1 && x 7 14)
    clear * - r8156 b8157 b8158 b8159 d8098 d8151
    omega
  have d8160 : (x 6 14).toNat = 1 := by
    have r8161 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
    have b8162 := hb (x 6 2)
    have b8163 := hb (x 6 14)
    clear * - r8161 b8162 b8163 d8155
    omega
  have d8164 : (x 5 1).toNat = 0 := by
    have r8165 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8166 := hb (x 5 1)
    have b8167 := hb (x 6 14)
    clear * - r8165 b8166 b8167 d8160
    omega
  have d8168 : (x 5 1 && x 5 11).toNat = 0 := by
    have r8169 := hand1 (x 5 1) (x 5 11)
    have b8170 := hb (x 5 1)
    have b8171 := hb (x 5 1 && x 5 11)
    clear * - r8169 b8170 b8171 d8164
    omega
  have d8172 : (x 8 12).toNat = 0 := by
    have r8173 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8174 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e8175 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b8176 := hb (x 5 3)
    have b8177 := hb (x 6 2)
    have b8178 := hb (x 7 13)
    have b8179 := hb (x 8 12)
    clear * - r8173 e8174 e8175 b8176 b8177 b8178 b8179 d8155
    omega
  have d8180 : (x 8 4).toNat = 0 := by
    have r8181 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
    have b8182 := hb (x 8 4)
    have b8183 := hb (x 8 12)
    clear * - r8181 b8182 b8183 d8172
    omega
  have d8184 : (x 7 13).toNat = 0 := by
    have r8185 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8186 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e8187 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b8188 := hb (x 5 3)
    have b8189 := hb (x 6 2)
    have b8190 := hb (x 7 13)
    have b8191 := hb (x 8 12)
    clear * - r8185 e8186 e8187 b8188 b8189 b8190 b8191 d8172 d8155
    omega
  have d8192 : (x 6 1 && x 6 14).toNat = 1 := by
    have r8193 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8194 := hb (x 5 2)
    have b8195 := hb (x 7 13)
    have b8196 := hb (x 6 1 && x 6 14)
    clear * - r8193 b8194 b8195 b8196 d8184 g7
    omega
  have d8197 : (x 6 1).toNat = 1 := by
    have r8198 := hand1 (x 6 1) (x 6 14)
    have b8199 := hb (x 6 1)
    have b8200 := hb (x 6 1 && x 6 14)
    clear * - r8198 b8199 b8200 d8192
    omega
  have d8201 : (x 7 14).toNat = 0 := by
    have r8202 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8203 := hb (x 6 1)
    have b8204 := hb (x 7 14)
    clear * - r8202 b8203 b8204 d8197
    omega
  have d8205 : (x 7 3 && x 7 14).toNat = 0 := by
    have r8206 := hand2 (x 7 3) (x 7 14)
    have b8207 := hb (x 7 14)
    have b8208 := hb (x 7 3 && x 7 14)
    clear * - r8206 b8207 b8208 d8201
    omega
  have d8209 : (x 10 11).toNat = 1 := by
    have r8210 : 1 ≤ (x 10 11).toNat + (x 9 1 && x 9 12).toNat + (x 8 2 && x 8 13).toNat + (x 7 3 && x 7 14).toNat + (x 6 4).toNat := by have q := hcov11 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8211 := hb (x 6 4)
    have b8212 := hb (x 10 11)
    have b8213 := hb (x 9 1 && x 9 12)
    have b8214 := hb (x 8 2 && x 8 13)
    have b8215 := hb (x 7 3 && x 7 14)
    clear * - r8210 b8211 b8212 b8213 b8214 b8215 d8086 d8106 d8205 g8
    omega
  have d8216 : (x 10 3).toNat = 1 := by
    have r8217 : (x 10 11).toNat ≤ (x 10 3).toNat := himp _ _ (hp11 10)
    have b8218 := hb (x 10 3)
    have b8219 := hb (x 10 11)
    clear * - r8217 b8218 b8219 d8209
    omega
  have d8220 : (x 13 12).toNat = 0 := by
    have r8221 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8222 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e8223 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b8224 := hb (x 10 3)
    have b8225 := hb (x 11 2)
    have b8226 := hb (x 12 13)
    have b8227 := hb (x 13 12)
    clear * - r8221 e8222 e8223 b8224 b8225 b8226 b8227 d8216
    omega
  have d8228 : (x 13 2 && x 13 12).toNat = 0 := by
    have r8229 := hand2 (x 13 2) (x 13 12)
    have b8230 := hb (x 13 12)
    have b8231 := hb (x 13 2 && x 13 12)
    clear * - r8229 b8230 b8231 d8220
    omega
  have d8232 : (x 13 4).toNat = 0 := by
    have r8233 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
    have b8234 := hb (x 13 4)
    have b8235 := hb (x 13 12)
    clear * - r8233 b8234 b8235 d8220
    omega
  have d8236 : (x 13 4 && x 13 14).toNat = 0 := by
    have r8237 := hand1 (x 13 4) (x 13 14)
    have b8238 := hb (x 13 4)
    have b8239 := hb (x 13 4 && x 13 14)
    clear * - r8237 b8238 b8239 d8232
    omega
  have d8240 : (x 12 13).toNat = 0 := by
    have r8241 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8242 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e8243 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b8244 := hb (x 10 3)
    have b8245 := hb (x 11 2)
    have b8246 := hb (x 12 13)
    have b8247 := hb (x 13 12)
    clear * - r8241 e8242 e8243 b8244 b8245 b8246 b8247 d8220 d8216
    omega
  have d8248 : (x 12 3 && x 12 13).toNat = 0 := by
    have r8249 := hand2 (x 12 3) (x 12 13)
    have b8250 := hb (x 12 13)
    have b8251 := hb (x 12 3 && x 12 13)
    clear * - r8249 b8250 b8251 d8240
    omega
  have d8252 : (x 12 5).toNat = 0 := by
    have r8253 : (x 12 5).toNat ≤ (x 12 13).toNat := himp _ _ (hp5 12)
    have b8254 := hb (x 12 5)
    have b8255 := hb (x 12 13)
    clear * - r8253 b8254 b8255 d8240
    omega
  have d8256 : (x 11 2).toNat = 0 := by
    have r8257 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8258 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e8259 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b8260 := hb (x 10 3)
    have b8261 := hb (x 11 2)
    have b8262 := hb (x 12 13)
    have b8263 := hb (x 13 12)
    clear * - r8257 e8258 e8259 b8260 b8261 b8262 b8263 d8220 d8240 d8216
    omega
  have d8264 : (x 11 10).toNat = 0 := by
    have r8265 : (x 11 10).toNat ≤ (x 11 2).toNat := himp _ _ (hp10 11)
    have b8266 := hb (x 11 2)
    have b8267 := hb (x 11 10)
    clear * - r8265 b8266 b8267 d8256
    omega
  have d8268 : (x 10 1 && x 10 11).toNat = 1 := by
    have r8269 : 1 ≤ (x 11 10).toNat + (x 10 1 && x 10 11).toNat + (x 9 2 && x 9 12).toNat + (x 8 3 && x 8 13).toNat + (x 7 4 && x 7 14).toNat + (x 6 5).toNat := by have q := hcov10 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8270 := hb (x 6 5)
    have b8271 := hb (x 11 10)
    have b8272 := hb (x 10 1 && x 10 11)
    have b8273 := hb (x 9 2 && x 9 12)
    have b8274 := hb (x 8 3 && x 8 13)
    have b8275 := hb (x 7 4 && x 7 14)
    clear * - r8269 b8270 b8271 b8272 b8273 b8274 b8275 d8264 d8059 d8110 g15 g9
    omega
  have d8276 : (x 10 1).toNat = 1 := by
    have r8277 := hand1 (x 10 1) (x 10 11)
    have b8278 := hb (x 10 1)
    have b8279 := hb (x 10 1 && x 10 11)
    clear * - r8277 b8278 b8279 d8268
    omega
  have d8280 : (x 11 14).toNat = 0 := by
    have r8281 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8282 := hb (x 10 1)
    have b8283 := hb (x 11 14)
    clear * - r8281 b8282 b8283 d8276
    omega
  have d8284 : (x 11 1 && x 11 14).toNat = 0 := by
    have r8285 := hand2 (x 11 1) (x 11 14)
    have b8286 := hb (x 11 14)
    have b8287 := hb (x 11 1 && x 11 14)
    clear * - r8285 b8286 b8287 d8280
    omega
  have d8288 : (x 10 2).toNat = 1 := by
    have r8289 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8290 := hb (x 10 2)
    have b8291 := hb (x 12 13)
    have b8292 := hb (x 11 1 && x 11 14)
    clear * - r8289 b8290 b8291 b8292 d8240 d8284
    omega
  have d8293 : (x 12 12).toNat = 0 := by
    have r8294 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8295 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e8296 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b8297 := hb (x 9 3)
    have b8298 := hb (x 10 2)
    have b8299 := hb (x 11 13)
    have b8300 := hb (x 12 12)
    clear * - r8294 e8295 e8296 b8297 b8298 b8299 b8300 d8288
    omega
  have d8301 : (x 12 4).toNat = 0 := by
    have r8302 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
    have b8303 := hb (x 12 4)
    have b8304 := hb (x 12 12)
    clear * - r8302 b8303 b8304 d8293
    omega
  have d8305 : (x 12 4 && x 12 11).toNat = 0 := by
    have r8306 := hand1 (x 12 4) (x 12 11)
    have b8307 := hb (x 12 4)
    have b8308 := hb (x 12 4 && x 12 11)
    clear * - r8306 b8307 b8308 d8301
    omega
  have d8309 : (x 11 13).toNat = 0 := by
    have r8310 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8311 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e8312 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b8313 := hb (x 9 3)
    have b8314 := hb (x 10 2)
    have b8315 := hb (x 11 13)
    have b8316 := hb (x 12 12)
    clear * - r8310 e8311 e8312 b8313 b8314 b8315 b8316 d8293 d8288
    omega
  have d8317 : (x 9 3).toNat = 0 := by
    have r8318 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8319 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e8320 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b8321 := hb (x 9 3)
    have b8322 := hb (x 10 2)
    have b8323 := hb (x 11 13)
    have b8324 := hb (x 12 12)
    clear * - r8318 e8319 e8320 b8321 b8322 b8323 b8324 d8293 d8309 d8288
    omega
  have d8325 : (x 9 3 && x 9 14).toNat = 0 := by
    have r8326 := hand1 (x 9 3) (x 9 14)
    have b8327 := hb (x 9 3)
    have b8328 := hb (x 9 3 && x 9 14)
    clear * - r8326 b8327 b8328 d8317
    omega
  have d8329 : (x 12 11).toNat = 1 := by
    have r8330 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8331 := hb (x 8 4)
    have b8332 := hb (x 12 11)
    have b8333 := hb (x 11 1 && x 11 12)
    have b8334 := hb (x 10 2 && x 10 13)
    have b8335 := hb (x 9 3 && x 9 14)
    clear * - r8330 b8331 b8332 b8333 b8334 b8335 d8007 d8035 d8325 d8180
    omega
  have d8336 : (x 12 3).toNat = 1 := by
    have r8337 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
    have b8338 := hb (x 12 3)
    have b8339 := hb (x 12 11)
    clear * - r8337 b8338 b8339 d8329
    omega
  have d8340 : (x 15 12).toNat = 0 := by
    have r8341 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8342 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e8343 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b8344 := hb (x 12 3)
    have b8345 := hb (x 13 2)
    have b8346 := hb (x 14 13)
    have b8347 := hb (x 15 12)
    clear * - r8341 e8342 e8343 b8344 b8345 b8346 b8347 d8336
    omega
  have d8348 : (x 15 1 && x 15 12).toNat = 0 := by
    have r8349 := hand2 (x 15 1) (x 15 12)
    have b8350 := hb (x 15 12)
    have b8351 := hb (x 15 1 && x 15 12)
    clear * - r8349 b8350 b8351 d8340
    omega
  have d8352 : (x 15 2 && x 15 12).toNat = 0 := by
    have r8353 := hand2 (x 15 2) (x 15 12)
    have b8354 := hb (x 15 12)
    have b8355 := hb (x 15 2 && x 15 12)
    clear * - r8353 b8354 b8355 d8340
    omega
  have d8356 : (x 14 13).toNat = 0 := by
    have r8357 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8358 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e8359 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b8360 := hb (x 12 3)
    have b8361 := hb (x 13 2)
    have b8362 := hb (x 14 13)
    have b8363 := hb (x 15 12)
    clear * - r8357 e8358 e8359 b8360 b8361 b8362 b8363 d8340 d8336
    omega
  have d8364 : (x 14 2 && x 14 13).toNat = 0 := by
    have r8365 := hand2 (x 14 2) (x 14 13)
    have b8366 := hb (x 14 13)
    have b8367 := hb (x 14 2 && x 14 13)
    clear * - r8365 b8366 b8367 d8356
    omega
  have d8368 : (x 14 3 && x 14 13).toNat = 0 := by
    have r8369 := hand2 (x 14 3) (x 14 13)
    have b8370 := hb (x 14 13)
    have b8371 := hb (x 14 3 && x 14 13)
    clear * - r8369 b8370 b8371 d8356
    omega
  have d8372 : (x 13 2).toNat = 0 := by
    have r8373 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8374 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e8375 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b8376 := hb (x 12 3)
    have b8377 := hb (x 13 2)
    have b8378 := hb (x 14 13)
    have b8379 := hb (x 15 12)
    clear * - r8373 e8374 e8375 b8376 b8377 b8378 b8379 d8340 d8356 d8336
    omega
  have d8380 : (x 13 10).toNat = 0 := by
    have r8381 : (x 13 10).toNat ≤ (x 13 2).toNat := himp _ _ (hp10 13)
    have b8382 := hb (x 13 2)
    have b8383 := hb (x 13 10)
    clear * - r8381 b8382 b8383 d8372
    omega
  have d8384 : (x 13 3 && x 13 10).toNat = 0 := by
    have r8385 := hand2 (x 13 3) (x 13 10)
    have b8386 := hb (x 13 10)
    have b8387 := hb (x 13 3 && x 13 10)
    clear * - r8385 b8386 b8387 d8380
    omega
  have d8388 : (x 12 1 && x 12 11).toNat = 1 := by
    have r8389 : 1 ≤ (x 13 10).toNat + (x 12 1 && x 12 11).toNat + (x 11 2 && x 11 12).toNat + (x 10 3 && x 10 13).toNat + (x 9 4 && x 9 14).toNat + (x 8 5).toNat := by have q := hcov10 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8390 := hb (x 8 5)
    have b8391 := hb (x 13 10)
    have b8392 := hb (x 12 1 && x 12 11)
    have b8393 := hb (x 11 2 && x 11 12)
    have b8394 := hb (x 10 3 && x 10 13)
    have b8395 := hb (x 9 4 && x 9 14)
    clear * - r8389 b8390 b8391 b8392 b8393 b8394 b8395 d8380 d8011 d8039 d8094 d8114
    omega
  have d8396 : (x 12 1).toNat = 1 := by
    have r8397 := hand1 (x 12 1) (x 12 11)
    have b8398 := hb (x 12 1)
    have b8399 := hb (x 12 1 && x 12 11)
    clear * - r8397 b8398 b8399 d8388
    omega
  have d8400 : (x 13 14).toNat = 0 := by
    have r8401 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8402 := hb (x 12 1)
    have b8403 := hb (x 13 14)
    clear * - r8401 b8402 b8403 d8396
    omega
  have d8404 : (x 13 3 && x 13 14).toNat = 0 := by
    have r8405 := hand2 (x 13 3) (x 13 14)
    have b8406 := hb (x 13 14)
    have b8407 := hb (x 13 3 && x 13 14)
    clear * - r8405 b8406 b8407 d8400
    omega
  have d8408 : (x 16 11).toNat = 1 := by
    have r8409 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8410 := hb (x 12 4)
    have b8411 := hb (x 16 11)
    have b8412 := hb (x 15 1 && x 15 12)
    have b8413 := hb (x 14 2 && x 14 13)
    have b8414 := hb (x 13 3 && x 13 14)
    clear * - r8409 b8410 b8411 b8412 b8413 b8414 d8348 d8364 d8404 d8301
    omega
  have d8415 : (x 16 3).toNat = 1 := by
    have r8416 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
    have b8417 := hb (x 16 3)
    have b8418 := hb (x 16 11)
    clear * - r8416 b8417 b8418 d8408
    omega
  have d8419 : (x 19 12).toNat = 0 := by
    have r8420 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8421 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e8422 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have b8423 := hb (x 16 3)
    have b8424 := hb (x 17 2)
    have b8425 := hb (x 18 13)
    have b8426 := hb (x 19 12)
    clear * - r8420 e8421 e8422 b8423 b8424 b8425 b8426 d8415
    omega
  have d8427 : (x 19 1 && x 19 12).toNat = 0 := by
    have r8428 := hand2 (x 19 1) (x 19 12)
    have b8429 := hb (x 19 12)
    have b8430 := hb (x 19 1 && x 19 12)
    clear * - r8428 b8429 b8430 d8419
    omega
  have d8431 : (x 19 4).toNat = 0 := by
    have r8432 : (x 19 4).toNat ≤ (x 19 12).toNat := himp _ _ (hp4 19)
    have b8433 := hb (x 19 4)
    have b8434 := hb (x 19 12)
    clear * - r8432 b8433 b8434 d8419
    omega
  have d8435 : (x 18 13).toNat = 0 := by
    have r8436 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8437 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e8438 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have b8439 := hb (x 16 3)
    have b8440 := hb (x 17 2)
    have b8441 := hb (x 18 13)
    have b8442 := hb (x 19 12)
    clear * - r8436 e8437 e8438 b8439 b8440 b8441 b8442 d8419 d8415
    omega
  have d8443 : (x 18 2 && x 18 13).toNat = 0 := by
    have r8444 := hand2 (x 18 2) (x 18 13)
    have b8445 := hb (x 18 13)
    have b8446 := hb (x 18 2 && x 18 13)
    clear * - r8444 b8445 b8446 d8435
    omega
  have d8447 : (x 18 5).toNat = 0 := by
    have r8448 : (x 18 5).toNat ≤ (x 18 13).toNat := himp _ _ (hp5 18)
    have b8449 := hb (x 18 5)
    have b8450 := hb (x 18 13)
    clear * - r8448 b8449 b8450 d8435
    omega
  have d8451 : (x 17 2).toNat = 0 := by
    have r8452 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8453 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e8454 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have b8455 := hb (x 16 3)
    have b8456 := hb (x 17 2)
    have b8457 := hb (x 18 13)
    have b8458 := hb (x 19 12)
    clear * - r8452 e8453 e8454 b8455 b8456 b8457 b8458 d8419 d8435 d8415
    omega
  have d8459 : (x 17 10).toNat = 0 := by
    have r8460 : (x 17 10).toNat ≤ (x 17 2).toNat := himp _ _ (hp10 17)
    have b8461 := hb (x 17 2)
    have b8462 := hb (x 17 10)
    clear * - r8460 b8461 b8462 d8451
    omega
  have d8463 : (x 16 1 && x 16 11).toNat = 1 := by
    have r8464 : 1 ≤ (x 17 10).toNat + (x 16 1 && x 16 11).toNat + (x 15 2 && x 15 12).toNat + (x 14 3 && x 14 13).toNat + (x 13 4 && x 13 14).toNat + (x 12 5).toNat := by have q := hcov10 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8465 := hb (x 12 5)
    have b8466 := hb (x 17 10)
    have b8467 := hb (x 16 1 && x 16 11)
    have b8468 := hb (x 15 2 && x 15 12)
    have b8469 := hb (x 14 3 && x 14 13)
    have b8470 := hb (x 13 4 && x 13 14)
    clear * - r8464 b8465 b8466 b8467 b8468 b8469 b8470 d8459 d8352 d8368 d8236 d8252
    omega
  have d8471 : (x 16 1).toNat = 1 := by
    have r8472 := hand1 (x 16 1) (x 16 11)
    have b8473 := hb (x 16 1)
    have b8474 := hb (x 16 1 && x 16 11)
    clear * - r8472 b8473 b8474 d8463
    omega
  have d8475 : (x 17 14).toNat = 0 := by
    have r8476 : (x 17 14).toNat + (x 16 1).toNat = 1 := by have q := hd14 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8477 := hb (x 16 1)
    have b8478 := hb (x 17 14)
    clear * - r8476 b8477 b8478 d8471
    omega
  have d8479 : (x 17 1 && x 17 14).toNat = 0 := by
    have r8480 := hand2 (x 17 1) (x 17 14)
    have b8481 := hb (x 17 14)
    have b8482 := hb (x 17 1 && x 17 14)
    clear * - r8480 b8481 b8482 d8475
    omega
  have d8483 : (x 16 2).toNat = 1 := by
    have r8484 : 1 ≤ (x 18 13).toNat + (x 17 1 && x 17 14).toNat + (x 16 2).toNat := by have q := hcov13 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8485 := hb (x 16 2)
    have b8486 := hb (x 18 13)
    have b8487 := hb (x 17 1 && x 17 14)
    clear * - r8484 b8485 b8486 b8487 d8435 d8479
    omega
  have d8488 : (x 16 14).toNat = 1 := by
    have r8489 : (x 16 2).toNat ≤ (x 16 14).toNat := himp _ _ (hp2 16)
    have b8490 := hb (x 16 2)
    have b8491 := hb (x 16 14)
    clear * - r8489 b8490 b8491 d8483
    omega
  have d8492 : (x 15 1).toNat = 0 := by
    have r8493 : (x 16 14).toNat + (x 15 1).toNat = 1 := by have q := hd14 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8494 := hb (x 15 1)
    have b8495 := hb (x 16 14)
    clear * - r8493 b8494 b8495 d8488
    omega
  have d8496 : (x 15 1 && x 15 14).toNat = 0 := by
    have r8497 := hand1 (x 15 1) (x 15 14)
    have b8498 := hb (x 15 1)
    have b8499 := hb (x 15 1 && x 15 14)
    clear * - r8497 b8498 b8499 d8492
    omega
  have d8500 : (x 15 1 && x 15 8).toNat = 0 := by
    have r8501 := hand1 (x 15 1) (x 15 8)
    have b8502 := hb (x 15 1)
    have b8503 := hb (x 15 1 && x 15 8)
    clear * - r8501 b8502 b8503 d8492
    omega
  have d8504 : (x 15 13).toNat = 0 := by
    have r8505 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
    have b8506 := hb (x 15 1)
    have b8507 := hb (x 15 13)
    clear * - r8505 b8506 b8507 d8492
    omega
  have d8508 : (x 17 3 && x 17 14).toNat = 0 := by
    have r8509 := hand2 (x 17 3) (x 17 14)
    have b8510 := hb (x 17 14)
    have b8511 := hb (x 17 3 && x 17 14)
    clear * - r8509 b8510 b8511 d8475
    omega
  have d8512 : (x 17 6).toNat = 0 := by
    have r8513 : (x 17 6).toNat ≤ (x 17 14).toNat := himp _ _ (hp6 17)
    have b8514 := hb (x 17 6)
    have b8515 := hb (x 17 14)
    clear * - r8513 b8514 b8515 d8475
    omega
  have d8516 : (x 14 1 && x 14 14).toNat = 1 := by
    have r8517 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8518 := hb (x 13 2)
    have b8519 := hb (x 15 13)
    have b8520 := hb (x 14 1 && x 14 14)
    clear * - r8517 b8518 b8519 b8520 d8504 d8372
    omega
  have d8521 : (x 14 1).toNat = 1 := by
    have r8522 := hand1 (x 14 1) (x 14 14)
    have b8523 := hb (x 14 1)
    have b8524 := hb (x 14 1 && x 14 14)
    clear * - r8522 b8523 b8524 d8516
    omega
  have d8525 : (x 15 14).toNat = 0 := by
    have r8526 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8527 := hb (x 14 1)
    have b8528 := hb (x 15 14)
    clear * - r8526 b8527 b8528 d8521
    omega
  have d8529 : (x 15 2).toNat = 0 := by
    have r8530 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
    have b8531 := hb (x 15 2)
    have b8532 := hb (x 15 14)
    clear * - r8530 b8531 b8532 d8525
    omega
  have d8533 : (x 15 10).toNat = 0 := by
    have r8534 : (x 15 10).toNat ≤ (x 15 2).toNat := himp _ _ (hp10 15)
    have b8535 := hb (x 15 2)
    have b8536 := hb (x 15 10)
    clear * - r8534 b8535 b8536 d8529
    omega
  have d8537 : (x 14 1 && x 14 11).toNat = 1 := by
    have r8538 : 1 ≤ (x 15 10).toNat + (x 14 1 && x 14 11).toNat + (x 13 2 && x 13 12).toNat + (x 12 3 && x 12 13).toNat + (x 11 4 && x 11 14).toNat + (x 10 5).toNat := by have q := hcov10 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8539 := hb (x 10 5)
    have b8540 := hb (x 15 10)
    have b8541 := hb (x 14 1 && x 14 11)
    have b8542 := hb (x 13 2 && x 13 12)
    have b8543 := hb (x 12 3 && x 12 13)
    have b8544 := hb (x 11 4 && x 11 14)
    clear * - r8538 b8539 b8540 b8541 b8542 b8543 b8544 d8533 d8228 d8248 d8023 d8047
    omega
  have d8545 : (x 14 11).toNat = 1 := by
    have r8546 := hand2 (x 14 1) (x 14 11)
    have b8547 := hb (x 14 11)
    have b8548 := hb (x 14 1 && x 14 11)
    clear * - r8546 b8547 b8548 d8537
    omega
  have d8549 : (x 14 3).toNat = 1 := by
    have r8550 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
    have b8551 := hb (x 14 3)
    have b8552 := hb (x 14 11)
    clear * - r8550 b8551 b8552 d8545
    omega
  have d8553 : (x 17 12).toNat = 0 := by
    have r8554 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8555 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
    have e8556 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
    have b8557 := hb (x 14 3)
    have b8558 := hb (x 15 2)
    have b8559 := hb (x 16 13)
    have b8560 := hb (x 17 12)
    clear * - r8554 e8555 e8556 b8557 b8558 b8559 b8560 d8529 d8549
    omega
  have d8561 : (x 16 13).toNat = 0 := by
    have r8562 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8563 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
    have e8564 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
    have b8565 := hb (x 14 3)
    have b8566 := hb (x 15 2)
    have b8567 := hb (x 16 13)
    have b8568 := hb (x 17 12)
    clear * - r8562 e8563 e8564 b8565 b8566 b8567 b8568 d8553 d8529 d8549
    omega
  have d8569 : (x 14 2).toNat = 1 := by
    have r8570 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8571 := hb (x 14 2)
    have b8572 := hb (x 16 13)
    have b8573 := hb (x 15 1 && x 15 14)
    clear * - r8570 b8571 b8572 b8573 d8561 d8496
    omega
  have d8574 : (x 16 12).toNat = 0 := by
    have r8575 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8576 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e8577 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b8578 := hb (x 13 3)
    have b8579 := hb (x 14 2)
    have b8580 := hb (x 15 13)
    have b8581 := hb (x 16 12)
    clear * - r8575 e8576 e8577 b8578 b8579 b8580 b8581 d8504 d8569
    omega
  have d8582 : (x 16 4).toNat = 0 := by
    have r8583 : (x 16 4).toNat ≤ (x 16 12).toNat := himp _ _ (hp4 16)
    have b8584 := hb (x 16 4)
    have b8585 := hb (x 16 12)
    clear * - r8583 b8584 b8585 d8574
    omega
  have d8586 : (x 20 11).toNat = 1 := by
    have r8587 : 1 ≤ (x 20 11).toNat + (x 19 1 && x 19 12).toNat + (x 18 2 && x 18 13).toNat + (x 17 3 && x 17 14).toNat + (x 16 4).toNat := by have q := hcov11 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8588 := hb (x 16 4)
    have b8589 := hb (x 20 11)
    have b8590 := hb (x 19 1 && x 19 12)
    have b8591 := hb (x 18 2 && x 18 13)
    have b8592 := hb (x 17 3 && x 17 14)
    clear * - r8587 b8588 b8589 b8590 b8591 b8592 d8427 d8443 d8508 d8582
    omega
  have d8593 : (x 5 3).toNat = 0 := by
    have r8594 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8595 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e8596 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b8597 := hb (x 5 3)
    have b8598 := hb (x 6 2)
    have b8599 := hb (x 7 13)
    have b8600 := hb (x 8 12)
    clear * - r8594 e8595 e8596 b8597 b8598 b8599 b8600 d8172 d8184 d8155
    omega
  have d8601 : (x 5 11).toNat = 0 := by
    have r8602 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
    have b8603 := hb (x 5 3)
    have b8604 := hb (x 5 11)
    clear * - r8602 b8603 b8604 d8593
    omega
  have d8605 : (x 7 9).toNat = 0 := by
    have r8606 : (x 7 9).toNat ≤ (x 7 1).toNat := himp _ _ (hp9 7)
    have b8607 := hb (x 7 1)
    have b8608 := hb (x 7 9)
    clear * - r8606 b8607 b8608 d8147
    omega
  have d8609 : (x 9 7 && x 9 14).toNat = 0 := by
    have r8610 := hand2 (x 9 7) (x 9 14)
    have b8611 := hb (x 9 14)
    have b8612 := hb (x 9 7 && x 9 14)
    clear * - r8610 b8611 b8612 d8130
    omega
  have d8613 : (x 9 6).toNat = 0 := by
    have r8614 : (x 9 6).toNat ≤ (x 9 14).toNat := himp _ _ (hp6 9)
    have b8615 := hb (x 9 6)
    have b8616 := hb (x 9 14)
    clear * - r8614 b8615 b8616 d8130
    omega
  have d8617 : (x 6 10).toNat = 1 := by
    have r8618 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8619 := hb (x 1 5)
    have b8620 := hb (x 6 10)
    have b8621 := hb (x 5 1 && x 5 11)
    have b8622 := hb (x 4 2 && x 4 12)
    have b8623 := hb (x 3 3 && x 3 13)
    have b8624 := hb (x 2 4 && x 2 14)
    clear * - r8618 b8619 b8620 b8621 b8622 b8623 b8624 d8168 d7980 g10 g11 g0
    omega
  have d8625 : (x 23 8).toNat = 0 := by
    have r8626 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8627 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
    have e8628 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
    have e8629 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
    have e8630 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
    have e8631 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
    have e8632 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
    have b8633 := hb (x 16 7)
    have b8634 := hb (x 17 6)
    have b8635 := hb (x 18 5)
    have b8636 := hb (x 19 4)
    have b8637 := hb (x 20 11)
    have b8638 := hb (x 21 10)
    have b8639 := hb (x 22 9)
    have b8640 := hb (x 23 8)
    clear * - r8626 e8627 e8628 e8629 e8630 e8631 e8632 b8633 b8634 b8635 b8636 b8637 b8638 b8639 b8640 d8586 d8431 d8447 d8512
    omega
  have d8641 : (x 22 9).toNat = 0 := by
    have r8642 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8643 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
    have e8644 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
    have e8645 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
    have e8646 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
    have e8647 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
    have e8648 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
    have b8649 := hb (x 16 7)
    have b8650 := hb (x 17 6)
    have b8651 := hb (x 18 5)
    have b8652 := hb (x 19 4)
    have b8653 := hb (x 20 11)
    have b8654 := hb (x 21 10)
    have b8655 := hb (x 22 9)
    have b8656 := hb (x 23 8)
    clear * - r8642 e8643 e8644 e8645 e8646 e8647 e8648 b8649 b8650 b8651 b8652 b8653 b8654 b8655 b8656 d8625 d8586 d8431 d8447 d8512
    omega
  have d8657 : (x 21 10).toNat = 0 := by
    have r8658 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8659 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
    have e8660 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
    have e8661 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
    have e8662 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
    have e8663 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
    have e8664 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
    have b8665 := hb (x 16 7)
    have b8666 := hb (x 17 6)
    have b8667 := hb (x 18 5)
    have b8668 := hb (x 19 4)
    have b8669 := hb (x 20 11)
    have b8670 := hb (x 21 10)
    have b8671 := hb (x 22 9)
    have b8672 := hb (x 23 8)
    clear * - r8658 e8659 e8660 e8661 e8662 e8663 e8664 b8665 b8666 b8667 b8668 b8669 b8670 b8671 b8672 d8625 d8641 d8586 d8431 d8447 d8512
    omega
  have d8673 : (x 16 7).toNat = 0 := by
    have r8674 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8675 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
    have e8676 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
    have e8677 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
    have e8678 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
    have e8679 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
    have e8680 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
    have b8681 := hb (x 16 7)
    have b8682 := hb (x 17 6)
    have b8683 := hb (x 18 5)
    have b8684 := hb (x 19 4)
    have b8685 := hb (x 20 11)
    have b8686 := hb (x 21 10)
    have b8687 := hb (x 22 9)
    have b8688 := hb (x 23 8)
    clear * - r8674 e8675 e8676 e8677 e8678 e8679 e8680 b8681 b8682 b8683 b8684 b8685 b8686 b8687 b8688 d8625 d8641 d8657 d8586 d8431 d8447 d8512
    omega
  have d8689 : (x 15 8).toNat = 0 := by
    have r8690 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8691 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
    have e8692 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
    have e8693 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
    have e8694 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
    have e8695 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
    have e8696 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
    have b8697 := hb (x 8 7)
    have b8698 := hb (x 9 6)
    have b8699 := hb (x 10 5)
    have b8700 := hb (x 11 4)
    have b8701 := hb (x 12 11)
    have b8702 := hb (x 13 10)
    have b8703 := hb (x 14 9)
    have b8704 := hb (x 15 8)
    clear * - r8690 e8691 e8692 e8693 e8694 e8695 e8696 b8697 b8698 b8699 b8700 b8701 b8702 b8703 b8704 d8380 d8329 d8019 d8047 d8613
    omega
  have d8705 : (x 14 9).toNat = 0 := by
    have r8706 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8707 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
    have e8708 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
    have e8709 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
    have e8710 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
    have e8711 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
    have e8712 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
    have b8713 := hb (x 8 7)
    have b8714 := hb (x 9 6)
    have b8715 := hb (x 10 5)
    have b8716 := hb (x 11 4)
    have b8717 := hb (x 12 11)
    have b8718 := hb (x 13 10)
    have b8719 := hb (x 14 9)
    have b8720 := hb (x 15 8)
    clear * - r8706 e8707 e8708 e8709 e8710 e8711 e8712 b8713 b8714 b8715 b8716 b8717 b8718 b8719 b8720 d8689 d8380 d8329 d8019 d8047 d8613
    omega
  have d8721 : (x 14 2 && x 14 9).toNat = 0 := by
    have r8722 := hand2 (x 14 2) (x 14 9)
    have b8723 := hb (x 14 9)
    have b8724 := hb (x 14 2 && x 14 9)
    clear * - r8722 b8723 b8724 d8705
    omega
  have d8725 : (x 8 8).toNat = 0 := by
    have r8726 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8727 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e8728 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e8729 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e8730 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e8731 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e8732 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have b8733 := hb (x 1 7)
    have b8734 := hb (x 2 6)
    have b8735 := hb (x 3 5)
    have b8736 := hb (x 4 4)
    have b8737 := hb (x 5 11)
    have b8738 := hb (x 6 10)
    have b8739 := hb (x 7 9)
    have b8740 := hb (x 8 8)
    clear * - r8726 e8727 e8728 e8729 e8730 e8731 e8732 b8733 b8734 b8735 b8736 b8737 b8738 b8739 b8740 d8605 d8617 d8601 d7984 g5 g1
    omega
  have r8741 : 1 ≤ (x 16 7).toNat + (x 15 1 && x 15 8).toNat + (x 14 2 && x 14 9).toNat + (x 13 3 && x 13 10).toNat + (x 12 4 && x 12 11).toNat + (x 11 5 && x 11 12).toNat + (x 10 6 && x 10 13).toNat + (x 9 7 && x 9 14).toNat + (x 8 8).toNat := by have q := hcov7 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have b8742 := hb (x 8 8)
  have b8743 := hb (x 16 7)
  have b8744 := hb (x 15 1 && x 15 8)
  have b8745 := hb (x 14 2 && x 14 9)
  have b8746 := hb (x 13 3 && x 13 10)
  have b8747 := hb (x 12 4 && x 12 11)
  have b8748 := hb (x 11 5 && x 11 12)
  have b8749 := hb (x 10 6 && x 10 13)
  have b8750 := hb (x 9 7 && x 9 14)
  linarith only [r8741, b8742, b8743, b8744, b8745, b8746, b8747, b8748, b8749, b8750, d8673, d8500, d8721, d8384, d8305, d8015, d8043, d8609, d8725]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b0011000000001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-1) 8).toNat = 0)
    (g1 : (x (-1) 9).toNat = 0)
    (g2 : (x (-1) 12).toNat = 0)
    (g3 : (x (-1) 13).toNat = 0)
    (g4 : (x (-1) 14).toNat = 1)
    (g5 : (x 0 11).toNat = 1)
    (g6 : (x 0 13).toNat = 1)
    (g7 : (x 1 10).toNat = 0)
    (g8 : (x 1 12).toNat = 0)
    (g9 : (x 2 9).toNat = 0)
    (g10 : (x 3 8).toNat = 0)
    (g11 : (x 3 10).toNat = 0)
    (g12 : (x 5 6).toNat = 0)
    (g13 : (x 6 5).toNat = 0)
    (g14 : (x 7 4).toNat = 0)
    (g15 : (x 5 2 && x 5 6).toNat = 0)
    (g16 : (x 3 4 && x 3 8).toNat = 0)
    (g17 : (x 2 5 && x 2 9).toNat = 0)
    (g18 : (x 1 6 && x 1 10).toNat = 0)
    (g19 : (x 0 7 && x 0 11).toNat = 0)
    (g20 : (x (-1) 8 && x (-1) 12).toNat = 0)
    (g21 : (x 5 2 && x 5 8).toNat = 0)
    (g22 : (x 3 4 && x 3 10).toNat = 0)
    (g23 : (x 2 5 && x 2 11).toNat = 0)
    (g24 : (x 1 6 && x 1 12).toNat = 0)
    (g25 : (x 0 7 && x 0 13).toNat = 0)
    (g26 : (x (-1) 8 && x (-1) 14).toNat = 0)
    (g27 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g28 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g29 : (x 7 4 && x 7 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d8752 : (x (-2) 1).toNat = 0 := by
    have r8753 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8754 := hb (x (-2) 1)
    have b8755 := hb (x (-1) 14)
    clear * - r8753 b8754 b8755 g4
    omega
  have d8756 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
    have r8757 := hand1 (x (-2) 1) (x (-2) 14)
    have b8758 := hb (x (-2) 1)
    have b8759 := hb (x (-2) 1 && x (-2) 14)
    clear * - r8757 b8758 b8759 d8752
    omega
  have d8760 : (x (-2) 13).toNat = 0 := by
    have r8761 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
    have b8762 := hb (x (-2) 1)
    have b8763 := hb (x (-2) 13)
    clear * - r8761 b8762 b8763 d8752
    omega
  have d8764 : (x (-2) 9 && x (-2) 13).toNat = 0 := by
    have r8765 := hand2 (x (-2) 9) (x (-2) 13)
    have b8766 := hb (x (-2) 13)
    have b8767 := hb (x (-2) 9 && x (-2) 13)
    clear * - r8765 b8766 b8767 d8760
    omega
  have d8768 : (x (-2) 9).toNat = 0 := by
    have r8769 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
    have b8770 := hb (x (-2) 1)
    have b8771 := hb (x (-2) 9)
    clear * - r8769 b8770 b8771 d8752
    omega
  have d8772 : (x (-3) 2).toNat = 1 := by
    have r8773 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8774 := hb (x (-3) 2)
    have b8775 := hb (x (-1) 13)
    have b8776 := hb (x (-2) 1 && x (-2) 14)
    clear * - r8773 b8774 b8775 b8776 g3 d8756
    omega
  have d8777 : (x (-3) 14).toNat = 1 := by
    have r8778 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
    have b8779 := hb (x (-3) 2)
    have b8780 := hb (x (-3) 14)
    clear * - r8778 b8779 b8780 d8772
    omega
  have d8781 : (x (-4) 3).toNat = 0 := by
    have r8782 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8783 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e8784 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b8785 := hb (x (-4) 3)
    have b8786 := hb (x (-3) 2)
    have b8787 := hb (x (-2) 13)
    have b8788 := hb (x (-1) 12)
    clear * - r8782 e8783 e8784 b8785 b8786 b8787 b8788 g2 d8760 d8772
    omega
  have d8789 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
    have r8790 := hand1 (x (-4) 3) (x (-4) 12)
    have b8791 := hb (x (-4) 3)
    have b8792 := hb (x (-4) 3 && x (-4) 12)
    clear * - r8790 b8791 b8792 d8781
    omega
  have d8793 : (x (-4) 11).toNat = 0 := by
    have r8794 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
    have b8795 := hb (x (-4) 3)
    have b8796 := hb (x (-4) 11)
    clear * - r8794 b8795 b8796 d8781
    omega
  have r8797 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r8798 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r8799 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e8800 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
  have e8801 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
  have e8802 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
  have e8803 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
  have e8804 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
  have e8805 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
  have r8806 : 1 ≤ (x 7 4).toNat + (x 6 1 && x 6 5).toNat + (x 5 2 && x 5 6).toNat + (x 4 3 && x 4 7).toNat + (x 3 4 && x 3 8).toNat + (x 2 5 && x 2 9).toNat + (x 1 6 && x 1 10).toNat + (x 0 7 && x 0 11).toNat + (x (-1) 8 && x (-1) 12).toNat + (x (-2) 9 && x (-2) 13).toNat + (x (-3) 10 && x (-3) 14).toNat + (x (-4) 11).toNat := by have q := hcov4 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e8807 : (x 6 1 && x 6 5).toNat = (x 6 5).toNat := handr _ _ (fun h => hp13 6 (hp5 6 (h)))
  have e8808 : (x (-3) 10 && x (-3) 14).toNat = (x (-3) 10).toNat := handl _ _ (fun h => hp2 (-3) (hp10 (-3) (h)))
  have r8809 : 1 ≤ (x 7 6).toNat + (x 6 1 && x 6 7).toNat + (x 5 2 && x 5 8).toNat + (x 4 3 && x 4 9).toNat + (x 3 4 && x 3 10).toNat + (x 2 5 && x 2 11).toNat + (x 1 6 && x 1 12).toNat + (x 0 7 && x 0 13).toNat + (x (-1) 8 && x (-1) 14).toNat + (x (-2) 9).toNat := by have q := hcov6 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r8810 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r8811 : 1 ≤ (x 11 10).toNat + (x 10 1 && x 10 11).toNat + (x 9 2 && x 9 12).toNat + (x 8 3 && x 8 13).toNat + (x 7 4 && x 7 14).toNat + (x 6 5).toNat := by have q := hcov10 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r8812 : (x 11 10).toNat ≤ (x 11 2).toNat := himp _ _ (hp10 11)
  have r8813 := hand2 (x 4 3) (x 4 7)
  have r8814 := hand2 (x 6 1) (x 6 7)
  have r8815 := hand2 (x 4 3) (x 4 9)
  have r8816 := hand1 (x (-5) 4) (x (-5) 13)
  have r8817 := hand1 (x (-6) 5) (x (-6) 14)
  have r8818 := hand1 (x 10 1) (x 10 11)
  have r8819 := hand1 (x 9 2) (x 9 12)
  have r8820 := hand1 (x 8 3) (x 8 13)
  linarith only [r8797, r8798, r8799, e8800, e8801, e8802, e8803, e8804, e8805, r8806, e8807, e8808, r8809, r8810, r8811, r8812, r8813, r8814, r8815, r8816, r8817, r8818, r8819, r8820, d8793, d8777, d8768, d8760, g0, g1, g2, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, d8764, g21, g22, g23, g24, g25, g26, g27, g28, d8789, g29]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b001100000001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-1) 10).toNat = 0)
    (g1 : (x (-1) 11).toNat = 0)
    (g2 : (x (-1) 12).toNat = 1)
    (g3 : (x (-1) 13).toNat = 0)
    (g4 : (x (-2) 1 && x (-2) 11).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d8885 : (x (-2) 13).toNat = 0 := by
    have r8886 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8887 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e8888 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b8889 := hb (x (-4) 3)
    have b8890 := hb (x (-3) 2)
    have b8891 := hb (x (-2) 13)
    have b8892 := hb (x (-1) 12)
    clear * - r8886 e8887 e8888 b8889 b8890 b8891 b8892 g2
    omega
  have d8893 : (x (-3) 2).toNat = 0 := by
    have r8894 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8895 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e8896 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b8897 := hb (x (-4) 3)
    have b8898 := hb (x (-3) 2)
    have b8899 := hb (x (-2) 13)
    have b8900 := hb (x (-1) 12)
    clear * - r8894 e8895 e8896 b8897 b8898 b8899 b8900 g2 d8885
    omega
  have d8901 : (x (-3) 2 && x (-3) 13).toNat = 0 := by
    have r8902 := hand1 (x (-3) 2) (x (-3) 13)
    have b8903 := hb (x (-3) 2)
    have b8904 := hb (x (-3) 2 && x (-3) 13)
    clear * - r8902 b8903 b8904 d8893
    omega
  have d8905 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
    have r8906 := hand1 (x (-3) 2) (x (-3) 12)
    have b8907 := hb (x (-3) 2)
    have b8908 := hb (x (-3) 2 && x (-3) 12)
    clear * - r8906 b8907 b8908 d8893
    omega
  have d8909 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
    have r8910 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8911 := hb (x (-3) 2)
    have b8912 := hb (x (-1) 13)
    have b8913 := hb (x (-2) 1 && x (-2) 14)
    clear * - r8910 b8911 b8912 b8913 g3 d8893
    omega
  have d8914 : (x (-2) 14).toNat = 1 := by
    have r8915 := hand2 (x (-2) 1) (x (-2) 14)
    have b8916 := hb (x (-2) 14)
    have b8917 := hb (x (-2) 1 && x (-2) 14)
    clear * - r8915 b8916 b8917 d8909
    omega
  have d8918 : (x (-3) 1).toNat = 0 := by
    have r8919 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8920 := hb (x (-3) 1)
    have b8921 := hb (x (-2) 14)
    clear * - r8919 b8920 b8921 d8914
    omega
  have d8922 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
    have r8923 := hand1 (x (-3) 1) (x (-3) 14)
    have b8924 := hb (x (-3) 1)
    have b8925 := hb (x (-3) 1 && x (-3) 14)
    clear * - r8923 b8924 b8925 d8918
    omega
  have d8926 : (x (-4) 2).toNat = 1 := by
    have r8927 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8928 := hb (x (-4) 2)
    have b8929 := hb (x (-2) 13)
    have b8930 := hb (x (-3) 1 && x (-3) 14)
    clear * - r8927 b8928 b8929 b8930 d8885 d8922
    omega
  have d8931 : (x (-4) 14).toNat = 1 := by
    have r8932 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
    have b8933 := hb (x (-4) 2)
    have b8934 := hb (x (-4) 14)
    clear * - r8932 b8933 b8934 d8926
    omega
  have d8935 : (x (-5) 1).toNat = 0 := by
    have r8936 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8937 := hb (x (-5) 1)
    have b8938 := hb (x (-4) 14)
    clear * - r8936 b8937 b8938 d8931
    omega
  have d8939 : (x (-5) 13).toNat = 0 := by
    have r8940 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
    have b8941 := hb (x (-5) 1)
    have b8942 := hb (x (-5) 13)
    clear * - r8940 b8941 b8942 d8935
    omega
  have d8943 : (x (-3) 13).toNat = 0 := by
    have r8944 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
    have b8945 := hb (x (-3) 1)
    have b8946 := hb (x (-3) 13)
    clear * - r8944 b8945 b8946 d8918
    omega
  have d8947 : (x (-4) 3).toNat = 0 := by
    have r8948 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8949 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e8950 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b8951 := hb (x (-4) 3)
    have b8952 := hb (x (-3) 2)
    have b8953 := hb (x (-2) 13)
    have b8954 := hb (x (-1) 12)
    clear * - r8948 e8949 e8950 b8951 b8952 b8953 b8954 g2 d8885 d8893
    omega
  have d8955 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
    have r8956 := hand1 (x (-4) 3) (x (-4) 14)
    have b8957 := hb (x (-4) 3)
    have b8958 := hb (x (-4) 3 && x (-4) 14)
    clear * - r8956 b8957 b8958 d8947
    omega
  have d8959 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
    have r8960 := hand1 (x (-4) 3) (x (-4) 13)
    have b8961 := hb (x (-4) 3)
    have b8962 := hb (x (-4) 3 && x (-4) 13)
    clear * - r8960 b8961 b8962 d8947
    omega
  have d8963 : (x (-2) 12).toNat = 0 := by
    have r8964 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8965 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
    have e8966 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
    have b8967 := hb (x (-5) 3)
    have b8968 := hb (x (-4) 2)
    have b8969 := hb (x (-3) 13)
    have b8970 := hb (x (-2) 12)
    clear * - r8964 e8965 e8966 b8967 b8968 b8969 b8970 d8943 d8926
    omega
  have d8971 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
    have r8972 := hand2 (x (-2) 1) (x (-2) 12)
    have b8973 := hb (x (-2) 12)
    have b8974 := hb (x (-2) 1 && x (-2) 12)
    clear * - r8972 b8973 b8974 d8963
    omega
  have d8975 : (x (-5) 4).toNat = 1 := by
    have r8976 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8977 := hb (x (-5) 4)
    have b8978 := hb (x (-1) 11)
    have b8979 := hb (x (-2) 1 && x (-2) 12)
    have b8980 := hb (x (-3) 2 && x (-3) 13)
    have b8981 := hb (x (-4) 3 && x (-4) 14)
    clear * - r8976 b8977 b8978 b8979 b8980 b8981 g1 d8971 d8901 d8955
    omega
  have d8982 : (x (-5) 12).toNat = 1 := by
    have r8983 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
    have b8984 := hb (x (-5) 4)
    have b8985 := hb (x (-5) 12)
    clear * - r8983 b8984 b8985 d8975
    omega
  have d8986 : (x (-6) 13).toNat = 0 := by
    have r8987 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8988 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
    have e8989 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
    have b8990 := hb (x (-8) 3)
    have b8991 := hb (x (-7) 2)
    have b8992 := hb (x (-6) 13)
    have b8993 := hb (x (-5) 12)
    clear * - r8987 e8988 e8989 b8990 b8991 b8992 b8993 d8982
    omega
  have d8994 : (x (-6) 5).toNat = 0 := by
    have r8995 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
    have b8996 := hb (x (-6) 5)
    have b8997 := hb (x (-6) 13)
    clear * - r8995 b8996 b8997 d8986
    omega
  have d8998 : (x (-7) 2).toNat = 0 := by
    have r8999 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9000 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
    have e9001 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
    have b9002 := hb (x (-8) 3)
    have b9003 := hb (x (-7) 2)
    have b9004 := hb (x (-6) 13)
    have b9005 := hb (x (-5) 12)
    clear * - r8999 e9000 e9001 b9002 b9003 b9004 b9005 d8982 d8986
    omega
  have d9006 : (x (-6) 1 && x (-6) 14).toNat = 1 := by
    have r9007 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9008 := hb (x (-7) 2)
    have b9009 := hb (x (-5) 13)
    have b9010 := hb (x (-6) 1 && x (-6) 14)
    clear * - r9007 b9008 b9009 b9010 d8939 d8998
    omega
  have d9011 : (x (-6) 1).toNat = 1 := by
    have r9012 := hand1 (x (-6) 1) (x (-6) 14)
    have b9013 := hb (x (-6) 1)
    have b9014 := hb (x (-6) 1 && x (-6) 14)
    clear * - r9012 b9013 b9014 d9006
    omega
  have d9015 : (x (-5) 14).toNat = 0 := by
    have r9016 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9017 := hb (x (-6) 1)
    have b9018 := hb (x (-5) 14)
    clear * - r9016 b9017 b9018 d9011
    omega
  have d9019 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
    have r9020 := hand2 (x (-5) 4) (x (-5) 14)
    have b9021 := hb (x (-5) 14)
    have b9022 := hb (x (-5) 4 && x (-5) 14)
    clear * - r9020 b9021 b9022 d9015
    omega
  have r9023 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have b9024 := hb (x (-6) 5)
  have b9025 := hb (x (-1) 10)
  have b9026 := hb (x (-2) 1 && x (-2) 11)
  have b9027 := hb (x (-3) 2 && x (-3) 12)
  have b9028 := hb (x (-4) 3 && x (-4) 13)
  have b9029 := hb (x (-5) 4 && x (-5) 14)
  linarith only [r9023, b9024, b9025, b9026, b9027, b9028, b9029, g0, g4, d8905, d8959, d9019, d8994]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b00110000001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 1 4).toNat = 0)
    (g1 : (x 1 11).toNat = 1)
    (g2 : (x 3 2).toNat = 0)
    (g3 : (x 3 13).toNat = 0)
    (g4 : (x 5 2).toNat = 0)
    (g5 : (x 3 2 && x 3 13).toNat = 0)
    (g6 : (x 7 1 && x 7 12).toNat = 0)
    (g7 : (x 6 2 && x 6 13).toNat = 0)
    (g8 : (x 5 3 && x 5 14).toNat = 0)
    (g9 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d9031 : (x 1 3).toNat = 1 := by
    have r9032 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
    have b9033 := hb (x 1 3)
    have b9034 := hb (x 1 11)
    clear * - r9032 b9033 b9034 g1
    omega
  have d9035 : (x 4 12).toNat = 0 := by
    have r9036 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9037 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e9038 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b9039 := hb (x 1 3)
    have b9040 := hb (x 2 2)
    have b9041 := hb (x 3 13)
    have b9042 := hb (x 4 12)
    clear * - r9036 e9037 e9038 b9039 b9040 b9041 b9042 g3 d9031
    omega
  have d9043 : (x 4 1 && x 4 12).toNat = 0 := by
    have r9044 := hand2 (x 4 1) (x 4 12)
    have b9045 := hb (x 4 12)
    have b9046 := hb (x 4 1 && x 4 12)
    clear * - r9044 b9045 b9046 d9035
    omega
  have d9047 : (x 4 4).toNat = 0 := by
    have r9048 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
    have b9049 := hb (x 4 4)
    have b9050 := hb (x 4 12)
    clear * - r9048 b9049 b9050 d9035
    omega
  have d9051 : (x 2 2).toNat = 0 := by
    have r9052 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9053 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e9054 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b9055 := hb (x 1 3)
    have b9056 := hb (x 2 2)
    have b9057 := hb (x 3 13)
    have b9058 := hb (x 4 12)
    clear * - r9052 e9053 e9054 b9055 b9056 b9057 b9058 d9035 g3 d9031
    omega
  have d9059 : (x 4 13).toNat = 1 := by
    have r9060 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9061 := hb (x 2 2)
    have b9062 := hb (x 4 13)
    have b9063 := hb (x 3 1 && x 3 14)
    clear * - r9060 b9061 b9062 b9063 g9 d9051
    omega
  have d9064 : (x 5 12).toNat = 0 := by
    have r9065 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9066 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e9067 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b9068 := hb (x 2 3)
    have b9069 := hb (x 3 2)
    have b9070 := hb (x 4 13)
    have b9071 := hb (x 5 12)
    clear * - r9065 e9066 e9067 b9068 b9069 b9070 b9071 d9059 g2
    omega
  have d9072 : (x 5 4).toNat = 0 := by
    have r9073 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
    have b9074 := hb (x 5 4)
    have b9075 := hb (x 5 12)
    clear * - r9073 b9074 b9075 d9064
    omega
  have d9076 : (x 2 3).toNat = 0 := by
    have r9077 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9078 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e9079 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b9080 := hb (x 2 3)
    have b9081 := hb (x 3 2)
    have b9082 := hb (x 4 13)
    have b9083 := hb (x 5 12)
    clear * - r9077 e9078 e9079 b9080 b9081 b9082 b9083 d9064 d9059 g2
    omega
  have d9084 : (x 2 3 && x 2 14).toNat = 0 := by
    have r9085 := hand1 (x 2 3) (x 2 14)
    have b9086 := hb (x 2 3)
    have b9087 := hb (x 2 3 && x 2 14)
    clear * - r9085 b9086 b9087 d9076
    omega
  have d9088 : (x 8 11).toNat = 1 := by
    have r9089 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9090 := hb (x 4 4)
    have b9091 := hb (x 8 11)
    have b9092 := hb (x 7 1 && x 7 12)
    have b9093 := hb (x 6 2 && x 6 13)
    have b9094 := hb (x 5 3 && x 5 14)
    clear * - r9089 b9090 b9091 b9092 b9093 b9094 g6 g7 g8 d9047
    omega
  have d9095 : (x 8 3).toNat = 1 := by
    have r9096 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
    have b9097 := hb (x 8 3)
    have b9098 := hb (x 8 11)
    clear * - r9096 b9097 b9098 d9088
    omega
  have d9099 : (x 11 12).toNat = 0 := by
    have r9100 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9101 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e9102 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b9103 := hb (x 8 3)
    have b9104 := hb (x 9 2)
    have b9105 := hb (x 10 13)
    have b9106 := hb (x 11 12)
    clear * - r9100 e9101 e9102 b9103 b9104 b9105 b9106 d9095
    omega
  have d9107 : (x 11 1 && x 11 12).toNat = 0 := by
    have r9108 := hand2 (x 11 1) (x 11 12)
    have b9109 := hb (x 11 12)
    have b9110 := hb (x 11 1 && x 11 12)
    clear * - r9108 b9109 b9110 d9099
    omega
  have d9111 : (x 10 13).toNat = 0 := by
    have r9112 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9113 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e9114 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b9115 := hb (x 8 3)
    have b9116 := hb (x 9 2)
    have b9117 := hb (x 10 13)
    have b9118 := hb (x 11 12)
    clear * - r9112 e9113 e9114 b9115 b9116 b9117 b9118 d9099 d9095
    omega
  have d9119 : (x 10 2 && x 10 13).toNat = 0 := by
    have r9120 := hand2 (x 10 2) (x 10 13)
    have b9121 := hb (x 10 13)
    have b9122 := hb (x 10 2 && x 10 13)
    clear * - r9120 b9121 b9122 d9111
    omega
  have d9123 : (x 9 2).toNat = 0 := by
    have r9124 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9125 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e9126 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b9127 := hb (x 8 3)
    have b9128 := hb (x 9 2)
    have b9129 := hb (x 10 13)
    have b9130 := hb (x 11 12)
    clear * - r9124 e9125 e9126 b9127 b9128 b9129 b9130 d9099 d9111 d9095
    omega
  have d9131 : (x 5 11).toNat = 1 := by
    have r9132 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9133 := hb (x 1 4)
    have b9134 := hb (x 5 11)
    have b9135 := hb (x 4 1 && x 4 12)
    have b9136 := hb (x 3 2 && x 3 13)
    have b9137 := hb (x 2 3 && x 2 14)
    clear * - r9132 b9133 b9134 b9135 b9136 b9137 d9043 g5 d9084 g0
    omega
  have d9138 : (x 5 3).toNat = 1 := by
    have r9139 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
    have b9140 := hb (x 5 3)
    have b9141 := hb (x 5 11)
    clear * - r9139 b9140 b9141 d9131
    omega
  have d9142 : (x 8 12).toNat = 0 := by
    have r9143 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9144 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e9145 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b9146 := hb (x 5 3)
    have b9147 := hb (x 6 2)
    have b9148 := hb (x 7 13)
    have b9149 := hb (x 8 12)
    clear * - r9143 e9144 e9145 b9146 b9147 b9148 b9149 d9138
    omega
  have d9150 : (x 8 1 && x 8 12).toNat = 0 := by
    have r9151 := hand2 (x 8 1) (x 8 12)
    have b9152 := hb (x 8 12)
    have b9153 := hb (x 8 1 && x 8 12)
    clear * - r9151 b9152 b9153 d9142
    omega
  have d9154 : (x 8 4).toNat = 0 := by
    have r9155 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
    have b9156 := hb (x 8 4)
    have b9157 := hb (x 8 12)
    clear * - r9155 b9156 b9157 d9142
    omega
  have d9158 : (x 7 13).toNat = 0 := by
    have r9159 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9160 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e9161 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b9162 := hb (x 5 3)
    have b9163 := hb (x 6 2)
    have b9164 := hb (x 7 13)
    have b9165 := hb (x 8 12)
    clear * - r9159 e9160 e9161 b9162 b9163 b9164 b9165 d9142 d9138
    omega
  have d9166 : (x 7 2 && x 7 13).toNat = 0 := by
    have r9167 := hand2 (x 7 2) (x 7 13)
    have b9168 := hb (x 7 13)
    have b9169 := hb (x 7 2 && x 7 13)
    clear * - r9167 b9168 b9169 d9158
    omega
  have d9170 : (x 6 1 && x 6 14).toNat = 1 := by
    have r9171 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9172 := hb (x 5 2)
    have b9173 := hb (x 7 13)
    have b9174 := hb (x 6 1 && x 6 14)
    clear * - r9171 b9172 b9173 b9174 d9158 g4
    omega
  have d9175 : (x 6 1).toNat = 1 := by
    have r9176 := hand1 (x 6 1) (x 6 14)
    have b9177 := hb (x 6 1)
    have b9178 := hb (x 6 1 && x 6 14)
    clear * - r9176 b9177 b9178 d9170
    omega
  have d9179 : (x 7 14).toNat = 0 := by
    have r9180 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9181 := hb (x 6 1)
    have b9182 := hb (x 7 14)
    clear * - r9180 b9181 b9182 d9175
    omega
  have d9183 : (x 7 1 && x 7 14).toNat = 0 := by
    have r9184 := hand2 (x 7 1) (x 7 14)
    have b9185 := hb (x 7 14)
    have b9186 := hb (x 7 1 && x 7 14)
    clear * - r9184 b9185 b9186 d9179
    omega
  have d9187 : (x 7 2).toNat = 0 := by
    have r9188 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
    have b9189 := hb (x 7 2)
    have b9190 := hb (x 7 14)
    clear * - r9188 b9189 b9190 d9179
    omega
  have d9191 : (x 6 2).toNat = 0 := by
    have r9192 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9193 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e9194 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b9195 := hb (x 5 3)
    have b9196 := hb (x 6 2)
    have b9197 := hb (x 7 13)
    have b9198 := hb (x 8 12)
    clear * - r9192 e9193 e9194 b9195 b9196 b9197 b9198 d9142 d9158 d9138
    omega
  have d9199 : (x 8 13).toNat = 1 := by
    have r9200 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9201 := hb (x 6 2)
    have b9202 := hb (x 8 13)
    have b9203 := hb (x 7 1 && x 7 14)
    clear * - r9200 b9201 b9202 b9203 d9183 d9191
    omega
  have d9204 : (x 8 1).toNat = 1 := by
    have r9205 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
    have b9206 := hb (x 8 1)
    have b9207 := hb (x 8 13)
    clear * - r9205 b9206 b9207 d9199
    omega
  have d9208 : (x 9 14).toNat = 0 := by
    have r9209 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9210 := hb (x 8 1)
    have b9211 := hb (x 9 14)
    clear * - r9209 b9210 b9211 d9204
    omega
  have d9212 : (x 9 3 && x 9 14).toNat = 0 := by
    have r9213 := hand2 (x 9 3) (x 9 14)
    have b9214 := hb (x 9 14)
    have b9215 := hb (x 9 3 && x 9 14)
    clear * - r9213 b9214 b9215 d9208
    omega
  have d9216 : (x 12 11).toNat = 1 := by
    have r9217 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9218 := hb (x 8 4)
    have b9219 := hb (x 12 11)
    have b9220 := hb (x 11 1 && x 11 12)
    have b9221 := hb (x 10 2 && x 10 13)
    have b9222 := hb (x 9 3 && x 9 14)
    clear * - r9217 b9218 b9219 b9220 b9221 b9222 d9107 d9119 d9212 d9154
    omega
  have d9223 : (x 12 3).toNat = 1 := by
    have r9224 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
    have b9225 := hb (x 12 3)
    have b9226 := hb (x 12 11)
    clear * - r9224 b9225 b9226 d9216
    omega
  have d9227 : (x 15 12).toNat = 0 := by
    have r9228 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9229 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e9230 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b9231 := hb (x 12 3)
    have b9232 := hb (x 13 2)
    have b9233 := hb (x 14 13)
    have b9234 := hb (x 15 12)
    clear * - r9228 e9229 e9230 b9231 b9232 b9233 b9234 d9223
    omega
  have d9235 : (x 15 1 && x 15 12).toNat = 0 := by
    have r9236 := hand2 (x 15 1) (x 15 12)
    have b9237 := hb (x 15 12)
    have b9238 := hb (x 15 1 && x 15 12)
    clear * - r9236 b9237 b9238 d9227
    omega
  have d9239 : (x 14 13).toNat = 0 := by
    have r9240 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9241 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e9242 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b9243 := hb (x 12 3)
    have b9244 := hb (x 13 2)
    have b9245 := hb (x 14 13)
    have b9246 := hb (x 15 12)
    clear * - r9240 e9241 e9242 b9243 b9244 b9245 b9246 d9227 d9223
    omega
  have d9247 : (x 14 2 && x 14 13).toNat = 0 := by
    have r9248 := hand2 (x 14 2) (x 14 13)
    have b9249 := hb (x 14 13)
    have b9250 := hb (x 14 2 && x 14 13)
    clear * - r9248 b9249 b9250 d9239
    omega
  have d9251 : (x 13 2).toNat = 0 := by
    have r9252 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9253 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e9254 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b9255 := hb (x 12 3)
    have b9256 := hb (x 13 2)
    have b9257 := hb (x 14 13)
    have b9258 := hb (x 15 12)
    clear * - r9252 e9253 e9254 b9255 b9256 b9257 b9258 d9227 d9239 d9223
    omega
  have d9259 : (x 9 12).toNat = 0 := by
    have r9260 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9261 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e9262 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b9263 := hb (x 6 3)
    have b9264 := hb (x 7 2)
    have b9265 := hb (x 8 13)
    have b9266 := hb (x 9 12)
    clear * - r9260 e9261 e9262 b9263 b9264 b9265 b9266 d9199 d9187
    omega
  have d9267 : (x 9 4).toNat = 0 := by
    have r9268 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
    have b9269 := hb (x 9 4)
    have b9270 := hb (x 9 12)
    clear * - r9268 b9269 b9270 d9259
    omega
  have d9271 : (x 6 3).toNat = 0 := by
    have r9272 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9273 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e9274 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b9275 := hb (x 6 3)
    have b9276 := hb (x 7 2)
    have b9277 := hb (x 8 13)
    have b9278 := hb (x 9 12)
    clear * - r9272 e9273 e9274 b9275 b9276 b9277 b9278 d9259 d9199 d9187
    omega
  have d9279 : (x 6 3 && x 6 14).toNat = 0 := by
    have r9280 := hand1 (x 6 3) (x 6 14)
    have b9281 := hb (x 6 3)
    have b9282 := hb (x 6 3 && x 6 14)
    clear * - r9280 b9281 b9282 d9271
    omega
  have d9283 : (x 9 11).toNat = 1 := by
    have r9284 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9285 := hb (x 5 4)
    have b9286 := hb (x 9 11)
    have b9287 := hb (x 8 1 && x 8 12)
    have b9288 := hb (x 7 2 && x 7 13)
    have b9289 := hb (x 6 3 && x 6 14)
    clear * - r9284 b9285 b9286 b9287 b9288 b9289 d9150 d9166 d9279 d9072
    omega
  have d9290 : (x 9 3).toNat = 1 := by
    have r9291 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
    have b9292 := hb (x 9 3)
    have b9293 := hb (x 9 11)
    clear * - r9291 b9292 b9293 d9283
    omega
  have d9294 : (x 12 12).toNat = 0 := by
    have r9295 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9296 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e9297 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b9298 := hb (x 9 3)
    have b9299 := hb (x 10 2)
    have b9300 := hb (x 11 13)
    have b9301 := hb (x 12 12)
    clear * - r9295 e9296 e9297 b9298 b9299 b9300 b9301 d9290
    omega
  have d9302 : (x 12 1 && x 12 12).toNat = 0 := by
    have r9303 := hand2 (x 12 1) (x 12 12)
    have b9304 := hb (x 12 12)
    have b9305 := hb (x 12 1 && x 12 12)
    clear * - r9303 b9304 b9305 d9294
    omega
  have d9306 : (x 12 4).toNat = 0 := by
    have r9307 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
    have b9308 := hb (x 12 4)
    have b9309 := hb (x 12 12)
    clear * - r9307 b9308 b9309 d9294
    omega
  have d9310 : (x 11 13).toNat = 0 := by
    have r9311 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9312 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e9313 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b9314 := hb (x 9 3)
    have b9315 := hb (x 10 2)
    have b9316 := hb (x 11 13)
    have b9317 := hb (x 12 12)
    clear * - r9311 e9312 e9313 b9314 b9315 b9316 b9317 d9294 d9290
    omega
  have d9318 : (x 11 2 && x 11 13).toNat = 0 := by
    have r9319 := hand2 (x 11 2) (x 11 13)
    have b9320 := hb (x 11 13)
    have b9321 := hb (x 11 2 && x 11 13)
    clear * - r9319 b9320 b9321 d9310
    omega
  have d9322 : (x 10 1 && x 10 14).toNat = 1 := by
    have r9323 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9324 := hb (x 9 2)
    have b9325 := hb (x 11 13)
    have b9326 := hb (x 10 1 && x 10 14)
    clear * - r9323 b9324 b9325 b9326 d9310 d9123
    omega
  have d9327 : (x 10 1).toNat = 1 := by
    have r9328 := hand1 (x 10 1) (x 10 14)
    have b9329 := hb (x 10 1)
    have b9330 := hb (x 10 1 && x 10 14)
    clear * - r9328 b9329 b9330 d9322
    omega
  have d9331 : (x 11 14).toNat = 0 := by
    have r9332 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9333 := hb (x 10 1)
    have b9334 := hb (x 11 14)
    clear * - r9332 b9333 b9334 d9327
    omega
  have d9335 : (x 11 1 && x 11 14).toNat = 0 := by
    have r9336 := hand2 (x 11 1) (x 11 14)
    have b9337 := hb (x 11 14)
    have b9338 := hb (x 11 1 && x 11 14)
    clear * - r9336 b9337 b9338 d9331
    omega
  have d9339 : (x 11 2).toNat = 0 := by
    have r9340 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
    have b9341 := hb (x 11 2)
    have b9342 := hb (x 11 14)
    clear * - r9340 b9341 b9342 d9331
    omega
  have d9343 : (x 10 2).toNat = 0 := by
    have r9344 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9345 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e9346 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b9347 := hb (x 9 3)
    have b9348 := hb (x 10 2)
    have b9349 := hb (x 11 13)
    have b9350 := hb (x 12 12)
    clear * - r9344 e9345 e9346 b9347 b9348 b9349 b9350 d9294 d9310 d9290
    omega
  have d9351 : (x 12 13).toNat = 1 := by
    have r9352 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9353 := hb (x 10 2)
    have b9354 := hb (x 12 13)
    have b9355 := hb (x 11 1 && x 11 14)
    clear * - r9352 b9353 b9354 b9355 d9335 d9343
    omega
  have d9356 : (x 12 1).toNat = 1 := by
    have r9357 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
    have b9358 := hb (x 12 1)
    have b9359 := hb (x 12 13)
    clear * - r9357 b9358 b9359 d9351
    omega
  have d9360 : (x 13 14).toNat = 0 := by
    have r9361 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9362 := hb (x 12 1)
    have b9363 := hb (x 13 14)
    clear * - r9361 b9362 b9363 d9356
    omega
  have d9364 : (x 13 1 && x 13 14).toNat = 0 := by
    have r9365 := hand2 (x 13 1) (x 13 14)
    have b9366 := hb (x 13 14)
    have b9367 := hb (x 13 1 && x 13 14)
    clear * - r9365 b9366 b9367 d9360
    omega
  have d9368 : (x 12 2).toNat = 1 := by
    have r9369 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9370 := hb (x 12 2)
    have b9371 := hb (x 14 13)
    have b9372 := hb (x 13 1 && x 13 14)
    clear * - r9369 b9370 b9371 b9372 d9239 d9364
    omega
  have d9373 : (x 14 12).toNat = 0 := by
    have r9374 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9375 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e9376 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b9377 := hb (x 11 3)
    have b9378 := hb (x 12 2)
    have b9379 := hb (x 13 13)
    have b9380 := hb (x 14 12)
    clear * - r9374 e9375 e9376 b9377 b9378 b9379 b9380 d9368
    omega
  have d9381 : (x 14 4).toNat = 0 := by
    have r9382 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
    have b9383 := hb (x 14 4)
    have b9384 := hb (x 14 12)
    clear * - r9382 b9383 b9384 d9373
    omega
  have d9385 : (x 14 4 && x 14 14).toNat = 0 := by
    have r9386 := hand1 (x 14 4) (x 14 14)
    have b9387 := hb (x 14 4)
    have b9388 := hb (x 14 4 && x 14 14)
    clear * - r9386 b9387 b9388 d9381
    omega
  have d9389 : (x 13 13).toNat = 0 := by
    have r9390 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9391 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e9392 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b9393 := hb (x 11 3)
    have b9394 := hb (x 12 2)
    have b9395 := hb (x 13 13)
    have b9396 := hb (x 14 12)
    clear * - r9390 e9391 e9392 b9393 b9394 b9395 b9396 d9373 d9368
    omega
  have d9397 : (x 13 5).toNat = 0 := by
    have r9398 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
    have b9399 := hb (x 13 5)
    have b9400 := hb (x 13 13)
    clear * - r9398 b9399 b9400 d9389
    omega
  have d9401 : (x 13 3 && x 13 14).toNat = 0 := by
    have r9402 := hand2 (x 13 3) (x 13 14)
    have b9403 := hb (x 13 14)
    have b9404 := hb (x 13 3 && x 13 14)
    clear * - r9402 b9403 b9404 d9360
    omega
  have d9405 : (x 16 11).toNat = 1 := by
    have r9406 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9407 := hb (x 12 4)
    have b9408 := hb (x 16 11)
    have b9409 := hb (x 15 1 && x 15 12)
    have b9410 := hb (x 14 2 && x 14 13)
    have b9411 := hb (x 13 3 && x 13 14)
    clear * - r9406 b9407 b9408 b9409 b9410 b9411 d9235 d9247 d9401 d9306
    omega
  have d9412 : (x 16 3).toNat = 1 := by
    have r9413 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
    have b9414 := hb (x 16 3)
    have b9415 := hb (x 16 11)
    clear * - r9413 b9414 b9415 d9405
    omega
  have d9416 : (x 19 12).toNat = 0 := by
    have r9417 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9418 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e9419 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have b9420 := hb (x 16 3)
    have b9421 := hb (x 17 2)
    have b9422 := hb (x 18 13)
    have b9423 := hb (x 19 12)
    clear * - r9417 e9418 e9419 b9420 b9421 b9422 b9423 d9412
    omega
  have d9424 : (x 18 13).toNat = 0 := by
    have r9425 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9426 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e9427 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have b9428 := hb (x 16 3)
    have b9429 := hb (x 17 2)
    have b9430 := hb (x 18 13)
    have b9431 := hb (x 19 12)
    clear * - r9425 e9426 e9427 b9428 b9429 b9430 b9431 d9416 d9412
    omega
  have d9432 : (x 17 2).toNat = 0 := by
    have r9433 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9434 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e9435 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have b9436 := hb (x 16 3)
    have b9437 := hb (x 17 2)
    have b9438 := hb (x 18 13)
    have b9439 := hb (x 19 12)
    clear * - r9433 e9434 e9435 b9436 b9437 b9438 b9439 d9416 d9424 d9412
    omega
  have d9440 : (x 13 12).toNat = 0 := by
    have r9441 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9442 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e9443 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b9444 := hb (x 10 3)
    have b9445 := hb (x 11 2)
    have b9446 := hb (x 12 13)
    have b9447 := hb (x 13 12)
    clear * - r9441 e9442 e9443 b9444 b9445 b9446 b9447 d9351 d9339
    omega
  have d9448 : (x 13 4).toNat = 0 := by
    have r9449 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
    have b9450 := hb (x 13 4)
    have b9451 := hb (x 13 12)
    clear * - r9449 b9450 b9451 d9440
    omega
  have d9452 : (x 10 3).toNat = 0 := by
    have r9453 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9454 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e9455 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b9456 := hb (x 10 3)
    have b9457 := hb (x 11 2)
    have b9458 := hb (x 12 13)
    have b9459 := hb (x 13 12)
    clear * - r9453 e9454 e9455 b9456 b9457 b9458 b9459 d9440 d9351 d9339
    omega
  have d9460 : (x 10 3 && x 10 14).toNat = 0 := by
    have r9461 := hand1 (x 10 3) (x 10 14)
    have b9462 := hb (x 10 3)
    have b9463 := hb (x 10 3 && x 10 14)
    clear * - r9461 b9462 b9463 d9452
    omega
  have d9464 : (x 13 11).toNat = 1 := by
    have r9465 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9466 := hb (x 9 4)
    have b9467 := hb (x 13 11)
    have b9468 := hb (x 12 1 && x 12 12)
    have b9469 := hb (x 11 2 && x 11 13)
    have b9470 := hb (x 10 3 && x 10 14)
    clear * - r9465 b9466 b9467 b9468 b9469 b9470 d9302 d9318 d9460 d9267
    omega
  have d9471 : (x 13 3).toNat = 1 := by
    have r9472 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
    have b9473 := hb (x 13 3)
    have b9474 := hb (x 13 11)
    clear * - r9472 b9473 b9474 d9464
    omega
  have d9475 : (x 16 12).toNat = 0 := by
    have r9476 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9477 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e9478 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b9479 := hb (x 13 3)
    have b9480 := hb (x 14 2)
    have b9481 := hb (x 15 13)
    have b9482 := hb (x 16 12)
    clear * - r9476 e9477 e9478 b9479 b9480 b9481 b9482 d9471
    omega
  have d9483 : (x 16 1 && x 16 12).toNat = 0 := by
    have r9484 := hand2 (x 16 1) (x 16 12)
    have b9485 := hb (x 16 12)
    have b9486 := hb (x 16 1 && x 16 12)
    clear * - r9484 b9485 b9486 d9475
    omega
  have d9487 : (x 16 2 && x 16 12).toNat = 0 := by
    have r9488 := hand2 (x 16 2) (x 16 12)
    have b9489 := hb (x 16 12)
    have b9490 := hb (x 16 2 && x 16 12)
    clear * - r9488 b9489 b9490 d9475
    omega
  have d9491 : (x 15 13).toNat = 0 := by
    have r9492 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9493 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e9494 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b9495 := hb (x 13 3)
    have b9496 := hb (x 14 2)
    have b9497 := hb (x 15 13)
    have b9498 := hb (x 16 12)
    clear * - r9492 e9493 e9494 b9495 b9496 b9497 b9498 d9475 d9471
    omega
  have d9499 : (x 15 2 && x 15 13).toNat = 0 := by
    have r9500 := hand2 (x 15 2) (x 15 13)
    have b9501 := hb (x 15 13)
    have b9502 := hb (x 15 2 && x 15 13)
    clear * - r9500 b9501 b9502 d9491
    omega
  have d9503 : (x 15 3 && x 15 13).toNat = 0 := by
    have r9504 := hand2 (x 15 3) (x 15 13)
    have b9505 := hb (x 15 13)
    have b9506 := hb (x 15 3 && x 15 13)
    clear * - r9504 b9505 b9506 d9491
    omega
  have d9507 : (x 14 1 && x 14 14).toNat = 1 := by
    have r9508 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9509 := hb (x 13 2)
    have b9510 := hb (x 15 13)
    have b9511 := hb (x 14 1 && x 14 14)
    clear * - r9508 b9509 b9510 b9511 d9491 d9251
    omega
  have d9512 : (x 14 1).toNat = 1 := by
    have r9513 := hand1 (x 14 1) (x 14 14)
    have b9514 := hb (x 14 1)
    have b9515 := hb (x 14 1 && x 14 14)
    clear * - r9513 b9514 b9515 d9507
    omega
  have d9516 : (x 15 14).toNat = 0 := by
    have r9517 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9518 := hb (x 14 1)
    have b9519 := hb (x 15 14)
    clear * - r9517 b9518 b9519 d9512
    omega
  have d9520 : (x 15 1 && x 15 14).toNat = 0 := by
    have r9521 := hand2 (x 15 1) (x 15 14)
    have b9522 := hb (x 15 14)
    have b9523 := hb (x 15 1 && x 15 14)
    clear * - r9521 b9522 b9523 d9516
    omega
  have d9524 : (x 15 2).toNat = 0 := by
    have r9525 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
    have b9526 := hb (x 15 2)
    have b9527 := hb (x 15 14)
    clear * - r9525 b9526 b9527 d9516
    omega
  have d9528 : (x 14 2).toNat = 0 := by
    have r9529 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9530 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e9531 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b9532 := hb (x 13 3)
    have b9533 := hb (x 14 2)
    have b9534 := hb (x 15 13)
    have b9535 := hb (x 16 12)
    clear * - r9529 e9530 e9531 b9532 b9533 b9534 b9535 d9475 d9491 d9471
    omega
  have d9536 : (x 16 13).toNat = 1 := by
    have r9537 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9538 := hb (x 14 2)
    have b9539 := hb (x 16 13)
    have b9540 := hb (x 15 1 && x 15 14)
    clear * - r9537 b9538 b9539 b9540 d9520 d9528
    omega
  have d9541 : (x 17 12).toNat = 0 := by
    have r9542 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9543 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
    have e9544 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
    have b9545 := hb (x 14 3)
    have b9546 := hb (x 15 2)
    have b9547 := hb (x 16 13)
    have b9548 := hb (x 17 12)
    clear * - r9542 e9543 e9544 b9545 b9546 b9547 b9548 d9536 d9524
    omega
  have d9549 : (x 14 3).toNat = 0 := by
    have r9550 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9551 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
    have e9552 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
    have b9553 := hb (x 14 3)
    have b9554 := hb (x 15 2)
    have b9555 := hb (x 16 13)
    have b9556 := hb (x 17 12)
    clear * - r9550 e9551 e9552 b9553 b9554 b9555 b9556 d9541 d9536 d9524
    omega
  have d9557 : (x 14 3 && x 14 14).toNat = 0 := by
    have r9558 := hand1 (x 14 3) (x 14 14)
    have b9559 := hb (x 14 3)
    have b9560 := hb (x 14 3 && x 14 14)
    clear * - r9558 b9559 b9560 d9549
    omega
  have d9561 : (x 17 11).toNat = 1 := by
    have r9562 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9563 := hb (x 13 4)
    have b9564 := hb (x 17 11)
    have b9565 := hb (x 16 1 && x 16 12)
    have b9566 := hb (x 15 2 && x 15 13)
    have b9567 := hb (x 14 3 && x 14 14)
    clear * - r9562 b9563 b9564 b9565 b9566 b9567 d9483 d9499 d9557 d9448
    omega
  have d9568 : (x 17 3).toNat = 1 := by
    have r9569 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
    have b9570 := hb (x 17 3)
    have b9571 := hb (x 17 11)
    clear * - r9569 b9570 b9571 d9561
    omega
  have d9572 : (x 20 12).toNat = 0 := by
    have r9573 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9574 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
    have e9575 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
    have b9576 := hb (x 17 3)
    have b9577 := hb (x 18 2)
    have b9578 := hb (x 19 13)
    have b9579 := hb (x 20 12)
    clear * - r9573 e9574 e9575 b9576 b9577 b9578 b9579 d9568
    omega
  have d9580 : (x 19 13).toNat = 0 := by
    have r9581 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9582 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
    have e9583 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
    have b9584 := hb (x 17 3)
    have b9585 := hb (x 18 2)
    have b9586 := hb (x 19 13)
    have b9587 := hb (x 20 12)
    clear * - r9581 e9582 e9583 b9584 b9585 b9586 b9587 d9572 d9568
    omega
  have d9588 : (x 18 1 && x 18 14).toNat = 1 := by
    have r9589 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9590 := hb (x 17 2)
    have b9591 := hb (x 19 13)
    have b9592 := hb (x 18 1 && x 18 14)
    clear * - r9589 b9590 b9591 b9592 d9580 d9432
    omega
  have d9593 : (x 18 14).toNat = 1 := by
    have r9594 := hand2 (x 18 1) (x 18 14)
    have b9595 := hb (x 18 14)
    have b9596 := hb (x 18 1 && x 18 14)
    clear * - r9594 b9595 b9596 d9588
    omega
  have d9597 : (x 17 1).toNat = 0 := by
    have r9598 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9599 := hb (x 17 1)
    have b9600 := hb (x 18 14)
    clear * - r9598 b9599 b9600 d9593
    omega
  have d9601 : (x 17 1 && x 17 11).toNat = 0 := by
    have r9602 := hand1 (x 17 1) (x 17 11)
    have b9603 := hb (x 17 1)
    have b9604 := hb (x 17 1 && x 17 11)
    clear * - r9602 b9603 b9604 d9597
    omega
  have d9605 : (x 18 2).toNat = 0 := by
    have r9606 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9607 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
    have e9608 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
    have b9609 := hb (x 17 3)
    have b9610 := hb (x 18 2)
    have b9611 := hb (x 19 13)
    have b9612 := hb (x 20 12)
    clear * - r9606 e9607 e9608 b9609 b9610 b9611 b9612 d9572 d9580 d9568
    omega
  have d9613 : (x 18 10).toNat = 0 := by
    have r9614 : (x 18 10).toNat ≤ (x 18 2).toNat := himp _ _ (hp10 18)
    have b9615 := hb (x 18 2)
    have b9616 := hb (x 18 10)
    clear * - r9614 b9615 b9616 d9605
    omega
  have r9617 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := by have q := hcov10 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have b9618 := hb (x 13 5)
  have b9619 := hb (x 18 10)
  have b9620 := hb (x 17 1 && x 17 11)
  have b9621 := hb (x 16 2 && x 16 12)
  have b9622 := hb (x 15 3 && x 15 13)
  have b9623 := hb (x 14 4 && x 14 14)
  linarith only [r9617, b9618, b9619, b9620, b9621, b9622, b9623, d9613, d9601, d9487, d9503, d9385, d9397]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b0011000001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-2) 11).toNat = 0)
    (g1 : (x (-1) 10).toNat = 0)
    (g2 : (x 0 9).toNat = 0)
    (g3 : (x 1 8).toNat = 1)
    (g4 : (x 1 9).toNat = 0)
    (g5 : (x 0 1 && x 0 10).toNat = 0)
    (g6 : (x (-1) 2 && x (-1) 11).toNat = 0)
    (g7 : (x (-2) 3 && x (-2) 12).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d9625 : (x (-3) 4).toNat = 0 := by
    have r9626 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9627 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e9628 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e9629 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e9630 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e9631 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e9632 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b9633 := hb (x (-6) 7)
    have b9634 := hb (x (-5) 6)
    have b9635 := hb (x (-4) 5)
    have b9636 := hb (x (-3) 4)
    have b9637 := hb (x (-2) 11)
    have b9638 := hb (x (-1) 10)
    have b9639 := hb (x 0 9)
    have b9640 := hb (x 1 8)
    clear * - r9626 e9627 e9628 e9629 e9630 e9631 e9632 b9633 b9634 b9635 b9636 b9637 b9638 b9639 b9640 g3 g2 g1 g0
    omega
  have d9641 : (x (-3) 4 && x (-3) 13).toNat = 0 := by
    have r9642 := hand1 (x (-3) 4) (x (-3) 13)
    have b9643 := hb (x (-3) 4)
    have b9644 := hb (x (-3) 4 && x (-3) 13)
    clear * - r9642 b9643 b9644 d9625
    omega
  have d9645 : (x (-4) 5).toNat = 0 := by
    have r9646 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9647 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e9648 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e9649 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e9650 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e9651 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e9652 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b9653 := hb (x (-6) 7)
    have b9654 := hb (x (-5) 6)
    have b9655 := hb (x (-4) 5)
    have b9656 := hb (x (-3) 4)
    have b9657 := hb (x (-2) 11)
    have b9658 := hb (x (-1) 10)
    have b9659 := hb (x 0 9)
    have b9660 := hb (x 1 8)
    clear * - r9646 e9647 e9648 e9649 e9650 e9651 e9652 b9653 b9654 b9655 b9656 b9657 b9658 b9659 b9660 g3 g2 g1 g0 d9625
    omega
  have d9661 : (x (-4) 5 && x (-4) 14).toNat = 0 := by
    have r9662 := hand1 (x (-4) 5) (x (-4) 14)
    have b9663 := hb (x (-4) 5)
    have b9664 := hb (x (-4) 5 && x (-4) 14)
    clear * - r9662 b9663 b9664 d9645
    omega
  have d9665 : (x (-5) 6).toNat = 1 := by
    have r9666 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9667 := hb (x (-5) 6)
    have b9668 := hb (x 1 9)
    have b9669 := hb (x 0 1 && x 0 10)
    have b9670 := hb (x (-1) 2 && x (-1) 11)
    have b9671 := hb (x (-2) 3 && x (-2) 12)
    have b9672 := hb (x (-3) 4 && x (-3) 13)
    have b9673 := hb (x (-4) 5 && x (-4) 14)
    clear * - r9666 b9667 b9668 b9669 b9670 b9671 b9672 b9673 g4 g5 g6 g7 d9641 d9661
    omega
  have r9674 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e9675 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
  have e9676 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
  have e9677 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
  have e9678 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
  have e9679 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
  have e9680 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
  have b9681 := hb (x (-6) 7)
  have b9682 := hb (x (-5) 6)
  have b9683 := hb (x (-4) 5)
  have b9684 := hb (x (-3) 4)
  have b9685 := hb (x (-2) 11)
  have b9686 := hb (x (-1) 10)
  have b9687 := hb (x 0 9)
  have b9688 := hb (x 1 8)
  linarith only [r9674, e9675, e9676, e9677, e9678, e9679, e9680, b9681, b9682, b9683, b9684, b9685, b9686, b9687, b9688, g3, g2, g1, g0, d9625, d9645, d9665]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b001100001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-4) 7).toNat = 0)
    (g1 : (x (-3) 6).toNat = 0)
    (g2 : (x (-3) 11).toNat = 0)
    (g3 : (x (-2) 5).toNat = 0)
    (g4 : (x (-2) 10).toNat = 0)
    (g5 : (x (-1) 4).toNat = 0)
    (g6 : (x (-1) 8).toNat = 1)
    (g7 : (x (-1) 9).toNat = 0)
    (g8 : (x (-1) 10).toNat = 0)
    (g9 : (x 0 3).toNat = 1)
    (g10 : (x 0 7).toNat = 0)
    (g11 : (x 0 8).toNat = 0)
    (g12 : (x 0 9).toNat = 0)
    (g13 : (x 0 10).toNat = 0)
    (g14 : (x 1 2).toNat = 0)
    (g15 : (x 2 1).toNat = 1)
    (g16 : (x 3 2).toNat = 0)
    (g17 : (x 3 6).toNat = 0)
    (g18 : (x 5 6).toNat = 0)
    (g19 : (x 6 5).toNat = 0)
    (g20 : (x 7 4).toNat = 0)
    (g21 : (x 1 2 && x 1 8).toNat = 0)
    (g22 : (x 0 3 && x 0 9).toNat = 0)
    (g23 : (x (-1) 4 && x (-1) 10).toNat = 0)
    (g24 : (x (-2) 5 && x (-2) 11).toNat = 0)
    (g25 : (x (-3) 6 && x (-3) 12).toNat = 0)
    (g26 : (x (-4) 7 && x (-4) 13).toNat = 0)
    (g27 : (x (-1) 1 && x (-1) 8).toNat = 0)
    (g28 : (x (-2) 2 && x (-2) 9).toNat = 0)
    (g29 : (x (-3) 3 && x (-3) 10).toNat = 0)
    (g30 : (x 3 1 && x 3 8).toNat = 0)
    (g31 : (x 2 2 && x 2 9).toNat = 0)
    (g32 : (x 1 3 && x 1 10).toNat = 0)
    (g33 : (x 0 4 && x 0 11).toNat = 0)
    (g34 : (x (-1) 5 && x (-1) 12).toNat = 0)
    (g35 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g36 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g37 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g38 : (x (-2) 2 && x (-2) 11).toNat = 0)
    (g39 : (x (-3) 3 && x (-3) 12).toNat = 0)
    (g40 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g41 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g42 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g43 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g44 : (x 7 2 && x 7 12).toNat = 0)
    (g45 : (x 6 3 && x 6 13).toNat = 0)
    (g46 : (x 5 4 && x 5 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d9690 : (x (-2) 9).toNat = 0 := by
    have r9691 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9692 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
    have e9693 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
    have e9694 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
    have e9695 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
    have e9696 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
    have e9697 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
    have b9698 := hb (x (-8) 7)
    have b9699 := hb (x (-7) 6)
    have b9700 := hb (x (-6) 5)
    have b9701 := hb (x (-5) 4)
    have b9702 := hb (x (-4) 11)
    have b9703 := hb (x (-3) 10)
    have b9704 := hb (x (-2) 9)
    have b9705 := hb (x (-1) 8)
    clear * - r9691 e9692 e9693 e9694 e9695 e9696 e9697 b9698 b9699 b9700 b9701 b9702 b9703 b9704 b9705 g6
    omega
  have d9706 : (x (-3) 10).toNat = 0 := by
    have r9707 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9708 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
    have e9709 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
    have e9710 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
    have e9711 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
    have e9712 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
    have e9713 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
    have b9714 := hb (x (-8) 7)
    have b9715 := hb (x (-7) 6)
    have b9716 := hb (x (-6) 5)
    have b9717 := hb (x (-5) 4)
    have b9718 := hb (x (-4) 11)
    have b9719 := hb (x (-3) 10)
    have b9720 := hb (x (-2) 9)
    have b9721 := hb (x (-1) 8)
    clear * - r9707 e9708 e9709 e9710 e9711 e9712 e9713 b9714 b9715 b9716 b9717 b9718 b9719 b9720 b9721 g6 d9690
    omega
  have d9722 : (x (-4) 11).toNat = 0 := by
    have r9723 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9724 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
    have e9725 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
    have e9726 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
    have e9727 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
    have e9728 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
    have e9729 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
    have b9730 := hb (x (-8) 7)
    have b9731 := hb (x (-7) 6)
    have b9732 := hb (x (-6) 5)
    have b9733 := hb (x (-5) 4)
    have b9734 := hb (x (-4) 11)
    have b9735 := hb (x (-3) 10)
    have b9736 := hb (x (-2) 9)
    have b9737 := hb (x (-1) 8)
    clear * - r9723 e9724 e9725 e9726 e9727 e9728 e9729 b9730 b9731 b9732 b9733 b9734 b9735 b9736 b9737 g6 d9690 d9706
    omega
  have d9738 : (x (-4) 4 && x (-4) 11).toNat = 0 := by
    have r9739 := hand2 (x (-4) 4) (x (-4) 11)
    have b9740 := hb (x (-4) 11)
    have b9741 := hb (x (-4) 4 && x (-4) 11)
    clear * - r9739 b9740 b9741 d9722
    omega
  have d9742 : (x (-5) 4).toNat = 0 := by
    have r9743 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9744 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
    have e9745 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
    have e9746 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
    have e9747 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
    have e9748 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
    have e9749 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
    have b9750 := hb (x (-8) 7)
    have b9751 := hb (x (-7) 6)
    have b9752 := hb (x (-6) 5)
    have b9753 := hb (x (-5) 4)
    have b9754 := hb (x (-4) 11)
    have b9755 := hb (x (-3) 10)
    have b9756 := hb (x (-2) 9)
    have b9757 := hb (x (-1) 8)
    clear * - r9743 e9744 e9745 e9746 e9747 e9748 e9749 b9750 b9751 b9752 b9753 b9754 b9755 b9756 b9757 g6 d9690 d9706 d9722
    omega
  have d9758 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
    have r9759 := hand1 (x (-5) 4) (x (-5) 14)
    have b9760 := hb (x (-5) 4)
    have b9761 := hb (x (-5) 4 && x (-5) 14)
    clear * - r9759 b9760 b9761 d9742
    omega
  have d9762 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
    have r9763 := hand1 (x (-5) 4) (x (-5) 13)
    have b9764 := hb (x (-5) 4)
    have b9765 := hb (x (-5) 4 && x (-5) 13)
    clear * - r9763 b9764 b9765 d9742
    omega
  have d9766 : (x (-6) 5).toNat = 0 := by
    have r9767 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9768 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
    have e9769 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
    have e9770 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
    have e9771 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
    have e9772 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
    have e9773 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
    have b9774 := hb (x (-8) 7)
    have b9775 := hb (x (-7) 6)
    have b9776 := hb (x (-6) 5)
    have b9777 := hb (x (-5) 4)
    have b9778 := hb (x (-4) 11)
    have b9779 := hb (x (-3) 10)
    have b9780 := hb (x (-2) 9)
    have b9781 := hb (x (-1) 8)
    clear * - r9767 e9768 e9769 e9770 e9771 e9772 e9773 b9774 b9775 b9776 b9777 b9778 b9779 b9780 b9781 g6 d9690 d9706 d9722 d9742
    omega
  have d9782 : (x (-6) 5 && x (-6) 14).toNat = 0 := by
    have r9783 := hand1 (x (-6) 5) (x (-6) 14)
    have b9784 := hb (x (-6) 5)
    have b9785 := hb (x (-6) 5 && x (-6) 14)
    clear * - r9783 b9784 b9785 d9766
    omega
  have d9786 : (x (-7) 6).toNat = 0 := by
    have r9787 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9788 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
    have e9789 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
    have e9790 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
    have e9791 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
    have e9792 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
    have e9793 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
    have b9794 := hb (x (-8) 7)
    have b9795 := hb (x (-7) 6)
    have b9796 := hb (x (-6) 5)
    have b9797 := hb (x (-5) 4)
    have b9798 := hb (x (-4) 11)
    have b9799 := hb (x (-3) 10)
    have b9800 := hb (x (-2) 9)
    have b9801 := hb (x (-1) 8)
    clear * - r9787 e9788 e9789 e9790 e9791 e9792 e9793 b9794 b9795 b9796 b9797 b9798 b9799 b9800 b9801 g6 d9690 d9706 d9722 d9742 d9766
    omega
  have d9802 : (x (-4) 3 && x (-4) 12).toNat = 1 := by
    have r9803 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9804 := hb (x (-7) 6)
    have b9805 := hb (x (-1) 9)
    have b9806 := hb (x (-2) 1 && x (-2) 10)
    have b9807 := hb (x (-3) 2 && x (-3) 11)
    have b9808 := hb (x (-4) 3 && x (-4) 12)
    have b9809 := hb (x (-5) 4 && x (-5) 13)
    have b9810 := hb (x (-6) 5 && x (-6) 14)
    clear * - r9803 b9804 b9805 b9806 b9807 b9808 b9809 b9810 g7 g35 g36 d9762 d9782 d9786
    omega
  have d9811 : (x (-4) 12).toNat = 1 := by
    have r9812 := hand2 (x (-4) 3) (x (-4) 12)
    have b9813 := hb (x (-4) 12)
    have b9814 := hb (x (-4) 3 && x (-4) 12)
    clear * - r9812 b9813 b9814 d9802
    omega
  have d9815 : (x (-5) 13).toNat = 0 := by
    have r9816 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9817 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e9818 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b9819 := hb (x (-7) 3)
    have b9820 := hb (x (-6) 2)
    have b9821 := hb (x (-5) 13)
    have b9822 := hb (x (-4) 12)
    clear * - r9816 e9817 e9818 b9819 b9820 b9821 b9822 d9811
    omega
  have d9823 : (x (-5) 5).toNat = 0 := by
    have r9824 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
    have b9825 := hb (x (-5) 5)
    have b9826 := hb (x (-5) 13)
    clear * - r9824 b9825 b9826 d9815
    omega
  have d9827 : (x (-5) 5 && x (-5) 14).toNat = 0 := by
    have r9828 := hand1 (x (-5) 5) (x (-5) 14)
    have b9829 := hb (x (-5) 5)
    have b9830 := hb (x (-5) 5 && x (-5) 14)
    clear * - r9828 b9829 b9830 d9823
    omega
  have d9831 : (x (-5) 5 && x (-5) 12).toNat = 0 := by
    have r9832 := hand1 (x (-5) 5) (x (-5) 12)
    have b9833 := hb (x (-5) 5)
    have b9834 := hb (x (-5) 5 && x (-5) 12)
    clear * - r9832 b9833 b9834 d9823
    omega
  have d9835 : (x (-4) 4 && x (-4) 14).toNat = 1 := by
    have r9836 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9837 := hb (x (-5) 5)
    have b9838 := hb (x 0 10)
    have b9839 := hb (x (-1) 1 && x (-1) 11)
    have b9840 := hb (x (-2) 2 && x (-2) 12)
    have b9841 := hb (x (-3) 3 && x (-3) 13)
    have b9842 := hb (x (-4) 4 && x (-4) 14)
    clear * - r9836 b9837 b9838 b9839 b9840 b9841 b9842 g13 g41 g42 g43 d9823
    omega
  have d9843 : (x (-4) 14).toNat = 1 := by
    have r9844 := hand2 (x (-4) 4) (x (-4) 14)
    have b9845 := hb (x (-4) 14)
    have b9846 := hb (x (-4) 4 && x (-4) 14)
    clear * - r9844 b9845 b9846 d9835
    omega
  have d9847 : (x (-5) 1).toNat = 0 := by
    have r9848 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9849 := hb (x (-5) 1)
    have b9850 := hb (x (-4) 14)
    clear * - r9848 b9849 b9850 d9843
    omega
  have d9851 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
    have r9852 := hand1 (x (-5) 1) (x (-5) 12)
    have b9853 := hb (x (-5) 1)
    have b9854 := hb (x (-5) 1 && x (-5) 12)
    clear * - r9852 b9853 b9854 d9847
    omega
  have d9855 : (x (-5) 9).toNat = 0 := by
    have r9856 : (x (-5) 9).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp9 (-5))
    have b9857 := hb (x (-5) 1)
    have b9858 := hb (x (-5) 9)
    clear * - r9856 b9857 b9858 d9847
    omega
  have d9859 : (x (-4) 4).toNat = 1 := by
    have r9860 := hand1 (x (-4) 4) (x (-4) 14)
    have b9861 := hb (x (-4) 4)
    have b9862 := hb (x (-4) 4 && x (-4) 14)
    clear * - r9860 b9861 b9862 d9835
    omega
  have d9863 : (x (-6) 6).toNat = 0 := by
    have r9864 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9865 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e9866 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e9867 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e9868 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e9869 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e9870 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b9871 := hb (x (-7) 7)
    have b9872 := hb (x (-6) 6)
    have b9873 := hb (x (-5) 5)
    have b9874 := hb (x (-4) 4)
    have b9875 := hb (x (-3) 11)
    have b9876 := hb (x (-2) 10)
    have b9877 := hb (x (-1) 9)
    have b9878 := hb (x 0 8)
    clear * - r9864 e9865 e9866 e9867 e9868 e9869 e9870 b9871 b9872 b9873 b9874 b9875 b9876 b9877 b9878 g11 g7 g4 g2 d9859 d9823
    omega
  have d9879 : (x (-6) 6 && x (-6) 13).toNat = 0 := by
    have r9880 := hand1 (x (-6) 6) (x (-6) 13)
    have b9881 := hb (x (-6) 6)
    have b9882 := hb (x (-6) 6 && x (-6) 13)
    clear * - r9880 b9881 b9882 d9863
    omega
  have d9883 : (x (-4) 4 && x (-4) 13).toNat = 1 := by
    have r9884 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9885 := hb (x (-6) 6)
    have b9886 := hb (x 0 9)
    have b9887 := hb (x (-1) 1 && x (-1) 10)
    have b9888 := hb (x (-2) 2 && x (-2) 11)
    have b9889 := hb (x (-3) 3 && x (-3) 12)
    have b9890 := hb (x (-4) 4 && x (-4) 13)
    have b9891 := hb (x (-5) 5 && x (-5) 14)
    clear * - r9884 b9885 b9886 b9887 b9888 b9889 b9890 b9891 g12 g37 g38 g39 d9827 d9863
    omega
  have d9892 : (x (-4) 13).toNat = 1 := by
    have r9893 := hand2 (x (-4) 4) (x (-4) 13)
    have b9894 := hb (x (-4) 13)
    have b9895 := hb (x (-4) 4 && x (-4) 13)
    clear * - r9893 b9894 b9895 d9883
    omega
  have d9896 : (x (-4) 1).toNat = 1 := by
    have r9897 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
    have b9898 := hb (x (-4) 1)
    have b9899 := hb (x (-4) 13)
    clear * - r9897 b9898 b9899 d9892
    omega
  have d9900 : (x (-3) 14).toNat = 0 := by
    have r9901 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9902 := hb (x (-4) 1)
    have b9903 := hb (x (-3) 14)
    clear * - r9901 b9902 b9903 d9896
    omega
  have d9904 : (x (-3) 7 && x (-3) 14).toNat = 0 := by
    have r9905 := hand2 (x (-3) 7) (x (-3) 14)
    have b9906 := hb (x (-3) 14)
    have b9907 := hb (x (-3) 7 && x (-3) 14)
    clear * - r9905 b9906 b9907 d9900
    omega
  have d9908 : (x (-3) 2).toNat = 0 := by
    have r9909 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
    have b9910 := hb (x (-3) 2)
    have b9911 := hb (x (-3) 14)
    clear * - r9909 b9910 b9911 d9900
    omega
  have d9912 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
    have r9913 := hand1 (x (-3) 2) (x (-3) 12)
    have b9914 := hb (x (-3) 2)
    have b9915 := hb (x (-3) 2 && x (-3) 12)
    clear * - r9913 b9914 b9915 d9908
    omega
  have d9916 : (x (-4) 3 && x (-4) 13).toNat = 1 := by
    have r9917 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9918 := hb (x (-6) 5)
    have b9919 := hb (x (-1) 10)
    have b9920 := hb (x (-2) 1 && x (-2) 11)
    have b9921 := hb (x (-3) 2 && x (-3) 12)
    have b9922 := hb (x (-4) 3 && x (-4) 13)
    have b9923 := hb (x (-5) 4 && x (-5) 14)
    clear * - r9917 b9918 b9919 b9920 b9921 b9922 b9923 g8 g40 d9912 d9758 d9766
    omega
  have d9924 : (x (-4) 3).toNat = 1 := by
    have r9925 := hand1 (x (-4) 3) (x (-4) 13)
    have b9926 := hb (x (-4) 3)
    have b9927 := hb (x (-4) 3 && x (-4) 13)
    clear * - r9925 b9926 b9927 d9916
    omega
  have d9928 : (x (-1) 12).toNat = 0 := by
    have r9929 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9930 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e9931 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b9932 := hb (x (-4) 3)
    have b9933 := hb (x (-3) 2)
    have b9934 := hb (x (-2) 13)
    have b9935 := hb (x (-1) 12)
    clear * - r9929 e9930 e9931 b9932 b9933 b9934 b9935 d9908 d9924
    omega
  have d9936 : (x (-2) 13).toNat = 0 := by
    have r9937 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9938 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e9939 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b9940 := hb (x (-4) 3)
    have b9941 := hb (x (-3) 2)
    have b9942 := hb (x (-2) 13)
    have b9943 := hb (x (-1) 12)
    clear * - r9937 e9938 e9939 b9940 b9941 b9942 b9943 d9928 d9908 d9924
    omega
  have d9944 : (x (-2) 6 && x (-2) 13).toNat = 0 := by
    have r9945 := hand2 (x (-2) 6) (x (-2) 13)
    have b9946 := hb (x (-2) 13)
    have b9947 := hb (x (-2) 6 && x (-2) 13)
    clear * - r9945 b9946 b9947 d9936
    omega
  have d9948 : (x (-7) 7).toNat = 0 := by
    have r9949 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9950 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e9951 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e9952 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e9953 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e9954 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e9955 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b9956 := hb (x (-7) 7)
    have b9957 := hb (x (-6) 6)
    have b9958 := hb (x (-5) 5)
    have b9959 := hb (x (-4) 4)
    have b9960 := hb (x (-3) 11)
    have b9961 := hb (x (-2) 10)
    have b9962 := hb (x (-1) 9)
    have b9963 := hb (x 0 8)
    clear * - r9949 e9950 e9951 e9952 e9953 e9954 e9955 b9956 b9957 b9958 b9959 b9960 b9961 b9962 b9963 g11 g7 g4 g2 d9859 d9823 d9863
    omega
  have d9964 : (x (-7) 7 && x (-7) 14).toNat = 0 := by
    have r9965 := hand1 (x (-7) 7) (x (-7) 14)
    have b9966 := hb (x (-7) 7)
    have b9967 := hb (x (-7) 7 && x (-7) 14)
    clear * - r9965 b9966 b9967 d9948
    omega
  have d9968 : (x (-6) 2).toNat = 0 := by
    have r9969 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9970 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e9971 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b9972 := hb (x (-7) 3)
    have b9973 := hb (x (-6) 2)
    have b9974 := hb (x (-5) 13)
    have b9975 := hb (x (-4) 12)
    clear * - r9969 e9970 e9971 b9972 b9973 b9974 b9975 d9811 d9815
    omega
  have d9976 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
    have r9977 := hand1 (x (-6) 2) (x (-6) 13)
    have b9978 := hb (x (-6) 2)
    have b9979 := hb (x (-6) 2 && x (-6) 13)
    clear * - r9977 b9978 b9979 d9968
    omega
  have d9980 : (x (-6) 10).toNat = 0 := by
    have r9981 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
    have b9982 := hb (x (-6) 2)
    have b9983 := hb (x (-6) 10)
    clear * - r9981 b9982 b9983 d9968
    omega
  have d9984 : (x (-7) 3).toNat = 0 := by
    have r9985 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9986 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e9987 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b9988 := hb (x (-7) 3)
    have b9989 := hb (x (-6) 2)
    have b9990 := hb (x (-5) 13)
    have b9991 := hb (x (-4) 12)
    clear * - r9985 e9986 e9987 b9988 b9989 b9990 b9991 d9811 d9815 d9968
    omega
  have d9992 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
    have r9993 := hand1 (x (-7) 3) (x (-7) 14)
    have b9994 := hb (x (-7) 3)
    have b9995 := hb (x (-7) 3 && x (-7) 14)
    clear * - r9993 b9994 b9995 d9984
    omega
  have d9996 : (x (-8) 4).toNat = 1 := by
    have r9997 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9998 := hb (x (-8) 4)
    have b9999 := hb (x (-4) 11)
    have b10000 := hb (x (-5) 1 && x (-5) 12)
    have b10001 := hb (x (-6) 2 && x (-6) 13)
    have b10002 := hb (x (-7) 3 && x (-7) 14)
    clear * - r9997 b9998 b9999 b10000 b10001 b10002 d9722 d9851 d9976 d9992
    omega
  have d10003 : (x (-8) 12).toNat = 1 := by
    have r10004 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
    have b10005 := hb (x (-8) 4)
    have b10006 := hb (x (-8) 12)
    clear * - r10004 b10005 b10006 d9996
    omega
  have d10007 : (x (-9) 13).toNat = 0 := by
    have r10008 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10009 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
    have e10010 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
    have b10011 := hb (x (-11) 3)
    have b10012 := hb (x (-10) 2)
    have b10013 := hb (x (-9) 13)
    have b10014 := hb (x (-8) 12)
    clear * - r10008 e10009 e10010 b10011 b10012 b10013 b10014 d10003
    omega
  have d10015 : (x (-9) 5).toNat = 0 := by
    have r10016 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
    have b10017 := hb (x (-9) 5)
    have b10018 := hb (x (-9) 13)
    clear * - r10016 b10017 b10018 d10007
    omega
  have d10019 : (x (-10) 2).toNat = 0 := by
    have r10020 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10021 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
    have e10022 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
    have b10023 := hb (x (-11) 3)
    have b10024 := hb (x (-10) 2)
    have b10025 := hb (x (-9) 13)
    have b10026 := hb (x (-8) 12)
    clear * - r10020 e10021 e10022 b10023 b10024 b10025 b10026 d10003 d10007
    omega
  have d10027 : (x (-10) 2 && x (-10) 13).toNat = 0 := by
    have r10028 := hand1 (x (-10) 2) (x (-10) 13)
    have b10029 := hb (x (-10) 2)
    have b10030 := hb (x (-10) 2 && x (-10) 13)
    clear * - r10028 b10029 b10030 d10019
    omega
  have d10031 : (x (-10) 10).toNat = 0 := by
    have r10032 : (x (-10) 10).toNat ≤ (x (-10) 2).toNat := himp _ _ (hp10 (-10))
    have b10033 := hb (x (-10) 2)
    have b10034 := hb (x (-10) 10)
    clear * - r10032 b10033 b10034 d10019
    omega
  have d10035 : (x (-11) 3).toNat = 0 := by
    have r10036 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10037 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
    have e10038 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
    have b10039 := hb (x (-11) 3)
    have b10040 := hb (x (-10) 2)
    have b10041 := hb (x (-9) 13)
    have b10042 := hb (x (-8) 12)
    clear * - r10036 e10037 e10038 b10039 b10040 b10041 b10042 d10003 d10007 d10019
    omega
  have d10043 : (x (-11) 3 && x (-11) 14).toNat = 0 := by
    have r10044 := hand1 (x (-11) 3) (x (-11) 14)
    have b10045 := hb (x (-11) 3)
    have b10046 := hb (x (-11) 3 && x (-11) 14)
    clear * - r10044 b10045 b10046 d10035
    omega
  have d10047 : (x (-11) 11).toNat = 0 := by
    have r10048 : (x (-11) 11).toNat ≤ (x (-11) 3).toNat := himp _ _ (hp11 (-11))
    have b10049 := hb (x (-11) 3)
    have b10050 := hb (x (-11) 11)
    clear * - r10048 b10049 b10050 d10035
    omega
  have d10051 : (x (-7) 11).toNat = 0 := by
    have r10052 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
    have b10053 := hb (x (-7) 3)
    have b10054 := hb (x (-7) 11)
    clear * - r10052 b10053 b10054 d9984
    omega
  have d10055 : (x (-4) 8).toNat = 0 := by
    have r10056 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10057 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
    have e10058 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
    have e10059 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
    have e10060 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
    have e10061 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
    have e10062 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
    have b10063 := hb (x (-11) 7)
    have b10064 := hb (x (-10) 6)
    have b10065 := hb (x (-9) 5)
    have b10066 := hb (x (-8) 4)
    have b10067 := hb (x (-7) 11)
    have b10068 := hb (x (-6) 10)
    have b10069 := hb (x (-5) 9)
    have b10070 := hb (x (-4) 8)
    clear * - r10056 e10057 e10058 e10059 e10060 e10061 e10062 b10063 b10064 b10065 b10066 b10067 b10068 b10069 b10070 d9855 d9980 d10051 d9996 d10015
    omega
  have d10071 : (x 4 7).toNat = 1 := by
    have r10072 : 1 ≤ (x 4 7).toNat + (x 3 1 && x 3 8).toNat + (x 2 2 && x 2 9).toNat + (x 1 3 && x 1 10).toNat + (x 0 4 && x 0 11).toNat + (x (-1) 5 && x (-1) 12).toNat + (x (-2) 6 && x (-2) 13).toNat + (x (-3) 7 && x (-3) 14).toNat + (x (-4) 8).toNat := by have q := hcov7 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b10073 := hb (x (-4) 8)
    have b10074 := hb (x 4 7)
    have b10075 := hb (x 3 1 && x 3 8)
    have b10076 := hb (x 2 2 && x 2 9)
    have b10077 := hb (x 1 3 && x 1 10)
    have b10078 := hb (x 0 4 && x 0 11)
    have b10079 := hb (x (-1) 5 && x (-1) 12)
    have b10080 := hb (x (-2) 6 && x (-2) 13)
    have b10081 := hb (x (-3) 7 && x (-3) 14)
    clear * - r10072 b10073 b10074 b10075 b10076 b10077 b10078 b10079 b10080 b10081 g30 g31 g32 g33 g34 d9944 d9904 d10055
    omega
  have d10082 : (x 11 8).toNat = 0 := by
    have r10083 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10084 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e10085 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e10086 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e10087 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e10088 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e10089 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have b10090 := hb (x 4 7)
    have b10091 := hb (x 5 6)
    have b10092 := hb (x 6 5)
    have b10093 := hb (x 7 4)
    have b10094 := hb (x 8 11)
    have b10095 := hb (x 9 10)
    have b10096 := hb (x 10 9)
    have b10097 := hb (x 11 8)
    clear * - r10083 e10084 e10085 e10086 e10087 e10088 e10089 b10090 b10091 b10092 b10093 b10094 b10095 b10096 b10097 g20 g19 g18 d10071
    omega
  have d10098 : (x 10 9).toNat = 0 := by
    have r10099 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10100 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e10101 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e10102 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e10103 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e10104 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e10105 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have b10106 := hb (x 4 7)
    have b10107 := hb (x 5 6)
    have b10108 := hb (x 6 5)
    have b10109 := hb (x 7 4)
    have b10110 := hb (x 8 11)
    have b10111 := hb (x 9 10)
    have b10112 := hb (x 10 9)
    have b10113 := hb (x 11 8)
    clear * - r10099 e10100 e10101 e10102 e10103 e10104 e10105 b10106 b10107 b10108 b10109 b10110 b10111 b10112 b10113 d10082 g20 g19 g18 d10071
    omega
  have d10114 : (x 9 10).toNat = 0 := by
    have r10115 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10116 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e10117 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e10118 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e10119 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e10120 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e10121 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have b10122 := hb (x 4 7)
    have b10123 := hb (x 5 6)
    have b10124 := hb (x 6 5)
    have b10125 := hb (x 7 4)
    have b10126 := hb (x 8 11)
    have b10127 := hb (x 9 10)
    have b10128 := hb (x 10 9)
    have b10129 := hb (x 11 8)
    clear * - r10115 e10116 e10117 e10118 e10119 e10120 e10121 b10122 b10123 b10124 b10125 b10126 b10127 b10128 b10129 d10082 d10098 g20 g19 g18 d10071
    omega
  have d10130 : (x 8 11).toNat = 0 := by
    have r10131 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10132 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e10133 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e10134 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e10135 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e10136 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e10137 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have b10138 := hb (x 4 7)
    have b10139 := hb (x 5 6)
    have b10140 := hb (x 6 5)
    have b10141 := hb (x 7 4)
    have b10142 := hb (x 8 11)
    have b10143 := hb (x 9 10)
    have b10144 := hb (x 10 9)
    have b10145 := hb (x 11 8)
    clear * - r10131 e10132 e10133 e10134 e10135 e10136 e10137 b10138 b10139 b10140 b10141 b10142 b10143 b10144 b10145 d10082 d10098 d10114 g20 g19 g18 d10071
    omega
  have d10146 : (x 8 1 && x 8 11).toNat = 0 := by
    have r10147 := hand2 (x 8 1) (x 8 11)
    have b10148 := hb (x 8 11)
    have b10149 := hb (x 8 1 && x 8 11)
    clear * - r10147 b10148 b10149 d10130
    omega
  have d10150 : (x 4 5).toNat = 1 := by
    have r10151 : 1 ≤ (x 9 10).toNat + (x 8 1 && x 8 11).toNat + (x 7 2 && x 7 12).toNat + (x 6 3 && x 6 13).toNat + (x 5 4 && x 5 14).toNat + (x 4 5).toNat := by have q := hcov10 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b10152 := hb (x 4 5)
    have b10153 := hb (x 9 10)
    have b10154 := hb (x 8 1 && x 8 11)
    have b10155 := hb (x 7 2 && x 7 12)
    have b10156 := hb (x 6 3 && x 6 13)
    have b10157 := hb (x 5 4 && x 5 14)
    clear * - r10151 b10152 b10153 b10154 b10155 b10156 b10157 d10114 d10146 g44 g45 g46
    omega
  have d10158 : (x 4 13).toNat = 1 := by
    have r10159 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
    have b10160 := hb (x 4 5)
    have b10161 := hb (x 4 13)
    clear * - r10159 b10160 b10161 d10150
    omega
  have d10162 : (x 5 12).toNat = 0 := by
    have r10163 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10164 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e10165 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b10166 := hb (x 2 3)
    have b10167 := hb (x 3 2)
    have b10168 := hb (x 4 13)
    have b10169 := hb (x 5 12)
    clear * - r10163 e10164 e10165 b10166 b10167 b10168 b10169 d10158 g16
    omega
  have d10170 : (x 5 4).toNat = 0 := by
    have r10171 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
    have b10172 := hb (x 5 4)
    have b10173 := hb (x 5 12)
    clear * - r10171 b10172 b10173 d10162
    omega
  have d10174 : (x 9 8).toNat = 0 := by
    have r10175 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10176 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
    have e10177 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
    have e10178 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
    have e10179 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
    have e10180 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
    have e10181 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
    have b10182 := hb (x 2 7)
    have b10183 := hb (x 3 6)
    have b10184 := hb (x 4 5)
    have b10185 := hb (x 5 4)
    have b10186 := hb (x 6 11)
    have b10187 := hb (x 7 10)
    have b10188 := hb (x 8 9)
    have b10189 := hb (x 9 8)
    clear * - r10175 e10176 e10177 e10178 e10179 e10180 e10181 b10182 b10183 b10184 b10185 b10186 b10187 b10188 b10189 d10170 d10150 g17
    omega
  have d10190 : (x 8 9).toNat = 0 := by
    have r10191 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10192 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
    have e10193 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
    have e10194 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
    have e10195 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
    have e10196 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
    have e10197 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
    have b10198 := hb (x 2 7)
    have b10199 := hb (x 3 6)
    have b10200 := hb (x 4 5)
    have b10201 := hb (x 5 4)
    have b10202 := hb (x 6 11)
    have b10203 := hb (x 7 10)
    have b10204 := hb (x 8 9)
    have b10205 := hb (x 9 8)
    clear * - r10191 e10192 e10193 e10194 e10195 e10196 e10197 b10198 b10199 b10200 b10201 b10202 b10203 b10204 b10205 d10174 d10170 d10150 g17
    omega
  have d10206 : (x 7 10).toNat = 0 := by
    have r10207 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10208 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
    have e10209 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
    have e10210 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
    have e10211 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
    have e10212 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
    have e10213 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
    have b10214 := hb (x 2 7)
    have b10215 := hb (x 3 6)
    have b10216 := hb (x 4 5)
    have b10217 := hb (x 5 4)
    have b10218 := hb (x 6 11)
    have b10219 := hb (x 7 10)
    have b10220 := hb (x 8 9)
    have b10221 := hb (x 9 8)
    clear * - r10207 e10208 e10209 e10210 e10211 e10212 e10213 b10214 b10215 b10216 b10217 b10218 b10219 b10220 b10221 d10174 d10190 d10170 d10150 g17
    omega
  have d10222 : (x 6 11).toNat = 0 := by
    have r10223 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10224 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
    have e10225 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
    have e10226 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
    have e10227 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
    have e10228 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
    have e10229 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
    have b10230 := hb (x 2 7)
    have b10231 := hb (x 3 6)
    have b10232 := hb (x 4 5)
    have b10233 := hb (x 5 4)
    have b10234 := hb (x 6 11)
    have b10235 := hb (x 7 10)
    have b10236 := hb (x 8 9)
    have b10237 := hb (x 9 8)
    clear * - r10223 e10224 e10225 e10226 e10227 e10228 e10229 b10230 b10231 b10232 b10233 b10234 b10235 b10236 b10237 d10174 d10190 d10206 d10170 d10150 g17
    omega
  have d10238 : (x 2 7).toNat = 0 := by
    have r10239 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10240 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
    have e10241 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
    have e10242 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
    have e10243 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
    have e10244 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
    have e10245 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
    have b10246 := hb (x 2 7)
    have b10247 := hb (x 3 6)
    have b10248 := hb (x 4 5)
    have b10249 := hb (x 5 4)
    have b10250 := hb (x 6 11)
    have b10251 := hb (x 7 10)
    have b10252 := hb (x 8 9)
    have b10253 := hb (x 9 8)
    clear * - r10239 e10240 e10241 e10242 e10243 e10244 e10245 b10246 b10247 b10248 b10249 b10250 b10251 b10252 b10253 d10174 d10190 d10206 d10222 d10170 d10150 g17
    omega
  have d10254 : (x 2 1 && x 2 7).toNat = 0 := by
    have r10255 := hand2 (x 2 1) (x 2 7)
    have b10256 := hb (x 2 7)
    have b10257 := hb (x 2 1 && x 2 7)
    clear * - r10255 b10256 b10257 d10238
    omega
  have d10258 : (x (-8) 8).toNat = 1 := by
    have r10259 : 1 ≤ (x 0 7).toNat + (x (-1) 1 && x (-1) 8).toNat + (x (-2) 2 && x (-2) 9).toNat + (x (-3) 3 && x (-3) 10).toNat + (x (-4) 4 && x (-4) 11).toNat + (x (-5) 5 && x (-5) 12).toNat + (x (-6) 6 && x (-6) 13).toNat + (x (-7) 7 && x (-7) 14).toNat + (x (-8) 8).toNat := by have q := hcov7 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b10260 := hb (x (-8) 8)
    have b10261 := hb (x 0 7)
    have b10262 := hb (x (-1) 1 && x (-1) 8)
    have b10263 := hb (x (-2) 2 && x (-2) 9)
    have b10264 := hb (x (-3) 3 && x (-3) 10)
    have b10265 := hb (x (-4) 4 && x (-4) 11)
    have b10266 := hb (x (-5) 5 && x (-5) 12)
    have b10267 := hb (x (-6) 6 && x (-6) 13)
    have b10268 := hb (x (-7) 7 && x (-7) 14)
    clear * - r10259 b10260 b10261 b10262 b10263 b10264 b10265 b10266 b10267 b10268 g10 g27 g28 g29 d9738 d9831 d9879 d9964
    omega
  have d10269 : (x (-9) 9).toNat = 0 := by
    have r10270 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10271 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
    have e10272 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
    have e10273 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
    have e10274 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
    have e10275 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
    have e10276 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
    have b10277 := hb (x (-15) 7)
    have b10278 := hb (x (-14) 6)
    have b10279 := hb (x (-13) 5)
    have b10280 := hb (x (-12) 4)
    have b10281 := hb (x (-11) 11)
    have b10282 := hb (x (-10) 10)
    have b10283 := hb (x (-9) 9)
    have b10284 := hb (x (-8) 8)
    clear * - r10270 e10271 e10272 e10273 e10274 e10275 e10276 b10277 b10278 b10279 b10280 b10281 b10282 b10283 b10284 d10258 d10031 d10047
    omega
  have d10285 : (x (-12) 4).toNat = 0 := by
    have r10286 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10287 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
    have e10288 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
    have e10289 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
    have e10290 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
    have e10291 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
    have e10292 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
    have b10293 := hb (x (-15) 7)
    have b10294 := hb (x (-14) 6)
    have b10295 := hb (x (-13) 5)
    have b10296 := hb (x (-12) 4)
    have b10297 := hb (x (-11) 11)
    have b10298 := hb (x (-10) 10)
    have b10299 := hb (x (-9) 9)
    have b10300 := hb (x (-8) 8)
    clear * - r10286 e10287 e10288 e10289 e10290 e10291 e10292 b10293 b10294 b10295 b10296 b10297 b10298 b10299 b10300 d10258 d10269 d10031 d10047
    omega
  have r10301 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r10302 : 1 ≤ (x 3 6).toNat + (x 2 1 && x 2 7).toNat + (x 1 2 && x 1 8).toNat + (x 0 3 && x 0 9).toNat + (x (-1) 4 && x (-1) 10).toNat + (x (-2) 5 && x (-2) 11).toNat + (x (-3) 6 && x (-3) 12).toNat + (x (-4) 7 && x (-4) 13).toNat + (x (-5) 8 && x (-5) 14).toNat + (x (-6) 9).toNat := by have q := hcov6 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r10303 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := by have q := hcov11 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r10304 := hand1 (x (-5) 8) (x (-5) 14)
  have r10305 := hand2 (x (-9) 1) (x (-9) 12)
  linarith only [r10301, r10302, r10303, r10304, r10305, d10285, g0, g1, g3, g5, g9, g14, g15, g17, d10254, g21, g22, g23, g24, g25, g26, d10027, d10043]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b00110001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-2) 11).toNat = 0)
    (g1 : (x (-1) 10).toNat = 0)
    (g2 : (x 0 9).toNat = 0)
    (g3 : (x 1 6).toNat = 0)
    (g4 : (x 1 7).toNat = 1)
    (g5 : (x 1 9).toNat = 0)
    (g6 : (x 1 10).toNat = 0)
    (g7 : (x 3 2).toNat = 0)
    (g8 : (x 3 5).toNat = 0)
    (g9 : (x 3 6).toNat = 0)
    (g10 : (x 3 13).toNat = 0)
    (g11 : (x 5 6).toNat = 0)
    (g12 : (x 6 5).toNat = 0)
    (g13 : (x 7 4).toNat = 0)
    (g14 : (x 7 4 && x 7 9).toNat = 0)
    (g15 : (x 6 5 && x 6 10).toNat = 0)
    (g16 : (x 5 6 && x 5 11).toNat = 0)
    (g17 : (x 3 8 && x 3 13).toNat = 0)
    (g18 : (x 2 9 && x 2 14).toNat = 0)
    (g19 : (x 3 6 && x 3 13).toNat = 0)
    (g20 : (x 0 1 && x 0 10).toNat = 0)
    (g21 : (x (-1) 2 && x (-1) 11).toNat = 0)
    (g22 : (x (-2) 3 && x (-2) 12).toNat = 0)
    (g23 : (x 5 2 && x 5 11).toNat = 0)
    (g24 : (x 3 4 && x 3 13).toNat = 0)
    (g25 : (x 2 5 && x 2 14).toNat = 0)
    (g26 : (x 3 5 && x 3 14).toNat = 0)
    (g27 : (x 7 1 && x 7 12).toNat = 0)
    (g28 : (x 6 2 && x 6 13).toNat = 0)
    (g29 : (x 5 3 && x 5 14).toNat = 0)
    (g30 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d10334 : (x 8 8).toNat = 0 := by
    have r10335 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10336 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e10337 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e10338 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e10339 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e10340 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e10341 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have b10342 := hb (x 1 7)
    have b10343 := hb (x 2 6)
    have b10344 := hb (x 3 5)
    have b10345 := hb (x 4 4)
    have b10346 := hb (x 5 11)
    have b10347 := hb (x 6 10)
    have b10348 := hb (x 7 9)
    have b10349 := hb (x 8 8)
    clear * - r10335 e10336 e10337 e10338 e10339 e10340 e10341 b10342 b10343 b10344 b10345 b10346 b10347 b10348 b10349 g8 g4
    omega
  have d10350 : (x 8 1 && x 8 8).toNat = 0 := by
    have r10351 := hand2 (x 8 1) (x 8 8)
    have b10352 := hb (x 8 8)
    have b10353 := hb (x 8 1 && x 8 8)
    clear * - r10351 b10352 b10353 d10334
    omega
  have d10354 : (x 8 3 && x 8 8).toNat = 0 := by
    have r10355 := hand2 (x 8 3) (x 8 8)
    have b10356 := hb (x 8 8)
    have b10357 := hb (x 8 3 && x 8 8)
    clear * - r10355 b10356 b10357 d10334
    omega
  have d10358 : (x 7 9).toNat = 0 := by
    have r10359 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10360 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e10361 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e10362 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e10363 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e10364 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e10365 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have b10366 := hb (x 1 7)
    have b10367 := hb (x 2 6)
    have b10368 := hb (x 3 5)
    have b10369 := hb (x 4 4)
    have b10370 := hb (x 5 11)
    have b10371 := hb (x 6 10)
    have b10372 := hb (x 7 9)
    have b10373 := hb (x 8 8)
    clear * - r10359 e10360 e10361 e10362 e10363 e10364 e10365 b10366 b10367 b10368 b10369 b10370 b10371 b10372 b10373 d10334 g8 g4
    omega
  have d10374 : (x 7 2 && x 7 9).toNat = 0 := by
    have r10375 := hand2 (x 7 2) (x 7 9)
    have b10376 := hb (x 7 9)
    have b10377 := hb (x 7 2 && x 7 9)
    clear * - r10375 b10376 b10377 d10358
    omega
  have d10378 : (x 6 10).toNat = 0 := by
    have r10379 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10380 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e10381 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e10382 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e10383 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e10384 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e10385 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have b10386 := hb (x 1 7)
    have b10387 := hb (x 2 6)
    have b10388 := hb (x 3 5)
    have b10389 := hb (x 4 4)
    have b10390 := hb (x 5 11)
    have b10391 := hb (x 6 10)
    have b10392 := hb (x 7 9)
    have b10393 := hb (x 8 8)
    clear * - r10379 e10380 e10381 e10382 e10383 e10384 e10385 b10386 b10387 b10388 b10389 b10390 b10391 b10392 b10393 d10334 d10358 g8 g4
    omega
  have d10394 : (x 6 1 && x 6 10).toNat = 0 := by
    have r10395 := hand2 (x 6 1) (x 6 10)
    have b10396 := hb (x 6 10)
    have b10397 := hb (x 6 1 && x 6 10)
    clear * - r10395 b10396 b10397 d10378
    omega
  have d10398 : (x 4 3 && x 4 12).toNat = 1 := by
    have r10399 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b10400 := hb (x 1 6)
    have b10401 := hb (x 7 9)
    have b10402 := hb (x 6 1 && x 6 10)
    have b10403 := hb (x 5 2 && x 5 11)
    have b10404 := hb (x 4 3 && x 4 12)
    have b10405 := hb (x 3 4 && x 3 13)
    have b10406 := hb (x 2 5 && x 2 14)
    clear * - r10399 b10400 b10401 b10402 b10403 b10404 b10405 b10406 d10358 d10394 g23 g24 g25 g3
    omega
  have d10407 : (x 4 12).toNat = 1 := by
    have r10408 := hand2 (x 4 3) (x 4 12)
    have b10409 := hb (x 4 12)
    have b10410 := hb (x 4 3 && x 4 12)
    clear * - r10408 b10409 b10410 d10398
    omega
  have d10411 : (x 2 2).toNat = 0 := by
    have r10412 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10413 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e10414 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b10415 := hb (x 1 3)
    have b10416 := hb (x 2 2)
    have b10417 := hb (x 3 13)
    have b10418 := hb (x 4 12)
    clear * - r10412 e10413 e10414 b10415 b10416 b10417 b10418 d10407 g10
    omega
  have d10419 : (x 4 13).toNat = 1 := by
    have r10420 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b10421 := hb (x 2 2)
    have b10422 := hb (x 4 13)
    have b10423 := hb (x 3 1 && x 3 14)
    clear * - r10420 b10421 b10422 b10423 g30 d10411
    omega
  have d10424 : (x 5 12).toNat = 0 := by
    have r10425 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10426 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e10427 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b10428 := hb (x 2 3)
    have b10429 := hb (x 3 2)
    have b10430 := hb (x 4 13)
    have b10431 := hb (x 5 12)
    clear * - r10425 e10426 e10427 b10428 b10429 b10430 b10431 d10419 g7
    omega
  have d10432 : (x 5 3 && x 5 12).toNat = 0 := by
    have r10433 := hand2 (x 5 3) (x 5 12)
    have b10434 := hb (x 5 12)
    have b10435 := hb (x 5 3 && x 5 12)
    clear * - r10433 b10434 b10435 d10424
    omega
  have d10436 : (x 5 4).toNat = 0 := by
    have r10437 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
    have b10438 := hb (x 5 4)
    have b10439 := hb (x 5 12)
    clear * - r10437 b10438 b10439 d10424
    omega
  have d10440 : (x 5 4 && x 5 11).toNat = 0 := by
    have r10441 := hand1 (x 5 4) (x 5 11)
    have b10442 := hb (x 5 4)
    have b10443 := hb (x 5 4 && x 5 11)
    clear * - r10441 b10442 b10443 d10436
    omega
  have d10444 : (x 6 3 && x 6 10).toNat = 0 := by
    have r10445 := hand2 (x 6 3) (x 6 10)
    have b10446 := hb (x 6 10)
    have b10447 := hb (x 6 3 && x 6 10)
    clear * - r10445 b10446 b10447 d10378
    omega
  have d10448 : (x 5 11).toNat = 0 := by
    have r10449 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10450 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e10451 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e10452 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e10453 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e10454 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e10455 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have b10456 := hb (x 1 7)
    have b10457 := hb (x 2 6)
    have b10458 := hb (x 3 5)
    have b10459 := hb (x 4 4)
    have b10460 := hb (x 5 11)
    have b10461 := hb (x 6 10)
    have b10462 := hb (x 7 9)
    have b10463 := hb (x 8 8)
    clear * - r10449 e10450 e10451 e10452 e10453 e10454 e10455 b10456 b10457 b10458 b10459 b10460 b10461 b10462 b10463 d10334 d10358 d10378 g8 g4
    omega
  have d10464 : (x 4 4).toNat = 0 := by
    have r10465 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10466 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e10467 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e10468 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e10469 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e10470 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e10471 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have b10472 := hb (x 1 7)
    have b10473 := hb (x 2 6)
    have b10474 := hb (x 3 5)
    have b10475 := hb (x 4 4)
    have b10476 := hb (x 5 11)
    have b10477 := hb (x 6 10)
    have b10478 := hb (x 7 9)
    have b10479 := hb (x 8 8)
    clear * - r10465 e10466 e10467 e10468 e10469 e10470 e10471 b10472 b10473 b10474 b10475 b10476 b10477 b10478 b10479 d10334 d10358 d10378 d10448 g8 g4
    omega
  have d10480 : (x 4 4 && x 4 13).toNat = 0 := by
    have r10481 := hand1 (x 4 4) (x 4 13)
    have b10482 := hb (x 4 4)
    have b10483 := hb (x 4 4 && x 4 13)
    clear * - r10481 b10482 b10483 d10464
    omega
  have d10484 : (x 8 11).toNat = 1 := by
    have r10485 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b10486 := hb (x 4 4)
    have b10487 := hb (x 8 11)
    have b10488 := hb (x 7 1 && x 7 12)
    have b10489 := hb (x 6 2 && x 6 13)
    have b10490 := hb (x 5 3 && x 5 14)
    clear * - r10485 b10486 b10487 b10488 b10489 b10490 g27 g28 g29 d10464
    omega
  have d10491 : (x 8 3).toNat = 1 := by
    have r10492 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
    have b10493 := hb (x 8 3)
    have b10494 := hb (x 8 11)
    clear * - r10492 b10493 b10494 d10484
    omega
  have d10495 : (x 11 12).toNat = 0 := by
    have r10496 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10497 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e10498 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b10499 := hb (x 8 3)
    have b10500 := hb (x 9 2)
    have b10501 := hb (x 10 13)
    have b10502 := hb (x 11 12)
    clear * - r10496 e10497 e10498 b10499 b10500 b10501 b10502 d10491
    omega
  have d10503 : (x 10 13).toNat = 0 := by
    have r10504 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10505 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e10506 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b10507 := hb (x 8 3)
    have b10508 := hb (x 9 2)
    have b10509 := hb (x 10 13)
    have b10510 := hb (x 11 12)
    clear * - r10504 e10505 e10506 b10507 b10508 b10509 b10510 d10495 d10491
    omega
  have d10511 : (x 9 2).toNat = 0 := by
    have r10512 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10513 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e10514 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b10515 := hb (x 8 3)
    have b10516 := hb (x 9 2)
    have b10517 := hb (x 10 13)
    have b10518 := hb (x 11 12)
    clear * - r10512 e10513 e10514 b10515 b10516 b10517 b10518 d10495 d10503 d10491
    omega
  have d10519 : (x 9 2 && x 9 7).toNat = 0 := by
    have r10520 := hand1 (x 9 2) (x 9 7)
    have b10521 := hb (x 9 2)
    have b10522 := hb (x 9 2 && x 9 7)
    clear * - r10520 b10521 b10522 d10511
    omega
  have d10523 : (x 9 10).toNat = 0 := by
    have r10524 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
    have b10525 := hb (x 9 2)
    have b10526 := hb (x 9 10)
    clear * - r10524 b10525 b10526 d10511
    omega
  have d10527 : (x 11 8).toNat = 0 := by
    have r10528 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10529 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e10530 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e10531 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e10532 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e10533 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e10534 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have b10535 := hb (x 4 7)
    have b10536 := hb (x 5 6)
    have b10537 := hb (x 6 5)
    have b10538 := hb (x 7 4)
    have b10539 := hb (x 8 11)
    have b10540 := hb (x 9 10)
    have b10541 := hb (x 10 9)
    have b10542 := hb (x 11 8)
    clear * - r10528 e10529 e10530 e10531 e10532 e10533 e10534 b10535 b10536 b10537 b10538 b10539 b10540 b10541 b10542 d10523 d10484 g13 g12 g11
    omega
  have d10543 : (x 10 9).toNat = 0 := by
    have r10544 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10545 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e10546 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e10547 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e10548 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e10549 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e10550 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have b10551 := hb (x 4 7)
    have b10552 := hb (x 5 6)
    have b10553 := hb (x 6 5)
    have b10554 := hb (x 7 4)
    have b10555 := hb (x 8 11)
    have b10556 := hb (x 9 10)
    have b10557 := hb (x 10 9)
    have b10558 := hb (x 11 8)
    clear * - r10544 e10545 e10546 e10547 e10548 e10549 e10550 b10551 b10552 b10553 b10554 b10555 b10556 b10557 b10558 d10527 d10523 d10484 g13 g12 g11
    omega
  have d10559 : (x 4 7).toNat = 0 := by
    have r10560 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10561 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e10562 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e10563 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e10564 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e10565 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e10566 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have b10567 := hb (x 4 7)
    have b10568 := hb (x 5 6)
    have b10569 := hb (x 6 5)
    have b10570 := hb (x 7 4)
    have b10571 := hb (x 8 11)
    have b10572 := hb (x 9 10)
    have b10573 := hb (x 10 9)
    have b10574 := hb (x 11 8)
    clear * - r10560 e10561 e10562 e10563 e10564 e10565 e10566 b10567 b10568 b10569 b10570 b10571 b10572 b10573 b10574 d10527 d10543 d10523 d10484 g13 g12 g11
    omega
  have d10575 : (x 4 7 && x 4 12).toNat = 0 := by
    have r10576 := hand1 (x 4 7) (x 4 12)
    have b10577 := hb (x 4 7)
    have b10578 := hb (x 4 7 && x 4 12)
    clear * - r10576 b10577 b10578 d10559
    omega
  have d10579 : (x 2 6).toNat = 0 := by
    have r10580 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10581 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e10582 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e10583 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e10584 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e10585 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e10586 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have b10587 := hb (x 1 7)
    have b10588 := hb (x 2 6)
    have b10589 := hb (x 3 5)
    have b10590 := hb (x 4 4)
    have b10591 := hb (x 5 11)
    have b10592 := hb (x 6 10)
    have b10593 := hb (x 7 9)
    have b10594 := hb (x 8 8)
    clear * - r10580 e10581 e10582 e10583 e10584 e10585 e10586 b10587 b10588 b10589 b10590 b10591 b10592 b10593 b10594 d10334 d10358 d10378 d10448 d10464 g8 g4
    omega
  have r10595 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e10596 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
  have e10597 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
  have e10598 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
  have e10599 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
  have e10600 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
  have e10601 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
  have r10602 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e10603 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
  have e10604 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
  have e10605 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
  have e10606 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
  have e10607 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
  have e10608 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
  have r10609 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e10610 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
  have e10611 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
  have e10612 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
  have e10613 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
  have e10614 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
  have e10615 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
  have r10616 : 1 ≤ (x 11 5).toNat + (x 10 1 && x 10 6).toNat + (x 9 2 && x 9 7).toNat + (x 8 3 && x 8 8).toNat + (x 7 4 && x 7 9).toNat + (x 6 5 && x 6 10).toNat + (x 5 6 && x 5 11).toNat + (x 4 7 && x 4 12).toNat + (x 3 8 && x 3 13).toNat + (x 2 9 && x 2 14).toNat + (x 1 10).toNat := by have q := hcov5 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r10617 : 1 ≤ (x 9 7).toNat + (x 8 1 && x 8 8).toNat + (x 7 2 && x 7 9).toNat + (x 6 3 && x 6 10).toNat + (x 5 4 && x 5 11).toNat + (x 4 5 && x 4 12).toNat + (x 3 6 && x 3 13).toNat + (x 2 7 && x 2 14).toNat + (x 1 8).toNat := by have q := hcov7 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r10618 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r10619 : 1 ≤ (x 8 9).toNat + (x 7 1 && x 7 10).toNat + (x 6 2 && x 6 11).toNat + (x 5 3 && x 5 12).toNat + (x 4 4 && x 4 13).toNat + (x 3 5 && x 3 14).toNat + (x 2 6).toNat := by have q := hcov9 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r10620 := hand2 (x 10 1) (x 10 6)
  have r10621 := hand1 (x 4 5) (x 4 12)
  have r10622 := hand1 (x 2 7) (x 2 14)
  have r10623 := hand1 (x (-3) 4) (x (-3) 13)
  have r10624 := hand1 (x (-4) 5) (x (-4) 14)
  have r10625 := hand2 (x 7 1) (x 7 10)
  have r10626 := hand2 (x 6 2) (x 6 11)
  linarith only [r10595, e10596, e10597, e10598, e10599, e10600, e10601, r10602, e10603, e10604, e10605, e10606, e10607, e10608, r10609, e10610, e10611, e10612, e10613, e10614, e10615, r10616, r10617, r10618, r10619, r10620, r10621, r10622, r10623, r10624, r10625, r10626, g0, g1, g2, g5, g6, d10579, g9, d10436, d10519, d10354, g14, g15, g16, d10575, g17, g18, d10350, d10374, d10444, d10440, g19, g20, g21, g22, d10432, d10480, g26]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b0011001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-1) 6).toNat = 1)
    (g1 : (x (-1) 13).toNat = 0)
    (g2 : (x 0 5).toNat = 0)
    (g3 : (x 0 10).toNat = 0)
    (g4 : (x 1 4).toNat = 0)
    (g5 : (x 3 10).toNat = 0)
    (g6 : (x 3 1 && x 3 10).toNat = 0)
    (g7 : (x 1 3 && x 1 12).toNat = 0)
    (g8 : (x 0 4 && x 0 13).toNat = 0)
    (g9 : (x (-1) 5 && x (-1) 14).toNat = 0)
    (g10 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g11 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g12 : (x (-3) 3 && x (-3) 13).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d10681 : (x (-1) 14).toNat = 1 := by
    have r10682 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
    have b10683 := hb (x (-1) 6)
    have b10684 := hb (x (-1) 14)
    clear * - r10682 b10683 b10684 g0
    omega
  have d10685 : (x (-2) 1).toNat = 0 := by
    have r10686 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b10687 := hb (x (-2) 1)
    have b10688 := hb (x (-1) 14)
    clear * - r10686 b10687 b10688 d10681
    omega
  have d10689 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
    have r10690 := hand1 (x (-2) 1) (x (-2) 14)
    have b10691 := hb (x (-2) 1)
    have b10692 := hb (x (-2) 1 && x (-2) 14)
    clear * - r10690 b10691 b10692 d10685
    omega
  have d10693 : (x (-2) 13).toNat = 0 := by
    have r10694 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
    have b10695 := hb (x (-2) 1)
    have b10696 := hb (x (-2) 13)
    clear * - r10694 b10695 b10696 d10685
    omega
  have d10697 : (x (-3) 2).toNat = 1 := by
    have r10698 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b10699 := hb (x (-3) 2)
    have b10700 := hb (x (-1) 13)
    have b10701 := hb (x (-2) 1 && x (-2) 14)
    clear * - r10698 b10699 b10700 b10701 g1 d10689
    omega
  have d10702 : (x (-3) 14).toNat = 1 := by
    have r10703 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
    have b10704 := hb (x (-3) 2)
    have b10705 := hb (x (-3) 14)
    clear * - r10703 b10704 b10705 d10697
    omega
  have d10706 : (x (-4) 1).toNat = 0 := by
    have r10707 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b10708 := hb (x (-4) 1)
    have b10709 := hb (x (-3) 14)
    clear * - r10707 b10708 b10709 d10702
    omega
  have d10710 : (x (-4) 13).toNat = 0 := by
    have r10711 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
    have b10712 := hb (x (-4) 1)
    have b10713 := hb (x (-4) 13)
    clear * - r10711 b10712 b10713 d10706
    omega
  have d10714 : (x 5 8).toNat = 0 := by
    have r10715 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10716 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e10717 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e10718 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e10719 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e10720 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e10721 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b10722 := hb (x (-2) 7)
    have b10723 := hb (x (-1) 6)
    have b10724 := hb (x 0 5)
    have b10725 := hb (x 1 4)
    have b10726 := hb (x 2 11)
    have b10727 := hb (x 3 10)
    have b10728 := hb (x 4 9)
    have b10729 := hb (x 5 8)
    clear * - r10715 e10716 e10717 e10718 e10719 e10720 e10721 b10722 b10723 b10724 b10725 b10726 b10727 b10728 b10729 g5 g4 g2 g0
    omega
  have d10730 : (x 4 9).toNat = 0 := by
    have r10731 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10732 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e10733 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e10734 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e10735 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e10736 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e10737 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b10738 := hb (x (-2) 7)
    have b10739 := hb (x (-1) 6)
    have b10740 := hb (x 0 5)
    have b10741 := hb (x 1 4)
    have b10742 := hb (x 2 11)
    have b10743 := hb (x 3 10)
    have b10744 := hb (x 4 9)
    have b10745 := hb (x 5 8)
    clear * - r10731 e10732 e10733 e10734 e10735 e10736 e10737 b10738 b10739 b10740 b10741 b10742 b10743 b10744 b10745 d10714 g5 g4 g2 g0
    omega
  have d10746 : (x 2 11).toNat = 0 := by
    have r10747 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10748 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e10749 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e10750 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e10751 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e10752 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e10753 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b10754 := hb (x (-2) 7)
    have b10755 := hb (x (-1) 6)
    have b10756 := hb (x 0 5)
    have b10757 := hb (x 1 4)
    have b10758 := hb (x 2 11)
    have b10759 := hb (x 3 10)
    have b10760 := hb (x 4 9)
    have b10761 := hb (x 5 8)
    clear * - r10747 e10748 e10749 e10750 e10751 e10752 e10753 b10754 b10755 b10756 b10757 b10758 b10759 b10760 b10761 d10714 d10730 g5 g4 g2 g0
    omega
  have d10762 : (x 2 2 && x 2 11).toNat = 0 := by
    have r10763 := hand2 (x 2 2) (x 2 11)
    have b10764 := hb (x 2 11)
    have b10765 := hb (x 2 2 && x 2 11)
    clear * - r10763 b10764 b10765 d10746
    omega
  have d10766 : (x (-2) 6).toNat = 1 := by
    have r10767 : 1 ≤ (x 4 9).toNat + (x 3 1 && x 3 10).toNat + (x 2 2 && x 2 11).toNat + (x 1 3 && x 1 12).toNat + (x 0 4 && x 0 13).toNat + (x (-1) 5 && x (-1) 14).toNat + (x (-2) 6).toNat := by have q := hcov9 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b10768 := hb (x (-2) 6)
    have b10769 := hb (x 4 9)
    have b10770 := hb (x 3 1 && x 3 10)
    have b10771 := hb (x 2 2 && x 2 11)
    have b10772 := hb (x 1 3 && x 1 12)
    have b10773 := hb (x 0 4 && x 0 13)
    have b10774 := hb (x (-1) 5 && x (-1) 14)
    clear * - r10767 b10768 b10769 b10770 b10771 b10772 b10773 b10774 d10730 g6 d10762 g7 g8 g9
    omega
  have d10775 : (x (-2) 14).toNat = 1 := by
    have r10776 : (x (-2) 6).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp6 (-2))
    have b10777 := hb (x (-2) 6)
    have b10778 := hb (x (-2) 14)
    clear * - r10776 b10777 b10778 d10766
    omega
  have d10779 : (x (-3) 1).toNat = 0 := by
    have r10780 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b10781 := hb (x (-3) 1)
    have b10782 := hb (x (-2) 14)
    clear * - r10780 b10781 b10782 d10775
    omega
  have d10783 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
    have r10784 := hand1 (x (-3) 1) (x (-3) 14)
    have b10785 := hb (x (-3) 1)
    have b10786 := hb (x (-3) 1 && x (-3) 14)
    clear * - r10784 b10785 b10786 d10779
    omega
  have d10787 : (x (-4) 2).toNat = 1 := by
    have r10788 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b10789 := hb (x (-4) 2)
    have b10790 := hb (x (-2) 13)
    have b10791 := hb (x (-3) 1 && x (-3) 14)
    clear * - r10788 b10789 b10790 b10791 d10693 d10783
    omega
  have d10792 : (x (-4) 14).toNat = 1 := by
    have r10793 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
    have b10794 := hb (x (-4) 2)
    have b10795 := hb (x (-4) 14)
    clear * - r10793 b10794 b10795 d10787
    omega
  have d10796 : (x (-5) 1).toNat = 0 := by
    have r10797 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b10798 := hb (x (-5) 1)
    have b10799 := hb (x (-4) 14)
    clear * - r10797 b10798 b10799 d10792
    omega
  have d10800 : (x (-5) 1 && x (-5) 14).toNat = 0 := by
    have r10801 := hand1 (x (-5) 1) (x (-5) 14)
    have b10802 := hb (x (-5) 1)
    have b10803 := hb (x (-5) 1 && x (-5) 14)
    clear * - r10801 b10802 b10803 d10796
    omega
  have d10804 : (x (-6) 2).toNat = 1 := by
    have r10805 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b10806 := hb (x (-6) 2)
    have b10807 := hb (x (-4) 13)
    have b10808 := hb (x (-5) 1 && x (-5) 14)
    clear * - r10805 b10806 b10807 b10808 d10710 d10800
    omega
  have d10809 : (x (-4) 12).toNat = 0 := by
    have r10810 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10811 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e10812 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b10813 := hb (x (-7) 3)
    have b10814 := hb (x (-6) 2)
    have b10815 := hb (x (-5) 13)
    have b10816 := hb (x (-4) 12)
    clear * - r10810 e10811 e10812 b10813 b10814 b10815 b10816 d10804
    omega
  have d10817 : (x (-4) 4).toNat = 0 := by
    have r10818 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
    have b10819 := hb (x (-4) 4)
    have b10820 := hb (x (-4) 12)
    clear * - r10818 b10819 b10820 d10809
    omega
  have d10821 : (x (-4) 4 && x (-4) 14).toNat = 0 := by
    have r10822 := hand1 (x (-4) 4) (x (-4) 14)
    have b10823 := hb (x (-4) 4)
    have b10824 := hb (x (-4) 4 && x (-4) 14)
    clear * - r10822 b10823 b10824 d10817
    omega
  have d10825 : (x (-5) 5).toNat = 1 := by
    have r10826 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b10827 := hb (x (-5) 5)
    have b10828 := hb (x 0 10)
    have b10829 := hb (x (-1) 1 && x (-1) 11)
    have b10830 := hb (x (-2) 2 && x (-2) 12)
    have b10831 := hb (x (-3) 3 && x (-3) 13)
    have b10832 := hb (x (-4) 4 && x (-4) 14)
    clear * - r10826 b10827 b10828 b10829 b10830 b10831 b10832 g3 g10 g11 g12 d10821
    omega
  have d10833 : (x (-5) 13).toNat = 1 := by
    have r10834 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
    have b10835 := hb (x (-5) 5)
    have b10836 := hb (x (-5) 13)
    clear * - r10834 b10835 b10836 d10825
    omega
  have r10837 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e10838 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
  have e10839 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
  have b10840 := hb (x (-7) 3)
  have b10841 := hb (x (-6) 2)
  have b10842 := hb (x (-5) 13)
  have b10843 := hb (x (-4) 12)
  linarith only [r10837, e10838, e10839, b10840, b10841, b10842, b10843, d10809, d10833, d10804]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b001101 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-2) 11).toNat = 0)
    (g1 : (x (-1) 10).toNat = 0)
    (g2 : (x 0 9).toNat = 1)
    (g3 : (x 1 9).toNat = 0)
    (g4 : (x 0 1 && x 0 10).toNat = 0)
    (g5 : (x (-1) 2 && x (-1) 11).toNat = 0)
    (g6 : (x (-2) 3 && x (-2) 12).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d10845 : (x 1 8).toNat = 0 := by
    have r10846 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10847 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e10848 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e10849 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e10850 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e10851 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e10852 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b10853 := hb (x (-6) 7)
    have b10854 := hb (x (-5) 6)
    have b10855 := hb (x (-4) 5)
    have b10856 := hb (x (-3) 4)
    have b10857 := hb (x (-2) 11)
    have b10858 := hb (x (-1) 10)
    have b10859 := hb (x 0 9)
    have b10860 := hb (x 1 8)
    clear * - r10846 e10847 e10848 e10849 e10850 e10851 e10852 b10853 b10854 b10855 b10856 b10857 b10858 b10859 b10860 g2 g1 g0
    omega
  have d10861 : (x (-3) 4).toNat = 0 := by
    have r10862 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10863 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e10864 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e10865 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e10866 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e10867 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e10868 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b10869 := hb (x (-6) 7)
    have b10870 := hb (x (-5) 6)
    have b10871 := hb (x (-4) 5)
    have b10872 := hb (x (-3) 4)
    have b10873 := hb (x (-2) 11)
    have b10874 := hb (x (-1) 10)
    have b10875 := hb (x 0 9)
    have b10876 := hb (x 1 8)
    clear * - r10862 e10863 e10864 e10865 e10866 e10867 e10868 b10869 b10870 b10871 b10872 b10873 b10874 b10875 b10876 d10845 g2 g1 g0
    omega
  have d10877 : (x (-3) 4 && x (-3) 13).toNat = 0 := by
    have r10878 := hand1 (x (-3) 4) (x (-3) 13)
    have b10879 := hb (x (-3) 4)
    have b10880 := hb (x (-3) 4 && x (-3) 13)
    clear * - r10878 b10879 b10880 d10861
    omega
  have d10881 : (x (-4) 5).toNat = 0 := by
    have r10882 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10883 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e10884 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e10885 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e10886 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e10887 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e10888 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b10889 := hb (x (-6) 7)
    have b10890 := hb (x (-5) 6)
    have b10891 := hb (x (-4) 5)
    have b10892 := hb (x (-3) 4)
    have b10893 := hb (x (-2) 11)
    have b10894 := hb (x (-1) 10)
    have b10895 := hb (x 0 9)
    have b10896 := hb (x 1 8)
    clear * - r10882 e10883 e10884 e10885 e10886 e10887 e10888 b10889 b10890 b10891 b10892 b10893 b10894 b10895 b10896 d10845 g2 g1 g0 d10861
    omega
  have d10897 : (x (-4) 5 && x (-4) 14).toNat = 0 := by
    have r10898 := hand1 (x (-4) 5) (x (-4) 14)
    have b10899 := hb (x (-4) 5)
    have b10900 := hb (x (-4) 5 && x (-4) 14)
    clear * - r10898 b10899 b10900 d10881
    omega
  have d10901 : (x (-5) 6).toNat = 1 := by
    have r10902 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b10903 := hb (x (-5) 6)
    have b10904 := hb (x 1 9)
    have b10905 := hb (x 0 1 && x 0 10)
    have b10906 := hb (x (-1) 2 && x (-1) 11)
    have b10907 := hb (x (-2) 3 && x (-2) 12)
    have b10908 := hb (x (-3) 4 && x (-3) 13)
    have b10909 := hb (x (-4) 5 && x (-4) 14)
    clear * - r10902 b10903 b10904 b10905 b10906 b10907 b10908 b10909 g3 g4 g5 g6 d10877 d10897
    omega
  have r10910 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e10911 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
  have e10912 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
  have e10913 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
  have e10914 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
  have e10915 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
  have e10916 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
  have b10917 := hb (x (-6) 7)
  have b10918 := hb (x (-5) 6)
  have b10919 := hb (x (-4) 5)
  have b10920 := hb (x (-3) 4)
  have b10921 := hb (x (-2) 11)
  have b10922 := hb (x (-1) 10)
  have b10923 := hb (x 0 9)
  have b10924 := hb (x 1 8)
  linarith only [r10910, e10911, e10912, e10913, e10914, e10915, e10916, b10917, b10918, b10919, b10920, b10921, b10922, b10923, b10924, d10845, g2, g1, g0, d10861, d10881, d10901]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b00111_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 11).toNat = 0)
    (g1 : (x (-2) 10).toNat = 0)
    (g2 : (x (-1) 9).toNat = 0)
    (g3 : (x 0 8).toNat = 1)
    (g4 : (x 0 10).toNat = 0)
    (g5 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g6 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g7 : (x (-3) 3 && x (-3) 13).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d10926 : (x (-4) 4).toNat = 0 := by
    have r10927 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10928 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e10929 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e10930 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e10931 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e10932 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e10933 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b10934 := hb (x (-7) 7)
    have b10935 := hb (x (-6) 6)
    have b10936 := hb (x (-5) 5)
    have b10937 := hb (x (-4) 4)
    have b10938 := hb (x (-3) 11)
    have b10939 := hb (x (-2) 10)
    have b10940 := hb (x (-1) 9)
    have b10941 := hb (x 0 8)
    clear * - r10927 e10928 e10929 e10930 e10931 e10932 e10933 b10934 b10935 b10936 b10937 b10938 b10939 b10940 b10941 g3 g2 g1 g0
    omega
  have d10942 : (x (-4) 4 && x (-4) 14).toNat = 0 := by
    have r10943 := hand1 (x (-4) 4) (x (-4) 14)
    have b10944 := hb (x (-4) 4)
    have b10945 := hb (x (-4) 4 && x (-4) 14)
    clear * - r10943 b10944 b10945 d10926
    omega
  have d10946 : (x (-5) 5).toNat = 1 := by
    have r10947 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b10948 := hb (x (-5) 5)
    have b10949 := hb (x 0 10)
    have b10950 := hb (x (-1) 1 && x (-1) 11)
    have b10951 := hb (x (-2) 2 && x (-2) 12)
    have b10952 := hb (x (-3) 3 && x (-3) 13)
    have b10953 := hb (x (-4) 4 && x (-4) 14)
    clear * - r10947 b10948 b10949 b10950 b10951 b10952 b10953 g4 g5 g6 g7 d10942
    omega
  have r10954 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e10955 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
  have e10956 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
  have e10957 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
  have e10958 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
  have e10959 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
  have e10960 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
  have b10961 := hb (x (-7) 7)
  have b10962 := hb (x (-6) 6)
  have b10963 := hb (x (-5) 5)
  have b10964 := hb (x (-4) 4)
  have b10965 := hb (x (-3) 11)
  have b10966 := hb (x (-2) 10)
  have b10967 := hb (x (-1) 9)
  have b10968 := hb (x 0 8)
  linarith only [r10954, e10955, e10956, e10957, e10958, e10959, e10960, b10961, b10962, b10963, b10964, b10965, b10966, b10967, b10968, g3, g2, g1, g0, d10926, d10946]

theorem cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b00111 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 11).toNat = 0)
    (g1 : (x (-2) 10).toNat = 0)
    (g2 : (x (-1) 9).toNat = 0)
    (g3 : (x 0 8).toNat = 1)
    (g4 : (x 0 10).toNat = 0)
    (g5 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g6 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g7 : (x (-3) 3 && x (-3) 13).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b00111_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7
