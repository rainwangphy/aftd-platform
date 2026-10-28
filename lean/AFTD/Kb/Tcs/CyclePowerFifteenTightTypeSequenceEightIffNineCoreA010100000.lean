import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a010100000

Topic: combinatorics   Node: e596fe3f0989

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core: under the layer-free tight-cover constraints for k = 15 and 74 fixed bits of the class-type sequence near position 0, the constraints are contradictory. Its module also proves the sibling branches cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a0011, cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a0100.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a0011 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-4) 4).toNat = 0)
    (g1 : (x 0 4).toNat = 1)
    (g2 : (x 0 11).toNat = 0)
    (g3 : (x 1 2).toNat = 0)
    (g4 : (x 3 2).toNat = 0)
    (g5 : (x 3 4).toNat = 0)
    (g6 : (x 0 1 && x 0 14).toNat = 0)
    (g7 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d40940 : (x 0 12).toNat = 1 := by
    have r40941 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
    have b40942 := hb (x 0 4)
    have b40943 := hb (x 0 12)
    clear * - r40941 b40942 b40943 g1
    omega
  have d40944 : (x (-1) 13).toNat = 0 := by
    have r40945 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e40946 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e40947 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b40948 := hb (x (-3) 3)
    have b40949 := hb (x (-2) 2)
    have b40950 := hb (x (-1) 13)
    have b40951 := hb (x 0 12)
    clear * - r40945 e40946 e40947 b40948 b40949 b40950 b40951 d40940
    omega
  have d40952 : (x (-2) 2).toNat = 0 := by
    have r40953 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e40954 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e40955 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b40956 := hb (x (-3) 3)
    have b40957 := hb (x (-2) 2)
    have b40958 := hb (x (-1) 13)
    have b40959 := hb (x 0 12)
    clear * - r40953 e40954 e40955 b40956 b40957 b40958 b40959 d40940 d40944
    omega
  have d40960 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
    have r40961 := hand1 (x (-2) 2) (x (-2) 13)
    have b40962 := hb (x (-2) 2)
    have b40963 := hb (x (-2) 2 && x (-2) 13)
    clear * - r40961 b40962 b40963 d40952
    omega
  have d40964 : (x (-3) 3).toNat = 0 := by
    have r40965 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e40966 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e40967 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b40968 := hb (x (-3) 3)
    have b40969 := hb (x (-2) 2)
    have b40970 := hb (x (-1) 13)
    have b40971 := hb (x 0 12)
    clear * - r40965 e40966 e40967 b40968 b40969 b40970 b40971 d40940 d40944 d40952
    omega
  have d40972 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
    have r40973 := hand1 (x (-3) 3) (x (-3) 14)
    have b40974 := hb (x (-3) 3)
    have b40975 := hb (x (-3) 3 && x (-3) 14)
    clear * - r40973 b40974 b40975 d40964
    omega
  have d40976 : (x (-1) 1 && x (-1) 12).toNat = 1 := by
    have r40977 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b40978 := hb (x (-4) 4)
    have b40979 := hb (x 0 11)
    have b40980 := hb (x (-1) 1 && x (-1) 12)
    have b40981 := hb (x (-2) 2 && x (-2) 13)
    have b40982 := hb (x (-3) 3 && x (-3) 14)
    clear * - r40977 b40978 b40979 b40980 b40981 b40982 g2 d40960 d40972 g0
    omega
  have d40983 : (x (-1) 12).toNat = 1 := by
    have r40984 := hand2 (x (-1) 1) (x (-1) 12)
    have b40985 := hb (x (-1) 12)
    have b40986 := hb (x (-1) 1 && x (-1) 12)
    clear * - r40984 b40985 b40986 d40976
    omega
  have d40987 : (x (-2) 13).toNat = 0 := by
    have r40988 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e40989 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e40990 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b40991 := hb (x (-4) 3)
    have b40992 := hb (x (-3) 2)
    have b40993 := hb (x (-2) 13)
    have b40994 := hb (x (-1) 12)
    clear * - r40988 e40989 e40990 b40991 b40992 b40993 b40994 d40983
    omega
  have d40995 : (x (-3) 2).toNat = 0 := by
    have r40996 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e40997 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e40998 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b40999 := hb (x (-4) 3)
    have b41000 := hb (x (-3) 2)
    have b41001 := hb (x (-2) 13)
    have b41002 := hb (x (-1) 12)
    clear * - r40996 e40997 e40998 b40999 b41000 b41001 b41002 d40983 d40987
    omega
  have d41003 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
    have r41004 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b41005 := hb (x (-3) 2)
    have b41006 := hb (x (-1) 13)
    have b41007 := hb (x (-2) 1 && x (-2) 14)
    clear * - r41004 b41005 b41006 b41007 d40944 d40995
    omega
  have d41008 : (x (-2) 1).toNat = 1 := by
    have r41009 := hand1 (x (-2) 1) (x (-2) 14)
    have b41010 := hb (x (-2) 1)
    have b41011 := hb (x (-2) 1 && x (-2) 14)
    clear * - r41009 b41010 b41011 d41003
    omega
  have d41012 : (x (-1) 14).toNat = 0 := by
    have r41013 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b41014 := hb (x (-2) 1)
    have b41015 := hb (x (-1) 14)
    clear * - r41013 b41014 b41015 d41008
    omega
  have d41016 : (x (-1) 1 && x (-1) 14).toNat = 0 := by
    have r41017 := hand2 (x (-1) 1) (x (-1) 14)
    have b41018 := hb (x (-1) 14)
    have b41019 := hb (x (-1) 1 && x (-1) 14)
    clear * - r41017 b41018 b41019 d41012
    omega
  have d41020 : (x 0 13).toNat = 1 := by
    have r41021 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b41022 := hb (x (-2) 2)
    have b41023 := hb (x 0 13)
    have b41024 := hb (x (-1) 1 && x (-1) 14)
    clear * - r41021 b41022 b41023 b41024 d41016 d40952
    omega
  have d41025 : (x 1 12).toNat = 0 := by
    have r41026 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e41027 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e41028 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b41029 := hb (x (-2) 3)
    have b41030 := hb (x (-1) 2)
    have b41031 := hb (x 0 13)
    have b41032 := hb (x 1 12)
    clear * - r41026 e41027 e41028 b41029 b41030 b41031 b41032 d41020
    omega
  have d41033 : (x (-1) 2).toNat = 0 := by
    have r41034 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e41035 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e41036 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b41037 := hb (x (-2) 3)
    have b41038 := hb (x (-1) 2)
    have b41039 := hb (x 0 13)
    have b41040 := hb (x 1 12)
    clear * - r41034 e41035 e41036 b41037 b41038 b41039 b41040 d41025 d41020
    omega
  have d41041 : (x 1 13).toNat = 1 := by
    have r41042 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b41043 := hb (x (-1) 2)
    have b41044 := hb (x 1 13)
    have b41045 := hb (x 0 1 && x 0 14)
    clear * - r41042 b41043 b41044 b41045 g6 d41033
    omega
  have d41046 : (x 1 1).toNat = 1 := by
    have r41047 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
    have b41048 := hb (x 1 1)
    have b41049 := hb (x 1 13)
    clear * - r41047 b41048 b41049 d41041
    omega
  have d41050 : (x 2 14).toNat = 0 := by
    have r41051 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b41052 := hb (x 1 1)
    have b41053 := hb (x 2 14)
    clear * - r41051 b41052 b41053 d41046
    omega
  have d41054 : (x 2 1 && x 2 14).toNat = 0 := by
    have r41055 := hand2 (x 2 1) (x 2 14)
    have b41056 := hb (x 2 14)
    have b41057 := hb (x 2 1 && x 2 14)
    clear * - r41055 b41056 b41057 d41050
    omega
  have d41058 : (x 3 13).toNat = 1 := by
    have r41059 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b41060 := hb (x 1 2)
    have b41061 := hb (x 3 13)
    have b41062 := hb (x 2 1 && x 2 14)
    clear * - r41059 b41060 b41061 b41062 d41054 g3
    omega
  have d41063 : (x 3 1).toNat = 1 := by
    have r41064 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
    have b41065 := hb (x 3 1)
    have b41066 := hb (x 3 13)
    clear * - r41064 b41065 b41066 d41058
    omega
  have d41067 : (x 4 14).toNat = 0 := by
    have r41068 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b41069 := hb (x 3 1)
    have b41070 := hb (x 4 14)
    clear * - r41068 b41069 b41070 d41063
    omega
  have d41071 : (x 4 1 && x 4 14).toNat = 0 := by
    have r41072 := hand2 (x 4 1) (x 4 14)
    have b41073 := hb (x 4 14)
    have b41074 := hb (x 4 1 && x 4 14)
    clear * - r41072 b41073 b41074 d41067
    omega
  have d41075 : (x 5 13).toNat = 1 := by
    have r41076 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b41077 := hb (x 3 2)
    have b41078 := hb (x 5 13)
    have b41079 := hb (x 4 1 && x 4 14)
    clear * - r41076 b41077 b41078 b41079 d41071 g4
    omega
  have d41080 : (x 5 1).toNat = 1 := by
    have r41081 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
    have b41082 := hb (x 5 1)
    have b41083 := hb (x 5 13)
    clear * - r41081 b41082 b41083 d41075
    omega
  have d41084 : (x 6 14).toNat = 0 := by
    have r41085 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b41086 := hb (x 5 1)
    have b41087 := hb (x 6 14)
    clear * - r41085 b41086 b41087 d41080
    omega
  have d41088 : (x 6 1 && x 6 14).toNat = 0 := by
    have r41089 := hand2 (x 6 1) (x 6 14)
    have b41090 := hb (x 6 14)
    have b41091 := hb (x 6 1 && x 6 14)
    clear * - r41089 b41090 b41091 d41084
    omega
  have d41092 : (x 6 2).toNat = 0 := by
    have r41093 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
    have b41094 := hb (x 6 2)
    have b41095 := hb (x 6 14)
    clear * - r41093 b41094 b41095 d41084
    omega
  have d41096 : (x 6 12).toNat = 0 := by
    have r41097 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e41098 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e41099 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b41100 := hb (x 3 3)
    have b41101 := hb (x 4 2)
    have b41102 := hb (x 5 13)
    have b41103 := hb (x 6 12)
    clear * - r41097 e41098 e41099 b41100 b41101 b41102 b41103 d41075
    omega
  have d41104 : (x 6 1 && x 6 12).toNat = 0 := by
    have r41105 := hand2 (x 6 1) (x 6 12)
    have b41106 := hb (x 6 12)
    have b41107 := hb (x 6 1 && x 6 12)
    clear * - r41105 b41106 b41107 d41096
    omega
  have d41108 : (x 4 2).toNat = 0 := by
    have r41109 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e41110 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e41111 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b41112 := hb (x 3 3)
    have b41113 := hb (x 4 2)
    have b41114 := hb (x 5 13)
    have b41115 := hb (x 6 12)
    clear * - r41109 e41110 e41111 b41112 b41113 b41114 b41115 d41096 d41075
    omega
  have d41116 : (x 4 3 && x 4 14).toNat = 0 := by
    have r41117 := hand2 (x 4 3) (x 4 14)
    have b41118 := hb (x 4 14)
    have b41119 := hb (x 4 3 && x 4 14)
    clear * - r41117 b41118 b41119 d41067
    omega
  have d41120 : (x 4 12).toNat = 0 := by
    have r41121 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e41122 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e41123 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b41124 := hb (x 1 3)
    have b41125 := hb (x 2 2)
    have b41126 := hb (x 3 13)
    have b41127 := hb (x 4 12)
    clear * - r41121 e41122 e41123 b41124 b41125 b41126 b41127 d41058
    omega
  have d41128 : (x 2 2).toNat = 0 := by
    have r41129 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e41130 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e41131 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b41132 := hb (x 1 3)
    have b41133 := hb (x 2 2)
    have b41134 := hb (x 3 13)
    have b41135 := hb (x 4 12)
    clear * - r41129 e41130 e41131 b41132 b41133 b41134 b41135 d41120 d41058
    omega
  have d41136 : (x 4 13).toNat = 1 := by
    have r41137 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b41138 := hb (x 2 2)
    have b41139 := hb (x 4 13)
    have b41140 := hb (x 3 1 && x 3 14)
    clear * - r41137 b41138 b41139 b41140 g7 d41128
    omega
  have d41141 : (x 4 1).toNat = 1 := by
    have r41142 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
    have b41143 := hb (x 4 1)
    have b41144 := hb (x 4 13)
    clear * - r41142 b41143 b41144 d41136
    omega
  have d41145 : (x 5 14).toNat = 0 := by
    have r41146 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b41147 := hb (x 4 1)
    have b41148 := hb (x 5 14)
    clear * - r41146 b41147 b41148 d41141
    omega
  have d41149 : (x 5 1 && x 5 14).toNat = 0 := by
    have r41150 := hand2 (x 5 1) (x 5 14)
    have b41151 := hb (x 5 14)
    have b41152 := hb (x 5 1 && x 5 14)
    clear * - r41150 b41151 b41152 d41145
    omega
  have d41153 : (x 6 13).toNat = 1 := by
    have r41154 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b41155 := hb (x 4 2)
    have b41156 := hb (x 6 13)
    have b41157 := hb (x 5 1 && x 5 14)
    clear * - r41154 b41155 b41156 b41157 d41149 d41108
    omega
  have d41158 : (x 6 1).toNat = 1 := by
    have r41159 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
    have b41160 := hb (x 6 1)
    have b41161 := hb (x 6 13)
    clear * - r41159 b41160 b41161 d41153
    omega
  have d41162 : (x 7 14).toNat = 0 := by
    have r41163 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b41164 := hb (x 6 1)
    have b41165 := hb (x 7 14)
    clear * - r41163 b41164 b41165 d41158
    omega
  have d41166 : (x 7 1 && x 7 14).toNat = 0 := by
    have r41167 := hand2 (x 7 1) (x 7 14)
    have b41168 := hb (x 7 14)
    have b41169 := hb (x 7 1 && x 7 14)
    clear * - r41167 b41168 b41169 d41162
    omega
  have d41170 : (x 8 13).toNat = 1 := by
    have r41171 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b41172 := hb (x 6 2)
    have b41173 := hb (x 8 13)
    have b41174 := hb (x 7 1 && x 7 14)
    clear * - r41171 b41172 b41173 b41174 d41166 d41092
    omega
  have d41175 : (x 9 12).toNat = 0 := by
    have r41176 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e41177 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e41178 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b41179 := hb (x 6 3)
    have b41180 := hb (x 7 2)
    have b41181 := hb (x 8 13)
    have b41182 := hb (x 9 12)
    clear * - r41176 e41177 e41178 b41179 b41180 b41181 b41182 d41170
    omega
  have d41183 : (x 7 2).toNat = 0 := by
    have r41184 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e41185 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e41186 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b41187 := hb (x 6 3)
    have b41188 := hb (x 7 2)
    have b41189 := hb (x 8 13)
    have b41190 := hb (x 9 12)
    clear * - r41184 e41185 e41186 b41187 b41188 b41189 b41190 d41175 d41170
    omega
  have d41191 : (x 7 12).toNat = 0 := by
    have r41192 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e41193 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e41194 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b41195 := hb (x 4 3)
    have b41196 := hb (x 5 2)
    have b41197 := hb (x 6 13)
    have b41198 := hb (x 7 12)
    clear * - r41192 e41193 e41194 b41195 b41196 b41197 b41198 d41153
    omega
  have d41199 : (x 5 2).toNat = 0 := by
    have r41200 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e41201 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e41202 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b41203 := hb (x 4 3)
    have b41204 := hb (x 5 2)
    have b41205 := hb (x 6 13)
    have b41206 := hb (x 7 12)
    clear * - r41200 e41201 e41202 b41203 b41204 b41205 b41206 d41191 d41153
    omega
  have d41207 : (x 5 2 && x 5 13).toNat = 0 := by
    have r41208 := hand1 (x 5 2) (x 5 13)
    have b41209 := hb (x 5 2)
    have b41210 := hb (x 5 2 && x 5 13)
    clear * - r41208 b41209 b41210 d41199
    omega
  have d41211 : (x 7 11).toNat = 1 := by
    have r41212 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b41213 := hb (x 3 4)
    have b41214 := hb (x 7 11)
    have b41215 := hb (x 6 1 && x 6 12)
    have b41216 := hb (x 5 2 && x 5 13)
    have b41217 := hb (x 4 3 && x 4 14)
    clear * - r41212 b41213 b41214 b41215 b41216 b41217 d41104 d41207 d41116 g5
    omega
  have d41218 : (x 7 3).toNat = 1 := by
    have r41219 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
    have b41220 := hb (x 7 3)
    have b41221 := hb (x 7 11)
    clear * - r41219 b41220 b41221 d41211
    omega
  have d41222 : (x 10 12).toNat = 0 := by
    have r41223 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e41224 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e41225 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b41226 := hb (x 7 3)
    have b41227 := hb (x 8 2)
    have b41228 := hb (x 9 13)
    have b41229 := hb (x 10 12)
    clear * - r41223 e41224 e41225 b41226 b41227 b41228 b41229 d41218
    omega
  have d41230 : (x 9 13).toNat = 0 := by
    have r41231 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e41232 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e41233 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b41234 := hb (x 7 3)
    have b41235 := hb (x 8 2)
    have b41236 := hb (x 9 13)
    have b41237 := hb (x 10 12)
    clear * - r41231 e41232 e41233 b41234 b41235 b41236 b41237 d41222 d41218
    omega
  have d41238 : (x 8 1 && x 8 14).toNat = 1 := by
    have r41239 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b41240 := hb (x 7 2)
    have b41241 := hb (x 9 13)
    have b41242 := hb (x 8 1 && x 8 14)
    clear * - r41239 b41240 b41241 b41242 d41230 d41183
    omega
  have d41243 : (x 8 14).toNat = 1 := by
    have r41244 := hand2 (x 8 1) (x 8 14)
    have b41245 := hb (x 8 14)
    have b41246 := hb (x 8 1 && x 8 14)
    clear * - r41244 b41245 b41246 d41238
    omega
  have d41247 : (x 7 1).toNat = 0 := by
    have r41248 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b41249 := hb (x 7 1)
    have b41250 := hb (x 8 14)
    clear * - r41248 b41249 b41250 d41243
    omega
  have d41251 : (x 7 13).toNat = 0 := by
    have r41252 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
    have b41253 := hb (x 7 1)
    have b41254 := hb (x 7 13)
    clear * - r41252 b41253 b41254 d41247
    omega
  have r41255 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have b41256 := hb (x 5 2)
  have b41257 := hb (x 7 13)
  have b41258 := hb (x 6 1 && x 6 14)
  linarith only [r41255, b41256, b41257, b41258, d41251, d41088, d41199]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a0100 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-6) 6).toNat = 0)
    (g1 : (x (-5) 5).toNat = 0)
    (g2 : (x (-1) 9).toNat = 0)
    (g3 : (x (-1) 13).toNat = 0)
    (g4 : (x 0 1).toNat = 0)
    (g5 : (x 0 2).toNat = 0)
    (g6 : (x 0 7).toNat = 0)
    (g7 : (x 0 9).toNat = 0)
    (g8 : (x 0 10).toNat = 0)
    (g9 : (x 0 14).toNat = 1)
    (g10 : (x (-1) 1 && x (-1) 6).toNat = 0)
    (g11 : (x (-4) 4 && x (-4) 9).toNat = 0)
    (g12 : (x (-5) 5 && x (-5) 10).toNat = 0)
    (g13 : (x (-6) 6 && x (-6) 11).toNat = 0)
    (g14 : (x (-7) 7 && x (-7) 12).toNat = 0)
    (g15 : (x (-1) 1 && x (-1) 8).toNat = 0)
    (g16 : (x (-4) 4 && x (-4) 11).toNat = 0)
    (g17 : (x (-5) 5 && x (-5) 12).toNat = 0)
    (g18 : (x (-6) 6 && x (-6) 13).toNat = 0)
    (g19 : (x (-7) 7 && x (-7) 14).toNat = 0)
    (g20 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g21 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g22 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g23 : (x (-4) 4 && x (-4) 13).toNat = 0)
    (g24 : (x (-5) 5 && x (-5) 14).toNat = 0)
    (g25 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g26 : (x (-4) 4 && x (-4) 14).toNat = 0)
    (g27 : (x (-1) 1 && x (-1) 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d41332 : (x 0 1 && x 0 14).toNat = 0 := by
    have r41333 := hand1 (x 0 1) (x 0 14)
    have b41334 := hb (x 0 1)
    have b41335 := hb (x 0 1 && x 0 14)
    clear * - r41333 b41334 b41335 g4
    omega
  have d41336 : (x 0 13).toNat = 0 := by
    have r41337 : (x 0 13).toNat ≤ (x 0 1).toNat := himp _ _ (hp13 0)
    have b41338 := hb (x 0 1)
    have b41339 := hb (x 0 13)
    clear * - r41337 b41338 b41339 g4
    omega
  have d41340 : (x 0 13 && x 0 14).toNat = 0 := by
    have r41341 := hand1 (x 0 13) (x 0 14)
    have b41342 := hb (x 0 13)
    have b41343 := hb (x 0 13 && x 0 14)
    clear * - r41341 b41342 b41343 d41336
    omega
  have d41344 : (x 0 5).toNat = 0 := by
    have r41345 : (x 0 5).toNat ≤ (x 0 13).toNat := himp _ _ (hp5 0)
    have b41346 := hb (x 0 5)
    have b41347 := hb (x 0 13)
    clear * - r41345 b41346 b41347 d41336
    omega
  have d41348 : (x 0 5 && x 0 14).toNat = 0 := by
    have r41349 := hand1 (x 0 5) (x 0 14)
    have b41350 := hb (x 0 5)
    have b41351 := hb (x 0 5 && x 0 14)
    clear * - r41349 b41350 b41351 d41344
    omega
  have d41352 : (x (-2) 2).toNat = 1 := by
    have r41353 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b41354 := hb (x (-2) 2)
    have b41355 := hb (x 0 13)
    have b41356 := hb (x (-1) 1 && x (-1) 14)
    clear * - r41353 b41354 b41355 b41356 d41336 g27
    omega
  have d41357 : (x (-2) 14).toNat = 1 := by
    have r41358 : (x (-2) 2).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp2 (-2))
    have b41359 := hb (x (-2) 2)
    have b41360 := hb (x (-2) 14)
    clear * - r41358 b41359 b41360 d41352
    omega
  have d41361 : (x (-3) 1).toNat = 0 := by
    have r41362 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b41363 := hb (x (-3) 1)
    have b41364 := hb (x (-2) 14)
    clear * - r41362 b41363 b41364 d41357
    omega
  have d41365 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
    have r41366 := hand1 (x (-3) 1) (x (-3) 14)
    have b41367 := hb (x (-3) 1)
    have b41368 := hb (x (-3) 1 && x (-3) 14)
    clear * - r41366 b41367 b41368 d41361
    omega
  have d41369 : (x (-3) 13).toNat = 0 := by
    have r41370 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
    have b41371 := hb (x (-3) 1)
    have b41372 := hb (x (-3) 13)
    clear * - r41370 b41371 b41372 d41361
    omega
  have d41373 : (x (-3) 3 && x (-3) 13).toNat = 0 := by
    have r41374 := hand2 (x (-3) 3) (x (-3) 13)
    have b41375 := hb (x (-3) 13)
    have b41376 := hb (x (-3) 3 && x (-3) 13)
    clear * - r41374 b41375 b41376 d41369
    omega
  have d41377 : (x 0 12).toNat = 0 := by
    have r41378 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e41379 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e41380 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b41381 := hb (x (-3) 3)
    have b41382 := hb (x (-2) 2)
    have b41383 := hb (x (-1) 13)
    have b41384 := hb (x 0 12)
    clear * - r41378 e41379 e41380 b41381 b41382 b41383 b41384 g3 d41352
    omega
  have d41385 : (x (-3) 3).toNat = 0 := by
    have r41386 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e41387 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e41388 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b41389 := hb (x (-3) 3)
    have b41390 := hb (x (-2) 2)
    have b41391 := hb (x (-1) 13)
    have b41392 := hb (x 0 12)
    clear * - r41386 e41387 e41388 b41389 b41390 b41391 b41392 d41377 g3 d41352
    omega
  have d41393 : (x (-3) 3 && x (-3) 12).toNat = 0 := by
    have r41394 := hand1 (x (-3) 3) (x (-3) 12)
    have b41395 := hb (x (-3) 3)
    have b41396 := hb (x (-3) 3 && x (-3) 12)
    clear * - r41394 b41395 b41396 d41385
    omega
  have d41397 : (x (-3) 3 && x (-3) 10).toNat = 0 := by
    have r41398 := hand1 (x (-3) 3) (x (-3) 10)
    have b41399 := hb (x (-3) 3)
    have b41400 := hb (x (-3) 3 && x (-3) 10)
    clear * - r41398 b41399 b41400 d41385
    omega
  have d41401 : (x (-3) 3 && x (-3) 8).toNat = 0 := by
    have r41402 := hand1 (x (-3) 3) (x (-3) 8)
    have b41403 := hb (x (-3) 3)
    have b41404 := hb (x (-3) 3 && x (-3) 8)
    clear * - r41402 b41403 b41404 d41385
    omega
  have d41405 : (x (-2) 2 && x (-2) 12).toNat = 1 := by
    have r41406 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b41407 := hb (x (-5) 5)
    have b41408 := hb (x 0 10)
    have b41409 := hb (x (-1) 1 && x (-1) 11)
    have b41410 := hb (x (-2) 2 && x (-2) 12)
    have b41411 := hb (x (-3) 3 && x (-3) 13)
    have b41412 := hb (x (-4) 4 && x (-4) 14)
    clear * - r41406 b41407 b41408 b41409 b41410 b41411 b41412 g8 g25 d41373 g26 g1
    omega
  have d41413 : (x (-2) 12).toNat = 1 := by
    have r41414 := hand2 (x (-2) 2) (x (-2) 12)
    have b41415 := hb (x (-2) 12)
    have b41416 := hb (x (-2) 2 && x (-2) 12)
    clear * - r41414 b41415 b41416 d41405
    omega
  have d41417 : (x (-4) 2).toNat = 0 := by
    have r41418 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e41419 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
    have e41420 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
    have b41421 := hb (x (-5) 3)
    have b41422 := hb (x (-4) 2)
    have b41423 := hb (x (-3) 13)
    have b41424 := hb (x (-2) 12)
    clear * - r41418 e41419 e41420 b41421 b41422 b41423 b41424 d41413 d41369
    omega
  have d41425 : (x (-2) 13).toNat = 1 := by
    have r41426 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b41427 := hb (x (-4) 2)
    have b41428 := hb (x (-2) 13)
    have b41429 := hb (x (-3) 1 && x (-3) 14)
    clear * - r41426 b41427 b41428 b41429 d41365 d41417
    omega
  have d41430 : (x (-2) 1).toNat = 1 := by
    have r41431 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
    have b41432 := hb (x (-2) 1)
    have b41433 := hb (x (-2) 13)
    clear * - r41431 b41432 b41433 d41425
    omega
  have d41434 : (x (-1) 14).toNat = 0 := by
    have r41435 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b41436 := hb (x (-2) 1)
    have b41437 := hb (x (-1) 14)
    clear * - r41435 b41436 b41437 d41430
    omega
  have d41438 : (x (-1) 6).toNat = 0 := by
    have r41439 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
    have b41440 := hb (x (-1) 6)
    have b41441 := hb (x (-1) 14)
    clear * - r41439 b41440 b41441 d41434
    omega
  have d41442 : (x (-1) 2 && x (-1) 6).toNat = 0 := by
    have r41443 := hand2 (x (-1) 2) (x (-1) 6)
    have b41444 := hb (x (-1) 6)
    have b41445 := hb (x (-1) 2 && x (-1) 6)
    clear * - r41443 b41444 b41445 d41438
    omega
  have d41446 : (x (-1) 2).toNat = 0 := by
    have r41447 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
    have b41448 := hb (x (-1) 2)
    have b41449 := hb (x (-1) 14)
    clear * - r41447 b41448 b41449 d41434
    omega
  have d41450 : (x (-1) 10).toNat = 0 := by
    have r41451 : (x (-1) 10).toNat ≤ (x (-1) 2).toNat := himp _ _ (hp10 (-1))
    have b41452 := hb (x (-1) 2)
    have b41453 := hb (x (-1) 10)
    clear * - r41451 b41452 b41453 d41446
    omega
  have d41454 : (x 1 13).toNat = 1 := by
    have r41455 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b41456 := hb (x (-1) 2)
    have b41457 := hb (x 1 13)
    have b41458 := hb (x 0 1 && x 0 14)
    clear * - r41455 b41456 b41457 b41458 d41332 d41446
    omega
  have d41459 : (x 2 12).toNat = 0 := by
    have r41460 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e41461 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e41462 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b41463 := hb (x (-1) 3)
    have b41464 := hb (x 0 2)
    have b41465 := hb (x 1 13)
    have b41466 := hb (x 2 12)
    clear * - r41460 e41461 e41462 b41463 b41464 b41465 b41466 d41454 g5
    omega
  have d41467 : (x 2 3 && x 2 12).toNat = 0 := by
    have r41468 := hand2 (x 2 3) (x 2 12)
    have b41469 := hb (x 2 12)
    have b41470 := hb (x 2 3 && x 2 12)
    clear * - r41468 b41469 b41470 d41459
    omega
  have d41471 : (x 2 11 && x 2 12).toNat = 0 := by
    have r41472 := hand2 (x 2 11) (x 2 12)
    have b41473 := hb (x 2 12)
    have b41474 := hb (x 2 11 && x 2 12)
    clear * - r41472 b41473 b41474 d41459
    omega
  have d41475 : (x (-1) 12).toNat = 0 := by
    have r41476 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e41477 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e41478 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b41479 := hb (x (-4) 3)
    have b41480 := hb (x (-3) 2)
    have b41481 := hb (x (-2) 13)
    have b41482 := hb (x (-1) 12)
    clear * - r41476 e41477 e41478 b41479 b41480 b41481 b41482 d41425
    omega
  have d41483 : (x (-3) 2).toNat = 0 := by
    have r41484 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e41485 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e41486 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b41487 := hb (x (-4) 3)
    have b41488 := hb (x (-3) 2)
    have b41489 := hb (x (-2) 13)
    have b41490 := hb (x (-1) 12)
    clear * - r41484 e41485 e41486 b41487 b41488 b41489 b41490 d41475 d41425
    omega
  have d41491 : (x (-3) 10).toNat = 0 := by
    have r41492 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
    have b41493 := hb (x (-3) 2)
    have b41494 := hb (x (-3) 10)
    clear * - r41492 b41493 b41494 d41483
    omega
  have d41495 : (x (-4) 3).toNat = 0 := by
    have r41496 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e41497 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e41498 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b41499 := hb (x (-4) 3)
    have b41500 := hb (x (-3) 2)
    have b41501 := hb (x (-2) 13)
    have b41502 := hb (x (-1) 12)
    clear * - r41496 e41497 e41498 b41499 b41500 b41501 b41502 d41475 d41425 d41483
    omega
  have d41503 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
    have r41504 := hand1 (x (-4) 3) (x (-4) 12)
    have b41505 := hb (x (-4) 3)
    have b41506 := hb (x (-4) 3 && x (-4) 12)
    clear * - r41504 b41505 b41506 d41495
    omega
  have d41507 : (x (-4) 11).toNat = 0 := by
    have r41508 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
    have b41509 := hb (x (-4) 3)
    have b41510 := hb (x (-4) 11)
    clear * - r41508 b41509 b41510 d41495
    omega
  have d41511 : (x (-2) 2 && x (-2) 11).toNat = 1 := by
    have r41512 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b41513 := hb (x (-6) 6)
    have b41514 := hb (x 0 9)
    have b41515 := hb (x (-1) 1 && x (-1) 10)
    have b41516 := hb (x (-2) 2 && x (-2) 11)
    have b41517 := hb (x (-3) 3 && x (-3) 12)
    have b41518 := hb (x (-4) 4 && x (-4) 13)
    have b41519 := hb (x (-5) 5 && x (-5) 14)
    clear * - r41512 b41513 b41514 b41515 b41516 b41517 b41518 b41519 g7 g22 d41393 g23 g24 g0
    omega
  have d41520 : (x (-2) 11).toNat = 1 := by
    have r41521 := hand2 (x (-2) 2) (x (-2) 11)
    have b41522 := hb (x (-2) 11)
    have b41523 := hb (x (-2) 2 && x (-2) 11)
    clear * - r41521 b41522 b41523 d41511
    omega
  have d41524 : (x (-2) 3).toNat = 1 := by
    have r41525 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
    have b41526 := hb (x (-2) 3)
    have b41527 := hb (x (-2) 11)
    clear * - r41525 b41526 b41527 d41520
    omega
  have d41528 : (x 1 12).toNat = 0 := by
    have r41529 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e41530 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e41531 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b41532 := hb (x (-2) 3)
    have b41533 := hb (x (-1) 2)
    have b41534 := hb (x 0 13)
    have b41535 := hb (x 1 12)
    clear * - r41529 e41530 e41531 b41532 b41533 b41534 b41535 d41336 d41446 d41524
    omega
  have d41536 : (x 1 12 && x 1 13).toNat = 0 := by
    have r41537 := hand1 (x 1 12) (x 1 13)
    have b41538 := hb (x 1 12)
    have b41539 := hb (x 1 12 && x 1 13)
    clear * - r41537 b41538 b41539 d41528
    omega
  have d41540 : (x 1 4).toNat = 0 := by
    have r41541 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
    have b41542 := hb (x 1 4)
    have b41543 := hb (x 1 12)
    clear * - r41541 b41542 b41543 d41528
    omega
  have d41544 : (x 1 4 && x 1 13).toNat = 0 := by
    have r41545 := hand1 (x 1 4) (x 1 13)
    have b41546 := hb (x 1 4)
    have b41547 := hb (x 1 4 && x 1 13)
    clear * - r41545 b41546 b41547 d41540
    omega
  have d41548 : (x 1 8).toNat = 0 := by
    have r41549 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e41550 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e41551 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e41552 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e41553 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e41554 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e41555 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b41556 := hb (x (-6) 7)
    have b41557 := hb (x (-5) 6)
    have b41558 := hb (x (-4) 5)
    have b41559 := hb (x (-3) 4)
    have b41560 := hb (x (-2) 11)
    have b41561 := hb (x (-1) 10)
    have b41562 := hb (x 0 9)
    have b41563 := hb (x 1 8)
    clear * - r41549 e41550 e41551 e41552 e41553 e41554 e41555 b41556 b41557 b41558 b41559 b41560 b41561 b41562 b41563 g7 d41450 d41520
    omega
  have d41564 : (x (-3) 4).toNat = 0 := by
    have r41565 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e41566 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e41567 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e41568 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e41569 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e41570 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e41571 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b41572 := hb (x (-6) 7)
    have b41573 := hb (x (-5) 6)
    have b41574 := hb (x (-4) 5)
    have b41575 := hb (x (-3) 4)
    have b41576 := hb (x (-2) 11)
    have b41577 := hb (x (-1) 10)
    have b41578 := hb (x 0 9)
    have b41579 := hb (x 1 8)
    clear * - r41565 e41566 e41567 e41568 e41569 e41570 e41571 b41572 b41573 b41574 b41575 b41576 b41577 b41578 b41579 d41548 g7 d41450 d41520
    omega
  have d41580 : (x (-3) 4 && x (-3) 8).toNat = 0 := by
    have r41581 := hand1 (x (-3) 4) (x (-3) 8)
    have b41582 := hb (x (-3) 4)
    have b41583 := hb (x (-3) 4 && x (-3) 8)
    clear * - r41581 b41582 b41583 d41564
    omega
  have d41584 : (x (-4) 5).toNat = 0 := by
    have r41585 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e41586 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e41587 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e41588 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e41589 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e41590 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e41591 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b41592 := hb (x (-6) 7)
    have b41593 := hb (x (-5) 6)
    have b41594 := hb (x (-4) 5)
    have b41595 := hb (x (-3) 4)
    have b41596 := hb (x (-2) 11)
    have b41597 := hb (x (-1) 10)
    have b41598 := hb (x 0 9)
    have b41599 := hb (x 1 8)
    clear * - r41585 e41586 e41587 e41588 e41589 e41590 e41591 b41592 b41593 b41594 b41595 b41596 b41597 b41598 b41599 d41548 g7 d41450 d41520 d41564
    omega
  have d41600 : (x (-4) 5 && x (-4) 9).toNat = 0 := by
    have r41601 := hand1 (x (-4) 5) (x (-4) 9)
    have b41602 := hb (x (-4) 5)
    have b41603 := hb (x (-4) 5 && x (-4) 9)
    clear * - r41601 b41602 b41603 d41584
    omega
  have d41604 : (x (-5) 6).toNat = 0 := by
    have r41605 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e41606 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e41607 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e41608 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e41609 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e41610 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e41611 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b41612 := hb (x (-6) 7)
    have b41613 := hb (x (-5) 6)
    have b41614 := hb (x (-4) 5)
    have b41615 := hb (x (-3) 4)
    have b41616 := hb (x (-2) 11)
    have b41617 := hb (x (-1) 10)
    have b41618 := hb (x 0 9)
    have b41619 := hb (x 1 8)
    clear * - r41605 e41606 e41607 e41608 e41609 e41610 e41611 b41612 b41613 b41614 b41615 b41616 b41617 b41618 b41619 d41548 g7 d41450 d41520 d41564 d41584
    omega
  have d41620 : (x (-5) 6 && x (-5) 10).toNat = 0 := by
    have r41621 := hand1 (x (-5) 6) (x (-5) 10)
    have b41622 := hb (x (-5) 6)
    have b41623 := hb (x (-5) 6 && x (-5) 10)
    clear * - r41621 b41622 b41623 d41604
    omega
  have d41624 : (x (-6) 7).toNat = 0 := by
    have r41625 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e41626 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e41627 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e41628 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e41629 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e41630 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e41631 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b41632 := hb (x (-6) 7)
    have b41633 := hb (x (-5) 6)
    have b41634 := hb (x (-4) 5)
    have b41635 := hb (x (-3) 4)
    have b41636 := hb (x (-2) 11)
    have b41637 := hb (x (-1) 10)
    have b41638 := hb (x 0 9)
    have b41639 := hb (x 1 8)
    clear * - r41625 e41626 e41627 e41628 e41629 e41630 e41631 b41632 b41633 b41634 b41635 b41636 b41637 b41638 b41639 d41548 g7 d41450 d41520 d41564 d41584 d41604
    omega
  have d41640 : (x (-6) 7 && x (-6) 11).toNat = 0 := by
    have r41641 := hand1 (x (-6) 7) (x (-6) 11)
    have b41642 := hb (x (-6) 7)
    have b41643 := hb (x (-6) 7 && x (-6) 11)
    clear * - r41641 b41642 b41643 d41624
    omega
  have r41644 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r41645 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e41646 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
  have e41647 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
  have e41648 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
  have e41649 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
  have e41650 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
  have e41651 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
  have r41652 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e41653 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
  have e41654 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
  have e41655 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
  have e41656 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
  have e41657 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
  have e41658 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
  have r41659 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e41660 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
  have e41661 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
  have e41662 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
  have e41663 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
  have e41664 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
  have e41665 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
  have r41666 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e41667 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
  have e41668 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
  have e41669 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
  have e41670 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
  have e41671 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
  have e41672 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
  have r41673 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e41674 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
  have e41675 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
  have r41676 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e41677 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
  have e41678 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
  have r41679 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r41680 : 1 ≤ (x 13 1).toNat + (x 12 1 && x 12 2).toNat + (x 11 2 && x 11 3).toNat + (x 10 3 && x 10 4).toNat + (x 9 4 && x 9 5).toNat + (x 8 5 && x 8 6).toNat + (x 7 6 && x 7 7).toNat + (x 6 7 && x 6 8).toNat + (x 5 8 && x 5 9).toNat + (x 4 9 && x 4 10).toNat + (x 3 10 && x 3 11).toNat + (x 2 11 && x 2 12).toNat + (x 1 12 && x 1 13).toNat + (x 0 13 && x 0 14).toNat + (x (-1) 14).toNat := by have q := hcov1 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r41681 : 1 ≤ (x 1 4).toNat + (x 0 1 && x 0 5).toNat + (x (-1) 2 && x (-1) 6).toNat + (x (-2) 3 && x (-2) 7).toNat + (x (-3) 4 && x (-3) 8).toNat + (x (-4) 5 && x (-4) 9).toNat + (x (-5) 6 && x (-5) 10).toNat + (x (-6) 7 && x (-6) 11).toNat + (x (-7) 8 && x (-7) 12).toNat + (x (-8) 9 && x (-8) 13).toNat + (x (-9) 10 && x (-9) 14).toNat + (x (-10) 11).toNat := by have q := hcov4 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e41682 : (x 0 1 && x 0 5).toNat = (x 0 5).toNat := handr _ _ (fun h => hp13 0 (hp5 0 (h)))
  have e41683 : (x (-9) 10 && x (-9) 14).toNat = (x (-9) 10).toNat := handl _ _ (fun h => hp2 (-9) (hp10 (-9) (h)))
  have r41684 : 1 ≤ (x 0 5).toNat + (x (-1) 1 && x (-1) 6).toNat + (x (-2) 2 && x (-2) 7).toNat + (x (-3) 3 && x (-3) 8).toNat + (x (-4) 4 && x (-4) 9).toNat + (x (-5) 5 && x (-5) 10).toNat + (x (-6) 6 && x (-6) 11).toNat + (x (-7) 7 && x (-7) 12).toNat + (x (-8) 8 && x (-8) 13).toNat + (x (-9) 9 && x (-9) 14).toNat + (x (-10) 10).toNat := by have q := hcov5 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r41685 : 1 ≤ (x 0 7).toNat + (x (-1) 1 && x (-1) 8).toNat + (x (-2) 2 && x (-2) 9).toNat + (x (-3) 3 && x (-3) 10).toNat + (x (-4) 4 && x (-4) 11).toNat + (x (-5) 5 && x (-5) 12).toNat + (x (-6) 6 && x (-6) 13).toNat + (x (-7) 7 && x (-7) 14).toNat + (x (-8) 8).toNat := by have q := hcov7 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r41686 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r41687 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r41688 : 1 ≤ (x (-7) 10).toNat + (x (-8) 1 && x (-8) 11).toNat + (x (-9) 2 && x (-9) 12).toNat + (x (-10) 3 && x (-10) 13).toNat + (x (-11) 4 && x (-11) 14).toNat + (x (-12) 5).toNat := by have q := hcov10 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r41689 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
  have r41690 : (x (-8) 13).toNat ≤ (x (-8) 1).toNat := himp _ _ (hp13 (-8))
  have r41691 : (x (-7) 6).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp6 (-7))
  have r41692 : (x (-7) 10).toNat ≤ (x (-7) 2).toNat := himp _ _ (hp10 (-7))
  have r41693 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
  have r41694 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
  have r41695 := hand2 (x 12 1) (x 12 2)
  have r41696 := hand2 (x 11 2) (x 11 3)
  have r41697 := hand2 (x 10 3) (x 10 4)
  have r41698 := hand2 (x 9 4) (x 9 5)
  have r41699 := hand2 (x 8 5) (x 8 6)
  have r41700 := hand2 (x 7 6) (x 7 7)
  have r41701 := hand2 (x 6 7) (x 6 8)
  have r41702 := hand1 (x 5 8) (x 5 9)
  have r41703 := hand1 (x 4 9) (x 4 10)
  have r41704 := hand1 (x 3 10) (x 3 11)
  have r41705 := hand2 (x (-2) 3) (x (-2) 7)
  have r41706 := hand2 (x (-7) 8) (x (-7) 12)
  have r41707 := hand1 (x (-8) 9) (x (-8) 13)
  have r41708 := hand2 (x (-2) 2) (x (-2) 7)
  have r41709 := hand2 (x (-8) 8) (x (-8) 13)
  have r41710 := hand1 (x (-9) 9) (x (-9) 14)
  have r41711 := hand2 (x (-2) 2) (x (-2) 9)
  have r41712 := hand1 (x (-5) 4) (x (-5) 13)
  have r41713 := hand1 (x (-6) 5) (x (-6) 14)
  have r41714 := hand2 (x 4 1) (x 4 10)
  have r41715 := hand2 (x 3 2) (x 3 11)
  have r41716 := hand2 (x (-8) 1) (x (-8) 11)
  have r41717 := hand1 (x (-9) 2) (x (-9) 12)
  have r41718 := hand1 (x (-10) 3) (x (-10) 13)
  have r41719 := hand1 (x (-11) 4) (x (-11) 14)
  linarith only [r41644, r41645, e41646, e41647, e41648, e41649, e41650, e41651, r41652, e41653, e41654, e41655, e41656, e41657, e41658, r41659, e41660, e41661, e41662, e41663, e41664, e41665, r41666, e41667, e41668, e41669, e41670, e41671, e41672, r41673, e41674, e41675, r41676, e41677, e41678, r41679, r41680, r41681, e41682, e41683, r41684, r41685, r41686, r41687, r41688, r41689, r41690, r41691, r41692, r41693, r41694, r41695, r41696, r41697, r41698, r41699, r41700, r41701, r41702, r41703, r41704, r41705, r41706, r41707, r41708, r41709, r41710, r41711, r41712, r41713, r41714, r41715, r41716, r41717, r41718, r41719, d41507, d41491, d41438, g2, d41434, d41344, g6, g9, d41540, d41454, d41459, d41471, d41536, d41340, d41442, d41580, d41600, d41620, d41640, g10, d41401, g11, g12, g13, g14, g15, d41397, g16, g17, g18, g19, g20, g21, d41503, d41467, d41544, d41348]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a010100000_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-6) 7).toNat = 0)
    (g1 : (x (-5) 6).toNat = 0)
    (g2 : (x (-5) 11).toNat = 0)
    (g3 : (x (-4) 5).toNat = 0)
    (g4 : (x (-4) 10).toNat = 0)
    (g5 : (x (-4) 11).toNat = 0)
    (g6 : (x (-3) 4).toNat = 0)
    (g7 : (x (-3) 9).toNat = 0)
    (g8 : (x (-3) 10).toNat = 0)
    (g9 : (x (-3) 11).toNat = 0)
    (g10 : (x (-2) 3).toNat = 1)
    (g11 : (x (-2) 10).toNat = 0)
    (g12 : (x (-1) 2).toNat = 0)
    (g13 : (x (-1) 4).toNat = 0)
    (g14 : (x (-1) 6).toNat = 0)
    (g15 : (x (-1) 9).toNat = 0)
    (g16 : (x 0 1).toNat = 1)
    (g17 : (x 0 3).toNat = 0)
    (g18 : (x 0 5).toNat = 0)
    (g19 : (x 0 7).toNat = 0)
    (g20 : (x 0 8).toNat = 1)
    (g21 : (x 0 11).toNat = 0)
    (g22 : (x 1 2).toNat = 0)
    (g23 : (x 1 4).toNat = 0)
    (g24 : (x 1 6).toNat = 0)
    (g25 : (x 1 7).toNat = 0)
    (g26 : (x 1 10).toNat = 0)
    (g27 : (x 2 1).toNat = 1)
    (g28 : (x 3 2).toNat = 0)
    (g29 : (x 3 10).toNat = 0)
    (g30 : (x 0 1 && x 0 3).toNat = 0)
    (g31 : (x (-1) 2 && x (-1) 4).toNat = 0)
    (g32 : (x (-3) 4 && x (-3) 6).toNat = 0)
    (g33 : (x (-4) 5 && x (-4) 7).toNat = 0)
    (g34 : (x (-5) 6 && x (-5) 8).toNat = 0)
    (g35 : (x (-6) 7 && x (-6) 9).toNat = 0)
    (g36 : (x (-1) 1 && x (-1) 6).toNat = 0)
    (g37 : (x (-3) 3 && x (-3) 8).toNat = 0)
    (g38 : (x (-4) 4 && x (-4) 9).toNat = 0)
    (g39 : (x (-5) 5 && x (-5) 10).toNat = 0)
    (g40 : (x (-6) 6 && x (-6) 11).toNat = 0)
    (g41 : (x (-7) 7 && x (-7) 12).toNat = 0)
    (g42 : (x 1 2 && x 1 7).toNat = 0)
    (g43 : (x 0 3 && x 0 8).toNat = 0)
    (g44 : (x (-1) 4 && x (-1) 9).toNat = 0)
    (g45 : (x (-2) 5 && x (-2) 10).toNat = 0)
    (g46 : (x (-3) 6 && x (-3) 11).toNat = 0)
    (g47 : (x 1 5 && x 1 10).toNat = 0)
    (g48 : (x 0 6 && x 0 11).toNat = 0)
    (g49 : (x (-1) 7 && x (-1) 12).toNat = 0)
    (g50 : (x (-3) 9 && x (-3) 14).toNat = 0)
    (g51 : (x 0 1 && x 0 7).toNat = 0)
    (g52 : (x (-1) 2 && x (-1) 8).toNat = 0)
    (g53 : (x (-3) 4 && x (-3) 10).toNat = 0)
    (g54 : (x (-4) 5 && x (-4) 11).toNat = 0)
    (g55 : (x (-5) 6 && x (-5) 12).toNat = 0)
    (g56 : (x (-6) 7 && x (-6) 13).toNat = 0)
    (g57 : (x (-1) 1 && x (-1) 8).toNat = 0)
    (g58 : (x (-3) 3 && x (-3) 10).toNat = 0)
    (g59 : (x (-4) 4 && x (-4) 11).toNat = 0)
    (g60 : (x (-5) 5 && x (-5) 12).toNat = 0)
    (g61 : (x (-6) 6 && x (-6) 13).toNat = 0)
    (g62 : (x (-7) 7 && x (-7) 14).toNat = 0)
    (g63 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g64 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g65 : (x (-4) 3 && x (-4) 12).toNat = 0)
    (g66 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g67 : (x (-4) 2 && x (-4) 12).toNat = 0)
    (g68 : (x (-5) 3 && x (-5) 13).toNat = 0)
    (g69 : (x 1 2 && x 1 12).toNat = 0)
    (g70 : (x 0 3 && x 0 13).toNat = 0)
    (g71 : (x (-1) 4 && x (-1) 14).toNat = 0)
    (g72 : (x 3 2 && x 3 13).toNat = 0)
    (g73 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  cases h42361 : x (-1) 8
  · have f42362 : (x (-1) 8).toNat = 0 := by rw [h42361]; rfl
    cases h42363 : x 1 11
    · have f42364 : (x 1 11).toNat = 0 := by rw [h42363]; rfl
      cases h42365 : x (-2) 5
      · have f42366 : (x (-2) 5).toNat = 0 := by rw [h42365]; rfl
        have d42367 : (x (-2) 3 && x (-2) 5).toNat = 0 := by
          have r42368 := hand2 (x (-2) 3) (x (-2) 5)
          have b42369 := hb (x (-2) 5)
          have b42370 := hb (x (-2) 3 && x (-2) 5)
          clear * - r42368 b42369 b42370 f42366
          omega
        have d42371 : (x 2 1 && x 2 11).toNat = 1 := by
          have r42372 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b42373 := hb (x (-2) 5)
          have b42374 := hb (x 3 10)
          have b42375 := hb (x 2 1 && x 2 11)
          have b42376 := hb (x 1 2 && x 1 12)
          have b42377 := hb (x 0 3 && x 0 13)
          have b42378 := hb (x (-1) 4 && x (-1) 14)
          clear * - r42372 b42373 b42374 b42375 b42376 b42377 b42378 g29 g69 g70 g71 f42366
          omega
        have d42379 : (x 2 11).toNat = 1 := by
          have r42380 := hand2 (x 2 1) (x 2 11)
          have b42381 := hb (x 2 11)
          have b42382 := hb (x 2 1 && x 2 11)
          clear * - r42380 b42381 b42382 d42371
          omega
        have d42383 : (x 5 8).toNat = 0 := by
          have r42384 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e42385 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
          have e42386 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
          have e42387 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
          have e42388 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
          have e42389 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
          have e42390 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
          have b42391 := hb (x (-2) 7)
          have b42392 := hb (x (-1) 6)
          have b42393 := hb (x 0 5)
          have b42394 := hb (x 1 4)
          have b42395 := hb (x 2 11)
          have b42396 := hb (x 3 10)
          have b42397 := hb (x 4 9)
          have b42398 := hb (x 5 8)
          clear * - r42384 e42385 e42386 e42387 e42388 e42389 e42390 b42391 b42392 b42393 b42394 b42395 b42396 b42397 b42398 g29 d42379 g23 g18 g14
          omega
        have d42399 : (x 4 9).toNat = 0 := by
          have r42400 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e42401 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
          have e42402 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
          have e42403 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
          have e42404 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
          have e42405 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
          have e42406 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
          have b42407 := hb (x (-2) 7)
          have b42408 := hb (x (-1) 6)
          have b42409 := hb (x 0 5)
          have b42410 := hb (x 1 4)
          have b42411 := hb (x 2 11)
          have b42412 := hb (x 3 10)
          have b42413 := hb (x 4 9)
          have b42414 := hb (x 5 8)
          clear * - r42400 e42401 e42402 e42403 e42404 e42405 e42406 b42407 b42408 b42409 b42410 b42411 b42412 b42413 b42414 d42383 g29 d42379 g23 g18 g14
          omega
        have d42415 : (x (-2) 7).toNat = 0 := by
          have r42416 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e42417 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
          have e42418 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
          have e42419 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
          have e42420 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
          have e42421 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
          have e42422 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
          have b42423 := hb (x (-2) 7)
          have b42424 := hb (x (-1) 6)
          have b42425 := hb (x 0 5)
          have b42426 := hb (x 1 4)
          have b42427 := hb (x 2 11)
          have b42428 := hb (x 3 10)
          have b42429 := hb (x 4 9)
          have b42430 := hb (x 5 8)
          clear * - r42416 e42417 e42418 e42419 e42420 e42421 e42422 b42423 b42424 b42425 b42426 b42427 b42428 b42429 b42430 d42383 d42399 g29 d42379 g23 g18 g14
          omega
        have d42431 : (x (-2) 2 && x (-2) 7).toNat = 0 := by
          have r42432 := hand2 (x (-2) 2) (x (-2) 7)
          have b42433 := hb (x (-2) 7)
          have b42434 := hb (x (-2) 2 && x (-2) 7)
          clear * - r42432 b42433 b42434 d42415
          omega
        have r42435 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r42436 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e42437 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
        have e42438 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
        have e42439 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
        have e42440 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
        have e42441 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
        have e42442 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
        have r42443 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e42444 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e42445 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e42446 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e42447 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e42448 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e42449 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have r42450 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e42451 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
        have e42452 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
        have r42453 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r42454 : 1 ≤ (x 1 2).toNat + (x 0 1 && x 0 3).toNat + (x (-1) 2 && x (-1) 4).toNat + (x (-2) 3 && x (-2) 5).toNat + (x (-3) 4 && x (-3) 6).toNat + (x (-4) 5 && x (-4) 7).toNat + (x (-5) 6 && x (-5) 8).toNat + (x (-6) 7 && x (-6) 9).toNat + (x (-7) 8 && x (-7) 10).toNat + (x (-8) 9 && x (-8) 11).toNat + (x (-9) 10 && x (-9) 12).toNat + (x (-10) 11 && x (-10) 13).toNat + (x (-11) 12 && x (-11) 14).toNat + (x (-12) 13).toNat := by have q := hcov2 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r42455 : 1 ≤ (x 0 5).toNat + (x (-1) 1 && x (-1) 6).toNat + (x (-2) 2 && x (-2) 7).toNat + (x (-3) 3 && x (-3) 8).toNat + (x (-4) 4 && x (-4) 9).toNat + (x (-5) 5 && x (-5) 10).toNat + (x (-6) 6 && x (-6) 11).toNat + (x (-7) 7 && x (-7) 12).toNat + (x (-8) 8 && x (-8) 13).toNat + (x (-9) 9 && x (-9) 14).toNat + (x (-10) 10).toNat := by have q := hcov5 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r42456 : 1 ≤ (x 1 6).toNat + (x 0 1 && x 0 7).toNat + (x (-1) 2 && x (-1) 8).toNat + (x (-2) 3 && x (-2) 9).toNat + (x (-3) 4 && x (-3) 10).toNat + (x (-4) 5 && x (-4) 11).toNat + (x (-5) 6 && x (-5) 12).toNat + (x (-6) 7 && x (-6) 13).toNat + (x (-7) 8 && x (-7) 14).toNat + (x (-8) 9).toNat := by have q := hcov6 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r42457 : 1 ≤ (x 0 7).toNat + (x (-1) 1 && x (-1) 8).toNat + (x (-2) 2 && x (-2) 9).toNat + (x (-3) 3 && x (-3) 10).toNat + (x (-4) 4 && x (-4) 11).toNat + (x (-5) 5 && x (-5) 12).toNat + (x (-6) 6 && x (-6) 13).toNat + (x (-7) 7 && x (-7) 14).toNat + (x (-8) 8).toNat := by have q := hcov7 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r42458 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r42459 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
        have r42460 : (x (-8) 13).toNat ≤ (x (-8) 1).toNat := himp _ _ (hp13 (-8))
        have r42461 : (x (-7) 6).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp6 (-7))
        have r42462 : (x (-7) 10).toNat ≤ (x (-7) 2).toNat := himp _ _ (hp10 (-7))
        have r42463 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
        have r42464 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
        have r42465 := hand2 (x (-7) 8) (x (-7) 10)
        have r42466 := hand2 (x (-8) 9) (x (-8) 11)
        have r42467 := hand1 (x (-9) 10) (x (-9) 12)
        have r42468 := hand1 (x (-10) 11) (x (-10) 13)
        have r42469 := hand1 (x (-11) 12) (x (-11) 14)
        have r42470 := hand2 (x (-8) 8) (x (-8) 13)
        have r42471 := hand1 (x (-9) 9) (x (-9) 14)
        have r42472 := hand2 (x (-2) 3) (x (-2) 9)
        have r42473 := hand1 (x (-7) 8) (x (-7) 14)
        have r42474 := hand2 (x (-2) 2) (x (-2) 9)
        have r42475 := hand1 (x (-5) 4) (x (-5) 13)
        have r42476 := hand1 (x (-6) 5) (x (-6) 14)
        linarith only [r42435, r42436, e42437, e42438, e42439, e42440, e42441, e42442, r42443, e42444, e42445, e42446, e42447, e42448, e42449, r42450, e42451, e42452, r42453, r42454, r42455, r42456, r42457, r42458, r42459, r42460, r42461, r42462, r42463, r42464, r42465, r42466, r42467, r42468, r42469, r42470, r42471, r42472, r42473, r42474, r42475, r42476, g0, g1, g3, g5, g6, g8, g10, g12, f42362, g15, g16, g18, g19, g22, g24, g30, g31, d42367, g32, g33, g34, g35, g36, d42431, g37, g38, g39, g40, g41, g51, g52, g53, g54, g55, g56, g57, g58, g59, g60, g61, g62, g63, g64, g65]
      · have f42562 : (x (-2) 5).toNat = 1 := by rw [h42365]; rfl
        have d42563 : (x 3 8).toNat = 0 := by
          have r42564 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e42565 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e42566 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e42567 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e42568 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e42569 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e42570 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b42571 := hb (x (-4) 7)
          have b42572 := hb (x (-3) 6)
          have b42573 := hb (x (-2) 5)
          have b42574 := hb (x (-1) 4)
          have b42575 := hb (x 0 11)
          have b42576 := hb (x 1 10)
          have b42577 := hb (x 2 9)
          have b42578 := hb (x 3 8)
          clear * - r42564 e42565 e42566 e42567 e42568 e42569 e42570 b42571 b42572 b42573 b42574 b42575 b42576 b42577 b42578 g26 g21 g13 f42562
          omega
        have d42579 : (x 3 3 && x 3 8).toNat = 0 := by
          have r42580 := hand2 (x 3 3) (x 3 8)
          have b42581 := hb (x 3 8)
          have b42582 := hb (x 3 3 && x 3 8)
          clear * - r42580 b42581 b42582 d42563
          omega
        have d42583 : (x 2 9).toNat = 0 := by
          have r42584 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e42585 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e42586 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e42587 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e42588 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e42589 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e42590 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b42591 := hb (x (-4) 7)
          have b42592 := hb (x (-3) 6)
          have b42593 := hb (x (-2) 5)
          have b42594 := hb (x (-1) 4)
          have b42595 := hb (x 0 11)
          have b42596 := hb (x 1 10)
          have b42597 := hb (x 2 9)
          have b42598 := hb (x 3 8)
          clear * - r42584 e42585 e42586 e42587 e42588 e42589 e42590 b42591 b42592 b42593 b42594 b42595 b42596 b42597 b42598 d42563 g26 g21 g13 f42562
          omega
        have d42599 : (x 2 4 && x 2 9).toNat = 0 := by
          have r42600 := hand2 (x 2 4) (x 2 9)
          have b42601 := hb (x 2 9)
          have b42602 := hb (x 2 4 && x 2 9)
          clear * - r42600 b42601 b42602 d42583
          omega
        have d42603 : (x (-3) 6).toNat = 0 := by
          have r42604 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e42605 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e42606 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e42607 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e42608 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e42609 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e42610 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b42611 := hb (x (-4) 7)
          have b42612 := hb (x (-3) 6)
          have b42613 := hb (x (-2) 5)
          have b42614 := hb (x (-1) 4)
          have b42615 := hb (x 0 11)
          have b42616 := hb (x 1 10)
          have b42617 := hb (x 2 9)
          have b42618 := hb (x 3 8)
          clear * - r42604 e42605 e42606 e42607 e42608 e42609 e42610 b42611 b42612 b42613 b42614 b42615 b42616 b42617 b42618 d42563 d42583 g26 g21 g13 f42562
          omega
        have d42619 : (x (-4) 7).toNat = 0 := by
          have r42620 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e42621 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e42622 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e42623 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e42624 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e42625 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e42626 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b42627 := hb (x (-4) 7)
          have b42628 := hb (x (-3) 6)
          have b42629 := hb (x (-2) 5)
          have b42630 := hb (x (-1) 4)
          have b42631 := hb (x 0 11)
          have b42632 := hb (x 1 10)
          have b42633 := hb (x 2 9)
          have b42634 := hb (x 3 8)
          clear * - r42620 e42621 e42622 e42623 e42624 e42625 e42626 b42627 b42628 b42629 b42630 b42631 b42632 b42633 b42634 d42563 d42583 g26 g21 g13 f42562 d42603
          omega
        have d42635 : (x (-4) 7 && x (-4) 12).toNat = 0 := by
          have r42636 := hand1 (x (-4) 7) (x (-4) 12)
          have b42637 := hb (x (-4) 7)
          have b42638 := hb (x (-4) 7 && x (-4) 12)
          clear * - r42636 b42637 b42638 d42619
          omega
        have r42639 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r42640 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r42641 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r42642 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e42643 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
        have e42644 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
        have e42645 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
        have e42646 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
        have e42647 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
        have e42648 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
        have r42649 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e42650 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
        have e42651 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
        have e42652 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
        have e42653 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
        have e42654 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
        have e42655 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
        have r42656 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e42657 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e42658 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e42659 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e42660 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e42661 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e42662 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have r42663 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e42664 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
        have e42665 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
        have e42666 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
        have e42667 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
        have e42668 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
        have e42669 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
        have r42670 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r42671 : 1 ≤ (x 3 5).toNat + (x 2 1 && x 2 6).toNat + (x 1 2 && x 1 7).toNat + (x 0 3 && x 0 8).toNat + (x (-1) 4 && x (-1) 9).toNat + (x (-2) 5 && x (-2) 10).toNat + (x (-3) 6 && x (-3) 11).toNat + (x (-4) 7 && x (-4) 12).toNat + (x (-5) 8 && x (-5) 13).toNat + (x (-6) 9 && x (-6) 14).toNat + (x (-7) 10).toNat := by have q := hcov5 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r42672 : 1 ≤ (x 6 5).toNat + (x 5 1 && x 5 6).toNat + (x 4 2 && x 4 7).toNat + (x 3 3 && x 3 8).toNat + (x 2 4 && x 2 9).toNat + (x 1 5 && x 1 10).toNat + (x 0 6 && x 0 11).toNat + (x (-1) 7 && x (-1) 12).toNat + (x (-2) 8 && x (-2) 13).toNat + (x (-3) 9 && x (-3) 14).toNat + (x (-4) 10).toNat := by have q := hcov5 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r42673 : 1 ≤ (x 1 6).toNat + (x 0 1 && x 0 7).toNat + (x (-1) 2 && x (-1) 8).toNat + (x (-2) 3 && x (-2) 9).toNat + (x (-3) 4 && x (-3) 10).toNat + (x (-4) 5 && x (-4) 11).toNat + (x (-5) 6 && x (-5) 12).toNat + (x (-6) 7 && x (-6) 13).toNat + (x (-7) 8 && x (-7) 14).toNat + (x (-8) 9).toNat := by have q := hcov6 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r42674 : 1 ≤ (x 0 7).toNat + (x (-1) 1 && x (-1) 8).toNat + (x (-2) 2 && x (-2) 9).toNat + (x (-3) 3 && x (-3) 10).toNat + (x (-4) 4 && x (-4) 11).toNat + (x (-5) 5 && x (-5) 12).toNat + (x (-6) 6 && x (-6) 13).toNat + (x (-7) 7 && x (-7) 14).toNat + (x (-8) 8).toNat := by have q := hcov7 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r42675 : 1 ≤ (x (-8) 9).toNat + (x (-9) 1 && x (-9) 10).toNat + (x (-10) 2 && x (-10) 11).toNat + (x (-11) 3 && x (-11) 12).toNat + (x (-12) 4 && x (-12) 13).toNat + (x (-13) 5 && x (-13) 14).toNat + (x (-14) 6).toNat := by have q := hcov9 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r42676 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r42677 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r42678 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := by have q := hcov11 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r42679 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r42680 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r42681 : (x (-8) 9).toNat ≤ (x (-8) 1).toNat := himp _ _ (hp9 (-8))
        have r42682 : (x (-7) 2).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp2 (-7))
        have r42683 := hand2 (x 2 1) (x 2 6)
        have r42684 := hand1 (x (-5) 8) (x (-5) 13)
        have r42685 := hand1 (x (-6) 9) (x (-6) 14)
        have r42686 := hand2 (x 5 1) (x 5 6)
        have r42687 := hand2 (x 4 2) (x 4 7)
        have r42688 := hand1 (x (-2) 8) (x (-2) 13)
        have r42689 := hand2 (x (-2) 3) (x (-2) 9)
        have r42690 := hand1 (x (-7) 8) (x (-7) 14)
        have r42691 := hand2 (x (-2) 2) (x (-2) 9)
        have r42692 := hand2 (x (-9) 1) (x (-9) 10)
        have r42693 := hand2 (x (-10) 2) (x (-10) 11)
        have r42694 := hand2 (x (-11) 3) (x (-11) 12)
        have r42695 := hand2 (x (-12) 4) (x (-12) 13)
        have r42696 := hand2 (x (-13) 5) (x (-13) 14)
        have r42697 := hand1 (x (-5) 4) (x (-5) 13)
        have r42698 := hand1 (x (-6) 5) (x (-6) 14)
        have r42699 := hand1 (x (-6) 4) (x (-6) 14)
        have r42700 := hand2 (x (-9) 1) (x (-9) 12)
        have r42701 := hand2 (x (-10) 2) (x (-10) 13)
        have r42702 := hand2 (x (-11) 3) (x (-11) 14)
        have r42703 := hand1 (x 7 1) (x 7 12)
        have r42704 := hand1 (x 6 2) (x 6 13)
        have r42705 := hand1 (x 5 3) (x 5 14)
        have r42706 := hand2 (x (-6) 1) (x (-6) 14)
        linarith only [r42639, r42640, r42641, r42642, e42643, e42644, e42645, e42646, e42647, e42648, r42649, e42650, e42651, e42652, e42653, e42654, e42655, r42656, e42657, e42658, e42659, e42660, e42661, e42662, r42663, e42664, e42665, e42666, e42667, e42668, e42669, r42670, r42671, r42672, r42673, r42674, r42675, r42676, r42677, r42678, r42679, r42680, r42681, r42682, r42683, r42684, r42685, r42686, r42687, r42688, r42689, r42690, r42691, r42692, r42693, r42694, r42695, r42696, r42697, r42698, r42699, r42700, r42701, r42702, r42703, r42704, r42705, r42706, g0, g1, g2, g3, d42619, g4, g5, g6, d42603, g7, g8, g9, g10, f42562, g11, g12, g13, f42362, g15, g16, g17, g19, g20, g22, g24, g25, g27, g42, g43, g44, g45, g46, d42635, d42579, d42599, g47, g48, g49, g50, g51, g52, g53, g54, g55, g56, g57, g58, g59, g60, g61, g62, g63, g64, g65, g66, g67, g68]
    · have f42840 : (x 1 11).toNat = 1 := by rw [h42363]; rfl
      have d42841 : (x 1 3).toNat = 1 := by
        have r42842 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
        have b42843 := hb (x 1 3)
        have b42844 := hb (x 1 11)
        clear * - r42842 b42843 b42844 f42840
        omega
      have d42845 : (x 4 12).toNat = 0 := by
        have r42846 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e42847 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e42848 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b42849 := hb (x 1 3)
        have b42850 := hb (x 2 2)
        have b42851 := hb (x 3 13)
        have b42852 := hb (x 4 12)
        clear * - r42846 e42847 e42848 b42849 b42850 b42851 b42852 d42841
        omega
      have d42853 : (x 4 1 && x 4 12).toNat = 0 := by
        have r42854 := hand2 (x 4 1) (x 4 12)
        have b42855 := hb (x 4 12)
        have b42856 := hb (x 4 1 && x 4 12)
        clear * - r42854 b42855 b42856 d42845
        omega
      have d42857 : (x 4 4).toNat = 0 := by
        have r42858 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
        have b42859 := hb (x 4 4)
        have b42860 := hb (x 4 12)
        clear * - r42858 b42859 b42860 d42845
        omega
      have d42861 : (x 3 13).toNat = 0 := by
        have r42862 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e42863 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e42864 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b42865 := hb (x 1 3)
        have b42866 := hb (x 2 2)
        have b42867 := hb (x 3 13)
        have b42868 := hb (x 4 12)
        clear * - r42862 e42863 e42864 b42865 b42866 b42867 b42868 d42845 d42841
        omega
      have d42869 : (x 2 2).toNat = 0 := by
        have r42870 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e42871 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e42872 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b42873 := hb (x 1 3)
        have b42874 := hb (x 2 2)
        have b42875 := hb (x 3 13)
        have b42876 := hb (x 4 12)
        clear * - r42870 e42871 e42872 b42873 b42874 b42875 b42876 d42845 d42861 d42841
        omega
      have d42877 : (x 4 13).toNat = 1 := by
        have r42878 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b42879 := hb (x 2 2)
        have b42880 := hb (x 4 13)
        have b42881 := hb (x 3 1 && x 3 14)
        clear * - r42878 b42879 b42880 b42881 g73 d42869
        omega
      have d42882 : (x 4 1).toNat = 1 := by
        have r42883 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
        have b42884 := hb (x 4 1)
        have b42885 := hb (x 4 13)
        clear * - r42883 b42884 b42885 d42877
        omega
      have d42886 : (x 5 14).toNat = 0 := by
        have r42887 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b42888 := hb (x 4 1)
        have b42889 := hb (x 5 14)
        clear * - r42887 b42888 b42889 d42882
        omega
      have d42890 : (x 5 3 && x 5 14).toNat = 0 := by
        have r42891 := hand2 (x 5 3) (x 5 14)
        have b42892 := hb (x 5 14)
        have b42893 := hb (x 5 3 && x 5 14)
        clear * - r42891 b42892 b42893 d42886
        omega
      have d42894 : (x 5 2).toNat = 0 := by
        have r42895 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
        have b42896 := hb (x 5 2)
        have b42897 := hb (x 5 14)
        clear * - r42895 b42896 b42897 d42886
        omega
      have d42898 : (x 5 12).toNat = 0 := by
        have r42899 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e42900 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e42901 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b42902 := hb (x 2 3)
        have b42903 := hb (x 3 2)
        have b42904 := hb (x 4 13)
        have b42905 := hb (x 5 12)
        clear * - r42899 e42900 e42901 b42902 b42903 b42904 b42905 d42877 g28
        omega
      have d42906 : (x 5 4).toNat = 0 := by
        have r42907 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
        have b42908 := hb (x 5 4)
        have b42909 := hb (x 5 12)
        clear * - r42907 b42908 b42909 d42898
        omega
      have d42910 : (x 2 3).toNat = 0 := by
        have r42911 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e42912 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e42913 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b42914 := hb (x 2 3)
        have b42915 := hb (x 3 2)
        have b42916 := hb (x 4 13)
        have b42917 := hb (x 5 12)
        clear * - r42911 e42912 e42913 b42914 b42915 b42916 b42917 d42898 d42877 g28
        omega
      have d42918 : (x 2 3 && x 2 14).toNat = 0 := by
        have r42919 := hand1 (x 2 3) (x 2 14)
        have b42920 := hb (x 2 3)
        have b42921 := hb (x 2 3 && x 2 14)
        clear * - r42919 b42920 b42921 d42910
        omega
      have d42922 : (x 5 11).toNat = 1 := by
        have r42923 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b42924 := hb (x 1 4)
        have b42925 := hb (x 5 11)
        have b42926 := hb (x 4 1 && x 4 12)
        have b42927 := hb (x 3 2 && x 3 13)
        have b42928 := hb (x 2 3 && x 2 14)
        clear * - r42923 b42924 b42925 b42926 b42927 b42928 d42853 g72 d42918 g23
        omega
      have d42929 : (x 5 3).toNat = 1 := by
        have r42930 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
        have b42931 := hb (x 5 3)
        have b42932 := hb (x 5 11)
        clear * - r42930 b42931 b42932 d42922
        omega
      have d42933 : (x 8 12).toNat = 0 := by
        have r42934 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e42935 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e42936 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have b42937 := hb (x 5 3)
        have b42938 := hb (x 6 2)
        have b42939 := hb (x 7 13)
        have b42940 := hb (x 8 12)
        clear * - r42934 e42935 e42936 b42937 b42938 b42939 b42940 d42929
        omega
      have d42941 : (x 8 1 && x 8 12).toNat = 0 := by
        have r42942 := hand2 (x 8 1) (x 8 12)
        have b42943 := hb (x 8 12)
        have b42944 := hb (x 8 1 && x 8 12)
        clear * - r42942 b42943 b42944 d42933
        omega
      have d42945 : (x 8 4).toNat = 0 := by
        have r42946 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
        have b42947 := hb (x 8 4)
        have b42948 := hb (x 8 12)
        clear * - r42946 b42947 b42948 d42933
        omega
      have d42949 : (x 7 13).toNat = 0 := by
        have r42950 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e42951 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e42952 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have b42953 := hb (x 5 3)
        have b42954 := hb (x 6 2)
        have b42955 := hb (x 7 13)
        have b42956 := hb (x 8 12)
        clear * - r42950 e42951 e42952 b42953 b42954 b42955 b42956 d42933 d42929
        omega
      have d42957 : (x 7 2 && x 7 13).toNat = 0 := by
        have r42958 := hand2 (x 7 2) (x 7 13)
        have b42959 := hb (x 7 13)
        have b42960 := hb (x 7 2 && x 7 13)
        clear * - r42958 b42959 b42960 d42949
        omega
      have d42961 : (x 6 1 && x 6 14).toNat = 1 := by
        have r42962 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b42963 := hb (x 5 2)
        have b42964 := hb (x 7 13)
        have b42965 := hb (x 6 1 && x 6 14)
        clear * - r42962 b42963 b42964 b42965 d42949 d42894
        omega
      have d42966 : (x 6 1).toNat = 1 := by
        have r42967 := hand1 (x 6 1) (x 6 14)
        have b42968 := hb (x 6 1)
        have b42969 := hb (x 6 1 && x 6 14)
        clear * - r42967 b42968 b42969 d42961
        omega
      have d42970 : (x 7 14).toNat = 0 := by
        have r42971 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b42972 := hb (x 6 1)
        have b42973 := hb (x 7 14)
        clear * - r42971 b42972 b42973 d42966
        omega
      have d42974 : (x 7 1 && x 7 14).toNat = 0 := by
        have r42975 := hand2 (x 7 1) (x 7 14)
        have b42976 := hb (x 7 14)
        have b42977 := hb (x 7 1 && x 7 14)
        clear * - r42975 b42976 b42977 d42970
        omega
      have d42978 : (x 7 2).toNat = 0 := by
        have r42979 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
        have b42980 := hb (x 7 2)
        have b42981 := hb (x 7 14)
        clear * - r42979 b42980 b42981 d42970
        omega
      have d42982 : (x 6 2).toNat = 0 := by
        have r42983 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e42984 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e42985 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have b42986 := hb (x 5 3)
        have b42987 := hb (x 6 2)
        have b42988 := hb (x 7 13)
        have b42989 := hb (x 8 12)
        clear * - r42983 e42984 e42985 b42986 b42987 b42988 b42989 d42933 d42949 d42929
        omega
      have d42990 : (x 6 2 && x 6 13).toNat = 0 := by
        have r42991 := hand1 (x 6 2) (x 6 13)
        have b42992 := hb (x 6 2)
        have b42993 := hb (x 6 2 && x 6 13)
        clear * - r42991 b42992 b42993 d42982
        omega
      have d42994 : (x 8 13).toNat = 1 := by
        have r42995 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b42996 := hb (x 6 2)
        have b42997 := hb (x 8 13)
        have b42998 := hb (x 7 1 && x 7 14)
        clear * - r42995 b42996 b42997 b42998 d42974 d42982
        omega
      have d42999 : (x 8 1).toNat = 1 := by
        have r43000 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
        have b43001 := hb (x 8 1)
        have b43002 := hb (x 8 13)
        clear * - r43000 b43001 b43002 d42994
        omega
      have d43003 : (x 9 14).toNat = 0 := by
        have r43004 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b43005 := hb (x 8 1)
        have b43006 := hb (x 9 14)
        clear * - r43004 b43005 b43006 d42999
        omega
      have d43007 : (x 9 3 && x 9 14).toNat = 0 := by
        have r43008 := hand2 (x 9 3) (x 9 14)
        have b43009 := hb (x 9 14)
        have b43010 := hb (x 9 3 && x 9 14)
        clear * - r43008 b43009 b43010 d43003
        omega
      have d43011 : (x 9 2).toNat = 0 := by
        have r43012 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
        have b43013 := hb (x 9 2)
        have b43014 := hb (x 9 14)
        clear * - r43012 b43013 b43014 d43003
        omega
      have d43015 : (x 9 12).toNat = 0 := by
        have r43016 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43017 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
        have e43018 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
        have b43019 := hb (x 6 3)
        have b43020 := hb (x 7 2)
        have b43021 := hb (x 8 13)
        have b43022 := hb (x 9 12)
        clear * - r43016 e43017 e43018 b43019 b43020 b43021 b43022 d42994 d42978
        omega
      have d43023 : (x 9 4).toNat = 0 := by
        have r43024 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
        have b43025 := hb (x 9 4)
        have b43026 := hb (x 9 12)
        clear * - r43024 b43025 b43026 d43015
        omega
      have d43027 : (x 6 3).toNat = 0 := by
        have r43028 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43029 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
        have e43030 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
        have b43031 := hb (x 6 3)
        have b43032 := hb (x 7 2)
        have b43033 := hb (x 8 13)
        have b43034 := hb (x 9 12)
        clear * - r43028 e43029 e43030 b43031 b43032 b43033 b43034 d43015 d42994 d42978
        omega
      have d43035 : (x 6 3 && x 6 14).toNat = 0 := by
        have r43036 := hand1 (x 6 3) (x 6 14)
        have b43037 := hb (x 6 3)
        have b43038 := hb (x 6 3 && x 6 14)
        clear * - r43036 b43037 b43038 d43027
        omega
      have d43039 : (x 9 11).toNat = 1 := by
        have r43040 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b43041 := hb (x 5 4)
        have b43042 := hb (x 9 11)
        have b43043 := hb (x 8 1 && x 8 12)
        have b43044 := hb (x 7 2 && x 7 13)
        have b43045 := hb (x 6 3 && x 6 14)
        clear * - r43040 b43041 b43042 b43043 b43044 b43045 d42941 d42957 d43035 d42906
        omega
      have d43046 : (x 9 3).toNat = 1 := by
        have r43047 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
        have b43048 := hb (x 9 3)
        have b43049 := hb (x 9 11)
        clear * - r43047 b43048 b43049 d43039
        omega
      have d43050 : (x 12 12).toNat = 0 := by
        have r43051 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43052 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
        have e43053 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
        have b43054 := hb (x 9 3)
        have b43055 := hb (x 10 2)
        have b43056 := hb (x 11 13)
        have b43057 := hb (x 12 12)
        clear * - r43051 e43052 e43053 b43054 b43055 b43056 b43057 d43046
        omega
      have d43058 : (x 12 1 && x 12 12).toNat = 0 := by
        have r43059 := hand2 (x 12 1) (x 12 12)
        have b43060 := hb (x 12 12)
        have b43061 := hb (x 12 1 && x 12 12)
        clear * - r43059 b43060 b43061 d43050
        omega
      have d43062 : (x 12 4).toNat = 0 := by
        have r43063 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
        have b43064 := hb (x 12 4)
        have b43065 := hb (x 12 12)
        clear * - r43063 b43064 b43065 d43050
        omega
      have d43066 : (x 11 13).toNat = 0 := by
        have r43067 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43068 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
        have e43069 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
        have b43070 := hb (x 9 3)
        have b43071 := hb (x 10 2)
        have b43072 := hb (x 11 13)
        have b43073 := hb (x 12 12)
        clear * - r43067 e43068 e43069 b43070 b43071 b43072 b43073 d43050 d43046
        omega
      have d43074 : (x 11 2 && x 11 13).toNat = 0 := by
        have r43075 := hand2 (x 11 2) (x 11 13)
        have b43076 := hb (x 11 13)
        have b43077 := hb (x 11 2 && x 11 13)
        clear * - r43075 b43076 b43077 d43066
        omega
      have d43078 : (x 10 1 && x 10 14).toNat = 1 := by
        have r43079 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b43080 := hb (x 9 2)
        have b43081 := hb (x 11 13)
        have b43082 := hb (x 10 1 && x 10 14)
        clear * - r43079 b43080 b43081 b43082 d43066 d43011
        omega
      have d43083 : (x 10 14).toNat = 1 := by
        have r43084 := hand2 (x 10 1) (x 10 14)
        have b43085 := hb (x 10 14)
        have b43086 := hb (x 10 1 && x 10 14)
        clear * - r43084 b43085 b43086 d43078
        omega
      have d43087 : (x 9 1).toNat = 0 := by
        have r43088 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b43089 := hb (x 9 1)
        have b43090 := hb (x 10 14)
        clear * - r43088 b43089 b43090 d43083
        omega
      have d43091 : (x 9 13).toNat = 0 := by
        have r43092 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
        have b43093 := hb (x 9 1)
        have b43094 := hb (x 9 13)
        clear * - r43092 b43093 b43094 d43087
        omega
      have d43095 : (x 8 1 && x 8 14).toNat = 1 := by
        have r43096 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b43097 := hb (x 7 2)
        have b43098 := hb (x 9 13)
        have b43099 := hb (x 8 1 && x 8 14)
        clear * - r43096 b43097 b43098 b43099 d43091 d42978
        omega
      have d43100 : (x 8 14).toNat = 1 := by
        have r43101 := hand2 (x 8 1) (x 8 14)
        have b43102 := hb (x 8 14)
        have b43103 := hb (x 8 1 && x 8 14)
        clear * - r43101 b43102 b43103 d43095
        omega
      have d43104 : (x 7 1).toNat = 0 := by
        have r43105 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b43106 := hb (x 7 1)
        have b43107 := hb (x 8 14)
        clear * - r43105 b43106 b43107 d43100
        omega
      have d43108 : (x 7 1 && x 7 12).toNat = 0 := by
        have r43109 := hand1 (x 7 1) (x 7 12)
        have b43110 := hb (x 7 1)
        have b43111 := hb (x 7 1 && x 7 12)
        clear * - r43109 b43110 b43111 d43104
        omega
      have d43112 : (x 8 11).toNat = 1 := by
        have r43113 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b43114 := hb (x 4 4)
        have b43115 := hb (x 8 11)
        have b43116 := hb (x 7 1 && x 7 12)
        have b43117 := hb (x 6 2 && x 6 13)
        have b43118 := hb (x 5 3 && x 5 14)
        clear * - r43113 b43114 b43115 b43116 b43117 b43118 d43108 d42990 d42890 d42857
        omega
      have d43119 : (x 8 3).toNat = 1 := by
        have r43120 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
        have b43121 := hb (x 8 3)
        have b43122 := hb (x 8 11)
        clear * - r43120 b43121 b43122 d43112
        omega
      have d43123 : (x 11 12).toNat = 0 := by
        have r43124 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43125 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e43126 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b43127 := hb (x 8 3)
        have b43128 := hb (x 9 2)
        have b43129 := hb (x 10 13)
        have b43130 := hb (x 11 12)
        clear * - r43124 e43125 e43126 b43127 b43128 b43129 b43130 d43011 d43119
        omega
      have d43131 : (x 11 1 && x 11 12).toNat = 0 := by
        have r43132 := hand2 (x 11 1) (x 11 12)
        have b43133 := hb (x 11 12)
        have b43134 := hb (x 11 1 && x 11 12)
        clear * - r43132 b43133 b43134 d43123
        omega
      have d43135 : (x 10 13).toNat = 0 := by
        have r43136 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43137 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e43138 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b43139 := hb (x 8 3)
        have b43140 := hb (x 9 2)
        have b43141 := hb (x 10 13)
        have b43142 := hb (x 11 12)
        clear * - r43136 e43137 e43138 b43139 b43140 b43141 b43142 d43123 d43011 d43119
        omega
      have d43143 : (x 10 2 && x 10 13).toNat = 0 := by
        have r43144 := hand2 (x 10 2) (x 10 13)
        have b43145 := hb (x 10 13)
        have b43146 := hb (x 10 2 && x 10 13)
        clear * - r43144 b43145 b43146 d43135
        omega
      have d43147 : (x 12 11).toNat = 1 := by
        have r43148 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b43149 := hb (x 8 4)
        have b43150 := hb (x 12 11)
        have b43151 := hb (x 11 1 && x 11 12)
        have b43152 := hb (x 10 2 && x 10 13)
        have b43153 := hb (x 9 3 && x 9 14)
        clear * - r43148 b43149 b43150 b43151 b43152 b43153 d43131 d43143 d43007 d42945
        omega
      have d43154 : (x 12 3).toNat = 1 := by
        have r43155 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
        have b43156 := hb (x 12 3)
        have b43157 := hb (x 12 11)
        clear * - r43155 b43156 b43157 d43147
        omega
      have d43158 : (x 15 12).toNat = 0 := by
        have r43159 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43160 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e43161 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b43162 := hb (x 12 3)
        have b43163 := hb (x 13 2)
        have b43164 := hb (x 14 13)
        have b43165 := hb (x 15 12)
        clear * - r43159 e43160 e43161 b43162 b43163 b43164 b43165 d43154
        omega
      have d43166 : (x 15 1 && x 15 12).toNat = 0 := by
        have r43167 := hand2 (x 15 1) (x 15 12)
        have b43168 := hb (x 15 12)
        have b43169 := hb (x 15 1 && x 15 12)
        clear * - r43167 b43168 b43169 d43158
        omega
      have d43170 : (x 14 13).toNat = 0 := by
        have r43171 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43172 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e43173 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b43174 := hb (x 12 3)
        have b43175 := hb (x 13 2)
        have b43176 := hb (x 14 13)
        have b43177 := hb (x 15 12)
        clear * - r43171 e43172 e43173 b43174 b43175 b43176 b43177 d43158 d43154
        omega
      have d43178 : (x 14 2 && x 14 13).toNat = 0 := by
        have r43179 := hand2 (x 14 2) (x 14 13)
        have b43180 := hb (x 14 13)
        have b43181 := hb (x 14 2 && x 14 13)
        clear * - r43179 b43180 b43181 d43170
        omega
      have d43182 : (x 13 2).toNat = 0 := by
        have r43183 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43184 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e43185 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b43186 := hb (x 12 3)
        have b43187 := hb (x 13 2)
        have b43188 := hb (x 14 13)
        have b43189 := hb (x 15 12)
        clear * - r43183 e43184 e43185 b43186 b43187 b43188 b43189 d43158 d43170 d43154
        omega
      have d43190 : (x 10 1).toNat = 1 := by
        have r43191 := hand1 (x 10 1) (x 10 14)
        have b43192 := hb (x 10 1)
        have b43193 := hb (x 10 1 && x 10 14)
        clear * - r43191 b43192 b43193 d43078
        omega
      have d43194 : (x 11 14).toNat = 0 := by
        have r43195 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b43196 := hb (x 10 1)
        have b43197 := hb (x 11 14)
        clear * - r43195 b43196 b43197 d43190
        omega
      have d43198 : (x 11 1 && x 11 14).toNat = 0 := by
        have r43199 := hand2 (x 11 1) (x 11 14)
        have b43200 := hb (x 11 14)
        have b43201 := hb (x 11 1 && x 11 14)
        clear * - r43199 b43200 b43201 d43194
        omega
      have d43202 : (x 11 2).toNat = 0 := by
        have r43203 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
        have b43204 := hb (x 11 2)
        have b43205 := hb (x 11 14)
        clear * - r43203 b43204 b43205 d43194
        omega
      have d43206 : (x 10 2).toNat = 0 := by
        have r43207 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43208 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
        have e43209 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
        have b43210 := hb (x 9 3)
        have b43211 := hb (x 10 2)
        have b43212 := hb (x 11 13)
        have b43213 := hb (x 12 12)
        clear * - r43207 e43208 e43209 b43210 b43211 b43212 b43213 d43050 d43066 d43046
        omega
      have d43214 : (x 12 13).toNat = 1 := by
        have r43215 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b43216 := hb (x 10 2)
        have b43217 := hb (x 12 13)
        have b43218 := hb (x 11 1 && x 11 14)
        clear * - r43215 b43216 b43217 b43218 d43198 d43206
        omega
      have d43219 : (x 12 1).toNat = 1 := by
        have r43220 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
        have b43221 := hb (x 12 1)
        have b43222 := hb (x 12 13)
        clear * - r43220 b43221 b43222 d43214
        omega
      have d43223 : (x 13 14).toNat = 0 := by
        have r43224 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b43225 := hb (x 12 1)
        have b43226 := hb (x 13 14)
        clear * - r43224 b43225 b43226 d43219
        omega
      have d43227 : (x 13 1 && x 13 14).toNat = 0 := by
        have r43228 := hand2 (x 13 1) (x 13 14)
        have b43229 := hb (x 13 14)
        have b43230 := hb (x 13 1 && x 13 14)
        clear * - r43228 b43229 b43230 d43223
        omega
      have d43231 : (x 12 2).toNat = 1 := by
        have r43232 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b43233 := hb (x 12 2)
        have b43234 := hb (x 14 13)
        have b43235 := hb (x 13 1 && x 13 14)
        clear * - r43232 b43233 b43234 b43235 d43170 d43227
        omega
      have d43236 : (x 14 12).toNat = 0 := by
        have r43237 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43238 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
        have e43239 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
        have b43240 := hb (x 11 3)
        have b43241 := hb (x 12 2)
        have b43242 := hb (x 13 13)
        have b43243 := hb (x 14 12)
        clear * - r43237 e43238 e43239 b43240 b43241 b43242 b43243 d43231
        omega
      have d43244 : (x 14 4).toNat = 0 := by
        have r43245 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
        have b43246 := hb (x 14 4)
        have b43247 := hb (x 14 12)
        clear * - r43245 b43246 b43247 d43236
        omega
      have d43248 : (x 14 4 && x 14 14).toNat = 0 := by
        have r43249 := hand1 (x 14 4) (x 14 14)
        have b43250 := hb (x 14 4)
        have b43251 := hb (x 14 4 && x 14 14)
        clear * - r43249 b43250 b43251 d43244
        omega
      have d43252 : (x 13 13).toNat = 0 := by
        have r43253 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43254 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
        have e43255 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
        have b43256 := hb (x 11 3)
        have b43257 := hb (x 12 2)
        have b43258 := hb (x 13 13)
        have b43259 := hb (x 14 12)
        clear * - r43253 e43254 e43255 b43256 b43257 b43258 b43259 d43236 d43231
        omega
      have d43260 : (x 13 5).toNat = 0 := by
        have r43261 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
        have b43262 := hb (x 13 5)
        have b43263 := hb (x 13 13)
        clear * - r43261 b43262 b43263 d43252
        omega
      have d43264 : (x 13 3 && x 13 14).toNat = 0 := by
        have r43265 := hand2 (x 13 3) (x 13 14)
        have b43266 := hb (x 13 14)
        have b43267 := hb (x 13 3 && x 13 14)
        clear * - r43265 b43266 b43267 d43223
        omega
      have d43268 : (x 16 11).toNat = 1 := by
        have r43269 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b43270 := hb (x 12 4)
        have b43271 := hb (x 16 11)
        have b43272 := hb (x 15 1 && x 15 12)
        have b43273 := hb (x 14 2 && x 14 13)
        have b43274 := hb (x 13 3 && x 13 14)
        clear * - r43269 b43270 b43271 b43272 b43273 b43274 d43166 d43178 d43264 d43062
        omega
      have d43275 : (x 16 3).toNat = 1 := by
        have r43276 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
        have b43277 := hb (x 16 3)
        have b43278 := hb (x 16 11)
        clear * - r43276 b43277 b43278 d43268
        omega
      have d43279 : (x 19 12).toNat = 0 := by
        have r43280 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43281 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
        have e43282 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
        have b43283 := hb (x 16 3)
        have b43284 := hb (x 17 2)
        have b43285 := hb (x 18 13)
        have b43286 := hb (x 19 12)
        clear * - r43280 e43281 e43282 b43283 b43284 b43285 b43286 d43275
        omega
      have d43287 : (x 18 13).toNat = 0 := by
        have r43288 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43289 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
        have e43290 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
        have b43291 := hb (x 16 3)
        have b43292 := hb (x 17 2)
        have b43293 := hb (x 18 13)
        have b43294 := hb (x 19 12)
        clear * - r43288 e43289 e43290 b43291 b43292 b43293 b43294 d43279 d43275
        omega
      have d43295 : (x 17 2).toNat = 0 := by
        have r43296 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43297 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
        have e43298 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
        have b43299 := hb (x 16 3)
        have b43300 := hb (x 17 2)
        have b43301 := hb (x 18 13)
        have b43302 := hb (x 19 12)
        clear * - r43296 e43297 e43298 b43299 b43300 b43301 b43302 d43279 d43287 d43275
        omega
      have d43303 : (x 13 12).toNat = 0 := by
        have r43304 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43305 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
        have e43306 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
        have b43307 := hb (x 10 3)
        have b43308 := hb (x 11 2)
        have b43309 := hb (x 12 13)
        have b43310 := hb (x 13 12)
        clear * - r43304 e43305 e43306 b43307 b43308 b43309 b43310 d43214 d43202
        omega
      have d43311 : (x 13 4).toNat = 0 := by
        have r43312 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
        have b43313 := hb (x 13 4)
        have b43314 := hb (x 13 12)
        clear * - r43312 b43313 b43314 d43303
        omega
      have d43315 : (x 10 3).toNat = 0 := by
        have r43316 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43317 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
        have e43318 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
        have b43319 := hb (x 10 3)
        have b43320 := hb (x 11 2)
        have b43321 := hb (x 12 13)
        have b43322 := hb (x 13 12)
        clear * - r43316 e43317 e43318 b43319 b43320 b43321 b43322 d43303 d43214 d43202
        omega
      have d43323 : (x 10 3 && x 10 14).toNat = 0 := by
        have r43324 := hand1 (x 10 3) (x 10 14)
        have b43325 := hb (x 10 3)
        have b43326 := hb (x 10 3 && x 10 14)
        clear * - r43324 b43325 b43326 d43315
        omega
      have d43327 : (x 13 11).toNat = 1 := by
        have r43328 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b43329 := hb (x 9 4)
        have b43330 := hb (x 13 11)
        have b43331 := hb (x 12 1 && x 12 12)
        have b43332 := hb (x 11 2 && x 11 13)
        have b43333 := hb (x 10 3 && x 10 14)
        clear * - r43328 b43329 b43330 b43331 b43332 b43333 d43058 d43074 d43323 d43023
        omega
      have d43334 : (x 13 3).toNat = 1 := by
        have r43335 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
        have b43336 := hb (x 13 3)
        have b43337 := hb (x 13 11)
        clear * - r43335 b43336 b43337 d43327
        omega
      have d43338 : (x 16 12).toNat = 0 := by
        have r43339 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43340 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
        have e43341 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
        have b43342 := hb (x 13 3)
        have b43343 := hb (x 14 2)
        have b43344 := hb (x 15 13)
        have b43345 := hb (x 16 12)
        clear * - r43339 e43340 e43341 b43342 b43343 b43344 b43345 d43334
        omega
      have d43346 : (x 16 1 && x 16 12).toNat = 0 := by
        have r43347 := hand2 (x 16 1) (x 16 12)
        have b43348 := hb (x 16 12)
        have b43349 := hb (x 16 1 && x 16 12)
        clear * - r43347 b43348 b43349 d43338
        omega
      have d43350 : (x 16 2 && x 16 12).toNat = 0 := by
        have r43351 := hand2 (x 16 2) (x 16 12)
        have b43352 := hb (x 16 12)
        have b43353 := hb (x 16 2 && x 16 12)
        clear * - r43351 b43352 b43353 d43338
        omega
      have d43354 : (x 15 13).toNat = 0 := by
        have r43355 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43356 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
        have e43357 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
        have b43358 := hb (x 13 3)
        have b43359 := hb (x 14 2)
        have b43360 := hb (x 15 13)
        have b43361 := hb (x 16 12)
        clear * - r43355 e43356 e43357 b43358 b43359 b43360 b43361 d43338 d43334
        omega
      have d43362 : (x 15 2 && x 15 13).toNat = 0 := by
        have r43363 := hand2 (x 15 2) (x 15 13)
        have b43364 := hb (x 15 13)
        have b43365 := hb (x 15 2 && x 15 13)
        clear * - r43363 b43364 b43365 d43354
        omega
      have d43366 : (x 15 3 && x 15 13).toNat = 0 := by
        have r43367 := hand2 (x 15 3) (x 15 13)
        have b43368 := hb (x 15 13)
        have b43369 := hb (x 15 3 && x 15 13)
        clear * - r43367 b43368 b43369 d43354
        omega
      have d43370 : (x 14 1 && x 14 14).toNat = 1 := by
        have r43371 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b43372 := hb (x 13 2)
        have b43373 := hb (x 15 13)
        have b43374 := hb (x 14 1 && x 14 14)
        clear * - r43371 b43372 b43373 b43374 d43354 d43182
        omega
      have d43375 : (x 14 1).toNat = 1 := by
        have r43376 := hand1 (x 14 1) (x 14 14)
        have b43377 := hb (x 14 1)
        have b43378 := hb (x 14 1 && x 14 14)
        clear * - r43376 b43377 b43378 d43370
        omega
      have d43379 : (x 15 14).toNat = 0 := by
        have r43380 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b43381 := hb (x 14 1)
        have b43382 := hb (x 15 14)
        clear * - r43380 b43381 b43382 d43375
        omega
      have d43383 : (x 15 1 && x 15 14).toNat = 0 := by
        have r43384 := hand2 (x 15 1) (x 15 14)
        have b43385 := hb (x 15 14)
        have b43386 := hb (x 15 1 && x 15 14)
        clear * - r43384 b43385 b43386 d43379
        omega
      have d43387 : (x 15 2).toNat = 0 := by
        have r43388 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
        have b43389 := hb (x 15 2)
        have b43390 := hb (x 15 14)
        clear * - r43388 b43389 b43390 d43379
        omega
      have d43391 : (x 14 2).toNat = 0 := by
        have r43392 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43393 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
        have e43394 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
        have b43395 := hb (x 13 3)
        have b43396 := hb (x 14 2)
        have b43397 := hb (x 15 13)
        have b43398 := hb (x 16 12)
        clear * - r43392 e43393 e43394 b43395 b43396 b43397 b43398 d43338 d43354 d43334
        omega
      have d43399 : (x 16 13).toNat = 1 := by
        have r43400 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b43401 := hb (x 14 2)
        have b43402 := hb (x 16 13)
        have b43403 := hb (x 15 1 && x 15 14)
        clear * - r43400 b43401 b43402 b43403 d43383 d43391
        omega
      have d43404 : (x 17 12).toNat = 0 := by
        have r43405 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43406 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
        have e43407 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
        have b43408 := hb (x 14 3)
        have b43409 := hb (x 15 2)
        have b43410 := hb (x 16 13)
        have b43411 := hb (x 17 12)
        clear * - r43405 e43406 e43407 b43408 b43409 b43410 b43411 d43399 d43387
        omega
      have d43412 : (x 14 3).toNat = 0 := by
        have r43413 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43414 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
        have e43415 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
        have b43416 := hb (x 14 3)
        have b43417 := hb (x 15 2)
        have b43418 := hb (x 16 13)
        have b43419 := hb (x 17 12)
        clear * - r43413 e43414 e43415 b43416 b43417 b43418 b43419 d43404 d43399 d43387
        omega
      have d43420 : (x 14 3 && x 14 14).toNat = 0 := by
        have r43421 := hand1 (x 14 3) (x 14 14)
        have b43422 := hb (x 14 3)
        have b43423 := hb (x 14 3 && x 14 14)
        clear * - r43421 b43422 b43423 d43412
        omega
      have d43424 : (x 17 11).toNat = 1 := by
        have r43425 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b43426 := hb (x 13 4)
        have b43427 := hb (x 17 11)
        have b43428 := hb (x 16 1 && x 16 12)
        have b43429 := hb (x 15 2 && x 15 13)
        have b43430 := hb (x 14 3 && x 14 14)
        clear * - r43425 b43426 b43427 b43428 b43429 b43430 d43346 d43362 d43420 d43311
        omega
      have d43431 : (x 17 3).toNat = 1 := by
        have r43432 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
        have b43433 := hb (x 17 3)
        have b43434 := hb (x 17 11)
        clear * - r43432 b43433 b43434 d43424
        omega
      have d43435 : (x 20 12).toNat = 0 := by
        have r43436 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43437 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
        have e43438 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
        have b43439 := hb (x 17 3)
        have b43440 := hb (x 18 2)
        have b43441 := hb (x 19 13)
        have b43442 := hb (x 20 12)
        clear * - r43436 e43437 e43438 b43439 b43440 b43441 b43442 d43431
        omega
      have d43443 : (x 19 13).toNat = 0 := by
        have r43444 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43445 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
        have e43446 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
        have b43447 := hb (x 17 3)
        have b43448 := hb (x 18 2)
        have b43449 := hb (x 19 13)
        have b43450 := hb (x 20 12)
        clear * - r43444 e43445 e43446 b43447 b43448 b43449 b43450 d43435 d43431
        omega
      have d43451 : (x 18 1 && x 18 14).toNat = 1 := by
        have r43452 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b43453 := hb (x 17 2)
        have b43454 := hb (x 19 13)
        have b43455 := hb (x 18 1 && x 18 14)
        clear * - r43452 b43453 b43454 b43455 d43443 d43295
        omega
      have d43456 : (x 18 14).toNat = 1 := by
        have r43457 := hand2 (x 18 1) (x 18 14)
        have b43458 := hb (x 18 14)
        have b43459 := hb (x 18 1 && x 18 14)
        clear * - r43457 b43458 b43459 d43451
        omega
      have d43460 : (x 17 1).toNat = 0 := by
        have r43461 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b43462 := hb (x 17 1)
        have b43463 := hb (x 18 14)
        clear * - r43461 b43462 b43463 d43456
        omega
      have d43464 : (x 17 1 && x 17 11).toNat = 0 := by
        have r43465 := hand1 (x 17 1) (x 17 11)
        have b43466 := hb (x 17 1)
        have b43467 := hb (x 17 1 && x 17 11)
        clear * - r43465 b43466 b43467 d43460
        omega
      have d43468 : (x 18 2).toNat = 0 := by
        have r43469 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43470 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
        have e43471 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
        have b43472 := hb (x 17 3)
        have b43473 := hb (x 18 2)
        have b43474 := hb (x 19 13)
        have b43475 := hb (x 20 12)
        clear * - r43469 e43470 e43471 b43472 b43473 b43474 b43475 d43435 d43443 d43431
        omega
      have d43476 : (x 18 10).toNat = 0 := by
        have r43477 : (x 18 10).toNat ≤ (x 18 2).toNat := himp _ _ (hp10 18)
        have b43478 := hb (x 18 2)
        have b43479 := hb (x 18 10)
        clear * - r43477 b43478 b43479 d43468
        omega
      have r43480 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := by have q := hcov10 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b43481 := hb (x 13 5)
      have b43482 := hb (x 18 10)
      have b43483 := hb (x 17 1 && x 17 11)
      have b43484 := hb (x 16 2 && x 16 12)
      have b43485 := hb (x 15 3 && x 15 13)
      have b43486 := hb (x 14 4 && x 14 14)
      linarith only [r43480, b43481, b43482, b43483, b43484, b43485, b43486, d43476, d43464, d43350, d43366, d43248, d43260]
  · have f43487 : (x (-1) 8).toNat = 1 := by rw [h42361]; rfl
    have d43488 : (x (-2) 9).toNat = 0 := by
      have r43489 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e43490 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
      have e43491 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
      have e43492 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
      have e43493 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
      have e43494 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
      have e43495 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
      have b43496 := hb (x (-8) 7)
      have b43497 := hb (x (-7) 6)
      have b43498 := hb (x (-6) 5)
      have b43499 := hb (x (-5) 4)
      have b43500 := hb (x (-4) 11)
      have b43501 := hb (x (-3) 10)
      have b43502 := hb (x (-2) 9)
      have b43503 := hb (x (-1) 8)
      clear * - r43489 e43490 e43491 e43492 e43493 e43494 e43495 b43496 b43497 b43498 b43499 b43500 b43501 b43502 b43503 f43487 g8 g5
      omega
    have d43504 : (x (-5) 4).toNat = 0 := by
      have r43505 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e43506 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
      have e43507 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
      have e43508 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
      have e43509 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
      have e43510 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
      have e43511 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
      have b43512 := hb (x (-8) 7)
      have b43513 := hb (x (-7) 6)
      have b43514 := hb (x (-6) 5)
      have b43515 := hb (x (-5) 4)
      have b43516 := hb (x (-4) 11)
      have b43517 := hb (x (-3) 10)
      have b43518 := hb (x (-2) 9)
      have b43519 := hb (x (-1) 8)
      clear * - r43505 e43506 e43507 e43508 e43509 e43510 e43511 b43512 b43513 b43514 b43515 b43516 b43517 b43518 b43519 f43487 d43488 g8 g5
      omega
    have d43520 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
      have r43521 := hand1 (x (-5) 4) (x (-5) 13)
      have b43522 := hb (x (-5) 4)
      have b43523 := hb (x (-5) 4 && x (-5) 13)
      clear * - r43521 b43522 b43523 d43504
      omega
    have d43524 : (x (-6) 5).toNat = 0 := by
      have r43525 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e43526 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
      have e43527 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
      have e43528 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
      have e43529 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
      have e43530 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
      have e43531 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
      have b43532 := hb (x (-8) 7)
      have b43533 := hb (x (-7) 6)
      have b43534 := hb (x (-6) 5)
      have b43535 := hb (x (-5) 4)
      have b43536 := hb (x (-4) 11)
      have b43537 := hb (x (-3) 10)
      have b43538 := hb (x (-2) 9)
      have b43539 := hb (x (-1) 8)
      clear * - r43525 e43526 e43527 e43528 e43529 e43530 e43531 b43532 b43533 b43534 b43535 b43536 b43537 b43538 b43539 f43487 d43488 g8 g5 d43504
      omega
    have d43540 : (x (-6) 5 && x (-6) 14).toNat = 0 := by
      have r43541 := hand1 (x (-6) 5) (x (-6) 14)
      have b43542 := hb (x (-6) 5)
      have b43543 := hb (x (-6) 5 && x (-6) 14)
      clear * - r43541 b43542 b43543 d43524
      omega
    have d43544 : (x (-7) 6).toNat = 1 := by
      have r43545 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b43546 := hb (x (-7) 6)
      have b43547 := hb (x (-1) 9)
      have b43548 := hb (x (-2) 1 && x (-2) 10)
      have b43549 := hb (x (-3) 2 && x (-3) 11)
      have b43550 := hb (x (-4) 3 && x (-4) 12)
      have b43551 := hb (x (-5) 4 && x (-5) 13)
      have b43552 := hb (x (-6) 5 && x (-6) 14)
      clear * - r43545 b43546 b43547 b43548 b43549 b43550 b43551 b43552 g15 g63 g64 g65 d43520 d43540
      omega
    have r43553 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e43554 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
    have e43555 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
    have e43556 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
    have e43557 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
    have e43558 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
    have e43559 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
    have b43560 := hb (x (-8) 7)
    have b43561 := hb (x (-7) 6)
    have b43562 := hb (x (-6) 5)
    have b43563 := hb (x (-5) 4)
    have b43564 := hb (x (-4) 11)
    have b43565 := hb (x (-3) 10)
    have b43566 := hb (x (-2) 9)
    have b43567 := hb (x (-1) 8)
    linarith only [r43553, e43554, e43555, e43556, e43557, e43558, e43559, b43560, b43561, b43562, b43563, b43564, b43565, b43566, b43567, f43487, d43488, g8, g5, d43504, d43524, d43544]

theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a010100000 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-6) 7).toNat = 0)
    (g1 : (x (-5) 6).toNat = 0)
    (g2 : (x (-5) 11).toNat = 0)
    (g3 : (x (-4) 5).toNat = 0)
    (g4 : (x (-4) 10).toNat = 0)
    (g5 : (x (-4) 11).toNat = 0)
    (g6 : (x (-3) 4).toNat = 0)
    (g7 : (x (-3) 9).toNat = 0)
    (g8 : (x (-3) 10).toNat = 0)
    (g9 : (x (-3) 11).toNat = 0)
    (g10 : (x (-2) 3).toNat = 1)
    (g11 : (x (-2) 10).toNat = 0)
    (g12 : (x (-1) 2).toNat = 0)
    (g13 : (x (-1) 4).toNat = 0)
    (g14 : (x (-1) 6).toNat = 0)
    (g15 : (x (-1) 9).toNat = 0)
    (g16 : (x 0 1).toNat = 1)
    (g17 : (x 0 3).toNat = 0)
    (g18 : (x 0 5).toNat = 0)
    (g19 : (x 0 7).toNat = 0)
    (g20 : (x 0 8).toNat = 1)
    (g21 : (x 0 11).toNat = 0)
    (g22 : (x 1 2).toNat = 0)
    (g23 : (x 1 4).toNat = 0)
    (g24 : (x 1 6).toNat = 0)
    (g25 : (x 1 7).toNat = 0)
    (g26 : (x 1 10).toNat = 0)
    (g27 : (x 2 1).toNat = 1)
    (g28 : (x 3 2).toNat = 0)
    (g29 : (x 3 10).toNat = 0)
    (g30 : (x 0 1 && x 0 3).toNat = 0)
    (g31 : (x (-1) 2 && x (-1) 4).toNat = 0)
    (g32 : (x (-3) 4 && x (-3) 6).toNat = 0)
    (g33 : (x (-4) 5 && x (-4) 7).toNat = 0)
    (g34 : (x (-5) 6 && x (-5) 8).toNat = 0)
    (g35 : (x (-6) 7 && x (-6) 9).toNat = 0)
    (g36 : (x (-1) 1 && x (-1) 6).toNat = 0)
    (g37 : (x (-3) 3 && x (-3) 8).toNat = 0)
    (g38 : (x (-4) 4 && x (-4) 9).toNat = 0)
    (g39 : (x (-5) 5 && x (-5) 10).toNat = 0)
    (g40 : (x (-6) 6 && x (-6) 11).toNat = 0)
    (g41 : (x (-7) 7 && x (-7) 12).toNat = 0)
    (g42 : (x 1 2 && x 1 7).toNat = 0)
    (g43 : (x 0 3 && x 0 8).toNat = 0)
    (g44 : (x (-1) 4 && x (-1) 9).toNat = 0)
    (g45 : (x (-2) 5 && x (-2) 10).toNat = 0)
    (g46 : (x (-3) 6 && x (-3) 11).toNat = 0)
    (g47 : (x 1 5 && x 1 10).toNat = 0)
    (g48 : (x 0 6 && x 0 11).toNat = 0)
    (g49 : (x (-1) 7 && x (-1) 12).toNat = 0)
    (g50 : (x (-3) 9 && x (-3) 14).toNat = 0)
    (g51 : (x 0 1 && x 0 7).toNat = 0)
    (g52 : (x (-1) 2 && x (-1) 8).toNat = 0)
    (g53 : (x (-3) 4 && x (-3) 10).toNat = 0)
    (g54 : (x (-4) 5 && x (-4) 11).toNat = 0)
    (g55 : (x (-5) 6 && x (-5) 12).toNat = 0)
    (g56 : (x (-6) 7 && x (-6) 13).toNat = 0)
    (g57 : (x (-1) 1 && x (-1) 8).toNat = 0)
    (g58 : (x (-3) 3 && x (-3) 10).toNat = 0)
    (g59 : (x (-4) 4 && x (-4) 11).toNat = 0)
    (g60 : (x (-5) 5 && x (-5) 12).toNat = 0)
    (g61 : (x (-6) 6 && x (-6) 13).toNat = 0)
    (g62 : (x (-7) 7 && x (-7) 14).toNat = 0)
    (g63 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g64 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g65 : (x (-4) 3 && x (-4) 12).toNat = 0)
    (g66 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g67 : (x (-4) 2 && x (-4) 12).toNat = 0)
    (g68 : (x (-5) 3 && x (-5) 13).toNat = 0)
    (g69 : (x 1 2 && x 1 12).toNat = 0)
    (g70 : (x 0 3 && x 0 13).toNat = 0)
    (g71 : (x (-1) 4 && x (-1) 14).toNat = 0)
    (g72 : (x 3 2 && x 3 13).toNat = 0)
    (g73 : (x 3 1 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a010100000_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73
