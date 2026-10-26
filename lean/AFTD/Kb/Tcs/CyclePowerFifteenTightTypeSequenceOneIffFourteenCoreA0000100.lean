import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0000100

Topic: combinatorics   Node: fe2589862045

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core: under the layer-free tight-cover constraints for k = 15 and 36 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0000100_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-2) 3).toNat = 0)
    (g1 : (x (-2) 5).toNat = 0)
    (g2 : (x (-2) 9).toNat = 0)
    (g3 : (x (-2) 13).toNat = 0)
    (g4 : (x (-1) 2).toNat = 1)
    (g5 : (x (-1) 8).toNat = 0)
    (g6 : (x 0 1).toNat = 1)
    (g7 : (x 0 3).toNat = 0)
    (g8 : (x 0 6).toNat = 0)
    (g9 : (x 0 7).toNat = 0)
    (g10 : (x 0 11).toNat = 0)
    (g11 : (x 1 2).toNat = 0)
    (g12 : (x 1 4).toNat = 0)
    (g13 : (x 1 6).toNat = 0)
    (g14 : (x 1 10).toNat = 0)
    (g15 : (x 2 1).toNat = 1)
    (g16 : (x 2 4).toNat = 0)
    (g17 : (x 3 2).toNat = 0)
    (g18 : (x 3 4).toNat = 0)
    (g19 : (x 1 2 && x 1 6).toNat = 0)
    (g20 : (x 0 3 && x 0 7).toNat = 0)
    (g21 : (x (-1) 4 && x (-1) 8).toNat = 0)
    (g22 : (x (-2) 5 && x (-2) 9).toNat = 0)
    (g23 : (x 0 1 && x 0 7).toNat = 0)
    (g24 : (x (-1) 2 && x (-1) 8).toNat = 0)
    (g25 : (x (-2) 3 && x (-2) 9).toNat = 0)
    (g26 : (x 3 3 && x 3 12).toNat = 0)
    (g27 : (x 2 4 && x 2 13).toNat = 0)
    (g28 : (x 1 5 && x 1 14).toNat = 0)
    (g29 : (x 2 1 && x 2 12).toNat = 0)
    (g30 : (x 1 2 && x 1 13).toNat = 0)
    (g31 : (x 0 3 && x 0 14).toNat = 0)
    (g32 : (x 3 2 && x 3 13).toNat = 0)
    (g33 : (x 3 3 && x 3 14).toNat = 0)
    (g34 : (x (-2) 1 && x (-2) 14).toNat = 0)
    (g35 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  cases h25939 : x 0 12
  · have f25940 : (x 0 12).toNat = 0 := by rw [h25939]; rfl
    cases h25941 : x 1 1
    · have f25942 : (x 1 1).toNat = 0 := by rw [h25941]; rfl
      cases h25943 : x 1 3
      · have f25944 : (x 1 3).toNat = 0 := by rw [h25943]; rfl
        cases h25945 : x (-1) 4
        · have f25946 : (x (-1) 4).toNat = 0 := by rw [h25945]; rfl
          have d25947 : (x 3 11).toNat = 1 := by
            have r25948 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := hcov11 3
            have b25949 := hb (x (-1) 4)
            have b25950 := hb (x 3 11)
            have b25951 := hb (x 2 1 && x 2 12)
            have b25952 := hb (x 1 2 && x 1 13)
            have b25953 := hb (x 0 3 && x 0 14)
            clear * - r25948 b25949 b25950 b25951 b25952 b25953 g29 g30 g31 f25946
            omega
          have d25954 : (x 3 3).toNat = 1 := by
            have r25955 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
            have b25956 := hb (x 3 3)
            have b25957 := hb (x 3 11)
            clear * - r25955 b25956 b25957 d25947
            omega
          have d25958 : (x 6 12).toNat = 0 := by
            have r25959 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
            have e25960 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
            have e25961 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
            have b25962 := hb (x 3 3)
            have b25963 := hb (x 4 2)
            have b25964 := hb (x 5 13)
            have b25965 := hb (x 6 12)
            clear * - r25959 e25960 e25961 b25962 b25963 b25964 b25965 d25954
            omega
          have d25966 : (x 6 1 && x 6 12).toNat = 0 := by
            have r25967 := hand2 (x 6 1) (x 6 12)
            have b25968 := hb (x 6 12)
            have b25969 := hb (x 6 1 && x 6 12)
            clear * - r25967 b25968 b25969 d25958
            omega
          have d25970 : (x 6 4).toNat = 0 := by
            have r25971 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
            have b25972 := hb (x 6 4)
            have b25973 := hb (x 6 12)
            clear * - r25971 b25972 b25973 d25958
            omega
          have d25974 : (x 5 13).toNat = 0 := by
            have r25975 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
            have e25976 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
            have e25977 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
            have b25978 := hb (x 3 3)
            have b25979 := hb (x 4 2)
            have b25980 := hb (x 5 13)
            have b25981 := hb (x 6 12)
            clear * - r25975 e25976 e25977 b25978 b25979 b25980 b25981 d25958 d25954
            omega
          have d25982 : (x 5 2 && x 5 13).toNat = 0 := by
            have r25983 := hand2 (x 5 2) (x 5 13)
            have b25984 := hb (x 5 13)
            have b25985 := hb (x 5 2 && x 5 13)
            clear * - r25983 b25984 b25985 d25974
            omega
          have d25986 : (x 4 1 && x 4 14).toNat = 1 := by
            have r25987 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := hcov13 5
            have b25988 := hb (x 3 2)
            have b25989 := hb (x 5 13)
            have b25990 := hb (x 4 1 && x 4 14)
            clear * - r25987 b25988 b25989 b25990 d25974 g17
            omega
          have d25991 : (x 4 1).toNat = 1 := by
            have r25992 := hand1 (x 4 1) (x 4 14)
            have b25993 := hb (x 4 1)
            have b25994 := hb (x 4 1 && x 4 14)
            clear * - r25992 b25993 b25994 d25986
            omega
          have d25995 : (x 5 14).toNat = 0 := by
            have r25996 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
            have b25997 := hb (x 4 1)
            have b25998 := hb (x 5 14)
            clear * - r25996 b25997 b25998 d25991
            omega
          have d25999 : (x 5 1 && x 5 14).toNat = 0 := by
            have r26000 := hand2 (x 5 1) (x 5 14)
            have b26001 := hb (x 5 14)
            have b26002 := hb (x 5 1 && x 5 14)
            clear * - r26000 b26001 b26002 d25995
            omega
          have d26003 : (x 5 2).toNat = 0 := by
            have r26004 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
            have b26005 := hb (x 5 2)
            have b26006 := hb (x 5 14)
            clear * - r26004 b26005 b26006 d25995
            omega
          have d26007 : (x 4 2).toNat = 0 := by
            have r26008 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
            have e26009 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
            have e26010 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
            have b26011 := hb (x 3 3)
            have b26012 := hb (x 4 2)
            have b26013 := hb (x 5 13)
            have b26014 := hb (x 6 12)
            clear * - r26008 e26009 e26010 b26011 b26012 b26013 b26014 d25958 d25974 d25954
            omega
          have d26015 : (x 4 2 && x 4 13).toNat = 0 := by
            have r26016 := hand1 (x 4 2) (x 4 13)
            have b26017 := hb (x 4 2)
            have b26018 := hb (x 4 2 && x 4 13)
            clear * - r26016 b26017 b26018 d26007
            omega
          have d26019 : (x 6 13).toNat = 1 := by
            have r26020 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := hcov13 6
            have b26021 := hb (x 4 2)
            have b26022 := hb (x 6 13)
            have b26023 := hb (x 5 1 && x 5 14)
            clear * - r26020 b26021 b26022 b26023 d25999 d26007
            omega
          have d26024 : (x 6 1).toNat = 1 := by
            have r26025 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
            have b26026 := hb (x 6 1)
            have b26027 := hb (x 6 13)
            clear * - r26025 b26026 b26027 d26019
            omega
          have d26028 : (x 7 14).toNat = 0 := by
            have r26029 : (x 7 14).toNat + (x 6 1).toNat = 1 := hd14 7
            have b26030 := hb (x 6 1)
            have b26031 := hb (x 7 14)
            clear * - r26029 b26030 b26031 d26024
            omega
          have d26032 : (x 7 3 && x 7 14).toNat = 0 := by
            have r26033 := hand2 (x 7 3) (x 7 14)
            have b26034 := hb (x 7 14)
            have b26035 := hb (x 7 3 && x 7 14)
            clear * - r26033 b26034 b26035 d26028
            omega
          have d26036 : (x 7 2).toNat = 0 := by
            have r26037 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
            have b26038 := hb (x 7 2)
            have b26039 := hb (x 7 14)
            clear * - r26037 b26038 b26039 d26028
            omega
          have d26040 : (x 7 12).toNat = 0 := by
            have r26041 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
            have e26042 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
            have e26043 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
            have b26044 := hb (x 4 3)
            have b26045 := hb (x 5 2)
            have b26046 := hb (x 6 13)
            have b26047 := hb (x 7 12)
            clear * - r26041 e26042 e26043 b26044 b26045 b26046 b26047 d26019 d26003
            omega
          have d26048 : (x 7 4).toNat = 0 := by
            have r26049 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
            have b26050 := hb (x 7 4)
            have b26051 := hb (x 7 12)
            clear * - r26049 b26050 b26051 d26040
            omega
          have d26052 : (x 4 3).toNat = 0 := by
            have r26053 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
            have e26054 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
            have e26055 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
            have b26056 := hb (x 4 3)
            have b26057 := hb (x 5 2)
            have b26058 := hb (x 6 13)
            have b26059 := hb (x 7 12)
            clear * - r26053 e26054 e26055 b26056 b26057 b26058 b26059 d26040 d26019 d26003
            omega
          have d26060 : (x 4 3 && x 4 14).toNat = 0 := by
            have r26061 := hand1 (x 4 3) (x 4 14)
            have b26062 := hb (x 4 3)
            have b26063 := hb (x 4 3 && x 4 14)
            clear * - r26061 b26062 b26063 d26052
            omega
          have d26064 : (x 7 11).toNat = 1 := by
            have r26065 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := hcov11 7
            have b26066 := hb (x 3 4)
            have b26067 := hb (x 7 11)
            have b26068 := hb (x 6 1 && x 6 12)
            have b26069 := hb (x 5 2 && x 5 13)
            have b26070 := hb (x 4 3 && x 4 14)
            clear * - r26065 b26066 b26067 b26068 b26069 b26070 d25966 d25982 d26060 g18
            omega
          have d26071 : (x 7 3).toNat = 1 := by
            have r26072 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
            have b26073 := hb (x 7 3)
            have b26074 := hb (x 7 11)
            clear * - r26072 b26073 b26074 d26064
            omega
          have d26075 : (x 10 12).toNat = 0 := by
            have r26076 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
            have e26077 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
            have e26078 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
            have b26079 := hb (x 7 3)
            have b26080 := hb (x 8 2)
            have b26081 := hb (x 9 13)
            have b26082 := hb (x 10 12)
            clear * - r26076 e26077 e26078 b26079 b26080 b26081 b26082 d26071
            omega
          have d26083 : (x 10 1 && x 10 12).toNat = 0 := by
            have r26084 := hand2 (x 10 1) (x 10 12)
            have b26085 := hb (x 10 12)
            have b26086 := hb (x 10 1 && x 10 12)
            clear * - r26084 b26085 b26086 d26075
            omega
          have d26087 : (x 10 4).toNat = 0 := by
            have r26088 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
            have b26089 := hb (x 10 4)
            have b26090 := hb (x 10 12)
            clear * - r26088 b26089 b26090 d26075
            omega
          have d26091 : (x 9 13).toNat = 0 := by
            have r26092 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
            have e26093 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
            have e26094 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
            have b26095 := hb (x 7 3)
            have b26096 := hb (x 8 2)
            have b26097 := hb (x 9 13)
            have b26098 := hb (x 10 12)
            clear * - r26092 e26093 e26094 b26095 b26096 b26097 b26098 d26075 d26071
            omega
          have d26099 : (x 9 2 && x 9 13).toNat = 0 := by
            have r26100 := hand2 (x 9 2) (x 9 13)
            have b26101 := hb (x 9 13)
            have b26102 := hb (x 9 2 && x 9 13)
            clear * - r26100 b26101 b26102 d26091
            omega
          have d26103 : (x 8 1 && x 8 14).toNat = 1 := by
            have r26104 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := hcov13 9
            have b26105 := hb (x 7 2)
            have b26106 := hb (x 9 13)
            have b26107 := hb (x 8 1 && x 8 14)
            clear * - r26104 b26105 b26106 b26107 d26091 d26036
            omega
          have d26108 : (x 8 14).toNat = 1 := by
            have r26109 := hand2 (x 8 1) (x 8 14)
            have b26110 := hb (x 8 14)
            have b26111 := hb (x 8 1 && x 8 14)
            clear * - r26109 b26110 b26111 d26103
            omega
          have d26112 : (x 7 1).toNat = 0 := by
            have r26113 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
            have b26114 := hb (x 7 1)
            have b26115 := hb (x 8 14)
            clear * - r26113 b26114 b26115 d26108
            omega
          have d26116 : (x 7 13).toNat = 0 := by
            have r26117 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
            have b26118 := hb (x 7 1)
            have b26119 := hb (x 7 13)
            clear * - r26117 b26118 b26119 d26112
            omega
          have d26120 : (x 6 1 && x 6 14).toNat = 1 := by
            have r26121 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
            have b26122 := hb (x 5 2)
            have b26123 := hb (x 7 13)
            have b26124 := hb (x 6 1 && x 6 14)
            clear * - r26121 b26122 b26123 b26124 d26116 d26003
            omega
          have d26125 : (x 6 14).toNat = 1 := by
            have r26126 := hand2 (x 6 1) (x 6 14)
            have b26127 := hb (x 6 14)
            have b26128 := hb (x 6 1 && x 6 14)
            clear * - r26126 b26127 b26128 d26120
            omega
          have d26129 : (x 5 1).toNat = 0 := by
            have r26130 : (x 6 14).toNat + (x 5 1).toNat = 1 := hd14 6
            have b26131 := hb (x 5 1)
            have b26132 := hb (x 6 14)
            clear * - r26130 b26131 b26132 d26125
            omega
          have d26133 : (x 5 1 && x 5 12).toNat = 0 := by
            have r26134 := hand1 (x 5 1) (x 5 12)
            have b26135 := hb (x 5 1)
            have b26136 := hb (x 5 1 && x 5 12)
            clear * - r26134 b26135 b26136 d26129
            omega
          have d26137 : (x 6 11).toNat = 1 := by
            have r26138 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := hcov11 6
            have b26139 := hb (x 2 4)
            have b26140 := hb (x 6 11)
            have b26141 := hb (x 5 1 && x 5 12)
            have b26142 := hb (x 4 2 && x 4 13)
            have b26143 := hb (x 3 3 && x 3 14)
            clear * - r26138 b26139 b26140 b26141 b26142 b26143 d26133 d26015 g33 g16
            omega
          have d26144 : (x 6 3).toNat = 1 := by
            have r26145 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
            have b26146 := hb (x 6 3)
            have b26147 := hb (x 6 11)
            clear * - r26145 b26146 b26147 d26137
            omega
          have d26148 : (x 9 12).toNat = 0 := by
            have r26149 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
            have e26150 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
            have e26151 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
            have b26152 := hb (x 6 3)
            have b26153 := hb (x 7 2)
            have b26154 := hb (x 8 13)
            have b26155 := hb (x 9 12)
            clear * - r26149 e26150 e26151 b26152 b26153 b26154 b26155 d26036 d26144
            omega
          have d26156 : (x 9 1 && x 9 12).toNat = 0 := by
            have r26157 := hand2 (x 9 1) (x 9 12)
            have b26158 := hb (x 9 12)
            have b26159 := hb (x 9 1 && x 9 12)
            clear * - r26157 b26158 b26159 d26148
            omega
          have d26160 : (x 8 13).toNat = 0 := by
            have r26161 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
            have e26162 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
            have e26163 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
            have b26164 := hb (x 6 3)
            have b26165 := hb (x 7 2)
            have b26166 := hb (x 8 13)
            have b26167 := hb (x 9 12)
            clear * - r26161 e26162 e26163 b26164 b26165 b26166 b26167 d26148 d26036 d26144
            omega
          have d26168 : (x 8 2 && x 8 13).toNat = 0 := by
            have r26169 := hand2 (x 8 2) (x 8 13)
            have b26170 := hb (x 8 13)
            have b26171 := hb (x 8 2 && x 8 13)
            clear * - r26169 b26170 b26171 d26160
            omega
          have d26172 : (x 10 11).toNat = 1 := by
            have r26173 : 1 ≤ (x 10 11).toNat + (x 9 1 && x 9 12).toNat + (x 8 2 && x 8 13).toNat + (x 7 3 && x 7 14).toNat + (x 6 4).toNat := hcov11 10
            have b26174 := hb (x 6 4)
            have b26175 := hb (x 10 11)
            have b26176 := hb (x 9 1 && x 9 12)
            have b26177 := hb (x 8 2 && x 8 13)
            have b26178 := hb (x 7 3 && x 7 14)
            clear * - r26173 b26174 b26175 b26176 b26177 b26178 d26156 d26168 d26032 d25970
            omega
          have d26179 : (x 10 3).toNat = 1 := by
            have r26180 : (x 10 11).toNat ≤ (x 10 3).toNat := himp _ _ (hp11 10)
            have b26181 := hb (x 10 3)
            have b26182 := hb (x 10 11)
            clear * - r26180 b26181 b26182 d26172
            omega
          have d26183 : (x 13 12).toNat = 0 := by
            have r26184 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
            have e26185 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
            have e26186 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
            have b26187 := hb (x 10 3)
            have b26188 := hb (x 11 2)
            have b26189 := hb (x 12 13)
            have b26190 := hb (x 13 12)
            clear * - r26184 e26185 e26186 b26187 b26188 b26189 b26190 d26179
            omega
          have d26191 : (x 13 1 && x 13 12).toNat = 0 := by
            have r26192 := hand2 (x 13 1) (x 13 12)
            have b26193 := hb (x 13 12)
            have b26194 := hb (x 13 1 && x 13 12)
            clear * - r26192 b26193 b26194 d26183
            omega
          have d26195 : (x 12 13).toNat = 0 := by
            have r26196 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
            have e26197 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
            have e26198 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
            have b26199 := hb (x 10 3)
            have b26200 := hb (x 11 2)
            have b26201 := hb (x 12 13)
            have b26202 := hb (x 13 12)
            clear * - r26196 e26197 e26198 b26199 b26200 b26201 b26202 d26183 d26179
            omega
          have d26203 : (x 12 2 && x 12 13).toNat = 0 := by
            have r26204 := hand2 (x 12 2) (x 12 13)
            have b26205 := hb (x 12 13)
            have b26206 := hb (x 12 2 && x 12 13)
            clear * - r26204 b26205 b26206 d26195
            omega
          have d26207 : (x 11 2).toNat = 0 := by
            have r26208 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
            have e26209 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
            have e26210 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
            have b26211 := hb (x 10 3)
            have b26212 := hb (x 11 2)
            have b26213 := hb (x 12 13)
            have b26214 := hb (x 13 12)
            clear * - r26208 e26209 e26210 b26211 b26212 b26213 b26214 d26183 d26195 d26179
            omega
          have d26215 : (x 8 1).toNat = 1 := by
            have r26216 := hand1 (x 8 1) (x 8 14)
            have b26217 := hb (x 8 1)
            have b26218 := hb (x 8 1 && x 8 14)
            clear * - r26216 b26217 b26218 d26103
            omega
          have d26219 : (x 9 14).toNat = 0 := by
            have r26220 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
            have b26221 := hb (x 8 1)
            have b26222 := hb (x 9 14)
            clear * - r26220 b26221 b26222 d26215
            omega
          have d26223 : (x 9 1 && x 9 14).toNat = 0 := by
            have r26224 := hand2 (x 9 1) (x 9 14)
            have b26225 := hb (x 9 14)
            have b26226 := hb (x 9 1 && x 9 14)
            clear * - r26224 b26225 b26226 d26219
            omega
          have d26227 : (x 9 2).toNat = 0 := by
            have r26228 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
            have b26229 := hb (x 9 2)
            have b26230 := hb (x 9 14)
            clear * - r26228 b26229 b26230 d26219
            omega
          have d26231 : (x 8 2).toNat = 0 := by
            have r26232 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
            have e26233 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
            have e26234 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
            have b26235 := hb (x 7 3)
            have b26236 := hb (x 8 2)
            have b26237 := hb (x 9 13)
            have b26238 := hb (x 10 12)
            clear * - r26232 e26233 e26234 b26235 b26236 b26237 b26238 d26075 d26091 d26071
            omega
          have d26239 : (x 10 13).toNat = 1 := by
            have r26240 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := hcov13 10
            have b26241 := hb (x 8 2)
            have b26242 := hb (x 10 13)
            have b26243 := hb (x 9 1 && x 9 14)
            clear * - r26240 b26241 b26242 b26243 d26223 d26231
            omega
          have d26244 : (x 10 1).toNat = 1 := by
            have r26245 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
            have b26246 := hb (x 10 1)
            have b26247 := hb (x 10 13)
            clear * - r26245 b26246 b26247 d26239
            omega
          have d26248 : (x 11 14).toNat = 0 := by
            have r26249 : (x 11 14).toNat + (x 10 1).toNat = 1 := hd14 11
            have b26250 := hb (x 10 1)
            have b26251 := hb (x 11 14)
            clear * - r26249 b26250 b26251 d26244
            omega
          have d26252 : (x 11 1 && x 11 14).toNat = 0 := by
            have r26253 := hand2 (x 11 1) (x 11 14)
            have b26254 := hb (x 11 14)
            have b26255 := hb (x 11 1 && x 11 14)
            clear * - r26253 b26254 b26255 d26248
            omega
          have d26256 : (x 10 2).toNat = 1 := by
            have r26257 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := hcov13 12
            have b26258 := hb (x 10 2)
            have b26259 := hb (x 12 13)
            have b26260 := hb (x 11 1 && x 11 14)
            clear * - r26257 b26258 b26259 b26260 d26195 d26252
            omega
          have d26261 : (x 12 12).toNat = 0 := by
            have r26262 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
            have e26263 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
            have e26264 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
            have b26265 := hb (x 9 3)
            have b26266 := hb (x 10 2)
            have b26267 := hb (x 11 13)
            have b26268 := hb (x 12 12)
            clear * - r26262 e26263 e26264 b26265 b26266 b26267 b26268 d26256
            omega
          have d26269 : (x 12 4).toNat = 0 := by
            have r26270 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
            have b26271 := hb (x 12 4)
            have b26272 := hb (x 12 12)
            clear * - r26270 b26271 b26272 d26261
            omega
          have d26273 : (x 12 4 && x 12 14).toNat = 0 := by
            have r26274 := hand1 (x 12 4) (x 12 14)
            have b26275 := hb (x 12 4)
            have b26276 := hb (x 12 4 && x 12 14)
            clear * - r26274 b26275 b26276 d26269
            omega
          have d26277 : (x 11 13).toNat = 0 := by
            have r26278 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
            have e26279 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
            have e26280 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
            have b26281 := hb (x 9 3)
            have b26282 := hb (x 10 2)
            have b26283 := hb (x 11 13)
            have b26284 := hb (x 12 12)
            clear * - r26278 e26279 e26280 b26281 b26282 b26283 b26284 d26261 d26256
            omega
          have d26285 : (x 11 5).toNat = 0 := by
            have r26286 : (x 11 5).toNat ≤ (x 11 13).toNat := himp _ _ (hp5 11)
            have b26287 := hb (x 11 5)
            have b26288 := hb (x 11 13)
            clear * - r26286 b26287 b26288 d26277
            omega
          have d26289 : (x 11 3 && x 11 14).toNat = 0 := by
            have r26290 := hand2 (x 11 3) (x 11 14)
            have b26291 := hb (x 11 14)
            have b26292 := hb (x 11 3 && x 11 14)
            clear * - r26290 b26291 b26292 d26248
            omega
          have d26293 : (x 14 11).toNat = 1 := by
            have r26294 : 1 ≤ (x 14 11).toNat + (x 13 1 && x 13 12).toNat + (x 12 2 && x 12 13).toNat + (x 11 3 && x 11 14).toNat + (x 10 4).toNat := hcov11 14
            have b26295 := hb (x 10 4)
            have b26296 := hb (x 14 11)
            have b26297 := hb (x 13 1 && x 13 12)
            have b26298 := hb (x 12 2 && x 12 13)
            have b26299 := hb (x 11 3 && x 11 14)
            clear * - r26294 b26295 b26296 b26297 b26298 b26299 d26191 d26203 d26289 d26087
            omega
          have d26300 : (x 14 3).toNat = 1 := by
            have r26301 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
            have b26302 := hb (x 14 3)
            have b26303 := hb (x 14 11)
            clear * - r26301 b26302 b26303 d26293
            omega
          have d26304 : (x 17 12).toNat = 0 := by
            have r26305 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
            have e26306 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
            have e26307 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
            have b26308 := hb (x 14 3)
            have b26309 := hb (x 15 2)
            have b26310 := hb (x 16 13)
            have b26311 := hb (x 17 12)
            clear * - r26305 e26306 e26307 b26308 b26309 b26310 b26311 d26300
            omega
          have d26312 : (x 16 13).toNat = 0 := by
            have r26313 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
            have e26314 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
            have e26315 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
            have b26316 := hb (x 14 3)
            have b26317 := hb (x 15 2)
            have b26318 := hb (x 16 13)
            have b26319 := hb (x 17 12)
            clear * - r26313 e26314 e26315 b26316 b26317 b26318 b26319 d26304 d26300
            omega
          have d26320 : (x 15 2).toNat = 0 := by
            have r26321 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
            have e26322 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
            have e26323 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
            have b26324 := hb (x 14 3)
            have b26325 := hb (x 15 2)
            have b26326 := hb (x 16 13)
            have b26327 := hb (x 17 12)
            clear * - r26321 e26322 e26323 b26324 b26325 b26326 b26327 d26304 d26312 d26300
            omega
          have d26328 : (x 11 12).toNat = 0 := by
            have r26329 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
            have e26330 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
            have e26331 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
            have b26332 := hb (x 8 3)
            have b26333 := hb (x 9 2)
            have b26334 := hb (x 10 13)
            have b26335 := hb (x 11 12)
            clear * - r26329 e26330 e26331 b26332 b26333 b26334 b26335 d26239 d26227
            omega
          have d26336 : (x 11 4).toNat = 0 := by
            have r26337 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
            have b26338 := hb (x 11 4)
            have b26339 := hb (x 11 12)
            clear * - r26337 b26338 b26339 d26328
            omega
          have d26340 : (x 8 3).toNat = 0 := by
            have r26341 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
            have e26342 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
            have e26343 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
            have b26344 := hb (x 8 3)
            have b26345 := hb (x 9 2)
            have b26346 := hb (x 10 13)
            have b26347 := hb (x 11 12)
            clear * - r26341 e26342 e26343 b26344 b26345 b26346 b26347 d26328 d26239 d26227
            omega
          have d26348 : (x 8 3 && x 8 14).toNat = 0 := by
            have r26349 := hand1 (x 8 3) (x 8 14)
            have b26350 := hb (x 8 3)
            have b26351 := hb (x 8 3 && x 8 14)
            clear * - r26349 b26350 b26351 d26340
            omega
          have d26352 : (x 11 11).toNat = 1 := by
            have r26353 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := hcov11 11
            have b26354 := hb (x 7 4)
            have b26355 := hb (x 11 11)
            have b26356 := hb (x 10 1 && x 10 12)
            have b26357 := hb (x 9 2 && x 9 13)
            have b26358 := hb (x 8 3 && x 8 14)
            clear * - r26353 b26354 b26355 b26356 b26357 b26358 d26083 d26099 d26348 d26048
            omega
          have d26359 : (x 11 3).toNat = 1 := by
            have r26360 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
            have b26361 := hb (x 11 3)
            have b26362 := hb (x 11 11)
            clear * - r26360 b26361 b26362 d26352
            omega
          have d26363 : (x 14 12).toNat = 0 := by
            have r26364 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
            have e26365 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
            have e26366 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
            have b26367 := hb (x 11 3)
            have b26368 := hb (x 12 2)
            have b26369 := hb (x 13 13)
            have b26370 := hb (x 14 12)
            clear * - r26364 e26365 e26366 b26367 b26368 b26369 b26370 d26359
            omega
          have d26371 : (x 14 1 && x 14 12).toNat = 0 := by
            have r26372 := hand2 (x 14 1) (x 14 12)
            have b26373 := hb (x 14 12)
            have b26374 := hb (x 14 1 && x 14 12)
            clear * - r26372 b26373 b26374 d26363
            omega
          have d26375 : (x 14 2 && x 14 12).toNat = 0 := by
            have r26376 := hand2 (x 14 2) (x 14 12)
            have b26377 := hb (x 14 12)
            have b26378 := hb (x 14 2 && x 14 12)
            clear * - r26376 b26377 b26378 d26363
            omega
          have d26379 : (x 13 13).toNat = 0 := by
            have r26380 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
            have e26381 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
            have e26382 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
            have b26383 := hb (x 11 3)
            have b26384 := hb (x 12 2)
            have b26385 := hb (x 13 13)
            have b26386 := hb (x 14 12)
            clear * - r26380 e26381 e26382 b26383 b26384 b26385 b26386 d26363 d26359
            omega
          have d26387 : (x 13 2 && x 13 13).toNat = 0 := by
            have r26388 := hand2 (x 13 2) (x 13 13)
            have b26389 := hb (x 13 13)
            have b26390 := hb (x 13 2 && x 13 13)
            clear * - r26388 b26389 b26390 d26379
            omega
          have d26391 : (x 13 3 && x 13 13).toNat = 0 := by
            have r26392 := hand2 (x 13 3) (x 13 13)
            have b26393 := hb (x 13 13)
            have b26394 := hb (x 13 3 && x 13 13)
            clear * - r26392 b26393 b26394 d26379
            omega
          have d26395 : (x 12 1 && x 12 14).toNat = 1 := by
            have r26396 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := hcov13 13
            have b26397 := hb (x 11 2)
            have b26398 := hb (x 13 13)
            have b26399 := hb (x 12 1 && x 12 14)
            clear * - r26396 b26397 b26398 b26399 d26379 d26207
            omega
          have d26400 : (x 12 1).toNat = 1 := by
            have r26401 := hand1 (x 12 1) (x 12 14)
            have b26402 := hb (x 12 1)
            have b26403 := hb (x 12 1 && x 12 14)
            clear * - r26401 b26402 b26403 d26395
            omega
          have d26404 : (x 13 14).toNat = 0 := by
            have r26405 : (x 13 14).toNat + (x 12 1).toNat = 1 := hd14 13
            have b26406 := hb (x 12 1)
            have b26407 := hb (x 13 14)
            clear * - r26405 b26406 b26407 d26400
            omega
          have d26408 : (x 13 1 && x 13 14).toNat = 0 := by
            have r26409 := hand2 (x 13 1) (x 13 14)
            have b26410 := hb (x 13 14)
            have b26411 := hb (x 13 1 && x 13 14)
            clear * - r26409 b26410 b26411 d26404
            omega
          have d26412 : (x 13 2).toNat = 0 := by
            have r26413 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
            have b26414 := hb (x 13 2)
            have b26415 := hb (x 13 14)
            clear * - r26413 b26414 b26415 d26404
            omega
          have d26416 : (x 12 2).toNat = 0 := by
            have r26417 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
            have e26418 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
            have e26419 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
            have b26420 := hb (x 11 3)
            have b26421 := hb (x 12 2)
            have b26422 := hb (x 13 13)
            have b26423 := hb (x 14 12)
            clear * - r26417 e26418 e26419 b26420 b26421 b26422 b26423 d26363 d26379 d26359
            omega
          have d26424 : (x 14 13).toNat = 1 := by
            have r26425 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
            have b26426 := hb (x 12 2)
            have b26427 := hb (x 14 13)
            have b26428 := hb (x 13 1 && x 13 14)
            clear * - r26425 b26426 b26427 b26428 d26408 d26416
            omega
          have d26429 : (x 15 12).toNat = 0 := by
            have r26430 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
            have e26431 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
            have e26432 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
            have b26433 := hb (x 12 3)
            have b26434 := hb (x 13 2)
            have b26435 := hb (x 14 13)
            have b26436 := hb (x 15 12)
            clear * - r26430 e26431 e26432 b26433 b26434 b26435 b26436 d26424 d26412
            omega
          have d26437 : (x 12 3).toNat = 0 := by
            have r26438 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
            have e26439 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
            have e26440 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
            have b26441 := hb (x 12 3)
            have b26442 := hb (x 13 2)
            have b26443 := hb (x 14 13)
            have b26444 := hb (x 15 12)
            clear * - r26438 e26439 e26440 b26441 b26442 b26443 b26444 d26429 d26424 d26412
            omega
          have d26445 : (x 12 3 && x 12 14).toNat = 0 := by
            have r26446 := hand1 (x 12 3) (x 12 14)
            have b26447 := hb (x 12 3)
            have b26448 := hb (x 12 3 && x 12 14)
            clear * - r26446 b26447 b26448 d26437
            omega
          have d26449 : (x 15 11).toNat = 1 := by
            have r26450 : 1 ≤ (x 15 11).toNat + (x 14 1 && x 14 12).toNat + (x 13 2 && x 13 13).toNat + (x 12 3 && x 12 14).toNat + (x 11 4).toNat := hcov11 15
            have b26451 := hb (x 11 4)
            have b26452 := hb (x 15 11)
            have b26453 := hb (x 14 1 && x 14 12)
            have b26454 := hb (x 13 2 && x 13 13)
            have b26455 := hb (x 12 3 && x 12 14)
            clear * - r26450 b26451 b26452 b26453 b26454 b26455 d26371 d26387 d26445 d26336
            omega
          have d26456 : (x 15 3).toNat = 1 := by
            have r26457 : (x 15 11).toNat ≤ (x 15 3).toNat := himp _ _ (hp11 15)
            have b26458 := hb (x 15 3)
            have b26459 := hb (x 15 11)
            clear * - r26457 b26458 b26459 d26449
            omega
          have d26460 : (x 18 12).toNat = 0 := by
            have r26461 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
            have e26462 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
            have e26463 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
            have b26464 := hb (x 15 3)
            have b26465 := hb (x 16 2)
            have b26466 := hb (x 17 13)
            have b26467 := hb (x 18 12)
            clear * - r26461 e26462 e26463 b26464 b26465 b26466 b26467 d26456
            omega
          have d26468 : (x 17 13).toNat = 0 := by
            have r26469 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
            have e26470 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
            have e26471 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
            have b26472 := hb (x 15 3)
            have b26473 := hb (x 16 2)
            have b26474 := hb (x 17 13)
            have b26475 := hb (x 18 12)
            clear * - r26469 e26470 e26471 b26472 b26473 b26474 b26475 d26460 d26456
            omega
          have d26476 : (x 16 1 && x 16 14).toNat = 1 := by
            have r26477 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := hcov13 17
            have b26478 := hb (x 15 2)
            have b26479 := hb (x 17 13)
            have b26480 := hb (x 16 1 && x 16 14)
            clear * - r26477 b26478 b26479 b26480 d26468 d26320
            omega
          have d26481 : (x 16 14).toNat = 1 := by
            have r26482 := hand2 (x 16 1) (x 16 14)
            have b26483 := hb (x 16 14)
            have b26484 := hb (x 16 1 && x 16 14)
            clear * - r26482 b26483 b26484 d26476
            omega
          have d26485 : (x 15 1).toNat = 0 := by
            have r26486 : (x 16 14).toNat + (x 15 1).toNat = 1 := hd14 16
            have b26487 := hb (x 15 1)
            have b26488 := hb (x 16 14)
            clear * - r26486 b26487 b26488 d26481
            omega
          have d26489 : (x 15 1 && x 15 11).toNat = 0 := by
            have r26490 := hand1 (x 15 1) (x 15 11)
            have b26491 := hb (x 15 1)
            have b26492 := hb (x 15 1 && x 15 11)
            clear * - r26490 b26491 b26492 d26485
            omega
          have d26493 : (x 16 2).toNat = 0 := by
            have r26494 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
            have e26495 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
            have e26496 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
            have b26497 := hb (x 15 3)
            have b26498 := hb (x 16 2)
            have b26499 := hb (x 17 13)
            have b26500 := hb (x 18 12)
            clear * - r26494 e26495 e26496 b26497 b26498 b26499 b26500 d26460 d26468 d26456
            omega
          have d26501 : (x 16 10).toNat = 0 := by
            have r26502 : (x 16 10).toNat ≤ (x 16 2).toNat := himp _ _ (hp10 16)
            have b26503 := hb (x 16 2)
            have b26504 := hb (x 16 10)
            clear * - r26502 b26503 b26504 d26493
            omega
          have r26505 : 1 ≤ (x 16 10).toNat + (x 15 1 && x 15 11).toNat + (x 14 2 && x 14 12).toNat + (x 13 3 && x 13 13).toNat + (x 12 4 && x 12 14).toNat + (x 11 5).toNat := hcov10 16
          have b26506 := hb (x 11 5)
          have b26507 := hb (x 16 10)
          have b26508 := hb (x 15 1 && x 15 11)
          have b26509 := hb (x 14 2 && x 14 12)
          have b26510 := hb (x 13 3 && x 13 13)
          have b26511 := hb (x 12 4 && x 12 14)
          linarith only [r26505, b26506, b26507, b26508, b26509, b26510, b26511, d26501, d26489, d26375, d26391, d26273, d26285]
        · have f26512 : (x (-1) 4).toNat = 1 := by rw [h25945]; rfl
          have d26513 : (x (-1) 12).toNat = 1 := by
            have r26514 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
            have b26515 := hb (x (-1) 4)
            have b26516 := hb (x (-1) 12)
            clear * - r26514 b26515 b26516 f26512
            omega
          have d26517 : (x (-3) 2).toNat = 0 := by
            have r26518 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
            have e26519 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e26520 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b26521 := hb (x (-4) 3)
            have b26522 := hb (x (-3) 2)
            have b26523 := hb (x (-2) 13)
            have b26524 := hb (x (-1) 12)
            clear * - r26518 e26519 e26520 b26521 b26522 b26523 b26524 d26513 g3
            omega
          have d26525 : (x (-3) 10).toNat = 0 := by
            have r26526 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
            have b26527 := hb (x (-3) 2)
            have b26528 := hb (x (-3) 10)
            clear * - r26526 b26527 b26528 d26517
            omega
          have d26529 : (x (-3) 4 && x (-3) 10).toNat = 0 := by
            have r26530 := hand2 (x (-3) 4) (x (-3) 10)
            have b26531 := hb (x (-3) 10)
            have b26532 := hb (x (-3) 4 && x (-3) 10)
            clear * - r26530 b26531 b26532 d26525
            omega
          have d26533 : (x (-3) 6 && x (-3) 10).toNat = 0 := by
            have r26534 := hand2 (x (-3) 6) (x (-3) 10)
            have b26535 := hb (x (-3) 10)
            have b26536 := hb (x (-3) 6 && x (-3) 10)
            clear * - r26534 b26535 b26536 d26525
            omega
          have d26537 : (x (-4) 3).toNat = 0 := by
            have r26538 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
            have e26539 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e26540 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b26541 := hb (x (-4) 3)
            have b26542 := hb (x (-3) 2)
            have b26543 := hb (x (-2) 13)
            have b26544 := hb (x (-1) 12)
            clear * - r26538 e26539 e26540 b26541 b26542 b26543 b26544 d26513 g3 d26517
            omega
          have d26545 : (x (-4) 11).toNat = 0 := by
            have r26546 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
            have b26547 := hb (x (-4) 3)
            have b26548 := hb (x (-4) 11)
            clear * - r26546 b26547 b26548 d26537
            omega
          have d26549 : (x (-4) 5 && x (-4) 11).toNat = 0 := by
            have r26550 := hand2 (x (-4) 5) (x (-4) 11)
            have b26551 := hb (x (-4) 11)
            have b26552 := hb (x (-4) 5 && x (-4) 11)
            clear * - r26550 b26551 b26552 d26545
            omega
          have d26553 : (x (-4) 7 && x (-4) 11).toNat = 0 := by
            have r26554 := hand2 (x (-4) 7) (x (-4) 11)
            have b26555 := hb (x (-4) 11)
            have b26556 := hb (x (-4) 7 && x (-4) 11)
            clear * - r26554 b26555 b26556 d26545
            omega
          have d26557 : (x 3 8).toNat = 0 := by
            have r26558 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := hd8 3
            have e26559 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
            have e26560 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
            have e26561 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
            have e26562 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
            have e26563 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
            have e26564 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
            have b26565 := hb (x (-4) 7)
            have b26566 := hb (x (-3) 6)
            have b26567 := hb (x (-2) 5)
            have b26568 := hb (x (-1) 4)
            have b26569 := hb (x 0 11)
            have b26570 := hb (x 1 10)
            have b26571 := hb (x 2 9)
            have b26572 := hb (x 3 8)
            clear * - r26558 e26559 e26560 e26561 e26562 e26563 e26564 b26565 b26566 b26567 b26568 b26569 b26570 b26571 b26572 g14 g10 f26512 g1
            omega
          have d26573 : (x 2 9).toNat = 0 := by
            have r26574 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := hd8 3
            have e26575 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
            have e26576 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
            have e26577 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
            have e26578 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
            have e26579 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
            have e26580 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
            have b26581 := hb (x (-4) 7)
            have b26582 := hb (x (-3) 6)
            have b26583 := hb (x (-2) 5)
            have b26584 := hb (x (-1) 4)
            have b26585 := hb (x 0 11)
            have b26586 := hb (x 1 10)
            have b26587 := hb (x 2 9)
            have b26588 := hb (x 3 8)
            clear * - r26574 e26575 e26576 e26577 e26578 e26579 e26580 b26581 b26582 b26583 b26584 b26585 b26586 b26587 b26588 d26557 g14 g10 f26512 g1
            omega
          have d26589 : (x (-3) 6).toNat = 0 := by
            have r26590 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := hd8 3
            have e26591 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
            have e26592 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
            have e26593 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
            have e26594 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
            have e26595 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
            have e26596 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
            have b26597 := hb (x (-4) 7)
            have b26598 := hb (x (-3) 6)
            have b26599 := hb (x (-2) 5)
            have b26600 := hb (x (-1) 4)
            have b26601 := hb (x 0 11)
            have b26602 := hb (x 1 10)
            have b26603 := hb (x 2 9)
            have b26604 := hb (x 3 8)
            clear * - r26590 e26591 e26592 e26593 e26594 e26595 e26596 b26597 b26598 b26599 b26600 b26601 b26602 b26603 b26604 d26557 d26573 g14 g10 f26512 g1
            omega
          have d26605 : (x (-4) 7).toNat = 0 := by
            have r26606 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := hd8 3
            have e26607 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
            have e26608 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
            have e26609 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
            have e26610 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
            have e26611 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
            have e26612 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
            have b26613 := hb (x (-4) 7)
            have b26614 := hb (x (-3) 6)
            have b26615 := hb (x (-2) 5)
            have b26616 := hb (x (-1) 4)
            have b26617 := hb (x 0 11)
            have b26618 := hb (x 1 10)
            have b26619 := hb (x 2 9)
            have b26620 := hb (x 3 8)
            clear * - r26606 e26607 e26608 e26609 e26610 e26611 e26612 b26613 b26614 b26615 b26616 b26617 b26618 b26619 b26620 d26557 d26573 g14 g10 f26512 g1 d26589
            omega
          have r26621 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := hcount 1
          have r26622 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := hcount 3
          have r26623 : (x 6 1).toNat + (x 5 2).toNat + (x 4 3).toNat + (x 3 4).toNat + (x 2 5).toNat + (x 1 6).toNat + (x 0 7).toNat + (x (-1) 8).toNat + (x (-2) 9).toNat + (x (-3) 10).toNat + (x (-4) 11).toNat + (x (-5) 12).toNat + (x (-6) 13).toNat + (x (-7) 14).toNat = 3 := hcount 7
          have r26624 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
          have e26625 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e26626 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e26627 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e26628 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e26629 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e26630 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have r26631 : (x (-12) 12).toNat + (x (-13) 1 && x (-13) 13).toNat + (x (-14) 2 && x (-14) 14).toNat + (x (-15) 3).toNat = 1 := hd12 (-12)
          have e26632 : (x (-13) 1 && x (-13) 13).toNat = (x (-13) 13).toNat := handr _ _ (fun h => hp13 (-13) (h))
          have e26633 : (x (-14) 2 && x (-14) 14).toNat = (x (-14) 2).toNat := handl _ _ (fun h => hp2 (-14) (h))
          have r26634 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := hd12 (-5)
          have e26635 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
          have e26636 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
          have r26637 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
          have e26638 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
          have e26639 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
          have r26640 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := hd14 (-7)
          have r26641 : 1 ≤ (x 3 4).toNat + (x 2 1 && x 2 5).toNat + (x 1 2 && x 1 6).toNat + (x 0 3 && x 0 7).toNat + (x (-1) 4 && x (-1) 8).toNat + (x (-2) 5 && x (-2) 9).toNat + (x (-3) 6 && x (-3) 10).toNat + (x (-4) 7 && x (-4) 11).toNat + (x (-5) 8 && x (-5) 12).toNat + (x (-6) 9 && x (-6) 13).toNat + (x (-7) 10 && x (-7) 14).toNat + (x (-8) 11).toNat := hcov4 3
          have e26642 : (x 2 1 && x 2 5).toNat = (x 2 5).toNat := handr _ _ (fun h => hp13 2 (hp5 2 (h)))
          have e26643 : (x (-7) 10 && x (-7) 14).toNat = (x (-7) 10).toNat := handl _ _ (fun h => hp2 (-7) (hp10 (-7) (h)))
          have r26644 : 1 ≤ (x 1 6).toNat + (x 0 1 && x 0 7).toNat + (x (-1) 2 && x (-1) 8).toNat + (x (-2) 3 && x (-2) 9).toNat + (x (-3) 4 && x (-3) 10).toNat + (x (-4) 5 && x (-4) 11).toNat + (x (-5) 6 && x (-5) 12).toNat + (x (-6) 7 && x (-6) 13).toNat + (x (-7) 8 && x (-7) 14).toNat + (x (-8) 9).toNat := hcov6 1
          have r26645 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := hcov9 6
          have r26646 : 1 ≤ (x (-7) 10).toNat + (x (-8) 1 && x (-8) 11).toNat + (x (-9) 2 && x (-9) 12).toNat + (x (-10) 3 && x (-10) 13).toNat + (x (-11) 4 && x (-11) 14).toNat + (x (-12) 5).toNat := hcov10 (-7)
          have r26647 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := hcov11 (-8)
          have r26648 : 1 ≤ (x (-12) 13).toNat + (x (-13) 1 && x (-13) 14).toNat + (x (-14) 2).toNat := hcov13 (-12)
          have r26649 : (x (-12) 4).toNat ≤ (x (-12) 12).toNat := himp _ _ (hp4 (-12))
          have r26650 : (x (-12) 5).toNat ≤ (x (-12) 13).toNat := himp _ _ (hp5 (-12))
          have r26651 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
          have r26652 := hand1 (x (-5) 8) (x (-5) 12)
          have r26653 := hand1 (x (-6) 9) (x (-6) 13)
          have r26654 := hand1 (x (-5) 6) (x (-5) 12)
          have r26655 := hand1 (x (-6) 7) (x (-6) 13)
          have r26656 := hand1 (x (-7) 8) (x (-7) 14)
          have r26657 := hand2 (x 5 1) (x 5 10)
          have r26658 := hand2 (x 4 2) (x 4 11)
          have r26659 := hand1 (x (-8) 1) (x (-8) 11)
          have r26660 := hand2 (x (-9) 2) (x (-9) 12)
          have r26661 := hand2 (x (-10) 3) (x (-10) 13)
          have r26662 := hand2 (x (-11) 4) (x (-11) 14)
          have r26663 := hand2 (x (-9) 1) (x (-9) 12)
          have r26664 := hand2 (x (-10) 2) (x (-10) 13)
          have r26665 := hand2 (x (-11) 3) (x (-11) 14)
          have r26666 := hand2 (x (-13) 1) (x (-13) 14)
          have b26667 := hb (x (-15) 3)
          have b26668 := hb (x (-14) 2)
          have b26669 := hb (x (-13) 13)
          have b26670 := hb (x (-13) 14)
          have b26671 := hb (x (-12) 4)
          have b26672 := hb (x (-12) 5)
          have b26673 := hb (x (-12) 12)
          have b26674 := hb (x (-12) 13)
          have b26675 := hb (x (-11) 12)
          have b26676 := hb (x (-11) 14)
          have b26677 := hb (x (-10) 11)
          have b26678 := hb (x (-10) 13)
          have b26679 := hb (x (-9) 10)
          have b26680 := hb (x (-9) 12)
          have b26681 := hb (x (-8) 1)
          have b26682 := hb (x (-8) 3)
          have b26683 := hb (x (-8) 9)
          have b26684 := hb (x (-8) 11)
          have b26685 := hb (x (-7) 2)
          have b26686 := hb (x (-7) 8)
          have b26687 := hb (x (-7) 10)
          have b26688 := hb (x (-7) 14)
          have b26689 := hb (x (-6) 7)
          have b26690 := hb (x (-6) 9)
          have b26691 := hb (x (-6) 13)
          have b26692 := hb (x (-5) 6)
          have b26693 := hb (x (-5) 8)
          have b26694 := hb (x (-5) 12)
          have b26695 := hb (x (-4) 5)
          have b26696 := hb (x (-4) 7)
          have b26697 := hb (x (-4) 11)
          have b26698 := hb (x (-3) 4)
          have b26699 := hb (x (-3) 6)
          have b26700 := hb (x (-3) 10)
          have b26701 := hb (x (-2) 3)
          have b26702 := hb (x (-2) 5)
          have b26703 := hb (x (-2) 9)
          have b26704 := hb (x (-1) 2)
          have b26705 := hb (x (-1) 4)
          have b26706 := hb (x (-1) 8)
          have b26707 := hb (x 0 1)
          have b26708 := hb (x 0 3)
          have b26709 := hb (x 0 6)
          have b26710 := hb (x 0 7)
          have b26711 := hb (x 1 2)
          have b26712 := hb (x 1 6)
          have b26713 := hb (x 2 1)
          have b26714 := hb (x 2 5)
          have b26715 := hb (x 3 4)
          have b26716 := hb (x 4 3)
          have b26717 := hb (x 4 11)
          have b26718 := hb (x 5 2)
          have b26719 := hb (x 5 10)
          have b26720 := hb (x 6 1)
          have b26721 := hb (x 6 9)
          have b26722 := hb (x 6 13)
          have b26723 := hb (x 7 8)
          have b26724 := hb (x 7 12)
          have b26725 := hb (x 1 2 && x 1 6)
          have b26726 := hb (x 0 3 && x 0 7)
          have b26727 := hb (x (-1) 4 && x (-1) 8)
          have b26728 := hb (x (-2) 5 && x (-2) 9)
          have b26729 := hb (x (-3) 6 && x (-3) 10)
          have b26730 := hb (x (-4) 7 && x (-4) 11)
          have b26731 := hb (x (-5) 8 && x (-5) 12)
          have b26732 := hb (x (-6) 9 && x (-6) 13)
          have b26733 := hb (x 0 1 && x 0 7)
          have b26734 := hb (x (-1) 2 && x (-1) 8)
          have b26735 := hb (x (-2) 3 && x (-2) 9)
          have b26736 := hb (x (-3) 4 && x (-3) 10)
          have b26737 := hb (x (-4) 5 && x (-4) 11)
          have b26738 := hb (x (-5) 6 && x (-5) 12)
          have b26739 := hb (x (-6) 7 && x (-6) 13)
          have b26740 := hb (x (-7) 8 && x (-7) 14)
          have b26741 := hb (x 5 1 && x 5 10)
          have b26742 := hb (x 4 2 && x 4 11)
          have b26743 := hb (x 3 3 && x 3 12)
          have b26744 := hb (x 2 4 && x 2 13)
          have b26745 := hb (x 1 5 && x 1 14)
          have b26746 := hb (x (-8) 1 && x (-8) 11)
          have b26747 := hb (x (-9) 2 && x (-9) 12)
          have b26748 := hb (x (-10) 3 && x (-10) 13)
          have b26749 := hb (x (-11) 4 && x (-11) 14)
          have b26750 := hb (x (-9) 1 && x (-9) 12)
          have b26751 := hb (x (-10) 2 && x (-10) 13)
          have b26752 := hb (x (-11) 3 && x (-11) 14)
          have b26753 := hb (x (-13) 1 && x (-13) 14)
          linarith only [r26621, r26622, r26623, r26624, e26625, e26626, e26627, e26628, e26629, e26630, r26631, e26632, e26633, r26634, e26635, e26636, r26637, e26638, e26639, r26640, r26641, e26642, e26643, r26644, r26645, r26646, r26647, r26648, r26649, r26650, r26651, r26652, r26653, r26654, r26655, r26656, r26657, r26658, r26659, r26660, r26661, r26662, r26663, r26664, r26665, r26666, b26667, b26668, b26669, b26670, b26671, b26672, b26673, b26674, b26675, b26676, b26677, b26678, b26679, b26680, b26681, b26682, b26683, b26684, b26685, b26686, b26687, b26688, b26689, b26690, b26691, b26692, b26693, b26694, b26695, b26696, b26697, b26698, b26699, b26700, b26701, b26702, b26703, b26704, b26705, b26706, b26707, b26708, b26709, b26710, b26711, b26712, b26713, b26714, b26715, b26716, b26717, b26718, b26719, b26720, b26721, b26722, b26723, b26724, b26725, b26726, b26727, b26728, b26729, b26730, b26731, b26732, b26733, b26734, b26735, b26736, b26737, b26738, b26739, b26740, b26741, b26742, b26743, b26744, b26745, b26746, b26747, b26748, b26749, b26750, b26751, b26752, b26753, d26605, d26545, d26589, d26525, g0, g1, g2, g4, f26512, g5, g6, g7, g8, g9, g11, g13, g15, g18, g19, g20, g21, g22, d26533, d26553, g23, g24, g25, d26529, d26549, g26, g27, g28]
      · have f26754 : (x 1 3).toNat = 1 := by rw [h25943]; rfl
        have d26755 : (x 4 12).toNat = 0 := by
          have r26756 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
          have e26757 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e26758 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b26759 := hb (x 1 3)
          have b26760 := hb (x 2 2)
          have b26761 := hb (x 3 13)
          have b26762 := hb (x 4 12)
          clear * - r26756 e26757 e26758 b26759 b26760 b26761 b26762 f26754
          omega
        have d26763 : (x 4 1 && x 4 12).toNat = 0 := by
          have r26764 := hand2 (x 4 1) (x 4 12)
          have b26765 := hb (x 4 12)
          have b26766 := hb (x 4 1 && x 4 12)
          clear * - r26764 b26765 b26766 d26755
          omega
        have d26767 : (x 4 4).toNat = 0 := by
          have r26768 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
          have b26769 := hb (x 4 4)
          have b26770 := hb (x 4 12)
          clear * - r26768 b26769 b26770 d26755
          omega
        have d26771 : (x 3 13).toNat = 0 := by
          have r26772 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
          have e26773 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e26774 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b26775 := hb (x 1 3)
          have b26776 := hb (x 2 2)
          have b26777 := hb (x 3 13)
          have b26778 := hb (x 4 12)
          clear * - r26772 e26773 e26774 b26775 b26776 b26777 b26778 d26755 f26754
          omega
        have d26779 : (x 2 2).toNat = 0 := by
          have r26780 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
          have e26781 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e26782 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b26783 := hb (x 1 3)
          have b26784 := hb (x 2 2)
          have b26785 := hb (x 3 13)
          have b26786 := hb (x 4 12)
          clear * - r26780 e26781 e26782 b26783 b26784 b26785 b26786 d26755 d26771 f26754
          omega
        have d26787 : (x 4 13).toNat = 1 := by
          have r26788 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
          have b26789 := hb (x 2 2)
          have b26790 := hb (x 4 13)
          have b26791 := hb (x 3 1 && x 3 14)
          clear * - r26788 b26789 b26790 b26791 g35 d26779
          omega
        have d26792 : (x 4 1).toNat = 1 := by
          have r26793 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
          have b26794 := hb (x 4 1)
          have b26795 := hb (x 4 13)
          clear * - r26793 b26794 b26795 d26787
          omega
        have d26796 : (x 5 14).toNat = 0 := by
          have r26797 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
          have b26798 := hb (x 4 1)
          have b26799 := hb (x 5 14)
          clear * - r26797 b26798 b26799 d26792
          omega
        have d26800 : (x 5 3 && x 5 14).toNat = 0 := by
          have r26801 := hand2 (x 5 3) (x 5 14)
          have b26802 := hb (x 5 14)
          have b26803 := hb (x 5 3 && x 5 14)
          clear * - r26801 b26802 b26803 d26796
          omega
        have d26804 : (x 5 2).toNat = 0 := by
          have r26805 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
          have b26806 := hb (x 5 2)
          have b26807 := hb (x 5 14)
          clear * - r26805 b26806 b26807 d26796
          omega
        have d26808 : (x 5 12).toNat = 0 := by
          have r26809 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
          have e26810 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e26811 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b26812 := hb (x 2 3)
          have b26813 := hb (x 3 2)
          have b26814 := hb (x 4 13)
          have b26815 := hb (x 5 12)
          clear * - r26809 e26810 e26811 b26812 b26813 b26814 b26815 d26787 g17
          omega
        have d26816 : (x 5 4).toNat = 0 := by
          have r26817 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
          have b26818 := hb (x 5 4)
          have b26819 := hb (x 5 12)
          clear * - r26817 b26818 b26819 d26808
          omega
        have d26820 : (x 2 3).toNat = 0 := by
          have r26821 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
          have e26822 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e26823 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b26824 := hb (x 2 3)
          have b26825 := hb (x 3 2)
          have b26826 := hb (x 4 13)
          have b26827 := hb (x 5 12)
          clear * - r26821 e26822 e26823 b26824 b26825 b26826 b26827 d26808 d26787 g17
          omega
        have d26828 : (x 2 3 && x 2 14).toNat = 0 := by
          have r26829 := hand1 (x 2 3) (x 2 14)
          have b26830 := hb (x 2 3)
          have b26831 := hb (x 2 3 && x 2 14)
          clear * - r26829 b26830 b26831 d26820
          omega
        have d26832 : (x 5 11).toNat = 1 := by
          have r26833 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := hcov11 5
          have b26834 := hb (x 1 4)
          have b26835 := hb (x 5 11)
          have b26836 := hb (x 4 1 && x 4 12)
          have b26837 := hb (x 3 2 && x 3 13)
          have b26838 := hb (x 2 3 && x 2 14)
          clear * - r26833 b26834 b26835 b26836 b26837 b26838 d26763 g32 d26828 g12
          omega
        have d26839 : (x 5 3).toNat = 1 := by
          have r26840 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
          have b26841 := hb (x 5 3)
          have b26842 := hb (x 5 11)
          clear * - r26840 b26841 b26842 d26832
          omega
        have d26843 : (x 8 12).toNat = 0 := by
          have r26844 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
          have e26845 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
          have e26846 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
          have b26847 := hb (x 5 3)
          have b26848 := hb (x 6 2)
          have b26849 := hb (x 7 13)
          have b26850 := hb (x 8 12)
          clear * - r26844 e26845 e26846 b26847 b26848 b26849 b26850 d26839
          omega
        have d26851 : (x 8 1 && x 8 12).toNat = 0 := by
          have r26852 := hand2 (x 8 1) (x 8 12)
          have b26853 := hb (x 8 12)
          have b26854 := hb (x 8 1 && x 8 12)
          clear * - r26852 b26853 b26854 d26843
          omega
        have d26855 : (x 8 4).toNat = 0 := by
          have r26856 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
          have b26857 := hb (x 8 4)
          have b26858 := hb (x 8 12)
          clear * - r26856 b26857 b26858 d26843
          omega
        have d26859 : (x 7 13).toNat = 0 := by
          have r26860 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
          have e26861 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
          have e26862 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
          have b26863 := hb (x 5 3)
          have b26864 := hb (x 6 2)
          have b26865 := hb (x 7 13)
          have b26866 := hb (x 8 12)
          clear * - r26860 e26861 e26862 b26863 b26864 b26865 b26866 d26843 d26839
          omega
        have d26867 : (x 7 2 && x 7 13).toNat = 0 := by
          have r26868 := hand2 (x 7 2) (x 7 13)
          have b26869 := hb (x 7 13)
          have b26870 := hb (x 7 2 && x 7 13)
          clear * - r26868 b26869 b26870 d26859
          omega
        have d26871 : (x 6 1 && x 6 14).toNat = 1 := by
          have r26872 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
          have b26873 := hb (x 5 2)
          have b26874 := hb (x 7 13)
          have b26875 := hb (x 6 1 && x 6 14)
          clear * - r26872 b26873 b26874 b26875 d26859 d26804
          omega
        have d26876 : (x 6 1).toNat = 1 := by
          have r26877 := hand1 (x 6 1) (x 6 14)
          have b26878 := hb (x 6 1)
          have b26879 := hb (x 6 1 && x 6 14)
          clear * - r26877 b26878 b26879 d26871
          omega
        have d26880 : (x 7 14).toNat = 0 := by
          have r26881 : (x 7 14).toNat + (x 6 1).toNat = 1 := hd14 7
          have b26882 := hb (x 6 1)
          have b26883 := hb (x 7 14)
          clear * - r26881 b26882 b26883 d26876
          omega
        have d26884 : (x 7 1 && x 7 14).toNat = 0 := by
          have r26885 := hand2 (x 7 1) (x 7 14)
          have b26886 := hb (x 7 14)
          have b26887 := hb (x 7 1 && x 7 14)
          clear * - r26885 b26886 b26887 d26880
          omega
        have d26888 : (x 7 2).toNat = 0 := by
          have r26889 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
          have b26890 := hb (x 7 2)
          have b26891 := hb (x 7 14)
          clear * - r26889 b26890 b26891 d26880
          omega
        have d26892 : (x 6 2).toNat = 0 := by
          have r26893 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
          have e26894 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
          have e26895 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
          have b26896 := hb (x 5 3)
          have b26897 := hb (x 6 2)
          have b26898 := hb (x 7 13)
          have b26899 := hb (x 8 12)
          clear * - r26893 e26894 e26895 b26896 b26897 b26898 b26899 d26843 d26859 d26839
          omega
        have d26900 : (x 6 2 && x 6 13).toNat = 0 := by
          have r26901 := hand1 (x 6 2) (x 6 13)
          have b26902 := hb (x 6 2)
          have b26903 := hb (x 6 2 && x 6 13)
          clear * - r26901 b26902 b26903 d26892
          omega
        have d26904 : (x 8 13).toNat = 1 := by
          have r26905 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := hcov13 8
          have b26906 := hb (x 6 2)
          have b26907 := hb (x 8 13)
          have b26908 := hb (x 7 1 && x 7 14)
          clear * - r26905 b26906 b26907 b26908 d26884 d26892
          omega
        have d26909 : (x 8 1).toNat = 1 := by
          have r26910 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
          have b26911 := hb (x 8 1)
          have b26912 := hb (x 8 13)
          clear * - r26910 b26911 b26912 d26904
          omega
        have d26913 : (x 9 14).toNat = 0 := by
          have r26914 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
          have b26915 := hb (x 8 1)
          have b26916 := hb (x 9 14)
          clear * - r26914 b26915 b26916 d26909
          omega
        have d26917 : (x 9 3 && x 9 14).toNat = 0 := by
          have r26918 := hand2 (x 9 3) (x 9 14)
          have b26919 := hb (x 9 14)
          have b26920 := hb (x 9 3 && x 9 14)
          clear * - r26918 b26919 b26920 d26913
          omega
        have d26921 : (x 9 2).toNat = 0 := by
          have r26922 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
          have b26923 := hb (x 9 2)
          have b26924 := hb (x 9 14)
          clear * - r26922 b26923 b26924 d26913
          omega
        have d26925 : (x 9 12).toNat = 0 := by
          have r26926 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
          have e26927 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
          have e26928 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
          have b26929 := hb (x 6 3)
          have b26930 := hb (x 7 2)
          have b26931 := hb (x 8 13)
          have b26932 := hb (x 9 12)
          clear * - r26926 e26927 e26928 b26929 b26930 b26931 b26932 d26904 d26888
          omega
        have d26933 : (x 9 4).toNat = 0 := by
          have r26934 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
          have b26935 := hb (x 9 4)
          have b26936 := hb (x 9 12)
          clear * - r26934 b26935 b26936 d26925
          omega
        have d26937 : (x 6 3).toNat = 0 := by
          have r26938 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
          have e26939 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
          have e26940 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
          have b26941 := hb (x 6 3)
          have b26942 := hb (x 7 2)
          have b26943 := hb (x 8 13)
          have b26944 := hb (x 9 12)
          clear * - r26938 e26939 e26940 b26941 b26942 b26943 b26944 d26925 d26904 d26888
          omega
        have d26945 : (x 6 3 && x 6 14).toNat = 0 := by
          have r26946 := hand1 (x 6 3) (x 6 14)
          have b26947 := hb (x 6 3)
          have b26948 := hb (x 6 3 && x 6 14)
          clear * - r26946 b26947 b26948 d26937
          omega
        have d26949 : (x 9 11).toNat = 1 := by
          have r26950 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := hcov11 9
          have b26951 := hb (x 5 4)
          have b26952 := hb (x 9 11)
          have b26953 := hb (x 8 1 && x 8 12)
          have b26954 := hb (x 7 2 && x 7 13)
          have b26955 := hb (x 6 3 && x 6 14)
          clear * - r26950 b26951 b26952 b26953 b26954 b26955 d26851 d26867 d26945 d26816
          omega
        have d26956 : (x 9 3).toNat = 1 := by
          have r26957 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
          have b26958 := hb (x 9 3)
          have b26959 := hb (x 9 11)
          clear * - r26957 b26958 b26959 d26949
          omega
        have d26960 : (x 12 12).toNat = 0 := by
          have r26961 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
          have e26962 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
          have e26963 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
          have b26964 := hb (x 9 3)
          have b26965 := hb (x 10 2)
          have b26966 := hb (x 11 13)
          have b26967 := hb (x 12 12)
          clear * - r26961 e26962 e26963 b26964 b26965 b26966 b26967 d26956
          omega
        have d26968 : (x 12 1 && x 12 12).toNat = 0 := by
          have r26969 := hand2 (x 12 1) (x 12 12)
          have b26970 := hb (x 12 12)
          have b26971 := hb (x 12 1 && x 12 12)
          clear * - r26969 b26970 b26971 d26960
          omega
        have d26972 : (x 12 4).toNat = 0 := by
          have r26973 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
          have b26974 := hb (x 12 4)
          have b26975 := hb (x 12 12)
          clear * - r26973 b26974 b26975 d26960
          omega
        have d26976 : (x 11 13).toNat = 0 := by
          have r26977 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
          have e26978 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
          have e26979 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
          have b26980 := hb (x 9 3)
          have b26981 := hb (x 10 2)
          have b26982 := hb (x 11 13)
          have b26983 := hb (x 12 12)
          clear * - r26977 e26978 e26979 b26980 b26981 b26982 b26983 d26960 d26956
          omega
        have d26984 : (x 11 2 && x 11 13).toNat = 0 := by
          have r26985 := hand2 (x 11 2) (x 11 13)
          have b26986 := hb (x 11 13)
          have b26987 := hb (x 11 2 && x 11 13)
          clear * - r26985 b26986 b26987 d26976
          omega
        have d26988 : (x 10 1 && x 10 14).toNat = 1 := by
          have r26989 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := hcov13 11
          have b26990 := hb (x 9 2)
          have b26991 := hb (x 11 13)
          have b26992 := hb (x 10 1 && x 10 14)
          clear * - r26989 b26990 b26991 b26992 d26976 d26921
          omega
        have d26993 : (x 10 14).toNat = 1 := by
          have r26994 := hand2 (x 10 1) (x 10 14)
          have b26995 := hb (x 10 14)
          have b26996 := hb (x 10 1 && x 10 14)
          clear * - r26994 b26995 b26996 d26988
          omega
        have d26997 : (x 9 1).toNat = 0 := by
          have r26998 : (x 10 14).toNat + (x 9 1).toNat = 1 := hd14 10
          have b26999 := hb (x 9 1)
          have b27000 := hb (x 10 14)
          clear * - r26998 b26999 b27000 d26993
          omega
        have d27001 : (x 9 13).toNat = 0 := by
          have r27002 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
          have b27003 := hb (x 9 1)
          have b27004 := hb (x 9 13)
          clear * - r27002 b27003 b27004 d26997
          omega
        have d27005 : (x 8 1 && x 8 14).toNat = 1 := by
          have r27006 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := hcov13 9
          have b27007 := hb (x 7 2)
          have b27008 := hb (x 9 13)
          have b27009 := hb (x 8 1 && x 8 14)
          clear * - r27006 b27007 b27008 b27009 d27001 d26888
          omega
        have d27010 : (x 8 14).toNat = 1 := by
          have r27011 := hand2 (x 8 1) (x 8 14)
          have b27012 := hb (x 8 14)
          have b27013 := hb (x 8 1 && x 8 14)
          clear * - r27011 b27012 b27013 d27005
          omega
        have d27014 : (x 7 1).toNat = 0 := by
          have r27015 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
          have b27016 := hb (x 7 1)
          have b27017 := hb (x 8 14)
          clear * - r27015 b27016 b27017 d27010
          omega
        have d27018 : (x 7 1 && x 7 12).toNat = 0 := by
          have r27019 := hand1 (x 7 1) (x 7 12)
          have b27020 := hb (x 7 1)
          have b27021 := hb (x 7 1 && x 7 12)
          clear * - r27019 b27020 b27021 d27014
          omega
        have d27022 : (x 8 11).toNat = 1 := by
          have r27023 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := hcov11 8
          have b27024 := hb (x 4 4)
          have b27025 := hb (x 8 11)
          have b27026 := hb (x 7 1 && x 7 12)
          have b27027 := hb (x 6 2 && x 6 13)
          have b27028 := hb (x 5 3 && x 5 14)
          clear * - r27023 b27024 b27025 b27026 b27027 b27028 d27018 d26900 d26800 d26767
          omega
        have d27029 : (x 8 3).toNat = 1 := by
          have r27030 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
          have b27031 := hb (x 8 3)
          have b27032 := hb (x 8 11)
          clear * - r27030 b27031 b27032 d27022
          omega
        have d27033 : (x 11 12).toNat = 0 := by
          have r27034 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
          have e27035 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e27036 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have b27037 := hb (x 8 3)
          have b27038 := hb (x 9 2)
          have b27039 := hb (x 10 13)
          have b27040 := hb (x 11 12)
          clear * - r27034 e27035 e27036 b27037 b27038 b27039 b27040 d26921 d27029
          omega
        have d27041 : (x 11 1 && x 11 12).toNat = 0 := by
          have r27042 := hand2 (x 11 1) (x 11 12)
          have b27043 := hb (x 11 12)
          have b27044 := hb (x 11 1 && x 11 12)
          clear * - r27042 b27043 b27044 d27033
          omega
        have d27045 : (x 10 13).toNat = 0 := by
          have r27046 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
          have e27047 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e27048 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have b27049 := hb (x 8 3)
          have b27050 := hb (x 9 2)
          have b27051 := hb (x 10 13)
          have b27052 := hb (x 11 12)
          clear * - r27046 e27047 e27048 b27049 b27050 b27051 b27052 d27033 d26921 d27029
          omega
        have d27053 : (x 10 2 && x 10 13).toNat = 0 := by
          have r27054 := hand2 (x 10 2) (x 10 13)
          have b27055 := hb (x 10 13)
          have b27056 := hb (x 10 2 && x 10 13)
          clear * - r27054 b27055 b27056 d27045
          omega
        have d27057 : (x 12 11).toNat = 1 := by
          have r27058 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := hcov11 12
          have b27059 := hb (x 8 4)
          have b27060 := hb (x 12 11)
          have b27061 := hb (x 11 1 && x 11 12)
          have b27062 := hb (x 10 2 && x 10 13)
          have b27063 := hb (x 9 3 && x 9 14)
          clear * - r27058 b27059 b27060 b27061 b27062 b27063 d27041 d27053 d26917 d26855
          omega
        have d27064 : (x 12 3).toNat = 1 := by
          have r27065 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
          have b27066 := hb (x 12 3)
          have b27067 := hb (x 12 11)
          clear * - r27065 b27066 b27067 d27057
          omega
        have d27068 : (x 15 12).toNat = 0 := by
          have r27069 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
          have e27070 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
          have e27071 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
          have b27072 := hb (x 12 3)
          have b27073 := hb (x 13 2)
          have b27074 := hb (x 14 13)
          have b27075 := hb (x 15 12)
          clear * - r27069 e27070 e27071 b27072 b27073 b27074 b27075 d27064
          omega
        have d27076 : (x 15 1 && x 15 12).toNat = 0 := by
          have r27077 := hand2 (x 15 1) (x 15 12)
          have b27078 := hb (x 15 12)
          have b27079 := hb (x 15 1 && x 15 12)
          clear * - r27077 b27078 b27079 d27068
          omega
        have d27080 : (x 14 13).toNat = 0 := by
          have r27081 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
          have e27082 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
          have e27083 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
          have b27084 := hb (x 12 3)
          have b27085 := hb (x 13 2)
          have b27086 := hb (x 14 13)
          have b27087 := hb (x 15 12)
          clear * - r27081 e27082 e27083 b27084 b27085 b27086 b27087 d27068 d27064
          omega
        have d27088 : (x 14 2 && x 14 13).toNat = 0 := by
          have r27089 := hand2 (x 14 2) (x 14 13)
          have b27090 := hb (x 14 13)
          have b27091 := hb (x 14 2 && x 14 13)
          clear * - r27089 b27090 b27091 d27080
          omega
        have d27092 : (x 13 2).toNat = 0 := by
          have r27093 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
          have e27094 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
          have e27095 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
          have b27096 := hb (x 12 3)
          have b27097 := hb (x 13 2)
          have b27098 := hb (x 14 13)
          have b27099 := hb (x 15 12)
          clear * - r27093 e27094 e27095 b27096 b27097 b27098 b27099 d27068 d27080 d27064
          omega
        have d27100 : (x 10 1).toNat = 1 := by
          have r27101 := hand1 (x 10 1) (x 10 14)
          have b27102 := hb (x 10 1)
          have b27103 := hb (x 10 1 && x 10 14)
          clear * - r27101 b27102 b27103 d26988
          omega
        have d27104 : (x 11 14).toNat = 0 := by
          have r27105 : (x 11 14).toNat + (x 10 1).toNat = 1 := hd14 11
          have b27106 := hb (x 10 1)
          have b27107 := hb (x 11 14)
          clear * - r27105 b27106 b27107 d27100
          omega
        have d27108 : (x 11 1 && x 11 14).toNat = 0 := by
          have r27109 := hand2 (x 11 1) (x 11 14)
          have b27110 := hb (x 11 14)
          have b27111 := hb (x 11 1 && x 11 14)
          clear * - r27109 b27110 b27111 d27104
          omega
        have d27112 : (x 11 2).toNat = 0 := by
          have r27113 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
          have b27114 := hb (x 11 2)
          have b27115 := hb (x 11 14)
          clear * - r27113 b27114 b27115 d27104
          omega
        have d27116 : (x 10 2).toNat = 0 := by
          have r27117 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
          have e27118 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
          have e27119 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
          have b27120 := hb (x 9 3)
          have b27121 := hb (x 10 2)
          have b27122 := hb (x 11 13)
          have b27123 := hb (x 12 12)
          clear * - r27117 e27118 e27119 b27120 b27121 b27122 b27123 d26960 d26976 d26956
          omega
        have d27124 : (x 12 13).toNat = 1 := by
          have r27125 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := hcov13 12
          have b27126 := hb (x 10 2)
          have b27127 := hb (x 12 13)
          have b27128 := hb (x 11 1 && x 11 14)
          clear * - r27125 b27126 b27127 b27128 d27108 d27116
          omega
        have d27129 : (x 12 1).toNat = 1 := by
          have r27130 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
          have b27131 := hb (x 12 1)
          have b27132 := hb (x 12 13)
          clear * - r27130 b27131 b27132 d27124
          omega
        have d27133 : (x 13 14).toNat = 0 := by
          have r27134 : (x 13 14).toNat + (x 12 1).toNat = 1 := hd14 13
          have b27135 := hb (x 12 1)
          have b27136 := hb (x 13 14)
          clear * - r27134 b27135 b27136 d27129
          omega
        have d27137 : (x 13 1 && x 13 14).toNat = 0 := by
          have r27138 := hand2 (x 13 1) (x 13 14)
          have b27139 := hb (x 13 14)
          have b27140 := hb (x 13 1 && x 13 14)
          clear * - r27138 b27139 b27140 d27133
          omega
        have d27141 : (x 12 2).toNat = 1 := by
          have r27142 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
          have b27143 := hb (x 12 2)
          have b27144 := hb (x 14 13)
          have b27145 := hb (x 13 1 && x 13 14)
          clear * - r27142 b27143 b27144 b27145 d27080 d27137
          omega
        have d27146 : (x 14 12).toNat = 0 := by
          have r27147 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
          have e27148 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
          have e27149 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
          have b27150 := hb (x 11 3)
          have b27151 := hb (x 12 2)
          have b27152 := hb (x 13 13)
          have b27153 := hb (x 14 12)
          clear * - r27147 e27148 e27149 b27150 b27151 b27152 b27153 d27141
          omega
        have d27154 : (x 14 4).toNat = 0 := by
          have r27155 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
          have b27156 := hb (x 14 4)
          have b27157 := hb (x 14 12)
          clear * - r27155 b27156 b27157 d27146
          omega
        have d27158 : (x 14 4 && x 14 14).toNat = 0 := by
          have r27159 := hand1 (x 14 4) (x 14 14)
          have b27160 := hb (x 14 4)
          have b27161 := hb (x 14 4 && x 14 14)
          clear * - r27159 b27160 b27161 d27154
          omega
        have d27162 : (x 13 13).toNat = 0 := by
          have r27163 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
          have e27164 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
          have e27165 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
          have b27166 := hb (x 11 3)
          have b27167 := hb (x 12 2)
          have b27168 := hb (x 13 13)
          have b27169 := hb (x 14 12)
          clear * - r27163 e27164 e27165 b27166 b27167 b27168 b27169 d27146 d27141
          omega
        have d27170 : (x 13 5).toNat = 0 := by
          have r27171 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
          have b27172 := hb (x 13 5)
          have b27173 := hb (x 13 13)
          clear * - r27171 b27172 b27173 d27162
          omega
        have d27174 : (x 13 3 && x 13 14).toNat = 0 := by
          have r27175 := hand2 (x 13 3) (x 13 14)
          have b27176 := hb (x 13 14)
          have b27177 := hb (x 13 3 && x 13 14)
          clear * - r27175 b27176 b27177 d27133
          omega
        have d27178 : (x 16 11).toNat = 1 := by
          have r27179 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := hcov11 16
          have b27180 := hb (x 12 4)
          have b27181 := hb (x 16 11)
          have b27182 := hb (x 15 1 && x 15 12)
          have b27183 := hb (x 14 2 && x 14 13)
          have b27184 := hb (x 13 3 && x 13 14)
          clear * - r27179 b27180 b27181 b27182 b27183 b27184 d27076 d27088 d27174 d26972
          omega
        have d27185 : (x 16 3).toNat = 1 := by
          have r27186 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
          have b27187 := hb (x 16 3)
          have b27188 := hb (x 16 11)
          clear * - r27186 b27187 b27188 d27178
          omega
        have d27189 : (x 19 12).toNat = 0 := by
          have r27190 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
          have e27191 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
          have e27192 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
          have b27193 := hb (x 16 3)
          have b27194 := hb (x 17 2)
          have b27195 := hb (x 18 13)
          have b27196 := hb (x 19 12)
          clear * - r27190 e27191 e27192 b27193 b27194 b27195 b27196 d27185
          omega
        have d27197 : (x 18 13).toNat = 0 := by
          have r27198 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
          have e27199 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
          have e27200 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
          have b27201 := hb (x 16 3)
          have b27202 := hb (x 17 2)
          have b27203 := hb (x 18 13)
          have b27204 := hb (x 19 12)
          clear * - r27198 e27199 e27200 b27201 b27202 b27203 b27204 d27189 d27185
          omega
        have d27205 : (x 17 2).toNat = 0 := by
          have r27206 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
          have e27207 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
          have e27208 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
          have b27209 := hb (x 16 3)
          have b27210 := hb (x 17 2)
          have b27211 := hb (x 18 13)
          have b27212 := hb (x 19 12)
          clear * - r27206 e27207 e27208 b27209 b27210 b27211 b27212 d27189 d27197 d27185
          omega
        have d27213 : (x 13 12).toNat = 0 := by
          have r27214 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
          have e27215 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
          have e27216 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
          have b27217 := hb (x 10 3)
          have b27218 := hb (x 11 2)
          have b27219 := hb (x 12 13)
          have b27220 := hb (x 13 12)
          clear * - r27214 e27215 e27216 b27217 b27218 b27219 b27220 d27124 d27112
          omega
        have d27221 : (x 13 4).toNat = 0 := by
          have r27222 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
          have b27223 := hb (x 13 4)
          have b27224 := hb (x 13 12)
          clear * - r27222 b27223 b27224 d27213
          omega
        have d27225 : (x 10 3).toNat = 0 := by
          have r27226 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
          have e27227 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
          have e27228 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
          have b27229 := hb (x 10 3)
          have b27230 := hb (x 11 2)
          have b27231 := hb (x 12 13)
          have b27232 := hb (x 13 12)
          clear * - r27226 e27227 e27228 b27229 b27230 b27231 b27232 d27213 d27124 d27112
          omega
        have d27233 : (x 10 3 && x 10 14).toNat = 0 := by
          have r27234 := hand1 (x 10 3) (x 10 14)
          have b27235 := hb (x 10 3)
          have b27236 := hb (x 10 3 && x 10 14)
          clear * - r27234 b27235 b27236 d27225
          omega
        have d27237 : (x 13 11).toNat = 1 := by
          have r27238 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := hcov11 13
          have b27239 := hb (x 9 4)
          have b27240 := hb (x 13 11)
          have b27241 := hb (x 12 1 && x 12 12)
          have b27242 := hb (x 11 2 && x 11 13)
          have b27243 := hb (x 10 3 && x 10 14)
          clear * - r27238 b27239 b27240 b27241 b27242 b27243 d26968 d26984 d27233 d26933
          omega
        have d27244 : (x 13 3).toNat = 1 := by
          have r27245 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
          have b27246 := hb (x 13 3)
          have b27247 := hb (x 13 11)
          clear * - r27245 b27246 b27247 d27237
          omega
        have d27248 : (x 16 12).toNat = 0 := by
          have r27249 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
          have e27250 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
          have e27251 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
          have b27252 := hb (x 13 3)
          have b27253 := hb (x 14 2)
          have b27254 := hb (x 15 13)
          have b27255 := hb (x 16 12)
          clear * - r27249 e27250 e27251 b27252 b27253 b27254 b27255 d27244
          omega
        have d27256 : (x 16 1 && x 16 12).toNat = 0 := by
          have r27257 := hand2 (x 16 1) (x 16 12)
          have b27258 := hb (x 16 12)
          have b27259 := hb (x 16 1 && x 16 12)
          clear * - r27257 b27258 b27259 d27248
          omega
        have d27260 : (x 16 2 && x 16 12).toNat = 0 := by
          have r27261 := hand2 (x 16 2) (x 16 12)
          have b27262 := hb (x 16 12)
          have b27263 := hb (x 16 2 && x 16 12)
          clear * - r27261 b27262 b27263 d27248
          omega
        have d27264 : (x 15 13).toNat = 0 := by
          have r27265 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
          have e27266 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
          have e27267 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
          have b27268 := hb (x 13 3)
          have b27269 := hb (x 14 2)
          have b27270 := hb (x 15 13)
          have b27271 := hb (x 16 12)
          clear * - r27265 e27266 e27267 b27268 b27269 b27270 b27271 d27248 d27244
          omega
        have d27272 : (x 15 2 && x 15 13).toNat = 0 := by
          have r27273 := hand2 (x 15 2) (x 15 13)
          have b27274 := hb (x 15 13)
          have b27275 := hb (x 15 2 && x 15 13)
          clear * - r27273 b27274 b27275 d27264
          omega
        have d27276 : (x 15 3 && x 15 13).toNat = 0 := by
          have r27277 := hand2 (x 15 3) (x 15 13)
          have b27278 := hb (x 15 13)
          have b27279 := hb (x 15 3 && x 15 13)
          clear * - r27277 b27278 b27279 d27264
          omega
        have d27280 : (x 14 1 && x 14 14).toNat = 1 := by
          have r27281 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := hcov13 15
          have b27282 := hb (x 13 2)
          have b27283 := hb (x 15 13)
          have b27284 := hb (x 14 1 && x 14 14)
          clear * - r27281 b27282 b27283 b27284 d27264 d27092
          omega
        have d27285 : (x 14 1).toNat = 1 := by
          have r27286 := hand1 (x 14 1) (x 14 14)
          have b27287 := hb (x 14 1)
          have b27288 := hb (x 14 1 && x 14 14)
          clear * - r27286 b27287 b27288 d27280
          omega
        have d27289 : (x 15 14).toNat = 0 := by
          have r27290 : (x 15 14).toNat + (x 14 1).toNat = 1 := hd14 15
          have b27291 := hb (x 14 1)
          have b27292 := hb (x 15 14)
          clear * - r27290 b27291 b27292 d27285
          omega
        have d27293 : (x 15 1 && x 15 14).toNat = 0 := by
          have r27294 := hand2 (x 15 1) (x 15 14)
          have b27295 := hb (x 15 14)
          have b27296 := hb (x 15 1 && x 15 14)
          clear * - r27294 b27295 b27296 d27289
          omega
        have d27297 : (x 15 2).toNat = 0 := by
          have r27298 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
          have b27299 := hb (x 15 2)
          have b27300 := hb (x 15 14)
          clear * - r27298 b27299 b27300 d27289
          omega
        have d27301 : (x 14 2).toNat = 0 := by
          have r27302 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
          have e27303 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
          have e27304 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
          have b27305 := hb (x 13 3)
          have b27306 := hb (x 14 2)
          have b27307 := hb (x 15 13)
          have b27308 := hb (x 16 12)
          clear * - r27302 e27303 e27304 b27305 b27306 b27307 b27308 d27248 d27264 d27244
          omega
        have d27309 : (x 16 13).toNat = 1 := by
          have r27310 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := hcov13 16
          have b27311 := hb (x 14 2)
          have b27312 := hb (x 16 13)
          have b27313 := hb (x 15 1 && x 15 14)
          clear * - r27310 b27311 b27312 b27313 d27293 d27301
          omega
        have d27314 : (x 17 12).toNat = 0 := by
          have r27315 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
          have e27316 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
          have e27317 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
          have b27318 := hb (x 14 3)
          have b27319 := hb (x 15 2)
          have b27320 := hb (x 16 13)
          have b27321 := hb (x 17 12)
          clear * - r27315 e27316 e27317 b27318 b27319 b27320 b27321 d27309 d27297
          omega
        have d27322 : (x 14 3).toNat = 0 := by
          have r27323 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
          have e27324 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
          have e27325 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
          have b27326 := hb (x 14 3)
          have b27327 := hb (x 15 2)
          have b27328 := hb (x 16 13)
          have b27329 := hb (x 17 12)
          clear * - r27323 e27324 e27325 b27326 b27327 b27328 b27329 d27314 d27309 d27297
          omega
        have d27330 : (x 14 3 && x 14 14).toNat = 0 := by
          have r27331 := hand1 (x 14 3) (x 14 14)
          have b27332 := hb (x 14 3)
          have b27333 := hb (x 14 3 && x 14 14)
          clear * - r27331 b27332 b27333 d27322
          omega
        have d27334 : (x 17 11).toNat = 1 := by
          have r27335 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := hcov11 17
          have b27336 := hb (x 13 4)
          have b27337 := hb (x 17 11)
          have b27338 := hb (x 16 1 && x 16 12)
          have b27339 := hb (x 15 2 && x 15 13)
          have b27340 := hb (x 14 3 && x 14 14)
          clear * - r27335 b27336 b27337 b27338 b27339 b27340 d27256 d27272 d27330 d27221
          omega
        have d27341 : (x 17 3).toNat = 1 := by
          have r27342 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
          have b27343 := hb (x 17 3)
          have b27344 := hb (x 17 11)
          clear * - r27342 b27343 b27344 d27334
          omega
        have d27345 : (x 20 12).toNat = 0 := by
          have r27346 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
          have e27347 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
          have e27348 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
          have b27349 := hb (x 17 3)
          have b27350 := hb (x 18 2)
          have b27351 := hb (x 19 13)
          have b27352 := hb (x 20 12)
          clear * - r27346 e27347 e27348 b27349 b27350 b27351 b27352 d27341
          omega
        have d27353 : (x 19 13).toNat = 0 := by
          have r27354 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
          have e27355 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
          have e27356 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
          have b27357 := hb (x 17 3)
          have b27358 := hb (x 18 2)
          have b27359 := hb (x 19 13)
          have b27360 := hb (x 20 12)
          clear * - r27354 e27355 e27356 b27357 b27358 b27359 b27360 d27345 d27341
          omega
        have d27361 : (x 18 1 && x 18 14).toNat = 1 := by
          have r27362 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := hcov13 19
          have b27363 := hb (x 17 2)
          have b27364 := hb (x 19 13)
          have b27365 := hb (x 18 1 && x 18 14)
          clear * - r27362 b27363 b27364 b27365 d27353 d27205
          omega
        have d27366 : (x 18 14).toNat = 1 := by
          have r27367 := hand2 (x 18 1) (x 18 14)
          have b27368 := hb (x 18 14)
          have b27369 := hb (x 18 1 && x 18 14)
          clear * - r27367 b27368 b27369 d27361
          omega
        have d27370 : (x 17 1).toNat = 0 := by
          have r27371 : (x 18 14).toNat + (x 17 1).toNat = 1 := hd14 18
          have b27372 := hb (x 17 1)
          have b27373 := hb (x 18 14)
          clear * - r27371 b27372 b27373 d27366
          omega
        have d27374 : (x 17 1 && x 17 11).toNat = 0 := by
          have r27375 := hand1 (x 17 1) (x 17 11)
          have b27376 := hb (x 17 1)
          have b27377 := hb (x 17 1 && x 17 11)
          clear * - r27375 b27376 b27377 d27370
          omega
        have d27378 : (x 18 2).toNat = 0 := by
          have r27379 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
          have e27380 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
          have e27381 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
          have b27382 := hb (x 17 3)
          have b27383 := hb (x 18 2)
          have b27384 := hb (x 19 13)
          have b27385 := hb (x 20 12)
          clear * - r27379 e27380 e27381 b27382 b27383 b27384 b27385 d27345 d27353 d27341
          omega
        have d27386 : (x 18 10).toNat = 0 := by
          have r27387 : (x 18 10).toNat ≤ (x 18 2).toNat := himp _ _ (hp10 18)
          have b27388 := hb (x 18 2)
          have b27389 := hb (x 18 10)
          clear * - r27387 b27388 b27389 d27378
          omega
        have r27390 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := hcov10 18
        have b27391 := hb (x 13 5)
        have b27392 := hb (x 18 10)
        have b27393 := hb (x 17 1 && x 17 11)
        have b27394 := hb (x 16 2 && x 16 12)
        have b27395 := hb (x 15 3 && x 15 13)
        have b27396 := hb (x 14 4 && x 14 14)
        linarith only [r27390, b27391, b27392, b27393, b27394, b27395, b27396, d27386, d27374, d27260, d27276, d27158, d27170]
    · have f27397 : (x 1 1).toNat = 1 := by rw [h25941]; rfl
      have d27398 : (x 2 14).toNat = 0 := by
        have r27399 : (x 2 14).toNat + (x 1 1).toNat = 1 := hd14 2
        have b27400 := hb (x 1 1)
        have b27401 := hb (x 2 14)
        clear * - r27399 b27400 b27401 f27397
        omega
      have d27402 : (x 2 1 && x 2 14).toNat = 0 := by
        have r27403 := hand2 (x 2 1) (x 2 14)
        have b27404 := hb (x 2 14)
        have b27405 := hb (x 2 1 && x 2 14)
        clear * - r27403 b27404 b27405 d27398
        omega
      have d27406 : (x 2 2).toNat = 0 := by
        have r27407 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
        have b27408 := hb (x 2 2)
        have b27409 := hb (x 2 14)
        clear * - r27407 b27408 b27409 d27398
        omega
      have d27410 : (x 4 13).toNat = 1 := by
        have r27411 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
        have b27412 := hb (x 2 2)
        have b27413 := hb (x 4 13)
        have b27414 := hb (x 3 1 && x 3 14)
        clear * - r27411 b27412 b27413 b27414 g35 d27406
        omega
      have d27415 : (x 4 1).toNat = 1 := by
        have r27416 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
        have b27417 := hb (x 4 1)
        have b27418 := hb (x 4 13)
        clear * - r27416 b27417 b27418 d27410
        omega
      have d27419 : (x 5 14).toNat = 0 := by
        have r27420 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
        have b27421 := hb (x 4 1)
        have b27422 := hb (x 5 14)
        clear * - r27420 b27421 b27422 d27415
        omega
      have d27423 : (x 5 1 && x 5 14).toNat = 0 := by
        have r27424 := hand2 (x 5 1) (x 5 14)
        have b27425 := hb (x 5 14)
        have b27426 := hb (x 5 1 && x 5 14)
        clear * - r27424 b27425 b27426 d27419
        omega
      have d27427 : (x 5 2).toNat = 0 := by
        have r27428 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
        have b27429 := hb (x 5 2)
        have b27430 := hb (x 5 14)
        clear * - r27428 b27429 b27430 d27419
        omega
      have d27431 : (x 3 13).toNat = 1 := by
        have r27432 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := hcov13 3
        have b27433 := hb (x 1 2)
        have b27434 := hb (x 3 13)
        have b27435 := hb (x 2 1 && x 2 14)
        clear * - r27432 b27433 b27434 b27435 d27402 g11
        omega
      have d27436 : (x 3 1).toNat = 1 := by
        have r27437 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
        have b27438 := hb (x 3 1)
        have b27439 := hb (x 3 13)
        clear * - r27437 b27438 b27439 d27431
        omega
      have d27440 : (x 4 14).toNat = 0 := by
        have r27441 : (x 4 14).toNat + (x 3 1).toNat = 1 := hd14 4
        have b27442 := hb (x 3 1)
        have b27443 := hb (x 4 14)
        clear * - r27441 b27442 b27443 d27436
        omega
      have d27444 : (x 4 1 && x 4 14).toNat = 0 := by
        have r27445 := hand2 (x 4 1) (x 4 14)
        have b27446 := hb (x 4 14)
        have b27447 := hb (x 4 1 && x 4 14)
        clear * - r27445 b27446 b27447 d27440
        omega
      have d27448 : (x 5 13).toNat = 1 := by
        have r27449 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := hcov13 5
        have b27450 := hb (x 3 2)
        have b27451 := hb (x 5 13)
        have b27452 := hb (x 4 1 && x 4 14)
        clear * - r27449 b27450 b27451 b27452 d27444 g17
        omega
      have d27453 : (x 5 1).toNat = 1 := by
        have r27454 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
        have b27455 := hb (x 5 1)
        have b27456 := hb (x 5 13)
        clear * - r27454 b27455 b27456 d27448
        omega
      have d27457 : (x 6 14).toNat = 0 := by
        have r27458 : (x 6 14).toNat + (x 5 1).toNat = 1 := hd14 6
        have b27459 := hb (x 5 1)
        have b27460 := hb (x 6 14)
        clear * - r27458 b27459 b27460 d27453
        omega
      have d27461 : (x 6 1 && x 6 14).toNat = 0 := by
        have r27462 := hand2 (x 6 1) (x 6 14)
        have b27463 := hb (x 6 14)
        have b27464 := hb (x 6 1 && x 6 14)
        clear * - r27462 b27463 b27464 d27457
        omega
      have d27465 : (x 7 13).toNat = 1 := by
        have r27466 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
        have b27467 := hb (x 5 2)
        have b27468 := hb (x 7 13)
        have b27469 := hb (x 6 1 && x 6 14)
        clear * - r27466 b27467 b27468 b27469 d27461 d27427
        omega
      have d27470 : (x 7 1).toNat = 1 := by
        have r27471 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
        have b27472 := hb (x 7 1)
        have b27473 := hb (x 7 13)
        clear * - r27471 b27472 b27473 d27465
        omega
      have d27474 : (x 8 14).toNat = 0 := by
        have r27475 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
        have b27476 := hb (x 7 1)
        have b27477 := hb (x 8 14)
        clear * - r27475 b27476 b27477 d27470
        omega
      have d27478 : (x 8 1 && x 8 14).toNat = 0 := by
        have r27479 := hand2 (x 8 1) (x 8 14)
        have b27480 := hb (x 8 14)
        have b27481 := hb (x 8 1 && x 8 14)
        clear * - r27479 b27480 b27481 d27474
        omega
      have d27482 : (x 8 2).toNat = 0 := by
        have r27483 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
        have b27484 := hb (x 8 2)
        have b27485 := hb (x 8 14)
        clear * - r27483 b27484 b27485 d27474
        omega
      have d27486 : (x 6 2).toNat = 0 := by
        have r27487 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
        have b27488 := hb (x 6 2)
        have b27489 := hb (x 6 14)
        clear * - r27487 b27488 b27489 d27457
        omega
      have d27490 : (x 4 2).toNat = 0 := by
        have r27491 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
        have b27492 := hb (x 4 2)
        have b27493 := hb (x 4 14)
        clear * - r27491 b27492 b27493 d27440
        omega
      have d27494 : (x 6 13).toNat = 1 := by
        have r27495 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := hcov13 6
        have b27496 := hb (x 4 2)
        have b27497 := hb (x 6 13)
        have b27498 := hb (x 5 1 && x 5 14)
        clear * - r27495 b27496 b27497 b27498 d27423 d27490
        omega
      have d27499 : (x 6 1).toNat = 1 := by
        have r27500 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
        have b27501 := hb (x 6 1)
        have b27502 := hb (x 6 13)
        clear * - r27500 b27501 b27502 d27494
        omega
      have d27503 : (x 7 14).toNat = 0 := by
        have r27504 : (x 7 14).toNat + (x 6 1).toNat = 1 := hd14 7
        have b27505 := hb (x 6 1)
        have b27506 := hb (x 7 14)
        clear * - r27504 b27505 b27506 d27499
        omega
      have d27507 : (x 7 1 && x 7 14).toNat = 0 := by
        have r27508 := hand2 (x 7 1) (x 7 14)
        have b27509 := hb (x 7 14)
        have b27510 := hb (x 7 1 && x 7 14)
        clear * - r27508 b27509 b27510 d27503
        omega
      have d27511 : (x 8 13).toNat = 1 := by
        have r27512 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := hcov13 8
        have b27513 := hb (x 6 2)
        have b27514 := hb (x 8 13)
        have b27515 := hb (x 7 1 && x 7 14)
        clear * - r27512 b27513 b27514 b27515 d27507 d27486
        omega
      have d27516 : (x 8 1).toNat = 1 := by
        have r27517 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
        have b27518 := hb (x 8 1)
        have b27519 := hb (x 8 13)
        clear * - r27517 b27518 b27519 d27511
        omega
      have d27520 : (x 9 14).toNat = 0 := by
        have r27521 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
        have b27522 := hb (x 8 1)
        have b27523 := hb (x 9 14)
        clear * - r27521 b27522 b27523 d27516
        omega
      have d27524 : (x 9 1 && x 9 14).toNat = 0 := by
        have r27525 := hand2 (x 9 1) (x 9 14)
        have b27526 := hb (x 9 14)
        have b27527 := hb (x 9 1 && x 9 14)
        clear * - r27525 b27526 b27527 d27520
        omega
      have d27528 : (x 10 13).toNat = 1 := by
        have r27529 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := hcov13 10
        have b27530 := hb (x 8 2)
        have b27531 := hb (x 10 13)
        have b27532 := hb (x 9 1 && x 9 14)
        clear * - r27529 b27530 b27531 b27532 d27524 d27482
        omega
      have d27533 : (x 10 1).toNat = 1 := by
        have r27534 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
        have b27535 := hb (x 10 1)
        have b27536 := hb (x 10 13)
        clear * - r27534 b27535 b27536 d27528
        omega
      have d27537 : (x 11 14).toNat = 0 := by
        have r27538 : (x 11 14).toNat + (x 10 1).toNat = 1 := hd14 11
        have b27539 := hb (x 10 1)
        have b27540 := hb (x 11 14)
        clear * - r27538 b27539 b27540 d27533
        omega
      have d27541 : (x 11 1 && x 11 14).toNat = 0 := by
        have r27542 := hand2 (x 11 1) (x 11 14)
        have b27543 := hb (x 11 14)
        have b27544 := hb (x 11 1 && x 11 14)
        clear * - r27542 b27543 b27544 d27537
        omega
      have d27545 : (x 11 2).toNat = 0 := by
        have r27546 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
        have b27547 := hb (x 11 2)
        have b27548 := hb (x 11 14)
        clear * - r27546 b27547 b27548 d27537
        omega
      have d27549 : (x 9 2).toNat = 0 := by
        have r27550 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
        have b27551 := hb (x 9 2)
        have b27552 := hb (x 9 14)
        clear * - r27550 b27551 b27552 d27520
        omega
      have d27553 : (x 7 2).toNat = 0 := by
        have r27554 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
        have b27555 := hb (x 7 2)
        have b27556 := hb (x 7 14)
        clear * - r27554 b27555 b27556 d27503
        omega
      have d27557 : (x 9 13).toNat = 1 := by
        have r27558 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := hcov13 9
        have b27559 := hb (x 7 2)
        have b27560 := hb (x 9 13)
        have b27561 := hb (x 8 1 && x 8 14)
        clear * - r27558 b27559 b27560 b27561 d27478 d27553
        omega
      have d27562 : (x 9 1).toNat = 1 := by
        have r27563 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
        have b27564 := hb (x 9 1)
        have b27565 := hb (x 9 13)
        clear * - r27563 b27564 b27565 d27557
        omega
      have d27566 : (x 10 14).toNat = 0 := by
        have r27567 : (x 10 14).toNat + (x 9 1).toNat = 1 := hd14 10
        have b27568 := hb (x 9 1)
        have b27569 := hb (x 10 14)
        clear * - r27567 b27568 b27569 d27562
        omega
      have d27570 : (x 10 1 && x 10 14).toNat = 0 := by
        have r27571 := hand2 (x 10 1) (x 10 14)
        have b27572 := hb (x 10 14)
        have b27573 := hb (x 10 1 && x 10 14)
        clear * - r27571 b27572 b27573 d27566
        omega
      have d27574 : (x 11 13).toNat = 1 := by
        have r27575 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := hcov13 11
        have b27576 := hb (x 9 2)
        have b27577 := hb (x 11 13)
        have b27578 := hb (x 10 1 && x 10 14)
        clear * - r27575 b27576 b27577 b27578 d27570 d27549
        omega
      have d27579 : (x 11 1).toNat = 1 := by
        have r27580 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
        have b27581 := hb (x 11 1)
        have b27582 := hb (x 11 13)
        clear * - r27580 b27581 b27582 d27574
        omega
      have d27583 : (x 12 14).toNat = 0 := by
        have r27584 : (x 12 14).toNat + (x 11 1).toNat = 1 := hd14 12
        have b27585 := hb (x 11 1)
        have b27586 := hb (x 12 14)
        clear * - r27584 b27585 b27586 d27579
        omega
      have d27587 : (x 12 1 && x 12 14).toNat = 0 := by
        have r27588 := hand2 (x 12 1) (x 12 14)
        have b27589 := hb (x 12 14)
        have b27590 := hb (x 12 1 && x 12 14)
        clear * - r27588 b27589 b27590 d27583
        omega
      have d27591 : (x 13 13).toNat = 1 := by
        have r27592 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := hcov13 13
        have b27593 := hb (x 11 2)
        have b27594 := hb (x 13 13)
        have b27595 := hb (x 12 1 && x 12 14)
        clear * - r27592 b27593 b27594 b27595 d27587 d27545
        omega
      have d27596 : (x 13 1).toNat = 1 := by
        have r27597 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
        have b27598 := hb (x 13 1)
        have b27599 := hb (x 13 13)
        clear * - r27597 b27598 b27599 d27591
        omega
      have d27600 : (x 14 14).toNat = 0 := by
        have r27601 : (x 14 14).toNat + (x 13 1).toNat = 1 := hd14 14
        have b27602 := hb (x 13 1)
        have b27603 := hb (x 14 14)
        clear * - r27601 b27602 b27603 d27596
        omega
      have d27604 : (x 14 1 && x 14 14).toNat = 0 := by
        have r27605 := hand2 (x 14 1) (x 14 14)
        have b27606 := hb (x 14 14)
        have b27607 := hb (x 14 1 && x 14 14)
        clear * - r27605 b27606 b27607 d27600
        omega
      have d27608 : (x 14 3 && x 14 14).toNat = 0 := by
        have r27609 := hand2 (x 14 3) (x 14 14)
        have b27610 := hb (x 14 14)
        have b27611 := hb (x 14 3 && x 14 14)
        clear * - r27609 b27610 b27611 d27600
        omega
      have d27612 : (x 14 2).toNat = 0 := by
        have r27613 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
        have b27614 := hb (x 14 2)
        have b27615 := hb (x 14 14)
        clear * - r27613 b27614 b27615 d27600
        omega
      have d27616 : (x 12 2).toNat = 0 := by
        have r27617 : (x 12 2).toNat ≤ (x 12 14).toNat := himp _ _ (hp2 12)
        have b27618 := hb (x 12 2)
        have b27619 := hb (x 12 14)
        clear * - r27617 b27618 b27619 d27583
        omega
      have d27620 : (x 10 2).toNat = 0 := by
        have r27621 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
        have b27622 := hb (x 10 2)
        have b27623 := hb (x 10 14)
        clear * - r27621 b27622 b27623 d27566
        omega
      have d27624 : (x 12 13).toNat = 1 := by
        have r27625 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := hcov13 12
        have b27626 := hb (x 10 2)
        have b27627 := hb (x 12 13)
        have b27628 := hb (x 11 1 && x 11 14)
        clear * - r27625 b27626 b27627 b27628 d27541 d27620
        omega
      have d27629 : (x 12 1).toNat = 1 := by
        have r27630 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
        have b27631 := hb (x 12 1)
        have b27632 := hb (x 12 13)
        clear * - r27630 b27631 b27632 d27624
        omega
      have d27633 : (x 13 14).toNat = 0 := by
        have r27634 : (x 13 14).toNat + (x 12 1).toNat = 1 := hd14 13
        have b27635 := hb (x 12 1)
        have b27636 := hb (x 13 14)
        clear * - r27634 b27635 b27636 d27629
        omega
      have d27637 : (x 13 1 && x 13 14).toNat = 0 := by
        have r27638 := hand2 (x 13 1) (x 13 14)
        have b27639 := hb (x 13 14)
        have b27640 := hb (x 13 1 && x 13 14)
        clear * - r27638 b27639 b27640 d27633
        omega
      have d27641 : (x 14 13).toNat = 1 := by
        have r27642 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
        have b27643 := hb (x 12 2)
        have b27644 := hb (x 14 13)
        have b27645 := hb (x 13 1 && x 13 14)
        clear * - r27642 b27643 b27644 b27645 d27637 d27616
        omega
      have d27646 : (x 14 1).toNat = 1 := by
        have r27647 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
        have b27648 := hb (x 14 1)
        have b27649 := hb (x 14 13)
        clear * - r27647 b27648 b27649 d27641
        omega
      have d27650 : (x 15 14).toNat = 0 := by
        have r27651 : (x 15 14).toNat + (x 14 1).toNat = 1 := hd14 15
        have b27652 := hb (x 14 1)
        have b27653 := hb (x 15 14)
        clear * - r27651 b27652 b27653 d27646
        omega
      have d27654 : (x 15 1 && x 15 14).toNat = 0 := by
        have r27655 := hand2 (x 15 1) (x 15 14)
        have b27656 := hb (x 15 14)
        have b27657 := hb (x 15 1 && x 15 14)
        clear * - r27655 b27656 b27657 d27650
        omega
      have d27658 : (x 16 13).toNat = 1 := by
        have r27659 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := hcov13 16
        have b27660 := hb (x 14 2)
        have b27661 := hb (x 16 13)
        have b27662 := hb (x 15 1 && x 15 14)
        clear * - r27659 b27660 b27661 b27662 d27654 d27612
        omega
      have d27663 : (x 16 1).toNat = 1 := by
        have r27664 : (x 16 13).toNat ≤ (x 16 1).toNat := himp _ _ (hp13 16)
        have b27665 := hb (x 16 1)
        have b27666 := hb (x 16 13)
        clear * - r27664 b27665 b27666 d27658
        omega
      have d27667 : (x 17 14).toNat = 0 := by
        have r27668 : (x 17 14).toNat + (x 16 1).toNat = 1 := hd14 17
        have b27669 := hb (x 16 1)
        have b27670 := hb (x 17 14)
        clear * - r27668 b27669 b27670 d27663
        omega
      have d27671 : (x 17 2).toNat = 0 := by
        have r27672 : (x 17 2).toNat ≤ (x 17 14).toNat := himp _ _ (hp2 17)
        have b27673 := hb (x 17 2)
        have b27674 := hb (x 17 14)
        clear * - r27672 b27673 b27674 d27667
        omega
      have d27675 : (x 15 2).toNat = 0 := by
        have r27676 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
        have b27677 := hb (x 15 2)
        have b27678 := hb (x 15 14)
        clear * - r27676 b27677 b27678 d27650
        omega
      have d27679 : (x 15 2 && x 15 13).toNat = 0 := by
        have r27680 := hand1 (x 15 2) (x 15 13)
        have b27681 := hb (x 15 2)
        have b27682 := hb (x 15 2 && x 15 13)
        clear * - r27680 b27681 b27682 d27675
        omega
      have d27683 : (x 13 2).toNat = 0 := by
        have r27684 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
        have b27685 := hb (x 13 2)
        have b27686 := hb (x 13 14)
        clear * - r27684 b27685 b27686 d27633
        omega
      have d27687 : (x 15 13).toNat = 1 := by
        have r27688 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := hcov13 15
        have b27689 := hb (x 13 2)
        have b27690 := hb (x 15 13)
        have b27691 := hb (x 14 1 && x 14 14)
        clear * - r27688 b27689 b27690 b27691 d27604 d27683
        omega
      have d27692 : (x 15 1).toNat = 1 := by
        have r27693 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
        have b27694 := hb (x 15 1)
        have b27695 := hb (x 15 13)
        clear * - r27693 b27694 b27695 d27687
        omega
      have d27696 : (x 16 14).toNat = 0 := by
        have r27697 : (x 16 14).toNat + (x 15 1).toNat = 1 := hd14 16
        have b27698 := hb (x 15 1)
        have b27699 := hb (x 16 14)
        clear * - r27697 b27698 b27699 d27692
        omega
      have d27700 : (x 16 1 && x 16 14).toNat = 0 := by
        have r27701 := hand2 (x 16 1) (x 16 14)
        have b27702 := hb (x 16 14)
        have b27703 := hb (x 16 1 && x 16 14)
        clear * - r27701 b27702 b27703 d27696
        omega
      have d27704 : (x 17 13).toNat = 1 := by
        have r27705 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := hcov13 17
        have b27706 := hb (x 15 2)
        have b27707 := hb (x 17 13)
        have b27708 := hb (x 16 1 && x 16 14)
        clear * - r27705 b27706 b27707 b27708 d27700 d27675
        omega
      have d27709 : (x 17 1).toNat = 1 := by
        have r27710 : (x 17 13).toNat ≤ (x 17 1).toNat := himp _ _ (hp13 17)
        have b27711 := hb (x 17 1)
        have b27712 := hb (x 17 13)
        clear * - r27710 b27711 b27712 d27704
        omega
      have d27713 : (x 18 14).toNat = 0 := by
        have r27714 : (x 18 14).toNat + (x 17 1).toNat = 1 := hd14 18
        have b27715 := hb (x 17 1)
        have b27716 := hb (x 18 14)
        clear * - r27714 b27715 b27716 d27709
        omega
      have d27717 : (x 18 1 && x 18 14).toNat = 0 := by
        have r27718 := hand2 (x 18 1) (x 18 14)
        have b27719 := hb (x 18 14)
        have b27720 := hb (x 18 1 && x 18 14)
        clear * - r27718 b27719 b27720 d27713
        omega
      have d27721 : (x 19 13).toNat = 1 := by
        have r27722 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := hcov13 19
        have b27723 := hb (x 17 2)
        have b27724 := hb (x 19 13)
        have b27725 := hb (x 18 1 && x 18 14)
        clear * - r27722 b27723 b27724 b27725 d27717 d27671
        omega
      have d27726 : (x 18 2).toNat = 0 := by
        have r27727 : (x 18 2).toNat ≤ (x 18 14).toNat := himp _ _ (hp2 18)
        have b27728 := hb (x 18 2)
        have b27729 := hb (x 18 14)
        clear * - r27727 b27728 b27729 d27713
        omega
      have d27730 : (x 20 12).toNat = 0 := by
        have r27731 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
        have e27732 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
        have e27733 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
        have b27734 := hb (x 17 3)
        have b27735 := hb (x 18 2)
        have b27736 := hb (x 19 13)
        have b27737 := hb (x 20 12)
        clear * - r27731 e27732 e27733 b27734 b27735 b27736 b27737 d27721 d27726
        omega
      have d27738 : (x 17 3).toNat = 0 := by
        have r27739 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
        have e27740 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
        have e27741 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
        have b27742 := hb (x 17 3)
        have b27743 := hb (x 18 2)
        have b27744 := hb (x 19 13)
        have b27745 := hb (x 20 12)
        clear * - r27739 e27740 e27741 b27742 b27743 b27744 b27745 d27730 d27721 d27726
        omega
      have d27746 : (x 17 11).toNat = 0 := by
        have r27747 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
        have b27748 := hb (x 17 3)
        have b27749 := hb (x 17 11)
        clear * - r27747 b27748 b27749 d27738
        omega
      have d27750 : (x 16 12).toNat = 0 := by
        have r27751 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
        have e27752 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
        have e27753 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
        have b27754 := hb (x 13 3)
        have b27755 := hb (x 14 2)
        have b27756 := hb (x 15 13)
        have b27757 := hb (x 16 12)
        clear * - r27751 e27752 e27753 b27754 b27755 b27756 b27757 d27687 d27612
        omega
      have d27758 : (x 16 1 && x 16 12).toNat = 0 := by
        have r27759 := hand2 (x 16 1) (x 16 12)
        have b27760 := hb (x 16 12)
        have b27761 := hb (x 16 1 && x 16 12)
        clear * - r27759 b27760 b27761 d27750
        omega
      have d27762 : (x 13 12).toNat = 0 := by
        have r27763 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
        have e27764 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
        have e27765 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
        have b27766 := hb (x 10 3)
        have b27767 := hb (x 11 2)
        have b27768 := hb (x 12 13)
        have b27769 := hb (x 13 12)
        clear * - r27763 e27764 e27765 b27766 b27767 b27768 b27769 d27624 d27545
        omega
      have d27770 : (x 13 4).toNat = 0 := by
        have r27771 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
        have b27772 := hb (x 13 4)
        have b27773 := hb (x 13 12)
        clear * - r27771 b27772 b27773 d27762
        omega
      have r27774 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := hcov11 17
      have b27775 := hb (x 13 4)
      have b27776 := hb (x 17 11)
      have b27777 := hb (x 16 1 && x 16 12)
      have b27778 := hb (x 15 2 && x 15 13)
      have b27779 := hb (x 14 3 && x 14 14)
      linarith only [r27774, b27775, b27776, b27777, b27778, b27779, d27746, d27758, d27679, d27608, d27770]
  · have f27780 : (x 0 12).toNat = 1 := by rw [h25939]; rfl
    have d27781 : (x (-1) 13).toNat = 0 := by
      have r27782 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := hd12 0
      have e27783 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e27784 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have b27785 := hb (x (-3) 3)
      have b27786 := hb (x (-2) 2)
      have b27787 := hb (x (-1) 13)
      have b27788 := hb (x 0 12)
      clear * - r27782 e27783 e27784 b27785 b27786 b27787 b27788 f27780
      omega
    have d27789 : (x (-3) 2).toNat = 1 := by
      have r27790 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := hcov13 (-1)
      have b27791 := hb (x (-3) 2)
      have b27792 := hb (x (-1) 13)
      have b27793 := hb (x (-2) 1 && x (-2) 14)
      clear * - r27790 b27791 b27792 b27793 d27781 g34
      omega
    have d27794 : (x (-1) 12).toNat = 0 := by
      have r27795 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
      have e27796 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e27797 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b27798 := hb (x (-4) 3)
      have b27799 := hb (x (-3) 2)
      have b27800 := hb (x (-2) 13)
      have b27801 := hb (x (-1) 12)
      clear * - r27795 e27796 e27797 b27798 b27799 b27800 b27801 g3 d27789
      omega
    have d27802 : (x (-1) 4).toNat = 0 := by
      have r27803 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
      have b27804 := hb (x (-1) 4)
      have b27805 := hb (x (-1) 12)
      clear * - r27803 b27804 b27805 d27794
      omega
    have d27806 : (x 3 11).toNat = 1 := by
      have r27807 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := hcov11 3
      have b27808 := hb (x (-1) 4)
      have b27809 := hb (x 3 11)
      have b27810 := hb (x 2 1 && x 2 12)
      have b27811 := hb (x 1 2 && x 1 13)
      have b27812 := hb (x 0 3 && x 0 14)
      clear * - r27807 b27808 b27809 b27810 b27811 b27812 g29 g30 g31 d27802
      omega
    have d27813 : (x 3 3).toNat = 1 := by
      have r27814 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
      have b27815 := hb (x 3 3)
      have b27816 := hb (x 3 11)
      clear * - r27814 b27815 b27816 d27806
      omega
    have d27817 : (x 6 12).toNat = 0 := by
      have r27818 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
      have e27819 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e27820 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b27821 := hb (x 3 3)
      have b27822 := hb (x 4 2)
      have b27823 := hb (x 5 13)
      have b27824 := hb (x 6 12)
      clear * - r27818 e27819 e27820 b27821 b27822 b27823 b27824 d27813
      omega
    have d27825 : (x 6 1 && x 6 12).toNat = 0 := by
      have r27826 := hand2 (x 6 1) (x 6 12)
      have b27827 := hb (x 6 12)
      have b27828 := hb (x 6 1 && x 6 12)
      clear * - r27826 b27827 b27828 d27817
      omega
    have d27829 : (x 6 4).toNat = 0 := by
      have r27830 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
      have b27831 := hb (x 6 4)
      have b27832 := hb (x 6 12)
      clear * - r27830 b27831 b27832 d27817
      omega
    have d27833 : (x 5 13).toNat = 0 := by
      have r27834 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
      have e27835 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e27836 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b27837 := hb (x 3 3)
      have b27838 := hb (x 4 2)
      have b27839 := hb (x 5 13)
      have b27840 := hb (x 6 12)
      clear * - r27834 e27835 e27836 b27837 b27838 b27839 b27840 d27817 d27813
      omega
    have d27841 : (x 5 2 && x 5 13).toNat = 0 := by
      have r27842 := hand2 (x 5 2) (x 5 13)
      have b27843 := hb (x 5 13)
      have b27844 := hb (x 5 2 && x 5 13)
      clear * - r27842 b27843 b27844 d27833
      omega
    have d27845 : (x 4 1 && x 4 14).toNat = 1 := by
      have r27846 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := hcov13 5
      have b27847 := hb (x 3 2)
      have b27848 := hb (x 5 13)
      have b27849 := hb (x 4 1 && x 4 14)
      clear * - r27846 b27847 b27848 b27849 d27833 g17
      omega
    have d27850 : (x 4 1).toNat = 1 := by
      have r27851 := hand1 (x 4 1) (x 4 14)
      have b27852 := hb (x 4 1)
      have b27853 := hb (x 4 1 && x 4 14)
      clear * - r27851 b27852 b27853 d27845
      omega
    have d27854 : (x 5 14).toNat = 0 := by
      have r27855 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
      have b27856 := hb (x 4 1)
      have b27857 := hb (x 5 14)
      clear * - r27855 b27856 b27857 d27850
      omega
    have d27858 : (x 5 1 && x 5 14).toNat = 0 := by
      have r27859 := hand2 (x 5 1) (x 5 14)
      have b27860 := hb (x 5 14)
      have b27861 := hb (x 5 1 && x 5 14)
      clear * - r27859 b27860 b27861 d27854
      omega
    have d27862 : (x 5 2).toNat = 0 := by
      have r27863 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
      have b27864 := hb (x 5 2)
      have b27865 := hb (x 5 14)
      clear * - r27863 b27864 b27865 d27854
      omega
    have d27866 : (x 4 2).toNat = 0 := by
      have r27867 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
      have e27868 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e27869 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b27870 := hb (x 3 3)
      have b27871 := hb (x 4 2)
      have b27872 := hb (x 5 13)
      have b27873 := hb (x 6 12)
      clear * - r27867 e27868 e27869 b27870 b27871 b27872 b27873 d27817 d27833 d27813
      omega
    have d27874 : (x 4 2 && x 4 13).toNat = 0 := by
      have r27875 := hand1 (x 4 2) (x 4 13)
      have b27876 := hb (x 4 2)
      have b27877 := hb (x 4 2 && x 4 13)
      clear * - r27875 b27876 b27877 d27866
      omega
    have d27878 : (x 6 13).toNat = 1 := by
      have r27879 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := hcov13 6
      have b27880 := hb (x 4 2)
      have b27881 := hb (x 6 13)
      have b27882 := hb (x 5 1 && x 5 14)
      clear * - r27879 b27880 b27881 b27882 d27858 d27866
      omega
    have d27883 : (x 6 1).toNat = 1 := by
      have r27884 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
      have b27885 := hb (x 6 1)
      have b27886 := hb (x 6 13)
      clear * - r27884 b27885 b27886 d27878
      omega
    have d27887 : (x 7 14).toNat = 0 := by
      have r27888 : (x 7 14).toNat + (x 6 1).toNat = 1 := hd14 7
      have b27889 := hb (x 6 1)
      have b27890 := hb (x 7 14)
      clear * - r27888 b27889 b27890 d27883
      omega
    have d27891 : (x 7 3 && x 7 14).toNat = 0 := by
      have r27892 := hand2 (x 7 3) (x 7 14)
      have b27893 := hb (x 7 14)
      have b27894 := hb (x 7 3 && x 7 14)
      clear * - r27892 b27893 b27894 d27887
      omega
    have d27895 : (x 7 2).toNat = 0 := by
      have r27896 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
      have b27897 := hb (x 7 2)
      have b27898 := hb (x 7 14)
      clear * - r27896 b27897 b27898 d27887
      omega
    have d27899 : (x 7 12).toNat = 0 := by
      have r27900 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
      have e27901 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
      have e27902 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
      have b27903 := hb (x 4 3)
      have b27904 := hb (x 5 2)
      have b27905 := hb (x 6 13)
      have b27906 := hb (x 7 12)
      clear * - r27900 e27901 e27902 b27903 b27904 b27905 b27906 d27878 d27862
      omega
    have d27907 : (x 7 4).toNat = 0 := by
      have r27908 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
      have b27909 := hb (x 7 4)
      have b27910 := hb (x 7 12)
      clear * - r27908 b27909 b27910 d27899
      omega
    have d27911 : (x 4 3).toNat = 0 := by
      have r27912 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
      have e27913 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
      have e27914 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
      have b27915 := hb (x 4 3)
      have b27916 := hb (x 5 2)
      have b27917 := hb (x 6 13)
      have b27918 := hb (x 7 12)
      clear * - r27912 e27913 e27914 b27915 b27916 b27917 b27918 d27899 d27878 d27862
      omega
    have d27919 : (x 4 3 && x 4 14).toNat = 0 := by
      have r27920 := hand1 (x 4 3) (x 4 14)
      have b27921 := hb (x 4 3)
      have b27922 := hb (x 4 3 && x 4 14)
      clear * - r27920 b27921 b27922 d27911
      omega
    have d27923 : (x 7 11).toNat = 1 := by
      have r27924 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := hcov11 7
      have b27925 := hb (x 3 4)
      have b27926 := hb (x 7 11)
      have b27927 := hb (x 6 1 && x 6 12)
      have b27928 := hb (x 5 2 && x 5 13)
      have b27929 := hb (x 4 3 && x 4 14)
      clear * - r27924 b27925 b27926 b27927 b27928 b27929 d27825 d27841 d27919 g18
      omega
    have d27930 : (x 7 3).toNat = 1 := by
      have r27931 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
      have b27932 := hb (x 7 3)
      have b27933 := hb (x 7 11)
      clear * - r27931 b27932 b27933 d27923
      omega
    have d27934 : (x 10 12).toNat = 0 := by
      have r27935 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
      have e27936 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e27937 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b27938 := hb (x 7 3)
      have b27939 := hb (x 8 2)
      have b27940 := hb (x 9 13)
      have b27941 := hb (x 10 12)
      clear * - r27935 e27936 e27937 b27938 b27939 b27940 b27941 d27930
      omega
    have d27942 : (x 10 1 && x 10 12).toNat = 0 := by
      have r27943 := hand2 (x 10 1) (x 10 12)
      have b27944 := hb (x 10 12)
      have b27945 := hb (x 10 1 && x 10 12)
      clear * - r27943 b27944 b27945 d27934
      omega
    have d27946 : (x 10 4).toNat = 0 := by
      have r27947 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
      have b27948 := hb (x 10 4)
      have b27949 := hb (x 10 12)
      clear * - r27947 b27948 b27949 d27934
      omega
    have d27950 : (x 9 13).toNat = 0 := by
      have r27951 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
      have e27952 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e27953 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b27954 := hb (x 7 3)
      have b27955 := hb (x 8 2)
      have b27956 := hb (x 9 13)
      have b27957 := hb (x 10 12)
      clear * - r27951 e27952 e27953 b27954 b27955 b27956 b27957 d27934 d27930
      omega
    have d27958 : (x 9 2 && x 9 13).toNat = 0 := by
      have r27959 := hand2 (x 9 2) (x 9 13)
      have b27960 := hb (x 9 13)
      have b27961 := hb (x 9 2 && x 9 13)
      clear * - r27959 b27960 b27961 d27950
      omega
    have d27962 : (x 8 1 && x 8 14).toNat = 1 := by
      have r27963 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := hcov13 9
      have b27964 := hb (x 7 2)
      have b27965 := hb (x 9 13)
      have b27966 := hb (x 8 1 && x 8 14)
      clear * - r27963 b27964 b27965 b27966 d27950 d27895
      omega
    have d27967 : (x 8 14).toNat = 1 := by
      have r27968 := hand2 (x 8 1) (x 8 14)
      have b27969 := hb (x 8 14)
      have b27970 := hb (x 8 1 && x 8 14)
      clear * - r27968 b27969 b27970 d27962
      omega
    have d27971 : (x 7 1).toNat = 0 := by
      have r27972 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
      have b27973 := hb (x 7 1)
      have b27974 := hb (x 8 14)
      clear * - r27972 b27973 b27974 d27967
      omega
    have d27975 : (x 7 13).toNat = 0 := by
      have r27976 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
      have b27977 := hb (x 7 1)
      have b27978 := hb (x 7 13)
      clear * - r27976 b27977 b27978 d27971
      omega
    have d27979 : (x 6 1 && x 6 14).toNat = 1 := by
      have r27980 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
      have b27981 := hb (x 5 2)
      have b27982 := hb (x 7 13)
      have b27983 := hb (x 6 1 && x 6 14)
      clear * - r27980 b27981 b27982 b27983 d27975 d27862
      omega
    have d27984 : (x 6 14).toNat = 1 := by
      have r27985 := hand2 (x 6 1) (x 6 14)
      have b27986 := hb (x 6 14)
      have b27987 := hb (x 6 1 && x 6 14)
      clear * - r27985 b27986 b27987 d27979
      omega
    have d27988 : (x 5 1).toNat = 0 := by
      have r27989 : (x 6 14).toNat + (x 5 1).toNat = 1 := hd14 6
      have b27990 := hb (x 5 1)
      have b27991 := hb (x 6 14)
      clear * - r27989 b27990 b27991 d27984
      omega
    have d27992 : (x 5 1 && x 5 12).toNat = 0 := by
      have r27993 := hand1 (x 5 1) (x 5 12)
      have b27994 := hb (x 5 1)
      have b27995 := hb (x 5 1 && x 5 12)
      clear * - r27993 b27994 b27995 d27988
      omega
    have d27996 : (x 6 11).toNat = 1 := by
      have r27997 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := hcov11 6
      have b27998 := hb (x 2 4)
      have b27999 := hb (x 6 11)
      have b28000 := hb (x 5 1 && x 5 12)
      have b28001 := hb (x 4 2 && x 4 13)
      have b28002 := hb (x 3 3 && x 3 14)
      clear * - r27997 b27998 b27999 b28000 b28001 b28002 d27992 d27874 g33 g16
      omega
    have d28003 : (x 6 3).toNat = 1 := by
      have r28004 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
      have b28005 := hb (x 6 3)
      have b28006 := hb (x 6 11)
      clear * - r28004 b28005 b28006 d27996
      omega
    have d28007 : (x 9 12).toNat = 0 := by
      have r28008 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
      have e28009 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
      have e28010 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
      have b28011 := hb (x 6 3)
      have b28012 := hb (x 7 2)
      have b28013 := hb (x 8 13)
      have b28014 := hb (x 9 12)
      clear * - r28008 e28009 e28010 b28011 b28012 b28013 b28014 d27895 d28003
      omega
    have d28015 : (x 9 1 && x 9 12).toNat = 0 := by
      have r28016 := hand2 (x 9 1) (x 9 12)
      have b28017 := hb (x 9 12)
      have b28018 := hb (x 9 1 && x 9 12)
      clear * - r28016 b28017 b28018 d28007
      omega
    have d28019 : (x 8 13).toNat = 0 := by
      have r28020 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
      have e28021 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
      have e28022 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
      have b28023 := hb (x 6 3)
      have b28024 := hb (x 7 2)
      have b28025 := hb (x 8 13)
      have b28026 := hb (x 9 12)
      clear * - r28020 e28021 e28022 b28023 b28024 b28025 b28026 d28007 d27895 d28003
      omega
    have d28027 : (x 8 2 && x 8 13).toNat = 0 := by
      have r28028 := hand2 (x 8 2) (x 8 13)
      have b28029 := hb (x 8 13)
      have b28030 := hb (x 8 2 && x 8 13)
      clear * - r28028 b28029 b28030 d28019
      omega
    have d28031 : (x 10 11).toNat = 1 := by
      have r28032 : 1 ≤ (x 10 11).toNat + (x 9 1 && x 9 12).toNat + (x 8 2 && x 8 13).toNat + (x 7 3 && x 7 14).toNat + (x 6 4).toNat := hcov11 10
      have b28033 := hb (x 6 4)
      have b28034 := hb (x 10 11)
      have b28035 := hb (x 9 1 && x 9 12)
      have b28036 := hb (x 8 2 && x 8 13)
      have b28037 := hb (x 7 3 && x 7 14)
      clear * - r28032 b28033 b28034 b28035 b28036 b28037 d28015 d28027 d27891 d27829
      omega
    have d28038 : (x 10 3).toNat = 1 := by
      have r28039 : (x 10 11).toNat ≤ (x 10 3).toNat := himp _ _ (hp11 10)
      have b28040 := hb (x 10 3)
      have b28041 := hb (x 10 11)
      clear * - r28039 b28040 b28041 d28031
      omega
    have d28042 : (x 13 12).toNat = 0 := by
      have r28043 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
      have e28044 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
      have e28045 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
      have b28046 := hb (x 10 3)
      have b28047 := hb (x 11 2)
      have b28048 := hb (x 12 13)
      have b28049 := hb (x 13 12)
      clear * - r28043 e28044 e28045 b28046 b28047 b28048 b28049 d28038
      omega
    have d28050 : (x 13 1 && x 13 12).toNat = 0 := by
      have r28051 := hand2 (x 13 1) (x 13 12)
      have b28052 := hb (x 13 12)
      have b28053 := hb (x 13 1 && x 13 12)
      clear * - r28051 b28052 b28053 d28042
      omega
    have d28054 : (x 12 13).toNat = 0 := by
      have r28055 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
      have e28056 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
      have e28057 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
      have b28058 := hb (x 10 3)
      have b28059 := hb (x 11 2)
      have b28060 := hb (x 12 13)
      have b28061 := hb (x 13 12)
      clear * - r28055 e28056 e28057 b28058 b28059 b28060 b28061 d28042 d28038
      omega
    have d28062 : (x 12 2 && x 12 13).toNat = 0 := by
      have r28063 := hand2 (x 12 2) (x 12 13)
      have b28064 := hb (x 12 13)
      have b28065 := hb (x 12 2 && x 12 13)
      clear * - r28063 b28064 b28065 d28054
      omega
    have d28066 : (x 11 2).toNat = 0 := by
      have r28067 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
      have e28068 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
      have e28069 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
      have b28070 := hb (x 10 3)
      have b28071 := hb (x 11 2)
      have b28072 := hb (x 12 13)
      have b28073 := hb (x 13 12)
      clear * - r28067 e28068 e28069 b28070 b28071 b28072 b28073 d28042 d28054 d28038
      omega
    have d28074 : (x 8 1).toNat = 1 := by
      have r28075 := hand1 (x 8 1) (x 8 14)
      have b28076 := hb (x 8 1)
      have b28077 := hb (x 8 1 && x 8 14)
      clear * - r28075 b28076 b28077 d27962
      omega
    have d28078 : (x 9 14).toNat = 0 := by
      have r28079 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
      have b28080 := hb (x 8 1)
      have b28081 := hb (x 9 14)
      clear * - r28079 b28080 b28081 d28074
      omega
    have d28082 : (x 9 1 && x 9 14).toNat = 0 := by
      have r28083 := hand2 (x 9 1) (x 9 14)
      have b28084 := hb (x 9 14)
      have b28085 := hb (x 9 1 && x 9 14)
      clear * - r28083 b28084 b28085 d28078
      omega
    have d28086 : (x 9 2).toNat = 0 := by
      have r28087 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
      have b28088 := hb (x 9 2)
      have b28089 := hb (x 9 14)
      clear * - r28087 b28088 b28089 d28078
      omega
    have d28090 : (x 8 2).toNat = 0 := by
      have r28091 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
      have e28092 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e28093 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b28094 := hb (x 7 3)
      have b28095 := hb (x 8 2)
      have b28096 := hb (x 9 13)
      have b28097 := hb (x 10 12)
      clear * - r28091 e28092 e28093 b28094 b28095 b28096 b28097 d27934 d27950 d27930
      omega
    have d28098 : (x 10 13).toNat = 1 := by
      have r28099 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := hcov13 10
      have b28100 := hb (x 8 2)
      have b28101 := hb (x 10 13)
      have b28102 := hb (x 9 1 && x 9 14)
      clear * - r28099 b28100 b28101 b28102 d28082 d28090
      omega
    have d28103 : (x 10 1).toNat = 1 := by
      have r28104 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
      have b28105 := hb (x 10 1)
      have b28106 := hb (x 10 13)
      clear * - r28104 b28105 b28106 d28098
      omega
    have d28107 : (x 11 14).toNat = 0 := by
      have r28108 : (x 11 14).toNat + (x 10 1).toNat = 1 := hd14 11
      have b28109 := hb (x 10 1)
      have b28110 := hb (x 11 14)
      clear * - r28108 b28109 b28110 d28103
      omega
    have d28111 : (x 11 1 && x 11 14).toNat = 0 := by
      have r28112 := hand2 (x 11 1) (x 11 14)
      have b28113 := hb (x 11 14)
      have b28114 := hb (x 11 1 && x 11 14)
      clear * - r28112 b28113 b28114 d28107
      omega
    have d28115 : (x 10 2).toNat = 1 := by
      have r28116 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := hcov13 12
      have b28117 := hb (x 10 2)
      have b28118 := hb (x 12 13)
      have b28119 := hb (x 11 1 && x 11 14)
      clear * - r28116 b28117 b28118 b28119 d28054 d28111
      omega
    have d28120 : (x 12 12).toNat = 0 := by
      have r28121 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
      have e28122 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
      have e28123 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
      have b28124 := hb (x 9 3)
      have b28125 := hb (x 10 2)
      have b28126 := hb (x 11 13)
      have b28127 := hb (x 12 12)
      clear * - r28121 e28122 e28123 b28124 b28125 b28126 b28127 d28115
      omega
    have d28128 : (x 12 4).toNat = 0 := by
      have r28129 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
      have b28130 := hb (x 12 4)
      have b28131 := hb (x 12 12)
      clear * - r28129 b28130 b28131 d28120
      omega
    have d28132 : (x 12 4 && x 12 14).toNat = 0 := by
      have r28133 := hand1 (x 12 4) (x 12 14)
      have b28134 := hb (x 12 4)
      have b28135 := hb (x 12 4 && x 12 14)
      clear * - r28133 b28134 b28135 d28128
      omega
    have d28136 : (x 11 13).toNat = 0 := by
      have r28137 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
      have e28138 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
      have e28139 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
      have b28140 := hb (x 9 3)
      have b28141 := hb (x 10 2)
      have b28142 := hb (x 11 13)
      have b28143 := hb (x 12 12)
      clear * - r28137 e28138 e28139 b28140 b28141 b28142 b28143 d28120 d28115
      omega
    have d28144 : (x 11 5).toNat = 0 := by
      have r28145 : (x 11 5).toNat ≤ (x 11 13).toNat := himp _ _ (hp5 11)
      have b28146 := hb (x 11 5)
      have b28147 := hb (x 11 13)
      clear * - r28145 b28146 b28147 d28136
      omega
    have d28148 : (x 11 3 && x 11 14).toNat = 0 := by
      have r28149 := hand2 (x 11 3) (x 11 14)
      have b28150 := hb (x 11 14)
      have b28151 := hb (x 11 3 && x 11 14)
      clear * - r28149 b28150 b28151 d28107
      omega
    have d28152 : (x 14 11).toNat = 1 := by
      have r28153 : 1 ≤ (x 14 11).toNat + (x 13 1 && x 13 12).toNat + (x 12 2 && x 12 13).toNat + (x 11 3 && x 11 14).toNat + (x 10 4).toNat := hcov11 14
      have b28154 := hb (x 10 4)
      have b28155 := hb (x 14 11)
      have b28156 := hb (x 13 1 && x 13 12)
      have b28157 := hb (x 12 2 && x 12 13)
      have b28158 := hb (x 11 3 && x 11 14)
      clear * - r28153 b28154 b28155 b28156 b28157 b28158 d28050 d28062 d28148 d27946
      omega
    have d28159 : (x 14 3).toNat = 1 := by
      have r28160 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
      have b28161 := hb (x 14 3)
      have b28162 := hb (x 14 11)
      clear * - r28160 b28161 b28162 d28152
      omega
    have d28163 : (x 17 12).toNat = 0 := by
      have r28164 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
      have e28165 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
      have e28166 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
      have b28167 := hb (x 14 3)
      have b28168 := hb (x 15 2)
      have b28169 := hb (x 16 13)
      have b28170 := hb (x 17 12)
      clear * - r28164 e28165 e28166 b28167 b28168 b28169 b28170 d28159
      omega
    have d28171 : (x 16 13).toNat = 0 := by
      have r28172 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
      have e28173 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
      have e28174 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
      have b28175 := hb (x 14 3)
      have b28176 := hb (x 15 2)
      have b28177 := hb (x 16 13)
      have b28178 := hb (x 17 12)
      clear * - r28172 e28173 e28174 b28175 b28176 b28177 b28178 d28163 d28159
      omega
    have d28179 : (x 15 2).toNat = 0 := by
      have r28180 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
      have e28181 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
      have e28182 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
      have b28183 := hb (x 14 3)
      have b28184 := hb (x 15 2)
      have b28185 := hb (x 16 13)
      have b28186 := hb (x 17 12)
      clear * - r28180 e28181 e28182 b28183 b28184 b28185 b28186 d28163 d28171 d28159
      omega
    have d28187 : (x 11 12).toNat = 0 := by
      have r28188 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
      have e28189 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
      have e28190 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
      have b28191 := hb (x 8 3)
      have b28192 := hb (x 9 2)
      have b28193 := hb (x 10 13)
      have b28194 := hb (x 11 12)
      clear * - r28188 e28189 e28190 b28191 b28192 b28193 b28194 d28098 d28086
      omega
    have d28195 : (x 11 4).toNat = 0 := by
      have r28196 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
      have b28197 := hb (x 11 4)
      have b28198 := hb (x 11 12)
      clear * - r28196 b28197 b28198 d28187
      omega
    have d28199 : (x 8 3).toNat = 0 := by
      have r28200 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
      have e28201 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
      have e28202 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
      have b28203 := hb (x 8 3)
      have b28204 := hb (x 9 2)
      have b28205 := hb (x 10 13)
      have b28206 := hb (x 11 12)
      clear * - r28200 e28201 e28202 b28203 b28204 b28205 b28206 d28187 d28098 d28086
      omega
    have d28207 : (x 8 3 && x 8 14).toNat = 0 := by
      have r28208 := hand1 (x 8 3) (x 8 14)
      have b28209 := hb (x 8 3)
      have b28210 := hb (x 8 3 && x 8 14)
      clear * - r28208 b28209 b28210 d28199
      omega
    have d28211 : (x 11 11).toNat = 1 := by
      have r28212 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := hcov11 11
      have b28213 := hb (x 7 4)
      have b28214 := hb (x 11 11)
      have b28215 := hb (x 10 1 && x 10 12)
      have b28216 := hb (x 9 2 && x 9 13)
      have b28217 := hb (x 8 3 && x 8 14)
      clear * - r28212 b28213 b28214 b28215 b28216 b28217 d27942 d27958 d28207 d27907
      omega
    have d28218 : (x 11 3).toNat = 1 := by
      have r28219 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
      have b28220 := hb (x 11 3)
      have b28221 := hb (x 11 11)
      clear * - r28219 b28220 b28221 d28211
      omega
    have d28222 : (x 14 12).toNat = 0 := by
      have r28223 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
      have e28224 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
      have e28225 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
      have b28226 := hb (x 11 3)
      have b28227 := hb (x 12 2)
      have b28228 := hb (x 13 13)
      have b28229 := hb (x 14 12)
      clear * - r28223 e28224 e28225 b28226 b28227 b28228 b28229 d28218
      omega
    have d28230 : (x 14 1 && x 14 12).toNat = 0 := by
      have r28231 := hand2 (x 14 1) (x 14 12)
      have b28232 := hb (x 14 12)
      have b28233 := hb (x 14 1 && x 14 12)
      clear * - r28231 b28232 b28233 d28222
      omega
    have d28234 : (x 14 2 && x 14 12).toNat = 0 := by
      have r28235 := hand2 (x 14 2) (x 14 12)
      have b28236 := hb (x 14 12)
      have b28237 := hb (x 14 2 && x 14 12)
      clear * - r28235 b28236 b28237 d28222
      omega
    have d28238 : (x 13 13).toNat = 0 := by
      have r28239 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
      have e28240 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
      have e28241 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
      have b28242 := hb (x 11 3)
      have b28243 := hb (x 12 2)
      have b28244 := hb (x 13 13)
      have b28245 := hb (x 14 12)
      clear * - r28239 e28240 e28241 b28242 b28243 b28244 b28245 d28222 d28218
      omega
    have d28246 : (x 13 2 && x 13 13).toNat = 0 := by
      have r28247 := hand2 (x 13 2) (x 13 13)
      have b28248 := hb (x 13 13)
      have b28249 := hb (x 13 2 && x 13 13)
      clear * - r28247 b28248 b28249 d28238
      omega
    have d28250 : (x 13 3 && x 13 13).toNat = 0 := by
      have r28251 := hand2 (x 13 3) (x 13 13)
      have b28252 := hb (x 13 13)
      have b28253 := hb (x 13 3 && x 13 13)
      clear * - r28251 b28252 b28253 d28238
      omega
    have d28254 : (x 12 1 && x 12 14).toNat = 1 := by
      have r28255 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := hcov13 13
      have b28256 := hb (x 11 2)
      have b28257 := hb (x 13 13)
      have b28258 := hb (x 12 1 && x 12 14)
      clear * - r28255 b28256 b28257 b28258 d28238 d28066
      omega
    have d28259 : (x 12 1).toNat = 1 := by
      have r28260 := hand1 (x 12 1) (x 12 14)
      have b28261 := hb (x 12 1)
      have b28262 := hb (x 12 1 && x 12 14)
      clear * - r28260 b28261 b28262 d28254
      omega
    have d28263 : (x 13 14).toNat = 0 := by
      have r28264 : (x 13 14).toNat + (x 12 1).toNat = 1 := hd14 13
      have b28265 := hb (x 12 1)
      have b28266 := hb (x 13 14)
      clear * - r28264 b28265 b28266 d28259
      omega
    have d28267 : (x 13 1 && x 13 14).toNat = 0 := by
      have r28268 := hand2 (x 13 1) (x 13 14)
      have b28269 := hb (x 13 14)
      have b28270 := hb (x 13 1 && x 13 14)
      clear * - r28268 b28269 b28270 d28263
      omega
    have d28271 : (x 13 2).toNat = 0 := by
      have r28272 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
      have b28273 := hb (x 13 2)
      have b28274 := hb (x 13 14)
      clear * - r28272 b28273 b28274 d28263
      omega
    have d28275 : (x 12 2).toNat = 0 := by
      have r28276 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
      have e28277 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
      have e28278 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
      have b28279 := hb (x 11 3)
      have b28280 := hb (x 12 2)
      have b28281 := hb (x 13 13)
      have b28282 := hb (x 14 12)
      clear * - r28276 e28277 e28278 b28279 b28280 b28281 b28282 d28222 d28238 d28218
      omega
    have d28283 : (x 14 13).toNat = 1 := by
      have r28284 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
      have b28285 := hb (x 12 2)
      have b28286 := hb (x 14 13)
      have b28287 := hb (x 13 1 && x 13 14)
      clear * - r28284 b28285 b28286 b28287 d28267 d28275
      omega
    have d28288 : (x 15 12).toNat = 0 := by
      have r28289 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
      have e28290 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
      have e28291 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
      have b28292 := hb (x 12 3)
      have b28293 := hb (x 13 2)
      have b28294 := hb (x 14 13)
      have b28295 := hb (x 15 12)
      clear * - r28289 e28290 e28291 b28292 b28293 b28294 b28295 d28283 d28271
      omega
    have d28296 : (x 12 3).toNat = 0 := by
      have r28297 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
      have e28298 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
      have e28299 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
      have b28300 := hb (x 12 3)
      have b28301 := hb (x 13 2)
      have b28302 := hb (x 14 13)
      have b28303 := hb (x 15 12)
      clear * - r28297 e28298 e28299 b28300 b28301 b28302 b28303 d28288 d28283 d28271
      omega
    have d28304 : (x 12 3 && x 12 14).toNat = 0 := by
      have r28305 := hand1 (x 12 3) (x 12 14)
      have b28306 := hb (x 12 3)
      have b28307 := hb (x 12 3 && x 12 14)
      clear * - r28305 b28306 b28307 d28296
      omega
    have d28308 : (x 15 11).toNat = 1 := by
      have r28309 : 1 ≤ (x 15 11).toNat + (x 14 1 && x 14 12).toNat + (x 13 2 && x 13 13).toNat + (x 12 3 && x 12 14).toNat + (x 11 4).toNat := hcov11 15
      have b28310 := hb (x 11 4)
      have b28311 := hb (x 15 11)
      have b28312 := hb (x 14 1 && x 14 12)
      have b28313 := hb (x 13 2 && x 13 13)
      have b28314 := hb (x 12 3 && x 12 14)
      clear * - r28309 b28310 b28311 b28312 b28313 b28314 d28230 d28246 d28304 d28195
      omega
    have d28315 : (x 15 3).toNat = 1 := by
      have r28316 : (x 15 11).toNat ≤ (x 15 3).toNat := himp _ _ (hp11 15)
      have b28317 := hb (x 15 3)
      have b28318 := hb (x 15 11)
      clear * - r28316 b28317 b28318 d28308
      omega
    have d28319 : (x 18 12).toNat = 0 := by
      have r28320 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
      have e28321 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
      have e28322 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
      have b28323 := hb (x 15 3)
      have b28324 := hb (x 16 2)
      have b28325 := hb (x 17 13)
      have b28326 := hb (x 18 12)
      clear * - r28320 e28321 e28322 b28323 b28324 b28325 b28326 d28315
      omega
    have d28327 : (x 17 13).toNat = 0 := by
      have r28328 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
      have e28329 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
      have e28330 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
      have b28331 := hb (x 15 3)
      have b28332 := hb (x 16 2)
      have b28333 := hb (x 17 13)
      have b28334 := hb (x 18 12)
      clear * - r28328 e28329 e28330 b28331 b28332 b28333 b28334 d28319 d28315
      omega
    have d28335 : (x 16 1 && x 16 14).toNat = 1 := by
      have r28336 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := hcov13 17
      have b28337 := hb (x 15 2)
      have b28338 := hb (x 17 13)
      have b28339 := hb (x 16 1 && x 16 14)
      clear * - r28336 b28337 b28338 b28339 d28327 d28179
      omega
    have d28340 : (x 16 14).toNat = 1 := by
      have r28341 := hand2 (x 16 1) (x 16 14)
      have b28342 := hb (x 16 14)
      have b28343 := hb (x 16 1 && x 16 14)
      clear * - r28341 b28342 b28343 d28335
      omega
    have d28344 : (x 15 1).toNat = 0 := by
      have r28345 : (x 16 14).toNat + (x 15 1).toNat = 1 := hd14 16
      have b28346 := hb (x 15 1)
      have b28347 := hb (x 16 14)
      clear * - r28345 b28346 b28347 d28340
      omega
    have d28348 : (x 15 1 && x 15 11).toNat = 0 := by
      have r28349 := hand1 (x 15 1) (x 15 11)
      have b28350 := hb (x 15 1)
      have b28351 := hb (x 15 1 && x 15 11)
      clear * - r28349 b28350 b28351 d28344
      omega
    have d28352 : (x 16 2).toNat = 0 := by
      have r28353 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
      have e28354 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
      have e28355 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
      have b28356 := hb (x 15 3)
      have b28357 := hb (x 16 2)
      have b28358 := hb (x 17 13)
      have b28359 := hb (x 18 12)
      clear * - r28353 e28354 e28355 b28356 b28357 b28358 b28359 d28319 d28327 d28315
      omega
    have d28360 : (x 16 10).toNat = 0 := by
      have r28361 : (x 16 10).toNat ≤ (x 16 2).toNat := himp _ _ (hp10 16)
      have b28362 := hb (x 16 2)
      have b28363 := hb (x 16 10)
      clear * - r28361 b28362 b28363 d28352
      omega
    have r28364 : 1 ≤ (x 16 10).toNat + (x 15 1 && x 15 11).toNat + (x 14 2 && x 14 12).toNat + (x 13 3 && x 13 13).toNat + (x 12 4 && x 12 14).toNat + (x 11 5).toNat := hcov10 16
    have b28365 := hb (x 11 5)
    have b28366 := hb (x 16 10)
    have b28367 := hb (x 15 1 && x 15 11)
    have b28368 := hb (x 14 2 && x 14 12)
    have b28369 := hb (x 13 3 && x 13 13)
    have b28370 := hb (x 12 4 && x 12 14)
    linarith only [r28364, b28365, b28366, b28367, b28368, b28369, b28370, d28360, d28348, d28234, d28250, d28132, d28144]

theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0000100 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-2) 3).toNat = 0)
    (g1 : (x (-2) 5).toNat = 0)
    (g2 : (x (-2) 9).toNat = 0)
    (g3 : (x (-2) 13).toNat = 0)
    (g4 : (x (-1) 2).toNat = 1)
    (g5 : (x (-1) 8).toNat = 0)
    (g6 : (x 0 1).toNat = 1)
    (g7 : (x 0 3).toNat = 0)
    (g8 : (x 0 6).toNat = 0)
    (g9 : (x 0 7).toNat = 0)
    (g10 : (x 0 11).toNat = 0)
    (g11 : (x 1 2).toNat = 0)
    (g12 : (x 1 4).toNat = 0)
    (g13 : (x 1 6).toNat = 0)
    (g14 : (x 1 10).toNat = 0)
    (g15 : (x 2 1).toNat = 1)
    (g16 : (x 2 4).toNat = 0)
    (g17 : (x 3 2).toNat = 0)
    (g18 : (x 3 4).toNat = 0)
    (g19 : (x 1 2 && x 1 6).toNat = 0)
    (g20 : (x 0 3 && x 0 7).toNat = 0)
    (g21 : (x (-1) 4 && x (-1) 8).toNat = 0)
    (g22 : (x (-2) 5 && x (-2) 9).toNat = 0)
    (g23 : (x 0 1 && x 0 7).toNat = 0)
    (g24 : (x (-1) 2 && x (-1) 8).toNat = 0)
    (g25 : (x (-2) 3 && x (-2) 9).toNat = 0)
    (g26 : (x 3 3 && x 3 12).toNat = 0)
    (g27 : (x 2 4 && x 2 13).toNat = 0)
    (g28 : (x 1 5 && x 1 14).toNat = 0)
    (g29 : (x 2 1 && x 2 12).toNat = 0)
    (g30 : (x 1 2 && x 1 13).toNat = 0)
    (g31 : (x 0 3 && x 0 14).toNat = 0)
    (g32 : (x 3 2 && x 3 13).toNat = 0)
    (g33 : (x 3 3 && x 3 14).toNat = 0)
    (g34 : (x (-2) 1 && x (-2) 14).toNat = 0)
    (g35 : (x 3 1 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0000100_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35
