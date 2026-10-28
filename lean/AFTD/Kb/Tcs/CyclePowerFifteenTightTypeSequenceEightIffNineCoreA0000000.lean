import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a0000000

Topic: combinatorics   Node: 33b3f45f75ec

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core: under the layer-free tight-cover constraints for k = 15 and 60 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a0000000_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-7) 7).toNat = 0)
    (g1 : (x (-6) 6).toNat = 0)
    (g2 : (x (-5) 5).toNat = 0)
    (g3 : (x (-4) 4).toNat = 0)
    (g4 : (x (-3) 11).toNat = 0)
    (g5 : (x (-2) 10).toNat = 0)
    (g6 : (x (-1) 1).toNat = 1)
    (g7 : (x (-1) 9).toNat = 0)
    (g8 : (x 0 1).toNat = 0)
    (g9 : (x 0 2).toNat = 0)
    (g10 : (x 0 3).toNat = 0)
    (g11 : (x 0 4).toNat = 0)
    (g12 : (x 0 5).toNat = 0)
    (g13 : (x 0 6).toNat = 0)
    (g14 : (x 0 7).toNat = 0)
    (g15 : (x 0 8).toNat = 1)
    (g16 : (x 0 9).toNat = 0)
    (g17 : (x 0 10).toNat = 0)
    (g18 : (x 0 11).toNat = 0)
    (g19 : (x 0 12).toNat = 0)
    (g20 : (x 0 13).toNat = 0)
    (g21 : (x 1 1).toNat = 0)
    (g22 : (x 1 14).toNat = 1)
    (g23 : (x (-4) 4 && x (-4) 8).toNat = 0)
    (g24 : (x (-5) 5 && x (-5) 9).toNat = 0)
    (g25 : (x (-6) 6 && x (-6) 10).toNat = 0)
    (g26 : (x (-7) 7 && x (-7) 11).toNat = 0)
    (g27 : (x 0 7 && x 0 11).toNat = 0)
    (g28 : (x 0 1 && x 0 6).toNat = 0)
    (g29 : (x 0 3 && x 0 8).toNat = 0)
    (g30 : (x (-1) 4 && x (-1) 9).toNat = 0)
    (g31 : (x (-2) 5 && x (-2) 10).toNat = 0)
    (g32 : (x (-3) 6 && x (-3) 11).toNat = 0)
    (g33 : (x 0 9 && x 0 14).toNat = 0)
    (g34 : (x (-4) 4 && x (-4) 10).toNat = 0)
    (g35 : (x (-5) 5 && x (-5) 11).toNat = 0)
    (g36 : (x (-6) 6 && x (-6) 12).toNat = 0)
    (g37 : (x (-7) 7 && x (-7) 13).toNat = 0)
    (g38 : (x (-4) 4 && x (-4) 11).toNat = 0)
    (g39 : (x (-5) 5 && x (-5) 12).toNat = 0)
    (g40 : (x (-6) 6 && x (-6) 13).toNat = 0)
    (g41 : (x (-7) 7 && x (-7) 14).toNat = 0)
    (g42 : (x 0 1 && x 0 8).toNat = 0)
    (g43 : (x (-1) 2 && x (-1) 9).toNat = 0)
    (g44 : (x (-2) 3 && x (-2) 10).toNat = 0)
    (g45 : (x (-3) 4 && x (-3) 11).toNat = 0)
    (g46 : (x 0 7 && x 0 14).toNat = 0)
    (g47 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g48 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g49 : (x (-4) 4 && x (-4) 13).toNat = 0)
    (g50 : (x (-5) 5 && x (-5) 14).toNat = 0)
    (g51 : (x 0 1 && x 0 10).toNat = 0)
    (g52 : (x 0 5 && x 0 14).toNat = 0)
    (g53 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g54 : (x (-4) 4 && x (-4) 14).toNat = 0)
    (g55 : (x 0 3 && x 0 13).toNat = 0)
    (g56 : (x 0 4 && x 0 14).toNat = 0)
    (g57 : (x 0 1 && x 0 12).toNat = 0)
    (g58 : (x 0 3 && x 0 14).toNat = 0)
    (g59 : (x 0 1 && x 0 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d27981 : (x 1 1 && x 1 14).toNat = 0 := by
    have r27982 := hand1 (x 1 1) (x 1 14)
    have b27983 := hb (x 1 1)
    have b27984 := hb (x 1 1 && x 1 14)
    clear * - r27982 b27983 b27984 g21
    omega
  have d27985 : (x 1 13).toNat = 0 := by
    have r27986 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
    have b27987 := hb (x 1 1)
    have b27988 := hb (x 1 13)
    clear * - r27986 b27987 b27988 g21
    omega
  have d27989 : (x 1 2 && x 1 13).toNat = 0 := by
    have r27990 := hand2 (x 1 2) (x 1 13)
    have b27991 := hb (x 1 13)
    have b27992 := hb (x 1 2 && x 1 13)
    clear * - r27990 b27991 b27992 d27985
    omega
  have d27993 : (x 1 3 && x 1 13).toNat = 0 := by
    have r27994 := hand2 (x 1 3) (x 1 13)
    have b27995 := hb (x 1 13)
    have b27996 := hb (x 1 3 && x 1 13)
    clear * - r27994 b27995 b27996 d27985
    omega
  have d27997 : (x 1 4 && x 1 13).toNat = 0 := by
    have r27998 := hand2 (x 1 4) (x 1 13)
    have b27999 := hb (x 1 13)
    have b28000 := hb (x 1 4 && x 1 13)
    clear * - r27998 b27999 b28000 d27985
    omega
  have d28001 : (x 1 6 && x 1 13).toNat = 0 := by
    have r28002 := hand2 (x 1 6) (x 1 13)
    have b28003 := hb (x 1 13)
    have b28004 := hb (x 1 6 && x 1 13)
    clear * - r28002 b28003 b28004 d27985
    omega
  have d28005 : (x 1 8 && x 1 13).toNat = 0 := by
    have r28006 := hand2 (x 1 8) (x 1 13)
    have b28007 := hb (x 1 13)
    have b28008 := hb (x 1 8 && x 1 13)
    clear * - r28006 b28007 b28008 d27985
    omega
  have d28009 : (x 1 9).toNat = 0 := by
    have r28010 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
    have b28011 := hb (x 1 1)
    have b28012 := hb (x 1 9)
    clear * - r28010 b28011 b28012 g21
    omega
  have d28013 : (x 1 5).toNat = 0 := by
    have r28014 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
    have b28015 := hb (x 1 5)
    have b28016 := hb (x 1 13)
    clear * - r28014 b28015 b28016 d27985
    omega
  have d28017 : (x 1 5 && x 1 14).toNat = 0 := by
    have r28018 := hand1 (x 1 5) (x 1 14)
    have b28019 := hb (x 1 5)
    have b28020 := hb (x 1 5 && x 1 14)
    clear * - r28018 b28019 b28020 d28013
    omega
  have d28021 : (x 2 13).toNat = 1 := by
    have r28022 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b28023 := hb (x 0 2)
    have b28024 := hb (x 2 13)
    have b28025 := hb (x 1 1 && x 1 14)
    clear * - r28022 b28023 b28024 b28025 d27981 g9
    omega
  have d28026 : (x 2 1).toNat = 1 := by
    have r28027 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
    have b28028 := hb (x 2 1)
    have b28029 := hb (x 2 13)
    clear * - r28027 b28028 b28029 d28021
    omega
  have d28030 : (x 3 14).toNat = 0 := by
    have r28031 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b28032 := hb (x 2 1)
    have b28033 := hb (x 3 14)
    clear * - r28031 b28032 b28033 d28026
    omega
  have d28034 : (x 3 1 && x 3 14).toNat = 0 := by
    have r28035 := hand2 (x 3 1) (x 3 14)
    have b28036 := hb (x 3 14)
    have b28037 := hb (x 3 1 && x 3 14)
    clear * - r28035 b28036 b28037 d28030
    omega
  have d28038 : (x 3 3 && x 3 14).toNat = 0 := by
    have r28039 := hand2 (x 3 3) (x 3 14)
    have b28040 := hb (x 3 14)
    have b28041 := hb (x 3 3 && x 3 14)
    clear * - r28039 b28040 b28041 d28030
    omega
  have d28042 : (x 3 6).toNat = 0 := by
    have r28043 : (x 3 6).toNat ≤ (x 3 14).toNat := himp _ _ (hp6 3)
    have b28044 := hb (x 3 6)
    have b28045 := hb (x 3 14)
    clear * - r28043 b28044 b28045 d28030
    omega
  have d28046 : (x 3 6 && x 3 11).toNat = 0 := by
    have r28047 := hand1 (x 3 6) (x 3 11)
    have b28048 := hb (x 3 6)
    have b28049 := hb (x 3 6 && x 3 11)
    clear * - r28047 b28048 b28049 d28042
    omega
  have d28050 : (x 3 2).toNat = 0 := by
    have r28051 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
    have b28052 := hb (x 3 2)
    have b28053 := hb (x 3 14)
    clear * - r28051 b28052 b28053 d28030
    omega
  have d28054 : (x 3 2 && x 3 13).toNat = 0 := by
    have r28055 := hand1 (x 3 2) (x 3 13)
    have b28056 := hb (x 3 2)
    have b28057 := hb (x 3 2 && x 3 13)
    clear * - r28055 b28056 b28057 d28050
    omega
  have d28058 : (x 3 2 && x 3 11).toNat = 0 := by
    have r28059 := hand1 (x 3 2) (x 3 11)
    have b28060 := hb (x 3 2)
    have b28061 := hb (x 3 2 && x 3 11)
    clear * - r28059 b28060 b28061 d28050
    omega
  have d28062 : (x 3 10).toNat = 0 := by
    have r28063 : (x 3 10).toNat ≤ (x 3 2).toNat := himp _ _ (hp10 3)
    have b28064 := hb (x 3 2)
    have b28065 := hb (x 3 10)
    clear * - r28063 b28064 b28065 d28050
    omega
  have d28066 : (x (-1) 2).toNat = 1 := by
    have r28067 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b28068 := hb (x (-1) 2)
    have b28069 := hb (x 1 13)
    have b28070 := hb (x 0 1 && x 0 14)
    clear * - r28067 b28068 b28069 b28070 d27985 g59
    omega
  have d28071 : (x (-1) 14).toNat = 1 := by
    have r28072 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
    have b28073 := hb (x (-1) 2)
    have b28074 := hb (x (-1) 14)
    clear * - r28072 b28073 b28074 d28066
    omega
  have d28075 : (x (-2) 1).toNat = 0 := by
    have r28076 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b28077 := hb (x (-2) 1)
    have b28078 := hb (x (-1) 14)
    clear * - r28076 b28077 b28078 d28071
    omega
  have d28079 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
    have r28080 := hand1 (x (-2) 1) (x (-2) 14)
    have b28081 := hb (x (-2) 1)
    have b28082 := hb (x (-2) 1 && x (-2) 14)
    clear * - r28080 b28081 b28082 d28075
    omega
  have d28083 : (x (-2) 13).toNat = 0 := by
    have r28084 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
    have b28085 := hb (x (-2) 1)
    have b28086 := hb (x (-2) 13)
    clear * - r28084 b28085 b28086 d28075
    omega
  have d28087 : (x (-2) 9 && x (-2) 13).toNat = 0 := by
    have r28088 := hand2 (x (-2) 9) (x (-2) 13)
    have b28089 := hb (x (-2) 13)
    have b28090 := hb (x (-2) 9 && x (-2) 13)
    clear * - r28088 b28089 b28090 d28083
    omega
  have d28091 : (x (-2) 5).toNat = 0 := by
    have r28092 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
    have b28093 := hb (x (-2) 5)
    have b28094 := hb (x (-2) 13)
    clear * - r28092 b28093 b28094 d28083
    omega
  have d28095 : (x (-2) 9).toNat = 0 := by
    have r28096 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
    have b28097 := hb (x (-2) 1)
    have b28098 := hb (x (-2) 9)
    clear * - r28096 b28097 b28098 d28075
    omega
  have d28099 : (x (-2) 2 && x (-2) 9).toNat = 0 := by
    have r28100 := hand2 (x (-2) 2) (x (-2) 9)
    have b28101 := hb (x (-2) 9)
    have b28102 := hb (x (-2) 2 && x (-2) 9)
    clear * - r28100 b28101 b28102 d28095
    omega
  have d28103 : (x 3 12).toNat = 0 := by
    have r28104 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e28105 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e28106 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b28107 := hb (x 0 3)
    have b28108 := hb (x 1 2)
    have b28109 := hb (x 2 13)
    have b28110 := hb (x 3 12)
    clear * - r28104 e28105 e28106 b28107 b28108 b28109 b28110 d28021 g10
    omega
  have d28111 : (x 3 1 && x 3 12).toNat = 0 := by
    have r28112 := hand2 (x 3 1) (x 3 12)
    have b28113 := hb (x 3 12)
    have b28114 := hb (x 3 1 && x 3 12)
    clear * - r28112 b28113 b28114 d28103
    omega
  have d28115 : (x 3 3 && x 3 12).toNat = 0 := by
    have r28116 := hand2 (x 3 3) (x 3 12)
    have b28117 := hb (x 3 12)
    have b28118 := hb (x 3 3 && x 3 12)
    clear * - r28116 b28117 b28118 d28103
    omega
  have d28119 : (x 3 9 && x 3 12).toNat = 0 := by
    have r28120 := hand2 (x 3 9) (x 3 12)
    have b28121 := hb (x 3 12)
    have b28122 := hb (x 3 9 && x 3 12)
    clear * - r28120 b28121 b28122 d28103
    omega
  have d28123 : (x 3 4).toNat = 0 := by
    have r28124 : (x 3 4).toNat ≤ (x 3 12).toNat := himp _ _ (hp4 3)
    have b28125 := hb (x 3 4)
    have b28126 := hb (x 3 12)
    clear * - r28124 b28125 b28126 d28103
    omega
  have d28127 : (x 3 4 && x 3 11).toNat = 0 := by
    have r28128 := hand1 (x 3 4) (x 3 11)
    have b28129 := hb (x 3 4)
    have b28130 := hb (x 3 4 && x 3 11)
    clear * - r28128 b28129 b28130 d28123
    omega
  have d28131 : (x 3 4 && x 3 8).toNat = 0 := by
    have r28132 := hand1 (x 3 4) (x 3 8)
    have b28133 := hb (x 3 4)
    have b28134 := hb (x 3 4 && x 3 8)
    clear * - r28132 b28133 b28134 d28123
    omega
  have d28135 : (x 1 2).toNat = 0 := by
    have r28136 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e28137 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e28138 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b28139 := hb (x 0 3)
    have b28140 := hb (x 1 2)
    have b28141 := hb (x 2 13)
    have b28142 := hb (x 3 12)
    clear * - r28136 e28137 e28138 b28139 b28140 b28141 b28142 d28103 d28021 g10
    omega
  have d28143 : (x 1 2 && x 1 12).toNat = 0 := by
    have r28144 := hand1 (x 1 2) (x 1 12)
    have b28145 := hb (x 1 2)
    have b28146 := hb (x 1 2 && x 1 12)
    clear * - r28144 b28145 b28146 d28135
    omega
  have d28147 : (x 1 2 && x 1 7).toNat = 0 := by
    have r28148 := hand1 (x 1 2) (x 1 7)
    have b28149 := hb (x 1 2)
    have b28150 := hb (x 1 2 && x 1 7)
    clear * - r28148 b28149 b28150 d28135
    omega
  have d28151 : (x 1 10).toNat = 0 := by
    have r28152 : (x 1 10).toNat ≤ (x 1 2).toNat := himp _ _ (hp10 1)
    have b28153 := hb (x 1 2)
    have b28154 := hb (x 1 10)
    clear * - r28152 b28153 b28154 d28135
    omega
  have d28155 : (x 1 6 && x 1 10).toNat = 0 := by
    have r28156 := hand2 (x 1 6) (x 1 10)
    have b28157 := hb (x 1 10)
    have b28158 := hb (x 1 6 && x 1 10)
    clear * - r28156 b28157 b28158 d28151
    omega
  have d28159 : (x 1 12).toNat = 0 := by
    have r28160 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e28161 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e28162 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b28163 := hb (x (-2) 3)
    have b28164 := hb (x (-1) 2)
    have b28165 := hb (x 0 13)
    have b28166 := hb (x 1 12)
    clear * - r28160 e28161 e28162 b28163 b28164 b28165 b28166 g20 d28066
    omega
  have d28167 : (x 1 4).toNat = 0 := by
    have r28168 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
    have b28169 := hb (x 1 4)
    have b28170 := hb (x 1 12)
    clear * - r28168 b28169 b28170 d28159
    omega
  have d28171 : (x (-2) 3).toNat = 0 := by
    have r28172 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e28173 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e28174 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b28175 := hb (x (-2) 3)
    have b28176 := hb (x (-1) 2)
    have b28177 := hb (x 0 13)
    have b28178 := hb (x 1 12)
    clear * - r28172 e28173 e28174 b28175 b28176 b28177 b28178 d28159 g20 d28066
    omega
  have d28179 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
    have r28180 := hand1 (x (-2) 3) (x (-2) 14)
    have b28181 := hb (x (-2) 3)
    have b28182 := hb (x (-2) 3 && x (-2) 14)
    clear * - r28180 b28181 b28182 d28171
    omega
  have d28183 : (x (-2) 3 && x (-2) 12).toNat = 0 := by
    have r28184 := hand1 (x (-2) 3) (x (-2) 12)
    have b28185 := hb (x (-2) 3)
    have b28186 := hb (x (-2) 3 && x (-2) 12)
    clear * - r28184 b28185 b28186 d28171
    omega
  have d28187 : (x (-2) 3 && x (-2) 8).toNat = 0 := by
    have r28188 := hand1 (x (-2) 3) (x (-2) 8)
    have b28189 := hb (x (-2) 3)
    have b28190 := hb (x (-2) 3 && x (-2) 8)
    clear * - r28188 b28189 b28190 d28171
    omega
  have d28191 : (x (-2) 11).toNat = 0 := by
    have r28192 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
    have b28193 := hb (x (-2) 3)
    have b28194 := hb (x (-2) 11)
    clear * - r28192 b28193 b28194 d28171
    omega
  have d28195 : (x (-2) 2 && x (-2) 11).toNat = 0 := by
    have r28196 := hand2 (x (-2) 2) (x (-2) 11)
    have b28197 := hb (x (-2) 11)
    have b28198 := hb (x (-2) 2 && x (-2) 11)
    clear * - r28196 b28197 b28198 d28191
    omega
  cases h28199 : x (-1) 3
  · have f28200 : (x (-1) 3).toNat = 0 := by rw [h28199]; rfl
    have d28201 : (x (-1) 11).toNat = 0 := by
      have r28202 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
      have b28203 := hb (x (-1) 3)
      have b28204 := hb (x (-1) 11)
      clear * - r28202 b28203 b28204 f28200
      omega
    have d28205 : (x (-1) 1 && x (-1) 11).toNat = 0 := by
      have r28206 := hand2 (x (-1) 1) (x (-1) 11)
      have b28207 := hb (x (-1) 11)
      have b28208 := hb (x (-1) 1 && x (-1) 11)
      clear * - r28206 b28207 b28208 d28201
      omega
    have d28209 : (x (-1) 2 && x (-1) 11).toNat = 0 := by
      have r28210 := hand2 (x (-1) 2) (x (-1) 11)
      have b28211 := hb (x (-1) 11)
      have b28212 := hb (x (-1) 2 && x (-1) 11)
      clear * - r28210 b28211 b28212 d28201
      omega
    cases h28213 : x (-1) 6
    · have f28214 : (x (-1) 6).toNat = 0 := by rw [h28213]; rfl
      cases h28215 : x 1 3
      · have f28216 : (x 1 3).toNat = 0 := by rw [h28215]; rfl
        have d28217 : (x 1 11).toNat = 0 := by
          have r28218 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
          have b28219 := hb (x 1 3)
          have b28220 := hb (x 1 11)
          clear * - r28218 b28219 b28220 f28216
          omega
        cases h28221 : x (-1) 7
        · have f28222 : (x (-1) 7).toNat = 0 := by rw [h28221]; rfl
          have d28223 : (x (-1) 1 && x (-1) 7).toNat = 0 := by
            have r28224 := hand2 (x (-1) 1) (x (-1) 7)
            have b28225 := hb (x (-1) 7)
            have b28226 := hb (x (-1) 1 && x (-1) 7)
            clear * - r28224 b28225 b28226 f28222
            omega
          have d28227 : (x (-1) 2 && x (-1) 7).toNat = 0 := by
            have r28228 := hand2 (x (-1) 2) (x (-1) 7)
            have b28229 := hb (x (-1) 7)
            have b28230 := hb (x (-1) 2 && x (-1) 7)
            clear * - r28228 b28229 b28230 f28222
            omega
          have r28231 : (x (-1) 1).toNat + (x (-2) 2).toNat + (x (-3) 3).toNat + (x (-4) 4).toNat + (x (-5) 5).toNat + (x (-6) 6).toNat + (x (-7) 7).toNat + (x (-8) 8).toNat + (x (-9) 9).toNat + (x (-10) 10).toNat + (x (-11) 11).toNat + (x (-12) 12).toNat + (x (-13) 13).toNat + (x (-14) 14).toNat = 3 := by have q := hcount 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28232 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28233 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28234 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
          have e28235 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
          have e28236 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
          have e28237 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
          have e28238 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
          have e28239 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
          have r28240 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28241 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
          have e28242 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
          have r28243 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := by have q := hcov5 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28244 : 1 ≤ (x 0 6).toNat + (x (-1) 1 && x (-1) 7).toNat + (x (-2) 2 && x (-2) 8).toNat + (x (-3) 3 && x (-3) 9).toNat + (x (-4) 4 && x (-4) 10).toNat + (x (-5) 5 && x (-5) 11).toNat + (x (-6) 6 && x (-6) 12).toNat + (x (-7) 7 && x (-7) 13).toNat + (x (-8) 8 && x (-8) 14).toNat + (x (-9) 9).toNat := by have q := hcov6 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28245 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28246 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28247 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28248 : 1 ≤ (x (-12) 13).toNat + (x (-13) 1 && x (-13) 14).toNat + (x (-14) 2).toNat := by have q := hcov13 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28249 : (x (-14) 2).toNat ≤ (x (-14) 14).toNat := himp _ _ (hp2 (-14))
          have r28250 := hand2 (x (-3) 4) (x (-3) 9)
          have r28251 := hand2 (x (-4) 5) (x (-4) 10)
          have r28252 := hand2 (x (-5) 6) (x (-5) 11)
          have r28253 := hand1 (x (-6) 7) (x (-6) 12)
          have r28254 := hand1 (x (-7) 8) (x (-7) 13)
          have r28255 := hand1 (x (-8) 9) (x (-8) 14)
          have r28256 := hand2 (x (-2) 2) (x (-2) 8)
          have r28257 := hand2 (x (-3) 3) (x (-3) 9)
          have r28258 := hand1 (x (-8) 8) (x (-8) 14)
          have r28259 := hand1 (x (-3) 4) (x (-3) 13)
          have r28260 := hand1 (x (-4) 5) (x (-4) 14)
          have r28261 := hand1 (x (-4) 2) (x (-4) 12)
          have r28262 := hand1 (x (-5) 3) (x (-5) 13)
          have r28263 := hand1 (x (-6) 4) (x (-6) 14)
          have r28264 := hand1 (x (-2) 2) (x (-2) 12)
          have r28265 := hand2 (x (-2) 2) (x (-2) 12)
          have r28266 := hand1 (x (-3) 3) (x (-3) 13)
          have r28267 := hand2 (x (-3) 3) (x (-3) 13)
          have r28268 := hand2 (x (-13) 1) (x (-13) 14)
          linarith only [r28231, r28232, r28233, e28234, e28235, e28236, e28237, e28238, e28239, r28240, e28241, e28242, r28243, r28244, r28245, r28246, r28247, r28248, r28249, r28250, r28251, r28252, r28253, r28254, r28255, r28256, r28257, r28258, r28259, r28260, r28261, r28262, r28263, r28264, r28265, r28266, r28267, r28268, g0, g1, g2, g3, d28171, g5, g6, d28066, g8, g13, g17, d28013, d28009, g28, d28227, d28187, d28223, g34, g35, g36, g37, g51, d28209, d28183, g53, d28205, g54]
        · have f28346 : (x (-1) 7).toNat = 1 := by rw [h28221]; rfl
          have d28347 : (x 6 8).toNat = 0 := by
            have r28348 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e28349 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
            have e28350 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
            have e28351 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
            have e28352 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
            have e28353 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
            have e28354 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
            have b28355 := hb (x (-1) 7)
            have b28356 := hb (x 0 6)
            have b28357 := hb (x 1 5)
            have b28358 := hb (x 2 4)
            have b28359 := hb (x 3 11)
            have b28360 := hb (x 4 10)
            have b28361 := hb (x 5 9)
            have b28362 := hb (x 6 8)
            clear * - r28348 e28349 e28350 e28351 e28352 e28353 e28354 b28355 b28356 b28357 b28358 b28359 b28360 b28361 b28362 d28013 g13 f28346
            omega
          have d28363 : (x 6 1 && x 6 8).toNat = 0 := by
            have r28364 := hand2 (x 6 1) (x 6 8)
            have b28365 := hb (x 6 8)
            have b28366 := hb (x 6 1 && x 6 8)
            clear * - r28364 b28365 b28366 d28347
            omega
          have d28367 : (x 6 3 && x 6 8).toNat = 0 := by
            have r28368 := hand2 (x 6 3) (x 6 8)
            have b28369 := hb (x 6 8)
            have b28370 := hb (x 6 3 && x 6 8)
            clear * - r28368 b28369 b28370 d28347
            omega
          have d28371 : (x 5 9).toNat = 0 := by
            have r28372 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e28373 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
            have e28374 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
            have e28375 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
            have e28376 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
            have e28377 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
            have e28378 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
            have b28379 := hb (x (-1) 7)
            have b28380 := hb (x 0 6)
            have b28381 := hb (x 1 5)
            have b28382 := hb (x 2 4)
            have b28383 := hb (x 3 11)
            have b28384 := hb (x 4 10)
            have b28385 := hb (x 5 9)
            have b28386 := hb (x 6 8)
            clear * - r28372 e28373 e28374 e28375 e28376 e28377 e28378 b28379 b28380 b28381 b28382 b28383 b28384 b28385 b28386 d28347 d28013 g13 f28346
            omega
          have d28387 : (x 5 2 && x 5 9).toNat = 0 := by
            have r28388 := hand2 (x 5 2) (x 5 9)
            have b28389 := hb (x 5 9)
            have b28390 := hb (x 5 2 && x 5 9)
            clear * - r28388 b28389 b28390 d28371
            omega
          have d28391 : (x 5 4 && x 5 9).toNat = 0 := by
            have r28392 := hand2 (x 5 4) (x 5 9)
            have b28393 := hb (x 5 9)
            have b28394 := hb (x 5 4 && x 5 9)
            clear * - r28392 b28393 b28394 d28371
            omega
          have d28395 : (x 4 10).toNat = 0 := by
            have r28396 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e28397 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
            have e28398 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
            have e28399 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
            have e28400 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
            have e28401 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
            have e28402 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
            have b28403 := hb (x (-1) 7)
            have b28404 := hb (x 0 6)
            have b28405 := hb (x 1 5)
            have b28406 := hb (x 2 4)
            have b28407 := hb (x 3 11)
            have b28408 := hb (x 4 10)
            have b28409 := hb (x 5 9)
            have b28410 := hb (x 6 8)
            clear * - r28396 e28397 e28398 e28399 e28400 e28401 e28402 b28403 b28404 b28405 b28406 b28407 b28408 b28409 b28410 d28347 d28371 d28013 g13 f28346
            omega
          have d28411 : (x 4 1 && x 4 10).toNat = 0 := by
            have r28412 := hand2 (x 4 1) (x 4 10)
            have b28413 := hb (x 4 10)
            have b28414 := hb (x 4 1 && x 4 10)
            clear * - r28412 b28413 b28414 d28395
            omega
          have d28415 : (x 2 3 && x 2 12).toNat = 1 := by
            have r28416 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b28417 := hb (x (-1) 6)
            have b28418 := hb (x 5 9)
            have b28419 := hb (x 4 1 && x 4 10)
            have b28420 := hb (x 3 2 && x 3 11)
            have b28421 := hb (x 2 3 && x 2 12)
            have b28422 := hb (x 1 4 && x 1 13)
            have b28423 := hb (x 0 5 && x 0 14)
            clear * - r28416 b28417 b28418 b28419 b28420 b28421 b28422 b28423 d28371 d28411 d28058 d27997 g52 f28214
            omega
          have d28424 : (x 2 3).toNat = 1 := by
            have r28425 := hand1 (x 2 3) (x 2 12)
            have b28426 := hb (x 2 3)
            have b28427 := hb (x 2 3 && x 2 12)
            clear * - r28425 b28426 b28427 d28415
            omega
          have d28428 : (x 5 12).toNat = 0 := by
            have r28429 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e28430 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e28431 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b28432 := hb (x 2 3)
            have b28433 := hb (x 3 2)
            have b28434 := hb (x 4 13)
            have b28435 := hb (x 5 12)
            clear * - r28429 e28430 e28431 b28432 b28433 b28434 b28435 d28050 d28424
            omega
          have d28436 : (x 5 1 && x 5 12).toNat = 0 := by
            have r28437 := hand2 (x 5 1) (x 5 12)
            have b28438 := hb (x 5 12)
            have b28439 := hb (x 5 1 && x 5 12)
            clear * - r28437 b28438 b28439 d28428
            omega
          have d28440 : (x 5 4).toNat = 0 := by
            have r28441 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
            have b28442 := hb (x 5 4)
            have b28443 := hb (x 5 12)
            clear * - r28441 b28442 b28443 d28428
            omega
          have d28444 : (x 4 13).toNat = 0 := by
            have r28445 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e28446 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e28447 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b28448 := hb (x 2 3)
            have b28449 := hb (x 3 2)
            have b28450 := hb (x 4 13)
            have b28451 := hb (x 5 12)
            clear * - r28445 e28446 e28447 b28448 b28449 b28450 b28451 d28428 d28050 d28424
            omega
          have d28452 : (x 4 2 && x 4 13).toNat = 0 := by
            have r28453 := hand2 (x 4 2) (x 4 13)
            have b28454 := hb (x 4 13)
            have b28455 := hb (x 4 2 && x 4 13)
            clear * - r28453 b28454 b28455 d28444
            omega
          have d28456 : (x 4 5).toNat = 0 := by
            have r28457 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
            have b28458 := hb (x 4 5)
            have b28459 := hb (x 4 13)
            clear * - r28457 b28458 b28459 d28444
            omega
          have d28460 : (x 4 5 && x 4 10).toNat = 0 := by
            have r28461 := hand1 (x 4 5) (x 4 10)
            have b28462 := hb (x 4 5)
            have b28463 := hb (x 4 5 && x 4 10)
            clear * - r28461 b28462 b28463 d28456
            omega
          have d28464 : (x 4 3 && x 4 10).toNat = 0 := by
            have r28465 := hand2 (x 4 3) (x 4 10)
            have b28466 := hb (x 4 10)
            have b28467 := hb (x 4 3 && x 4 10)
            clear * - r28465 b28466 b28467 d28395
            omega
          have d28468 : (x 3 11).toNat = 0 := by
            have r28469 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e28470 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
            have e28471 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
            have e28472 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
            have e28473 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
            have e28474 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
            have e28475 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
            have b28476 := hb (x (-1) 7)
            have b28477 := hb (x 0 6)
            have b28478 := hb (x 1 5)
            have b28479 := hb (x 2 4)
            have b28480 := hb (x 3 11)
            have b28481 := hb (x 4 10)
            have b28482 := hb (x 5 9)
            have b28483 := hb (x 6 8)
            clear * - r28469 e28470 e28471 e28472 e28473 e28474 e28475 b28476 b28477 b28478 b28479 b28480 b28481 b28482 b28483 d28347 d28371 d28395 d28013 g13 f28346
            omega
          have d28484 : (x 2 4).toNat = 0 := by
            have r28485 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e28486 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
            have e28487 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
            have e28488 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
            have e28489 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
            have e28490 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
            have e28491 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
            have b28492 := hb (x (-1) 7)
            have b28493 := hb (x 0 6)
            have b28494 := hb (x 1 5)
            have b28495 := hb (x 2 4)
            have b28496 := hb (x 3 11)
            have b28497 := hb (x 4 10)
            have b28498 := hb (x 5 9)
            have b28499 := hb (x 6 8)
            clear * - r28485 e28486 e28487 e28488 e28489 e28490 e28491 b28492 b28493 b28494 b28495 b28496 b28497 b28498 b28499 d28347 d28371 d28395 d28468 d28013 g13 f28346
            omega
          have d28500 : (x 2 4 && x 2 13).toNat = 0 := by
            have r28501 := hand1 (x 2 4) (x 2 13)
            have b28502 := hb (x 2 4)
            have b28503 := hb (x 2 4 && x 2 13)
            clear * - r28501 b28502 b28503 d28484
            omega
          have d28504 : (x 6 11).toNat = 1 := by
            have r28505 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := by have q := hcov11 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b28506 := hb (x 2 4)
            have b28507 := hb (x 6 11)
            have b28508 := hb (x 5 1 && x 5 12)
            have b28509 := hb (x 4 2 && x 4 13)
            have b28510 := hb (x 3 3 && x 3 14)
            clear * - r28505 b28506 b28507 b28508 b28509 b28510 d28436 d28452 d28038 d28484
            omega
          have d28511 : (x 6 3).toNat = 1 := by
            have r28512 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
            have b28513 := hb (x 6 3)
            have b28514 := hb (x 6 11)
            clear * - r28512 b28513 b28514 d28504
            omega
          have d28515 : (x 9 12).toNat = 0 := by
            have r28516 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e28517 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
            have e28518 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
            have b28519 := hb (x 6 3)
            have b28520 := hb (x 7 2)
            have b28521 := hb (x 8 13)
            have b28522 := hb (x 9 12)
            clear * - r28516 e28517 e28518 b28519 b28520 b28521 b28522 d28511
            omega
          have d28523 : (x 8 13).toNat = 0 := by
            have r28524 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e28525 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
            have e28526 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
            have b28527 := hb (x 6 3)
            have b28528 := hb (x 7 2)
            have b28529 := hb (x 8 13)
            have b28530 := hb (x 9 12)
            clear * - r28524 e28525 e28526 b28527 b28528 b28529 b28530 d28515 d28511
            omega
          have d28531 : (x 7 2).toNat = 0 := by
            have r28532 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e28533 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
            have e28534 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
            have b28535 := hb (x 6 3)
            have b28536 := hb (x 7 2)
            have b28537 := hb (x 8 13)
            have b28538 := hb (x 9 12)
            clear * - r28532 e28533 e28534 b28535 b28536 b28537 b28538 d28515 d28523 d28511
            omega
          have d28539 : (x 7 2 && x 7 7).toNat = 0 := by
            have r28540 := hand1 (x 7 2) (x 7 7)
            have b28541 := hb (x 7 2)
            have b28542 := hb (x 7 2 && x 7 7)
            clear * - r28540 b28541 b28542 d28531
            omega
          have d28543 : (x 7 10).toNat = 0 := by
            have r28544 : (x 7 10).toNat ≤ (x 7 2).toNat := himp _ _ (hp10 7)
            have b28545 := hb (x 7 2)
            have b28546 := hb (x 7 10)
            clear * - r28544 b28545 b28546 d28531
            omega
          have d28547 : (x 9 8).toNat = 0 := by
            have r28548 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e28549 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
            have e28550 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
            have e28551 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
            have e28552 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
            have e28553 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
            have e28554 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
            have b28555 := hb (x 2 7)
            have b28556 := hb (x 3 6)
            have b28557 := hb (x 4 5)
            have b28558 := hb (x 5 4)
            have b28559 := hb (x 6 11)
            have b28560 := hb (x 7 10)
            have b28561 := hb (x 8 9)
            have b28562 := hb (x 9 8)
            clear * - r28548 e28549 e28550 e28551 e28552 e28553 e28554 b28555 b28556 b28557 b28558 b28559 b28560 b28561 b28562 d28543 d28504 d28440 d28456 d28042
            omega
          have d28563 : (x 8 9).toNat = 0 := by
            have r28564 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e28565 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
            have e28566 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
            have e28567 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
            have e28568 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
            have e28569 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
            have e28570 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
            have b28571 := hb (x 2 7)
            have b28572 := hb (x 3 6)
            have b28573 := hb (x 4 5)
            have b28574 := hb (x 5 4)
            have b28575 := hb (x 6 11)
            have b28576 := hb (x 7 10)
            have b28577 := hb (x 8 9)
            have b28578 := hb (x 9 8)
            clear * - r28564 e28565 e28566 e28567 e28568 e28569 e28570 b28571 b28572 b28573 b28574 b28575 b28576 b28577 b28578 d28547 d28543 d28504 d28440 d28456 d28042
            omega
          have d28579 : (x 2 7).toNat = 0 := by
            have r28580 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e28581 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
            have e28582 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
            have e28583 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
            have e28584 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
            have e28585 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
            have e28586 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
            have b28587 := hb (x 2 7)
            have b28588 := hb (x 3 6)
            have b28589 := hb (x 4 5)
            have b28590 := hb (x 5 4)
            have b28591 := hb (x 6 11)
            have b28592 := hb (x 7 10)
            have b28593 := hb (x 8 9)
            have b28594 := hb (x 9 8)
            clear * - r28580 e28581 e28582 e28583 e28584 e28585 e28586 b28587 b28588 b28589 b28590 b28591 b28592 b28593 b28594 d28547 d28563 d28543 d28504 d28440 d28456 d28042
            omega
          have d28595 : (x 2 7 && x 2 12).toNat = 0 := by
            have r28596 := hand1 (x 2 7) (x 2 12)
            have b28597 := hb (x 2 7)
            have b28598 := hb (x 2 7 && x 2 12)
            clear * - r28596 b28597 b28598 d28579
            omega
          have r28599 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28600 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
          have e28601 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
          have e28602 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
          have e28603 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
          have e28604 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
          have e28605 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
          have r28606 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28607 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e28608 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e28609 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e28610 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e28611 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e28612 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have r28613 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28614 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e28615 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e28616 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e28617 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e28618 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e28619 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have r28620 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28621 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
          have e28622 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
          have e28623 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
          have e28624 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
          have e28625 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
          have e28626 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
          have r28627 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28628 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e28629 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have r28630 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28631 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
          have e28632 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
          have r28633 : 1 ≤ (x 9 5).toNat + (x 8 1 && x 8 6).toNat + (x 7 2 && x 7 7).toNat + (x 6 3 && x 6 8).toNat + (x 5 4 && x 5 9).toNat + (x 4 5 && x 4 10).toNat + (x 3 6 && x 3 11).toNat + (x 2 7 && x 2 12).toNat + (x 1 8 && x 1 13).toNat + (x 0 9 && x 0 14).toNat + (x (-1) 10).toNat := by have q := hcov5 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28634 : 1 ≤ (x 7 7).toNat + (x 6 1 && x 6 8).toNat + (x 5 2 && x 5 9).toNat + (x 4 3 && x 4 10).toNat + (x 3 4 && x 3 11).toNat + (x 2 5 && x 2 12).toNat + (x 1 6 && x 1 13).toNat + (x 0 7 && x 0 14).toNat + (x (-1) 8).toNat := by have q := hcov7 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28635 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28636 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28637 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28638 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28639 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28640 := hand2 (x 8 1) (x 8 6)
          have r28641 := hand1 (x 2 5) (x 2 12)
          have r28642 := hand1 (x (-4) 3) (x (-4) 12)
          have r28643 := hand1 (x (-5) 4) (x (-5) 13)
          have r28644 := hand1 (x (-6) 5) (x (-6) 14)
          have r28645 := hand2 (x 5 1) (x 5 10)
          have r28646 := hand2 (x 4 2) (x 4 11)
          have r28647 := hand1 (x (-2) 2) (x (-2) 12)
          have r28648 := hand1 (x (-3) 3) (x (-3) 13)
          have r28649 := hand2 (x (-1) 2) (x (-1) 13)
          linarith only [r28599, e28600, e28601, e28602, e28603, e28604, e28605, r28606, e28607, e28608, e28609, e28610, e28611, e28612, r28613, e28614, e28615, e28616, e28617, e28618, e28619, r28620, e28621, e28622, e28623, e28624, e28625, e28626, r28627, e28628, e28629, r28630, e28631, e28632, r28633, r28634, r28635, r28636, r28637, r28638, r28639, r28640, r28641, r28642, r28643, r28644, r28645, r28646, r28647, r28648, r28649, g2, d28095, d28191, d28083, g7, g13, g14, g16, g17, g19, d28217, d28123, d28539, d28367, d28391, d28460, d28046, d28595, d28005, g33, d28363, d28387, d28464, d28127, d28001, g46, g47, g48, d28115, d28500, d28017, d28205, g54, g57, d28179, d28079]
      · have f28729 : (x 1 3).toNat = 1 := by rw [h28215]; rfl
        have d28730 : (x 4 12).toNat = 0 := by
          have r28731 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28732 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e28733 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b28734 := hb (x 1 3)
          have b28735 := hb (x 2 2)
          have b28736 := hb (x 3 13)
          have b28737 := hb (x 4 12)
          clear * - r28731 e28732 e28733 b28734 b28735 b28736 b28737 f28729
          omega
        have d28738 : (x 4 1 && x 4 12).toNat = 0 := by
          have r28739 := hand2 (x 4 1) (x 4 12)
          have b28740 := hb (x 4 12)
          have b28741 := hb (x 4 1 && x 4 12)
          clear * - r28739 b28740 b28741 d28730
          omega
        have d28742 : (x 4 4).toNat = 0 := by
          have r28743 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
          have b28744 := hb (x 4 4)
          have b28745 := hb (x 4 12)
          clear * - r28743 b28744 b28745 d28730
          omega
        have d28746 : (x 3 13).toNat = 0 := by
          have r28747 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28748 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e28749 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b28750 := hb (x 1 3)
          have b28751 := hb (x 2 2)
          have b28752 := hb (x 3 13)
          have b28753 := hb (x 4 12)
          clear * - r28747 e28748 e28749 b28750 b28751 b28752 b28753 d28730 f28729
          omega
        have d28754 : (x 2 2).toNat = 0 := by
          have r28755 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28756 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e28757 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b28758 := hb (x 1 3)
          have b28759 := hb (x 2 2)
          have b28760 := hb (x 3 13)
          have b28761 := hb (x 4 12)
          clear * - r28755 e28756 e28757 b28758 b28759 b28760 b28761 d28730 d28746 f28729
          omega
        have d28762 : (x 4 13).toNat = 1 := by
          have r28763 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b28764 := hb (x 2 2)
          have b28765 := hb (x 4 13)
          have b28766 := hb (x 3 1 && x 3 14)
          clear * - r28763 b28764 b28765 b28766 d28034 d28754
          omega
        have d28767 : (x 4 1).toNat = 1 := by
          have r28768 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
          have b28769 := hb (x 4 1)
          have b28770 := hb (x 4 13)
          clear * - r28768 b28769 b28770 d28762
          omega
        have d28771 : (x 5 14).toNat = 0 := by
          have r28772 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b28773 := hb (x 4 1)
          have b28774 := hb (x 5 14)
          clear * - r28772 b28773 b28774 d28767
          omega
        have d28775 : (x 5 3 && x 5 14).toNat = 0 := by
          have r28776 := hand2 (x 5 3) (x 5 14)
          have b28777 := hb (x 5 14)
          have b28778 := hb (x 5 3 && x 5 14)
          clear * - r28776 b28777 b28778 d28771
          omega
        have d28779 : (x 5 2).toNat = 0 := by
          have r28780 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
          have b28781 := hb (x 5 2)
          have b28782 := hb (x 5 14)
          clear * - r28780 b28781 b28782 d28771
          omega
        have d28783 : (x 5 12).toNat = 0 := by
          have r28784 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28785 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e28786 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b28787 := hb (x 2 3)
          have b28788 := hb (x 3 2)
          have b28789 := hb (x 4 13)
          have b28790 := hb (x 5 12)
          clear * - r28784 e28785 e28786 b28787 b28788 b28789 b28790 d28762 d28050
          omega
        have d28791 : (x 5 4).toNat = 0 := by
          have r28792 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
          have b28793 := hb (x 5 4)
          have b28794 := hb (x 5 12)
          clear * - r28792 b28793 b28794 d28783
          omega
        have d28795 : (x 2 3).toNat = 0 := by
          have r28796 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28797 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e28798 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b28799 := hb (x 2 3)
          have b28800 := hb (x 3 2)
          have b28801 := hb (x 4 13)
          have b28802 := hb (x 5 12)
          clear * - r28796 e28797 e28798 b28799 b28800 b28801 b28802 d28783 d28762 d28050
          omega
        have d28803 : (x 2 3 && x 2 14).toNat = 0 := by
          have r28804 := hand1 (x 2 3) (x 2 14)
          have b28805 := hb (x 2 3)
          have b28806 := hb (x 2 3 && x 2 14)
          clear * - r28804 b28805 b28806 d28795
          omega
        have d28807 : (x 5 11).toNat = 1 := by
          have r28808 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b28809 := hb (x 1 4)
          have b28810 := hb (x 5 11)
          have b28811 := hb (x 4 1 && x 4 12)
          have b28812 := hb (x 3 2 && x 3 13)
          have b28813 := hb (x 2 3 && x 2 14)
          clear * - r28808 b28809 b28810 b28811 b28812 b28813 d28738 d28054 d28803 d28167
          omega
        have d28814 : (x 5 3).toNat = 1 := by
          have r28815 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
          have b28816 := hb (x 5 3)
          have b28817 := hb (x 5 11)
          clear * - r28815 b28816 b28817 d28807
          omega
        have d28818 : (x 8 12).toNat = 0 := by
          have r28819 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28820 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
          have e28821 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
          have b28822 := hb (x 5 3)
          have b28823 := hb (x 6 2)
          have b28824 := hb (x 7 13)
          have b28825 := hb (x 8 12)
          clear * - r28819 e28820 e28821 b28822 b28823 b28824 b28825 d28814
          omega
        have d28826 : (x 8 1 && x 8 12).toNat = 0 := by
          have r28827 := hand2 (x 8 1) (x 8 12)
          have b28828 := hb (x 8 12)
          have b28829 := hb (x 8 1 && x 8 12)
          clear * - r28827 b28828 b28829 d28818
          omega
        have d28830 : (x 8 4).toNat = 0 := by
          have r28831 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
          have b28832 := hb (x 8 4)
          have b28833 := hb (x 8 12)
          clear * - r28831 b28832 b28833 d28818
          omega
        have d28834 : (x 7 13).toNat = 0 := by
          have r28835 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28836 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
          have e28837 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
          have b28838 := hb (x 5 3)
          have b28839 := hb (x 6 2)
          have b28840 := hb (x 7 13)
          have b28841 := hb (x 8 12)
          clear * - r28835 e28836 e28837 b28838 b28839 b28840 b28841 d28818 d28814
          omega
        have d28842 : (x 7 2 && x 7 13).toNat = 0 := by
          have r28843 := hand2 (x 7 2) (x 7 13)
          have b28844 := hb (x 7 13)
          have b28845 := hb (x 7 2 && x 7 13)
          clear * - r28843 b28844 b28845 d28834
          omega
        have d28846 : (x 6 1 && x 6 14).toNat = 1 := by
          have r28847 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b28848 := hb (x 5 2)
          have b28849 := hb (x 7 13)
          have b28850 := hb (x 6 1 && x 6 14)
          clear * - r28847 b28848 b28849 b28850 d28834 d28779
          omega
        have d28851 : (x 6 1).toNat = 1 := by
          have r28852 := hand1 (x 6 1) (x 6 14)
          have b28853 := hb (x 6 1)
          have b28854 := hb (x 6 1 && x 6 14)
          clear * - r28852 b28853 b28854 d28846
          omega
        have d28855 : (x 7 14).toNat = 0 := by
          have r28856 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b28857 := hb (x 6 1)
          have b28858 := hb (x 7 14)
          clear * - r28856 b28857 b28858 d28851
          omega
        have d28859 : (x 7 1 && x 7 14).toNat = 0 := by
          have r28860 := hand2 (x 7 1) (x 7 14)
          have b28861 := hb (x 7 14)
          have b28862 := hb (x 7 1 && x 7 14)
          clear * - r28860 b28861 b28862 d28855
          omega
        have d28863 : (x 7 2).toNat = 0 := by
          have r28864 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
          have b28865 := hb (x 7 2)
          have b28866 := hb (x 7 14)
          clear * - r28864 b28865 b28866 d28855
          omega
        have d28867 : (x 6 2).toNat = 0 := by
          have r28868 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28869 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
          have e28870 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
          have b28871 := hb (x 5 3)
          have b28872 := hb (x 6 2)
          have b28873 := hb (x 7 13)
          have b28874 := hb (x 8 12)
          clear * - r28868 e28869 e28870 b28871 b28872 b28873 b28874 d28818 d28834 d28814
          omega
        have d28875 : (x 6 2 && x 6 13).toNat = 0 := by
          have r28876 := hand1 (x 6 2) (x 6 13)
          have b28877 := hb (x 6 2)
          have b28878 := hb (x 6 2 && x 6 13)
          clear * - r28876 b28877 b28878 d28867
          omega
        have d28879 : (x 8 13).toNat = 1 := by
          have r28880 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b28881 := hb (x 6 2)
          have b28882 := hb (x 8 13)
          have b28883 := hb (x 7 1 && x 7 14)
          clear * - r28880 b28881 b28882 b28883 d28859 d28867
          omega
        have d28884 : (x 8 1).toNat = 1 := by
          have r28885 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
          have b28886 := hb (x 8 1)
          have b28887 := hb (x 8 13)
          clear * - r28885 b28886 b28887 d28879
          omega
        have d28888 : (x 9 14).toNat = 0 := by
          have r28889 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b28890 := hb (x 8 1)
          have b28891 := hb (x 9 14)
          clear * - r28889 b28890 b28891 d28884
          omega
        have d28892 : (x 9 3 && x 9 14).toNat = 0 := by
          have r28893 := hand2 (x 9 3) (x 9 14)
          have b28894 := hb (x 9 14)
          have b28895 := hb (x 9 3 && x 9 14)
          clear * - r28893 b28894 b28895 d28888
          omega
        have d28896 : (x 9 2).toNat = 0 := by
          have r28897 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
          have b28898 := hb (x 9 2)
          have b28899 := hb (x 9 14)
          clear * - r28897 b28898 b28899 d28888
          omega
        have d28900 : (x 9 12).toNat = 0 := by
          have r28901 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28902 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
          have e28903 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
          have b28904 := hb (x 6 3)
          have b28905 := hb (x 7 2)
          have b28906 := hb (x 8 13)
          have b28907 := hb (x 9 12)
          clear * - r28901 e28902 e28903 b28904 b28905 b28906 b28907 d28879 d28863
          omega
        have d28908 : (x 9 4).toNat = 0 := by
          have r28909 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
          have b28910 := hb (x 9 4)
          have b28911 := hb (x 9 12)
          clear * - r28909 b28910 b28911 d28900
          omega
        have d28912 : (x 6 3).toNat = 0 := by
          have r28913 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28914 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
          have e28915 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
          have b28916 := hb (x 6 3)
          have b28917 := hb (x 7 2)
          have b28918 := hb (x 8 13)
          have b28919 := hb (x 9 12)
          clear * - r28913 e28914 e28915 b28916 b28917 b28918 b28919 d28900 d28879 d28863
          omega
        have d28920 : (x 6 3 && x 6 14).toNat = 0 := by
          have r28921 := hand1 (x 6 3) (x 6 14)
          have b28922 := hb (x 6 3)
          have b28923 := hb (x 6 3 && x 6 14)
          clear * - r28921 b28922 b28923 d28912
          omega
        have d28924 : (x 9 11).toNat = 1 := by
          have r28925 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b28926 := hb (x 5 4)
          have b28927 := hb (x 9 11)
          have b28928 := hb (x 8 1 && x 8 12)
          have b28929 := hb (x 7 2 && x 7 13)
          have b28930 := hb (x 6 3 && x 6 14)
          clear * - r28925 b28926 b28927 b28928 b28929 b28930 d28826 d28842 d28920 d28791
          omega
        have d28931 : (x 9 3).toNat = 1 := by
          have r28932 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
          have b28933 := hb (x 9 3)
          have b28934 := hb (x 9 11)
          clear * - r28932 b28933 b28934 d28924
          omega
        have d28935 : (x 12 12).toNat = 0 := by
          have r28936 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28937 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
          have e28938 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
          have b28939 := hb (x 9 3)
          have b28940 := hb (x 10 2)
          have b28941 := hb (x 11 13)
          have b28942 := hb (x 12 12)
          clear * - r28936 e28937 e28938 b28939 b28940 b28941 b28942 d28931
          omega
        have d28943 : (x 12 1 && x 12 12).toNat = 0 := by
          have r28944 := hand2 (x 12 1) (x 12 12)
          have b28945 := hb (x 12 12)
          have b28946 := hb (x 12 1 && x 12 12)
          clear * - r28944 b28945 b28946 d28935
          omega
        have d28947 : (x 12 4).toNat = 0 := by
          have r28948 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
          have b28949 := hb (x 12 4)
          have b28950 := hb (x 12 12)
          clear * - r28948 b28949 b28950 d28935
          omega
        have d28951 : (x 11 13).toNat = 0 := by
          have r28952 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28953 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
          have e28954 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
          have b28955 := hb (x 9 3)
          have b28956 := hb (x 10 2)
          have b28957 := hb (x 11 13)
          have b28958 := hb (x 12 12)
          clear * - r28952 e28953 e28954 b28955 b28956 b28957 b28958 d28935 d28931
          omega
        have d28959 : (x 11 2 && x 11 13).toNat = 0 := by
          have r28960 := hand2 (x 11 2) (x 11 13)
          have b28961 := hb (x 11 13)
          have b28962 := hb (x 11 2 && x 11 13)
          clear * - r28960 b28961 b28962 d28951
          omega
        have d28963 : (x 10 1 && x 10 14).toNat = 1 := by
          have r28964 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b28965 := hb (x 9 2)
          have b28966 := hb (x 11 13)
          have b28967 := hb (x 10 1 && x 10 14)
          clear * - r28964 b28965 b28966 b28967 d28951 d28896
          omega
        have d28968 : (x 10 14).toNat = 1 := by
          have r28969 := hand2 (x 10 1) (x 10 14)
          have b28970 := hb (x 10 14)
          have b28971 := hb (x 10 1 && x 10 14)
          clear * - r28969 b28970 b28971 d28963
          omega
        have d28972 : (x 9 1).toNat = 0 := by
          have r28973 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b28974 := hb (x 9 1)
          have b28975 := hb (x 10 14)
          clear * - r28973 b28974 b28975 d28968
          omega
        have d28976 : (x 9 13).toNat = 0 := by
          have r28977 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
          have b28978 := hb (x 9 1)
          have b28979 := hb (x 9 13)
          clear * - r28977 b28978 b28979 d28972
          omega
        have d28980 : (x 8 1 && x 8 14).toNat = 1 := by
          have r28981 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b28982 := hb (x 7 2)
          have b28983 := hb (x 9 13)
          have b28984 := hb (x 8 1 && x 8 14)
          clear * - r28981 b28982 b28983 b28984 d28976 d28863
          omega
        have d28985 : (x 8 14).toNat = 1 := by
          have r28986 := hand2 (x 8 1) (x 8 14)
          have b28987 := hb (x 8 14)
          have b28988 := hb (x 8 1 && x 8 14)
          clear * - r28986 b28987 b28988 d28980
          omega
        have d28989 : (x 7 1).toNat = 0 := by
          have r28990 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b28991 := hb (x 7 1)
          have b28992 := hb (x 8 14)
          clear * - r28990 b28991 b28992 d28985
          omega
        have d28993 : (x 7 1 && x 7 12).toNat = 0 := by
          have r28994 := hand1 (x 7 1) (x 7 12)
          have b28995 := hb (x 7 1)
          have b28996 := hb (x 7 1 && x 7 12)
          clear * - r28994 b28995 b28996 d28989
          omega
        have d28997 : (x 8 11).toNat = 1 := by
          have r28998 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b28999 := hb (x 4 4)
          have b29000 := hb (x 8 11)
          have b29001 := hb (x 7 1 && x 7 12)
          have b29002 := hb (x 6 2 && x 6 13)
          have b29003 := hb (x 5 3 && x 5 14)
          clear * - r28998 b28999 b29000 b29001 b29002 b29003 d28993 d28875 d28775 d28742
          omega
        have d29004 : (x 8 3).toNat = 1 := by
          have r29005 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
          have b29006 := hb (x 8 3)
          have b29007 := hb (x 8 11)
          clear * - r29005 b29006 b29007 d28997
          omega
        have d29008 : (x 11 12).toNat = 0 := by
          have r29009 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29010 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e29011 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have b29012 := hb (x 8 3)
          have b29013 := hb (x 9 2)
          have b29014 := hb (x 10 13)
          have b29015 := hb (x 11 12)
          clear * - r29009 e29010 e29011 b29012 b29013 b29014 b29015 d28896 d29004
          omega
        have d29016 : (x 11 1 && x 11 12).toNat = 0 := by
          have r29017 := hand2 (x 11 1) (x 11 12)
          have b29018 := hb (x 11 12)
          have b29019 := hb (x 11 1 && x 11 12)
          clear * - r29017 b29018 b29019 d29008
          omega
        have d29020 : (x 10 13).toNat = 0 := by
          have r29021 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29022 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e29023 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have b29024 := hb (x 8 3)
          have b29025 := hb (x 9 2)
          have b29026 := hb (x 10 13)
          have b29027 := hb (x 11 12)
          clear * - r29021 e29022 e29023 b29024 b29025 b29026 b29027 d29008 d28896 d29004
          omega
        have d29028 : (x 10 2 && x 10 13).toNat = 0 := by
          have r29029 := hand2 (x 10 2) (x 10 13)
          have b29030 := hb (x 10 13)
          have b29031 := hb (x 10 2 && x 10 13)
          clear * - r29029 b29030 b29031 d29020
          omega
        have d29032 : (x 12 11).toNat = 1 := by
          have r29033 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29034 := hb (x 8 4)
          have b29035 := hb (x 12 11)
          have b29036 := hb (x 11 1 && x 11 12)
          have b29037 := hb (x 10 2 && x 10 13)
          have b29038 := hb (x 9 3 && x 9 14)
          clear * - r29033 b29034 b29035 b29036 b29037 b29038 d29016 d29028 d28892 d28830
          omega
        have d29039 : (x 12 3).toNat = 1 := by
          have r29040 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
          have b29041 := hb (x 12 3)
          have b29042 := hb (x 12 11)
          clear * - r29040 b29041 b29042 d29032
          omega
        have d29043 : (x 15 12).toNat = 0 := by
          have r29044 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29045 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
          have e29046 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
          have b29047 := hb (x 12 3)
          have b29048 := hb (x 13 2)
          have b29049 := hb (x 14 13)
          have b29050 := hb (x 15 12)
          clear * - r29044 e29045 e29046 b29047 b29048 b29049 b29050 d29039
          omega
        have d29051 : (x 15 1 && x 15 12).toNat = 0 := by
          have r29052 := hand2 (x 15 1) (x 15 12)
          have b29053 := hb (x 15 12)
          have b29054 := hb (x 15 1 && x 15 12)
          clear * - r29052 b29053 b29054 d29043
          omega
        have d29055 : (x 14 13).toNat = 0 := by
          have r29056 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29057 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
          have e29058 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
          have b29059 := hb (x 12 3)
          have b29060 := hb (x 13 2)
          have b29061 := hb (x 14 13)
          have b29062 := hb (x 15 12)
          clear * - r29056 e29057 e29058 b29059 b29060 b29061 b29062 d29043 d29039
          omega
        have d29063 : (x 14 2 && x 14 13).toNat = 0 := by
          have r29064 := hand2 (x 14 2) (x 14 13)
          have b29065 := hb (x 14 13)
          have b29066 := hb (x 14 2 && x 14 13)
          clear * - r29064 b29065 b29066 d29055
          omega
        have d29067 : (x 13 2).toNat = 0 := by
          have r29068 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29069 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
          have e29070 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
          have b29071 := hb (x 12 3)
          have b29072 := hb (x 13 2)
          have b29073 := hb (x 14 13)
          have b29074 := hb (x 15 12)
          clear * - r29068 e29069 e29070 b29071 b29072 b29073 b29074 d29043 d29055 d29039
          omega
        have d29075 : (x 10 1).toNat = 1 := by
          have r29076 := hand1 (x 10 1) (x 10 14)
          have b29077 := hb (x 10 1)
          have b29078 := hb (x 10 1 && x 10 14)
          clear * - r29076 b29077 b29078 d28963
          omega
        have d29079 : (x 11 14).toNat = 0 := by
          have r29080 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29081 := hb (x 10 1)
          have b29082 := hb (x 11 14)
          clear * - r29080 b29081 b29082 d29075
          omega
        have d29083 : (x 11 1 && x 11 14).toNat = 0 := by
          have r29084 := hand2 (x 11 1) (x 11 14)
          have b29085 := hb (x 11 14)
          have b29086 := hb (x 11 1 && x 11 14)
          clear * - r29084 b29085 b29086 d29079
          omega
        have d29087 : (x 11 2).toNat = 0 := by
          have r29088 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
          have b29089 := hb (x 11 2)
          have b29090 := hb (x 11 14)
          clear * - r29088 b29089 b29090 d29079
          omega
        have d29091 : (x 10 2).toNat = 0 := by
          have r29092 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29093 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
          have e29094 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
          have b29095 := hb (x 9 3)
          have b29096 := hb (x 10 2)
          have b29097 := hb (x 11 13)
          have b29098 := hb (x 12 12)
          clear * - r29092 e29093 e29094 b29095 b29096 b29097 b29098 d28935 d28951 d28931
          omega
        have d29099 : (x 12 13).toNat = 1 := by
          have r29100 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29101 := hb (x 10 2)
          have b29102 := hb (x 12 13)
          have b29103 := hb (x 11 1 && x 11 14)
          clear * - r29100 b29101 b29102 b29103 d29083 d29091
          omega
        have d29104 : (x 12 1).toNat = 1 := by
          have r29105 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
          have b29106 := hb (x 12 1)
          have b29107 := hb (x 12 13)
          clear * - r29105 b29106 b29107 d29099
          omega
        have d29108 : (x 13 14).toNat = 0 := by
          have r29109 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29110 := hb (x 12 1)
          have b29111 := hb (x 13 14)
          clear * - r29109 b29110 b29111 d29104
          omega
        have d29112 : (x 13 1 && x 13 14).toNat = 0 := by
          have r29113 := hand2 (x 13 1) (x 13 14)
          have b29114 := hb (x 13 14)
          have b29115 := hb (x 13 1 && x 13 14)
          clear * - r29113 b29114 b29115 d29108
          omega
        have d29116 : (x 12 2).toNat = 1 := by
          have r29117 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29118 := hb (x 12 2)
          have b29119 := hb (x 14 13)
          have b29120 := hb (x 13 1 && x 13 14)
          clear * - r29117 b29118 b29119 b29120 d29055 d29112
          omega
        have d29121 : (x 14 12).toNat = 0 := by
          have r29122 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29123 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
          have e29124 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
          have b29125 := hb (x 11 3)
          have b29126 := hb (x 12 2)
          have b29127 := hb (x 13 13)
          have b29128 := hb (x 14 12)
          clear * - r29122 e29123 e29124 b29125 b29126 b29127 b29128 d29116
          omega
        have d29129 : (x 14 4).toNat = 0 := by
          have r29130 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
          have b29131 := hb (x 14 4)
          have b29132 := hb (x 14 12)
          clear * - r29130 b29131 b29132 d29121
          omega
        have d29133 : (x 14 4 && x 14 14).toNat = 0 := by
          have r29134 := hand1 (x 14 4) (x 14 14)
          have b29135 := hb (x 14 4)
          have b29136 := hb (x 14 4 && x 14 14)
          clear * - r29134 b29135 b29136 d29129
          omega
        have d29137 : (x 13 13).toNat = 0 := by
          have r29138 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29139 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
          have e29140 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
          have b29141 := hb (x 11 3)
          have b29142 := hb (x 12 2)
          have b29143 := hb (x 13 13)
          have b29144 := hb (x 14 12)
          clear * - r29138 e29139 e29140 b29141 b29142 b29143 b29144 d29121 d29116
          omega
        have d29145 : (x 13 5).toNat = 0 := by
          have r29146 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
          have b29147 := hb (x 13 5)
          have b29148 := hb (x 13 13)
          clear * - r29146 b29147 b29148 d29137
          omega
        have d29149 : (x 13 3 && x 13 14).toNat = 0 := by
          have r29150 := hand2 (x 13 3) (x 13 14)
          have b29151 := hb (x 13 14)
          have b29152 := hb (x 13 3 && x 13 14)
          clear * - r29150 b29151 b29152 d29108
          omega
        have d29153 : (x 16 11).toNat = 1 := by
          have r29154 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29155 := hb (x 12 4)
          have b29156 := hb (x 16 11)
          have b29157 := hb (x 15 1 && x 15 12)
          have b29158 := hb (x 14 2 && x 14 13)
          have b29159 := hb (x 13 3 && x 13 14)
          clear * - r29154 b29155 b29156 b29157 b29158 b29159 d29051 d29063 d29149 d28947
          omega
        have d29160 : (x 16 3).toNat = 1 := by
          have r29161 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
          have b29162 := hb (x 16 3)
          have b29163 := hb (x 16 11)
          clear * - r29161 b29162 b29163 d29153
          omega
        have d29164 : (x 19 12).toNat = 0 := by
          have r29165 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29166 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
          have e29167 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
          have b29168 := hb (x 16 3)
          have b29169 := hb (x 17 2)
          have b29170 := hb (x 18 13)
          have b29171 := hb (x 19 12)
          clear * - r29165 e29166 e29167 b29168 b29169 b29170 b29171 d29160
          omega
        have d29172 : (x 18 13).toNat = 0 := by
          have r29173 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29174 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
          have e29175 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
          have b29176 := hb (x 16 3)
          have b29177 := hb (x 17 2)
          have b29178 := hb (x 18 13)
          have b29179 := hb (x 19 12)
          clear * - r29173 e29174 e29175 b29176 b29177 b29178 b29179 d29164 d29160
          omega
        have d29180 : (x 17 2).toNat = 0 := by
          have r29181 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29182 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
          have e29183 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
          have b29184 := hb (x 16 3)
          have b29185 := hb (x 17 2)
          have b29186 := hb (x 18 13)
          have b29187 := hb (x 19 12)
          clear * - r29181 e29182 e29183 b29184 b29185 b29186 b29187 d29164 d29172 d29160
          omega
        have d29188 : (x 13 12).toNat = 0 := by
          have r29189 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29190 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
          have e29191 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
          have b29192 := hb (x 10 3)
          have b29193 := hb (x 11 2)
          have b29194 := hb (x 12 13)
          have b29195 := hb (x 13 12)
          clear * - r29189 e29190 e29191 b29192 b29193 b29194 b29195 d29099 d29087
          omega
        have d29196 : (x 13 4).toNat = 0 := by
          have r29197 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
          have b29198 := hb (x 13 4)
          have b29199 := hb (x 13 12)
          clear * - r29197 b29198 b29199 d29188
          omega
        have d29200 : (x 10 3).toNat = 0 := by
          have r29201 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29202 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
          have e29203 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
          have b29204 := hb (x 10 3)
          have b29205 := hb (x 11 2)
          have b29206 := hb (x 12 13)
          have b29207 := hb (x 13 12)
          clear * - r29201 e29202 e29203 b29204 b29205 b29206 b29207 d29188 d29099 d29087
          omega
        have d29208 : (x 10 3 && x 10 14).toNat = 0 := by
          have r29209 := hand1 (x 10 3) (x 10 14)
          have b29210 := hb (x 10 3)
          have b29211 := hb (x 10 3 && x 10 14)
          clear * - r29209 b29210 b29211 d29200
          omega
        have d29212 : (x 13 11).toNat = 1 := by
          have r29213 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29214 := hb (x 9 4)
          have b29215 := hb (x 13 11)
          have b29216 := hb (x 12 1 && x 12 12)
          have b29217 := hb (x 11 2 && x 11 13)
          have b29218 := hb (x 10 3 && x 10 14)
          clear * - r29213 b29214 b29215 b29216 b29217 b29218 d28943 d28959 d29208 d28908
          omega
        have d29219 : (x 13 3).toNat = 1 := by
          have r29220 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
          have b29221 := hb (x 13 3)
          have b29222 := hb (x 13 11)
          clear * - r29220 b29221 b29222 d29212
          omega
        have d29223 : (x 16 12).toNat = 0 := by
          have r29224 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29225 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
          have e29226 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
          have b29227 := hb (x 13 3)
          have b29228 := hb (x 14 2)
          have b29229 := hb (x 15 13)
          have b29230 := hb (x 16 12)
          clear * - r29224 e29225 e29226 b29227 b29228 b29229 b29230 d29219
          omega
        have d29231 : (x 16 1 && x 16 12).toNat = 0 := by
          have r29232 := hand2 (x 16 1) (x 16 12)
          have b29233 := hb (x 16 12)
          have b29234 := hb (x 16 1 && x 16 12)
          clear * - r29232 b29233 b29234 d29223
          omega
        have d29235 : (x 16 2 && x 16 12).toNat = 0 := by
          have r29236 := hand2 (x 16 2) (x 16 12)
          have b29237 := hb (x 16 12)
          have b29238 := hb (x 16 2 && x 16 12)
          clear * - r29236 b29237 b29238 d29223
          omega
        have d29239 : (x 15 13).toNat = 0 := by
          have r29240 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29241 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
          have e29242 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
          have b29243 := hb (x 13 3)
          have b29244 := hb (x 14 2)
          have b29245 := hb (x 15 13)
          have b29246 := hb (x 16 12)
          clear * - r29240 e29241 e29242 b29243 b29244 b29245 b29246 d29223 d29219
          omega
        have d29247 : (x 15 2 && x 15 13).toNat = 0 := by
          have r29248 := hand2 (x 15 2) (x 15 13)
          have b29249 := hb (x 15 13)
          have b29250 := hb (x 15 2 && x 15 13)
          clear * - r29248 b29249 b29250 d29239
          omega
        have d29251 : (x 15 3 && x 15 13).toNat = 0 := by
          have r29252 := hand2 (x 15 3) (x 15 13)
          have b29253 := hb (x 15 13)
          have b29254 := hb (x 15 3 && x 15 13)
          clear * - r29252 b29253 b29254 d29239
          omega
        have d29255 : (x 14 1 && x 14 14).toNat = 1 := by
          have r29256 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29257 := hb (x 13 2)
          have b29258 := hb (x 15 13)
          have b29259 := hb (x 14 1 && x 14 14)
          clear * - r29256 b29257 b29258 b29259 d29239 d29067
          omega
        have d29260 : (x 14 1).toNat = 1 := by
          have r29261 := hand1 (x 14 1) (x 14 14)
          have b29262 := hb (x 14 1)
          have b29263 := hb (x 14 1 && x 14 14)
          clear * - r29261 b29262 b29263 d29255
          omega
        have d29264 : (x 15 14).toNat = 0 := by
          have r29265 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29266 := hb (x 14 1)
          have b29267 := hb (x 15 14)
          clear * - r29265 b29266 b29267 d29260
          omega
        have d29268 : (x 15 1 && x 15 14).toNat = 0 := by
          have r29269 := hand2 (x 15 1) (x 15 14)
          have b29270 := hb (x 15 14)
          have b29271 := hb (x 15 1 && x 15 14)
          clear * - r29269 b29270 b29271 d29264
          omega
        have d29272 : (x 15 2).toNat = 0 := by
          have r29273 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
          have b29274 := hb (x 15 2)
          have b29275 := hb (x 15 14)
          clear * - r29273 b29274 b29275 d29264
          omega
        have d29276 : (x 14 2).toNat = 0 := by
          have r29277 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29278 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
          have e29279 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
          have b29280 := hb (x 13 3)
          have b29281 := hb (x 14 2)
          have b29282 := hb (x 15 13)
          have b29283 := hb (x 16 12)
          clear * - r29277 e29278 e29279 b29280 b29281 b29282 b29283 d29223 d29239 d29219
          omega
        have d29284 : (x 16 13).toNat = 1 := by
          have r29285 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29286 := hb (x 14 2)
          have b29287 := hb (x 16 13)
          have b29288 := hb (x 15 1 && x 15 14)
          clear * - r29285 b29286 b29287 b29288 d29268 d29276
          omega
        have d29289 : (x 17 12).toNat = 0 := by
          have r29290 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29291 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
          have e29292 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
          have b29293 := hb (x 14 3)
          have b29294 := hb (x 15 2)
          have b29295 := hb (x 16 13)
          have b29296 := hb (x 17 12)
          clear * - r29290 e29291 e29292 b29293 b29294 b29295 b29296 d29284 d29272
          omega
        have d29297 : (x 14 3).toNat = 0 := by
          have r29298 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29299 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
          have e29300 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
          have b29301 := hb (x 14 3)
          have b29302 := hb (x 15 2)
          have b29303 := hb (x 16 13)
          have b29304 := hb (x 17 12)
          clear * - r29298 e29299 e29300 b29301 b29302 b29303 b29304 d29289 d29284 d29272
          omega
        have d29305 : (x 14 3 && x 14 14).toNat = 0 := by
          have r29306 := hand1 (x 14 3) (x 14 14)
          have b29307 := hb (x 14 3)
          have b29308 := hb (x 14 3 && x 14 14)
          clear * - r29306 b29307 b29308 d29297
          omega
        have d29309 : (x 17 11).toNat = 1 := by
          have r29310 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29311 := hb (x 13 4)
          have b29312 := hb (x 17 11)
          have b29313 := hb (x 16 1 && x 16 12)
          have b29314 := hb (x 15 2 && x 15 13)
          have b29315 := hb (x 14 3 && x 14 14)
          clear * - r29310 b29311 b29312 b29313 b29314 b29315 d29231 d29247 d29305 d29196
          omega
        have d29316 : (x 17 3).toNat = 1 := by
          have r29317 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
          have b29318 := hb (x 17 3)
          have b29319 := hb (x 17 11)
          clear * - r29317 b29318 b29319 d29309
          omega
        have d29320 : (x 20 12).toNat = 0 := by
          have r29321 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29322 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
          have e29323 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
          have b29324 := hb (x 17 3)
          have b29325 := hb (x 18 2)
          have b29326 := hb (x 19 13)
          have b29327 := hb (x 20 12)
          clear * - r29321 e29322 e29323 b29324 b29325 b29326 b29327 d29316
          omega
        have d29328 : (x 19 13).toNat = 0 := by
          have r29329 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29330 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
          have e29331 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
          have b29332 := hb (x 17 3)
          have b29333 := hb (x 18 2)
          have b29334 := hb (x 19 13)
          have b29335 := hb (x 20 12)
          clear * - r29329 e29330 e29331 b29332 b29333 b29334 b29335 d29320 d29316
          omega
        have d29336 : (x 18 1 && x 18 14).toNat = 1 := by
          have r29337 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29338 := hb (x 17 2)
          have b29339 := hb (x 19 13)
          have b29340 := hb (x 18 1 && x 18 14)
          clear * - r29337 b29338 b29339 b29340 d29328 d29180
          omega
        have d29341 : (x 18 14).toNat = 1 := by
          have r29342 := hand2 (x 18 1) (x 18 14)
          have b29343 := hb (x 18 14)
          have b29344 := hb (x 18 1 && x 18 14)
          clear * - r29342 b29343 b29344 d29336
          omega
        have d29345 : (x 17 1).toNat = 0 := by
          have r29346 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29347 := hb (x 17 1)
          have b29348 := hb (x 18 14)
          clear * - r29346 b29347 b29348 d29341
          omega
        have d29349 : (x 17 1 && x 17 11).toNat = 0 := by
          have r29350 := hand1 (x 17 1) (x 17 11)
          have b29351 := hb (x 17 1)
          have b29352 := hb (x 17 1 && x 17 11)
          clear * - r29350 b29351 b29352 d29345
          omega
        have d29353 : (x 18 2).toNat = 0 := by
          have r29354 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29355 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
          have e29356 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
          have b29357 := hb (x 17 3)
          have b29358 := hb (x 18 2)
          have b29359 := hb (x 19 13)
          have b29360 := hb (x 20 12)
          clear * - r29354 e29355 e29356 b29357 b29358 b29359 b29360 d29320 d29328 d29316
          omega
        have d29361 : (x 18 10).toNat = 0 := by
          have r29362 : (x 18 10).toNat ≤ (x 18 2).toNat := himp _ _ (hp10 18)
          have b29363 := hb (x 18 2)
          have b29364 := hb (x 18 10)
          clear * - r29362 b29363 b29364 d29353
          omega
        have r29365 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := by have q := hcov10 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b29366 := hb (x 13 5)
        have b29367 := hb (x 18 10)
        have b29368 := hb (x 17 1 && x 17 11)
        have b29369 := hb (x 16 2 && x 16 12)
        have b29370 := hb (x 15 3 && x 15 13)
        have b29371 := hb (x 14 4 && x 14 14)
        linarith only [r29365, b29366, b29367, b29368, b29369, b29370, b29371, d29361, d29349, d29235, d29251, d29133, d29145]
    · have f29372 : (x (-1) 6).toNat = 1 := by rw [h28213]; rfl
      have d29373 : (x 5 8).toNat = 0 := by
        have r29374 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e29375 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
        have e29376 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
        have e29377 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
        have e29378 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
        have e29379 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
        have e29380 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
        have b29381 := hb (x (-2) 7)
        have b29382 := hb (x (-1) 6)
        have b29383 := hb (x 0 5)
        have b29384 := hb (x 1 4)
        have b29385 := hb (x 2 11)
        have b29386 := hb (x 3 10)
        have b29387 := hb (x 4 9)
        have b29388 := hb (x 5 8)
        clear * - r29374 e29375 e29376 e29377 e29378 e29379 e29380 b29381 b29382 b29383 b29384 b29385 b29386 b29387 b29388 d28062 d28167 g12 f29372
        omega
      have d29389 : (x 4 9).toNat = 0 := by
        have r29390 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e29391 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
        have e29392 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
        have e29393 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
        have e29394 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
        have e29395 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
        have e29396 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
        have b29397 := hb (x (-2) 7)
        have b29398 := hb (x (-1) 6)
        have b29399 := hb (x 0 5)
        have b29400 := hb (x 1 4)
        have b29401 := hb (x 2 11)
        have b29402 := hb (x 3 10)
        have b29403 := hb (x 4 9)
        have b29404 := hb (x 5 8)
        clear * - r29390 e29391 e29392 e29393 e29394 e29395 e29396 b29397 b29398 b29399 b29400 b29401 b29402 b29403 b29404 d29373 d28062 d28167 g12 f29372
        omega
      have d29405 : (x 2 11).toNat = 0 := by
        have r29406 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e29407 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
        have e29408 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
        have e29409 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
        have e29410 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
        have e29411 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
        have e29412 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
        have b29413 := hb (x (-2) 7)
        have b29414 := hb (x (-1) 6)
        have b29415 := hb (x 0 5)
        have b29416 := hb (x 1 4)
        have b29417 := hb (x 2 11)
        have b29418 := hb (x 3 10)
        have b29419 := hb (x 4 9)
        have b29420 := hb (x 5 8)
        clear * - r29406 e29407 e29408 e29409 e29410 e29411 e29412 b29413 b29414 b29415 b29416 b29417 b29418 b29419 b29420 d29373 d29389 d28062 d28167 g12 f29372
        omega
      have d29421 : (x 2 1 && x 2 11).toNat = 0 := by
        have r29422 := hand2 (x 2 1) (x 2 11)
        have b29423 := hb (x 2 11)
        have b29424 := hb (x 2 1 && x 2 11)
        clear * - r29422 b29423 b29424 d29405
        omega
      have d29425 : (x (-1) 4 && x (-1) 14).toNat = 1 := by
        have r29426 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b29427 := hb (x (-2) 5)
        have b29428 := hb (x 3 10)
        have b29429 := hb (x 2 1 && x 2 11)
        have b29430 := hb (x 1 2 && x 1 12)
        have b29431 := hb (x 0 3 && x 0 13)
        have b29432 := hb (x (-1) 4 && x (-1) 14)
        clear * - r29426 b29427 b29428 b29429 b29430 b29431 b29432 d28062 d29421 d28143 g55 d28091
        omega
      have d29433 : (x (-1) 4).toNat = 1 := by
        have r29434 := hand1 (x (-1) 4) (x (-1) 14)
        have b29435 := hb (x (-1) 4)
        have b29436 := hb (x (-1) 4 && x (-1) 14)
        clear * - r29434 b29435 b29436 d29425
        omega
      have d29437 : (x (-1) 12).toNat = 1 := by
        have r29438 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
        have b29439 := hb (x (-1) 4)
        have b29440 := hb (x (-1) 12)
        clear * - r29438 b29439 b29440 d29433
        omega
      have d29441 : (x (-3) 2).toNat = 0 := by
        have r29442 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e29443 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e29444 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b29445 := hb (x (-4) 3)
        have b29446 := hb (x (-3) 2)
        have b29447 := hb (x (-2) 13)
        have b29448 := hb (x (-1) 12)
        clear * - r29442 e29443 e29444 b29445 b29446 b29447 b29448 d29437 d28083
        omega
      have d29449 : (x (-1) 13).toNat = 1 := by
        have r29450 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b29451 := hb (x (-3) 2)
        have b29452 := hb (x (-1) 13)
        have b29453 := hb (x (-2) 1 && x (-2) 14)
        clear * - r29450 b29451 b29452 b29453 d28079 d29441
        omega
      have d29454 : (x (-2) 2).toNat = 0 := by
        have r29455 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e29456 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
        have e29457 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
        have b29458 := hb (x (-3) 3)
        have b29459 := hb (x (-2) 2)
        have b29460 := hb (x (-1) 13)
        have b29461 := hb (x 0 12)
        clear * - r29455 e29456 e29457 b29458 b29459 b29460 b29461 g19 d29449
        omega
      have d29462 : (x (-2) 2 && x (-2) 12).toNat = 0 := by
        have r29463 := hand1 (x (-2) 2) (x (-2) 12)
        have b29464 := hb (x (-2) 2)
        have b29465 := hb (x (-2) 2 && x (-2) 12)
        clear * - r29463 b29464 b29465 d29454
        omega
      have d29466 : (x (-3) 3 && x (-3) 13).toNat = 1 := by
        have r29467 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b29468 := hb (x (-5) 5)
        have b29469 := hb (x 0 10)
        have b29470 := hb (x (-1) 1 && x (-1) 11)
        have b29471 := hb (x (-2) 2 && x (-2) 12)
        have b29472 := hb (x (-3) 3 && x (-3) 13)
        have b29473 := hb (x (-4) 4 && x (-4) 14)
        clear * - r29467 b29468 b29469 b29470 b29471 b29472 b29473 g17 d28205 d29462 g54 g2
        omega
      have d29474 : (x (-3) 3).toNat = 1 := by
        have r29475 := hand1 (x (-3) 3) (x (-3) 13)
        have b29476 := hb (x (-3) 3)
        have b29477 := hb (x (-3) 3 && x (-3) 13)
        clear * - r29475 b29476 b29477 d29466
        omega
      have r29478 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e29479 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e29480 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have b29481 := hb (x (-3) 3)
      have b29482 := hb (x (-2) 2)
      have b29483 := hb (x (-1) 13)
      have b29484 := hb (x 0 12)
      linarith only [r29478, e29479, e29480, b29481, b29482, b29483, b29484, g19, d29449, d29454, d29474]
  · have f29485 : (x (-1) 3).toNat = 1 := by rw [h28199]; rfl
    have d29486 : (x 2 12).toNat = 0 := by
      have r29487 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e29488 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e29489 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b29490 := hb (x (-1) 3)
      have b29491 := hb (x 0 2)
      have b29492 := hb (x 1 13)
      have b29493 := hb (x 2 12)
      clear * - r29487 e29488 e29489 b29490 b29491 b29492 b29493 d27985 g9 f29485
      omega
    have d29494 : (x 2 1 && x 2 12).toNat = 0 := by
      have r29495 := hand2 (x 2 1) (x 2 12)
      have b29496 := hb (x 2 12)
      have b29497 := hb (x 2 1 && x 2 12)
      clear * - r29495 b29496 b29497 d29486
      omega
    have d29498 : (x 2 2 && x 2 12).toNat = 0 := by
      have r29499 := hand2 (x 2 2) (x 2 12)
      have b29500 := hb (x 2 12)
      have b29501 := hb (x 2 2 && x 2 12)
      clear * - r29499 b29500 b29501 d29486
      omega
    have d29502 : (x 2 4).toNat = 0 := by
      have r29503 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
      have b29504 := hb (x 2 4)
      have b29505 := hb (x 2 12)
      clear * - r29503 b29504 b29505 d29486
      omega
    have d29506 : (x 2 4 && x 2 14).toNat = 0 := by
      have r29507 := hand1 (x 2 4) (x 2 14)
      have b29508 := hb (x 2 4)
      have b29509 := hb (x 2 4 && x 2 14)
      clear * - r29507 b29508 b29509 d29502
      omega
    cases h29510 : x 1 3
    · have f29511 : (x 1 3).toNat = 0 := by rw [h29510]; rfl
      have d29512 : (x 1 3 && x 1 14).toNat = 0 := by
        have r29513 := hand1 (x 1 3) (x 1 14)
        have b29514 := hb (x 1 3)
        have b29515 := hb (x 1 3 && x 1 14)
        clear * - r29513 b29514 b29515 f29511
        omega
      have d29516 : (x 1 11).toNat = 0 := by
        have r29517 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
        have b29518 := hb (x 1 3)
        have b29519 := hb (x 1 11)
        clear * - r29517 b29518 b29519 f29511
        omega
      have d29520 : (x 1 11 && x 1 14).toNat = 0 := by
        have r29521 := hand1 (x 1 11) (x 1 14)
        have b29522 := hb (x 1 11)
        have b29523 := hb (x 1 11 && x 1 14)
        clear * - r29521 b29522 b29523 d29516
        omega
      cases h29524 : x (-1) 4
      · have f29525 : (x (-1) 4).toNat = 0 := by rw [h29524]; rfl
        have d29526 : (x 3 11).toNat = 1 := by
          have r29527 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29528 := hb (x (-1) 4)
          have b29529 := hb (x 3 11)
          have b29530 := hb (x 2 1 && x 2 12)
          have b29531 := hb (x 1 2 && x 1 13)
          have b29532 := hb (x 0 3 && x 0 14)
          clear * - r29527 b29528 b29529 b29530 b29531 b29532 d29494 d27989 g58 f29525
          omega
        have d29533 : (x 3 3).toNat = 1 := by
          have r29534 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
          have b29535 := hb (x 3 3)
          have b29536 := hb (x 3 11)
          clear * - r29534 b29535 b29536 d29526
          omega
        have d29537 : (x 6 12).toNat = 0 := by
          have r29538 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29539 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e29540 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b29541 := hb (x 3 3)
          have b29542 := hb (x 4 2)
          have b29543 := hb (x 5 13)
          have b29544 := hb (x 6 12)
          clear * - r29538 e29539 e29540 b29541 b29542 b29543 b29544 d29533
          omega
        have d29545 : (x 6 1 && x 6 12).toNat = 0 := by
          have r29546 := hand2 (x 6 1) (x 6 12)
          have b29547 := hb (x 6 12)
          have b29548 := hb (x 6 1 && x 6 12)
          clear * - r29546 b29547 b29548 d29537
          omega
        have d29549 : (x 6 4).toNat = 0 := by
          have r29550 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
          have b29551 := hb (x 6 4)
          have b29552 := hb (x 6 12)
          clear * - r29550 b29551 b29552 d29537
          omega
        have d29553 : (x 5 13).toNat = 0 := by
          have r29554 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29555 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e29556 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b29557 := hb (x 3 3)
          have b29558 := hb (x 4 2)
          have b29559 := hb (x 5 13)
          have b29560 := hb (x 6 12)
          clear * - r29554 e29555 e29556 b29557 b29558 b29559 b29560 d29537 d29533
          omega
        have d29561 : (x 5 2 && x 5 13).toNat = 0 := by
          have r29562 := hand2 (x 5 2) (x 5 13)
          have b29563 := hb (x 5 13)
          have b29564 := hb (x 5 2 && x 5 13)
          clear * - r29562 b29563 b29564 d29553
          omega
        have d29565 : (x 4 1 && x 4 14).toNat = 1 := by
          have r29566 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29567 := hb (x 3 2)
          have b29568 := hb (x 5 13)
          have b29569 := hb (x 4 1 && x 4 14)
          clear * - r29566 b29567 b29568 b29569 d29553 d28050
          omega
        have d29570 : (x 4 1).toNat = 1 := by
          have r29571 := hand1 (x 4 1) (x 4 14)
          have b29572 := hb (x 4 1)
          have b29573 := hb (x 4 1 && x 4 14)
          clear * - r29571 b29572 b29573 d29565
          omega
        have d29574 : (x 5 14).toNat = 0 := by
          have r29575 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29576 := hb (x 4 1)
          have b29577 := hb (x 5 14)
          clear * - r29575 b29576 b29577 d29570
          omega
        have d29578 : (x 5 1 && x 5 14).toNat = 0 := by
          have r29579 := hand2 (x 5 1) (x 5 14)
          have b29580 := hb (x 5 14)
          have b29581 := hb (x 5 1 && x 5 14)
          clear * - r29579 b29580 b29581 d29574
          omega
        have d29582 : (x 5 2).toNat = 0 := by
          have r29583 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
          have b29584 := hb (x 5 2)
          have b29585 := hb (x 5 14)
          clear * - r29583 b29584 b29585 d29574
          omega
        have d29586 : (x 4 2).toNat = 0 := by
          have r29587 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29588 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e29589 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b29590 := hb (x 3 3)
          have b29591 := hb (x 4 2)
          have b29592 := hb (x 5 13)
          have b29593 := hb (x 6 12)
          clear * - r29587 e29588 e29589 b29590 b29591 b29592 b29593 d29537 d29553 d29533
          omega
        have d29594 : (x 4 2 && x 4 13).toNat = 0 := by
          have r29595 := hand1 (x 4 2) (x 4 13)
          have b29596 := hb (x 4 2)
          have b29597 := hb (x 4 2 && x 4 13)
          clear * - r29595 b29596 b29597 d29586
          omega
        have d29598 : (x 6 13).toNat = 1 := by
          have r29599 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29600 := hb (x 4 2)
          have b29601 := hb (x 6 13)
          have b29602 := hb (x 5 1 && x 5 14)
          clear * - r29599 b29600 b29601 b29602 d29578 d29586
          omega
        have d29603 : (x 6 1).toNat = 1 := by
          have r29604 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
          have b29605 := hb (x 6 1)
          have b29606 := hb (x 6 13)
          clear * - r29604 b29605 b29606 d29598
          omega
        have d29607 : (x 7 14).toNat = 0 := by
          have r29608 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29609 := hb (x 6 1)
          have b29610 := hb (x 7 14)
          clear * - r29608 b29609 b29610 d29603
          omega
        have d29611 : (x 7 3 && x 7 14).toNat = 0 := by
          have r29612 := hand2 (x 7 3) (x 7 14)
          have b29613 := hb (x 7 14)
          have b29614 := hb (x 7 3 && x 7 14)
          clear * - r29612 b29613 b29614 d29607
          omega
        have d29615 : (x 7 2).toNat = 0 := by
          have r29616 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
          have b29617 := hb (x 7 2)
          have b29618 := hb (x 7 14)
          clear * - r29616 b29617 b29618 d29607
          omega
        have d29619 : (x 7 12).toNat = 0 := by
          have r29620 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29621 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
          have e29622 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
          have b29623 := hb (x 4 3)
          have b29624 := hb (x 5 2)
          have b29625 := hb (x 6 13)
          have b29626 := hb (x 7 12)
          clear * - r29620 e29621 e29622 b29623 b29624 b29625 b29626 d29598 d29582
          omega
        have d29627 : (x 7 4).toNat = 0 := by
          have r29628 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
          have b29629 := hb (x 7 4)
          have b29630 := hb (x 7 12)
          clear * - r29628 b29629 b29630 d29619
          omega
        have d29631 : (x 4 3).toNat = 0 := by
          have r29632 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29633 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
          have e29634 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
          have b29635 := hb (x 4 3)
          have b29636 := hb (x 5 2)
          have b29637 := hb (x 6 13)
          have b29638 := hb (x 7 12)
          clear * - r29632 e29633 e29634 b29635 b29636 b29637 b29638 d29619 d29598 d29582
          omega
        have d29639 : (x 4 3 && x 4 14).toNat = 0 := by
          have r29640 := hand1 (x 4 3) (x 4 14)
          have b29641 := hb (x 4 3)
          have b29642 := hb (x 4 3 && x 4 14)
          clear * - r29640 b29641 b29642 d29631
          omega
        have d29643 : (x 7 11).toNat = 1 := by
          have r29644 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29645 := hb (x 3 4)
          have b29646 := hb (x 7 11)
          have b29647 := hb (x 6 1 && x 6 12)
          have b29648 := hb (x 5 2 && x 5 13)
          have b29649 := hb (x 4 3 && x 4 14)
          clear * - r29644 b29645 b29646 b29647 b29648 b29649 d29545 d29561 d29639 d28123
          omega
        have d29650 : (x 7 3).toNat = 1 := by
          have r29651 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
          have b29652 := hb (x 7 3)
          have b29653 := hb (x 7 11)
          clear * - r29651 b29652 b29653 d29643
          omega
        have d29654 : (x 10 12).toNat = 0 := by
          have r29655 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29656 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
          have e29657 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
          have b29658 := hb (x 7 3)
          have b29659 := hb (x 8 2)
          have b29660 := hb (x 9 13)
          have b29661 := hb (x 10 12)
          clear * - r29655 e29656 e29657 b29658 b29659 b29660 b29661 d29650
          omega
        have d29662 : (x 10 1 && x 10 12).toNat = 0 := by
          have r29663 := hand2 (x 10 1) (x 10 12)
          have b29664 := hb (x 10 12)
          have b29665 := hb (x 10 1 && x 10 12)
          clear * - r29663 b29664 b29665 d29654
          omega
        have d29666 : (x 10 4).toNat = 0 := by
          have r29667 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
          have b29668 := hb (x 10 4)
          have b29669 := hb (x 10 12)
          clear * - r29667 b29668 b29669 d29654
          omega
        have d29670 : (x 9 13).toNat = 0 := by
          have r29671 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29672 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
          have e29673 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
          have b29674 := hb (x 7 3)
          have b29675 := hb (x 8 2)
          have b29676 := hb (x 9 13)
          have b29677 := hb (x 10 12)
          clear * - r29671 e29672 e29673 b29674 b29675 b29676 b29677 d29654 d29650
          omega
        have d29678 : (x 9 2 && x 9 13).toNat = 0 := by
          have r29679 := hand2 (x 9 2) (x 9 13)
          have b29680 := hb (x 9 13)
          have b29681 := hb (x 9 2 && x 9 13)
          clear * - r29679 b29680 b29681 d29670
          omega
        have d29682 : (x 8 1 && x 8 14).toNat = 1 := by
          have r29683 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29684 := hb (x 7 2)
          have b29685 := hb (x 9 13)
          have b29686 := hb (x 8 1 && x 8 14)
          clear * - r29683 b29684 b29685 b29686 d29670 d29615
          omega
        have d29687 : (x 8 14).toNat = 1 := by
          have r29688 := hand2 (x 8 1) (x 8 14)
          have b29689 := hb (x 8 14)
          have b29690 := hb (x 8 1 && x 8 14)
          clear * - r29688 b29689 b29690 d29682
          omega
        have d29691 : (x 7 1).toNat = 0 := by
          have r29692 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29693 := hb (x 7 1)
          have b29694 := hb (x 8 14)
          clear * - r29692 b29693 b29694 d29687
          omega
        have d29695 : (x 7 13).toNat = 0 := by
          have r29696 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
          have b29697 := hb (x 7 1)
          have b29698 := hb (x 7 13)
          clear * - r29696 b29697 b29698 d29691
          omega
        have d29699 : (x 6 1 && x 6 14).toNat = 1 := by
          have r29700 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29701 := hb (x 5 2)
          have b29702 := hb (x 7 13)
          have b29703 := hb (x 6 1 && x 6 14)
          clear * - r29700 b29701 b29702 b29703 d29695 d29582
          omega
        have d29704 : (x 6 14).toNat = 1 := by
          have r29705 := hand2 (x 6 1) (x 6 14)
          have b29706 := hb (x 6 14)
          have b29707 := hb (x 6 1 && x 6 14)
          clear * - r29705 b29706 b29707 d29699
          omega
        have d29708 : (x 5 1).toNat = 0 := by
          have r29709 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29710 := hb (x 5 1)
          have b29711 := hb (x 6 14)
          clear * - r29709 b29710 b29711 d29704
          omega
        have d29712 : (x 5 1 && x 5 12).toNat = 0 := by
          have r29713 := hand1 (x 5 1) (x 5 12)
          have b29714 := hb (x 5 1)
          have b29715 := hb (x 5 1 && x 5 12)
          clear * - r29713 b29714 b29715 d29708
          omega
        have d29716 : (x 6 11).toNat = 1 := by
          have r29717 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := by have q := hcov11 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29718 := hb (x 2 4)
          have b29719 := hb (x 6 11)
          have b29720 := hb (x 5 1 && x 5 12)
          have b29721 := hb (x 4 2 && x 4 13)
          have b29722 := hb (x 3 3 && x 3 14)
          clear * - r29717 b29718 b29719 b29720 b29721 b29722 d29712 d29594 d28038 d29502
          omega
        have d29723 : (x 6 3).toNat = 1 := by
          have r29724 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
          have b29725 := hb (x 6 3)
          have b29726 := hb (x 6 11)
          clear * - r29724 b29725 b29726 d29716
          omega
        have d29727 : (x 9 12).toNat = 0 := by
          have r29728 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29729 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
          have e29730 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
          have b29731 := hb (x 6 3)
          have b29732 := hb (x 7 2)
          have b29733 := hb (x 8 13)
          have b29734 := hb (x 9 12)
          clear * - r29728 e29729 e29730 b29731 b29732 b29733 b29734 d29615 d29723
          omega
        have d29735 : (x 9 1 && x 9 12).toNat = 0 := by
          have r29736 := hand2 (x 9 1) (x 9 12)
          have b29737 := hb (x 9 12)
          have b29738 := hb (x 9 1 && x 9 12)
          clear * - r29736 b29737 b29738 d29727
          omega
        have d29739 : (x 8 13).toNat = 0 := by
          have r29740 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29741 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
          have e29742 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
          have b29743 := hb (x 6 3)
          have b29744 := hb (x 7 2)
          have b29745 := hb (x 8 13)
          have b29746 := hb (x 9 12)
          clear * - r29740 e29741 e29742 b29743 b29744 b29745 b29746 d29727 d29615 d29723
          omega
        have d29747 : (x 8 2 && x 8 13).toNat = 0 := by
          have r29748 := hand2 (x 8 2) (x 8 13)
          have b29749 := hb (x 8 13)
          have b29750 := hb (x 8 2 && x 8 13)
          clear * - r29748 b29749 b29750 d29739
          omega
        have d29751 : (x 10 11).toNat = 1 := by
          have r29752 : 1 ≤ (x 10 11).toNat + (x 9 1 && x 9 12).toNat + (x 8 2 && x 8 13).toNat + (x 7 3 && x 7 14).toNat + (x 6 4).toNat := by have q := hcov11 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29753 := hb (x 6 4)
          have b29754 := hb (x 10 11)
          have b29755 := hb (x 9 1 && x 9 12)
          have b29756 := hb (x 8 2 && x 8 13)
          have b29757 := hb (x 7 3 && x 7 14)
          clear * - r29752 b29753 b29754 b29755 b29756 b29757 d29735 d29747 d29611 d29549
          omega
        have d29758 : (x 10 3).toNat = 1 := by
          have r29759 : (x 10 11).toNat ≤ (x 10 3).toNat := himp _ _ (hp11 10)
          have b29760 := hb (x 10 3)
          have b29761 := hb (x 10 11)
          clear * - r29759 b29760 b29761 d29751
          omega
        have d29762 : (x 13 12).toNat = 0 := by
          have r29763 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29764 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
          have e29765 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
          have b29766 := hb (x 10 3)
          have b29767 := hb (x 11 2)
          have b29768 := hb (x 12 13)
          have b29769 := hb (x 13 12)
          clear * - r29763 e29764 e29765 b29766 b29767 b29768 b29769 d29758
          omega
        have d29770 : (x 13 1 && x 13 12).toNat = 0 := by
          have r29771 := hand2 (x 13 1) (x 13 12)
          have b29772 := hb (x 13 12)
          have b29773 := hb (x 13 1 && x 13 12)
          clear * - r29771 b29772 b29773 d29762
          omega
        have d29774 : (x 12 13).toNat = 0 := by
          have r29775 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29776 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
          have e29777 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
          have b29778 := hb (x 10 3)
          have b29779 := hb (x 11 2)
          have b29780 := hb (x 12 13)
          have b29781 := hb (x 13 12)
          clear * - r29775 e29776 e29777 b29778 b29779 b29780 b29781 d29762 d29758
          omega
        have d29782 : (x 12 2 && x 12 13).toNat = 0 := by
          have r29783 := hand2 (x 12 2) (x 12 13)
          have b29784 := hb (x 12 13)
          have b29785 := hb (x 12 2 && x 12 13)
          clear * - r29783 b29784 b29785 d29774
          omega
        have d29786 : (x 11 2).toNat = 0 := by
          have r29787 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29788 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
          have e29789 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
          have b29790 := hb (x 10 3)
          have b29791 := hb (x 11 2)
          have b29792 := hb (x 12 13)
          have b29793 := hb (x 13 12)
          clear * - r29787 e29788 e29789 b29790 b29791 b29792 b29793 d29762 d29774 d29758
          omega
        have d29794 : (x 8 1).toNat = 1 := by
          have r29795 := hand1 (x 8 1) (x 8 14)
          have b29796 := hb (x 8 1)
          have b29797 := hb (x 8 1 && x 8 14)
          clear * - r29795 b29796 b29797 d29682
          omega
        have d29798 : (x 9 14).toNat = 0 := by
          have r29799 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29800 := hb (x 8 1)
          have b29801 := hb (x 9 14)
          clear * - r29799 b29800 b29801 d29794
          omega
        have d29802 : (x 9 1 && x 9 14).toNat = 0 := by
          have r29803 := hand2 (x 9 1) (x 9 14)
          have b29804 := hb (x 9 14)
          have b29805 := hb (x 9 1 && x 9 14)
          clear * - r29803 b29804 b29805 d29798
          omega
        have d29806 : (x 9 2).toNat = 0 := by
          have r29807 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
          have b29808 := hb (x 9 2)
          have b29809 := hb (x 9 14)
          clear * - r29807 b29808 b29809 d29798
          omega
        have d29810 : (x 8 2).toNat = 0 := by
          have r29811 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29812 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
          have e29813 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
          have b29814 := hb (x 7 3)
          have b29815 := hb (x 8 2)
          have b29816 := hb (x 9 13)
          have b29817 := hb (x 10 12)
          clear * - r29811 e29812 e29813 b29814 b29815 b29816 b29817 d29654 d29670 d29650
          omega
        have d29818 : (x 10 13).toNat = 1 := by
          have r29819 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29820 := hb (x 8 2)
          have b29821 := hb (x 10 13)
          have b29822 := hb (x 9 1 && x 9 14)
          clear * - r29819 b29820 b29821 b29822 d29802 d29810
          omega
        have d29823 : (x 10 1).toNat = 1 := by
          have r29824 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
          have b29825 := hb (x 10 1)
          have b29826 := hb (x 10 13)
          clear * - r29824 b29825 b29826 d29818
          omega
        have d29827 : (x 11 14).toNat = 0 := by
          have r29828 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29829 := hb (x 10 1)
          have b29830 := hb (x 11 14)
          clear * - r29828 b29829 b29830 d29823
          omega
        have d29831 : (x 11 1 && x 11 14).toNat = 0 := by
          have r29832 := hand2 (x 11 1) (x 11 14)
          have b29833 := hb (x 11 14)
          have b29834 := hb (x 11 1 && x 11 14)
          clear * - r29832 b29833 b29834 d29827
          omega
        have d29835 : (x 10 2).toNat = 1 := by
          have r29836 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29837 := hb (x 10 2)
          have b29838 := hb (x 12 13)
          have b29839 := hb (x 11 1 && x 11 14)
          clear * - r29836 b29837 b29838 b29839 d29774 d29831
          omega
        have d29840 : (x 12 12).toNat = 0 := by
          have r29841 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29842 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
          have e29843 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
          have b29844 := hb (x 9 3)
          have b29845 := hb (x 10 2)
          have b29846 := hb (x 11 13)
          have b29847 := hb (x 12 12)
          clear * - r29841 e29842 e29843 b29844 b29845 b29846 b29847 d29835
          omega
        have d29848 : (x 12 4).toNat = 0 := by
          have r29849 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
          have b29850 := hb (x 12 4)
          have b29851 := hb (x 12 12)
          clear * - r29849 b29850 b29851 d29840
          omega
        have d29852 : (x 12 4 && x 12 14).toNat = 0 := by
          have r29853 := hand1 (x 12 4) (x 12 14)
          have b29854 := hb (x 12 4)
          have b29855 := hb (x 12 4 && x 12 14)
          clear * - r29853 b29854 b29855 d29848
          omega
        have d29856 : (x 11 13).toNat = 0 := by
          have r29857 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29858 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
          have e29859 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
          have b29860 := hb (x 9 3)
          have b29861 := hb (x 10 2)
          have b29862 := hb (x 11 13)
          have b29863 := hb (x 12 12)
          clear * - r29857 e29858 e29859 b29860 b29861 b29862 b29863 d29840 d29835
          omega
        have d29864 : (x 11 5).toNat = 0 := by
          have r29865 : (x 11 5).toNat ≤ (x 11 13).toNat := himp _ _ (hp5 11)
          have b29866 := hb (x 11 5)
          have b29867 := hb (x 11 13)
          clear * - r29865 b29866 b29867 d29856
          omega
        have d29868 : (x 11 3 && x 11 14).toNat = 0 := by
          have r29869 := hand2 (x 11 3) (x 11 14)
          have b29870 := hb (x 11 14)
          have b29871 := hb (x 11 3 && x 11 14)
          clear * - r29869 b29870 b29871 d29827
          omega
        have d29872 : (x 14 11).toNat = 1 := by
          have r29873 : 1 ≤ (x 14 11).toNat + (x 13 1 && x 13 12).toNat + (x 12 2 && x 12 13).toNat + (x 11 3 && x 11 14).toNat + (x 10 4).toNat := by have q := hcov11 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29874 := hb (x 10 4)
          have b29875 := hb (x 14 11)
          have b29876 := hb (x 13 1 && x 13 12)
          have b29877 := hb (x 12 2 && x 12 13)
          have b29878 := hb (x 11 3 && x 11 14)
          clear * - r29873 b29874 b29875 b29876 b29877 b29878 d29770 d29782 d29868 d29666
          omega
        have d29879 : (x 14 3).toNat = 1 := by
          have r29880 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
          have b29881 := hb (x 14 3)
          have b29882 := hb (x 14 11)
          clear * - r29880 b29881 b29882 d29872
          omega
        have d29883 : (x 17 12).toNat = 0 := by
          have r29884 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29885 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
          have e29886 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
          have b29887 := hb (x 14 3)
          have b29888 := hb (x 15 2)
          have b29889 := hb (x 16 13)
          have b29890 := hb (x 17 12)
          clear * - r29884 e29885 e29886 b29887 b29888 b29889 b29890 d29879
          omega
        have d29891 : (x 16 13).toNat = 0 := by
          have r29892 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29893 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
          have e29894 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
          have b29895 := hb (x 14 3)
          have b29896 := hb (x 15 2)
          have b29897 := hb (x 16 13)
          have b29898 := hb (x 17 12)
          clear * - r29892 e29893 e29894 b29895 b29896 b29897 b29898 d29883 d29879
          omega
        have d29899 : (x 15 2).toNat = 0 := by
          have r29900 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29901 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
          have e29902 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
          have b29903 := hb (x 14 3)
          have b29904 := hb (x 15 2)
          have b29905 := hb (x 16 13)
          have b29906 := hb (x 17 12)
          clear * - r29900 e29901 e29902 b29903 b29904 b29905 b29906 d29883 d29891 d29879
          omega
        have d29907 : (x 11 12).toNat = 0 := by
          have r29908 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29909 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e29910 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have b29911 := hb (x 8 3)
          have b29912 := hb (x 9 2)
          have b29913 := hb (x 10 13)
          have b29914 := hb (x 11 12)
          clear * - r29908 e29909 e29910 b29911 b29912 b29913 b29914 d29818 d29806
          omega
        have d29915 : (x 11 4).toNat = 0 := by
          have r29916 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
          have b29917 := hb (x 11 4)
          have b29918 := hb (x 11 12)
          clear * - r29916 b29917 b29918 d29907
          omega
        have d29919 : (x 8 3).toNat = 0 := by
          have r29920 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29921 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e29922 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have b29923 := hb (x 8 3)
          have b29924 := hb (x 9 2)
          have b29925 := hb (x 10 13)
          have b29926 := hb (x 11 12)
          clear * - r29920 e29921 e29922 b29923 b29924 b29925 b29926 d29907 d29818 d29806
          omega
        have d29927 : (x 8 3 && x 8 14).toNat = 0 := by
          have r29928 := hand1 (x 8 3) (x 8 14)
          have b29929 := hb (x 8 3)
          have b29930 := hb (x 8 3 && x 8 14)
          clear * - r29928 b29929 b29930 d29919
          omega
        have d29931 : (x 11 11).toNat = 1 := by
          have r29932 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29933 := hb (x 7 4)
          have b29934 := hb (x 11 11)
          have b29935 := hb (x 10 1 && x 10 12)
          have b29936 := hb (x 9 2 && x 9 13)
          have b29937 := hb (x 8 3 && x 8 14)
          clear * - r29932 b29933 b29934 b29935 b29936 b29937 d29662 d29678 d29927 d29627
          omega
        have d29938 : (x 11 3).toNat = 1 := by
          have r29939 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
          have b29940 := hb (x 11 3)
          have b29941 := hb (x 11 11)
          clear * - r29939 b29940 b29941 d29931
          omega
        have d29942 : (x 14 12).toNat = 0 := by
          have r29943 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29944 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
          have e29945 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
          have b29946 := hb (x 11 3)
          have b29947 := hb (x 12 2)
          have b29948 := hb (x 13 13)
          have b29949 := hb (x 14 12)
          clear * - r29943 e29944 e29945 b29946 b29947 b29948 b29949 d29938
          omega
        have d29950 : (x 14 1 && x 14 12).toNat = 0 := by
          have r29951 := hand2 (x 14 1) (x 14 12)
          have b29952 := hb (x 14 12)
          have b29953 := hb (x 14 1 && x 14 12)
          clear * - r29951 b29952 b29953 d29942
          omega
        have d29954 : (x 14 2 && x 14 12).toNat = 0 := by
          have r29955 := hand2 (x 14 2) (x 14 12)
          have b29956 := hb (x 14 12)
          have b29957 := hb (x 14 2 && x 14 12)
          clear * - r29955 b29956 b29957 d29942
          omega
        have d29958 : (x 13 13).toNat = 0 := by
          have r29959 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29960 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
          have e29961 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
          have b29962 := hb (x 11 3)
          have b29963 := hb (x 12 2)
          have b29964 := hb (x 13 13)
          have b29965 := hb (x 14 12)
          clear * - r29959 e29960 e29961 b29962 b29963 b29964 b29965 d29942 d29938
          omega
        have d29966 : (x 13 2 && x 13 13).toNat = 0 := by
          have r29967 := hand2 (x 13 2) (x 13 13)
          have b29968 := hb (x 13 13)
          have b29969 := hb (x 13 2 && x 13 13)
          clear * - r29967 b29968 b29969 d29958
          omega
        have d29970 : (x 13 3 && x 13 13).toNat = 0 := by
          have r29971 := hand2 (x 13 3) (x 13 13)
          have b29972 := hb (x 13 13)
          have b29973 := hb (x 13 3 && x 13 13)
          clear * - r29971 b29972 b29973 d29958
          omega
        have d29974 : (x 12 1 && x 12 14).toNat = 1 := by
          have r29975 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29976 := hb (x 11 2)
          have b29977 := hb (x 13 13)
          have b29978 := hb (x 12 1 && x 12 14)
          clear * - r29975 b29976 b29977 b29978 d29958 d29786
          omega
        have d29979 : (x 12 1).toNat = 1 := by
          have r29980 := hand1 (x 12 1) (x 12 14)
          have b29981 := hb (x 12 1)
          have b29982 := hb (x 12 1 && x 12 14)
          clear * - r29980 b29981 b29982 d29974
          omega
        have d29983 : (x 13 14).toNat = 0 := by
          have r29984 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29985 := hb (x 12 1)
          have b29986 := hb (x 13 14)
          clear * - r29984 b29985 b29986 d29979
          omega
        have d29987 : (x 13 1 && x 13 14).toNat = 0 := by
          have r29988 := hand2 (x 13 1) (x 13 14)
          have b29989 := hb (x 13 14)
          have b29990 := hb (x 13 1 && x 13 14)
          clear * - r29988 b29989 b29990 d29983
          omega
        have d29991 : (x 13 2).toNat = 0 := by
          have r29992 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
          have b29993 := hb (x 13 2)
          have b29994 := hb (x 13 14)
          clear * - r29992 b29993 b29994 d29983
          omega
        have d29995 : (x 12 2).toNat = 0 := by
          have r29996 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29997 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
          have e29998 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
          have b29999 := hb (x 11 3)
          have b30000 := hb (x 12 2)
          have b30001 := hb (x 13 13)
          have b30002 := hb (x 14 12)
          clear * - r29996 e29997 e29998 b29999 b30000 b30001 b30002 d29942 d29958 d29938
          omega
        have d30003 : (x 14 13).toNat = 1 := by
          have r30004 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b30005 := hb (x 12 2)
          have b30006 := hb (x 14 13)
          have b30007 := hb (x 13 1 && x 13 14)
          clear * - r30004 b30005 b30006 b30007 d29987 d29995
          omega
        have d30008 : (x 15 12).toNat = 0 := by
          have r30009 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30010 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
          have e30011 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
          have b30012 := hb (x 12 3)
          have b30013 := hb (x 13 2)
          have b30014 := hb (x 14 13)
          have b30015 := hb (x 15 12)
          clear * - r30009 e30010 e30011 b30012 b30013 b30014 b30015 d30003 d29991
          omega
        have d30016 : (x 12 3).toNat = 0 := by
          have r30017 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30018 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
          have e30019 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
          have b30020 := hb (x 12 3)
          have b30021 := hb (x 13 2)
          have b30022 := hb (x 14 13)
          have b30023 := hb (x 15 12)
          clear * - r30017 e30018 e30019 b30020 b30021 b30022 b30023 d30008 d30003 d29991
          omega
        have d30024 : (x 12 3 && x 12 14).toNat = 0 := by
          have r30025 := hand1 (x 12 3) (x 12 14)
          have b30026 := hb (x 12 3)
          have b30027 := hb (x 12 3 && x 12 14)
          clear * - r30025 b30026 b30027 d30016
          omega
        have d30028 : (x 15 11).toNat = 1 := by
          have r30029 : 1 ≤ (x 15 11).toNat + (x 14 1 && x 14 12).toNat + (x 13 2 && x 13 13).toNat + (x 12 3 && x 12 14).toNat + (x 11 4).toNat := by have q := hcov11 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b30030 := hb (x 11 4)
          have b30031 := hb (x 15 11)
          have b30032 := hb (x 14 1 && x 14 12)
          have b30033 := hb (x 13 2 && x 13 13)
          have b30034 := hb (x 12 3 && x 12 14)
          clear * - r30029 b30030 b30031 b30032 b30033 b30034 d29950 d29966 d30024 d29915
          omega
        have d30035 : (x 15 3).toNat = 1 := by
          have r30036 : (x 15 11).toNat ≤ (x 15 3).toNat := himp _ _ (hp11 15)
          have b30037 := hb (x 15 3)
          have b30038 := hb (x 15 11)
          clear * - r30036 b30037 b30038 d30028
          omega
        have d30039 : (x 18 12).toNat = 0 := by
          have r30040 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30041 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
          have e30042 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
          have b30043 := hb (x 15 3)
          have b30044 := hb (x 16 2)
          have b30045 := hb (x 17 13)
          have b30046 := hb (x 18 12)
          clear * - r30040 e30041 e30042 b30043 b30044 b30045 b30046 d30035
          omega
        have d30047 : (x 17 13).toNat = 0 := by
          have r30048 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30049 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
          have e30050 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
          have b30051 := hb (x 15 3)
          have b30052 := hb (x 16 2)
          have b30053 := hb (x 17 13)
          have b30054 := hb (x 18 12)
          clear * - r30048 e30049 e30050 b30051 b30052 b30053 b30054 d30039 d30035
          omega
        have d30055 : (x 16 1 && x 16 14).toNat = 1 := by
          have r30056 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := by have q := hcov13 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b30057 := hb (x 15 2)
          have b30058 := hb (x 17 13)
          have b30059 := hb (x 16 1 && x 16 14)
          clear * - r30056 b30057 b30058 b30059 d30047 d29899
          omega
        have d30060 : (x 16 14).toNat = 1 := by
          have r30061 := hand2 (x 16 1) (x 16 14)
          have b30062 := hb (x 16 14)
          have b30063 := hb (x 16 1 && x 16 14)
          clear * - r30061 b30062 b30063 d30055
          omega
        have d30064 : (x 15 1).toNat = 0 := by
          have r30065 : (x 16 14).toNat + (x 15 1).toNat = 1 := by have q := hd14 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b30066 := hb (x 15 1)
          have b30067 := hb (x 16 14)
          clear * - r30065 b30066 b30067 d30060
          omega
        have d30068 : (x 15 1 && x 15 11).toNat = 0 := by
          have r30069 := hand1 (x 15 1) (x 15 11)
          have b30070 := hb (x 15 1)
          have b30071 := hb (x 15 1 && x 15 11)
          clear * - r30069 b30070 b30071 d30064
          omega
        have d30072 : (x 16 2).toNat = 0 := by
          have r30073 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30074 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
          have e30075 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
          have b30076 := hb (x 15 3)
          have b30077 := hb (x 16 2)
          have b30078 := hb (x 17 13)
          have b30079 := hb (x 18 12)
          clear * - r30073 e30074 e30075 b30076 b30077 b30078 b30079 d30039 d30047 d30035
          omega
        have d30080 : (x 16 10).toNat = 0 := by
          have r30081 : (x 16 10).toNat ≤ (x 16 2).toNat := himp _ _ (hp10 16)
          have b30082 := hb (x 16 2)
          have b30083 := hb (x 16 10)
          clear * - r30081 b30082 b30083 d30072
          omega
        have r30084 : 1 ≤ (x 16 10).toNat + (x 15 1 && x 15 11).toNat + (x 14 2 && x 14 12).toNat + (x 13 3 && x 13 13).toNat + (x 12 4 && x 12 14).toNat + (x 11 5).toNat := by have q := hcov10 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b30085 := hb (x 11 5)
        have b30086 := hb (x 16 10)
        have b30087 := hb (x 15 1 && x 15 11)
        have b30088 := hb (x 14 2 && x 14 12)
        have b30089 := hb (x 13 3 && x 13 13)
        have b30090 := hb (x 12 4 && x 12 14)
        linarith only [r30084, b30085, b30086, b30087, b30088, b30089, b30090, d30080, d30068, d29954, d29970, d29852, d29864]
      · have f30091 : (x (-1) 4).toNat = 1 := by rw [h29524]; rfl
        have d30092 : (x (-1) 12).toNat = 1 := by
          have r30093 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
          have b30094 := hb (x (-1) 4)
          have b30095 := hb (x (-1) 12)
          clear * - r30093 b30094 b30095 f30091
          omega
        have d30096 : (x (-3) 2).toNat = 0 := by
          have r30097 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30098 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e30099 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b30100 := hb (x (-4) 3)
          have b30101 := hb (x (-3) 2)
          have b30102 := hb (x (-2) 13)
          have b30103 := hb (x (-1) 12)
          clear * - r30097 e30098 e30099 b30100 b30101 b30102 b30103 d30092 d28083
          omega
        have d30104 : (x (-3) 10).toNat = 0 := by
          have r30105 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
          have b30106 := hb (x (-3) 2)
          have b30107 := hb (x (-3) 10)
          clear * - r30105 b30106 b30107 d30096
          omega
        have d30108 : (x (-3) 3 && x (-3) 10).toNat = 0 := by
          have r30109 := hand2 (x (-3) 3) (x (-3) 10)
          have b30110 := hb (x (-3) 10)
          have b30111 := hb (x (-3) 3 && x (-3) 10)
          clear * - r30109 b30110 b30111 d30104
          omega
        have d30112 : (x (-1) 13).toNat = 1 := by
          have r30113 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b30114 := hb (x (-3) 2)
          have b30115 := hb (x (-1) 13)
          have b30116 := hb (x (-2) 1 && x (-2) 14)
          clear * - r30113 b30114 b30115 b30116 d28079 d30096
          omega
        have d30117 : (x (-2) 2).toNat = 0 := by
          have r30118 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30119 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
          have e30120 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
          have b30121 := hb (x (-3) 3)
          have b30122 := hb (x (-2) 2)
          have b30123 := hb (x (-1) 13)
          have b30124 := hb (x 0 12)
          clear * - r30118 e30119 e30120 b30121 b30122 b30123 b30124 g19 d30112
          omega
        have d30125 : (x (-2) 2 && x (-2) 8).toNat = 0 := by
          have r30126 := hand1 (x (-2) 2) (x (-2) 8)
          have b30127 := hb (x (-2) 2)
          have b30128 := hb (x (-2) 2 && x (-2) 8)
          clear * - r30126 b30127 b30128 d30117
          omega
        have d30129 : (x (-2) 2 && x (-2) 6).toNat = 0 := by
          have r30130 := hand1 (x (-2) 2) (x (-2) 6)
          have b30131 := hb (x (-2) 2)
          have b30132 := hb (x (-2) 2 && x (-2) 6)
          clear * - r30130 b30131 b30132 d30117
          omega
        have d30133 : (x (-3) 3).toNat = 0 := by
          have r30134 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30135 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
          have e30136 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
          have b30137 := hb (x (-3) 3)
          have b30138 := hb (x (-2) 2)
          have b30139 := hb (x (-1) 13)
          have b30140 := hb (x 0 12)
          clear * - r30134 e30135 e30136 b30137 b30138 b30139 b30140 g19 d30112 d30117
          omega
        have d30141 : (x (-3) 3 && x (-3) 12).toNat = 0 := by
          have r30142 := hand1 (x (-3) 3) (x (-3) 12)
          have b30143 := hb (x (-3) 3)
          have b30144 := hb (x (-3) 3 && x (-3) 12)
          clear * - r30142 b30143 b30144 d30133
          omega
        have d30145 : (x (-3) 3 && x (-3) 9).toNat = 0 := by
          have r30146 := hand1 (x (-3) 3) (x (-3) 9)
          have b30147 := hb (x (-3) 3)
          have b30148 := hb (x (-3) 3 && x (-3) 9)
          clear * - r30146 b30147 b30148 d30133
          omega
        have d30149 : (x (-3) 3 && x (-3) 7).toNat = 0 := by
          have r30150 := hand1 (x (-3) 3) (x (-3) 7)
          have b30151 := hb (x (-3) 3)
          have b30152 := hb (x (-3) 3 && x (-3) 7)
          clear * - r30150 b30151 b30152 d30133
          omega
        have d30153 : (x (-4) 3).toNat = 0 := by
          have r30154 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30155 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e30156 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b30157 := hb (x (-4) 3)
          have b30158 := hb (x (-3) 2)
          have b30159 := hb (x (-2) 13)
          have b30160 := hb (x (-1) 12)
          clear * - r30154 e30155 e30156 b30157 b30158 b30159 b30160 d30092 d28083 d30096
          omega
        have d30161 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
          have r30162 := hand1 (x (-4) 3) (x (-4) 12)
          have b30163 := hb (x (-4) 3)
          have b30164 := hb (x (-4) 3 && x (-4) 12)
          clear * - r30162 b30163 b30164 d30153
          omega
        have d30165 : (x (-4) 11).toNat = 0 := by
          have r30166 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
          have b30167 := hb (x (-4) 3)
          have b30168 := hb (x (-4) 11)
          clear * - r30166 b30167 b30168 d30153
          omega
        have d30169 : (x (-1) 1 && x (-1) 10).toNat = 1 := by
          have r30170 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b30171 := hb (x (-6) 6)
          have b30172 := hb (x 0 9)
          have b30173 := hb (x (-1) 1 && x (-1) 10)
          have b30174 := hb (x (-2) 2 && x (-2) 11)
          have b30175 := hb (x (-3) 3 && x (-3) 12)
          have b30176 := hb (x (-4) 4 && x (-4) 13)
          have b30177 := hb (x (-5) 5 && x (-5) 14)
          clear * - r30170 b30171 b30172 b30173 b30174 b30175 b30176 b30177 g16 d28195 d30141 g49 g50 g1
          omega
        have d30178 : (x (-1) 10).toNat = 1 := by
          have r30179 := hand2 (x (-1) 1) (x (-1) 10)
          have b30180 := hb (x (-1) 10)
          have b30181 := hb (x (-1) 1 && x (-1) 10)
          clear * - r30179 b30180 b30181 d30169
          omega
        have d30182 : (x 3 8).toNat = 0 := by
          have r30183 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30184 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e30185 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e30186 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e30187 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e30188 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e30189 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b30190 := hb (x (-4) 7)
          have b30191 := hb (x (-3) 6)
          have b30192 := hb (x (-2) 5)
          have b30193 := hb (x (-1) 4)
          have b30194 := hb (x 0 11)
          have b30195 := hb (x 1 10)
          have b30196 := hb (x 2 9)
          have b30197 := hb (x 3 8)
          clear * - r30183 e30184 e30185 e30186 e30187 e30188 e30189 b30190 b30191 b30192 b30193 b30194 b30195 b30196 b30197 d28151 g18 f30091 d28091
          omega
        have d30198 : (x 2 9).toNat = 0 := by
          have r30199 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30200 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e30201 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e30202 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e30203 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e30204 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e30205 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b30206 := hb (x (-4) 7)
          have b30207 := hb (x (-3) 6)
          have b30208 := hb (x (-2) 5)
          have b30209 := hb (x (-1) 4)
          have b30210 := hb (x 0 11)
          have b30211 := hb (x 1 10)
          have b30212 := hb (x 2 9)
          have b30213 := hb (x 3 8)
          clear * - r30199 e30200 e30201 e30202 e30203 e30204 e30205 b30206 b30207 b30208 b30209 b30210 b30211 b30212 b30213 d30182 d28151 g18 f30091 d28091
          omega
        have d30214 : (x 2 5 && x 2 9).toNat = 0 := by
          have r30215 := hand2 (x 2 5) (x 2 9)
          have b30216 := hb (x 2 9)
          have b30217 := hb (x 2 5 && x 2 9)
          clear * - r30215 b30216 b30217 d30198
          omega
        have d30218 : (x (-3) 6).toNat = 0 := by
          have r30219 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30220 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e30221 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e30222 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e30223 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e30224 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e30225 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b30226 := hb (x (-4) 7)
          have b30227 := hb (x (-3) 6)
          have b30228 := hb (x (-2) 5)
          have b30229 := hb (x (-1) 4)
          have b30230 := hb (x 0 11)
          have b30231 := hb (x 1 10)
          have b30232 := hb (x 2 9)
          have b30233 := hb (x 3 8)
          clear * - r30219 e30220 e30221 e30222 e30223 e30224 e30225 b30226 b30227 b30228 b30229 b30230 b30231 b30232 b30233 d30182 d30198 d28151 g18 f30091 d28091
          omega
        have d30234 : (x (-4) 7).toNat = 0 := by
          have r30235 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30236 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e30237 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e30238 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e30239 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e30240 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e30241 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b30242 := hb (x (-4) 7)
          have b30243 := hb (x (-3) 6)
          have b30244 := hb (x (-2) 5)
          have b30245 := hb (x (-1) 4)
          have b30246 := hb (x 0 11)
          have b30247 := hb (x 1 10)
          have b30248 := hb (x 2 9)
          have b30249 := hb (x 3 8)
          clear * - r30235 e30236 e30237 e30238 e30239 e30240 e30241 b30242 b30243 b30244 b30245 b30246 b30247 b30248 b30249 d30182 d30198 d28151 g18 f30091 d28091 d30218
          omega
        have d30250 : (x (-4) 7 && x (-4) 12).toNat = 0 := by
          have r30251 := hand1 (x (-4) 7) (x (-4) 12)
          have b30252 := hb (x (-4) 7)
          have b30253 := hb (x (-4) 7 && x (-4) 12)
          clear * - r30251 b30252 b30253 d30234
          omega
        have d30254 : (x 1 8).toNat = 0 := by
          have r30255 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30256 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e30257 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e30258 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e30259 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e30260 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e30261 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b30262 := hb (x (-6) 7)
          have b30263 := hb (x (-5) 6)
          have b30264 := hb (x (-4) 5)
          have b30265 := hb (x (-3) 4)
          have b30266 := hb (x (-2) 11)
          have b30267 := hb (x (-1) 10)
          have b30268 := hb (x 0 9)
          have b30269 := hb (x 1 8)
          clear * - r30255 e30256 e30257 e30258 e30259 e30260 e30261 b30262 b30263 b30264 b30265 b30266 b30267 b30268 b30269 g16 d30178 d28191
          omega
        have d30270 : (x (-3) 4).toNat = 0 := by
          have r30271 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30272 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e30273 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e30274 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e30275 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e30276 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e30277 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b30278 := hb (x (-6) 7)
          have b30279 := hb (x (-5) 6)
          have b30280 := hb (x (-4) 5)
          have b30281 := hb (x (-3) 4)
          have b30282 := hb (x (-2) 11)
          have b30283 := hb (x (-1) 10)
          have b30284 := hb (x 0 9)
          have b30285 := hb (x 1 8)
          clear * - r30271 e30272 e30273 e30274 e30275 e30276 e30277 b30278 b30279 b30280 b30281 b30282 b30283 b30284 b30285 d30254 g16 d30178 d28191
          omega
        have d30286 : (x (-4) 5).toNat = 0 := by
          have r30287 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30288 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e30289 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e30290 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e30291 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e30292 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e30293 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b30294 := hb (x (-6) 7)
          have b30295 := hb (x (-5) 6)
          have b30296 := hb (x (-4) 5)
          have b30297 := hb (x (-3) 4)
          have b30298 := hb (x (-2) 11)
          have b30299 := hb (x (-1) 10)
          have b30300 := hb (x 0 9)
          have b30301 := hb (x 1 8)
          clear * - r30287 e30288 e30289 e30290 e30291 e30292 e30293 b30294 b30295 b30296 b30297 b30298 b30299 b30300 b30301 d30254 g16 d30178 d28191 d30270
          omega
        have d30302 : (x (-4) 5 && x (-4) 12).toNat = 0 := by
          have r30303 := hand1 (x (-4) 5) (x (-4) 12)
          have b30304 := hb (x (-4) 5)
          have b30305 := hb (x (-4) 5 && x (-4) 12)
          clear * - r30303 b30304 b30305 d30286
          omega
        have d30306 : (x (-5) 6).toNat = 0 := by
          have r30307 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30308 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e30309 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e30310 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e30311 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e30312 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e30313 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b30314 := hb (x (-6) 7)
          have b30315 := hb (x (-5) 6)
          have b30316 := hb (x (-4) 5)
          have b30317 := hb (x (-3) 4)
          have b30318 := hb (x (-2) 11)
          have b30319 := hb (x (-1) 10)
          have b30320 := hb (x 0 9)
          have b30321 := hb (x 1 8)
          clear * - r30307 e30308 e30309 e30310 e30311 e30312 e30313 b30314 b30315 b30316 b30317 b30318 b30319 b30320 b30321 d30254 g16 d30178 d28191 d30270 d30286
          omega
        have d30322 : (x (-5) 6 && x (-5) 13).toNat = 0 := by
          have r30323 := hand1 (x (-5) 6) (x (-5) 13)
          have b30324 := hb (x (-5) 6)
          have b30325 := hb (x (-5) 6 && x (-5) 13)
          clear * - r30323 b30324 b30325 d30306
          omega
        have d30326 : (x (-6) 7).toNat = 0 := by
          have r30327 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30328 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e30329 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e30330 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e30331 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e30332 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e30333 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b30334 := hb (x (-6) 7)
          have b30335 := hb (x (-5) 6)
          have b30336 := hb (x (-4) 5)
          have b30337 := hb (x (-3) 4)
          have b30338 := hb (x (-2) 11)
          have b30339 := hb (x (-1) 10)
          have b30340 := hb (x 0 9)
          have b30341 := hb (x 1 8)
          clear * - r30327 e30328 e30329 e30330 e30331 e30332 e30333 b30334 b30335 b30336 b30337 b30338 b30339 b30340 b30341 d30254 g16 d30178 d28191 d30270 d30286 d30306
          omega
        have d30342 : (x (-6) 7 && x (-6) 14).toNat = 0 := by
          have r30343 := hand1 (x (-6) 7) (x (-6) 14)
          have b30344 := hb (x (-6) 7)
          have b30345 := hb (x (-6) 7 && x (-6) 14)
          clear * - r30343 b30344 b30345 d30326
          omega
        cases h30346 : x (-1) 5
        · have f30347 : (x (-1) 5).toNat = 0 := by rw [h30346]; rfl
          have r30348 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r30349 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30350 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
          have e30351 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
          have e30352 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
          have e30353 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
          have e30354 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
          have e30355 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
          have r30356 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30357 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
          have e30358 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
          have e30359 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
          have e30360 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
          have e30361 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
          have e30362 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
          have r30363 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30364 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
          have e30365 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
          have e30366 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
          have e30367 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
          have e30368 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
          have e30369 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
          have r30370 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30371 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
          have e30372 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
          have e30373 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
          have e30374 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
          have e30375 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
          have e30376 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
          have r30377 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30378 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
          have e30379 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
          have e30380 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
          have e30381 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
          have e30382 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
          have e30383 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
          have r30384 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30385 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
          have e30386 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
          have r30387 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30388 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
          have e30389 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
          have r30390 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r30391 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r30392 : 1 ≤ (x 0 4).toNat + (x (-1) 1 && x (-1) 5).toNat + (x (-2) 2 && x (-2) 6).toNat + (x (-3) 3 && x (-3) 7).toNat + (x (-4) 4 && x (-4) 8).toNat + (x (-5) 5 && x (-5) 9).toNat + (x (-6) 6 && x (-6) 10).toNat + (x (-7) 7 && x (-7) 11).toNat + (x (-8) 8 && x (-8) 12).toNat + (x (-9) 9 && x (-9) 13).toNat + (x (-10) 10 && x (-10) 14).toNat + (x (-11) 11).toNat := by have q := hcov4 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30393 : (x (-1) 1 && x (-1) 5).toNat = (x (-1) 5).toNat := handr _ _ (fun h => hp13 (-1) (hp5 (-1) (h)))
          have e30394 : (x (-10) 10 && x (-10) 14).toNat = (x (-10) 10).toNat := handl _ _ (fun h => hp2 (-10) (hp10 (-10) (h)))
          have r30395 : 1 ≤ (x 7 4).toNat + (x 6 1 && x 6 5).toNat + (x 5 2 && x 5 6).toNat + (x 4 3 && x 4 7).toNat + (x 3 4 && x 3 8).toNat + (x 2 5 && x 2 9).toNat + (x 1 6 && x 1 10).toNat + (x 0 7 && x 0 11).toNat + (x (-1) 8 && x (-1) 12).toNat + (x (-2) 9 && x (-2) 13).toNat + (x (-3) 10 && x (-3) 14).toNat + (x (-4) 11).toNat := by have q := hcov4 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30396 : (x 6 1 && x 6 5).toNat = (x 6 5).toNat := handr _ _ (fun h => hp13 6 (hp5 6 (h)))
          have e30397 : (x (-3) 10 && x (-3) 14).toNat = (x (-3) 10).toNat := handl _ _ (fun h => hp2 (-3) (hp10 (-3) (h)))
          have r30398 : 1 ≤ (x 0 6).toNat + (x (-1) 1 && x (-1) 7).toNat + (x (-2) 2 && x (-2) 8).toNat + (x (-3) 3 && x (-3) 9).toNat + (x (-4) 4 && x (-4) 10).toNat + (x (-5) 5 && x (-5) 11).toNat + (x (-6) 6 && x (-6) 12).toNat + (x (-7) 7 && x (-7) 13).toNat + (x (-8) 8 && x (-8) 14).toNat + (x (-9) 9).toNat := by have q := hcov6 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r30399 : 1 ≤ (x 0 7).toNat + (x (-1) 1 && x (-1) 8).toNat + (x (-2) 2 && x (-2) 9).toNat + (x (-3) 3 && x (-3) 10).toNat + (x (-4) 4 && x (-4) 11).toNat + (x (-5) 5 && x (-5) 12).toNat + (x (-6) 6 && x (-6) 13).toNat + (x (-7) 7 && x (-7) 14).toNat + (x (-8) 8).toNat := by have q := hcov7 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r30400 : 1 ≤ (x 1 7).toNat + (x 0 1 && x 0 8).toNat + (x (-1) 2 && x (-1) 9).toNat + (x (-2) 3 && x (-2) 10).toNat + (x (-3) 4 && x (-3) 11).toNat + (x (-4) 5 && x (-4) 12).toNat + (x (-5) 6 && x (-5) 13).toNat + (x (-6) 7 && x (-6) 14).toNat + (x (-7) 8).toNat := by have q := hcov7 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r30401 : 1 ≤ (x (-8) 9).toNat + (x (-9) 1 && x (-9) 10).toNat + (x (-10) 2 && x (-10) 11).toNat + (x (-11) 3 && x (-11) 12).toNat + (x (-12) 4 && x (-12) 13).toNat + (x (-13) 5 && x (-13) 14).toNat + (x (-14) 6).toNat := by have q := hcov9 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r30402 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r30403 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r30404 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r30405 : 1 ≤ (x (-8) 13).toNat + (x (-9) 1 && x (-9) 14).toNat + (x (-10) 2).toNat := by have q := hcov13 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r30406 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r30407 : (x (-8) 13).toNat ≤ (x (-8) 1).toNat := himp _ _ (hp13 (-8))
          have r30408 : (x (-7) 6).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp6 (-7))
          have r30409 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
          have r30410 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
          have r30411 := hand2 (x (-8) 8) (x (-8) 12)
          have r30412 := hand2 (x (-9) 9) (x (-9) 13)
          have r30413 := hand2 (x 5 2) (x 5 6)
          have r30414 := hand2 (x 4 3) (x 4 7)
          have r30415 := hand1 (x (-1) 8) (x (-1) 12)
          have r30416 := hand2 (x (-1) 1) (x (-1) 7)
          have r30417 := hand2 (x (-8) 8) (x (-8) 14)
          have r30418 := hand2 (x (-1) 1) (x (-1) 8)
          have r30419 := hand2 (x (-9) 1) (x (-9) 10)
          have r30420 := hand2 (x (-10) 2) (x (-10) 11)
          have r30421 := hand1 (x (-11) 3) (x (-11) 12)
          have r30422 := hand1 (x (-12) 4) (x (-12) 13)
          have r30423 := hand1 (x (-13) 5) (x (-13) 14)
          have r30424 := hand1 (x (-5) 4) (x (-5) 13)
          have r30425 := hand1 (x (-6) 5) (x (-6) 14)
          have r30426 := hand2 (x 3 1) (x 3 11)
          have r30427 := hand1 (x 7 1) (x 7 12)
          have r30428 := hand1 (x 6 2) (x 6 13)
          have r30429 := hand1 (x 5 3) (x 5 14)
          have r30430 := hand1 (x (-9) 1) (x (-9) 14)
          have r30431 := hand2 (x (-6) 1) (x (-6) 14)
          linarith only [r30348, r30349, e30350, e30351, e30352, e30353, e30354, e30355, r30356, e30357, e30358, e30359, e30360, e30361, e30362, r30363, e30364, e30365, e30366, e30367, e30368, e30369, r30370, e30371, e30372, e30373, e30374, e30375, e30376, r30377, e30378, e30379, e30380, e30381, e30382, e30383, r30384, e30385, e30386, r30387, e30388, e30389, r30390, r30391, r30392, e30393, e30394, r30395, e30396, e30397, r30398, r30399, r30400, r30401, r30402, r30403, r30404, r30405, r30406, r30407, r30408, r30409, r30410, r30411, r30412, r30413, r30414, r30415, r30416, r30417, r30418, r30419, r30420, r30421, r30422, r30423, r30424, r30425, r30426, r30427, r30428, r30429, r30430, r30431, d30165, d30104, g4, d28095, g5, f30347, g7, g11, g13, g14, g15, d28013, d29502, d30129, d30149, g23, g24, g25, g26, d28131, d30214, d28155, g27, d28087, d30125, d30145, g34, g35, g36, g37, d28099, d30108, g38, g39, g40, g41, g42, g43, g44, g45, d30302, d30322, d30342, g47, g48, d30161, d29498, d27993, g56]
        · have f30559 : (x (-1) 5).toNat = 1 := by rw [h30346]; rfl
          have d30560 : (x 4 8).toNat = 0 := by
            have r30561 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e30562 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
            have e30563 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
            have e30564 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
            have e30565 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
            have e30566 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
            have e30567 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
            have b30568 := hb (x (-3) 7)
            have b30569 := hb (x (-2) 6)
            have b30570 := hb (x (-1) 5)
            have b30571 := hb (x 0 4)
            have b30572 := hb (x 1 11)
            have b30573 := hb (x 2 10)
            have b30574 := hb (x 3 9)
            have b30575 := hb (x 4 8)
            clear * - r30561 e30562 e30563 e30564 e30565 e30566 e30567 b30568 b30569 b30570 b30571 b30572 b30573 b30574 b30575 d29516 g11 f30559
            omega
          have d30576 : (x 4 8 && x 4 11).toNat = 0 := by
            have r30577 := hand1 (x 4 8) (x 4 11)
            have b30578 := hb (x 4 8)
            have b30579 := hb (x 4 8 && x 4 11)
            clear * - r30577 b30578 b30579 d30560
            omega
          have d30580 : (x 3 9).toNat = 0 := by
            have r30581 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e30582 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
            have e30583 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
            have e30584 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
            have e30585 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
            have e30586 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
            have e30587 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
            have b30588 := hb (x (-3) 7)
            have b30589 := hb (x (-2) 6)
            have b30590 := hb (x (-1) 5)
            have b30591 := hb (x 0 4)
            have b30592 := hb (x 1 11)
            have b30593 := hb (x 2 10)
            have b30594 := hb (x 3 9)
            have b30595 := hb (x 4 8)
            clear * - r30581 e30582 e30583 e30584 e30585 e30586 e30587 b30588 b30589 b30590 b30591 b30592 b30593 b30594 b30595 d30560 d29516 g11 f30559
            omega
          have d30596 : (x 2 10).toNat = 0 := by
            have r30597 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e30598 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
            have e30599 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
            have e30600 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
            have e30601 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
            have e30602 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
            have e30603 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
            have b30604 := hb (x (-3) 7)
            have b30605 := hb (x (-2) 6)
            have b30606 := hb (x (-1) 5)
            have b30607 := hb (x 0 4)
            have b30608 := hb (x 1 11)
            have b30609 := hb (x 2 10)
            have b30610 := hb (x 3 9)
            have b30611 := hb (x 4 8)
            clear * - r30597 e30598 e30599 e30600 e30601 e30602 e30603 b30604 b30605 b30606 b30607 b30608 b30609 b30610 b30611 d30560 d30580 d29516 g11 f30559
            omega
          have d30612 : (x 2 10 && x 2 13).toNat = 0 := by
            have r30613 := hand1 (x 2 10) (x 2 13)
            have b30614 := hb (x 2 10)
            have b30615 := hb (x 2 10 && x 2 13)
            clear * - r30613 b30614 b30615 d30596
            omega
          have r30616 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r30617 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r30618 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30619 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
          have e30620 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
          have e30621 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
          have e30622 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
          have e30623 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
          have e30624 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
          have r30625 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30626 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
          have e30627 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
          have e30628 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
          have e30629 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
          have e30630 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
          have e30631 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
          have r30632 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30633 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e30634 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e30635 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e30636 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e30637 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e30638 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have r30639 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e30640 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e30641 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have r30642 : 1 ≤ (x 12 3).toNat + (x 11 1 && x 11 4).toNat + (x 10 2 && x 10 5).toNat + (x 9 3 && x 9 6).toNat + (x 8 4 && x 8 7).toNat + (x 7 5 && x 7 8).toNat + (x 6 6 && x 6 9).toNat + (x 5 7 && x 5 10).toNat + (x 4 8 && x 4 11).toNat + (x 3 9 && x 3 12).toNat + (x 2 10 && x 2 13).toNat + (x 1 11 && x 1 14).toNat + (x 0 12).toNat := by have q := hcov3 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r30643 : 1 ≤ (x 3 5).toNat + (x 2 1 && x 2 6).toNat + (x 1 2 && x 1 7).toNat + (x 0 3 && x 0 8).toNat + (x (-1) 4 && x (-1) 9).toNat + (x (-2) 5 && x (-2) 10).toNat + (x (-3) 6 && x (-3) 11).toNat + (x (-4) 7 && x (-4) 12).toNat + (x (-5) 8 && x (-5) 13).toNat + (x (-6) 9 && x (-6) 14).toNat + (x (-7) 10).toNat := by have q := hcov5 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r30644 : 1 ≤ (x 0 7).toNat + (x (-1) 1 && x (-1) 8).toNat + (x (-2) 2 && x (-2) 9).toNat + (x (-3) 3 && x (-3) 10).toNat + (x (-4) 4 && x (-4) 11).toNat + (x (-5) 5 && x (-5) 12).toNat + (x (-6) 6 && x (-6) 13).toNat + (x (-7) 7 && x (-7) 14).toNat + (x (-8) 8).toNat := by have q := hcov7 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r30645 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r30646 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r30647 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := by have q := hcov11 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r30648 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r30649 := hand2 (x 11 1) (x 11 4)
          have r30650 := hand2 (x 10 2) (x 10 5)
          have r30651 := hand2 (x 9 3) (x 9 6)
          have r30652 := hand2 (x 8 4) (x 8 7)
          have r30653 := hand2 (x 7 5) (x 7 8)
          have r30654 := hand2 (x 6 6) (x 6 9)
          have r30655 := hand2 (x 5 7) (x 5 10)
          have r30656 := hand2 (x 2 1) (x 2 6)
          have r30657 := hand1 (x (-5) 8) (x (-5) 13)
          have r30658 := hand1 (x (-6) 9) (x (-6) 14)
          have r30659 := hand2 (x (-1) 1) (x (-1) 8)
          have r30660 := hand1 (x (-5) 4) (x (-5) 13)
          have r30661 := hand1 (x (-6) 5) (x (-6) 14)
          have r30662 := hand2 (x 5 1) (x 5 11)
          have r30663 := hand2 (x 4 2) (x 4 12)
          have r30664 := hand2 (x 3 3) (x 3 13)
          have r30665 := hand2 (x (-9) 1) (x (-9) 12)
          have r30666 := hand2 (x (-10) 2) (x (-10) 13)
          have r30667 := hand2 (x (-11) 3) (x (-11) 14)
          have r30668 := hand1 (x 2 2) (x 2 13)
          linarith only [r30616, r30617, r30618, e30619, e30620, e30621, e30622, e30623, e30624, r30625, e30626, e30627, e30628, e30629, e30630, e30631, r30632, e30633, e30634, e30635, e30636, e30637, e30638, r30639, e30640, e30641, r30642, r30643, r30644, r30645, r30646, r30647, r30648, r30649, r30650, r30651, r30652, r30653, r30654, r30655, r30656, r30657, r30658, r30659, r30660, r30661, r30662, r30663, r30664, r30665, r30666, r30667, r30668, d30234, d30165, d30218, d30104, d28091, d28095, f30091, g7, g10, g11, g14, g19, d28135, f29511, d28013, g22, d28026, d28021, d28103, d30576, d28119, d30612, d29520, d28147, g29, g30, g31, g32, d30250, d28099, d30108, g38, g39, g40, g41, g47, g48, d30161, d29506, d28111, d29512]
    · have f30772 : (x 1 3).toNat = 1 := by rw [h29510]; rfl
      have d30773 : (x 4 12).toNat = 0 := by
        have r30774 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30775 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e30776 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b30777 := hb (x 1 3)
        have b30778 := hb (x 2 2)
        have b30779 := hb (x 3 13)
        have b30780 := hb (x 4 12)
        clear * - r30774 e30775 e30776 b30777 b30778 b30779 b30780 f30772
        omega
      have d30781 : (x 4 1 && x 4 12).toNat = 0 := by
        have r30782 := hand2 (x 4 1) (x 4 12)
        have b30783 := hb (x 4 12)
        have b30784 := hb (x 4 1 && x 4 12)
        clear * - r30782 b30783 b30784 d30773
        omega
      have d30785 : (x 4 4).toNat = 0 := by
        have r30786 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
        have b30787 := hb (x 4 4)
        have b30788 := hb (x 4 12)
        clear * - r30786 b30787 b30788 d30773
        omega
      have d30789 : (x 3 13).toNat = 0 := by
        have r30790 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30791 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e30792 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b30793 := hb (x 1 3)
        have b30794 := hb (x 2 2)
        have b30795 := hb (x 3 13)
        have b30796 := hb (x 4 12)
        clear * - r30790 e30791 e30792 b30793 b30794 b30795 b30796 d30773 f30772
        omega
      have d30797 : (x 2 2).toNat = 0 := by
        have r30798 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30799 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e30800 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b30801 := hb (x 1 3)
        have b30802 := hb (x 2 2)
        have b30803 := hb (x 3 13)
        have b30804 := hb (x 4 12)
        clear * - r30798 e30799 e30800 b30801 b30802 b30803 b30804 d30773 d30789 f30772
        omega
      have d30805 : (x 4 13).toNat = 1 := by
        have r30806 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b30807 := hb (x 2 2)
        have b30808 := hb (x 4 13)
        have b30809 := hb (x 3 1 && x 3 14)
        clear * - r30806 b30807 b30808 b30809 d28034 d30797
        omega
      have d30810 : (x 4 1).toNat = 1 := by
        have r30811 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
        have b30812 := hb (x 4 1)
        have b30813 := hb (x 4 13)
        clear * - r30811 b30812 b30813 d30805
        omega
      have d30814 : (x 5 14).toNat = 0 := by
        have r30815 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b30816 := hb (x 4 1)
        have b30817 := hb (x 5 14)
        clear * - r30815 b30816 b30817 d30810
        omega
      have d30818 : (x 5 3 && x 5 14).toNat = 0 := by
        have r30819 := hand2 (x 5 3) (x 5 14)
        have b30820 := hb (x 5 14)
        have b30821 := hb (x 5 3 && x 5 14)
        clear * - r30819 b30820 b30821 d30814
        omega
      have d30822 : (x 5 2).toNat = 0 := by
        have r30823 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
        have b30824 := hb (x 5 2)
        have b30825 := hb (x 5 14)
        clear * - r30823 b30824 b30825 d30814
        omega
      have d30826 : (x 5 12).toNat = 0 := by
        have r30827 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30828 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e30829 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b30830 := hb (x 2 3)
        have b30831 := hb (x 3 2)
        have b30832 := hb (x 4 13)
        have b30833 := hb (x 5 12)
        clear * - r30827 e30828 e30829 b30830 b30831 b30832 b30833 d30805 d28050
        omega
      have d30834 : (x 5 4).toNat = 0 := by
        have r30835 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
        have b30836 := hb (x 5 4)
        have b30837 := hb (x 5 12)
        clear * - r30835 b30836 b30837 d30826
        omega
      have d30838 : (x 2 3).toNat = 0 := by
        have r30839 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30840 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e30841 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b30842 := hb (x 2 3)
        have b30843 := hb (x 3 2)
        have b30844 := hb (x 4 13)
        have b30845 := hb (x 5 12)
        clear * - r30839 e30840 e30841 b30842 b30843 b30844 b30845 d30826 d30805 d28050
        omega
      have d30846 : (x 2 3 && x 2 14).toNat = 0 := by
        have r30847 := hand1 (x 2 3) (x 2 14)
        have b30848 := hb (x 2 3)
        have b30849 := hb (x 2 3 && x 2 14)
        clear * - r30847 b30848 b30849 d30838
        omega
      have d30850 : (x 5 11).toNat = 1 := by
        have r30851 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b30852 := hb (x 1 4)
        have b30853 := hb (x 5 11)
        have b30854 := hb (x 4 1 && x 4 12)
        have b30855 := hb (x 3 2 && x 3 13)
        have b30856 := hb (x 2 3 && x 2 14)
        clear * - r30851 b30852 b30853 b30854 b30855 b30856 d30781 d28054 d30846 d28167
        omega
      have d30857 : (x 5 3).toNat = 1 := by
        have r30858 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
        have b30859 := hb (x 5 3)
        have b30860 := hb (x 5 11)
        clear * - r30858 b30859 b30860 d30850
        omega
      have d30861 : (x 8 12).toNat = 0 := by
        have r30862 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30863 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e30864 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have b30865 := hb (x 5 3)
        have b30866 := hb (x 6 2)
        have b30867 := hb (x 7 13)
        have b30868 := hb (x 8 12)
        clear * - r30862 e30863 e30864 b30865 b30866 b30867 b30868 d30857
        omega
      have d30869 : (x 8 1 && x 8 12).toNat = 0 := by
        have r30870 := hand2 (x 8 1) (x 8 12)
        have b30871 := hb (x 8 12)
        have b30872 := hb (x 8 1 && x 8 12)
        clear * - r30870 b30871 b30872 d30861
        omega
      have d30873 : (x 8 4).toNat = 0 := by
        have r30874 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
        have b30875 := hb (x 8 4)
        have b30876 := hb (x 8 12)
        clear * - r30874 b30875 b30876 d30861
        omega
      have d30877 : (x 7 13).toNat = 0 := by
        have r30878 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30879 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e30880 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have b30881 := hb (x 5 3)
        have b30882 := hb (x 6 2)
        have b30883 := hb (x 7 13)
        have b30884 := hb (x 8 12)
        clear * - r30878 e30879 e30880 b30881 b30882 b30883 b30884 d30861 d30857
        omega
      have d30885 : (x 7 2 && x 7 13).toNat = 0 := by
        have r30886 := hand2 (x 7 2) (x 7 13)
        have b30887 := hb (x 7 13)
        have b30888 := hb (x 7 2 && x 7 13)
        clear * - r30886 b30887 b30888 d30877
        omega
      have d30889 : (x 6 1 && x 6 14).toNat = 1 := by
        have r30890 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b30891 := hb (x 5 2)
        have b30892 := hb (x 7 13)
        have b30893 := hb (x 6 1 && x 6 14)
        clear * - r30890 b30891 b30892 b30893 d30877 d30822
        omega
      have d30894 : (x 6 1).toNat = 1 := by
        have r30895 := hand1 (x 6 1) (x 6 14)
        have b30896 := hb (x 6 1)
        have b30897 := hb (x 6 1 && x 6 14)
        clear * - r30895 b30896 b30897 d30889
        omega
      have d30898 : (x 7 14).toNat = 0 := by
        have r30899 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b30900 := hb (x 6 1)
        have b30901 := hb (x 7 14)
        clear * - r30899 b30900 b30901 d30894
        omega
      have d30902 : (x 7 1 && x 7 14).toNat = 0 := by
        have r30903 := hand2 (x 7 1) (x 7 14)
        have b30904 := hb (x 7 14)
        have b30905 := hb (x 7 1 && x 7 14)
        clear * - r30903 b30904 b30905 d30898
        omega
      have d30906 : (x 7 2).toNat = 0 := by
        have r30907 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
        have b30908 := hb (x 7 2)
        have b30909 := hb (x 7 14)
        clear * - r30907 b30908 b30909 d30898
        omega
      have d30910 : (x 6 2).toNat = 0 := by
        have r30911 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30912 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e30913 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have b30914 := hb (x 5 3)
        have b30915 := hb (x 6 2)
        have b30916 := hb (x 7 13)
        have b30917 := hb (x 8 12)
        clear * - r30911 e30912 e30913 b30914 b30915 b30916 b30917 d30861 d30877 d30857
        omega
      have d30918 : (x 6 2 && x 6 13).toNat = 0 := by
        have r30919 := hand1 (x 6 2) (x 6 13)
        have b30920 := hb (x 6 2)
        have b30921 := hb (x 6 2 && x 6 13)
        clear * - r30919 b30920 b30921 d30910
        omega
      have d30922 : (x 8 13).toNat = 1 := by
        have r30923 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b30924 := hb (x 6 2)
        have b30925 := hb (x 8 13)
        have b30926 := hb (x 7 1 && x 7 14)
        clear * - r30923 b30924 b30925 b30926 d30902 d30910
        omega
      have d30927 : (x 8 1).toNat = 1 := by
        have r30928 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
        have b30929 := hb (x 8 1)
        have b30930 := hb (x 8 13)
        clear * - r30928 b30929 b30930 d30922
        omega
      have d30931 : (x 9 14).toNat = 0 := by
        have r30932 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b30933 := hb (x 8 1)
        have b30934 := hb (x 9 14)
        clear * - r30932 b30933 b30934 d30927
        omega
      have d30935 : (x 9 3 && x 9 14).toNat = 0 := by
        have r30936 := hand2 (x 9 3) (x 9 14)
        have b30937 := hb (x 9 14)
        have b30938 := hb (x 9 3 && x 9 14)
        clear * - r30936 b30937 b30938 d30931
        omega
      have d30939 : (x 9 2).toNat = 0 := by
        have r30940 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
        have b30941 := hb (x 9 2)
        have b30942 := hb (x 9 14)
        clear * - r30940 b30941 b30942 d30931
        omega
      have d30943 : (x 9 12).toNat = 0 := by
        have r30944 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30945 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
        have e30946 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
        have b30947 := hb (x 6 3)
        have b30948 := hb (x 7 2)
        have b30949 := hb (x 8 13)
        have b30950 := hb (x 9 12)
        clear * - r30944 e30945 e30946 b30947 b30948 b30949 b30950 d30922 d30906
        omega
      have d30951 : (x 9 4).toNat = 0 := by
        have r30952 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
        have b30953 := hb (x 9 4)
        have b30954 := hb (x 9 12)
        clear * - r30952 b30953 b30954 d30943
        omega
      have d30955 : (x 6 3).toNat = 0 := by
        have r30956 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30957 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
        have e30958 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
        have b30959 := hb (x 6 3)
        have b30960 := hb (x 7 2)
        have b30961 := hb (x 8 13)
        have b30962 := hb (x 9 12)
        clear * - r30956 e30957 e30958 b30959 b30960 b30961 b30962 d30943 d30922 d30906
        omega
      have d30963 : (x 6 3 && x 6 14).toNat = 0 := by
        have r30964 := hand1 (x 6 3) (x 6 14)
        have b30965 := hb (x 6 3)
        have b30966 := hb (x 6 3 && x 6 14)
        clear * - r30964 b30965 b30966 d30955
        omega
      have d30967 : (x 9 11).toNat = 1 := by
        have r30968 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b30969 := hb (x 5 4)
        have b30970 := hb (x 9 11)
        have b30971 := hb (x 8 1 && x 8 12)
        have b30972 := hb (x 7 2 && x 7 13)
        have b30973 := hb (x 6 3 && x 6 14)
        clear * - r30968 b30969 b30970 b30971 b30972 b30973 d30869 d30885 d30963 d30834
        omega
      have d30974 : (x 9 3).toNat = 1 := by
        have r30975 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
        have b30976 := hb (x 9 3)
        have b30977 := hb (x 9 11)
        clear * - r30975 b30976 b30977 d30967
        omega
      have d30978 : (x 12 12).toNat = 0 := by
        have r30979 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30980 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
        have e30981 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
        have b30982 := hb (x 9 3)
        have b30983 := hb (x 10 2)
        have b30984 := hb (x 11 13)
        have b30985 := hb (x 12 12)
        clear * - r30979 e30980 e30981 b30982 b30983 b30984 b30985 d30974
        omega
      have d30986 : (x 12 1 && x 12 12).toNat = 0 := by
        have r30987 := hand2 (x 12 1) (x 12 12)
        have b30988 := hb (x 12 12)
        have b30989 := hb (x 12 1 && x 12 12)
        clear * - r30987 b30988 b30989 d30978
        omega
      have d30990 : (x 12 4).toNat = 0 := by
        have r30991 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
        have b30992 := hb (x 12 4)
        have b30993 := hb (x 12 12)
        clear * - r30991 b30992 b30993 d30978
        omega
      have d30994 : (x 11 13).toNat = 0 := by
        have r30995 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e30996 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
        have e30997 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
        have b30998 := hb (x 9 3)
        have b30999 := hb (x 10 2)
        have b31000 := hb (x 11 13)
        have b31001 := hb (x 12 12)
        clear * - r30995 e30996 e30997 b30998 b30999 b31000 b31001 d30978 d30974
        omega
      have d31002 : (x 11 2 && x 11 13).toNat = 0 := by
        have r31003 := hand2 (x 11 2) (x 11 13)
        have b31004 := hb (x 11 13)
        have b31005 := hb (x 11 2 && x 11 13)
        clear * - r31003 b31004 b31005 d30994
        omega
      have d31006 : (x 10 1 && x 10 14).toNat = 1 := by
        have r31007 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31008 := hb (x 9 2)
        have b31009 := hb (x 11 13)
        have b31010 := hb (x 10 1 && x 10 14)
        clear * - r31007 b31008 b31009 b31010 d30994 d30939
        omega
      have d31011 : (x 10 14).toNat = 1 := by
        have r31012 := hand2 (x 10 1) (x 10 14)
        have b31013 := hb (x 10 14)
        have b31014 := hb (x 10 1 && x 10 14)
        clear * - r31012 b31013 b31014 d31006
        omega
      have d31015 : (x 9 1).toNat = 0 := by
        have r31016 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31017 := hb (x 9 1)
        have b31018 := hb (x 10 14)
        clear * - r31016 b31017 b31018 d31011
        omega
      have d31019 : (x 9 13).toNat = 0 := by
        have r31020 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
        have b31021 := hb (x 9 1)
        have b31022 := hb (x 9 13)
        clear * - r31020 b31021 b31022 d31015
        omega
      have d31023 : (x 8 1 && x 8 14).toNat = 1 := by
        have r31024 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31025 := hb (x 7 2)
        have b31026 := hb (x 9 13)
        have b31027 := hb (x 8 1 && x 8 14)
        clear * - r31024 b31025 b31026 b31027 d31019 d30906
        omega
      have d31028 : (x 8 14).toNat = 1 := by
        have r31029 := hand2 (x 8 1) (x 8 14)
        have b31030 := hb (x 8 14)
        have b31031 := hb (x 8 1 && x 8 14)
        clear * - r31029 b31030 b31031 d31023
        omega
      have d31032 : (x 7 1).toNat = 0 := by
        have r31033 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31034 := hb (x 7 1)
        have b31035 := hb (x 8 14)
        clear * - r31033 b31034 b31035 d31028
        omega
      have d31036 : (x 7 1 && x 7 12).toNat = 0 := by
        have r31037 := hand1 (x 7 1) (x 7 12)
        have b31038 := hb (x 7 1)
        have b31039 := hb (x 7 1 && x 7 12)
        clear * - r31037 b31038 b31039 d31032
        omega
      have d31040 : (x 8 11).toNat = 1 := by
        have r31041 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31042 := hb (x 4 4)
        have b31043 := hb (x 8 11)
        have b31044 := hb (x 7 1 && x 7 12)
        have b31045 := hb (x 6 2 && x 6 13)
        have b31046 := hb (x 5 3 && x 5 14)
        clear * - r31041 b31042 b31043 b31044 b31045 b31046 d31036 d30918 d30818 d30785
        omega
      have d31047 : (x 8 3).toNat = 1 := by
        have r31048 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
        have b31049 := hb (x 8 3)
        have b31050 := hb (x 8 11)
        clear * - r31048 b31049 b31050 d31040
        omega
      have d31051 : (x 11 12).toNat = 0 := by
        have r31052 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31053 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e31054 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b31055 := hb (x 8 3)
        have b31056 := hb (x 9 2)
        have b31057 := hb (x 10 13)
        have b31058 := hb (x 11 12)
        clear * - r31052 e31053 e31054 b31055 b31056 b31057 b31058 d30939 d31047
        omega
      have d31059 : (x 11 1 && x 11 12).toNat = 0 := by
        have r31060 := hand2 (x 11 1) (x 11 12)
        have b31061 := hb (x 11 12)
        have b31062 := hb (x 11 1 && x 11 12)
        clear * - r31060 b31061 b31062 d31051
        omega
      have d31063 : (x 10 13).toNat = 0 := by
        have r31064 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31065 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e31066 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b31067 := hb (x 8 3)
        have b31068 := hb (x 9 2)
        have b31069 := hb (x 10 13)
        have b31070 := hb (x 11 12)
        clear * - r31064 e31065 e31066 b31067 b31068 b31069 b31070 d31051 d30939 d31047
        omega
      have d31071 : (x 10 2 && x 10 13).toNat = 0 := by
        have r31072 := hand2 (x 10 2) (x 10 13)
        have b31073 := hb (x 10 13)
        have b31074 := hb (x 10 2 && x 10 13)
        clear * - r31072 b31073 b31074 d31063
        omega
      have d31075 : (x 12 11).toNat = 1 := by
        have r31076 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31077 := hb (x 8 4)
        have b31078 := hb (x 12 11)
        have b31079 := hb (x 11 1 && x 11 12)
        have b31080 := hb (x 10 2 && x 10 13)
        have b31081 := hb (x 9 3 && x 9 14)
        clear * - r31076 b31077 b31078 b31079 b31080 b31081 d31059 d31071 d30935 d30873
        omega
      have d31082 : (x 12 3).toNat = 1 := by
        have r31083 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
        have b31084 := hb (x 12 3)
        have b31085 := hb (x 12 11)
        clear * - r31083 b31084 b31085 d31075
        omega
      have d31086 : (x 15 12).toNat = 0 := by
        have r31087 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31088 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e31089 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b31090 := hb (x 12 3)
        have b31091 := hb (x 13 2)
        have b31092 := hb (x 14 13)
        have b31093 := hb (x 15 12)
        clear * - r31087 e31088 e31089 b31090 b31091 b31092 b31093 d31082
        omega
      have d31094 : (x 15 1 && x 15 12).toNat = 0 := by
        have r31095 := hand2 (x 15 1) (x 15 12)
        have b31096 := hb (x 15 12)
        have b31097 := hb (x 15 1 && x 15 12)
        clear * - r31095 b31096 b31097 d31086
        omega
      have d31098 : (x 14 13).toNat = 0 := by
        have r31099 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31100 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e31101 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b31102 := hb (x 12 3)
        have b31103 := hb (x 13 2)
        have b31104 := hb (x 14 13)
        have b31105 := hb (x 15 12)
        clear * - r31099 e31100 e31101 b31102 b31103 b31104 b31105 d31086 d31082
        omega
      have d31106 : (x 14 2 && x 14 13).toNat = 0 := by
        have r31107 := hand2 (x 14 2) (x 14 13)
        have b31108 := hb (x 14 13)
        have b31109 := hb (x 14 2 && x 14 13)
        clear * - r31107 b31108 b31109 d31098
        omega
      have d31110 : (x 13 2).toNat = 0 := by
        have r31111 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31112 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e31113 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b31114 := hb (x 12 3)
        have b31115 := hb (x 13 2)
        have b31116 := hb (x 14 13)
        have b31117 := hb (x 15 12)
        clear * - r31111 e31112 e31113 b31114 b31115 b31116 b31117 d31086 d31098 d31082
        omega
      have d31118 : (x 10 1).toNat = 1 := by
        have r31119 := hand1 (x 10 1) (x 10 14)
        have b31120 := hb (x 10 1)
        have b31121 := hb (x 10 1 && x 10 14)
        clear * - r31119 b31120 b31121 d31006
        omega
      have d31122 : (x 11 14).toNat = 0 := by
        have r31123 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31124 := hb (x 10 1)
        have b31125 := hb (x 11 14)
        clear * - r31123 b31124 b31125 d31118
        omega
      have d31126 : (x 11 1 && x 11 14).toNat = 0 := by
        have r31127 := hand2 (x 11 1) (x 11 14)
        have b31128 := hb (x 11 14)
        have b31129 := hb (x 11 1 && x 11 14)
        clear * - r31127 b31128 b31129 d31122
        omega
      have d31130 : (x 11 2).toNat = 0 := by
        have r31131 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
        have b31132 := hb (x 11 2)
        have b31133 := hb (x 11 14)
        clear * - r31131 b31132 b31133 d31122
        omega
      have d31134 : (x 10 2).toNat = 0 := by
        have r31135 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31136 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
        have e31137 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
        have b31138 := hb (x 9 3)
        have b31139 := hb (x 10 2)
        have b31140 := hb (x 11 13)
        have b31141 := hb (x 12 12)
        clear * - r31135 e31136 e31137 b31138 b31139 b31140 b31141 d30978 d30994 d30974
        omega
      have d31142 : (x 12 13).toNat = 1 := by
        have r31143 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31144 := hb (x 10 2)
        have b31145 := hb (x 12 13)
        have b31146 := hb (x 11 1 && x 11 14)
        clear * - r31143 b31144 b31145 b31146 d31126 d31134
        omega
      have d31147 : (x 12 1).toNat = 1 := by
        have r31148 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
        have b31149 := hb (x 12 1)
        have b31150 := hb (x 12 13)
        clear * - r31148 b31149 b31150 d31142
        omega
      have d31151 : (x 13 14).toNat = 0 := by
        have r31152 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31153 := hb (x 12 1)
        have b31154 := hb (x 13 14)
        clear * - r31152 b31153 b31154 d31147
        omega
      have d31155 : (x 13 1 && x 13 14).toNat = 0 := by
        have r31156 := hand2 (x 13 1) (x 13 14)
        have b31157 := hb (x 13 14)
        have b31158 := hb (x 13 1 && x 13 14)
        clear * - r31156 b31157 b31158 d31151
        omega
      have d31159 : (x 12 2).toNat = 1 := by
        have r31160 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31161 := hb (x 12 2)
        have b31162 := hb (x 14 13)
        have b31163 := hb (x 13 1 && x 13 14)
        clear * - r31160 b31161 b31162 b31163 d31098 d31155
        omega
      have d31164 : (x 14 12).toNat = 0 := by
        have r31165 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31166 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
        have e31167 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
        have b31168 := hb (x 11 3)
        have b31169 := hb (x 12 2)
        have b31170 := hb (x 13 13)
        have b31171 := hb (x 14 12)
        clear * - r31165 e31166 e31167 b31168 b31169 b31170 b31171 d31159
        omega
      have d31172 : (x 14 4).toNat = 0 := by
        have r31173 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
        have b31174 := hb (x 14 4)
        have b31175 := hb (x 14 12)
        clear * - r31173 b31174 b31175 d31164
        omega
      have d31176 : (x 14 4 && x 14 14).toNat = 0 := by
        have r31177 := hand1 (x 14 4) (x 14 14)
        have b31178 := hb (x 14 4)
        have b31179 := hb (x 14 4 && x 14 14)
        clear * - r31177 b31178 b31179 d31172
        omega
      have d31180 : (x 13 13).toNat = 0 := by
        have r31181 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31182 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
        have e31183 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
        have b31184 := hb (x 11 3)
        have b31185 := hb (x 12 2)
        have b31186 := hb (x 13 13)
        have b31187 := hb (x 14 12)
        clear * - r31181 e31182 e31183 b31184 b31185 b31186 b31187 d31164 d31159
        omega
      have d31188 : (x 13 5).toNat = 0 := by
        have r31189 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
        have b31190 := hb (x 13 5)
        have b31191 := hb (x 13 13)
        clear * - r31189 b31190 b31191 d31180
        omega
      have d31192 : (x 13 3 && x 13 14).toNat = 0 := by
        have r31193 := hand2 (x 13 3) (x 13 14)
        have b31194 := hb (x 13 14)
        have b31195 := hb (x 13 3 && x 13 14)
        clear * - r31193 b31194 b31195 d31151
        omega
      have d31196 : (x 16 11).toNat = 1 := by
        have r31197 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31198 := hb (x 12 4)
        have b31199 := hb (x 16 11)
        have b31200 := hb (x 15 1 && x 15 12)
        have b31201 := hb (x 14 2 && x 14 13)
        have b31202 := hb (x 13 3 && x 13 14)
        clear * - r31197 b31198 b31199 b31200 b31201 b31202 d31094 d31106 d31192 d30990
        omega
      have d31203 : (x 16 3).toNat = 1 := by
        have r31204 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
        have b31205 := hb (x 16 3)
        have b31206 := hb (x 16 11)
        clear * - r31204 b31205 b31206 d31196
        omega
      have d31207 : (x 19 12).toNat = 0 := by
        have r31208 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31209 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
        have e31210 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
        have b31211 := hb (x 16 3)
        have b31212 := hb (x 17 2)
        have b31213 := hb (x 18 13)
        have b31214 := hb (x 19 12)
        clear * - r31208 e31209 e31210 b31211 b31212 b31213 b31214 d31203
        omega
      have d31215 : (x 18 13).toNat = 0 := by
        have r31216 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31217 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
        have e31218 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
        have b31219 := hb (x 16 3)
        have b31220 := hb (x 17 2)
        have b31221 := hb (x 18 13)
        have b31222 := hb (x 19 12)
        clear * - r31216 e31217 e31218 b31219 b31220 b31221 b31222 d31207 d31203
        omega
      have d31223 : (x 17 2).toNat = 0 := by
        have r31224 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31225 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
        have e31226 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
        have b31227 := hb (x 16 3)
        have b31228 := hb (x 17 2)
        have b31229 := hb (x 18 13)
        have b31230 := hb (x 19 12)
        clear * - r31224 e31225 e31226 b31227 b31228 b31229 b31230 d31207 d31215 d31203
        omega
      have d31231 : (x 13 12).toNat = 0 := by
        have r31232 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31233 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
        have e31234 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
        have b31235 := hb (x 10 3)
        have b31236 := hb (x 11 2)
        have b31237 := hb (x 12 13)
        have b31238 := hb (x 13 12)
        clear * - r31232 e31233 e31234 b31235 b31236 b31237 b31238 d31142 d31130
        omega
      have d31239 : (x 13 4).toNat = 0 := by
        have r31240 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
        have b31241 := hb (x 13 4)
        have b31242 := hb (x 13 12)
        clear * - r31240 b31241 b31242 d31231
        omega
      have d31243 : (x 10 3).toNat = 0 := by
        have r31244 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31245 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
        have e31246 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
        have b31247 := hb (x 10 3)
        have b31248 := hb (x 11 2)
        have b31249 := hb (x 12 13)
        have b31250 := hb (x 13 12)
        clear * - r31244 e31245 e31246 b31247 b31248 b31249 b31250 d31231 d31142 d31130
        omega
      have d31251 : (x 10 3 && x 10 14).toNat = 0 := by
        have r31252 := hand1 (x 10 3) (x 10 14)
        have b31253 := hb (x 10 3)
        have b31254 := hb (x 10 3 && x 10 14)
        clear * - r31252 b31253 b31254 d31243
        omega
      have d31255 : (x 13 11).toNat = 1 := by
        have r31256 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31257 := hb (x 9 4)
        have b31258 := hb (x 13 11)
        have b31259 := hb (x 12 1 && x 12 12)
        have b31260 := hb (x 11 2 && x 11 13)
        have b31261 := hb (x 10 3 && x 10 14)
        clear * - r31256 b31257 b31258 b31259 b31260 b31261 d30986 d31002 d31251 d30951
        omega
      have d31262 : (x 13 3).toNat = 1 := by
        have r31263 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
        have b31264 := hb (x 13 3)
        have b31265 := hb (x 13 11)
        clear * - r31263 b31264 b31265 d31255
        omega
      have d31266 : (x 16 12).toNat = 0 := by
        have r31267 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31268 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
        have e31269 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
        have b31270 := hb (x 13 3)
        have b31271 := hb (x 14 2)
        have b31272 := hb (x 15 13)
        have b31273 := hb (x 16 12)
        clear * - r31267 e31268 e31269 b31270 b31271 b31272 b31273 d31262
        omega
      have d31274 : (x 16 1 && x 16 12).toNat = 0 := by
        have r31275 := hand2 (x 16 1) (x 16 12)
        have b31276 := hb (x 16 12)
        have b31277 := hb (x 16 1 && x 16 12)
        clear * - r31275 b31276 b31277 d31266
        omega
      have d31278 : (x 16 2 && x 16 12).toNat = 0 := by
        have r31279 := hand2 (x 16 2) (x 16 12)
        have b31280 := hb (x 16 12)
        have b31281 := hb (x 16 2 && x 16 12)
        clear * - r31279 b31280 b31281 d31266
        omega
      have d31282 : (x 15 13).toNat = 0 := by
        have r31283 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31284 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
        have e31285 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
        have b31286 := hb (x 13 3)
        have b31287 := hb (x 14 2)
        have b31288 := hb (x 15 13)
        have b31289 := hb (x 16 12)
        clear * - r31283 e31284 e31285 b31286 b31287 b31288 b31289 d31266 d31262
        omega
      have d31290 : (x 15 2 && x 15 13).toNat = 0 := by
        have r31291 := hand2 (x 15 2) (x 15 13)
        have b31292 := hb (x 15 13)
        have b31293 := hb (x 15 2 && x 15 13)
        clear * - r31291 b31292 b31293 d31282
        omega
      have d31294 : (x 15 3 && x 15 13).toNat = 0 := by
        have r31295 := hand2 (x 15 3) (x 15 13)
        have b31296 := hb (x 15 13)
        have b31297 := hb (x 15 3 && x 15 13)
        clear * - r31295 b31296 b31297 d31282
        omega
      have d31298 : (x 14 1 && x 14 14).toNat = 1 := by
        have r31299 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31300 := hb (x 13 2)
        have b31301 := hb (x 15 13)
        have b31302 := hb (x 14 1 && x 14 14)
        clear * - r31299 b31300 b31301 b31302 d31282 d31110
        omega
      have d31303 : (x 14 1).toNat = 1 := by
        have r31304 := hand1 (x 14 1) (x 14 14)
        have b31305 := hb (x 14 1)
        have b31306 := hb (x 14 1 && x 14 14)
        clear * - r31304 b31305 b31306 d31298
        omega
      have d31307 : (x 15 14).toNat = 0 := by
        have r31308 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31309 := hb (x 14 1)
        have b31310 := hb (x 15 14)
        clear * - r31308 b31309 b31310 d31303
        omega
      have d31311 : (x 15 1 && x 15 14).toNat = 0 := by
        have r31312 := hand2 (x 15 1) (x 15 14)
        have b31313 := hb (x 15 14)
        have b31314 := hb (x 15 1 && x 15 14)
        clear * - r31312 b31313 b31314 d31307
        omega
      have d31315 : (x 15 2).toNat = 0 := by
        have r31316 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
        have b31317 := hb (x 15 2)
        have b31318 := hb (x 15 14)
        clear * - r31316 b31317 b31318 d31307
        omega
      have d31319 : (x 14 2).toNat = 0 := by
        have r31320 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31321 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
        have e31322 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
        have b31323 := hb (x 13 3)
        have b31324 := hb (x 14 2)
        have b31325 := hb (x 15 13)
        have b31326 := hb (x 16 12)
        clear * - r31320 e31321 e31322 b31323 b31324 b31325 b31326 d31266 d31282 d31262
        omega
      have d31327 : (x 16 13).toNat = 1 := by
        have r31328 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31329 := hb (x 14 2)
        have b31330 := hb (x 16 13)
        have b31331 := hb (x 15 1 && x 15 14)
        clear * - r31328 b31329 b31330 b31331 d31311 d31319
        omega
      have d31332 : (x 17 12).toNat = 0 := by
        have r31333 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31334 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
        have e31335 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
        have b31336 := hb (x 14 3)
        have b31337 := hb (x 15 2)
        have b31338 := hb (x 16 13)
        have b31339 := hb (x 17 12)
        clear * - r31333 e31334 e31335 b31336 b31337 b31338 b31339 d31327 d31315
        omega
      have d31340 : (x 14 3).toNat = 0 := by
        have r31341 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31342 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
        have e31343 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
        have b31344 := hb (x 14 3)
        have b31345 := hb (x 15 2)
        have b31346 := hb (x 16 13)
        have b31347 := hb (x 17 12)
        clear * - r31341 e31342 e31343 b31344 b31345 b31346 b31347 d31332 d31327 d31315
        omega
      have d31348 : (x 14 3 && x 14 14).toNat = 0 := by
        have r31349 := hand1 (x 14 3) (x 14 14)
        have b31350 := hb (x 14 3)
        have b31351 := hb (x 14 3 && x 14 14)
        clear * - r31349 b31350 b31351 d31340
        omega
      have d31352 : (x 17 11).toNat = 1 := by
        have r31353 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31354 := hb (x 13 4)
        have b31355 := hb (x 17 11)
        have b31356 := hb (x 16 1 && x 16 12)
        have b31357 := hb (x 15 2 && x 15 13)
        have b31358 := hb (x 14 3 && x 14 14)
        clear * - r31353 b31354 b31355 b31356 b31357 b31358 d31274 d31290 d31348 d31239
        omega
      have d31359 : (x 17 3).toNat = 1 := by
        have r31360 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
        have b31361 := hb (x 17 3)
        have b31362 := hb (x 17 11)
        clear * - r31360 b31361 b31362 d31352
        omega
      have d31363 : (x 20 12).toNat = 0 := by
        have r31364 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31365 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
        have e31366 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
        have b31367 := hb (x 17 3)
        have b31368 := hb (x 18 2)
        have b31369 := hb (x 19 13)
        have b31370 := hb (x 20 12)
        clear * - r31364 e31365 e31366 b31367 b31368 b31369 b31370 d31359
        omega
      have d31371 : (x 19 13).toNat = 0 := by
        have r31372 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31373 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
        have e31374 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
        have b31375 := hb (x 17 3)
        have b31376 := hb (x 18 2)
        have b31377 := hb (x 19 13)
        have b31378 := hb (x 20 12)
        clear * - r31372 e31373 e31374 b31375 b31376 b31377 b31378 d31363 d31359
        omega
      have d31379 : (x 18 1 && x 18 14).toNat = 1 := by
        have r31380 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31381 := hb (x 17 2)
        have b31382 := hb (x 19 13)
        have b31383 := hb (x 18 1 && x 18 14)
        clear * - r31380 b31381 b31382 b31383 d31371 d31223
        omega
      have d31384 : (x 18 14).toNat = 1 := by
        have r31385 := hand2 (x 18 1) (x 18 14)
        have b31386 := hb (x 18 14)
        have b31387 := hb (x 18 1 && x 18 14)
        clear * - r31385 b31386 b31387 d31379
        omega
      have d31388 : (x 17 1).toNat = 0 := by
        have r31389 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31390 := hb (x 17 1)
        have b31391 := hb (x 18 14)
        clear * - r31389 b31390 b31391 d31384
        omega
      have d31392 : (x 17 1 && x 17 11).toNat = 0 := by
        have r31393 := hand1 (x 17 1) (x 17 11)
        have b31394 := hb (x 17 1)
        have b31395 := hb (x 17 1 && x 17 11)
        clear * - r31393 b31394 b31395 d31388
        omega
      have d31396 : (x 18 2).toNat = 0 := by
        have r31397 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31398 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
        have e31399 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
        have b31400 := hb (x 17 3)
        have b31401 := hb (x 18 2)
        have b31402 := hb (x 19 13)
        have b31403 := hb (x 20 12)
        clear * - r31397 e31398 e31399 b31400 b31401 b31402 b31403 d31363 d31371 d31359
        omega
      have d31404 : (x 18 10).toNat = 0 := by
        have r31405 : (x 18 10).toNat ≤ (x 18 2).toNat := himp _ _ (hp10 18)
        have b31406 := hb (x 18 2)
        have b31407 := hb (x 18 10)
        clear * - r31405 b31406 b31407 d31396
        omega
      have r31408 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := by have q := hcov10 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b31409 := hb (x 13 5)
      have b31410 := hb (x 18 10)
      have b31411 := hb (x 17 1 && x 17 11)
      have b31412 := hb (x 16 2 && x 16 12)
      have b31413 := hb (x 15 3 && x 15 13)
      have b31414 := hb (x 14 4 && x 14 14)
      linarith only [r31408, b31409, b31410, b31411, b31412, b31413, b31414, d31404, d31392, d31278, d31294, d31176, d31188]

theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a0000000 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-7) 7).toNat = 0)
    (g1 : (x (-6) 6).toNat = 0)
    (g2 : (x (-5) 5).toNat = 0)
    (g3 : (x (-4) 4).toNat = 0)
    (g4 : (x (-3) 11).toNat = 0)
    (g5 : (x (-2) 10).toNat = 0)
    (g6 : (x (-1) 1).toNat = 1)
    (g7 : (x (-1) 9).toNat = 0)
    (g8 : (x 0 1).toNat = 0)
    (g9 : (x 0 2).toNat = 0)
    (g10 : (x 0 3).toNat = 0)
    (g11 : (x 0 4).toNat = 0)
    (g12 : (x 0 5).toNat = 0)
    (g13 : (x 0 6).toNat = 0)
    (g14 : (x 0 7).toNat = 0)
    (g15 : (x 0 8).toNat = 1)
    (g16 : (x 0 9).toNat = 0)
    (g17 : (x 0 10).toNat = 0)
    (g18 : (x 0 11).toNat = 0)
    (g19 : (x 0 12).toNat = 0)
    (g20 : (x 0 13).toNat = 0)
    (g21 : (x 1 1).toNat = 0)
    (g22 : (x 1 14).toNat = 1)
    (g23 : (x (-4) 4 && x (-4) 8).toNat = 0)
    (g24 : (x (-5) 5 && x (-5) 9).toNat = 0)
    (g25 : (x (-6) 6 && x (-6) 10).toNat = 0)
    (g26 : (x (-7) 7 && x (-7) 11).toNat = 0)
    (g27 : (x 0 7 && x 0 11).toNat = 0)
    (g28 : (x 0 1 && x 0 6).toNat = 0)
    (g29 : (x 0 3 && x 0 8).toNat = 0)
    (g30 : (x (-1) 4 && x (-1) 9).toNat = 0)
    (g31 : (x (-2) 5 && x (-2) 10).toNat = 0)
    (g32 : (x (-3) 6 && x (-3) 11).toNat = 0)
    (g33 : (x 0 9 && x 0 14).toNat = 0)
    (g34 : (x (-4) 4 && x (-4) 10).toNat = 0)
    (g35 : (x (-5) 5 && x (-5) 11).toNat = 0)
    (g36 : (x (-6) 6 && x (-6) 12).toNat = 0)
    (g37 : (x (-7) 7 && x (-7) 13).toNat = 0)
    (g38 : (x (-4) 4 && x (-4) 11).toNat = 0)
    (g39 : (x (-5) 5 && x (-5) 12).toNat = 0)
    (g40 : (x (-6) 6 && x (-6) 13).toNat = 0)
    (g41 : (x (-7) 7 && x (-7) 14).toNat = 0)
    (g42 : (x 0 1 && x 0 8).toNat = 0)
    (g43 : (x (-1) 2 && x (-1) 9).toNat = 0)
    (g44 : (x (-2) 3 && x (-2) 10).toNat = 0)
    (g45 : (x (-3) 4 && x (-3) 11).toNat = 0)
    (g46 : (x 0 7 && x 0 14).toNat = 0)
    (g47 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g48 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g49 : (x (-4) 4 && x (-4) 13).toNat = 0)
    (g50 : (x (-5) 5 && x (-5) 14).toNat = 0)
    (g51 : (x 0 1 && x 0 10).toNat = 0)
    (g52 : (x 0 5 && x 0 14).toNat = 0)
    (g53 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g54 : (x (-4) 4 && x (-4) 14).toNat = 0)
    (g55 : (x 0 3 && x 0 13).toNat = 0)
    (g56 : (x 0 4 && x 0 14).toNat = 0)
    (g57 : (x 0 1 && x 0 12).toNat = 0)
    (g58 : (x 0 3 && x 0 14).toNat = 0)
    (g59 : (x 0 1 && x 0 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a0000000_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59
