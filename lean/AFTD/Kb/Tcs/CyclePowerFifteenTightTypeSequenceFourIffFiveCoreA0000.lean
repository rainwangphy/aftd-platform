import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_four_iff_five_core_a0000

Topic: combinatorics   Node: 45c58d43df06

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_four_iff_five_core: under the layer-free tight-cover constraints for k = 15 and 8 fixed bits of the class-type sequence near position 0, the constraints are contradictory. Its module also proves the sibling branches cycle_power_fifteen_tight_type_sequence_four_iff_five_core_b101, cycle_power_fifteen_tight_type_sequence_four_iff_five_core_b11.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_four_iff_five_core_b101 (x : ℤ → Fin 16 → Bool)
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
    (g2 : (x (-3) 13).toNat = 0)
    (g3 : (x (-2) 11).toNat = 0)
    (g4 : (x (-1) 5).toNat = 0)
    (g5 : (x (-1) 9).toNat = 0)
    (g6 : (x (-1) 10).toNat = 0)
    (g7 : (x (-1) 11).toNat = 0)
    (g8 : (x (-1) 13).toNat = 0)
    (g9 : (x 0 4).toNat = 0)
    (g10 : (x 0 6).toNat = 0)
    (g11 : (x 0 7).toNat = 0)
    (g12 : (x 0 8).toNat = 1)
    (g13 : (x 1 6).toNat = 0)
    (g14 : (x 1 9).toNat = 0)
    (g15 : (x 1 11).toNat = 0)
    (g16 : (x 2 5).toNat = 0)
    (g17 : (x 3 2).toNat = 0)
    (g18 : (x 3 5).toNat = 0)
    (g19 : (x 3 6).toNat = 0)
    (g20 : (x 3 9).toNat = 0)
    (g21 : (x 3 13).toNat = 0)
    (g22 : (x 4 14).toNat = 1)
    (g23 : (x 5 2).toNat = 0)
    (g24 : (x 5 5).toNat = 0)
    (g25 : (x 5 6).toNat = 0)
    (g26 : (x 5 13).toNat = 0)
    (g27 : (x 6 4).toNat = 0)
    (g28 : (x 6 8).toNat = 0)
    (g29 : (x 6 12).toNat = 0)
    (g30 : (x 3 3 && x 3 6).toNat = 0)
    (g31 : (x 2 4 && x 2 7).toNat = 0)
    (g32 : (x 1 5 && x 1 8).toNat = 0)
    (g33 : (x 0 6 && x 0 9).toNat = 0)
    (g34 : (x (-1) 7 && x (-1) 10).toNat = 0)
    (g35 : (x (-2) 8 && x (-2) 11).toNat = 0)
    (g36 : (x (-3) 9 && x (-3) 12).toNat = 0)
    (g37 : (x 6 1 && x 6 4).toNat = 0)
    (g38 : (x 5 2 && x 5 5).toNat = 0)
    (g39 : (x 3 4 && x 3 7).toNat = 0)
    (g40 : (x 2 5 && x 2 8).toNat = 0)
    (g41 : (x 1 6 && x 1 9).toNat = 0)
    (g42 : (x 0 7 && x 0 10).toNat = 0)
    (g43 : (x (-1) 8 && x (-1) 11).toNat = 0)
    (g44 : (x (-3) 10 && x (-3) 13).toNat = 0)
    (g45 : (x (-3) 3 && x (-3) 7).toNat = 0)
    (g46 : (x 1 1 && x 1 6).toNat = 0)
    (g47 : (x 0 2 && x 0 7).toNat = 0)
    (g48 : (x (-1) 3 && x (-1) 8).toNat = 0)
    (g49 : (x (-3) 5 && x (-3) 10).toNat = 0)
    (g50 : (x (-1) 1 && x (-1) 7).toNat = 0)
    (g51 : (x (-3) 3 && x (-3) 9).toNat = 0)
    (g52 : (x 0 1 && x 0 7).toNat = 0)
    (g53 : (x (-1) 2 && x (-1) 8).toNat = 0)
    (g54 : (x (-2) 3 && x (-2) 9).toNat = 0)
    (g55 : (x 4 2 && x 4 8).toNat = 0)
    (g56 : (x 3 3 && x 3 9).toNat = 0)
    (g57 : (x 2 4 && x 2 10).toNat = 0)
    (g58 : (x 1 5 && x 1 11).toNat = 0)
    (g59 : (x 0 6 && x 0 12).toNat = 0)
    (g60 : (x (-1) 7 && x (-1) 13).toNat = 0)
    (g61 : (x 5 2 && x 5 8).toNat = 0)
    (g62 : (x 4 3 && x 4 9).toNat = 0)
    (g63 : (x 3 4 && x 3 10).toNat = 0)
    (g64 : (x 2 5 && x 2 11).toNat = 0)
    (g65 : (x 1 6 && x 1 12).toNat = 0)
    (g66 : (x 0 7 && x 0 13).toNat = 0)
    (g67 : (x 6 6 && x 6 12).toNat = 0)
    (g68 : (x 5 7 && x 5 13).toNat = 0)
    (g69 : (x 4 8 && x 4 14).toNat = 0)
    (g70 : (x (-1) 1 && x (-1) 8).toNat = 0)
    (g71 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g72 : (x (-2) 2 && x (-2) 11).toNat = 0)
    (g73 : (x 5 2 && x 5 11).toNat = 0)
    (g74 : (x 3 4 && x 3 13).toNat = 0)
    (g75 : (x 2 5 && x 2 14).toNat = 0)
    (g76 : (x 6 3 && x 6 12).toNat = 0)
    (g77 : (x 5 4 && x 5 13).toNat = 0)
    (g78 : (x 7 4 && x 7 13).toNat = 0)
    (g79 : (x 6 5 && x 6 14).toNat = 0)
    (g80 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g81 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g82 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g83 : (x (-3) 1 && x (-3) 12).toNat = 0)
    (g84 : (x (-3) 2 && x (-3) 13).toNat = 0)
    (g85 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g86 : (x (-2) 3 && x (-2) 14).toNat = 0)
    (g87 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d8295 : (x (-2) 10).toNat = 0 := by
    have r8296 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8297 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e8298 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e8299 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e8300 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e8301 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e8302 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b8303 := hb (x (-7) 7)
    have b8304 := hb (x (-6) 6)
    have b8305 := hb (x (-5) 5)
    have b8306 := hb (x (-4) 4)
    have b8307 := hb (x (-3) 11)
    have b8308 := hb (x (-2) 10)
    have b8309 := hb (x (-1) 9)
    have b8310 := hb (x 0 8)
    clear * - r8296 e8297 e8298 e8299 e8300 e8301 e8302 b8303 b8304 b8305 b8306 b8307 b8308 b8309 b8310 g12 g5
    omega
  have d8311 : (x (-2) 1 && x (-2) 10).toNat = 0 := by
    have r8312 := hand2 (x (-2) 1) (x (-2) 10)
    have b8313 := hb (x (-2) 10)
    have b8314 := hb (x (-2) 1 && x (-2) 10)
    clear * - r8312 b8313 b8314 d8295
    omega
  have d8315 : (x (-3) 11).toNat = 0 := by
    have r8316 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8317 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e8318 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e8319 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e8320 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e8321 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e8322 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b8323 := hb (x (-7) 7)
    have b8324 := hb (x (-6) 6)
    have b8325 := hb (x (-5) 5)
    have b8326 := hb (x (-4) 4)
    have b8327 := hb (x (-3) 11)
    have b8328 := hb (x (-2) 10)
    have b8329 := hb (x (-1) 9)
    have b8330 := hb (x 0 8)
    clear * - r8316 e8317 e8318 e8319 e8320 e8321 e8322 b8323 b8324 b8325 b8326 b8327 b8328 b8329 b8330 g12 g5 d8295
    omega
  have d8331 : (x (-3) 2 && x (-3) 11).toNat = 0 := by
    have r8332 := hand2 (x (-3) 2) (x (-3) 11)
    have b8333 := hb (x (-3) 11)
    have b8334 := hb (x (-3) 2 && x (-3) 11)
    clear * - r8332 b8333 b8334 d8315
    omega
  have d8335 : (x (-4) 4).toNat = 0 := by
    have r8336 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8337 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e8338 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e8339 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e8340 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e8341 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e8342 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b8343 := hb (x (-7) 7)
    have b8344 := hb (x (-6) 6)
    have b8345 := hb (x (-5) 5)
    have b8346 := hb (x (-4) 4)
    have b8347 := hb (x (-3) 11)
    have b8348 := hb (x (-2) 10)
    have b8349 := hb (x (-1) 9)
    have b8350 := hb (x 0 8)
    clear * - r8336 e8337 e8338 e8339 e8340 e8341 e8342 b8343 b8344 b8345 b8346 b8347 b8348 b8349 b8350 g12 g5 d8295 d8315
    omega
  have d8351 : (x (-4) 4 && x (-4) 14).toNat = 0 := by
    have r8352 := hand1 (x (-4) 4) (x (-4) 14)
    have b8353 := hb (x (-4) 4)
    have b8354 := hb (x (-4) 4 && x (-4) 14)
    clear * - r8352 b8353 b8354 d8335
    omega
  have d8355 : (x (-4) 4 && x (-4) 13).toNat = 0 := by
    have r8356 := hand1 (x (-4) 4) (x (-4) 13)
    have b8357 := hb (x (-4) 4)
    have b8358 := hb (x (-4) 4 && x (-4) 13)
    clear * - r8356 b8357 b8358 d8335
    omega
  have d8359 : (x (-4) 4 && x (-4) 11).toNat = 0 := by
    have r8360 := hand1 (x (-4) 4) (x (-4) 11)
    have b8361 := hb (x (-4) 4)
    have b8362 := hb (x (-4) 4 && x (-4) 11)
    clear * - r8360 b8361 b8362 d8335
    omega
  have d8363 : (x (-4) 4 && x (-4) 10).toNat = 0 := by
    have r8364 := hand1 (x (-4) 4) (x (-4) 10)
    have b8365 := hb (x (-4) 4)
    have b8366 := hb (x (-4) 4 && x (-4) 10)
    clear * - r8364 b8365 b8366 d8335
    omega
  have d8367 : (x (-4) 4 && x (-4) 8).toNat = 0 := by
    have r8368 := hand1 (x (-4) 4) (x (-4) 8)
    have b8369 := hb (x (-4) 4)
    have b8370 := hb (x (-4) 4 && x (-4) 8)
    clear * - r8368 b8369 b8370 d8335
    omega
  have d8371 : (x (-5) 5).toNat = 0 := by
    have r8372 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8373 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e8374 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e8375 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e8376 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e8377 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e8378 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b8379 := hb (x (-7) 7)
    have b8380 := hb (x (-6) 6)
    have b8381 := hb (x (-5) 5)
    have b8382 := hb (x (-4) 4)
    have b8383 := hb (x (-3) 11)
    have b8384 := hb (x (-2) 10)
    have b8385 := hb (x (-1) 9)
    have b8386 := hb (x 0 8)
    clear * - r8372 e8373 e8374 e8375 e8376 e8377 e8378 b8379 b8380 b8381 b8382 b8383 b8384 b8385 b8386 g12 g5 d8295 d8315 d8335
    omega
  have d8387 : (x (-5) 5 && x (-5) 14).toNat = 0 := by
    have r8388 := hand1 (x (-5) 5) (x (-5) 14)
    have b8389 := hb (x (-5) 5)
    have b8390 := hb (x (-5) 5 && x (-5) 14)
    clear * - r8388 b8389 b8390 d8371
    omega
  have d8391 : (x (-5) 5 && x (-5) 12).toNat = 0 := by
    have r8392 := hand1 (x (-5) 5) (x (-5) 12)
    have b8393 := hb (x (-5) 5)
    have b8394 := hb (x (-5) 5 && x (-5) 12)
    clear * - r8392 b8393 b8394 d8371
    omega
  have d8395 : (x (-5) 5 && x (-5) 11).toNat = 0 := by
    have r8396 := hand1 (x (-5) 5) (x (-5) 11)
    have b8397 := hb (x (-5) 5)
    have b8398 := hb (x (-5) 5 && x (-5) 11)
    clear * - r8396 b8397 b8398 d8371
    omega
  have d8399 : (x (-5) 5 && x (-5) 9).toNat = 0 := by
    have r8400 := hand1 (x (-5) 5) (x (-5) 9)
    have b8401 := hb (x (-5) 5)
    have b8402 := hb (x (-5) 5 && x (-5) 9)
    clear * - r8400 b8401 b8402 d8371
    omega
  have d8403 : (x (-6) 6).toNat = 0 := by
    have r8404 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8405 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e8406 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e8407 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e8408 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e8409 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e8410 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b8411 := hb (x (-7) 7)
    have b8412 := hb (x (-6) 6)
    have b8413 := hb (x (-5) 5)
    have b8414 := hb (x (-4) 4)
    have b8415 := hb (x (-3) 11)
    have b8416 := hb (x (-2) 10)
    have b8417 := hb (x (-1) 9)
    have b8418 := hb (x 0 8)
    clear * - r8404 e8405 e8406 e8407 e8408 e8409 e8410 b8411 b8412 b8413 b8414 b8415 b8416 b8417 b8418 g12 g5 d8295 d8315 d8335 d8371
    omega
  have d8419 : (x (-6) 6 && x (-6) 13).toNat = 0 := by
    have r8420 := hand1 (x (-6) 6) (x (-6) 13)
    have b8421 := hb (x (-6) 6)
    have b8422 := hb (x (-6) 6 && x (-6) 13)
    clear * - r8420 b8421 b8422 d8403
    omega
  have d8423 : (x (-6) 6 && x (-6) 12).toNat = 0 := by
    have r8424 := hand1 (x (-6) 6) (x (-6) 12)
    have b8425 := hb (x (-6) 6)
    have b8426 := hb (x (-6) 6 && x (-6) 12)
    clear * - r8424 b8425 b8426 d8403
    omega
  have d8427 : (x (-6) 6 && x (-6) 10).toNat = 0 := by
    have r8428 := hand1 (x (-6) 6) (x (-6) 10)
    have b8429 := hb (x (-6) 6)
    have b8430 := hb (x (-6) 6 && x (-6) 10)
    clear * - r8428 b8429 b8430 d8403
    omega
  have d8431 : (x (-7) 7).toNat = 0 := by
    have r8432 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8433 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e8434 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e8435 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e8436 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e8437 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e8438 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b8439 := hb (x (-7) 7)
    have b8440 := hb (x (-6) 6)
    have b8441 := hb (x (-5) 5)
    have b8442 := hb (x (-4) 4)
    have b8443 := hb (x (-3) 11)
    have b8444 := hb (x (-2) 10)
    have b8445 := hb (x (-1) 9)
    have b8446 := hb (x 0 8)
    clear * - r8432 e8433 e8434 e8435 e8436 e8437 e8438 b8439 b8440 b8441 b8442 b8443 b8444 b8445 b8446 g12 g5 d8295 d8315 d8335 d8371 d8403
    omega
  have d8447 : (x (-7) 7 && x (-7) 14).toNat = 0 := by
    have r8448 := hand1 (x (-7) 7) (x (-7) 14)
    have b8449 := hb (x (-7) 7)
    have b8450 := hb (x (-7) 7 && x (-7) 14)
    clear * - r8448 b8449 b8450 d8431
    omega
  have d8451 : (x (-7) 7 && x (-7) 13).toNat = 0 := by
    have r8452 := hand1 (x (-7) 7) (x (-7) 13)
    have b8453 := hb (x (-7) 7)
    have b8454 := hb (x (-7) 7 && x (-7) 13)
    clear * - r8452 b8453 b8454 d8431
    omega
  have d8455 : (x (-7) 7 && x (-7) 11).toNat = 0 := by
    have r8456 := hand1 (x (-7) 7) (x (-7) 11)
    have b8457 := hb (x (-7) 7)
    have b8458 := hb (x (-7) 7 && x (-7) 11)
    clear * - r8456 b8457 b8458 d8431
    omega
  cases h8459 : x 0 9
  · have f8460 : (x 0 9).toNat = 0 := by rw [h8459]; rfl
    have d8461 : (x (-3) 3 && x (-3) 12).toNat = 1 := by
      have r8462 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8463 := hb (x (-6) 6)
      have b8464 := hb (x 0 9)
      have b8465 := hb (x (-1) 1 && x (-1) 10)
      have b8466 := hb (x (-2) 2 && x (-2) 11)
      have b8467 := hb (x (-3) 3 && x (-3) 12)
      have b8468 := hb (x (-4) 4 && x (-4) 13)
      have b8469 := hb (x (-5) 5 && x (-5) 14)
      clear * - r8462 b8463 b8464 b8465 b8466 b8467 b8468 b8469 f8460 g71 g72 d8355 d8387 d8403
      omega
    have d8470 : (x (-3) 12).toNat = 1 := by
      have r8471 := hand2 (x (-3) 3) (x (-3) 12)
      have b8472 := hb (x (-3) 12)
      have b8473 := hb (x (-3) 3 && x (-3) 12)
      clear * - r8471 b8472 b8473 d8461
      omega
    have d8474 : (x (-4) 13).toNat = 0 := by
      have r8475 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8476 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e8477 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b8478 := hb (x (-6) 3)
      have b8479 := hb (x (-5) 2)
      have b8480 := hb (x (-4) 13)
      have b8481 := hb (x (-3) 12)
      clear * - r8475 e8476 e8477 b8478 b8479 b8480 b8481 d8470
      omega
    have d8482 : (x (-5) 2).toNat = 0 := by
      have r8483 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8484 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e8485 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b8486 := hb (x (-6) 3)
      have b8487 := hb (x (-5) 2)
      have b8488 := hb (x (-4) 13)
      have b8489 := hb (x (-3) 12)
      clear * - r8483 e8484 e8485 b8486 b8487 b8488 b8489 d8470 d8474
      omega
    have d8490 : (x (-5) 2 && x (-5) 13).toNat = 0 := by
      have r8491 := hand1 (x (-5) 2) (x (-5) 13)
      have b8492 := hb (x (-5) 2)
      have b8493 := hb (x (-5) 2 && x (-5) 13)
      clear * - r8491 b8492 b8493 d8482
      omega
    have d8494 : (x (-4) 1 && x (-4) 14).toNat = 1 := by
      have r8495 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8496 := hb (x (-5) 2)
      have b8497 := hb (x (-3) 13)
      have b8498 := hb (x (-4) 1 && x (-4) 14)
      clear * - r8495 b8496 b8497 b8498 g2 d8482
      omega
    have d8499 : (x (-4) 14).toNat = 1 := by
      have r8500 := hand2 (x (-4) 1) (x (-4) 14)
      have b8501 := hb (x (-4) 14)
      have b8502 := hb (x (-4) 1 && x (-4) 14)
      clear * - r8500 b8501 b8502 d8494
      omega
    have d8503 : (x (-5) 1).toNat = 0 := by
      have r8504 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8505 := hb (x (-5) 1)
      have b8506 := hb (x (-4) 14)
      clear * - r8504 b8505 b8506 d8499
      omega
    have d8507 : (x (-5) 1 && x (-5) 14).toNat = 0 := by
      have r8508 := hand1 (x (-5) 1) (x (-5) 14)
      have b8509 := hb (x (-5) 1)
      have b8510 := hb (x (-5) 1 && x (-5) 14)
      clear * - r8508 b8509 b8510 d8503
      omega
    have d8511 : (x (-6) 2).toNat = 1 := by
      have r8512 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8513 := hb (x (-6) 2)
      have b8514 := hb (x (-4) 13)
      have b8515 := hb (x (-5) 1 && x (-5) 14)
      clear * - r8512 b8513 b8514 b8515 d8474 d8507
      omega
    have d8516 : (x (-6) 14).toNat = 1 := by
      have r8517 : (x (-6) 2).toNat ≤ (x (-6) 14).toNat := himp _ _ (hp2 (-6))
      have b8518 := hb (x (-6) 2)
      have b8519 := hb (x (-6) 14)
      clear * - r8517 b8518 b8519 d8511
      omega
    have d8520 : (x (-7) 1).toNat = 0 := by
      have r8521 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8522 := hb (x (-7) 1)
      have b8523 := hb (x (-6) 14)
      clear * - r8521 b8522 b8523 d8516
      omega
    have d8524 : (x (-7) 1 && x (-7) 14).toNat = 0 := by
      have r8525 := hand1 (x (-7) 1) (x (-7) 14)
      have b8526 := hb (x (-7) 1)
      have b8527 := hb (x (-7) 1 && x (-7) 14)
      clear * - r8525 b8526 b8527 d8520
      omega
    have d8528 : (x (-7) 13).toNat = 0 := by
      have r8529 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
      have b8530 := hb (x (-7) 1)
      have b8531 := hb (x (-7) 13)
      clear * - r8529 b8530 b8531 d8520
      omega
    have d8532 : (x (-7) 5).toNat = 0 := by
      have r8533 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
      have b8534 := hb (x (-7) 5)
      have b8535 := hb (x (-7) 13)
      clear * - r8533 b8534 b8535 d8528
      omega
    have d8536 : (x (-4) 12).toNat = 0 := by
      have r8537 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8538 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e8539 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have b8540 := hb (x (-7) 3)
      have b8541 := hb (x (-6) 2)
      have b8542 := hb (x (-5) 13)
      have b8543 := hb (x (-4) 12)
      clear * - r8537 e8538 e8539 b8540 b8541 b8542 b8543 d8511
      omega
    have d8544 : (x (-4) 1 && x (-4) 12).toNat = 0 := by
      have r8545 := hand2 (x (-4) 1) (x (-4) 12)
      have b8546 := hb (x (-4) 12)
      have b8547 := hb (x (-4) 1 && x (-4) 12)
      clear * - r8545 b8546 b8547 d8536
      omega
    have d8548 : (x (-4) 2 && x (-4) 12).toNat = 0 := by
      have r8549 := hand2 (x (-4) 2) (x (-4) 12)
      have b8550 := hb (x (-4) 12)
      have b8551 := hb (x (-4) 2 && x (-4) 12)
      clear * - r8549 b8550 b8551 d8536
      omega
    have d8552 : (x (-5) 13).toNat = 0 := by
      have r8553 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8554 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e8555 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have b8556 := hb (x (-7) 3)
      have b8557 := hb (x (-6) 2)
      have b8558 := hb (x (-5) 13)
      have b8559 := hb (x (-4) 12)
      clear * - r8553 e8554 e8555 b8556 b8557 b8558 b8559 d8536 d8511
      omega
    have d8560 : (x (-5) 3 && x (-5) 13).toNat = 0 := by
      have r8561 := hand2 (x (-5) 3) (x (-5) 13)
      have b8562 := hb (x (-5) 13)
      have b8563 := hb (x (-5) 3 && x (-5) 13)
      clear * - r8561 b8562 b8563 d8552
      omega
    have d8564 : (x (-6) 4 && x (-6) 14).toNat = 1 := by
      have r8565 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8566 := hb (x (-7) 5)
      have b8567 := hb (x (-2) 10)
      have b8568 := hb (x (-3) 1 && x (-3) 11)
      have b8569 := hb (x (-4) 2 && x (-4) 12)
      have b8570 := hb (x (-5) 3 && x (-5) 13)
      have b8571 := hb (x (-6) 4 && x (-6) 14)
      clear * - r8565 b8566 b8567 b8568 b8569 b8570 b8571 d8295 g80 d8548 d8560 d8532
      omega
    have d8572 : (x (-6) 4).toNat = 1 := by
      have r8573 := hand1 (x (-6) 4) (x (-6) 14)
      have b8574 := hb (x (-6) 4)
      have b8575 := hb (x (-6) 4 && x (-6) 14)
      clear * - r8573 b8574 b8575 d8564
      omega
    have d8576 : (x (-6) 12).toNat = 1 := by
      have r8577 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
      have b8578 := hb (x (-6) 4)
      have b8579 := hb (x (-6) 12)
      clear * - r8577 b8578 b8579 d8572
      omega
    have d8580 : (x (-8) 2).toNat = 0 := by
      have r8581 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8582 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
      have e8583 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
      have b8584 := hb (x (-9) 3)
      have b8585 := hb (x (-8) 2)
      have b8586 := hb (x (-7) 13)
      have b8587 := hb (x (-6) 12)
      clear * - r8581 e8582 e8583 b8584 b8585 b8586 b8587 d8576 d8528
      omega
    have d8588 : (x (-6) 13).toNat = 1 := by
      have r8589 : 1 ≤ (x (-6) 13).toNat + (x (-7) 1 && x (-7) 14).toNat + (x (-8) 2).toNat := by have q := hcov13 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8590 := hb (x (-8) 2)
      have b8591 := hb (x (-6) 13)
      have b8592 := hb (x (-7) 1 && x (-7) 14)
      clear * - r8589 b8590 b8591 b8592 d8524 d8580
      omega
    have d8593 : (x (-5) 12).toNat = 0 := by
      have r8594 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8595 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
      have e8596 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
      have b8597 := hb (x (-8) 3)
      have b8598 := hb (x (-7) 2)
      have b8599 := hb (x (-6) 13)
      have b8600 := hb (x (-5) 12)
      clear * - r8594 e8595 e8596 b8597 b8598 b8599 b8600 d8588
      omega
    have d8601 : (x (-7) 2).toNat = 0 := by
      have r8602 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8603 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
      have e8604 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
      have b8605 := hb (x (-8) 3)
      have b8606 := hb (x (-7) 2)
      have b8607 := hb (x (-6) 13)
      have b8608 := hb (x (-5) 12)
      clear * - r8602 e8603 e8604 b8605 b8606 b8607 b8608 d8593 d8588
      omega
    have d8609 : (x (-8) 3).toNat = 0 := by
      have r8610 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8611 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
      have e8612 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
      have b8613 := hb (x (-8) 3)
      have b8614 := hb (x (-7) 2)
      have b8615 := hb (x (-6) 13)
      have b8616 := hb (x (-5) 12)
      clear * - r8610 e8611 e8612 b8613 b8614 b8615 b8616 d8593 d8588 d8601
      omega
    have d8617 : (x (-8) 11).toNat = 0 := by
      have r8618 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
      have b8619 := hb (x (-8) 3)
      have b8620 := hb (x (-8) 11)
      clear * - r8618 b8619 b8620 d8609
      omega
    have d8621 : (x (-7) 3).toNat = 0 := by
      have r8622 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8623 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e8624 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have b8625 := hb (x (-7) 3)
      have b8626 := hb (x (-6) 2)
      have b8627 := hb (x (-5) 13)
      have b8628 := hb (x (-4) 12)
      clear * - r8622 e8623 e8624 b8625 b8626 b8627 b8628 d8536 d8552 d8511
      omega
    have d8629 : (x (-7) 11).toNat = 0 := by
      have r8630 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
      have b8631 := hb (x (-7) 3)
      have b8632 := hb (x (-7) 11)
      clear * - r8630 b8631 b8632 d8621
      omega
    have d8633 : (x (-6) 3).toNat = 0 := by
      have r8634 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8635 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e8636 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b8637 := hb (x (-6) 3)
      have b8638 := hb (x (-5) 2)
      have b8639 := hb (x (-4) 13)
      have b8640 := hb (x (-3) 12)
      clear * - r8634 e8635 e8636 b8637 b8638 b8639 b8640 d8470 d8474 d8482
      omega
    have d8641 : (x (-6) 3 && x (-6) 14).toNat = 0 := by
      have r8642 := hand1 (x (-6) 3) (x (-6) 14)
      have b8643 := hb (x (-6) 3)
      have b8644 := hb (x (-6) 3 && x (-6) 14)
      clear * - r8642 b8643 b8644 d8633
      omega
    have d8645 : (x (-7) 4).toNat = 1 := by
      have r8646 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := by have q := hcov11 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8647 := hb (x (-7) 4)
      have b8648 := hb (x (-3) 11)
      have b8649 := hb (x (-4) 1 && x (-4) 12)
      have b8650 := hb (x (-5) 2 && x (-5) 13)
      have b8651 := hb (x (-6) 3 && x (-6) 14)
      clear * - r8646 b8647 b8648 b8649 b8650 b8651 d8315 d8544 d8490 d8641
      omega
    have d8652 : (x (-7) 12).toNat = 1 := by
      have r8653 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
      have b8654 := hb (x (-7) 4)
      have b8655 := hb (x (-7) 12)
      clear * - r8653 b8654 b8655 d8645
      omega
    have d8656 : (x (-8) 13).toNat = 0 := by
      have r8657 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8658 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
      have e8659 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
      have b8660 := hb (x (-10) 3)
      have b8661 := hb (x (-9) 2)
      have b8662 := hb (x (-8) 13)
      have b8663 := hb (x (-7) 12)
      clear * - r8657 e8658 e8659 b8660 b8661 b8662 b8663 d8652
      omega
    have d8664 : (x (-9) 2).toNat = 0 := by
      have r8665 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8666 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
      have e8667 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
      have b8668 := hb (x (-10) 3)
      have b8669 := hb (x (-9) 2)
      have b8670 := hb (x (-8) 13)
      have b8671 := hb (x (-7) 12)
      clear * - r8665 e8666 e8667 b8668 b8669 b8670 b8671 d8652 d8656
      omega
    have d8672 : (x (-9) 2 && x (-9) 13).toNat = 0 := by
      have r8673 := hand1 (x (-9) 2) (x (-9) 13)
      have b8674 := hb (x (-9) 2)
      have b8675 := hb (x (-9) 2 && x (-9) 13)
      clear * - r8673 b8674 b8675 d8664
      omega
    have d8676 : (x (-8) 1 && x (-8) 14).toNat = 1 := by
      have r8677 : 1 ≤ (x (-7) 13).toNat + (x (-8) 1 && x (-8) 14).toNat + (x (-9) 2).toNat := by have q := hcov13 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8678 := hb (x (-9) 2)
      have b8679 := hb (x (-7) 13)
      have b8680 := hb (x (-8) 1 && x (-8) 14)
      clear * - r8677 b8678 b8679 b8680 d8528 d8664
      omega
    have d8681 : (x (-8) 14).toNat = 1 := by
      have r8682 := hand2 (x (-8) 1) (x (-8) 14)
      have b8683 := hb (x (-8) 14)
      have b8684 := hb (x (-8) 1 && x (-8) 14)
      clear * - r8682 b8683 b8684 d8676
      omega
    have d8685 : (x (-9) 1).toNat = 0 := by
      have r8686 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8687 := hb (x (-9) 1)
      have b8688 := hb (x (-8) 14)
      clear * - r8686 b8687 b8688 d8681
      omega
    have d8689 : (x (-9) 1 && x (-9) 14).toNat = 0 := by
      have r8690 := hand1 (x (-9) 1) (x (-9) 14)
      have b8691 := hb (x (-9) 1)
      have b8692 := hb (x (-9) 1 && x (-9) 14)
      clear * - r8690 b8691 b8692 d8685
      omega
    have d8693 : (x (-10) 2).toNat = 1 := by
      have r8694 : 1 ≤ (x (-8) 13).toNat + (x (-9) 1 && x (-9) 14).toNat + (x (-10) 2).toNat := by have q := hcov13 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8695 := hb (x (-10) 2)
      have b8696 := hb (x (-8) 13)
      have b8697 := hb (x (-9) 1 && x (-9) 14)
      clear * - r8694 b8695 b8696 b8697 d8656 d8689
      omega
    have d8698 : (x (-10) 14).toNat = 1 := by
      have r8699 : (x (-10) 2).toNat ≤ (x (-10) 14).toNat := himp _ _ (hp2 (-10))
      have b8700 := hb (x (-10) 2)
      have b8701 := hb (x (-10) 14)
      clear * - r8699 b8700 b8701 d8693
      omega
    have d8702 : (x (-11) 1).toNat = 0 := by
      have r8703 : (x (-10) 14).toNat + (x (-11) 1).toNat = 1 := by have q := hd14 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8704 := hb (x (-11) 1)
      have b8705 := hb (x (-10) 14)
      clear * - r8703 b8704 b8705 d8698
      omega
    have d8706 : (x (-11) 13).toNat = 0 := by
      have r8707 : (x (-11) 13).toNat ≤ (x (-11) 1).toNat := himp _ _ (hp13 (-11))
      have b8708 := hb (x (-11) 1)
      have b8709 := hb (x (-11) 13)
      clear * - r8707 b8708 b8709 d8702
      omega
    have d8710 : (x (-8) 12).toNat = 0 := by
      have r8711 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8712 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
      have e8713 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
      have b8714 := hb (x (-11) 3)
      have b8715 := hb (x (-10) 2)
      have b8716 := hb (x (-9) 13)
      have b8717 := hb (x (-8) 12)
      clear * - r8711 e8712 e8713 b8714 b8715 b8716 b8717 d8693
      omega
    have d8718 : (x (-8) 1 && x (-8) 12).toNat = 0 := by
      have r8719 := hand2 (x (-8) 1) (x (-8) 12)
      have b8720 := hb (x (-8) 12)
      have b8721 := hb (x (-8) 1 && x (-8) 12)
      clear * - r8719 b8720 b8721 d8710
      omega
    have d8722 : (x (-9) 13).toNat = 0 := by
      have r8723 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8724 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
      have e8725 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
      have b8726 := hb (x (-11) 3)
      have b8727 := hb (x (-10) 2)
      have b8728 := hb (x (-9) 13)
      have b8729 := hb (x (-8) 12)
      clear * - r8723 e8724 e8725 b8726 b8727 b8728 b8729 d8710 d8693
      omega
    have d8730 : (x (-11) 3).toNat = 0 := by
      have r8731 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8732 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
      have e8733 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
      have b8734 := hb (x (-11) 3)
      have b8735 := hb (x (-10) 2)
      have b8736 := hb (x (-9) 13)
      have b8737 := hb (x (-8) 12)
      clear * - r8731 e8732 e8733 b8734 b8735 b8736 b8737 d8710 d8722 d8693
      omega
    have d8738 : (x (-11) 3 && x (-11) 14).toNat = 0 := by
      have r8739 := hand1 (x (-11) 3) (x (-11) 14)
      have b8740 := hb (x (-11) 3)
      have b8741 := hb (x (-11) 3 && x (-11) 14)
      clear * - r8739 b8740 b8741 d8730
      omega
    have d8742 : (x (-11) 11).toNat = 0 := by
      have r8743 : (x (-11) 11).toNat ≤ (x (-11) 3).toNat := himp _ _ (hp11 (-11))
      have b8744 := hb (x (-11) 3)
      have b8745 := hb (x (-11) 11)
      clear * - r8743 b8744 b8745 d8730
      omega
    have d8746 : (x (-9) 1 && x (-9) 12).toNat = 0 := by
      have r8747 := hand1 (x (-9) 1) (x (-9) 12)
      have b8748 := hb (x (-9) 1)
      have b8749 := hb (x (-9) 1 && x (-9) 12)
      clear * - r8747 b8748 b8749 d8685
      omega
    have d8750 : (x (-10) 3).toNat = 0 := by
      have r8751 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8752 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
      have e8753 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
      have b8754 := hb (x (-10) 3)
      have b8755 := hb (x (-9) 2)
      have b8756 := hb (x (-8) 13)
      have b8757 := hb (x (-7) 12)
      clear * - r8751 e8752 e8753 b8754 b8755 b8756 b8757 d8652 d8656 d8664
      omega
    have d8758 : (x (-10) 3 && x (-10) 14).toNat = 0 := by
      have r8759 := hand1 (x (-10) 3) (x (-10) 14)
      have b8760 := hb (x (-10) 3)
      have b8761 := hb (x (-10) 3 && x (-10) 14)
      clear * - r8759 b8760 b8761 d8750
      omega
    have d8762 : (x (-11) 4).toNat = 1 := by
      have r8763 : 1 ≤ (x (-7) 11).toNat + (x (-8) 1 && x (-8) 12).toNat + (x (-9) 2 && x (-9) 13).toNat + (x (-10) 3 && x (-10) 14).toNat + (x (-11) 4).toNat := by have q := hcov11 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8764 := hb (x (-11) 4)
      have b8765 := hb (x (-7) 11)
      have b8766 := hb (x (-8) 1 && x (-8) 12)
      have b8767 := hb (x (-9) 2 && x (-9) 13)
      have b8768 := hb (x (-10) 3 && x (-10) 14)
      clear * - r8763 b8764 b8765 b8766 b8767 b8768 d8629 d8718 d8672 d8758
      omega
    have d8769 : (x (-11) 12).toNat = 1 := by
      have r8770 : (x (-11) 4).toNat ≤ (x (-11) 12).toNat := himp _ _ (hp4 (-11))
      have b8771 := hb (x (-11) 4)
      have b8772 := hb (x (-11) 12)
      clear * - r8770 b8771 b8772 d8762
      omega
    have d8773 : (x (-12) 13).toNat = 0 := by
      have r8774 : (x (-11) 12).toNat + (x (-12) 1 && x (-12) 13).toNat + (x (-13) 2 && x (-13) 14).toNat + (x (-14) 3).toNat = 1 := by have q := hd12 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8775 : (x (-12) 1 && x (-12) 13).toNat = (x (-12) 13).toNat := handr _ _ (fun h => hp13 (-12) (h))
      have e8776 : (x (-13) 2 && x (-13) 14).toNat = (x (-13) 2).toNat := handl _ _ (fun h => hp2 (-13) (h))
      have b8777 := hb (x (-14) 3)
      have b8778 := hb (x (-13) 2)
      have b8779 := hb (x (-12) 13)
      have b8780 := hb (x (-11) 12)
      clear * - r8774 e8775 e8776 b8777 b8778 b8779 b8780 d8769
      omega
    have d8781 : (x (-13) 2).toNat = 0 := by
      have r8782 : (x (-11) 12).toNat + (x (-12) 1 && x (-12) 13).toNat + (x (-13) 2 && x (-13) 14).toNat + (x (-14) 3).toNat = 1 := by have q := hd12 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8783 : (x (-12) 1 && x (-12) 13).toNat = (x (-12) 13).toNat := handr _ _ (fun h => hp13 (-12) (h))
      have e8784 : (x (-13) 2 && x (-13) 14).toNat = (x (-13) 2).toNat := handl _ _ (fun h => hp2 (-13) (h))
      have b8785 := hb (x (-14) 3)
      have b8786 := hb (x (-13) 2)
      have b8787 := hb (x (-12) 13)
      have b8788 := hb (x (-11) 12)
      clear * - r8782 e8783 e8784 b8785 b8786 b8787 b8788 d8769 d8773
      omega
    have d8789 : (x (-13) 2 && x (-13) 13).toNat = 0 := by
      have r8790 := hand1 (x (-13) 2) (x (-13) 13)
      have b8791 := hb (x (-13) 2)
      have b8792 := hb (x (-13) 2 && x (-13) 13)
      clear * - r8790 b8791 b8792 d8781
      omega
    have d8793 : (x (-13) 2 && x (-13) 12).toNat = 0 := by
      have r8794 := hand1 (x (-13) 2) (x (-13) 12)
      have b8795 := hb (x (-13) 2)
      have b8796 := hb (x (-13) 2 && x (-13) 12)
      clear * - r8794 b8795 b8796 d8781
      omega
    have d8797 : (x (-12) 1 && x (-12) 14).toNat = 1 := by
      have r8798 : 1 ≤ (x (-11) 13).toNat + (x (-12) 1 && x (-12) 14).toNat + (x (-13) 2).toNat := by have q := hcov13 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8799 := hb (x (-13) 2)
      have b8800 := hb (x (-11) 13)
      have b8801 := hb (x (-12) 1 && x (-12) 14)
      clear * - r8798 b8799 b8800 b8801 d8706 d8781
      omega
    have d8802 : (x (-12) 14).toNat = 1 := by
      have r8803 := hand2 (x (-12) 1) (x (-12) 14)
      have b8804 := hb (x (-12) 14)
      have b8805 := hb (x (-12) 1 && x (-12) 14)
      clear * - r8803 b8804 b8805 d8797
      omega
    have d8806 : (x (-13) 1).toNat = 0 := by
      have r8807 : (x (-12) 14).toNat + (x (-13) 1).toNat = 1 := by have q := hd14 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8808 := hb (x (-13) 1)
      have b8809 := hb (x (-12) 14)
      clear * - r8807 b8808 b8809 d8802
      omega
    have d8810 : (x (-13) 1 && x (-13) 14).toNat = 0 := by
      have r8811 := hand1 (x (-13) 1) (x (-13) 14)
      have b8812 := hb (x (-13) 1)
      have b8813 := hb (x (-13) 1 && x (-13) 14)
      clear * - r8811 b8812 b8813 d8806
      omega
    have d8814 : (x (-14) 2).toNat = 1 := by
      have r8815 : 1 ≤ (x (-12) 13).toNat + (x (-13) 1 && x (-13) 14).toNat + (x (-14) 2).toNat := by have q := hcov13 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8816 := hb (x (-14) 2)
      have b8817 := hb (x (-12) 13)
      have b8818 := hb (x (-13) 1 && x (-13) 14)
      clear * - r8815 b8816 b8817 b8818 d8773 d8810
      omega
    have d8819 : (x (-14) 14).toNat = 1 := by
      have r8820 : (x (-14) 2).toNat ≤ (x (-14) 14).toNat := himp _ _ (hp2 (-14))
      have b8821 := hb (x (-14) 2)
      have b8822 := hb (x (-14) 14)
      clear * - r8820 b8821 b8822 d8814
      omega
    have d8823 : (x (-15) 1).toNat = 0 := by
      have r8824 : (x (-14) 14).toNat + (x (-15) 1).toNat = 1 := by have q := hd14 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8825 := hb (x (-15) 1)
      have b8826 := hb (x (-14) 14)
      clear * - r8824 b8825 b8826 d8819
      omega
    have d8827 : (x (-15) 13).toNat = 0 := by
      have r8828 : (x (-15) 13).toNat ≤ (x (-15) 1).toNat := himp _ _ (hp13 (-15))
      have b8829 := hb (x (-15) 1)
      have b8830 := hb (x (-15) 13)
      clear * - r8828 b8829 b8830 d8823
      omega
    have d8831 : (x (-12) 12).toNat = 0 := by
      have r8832 : (x (-12) 12).toNat + (x (-13) 1 && x (-13) 13).toNat + (x (-14) 2 && x (-14) 14).toNat + (x (-15) 3).toNat = 1 := by have q := hd12 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8833 : (x (-13) 1 && x (-13) 13).toNat = (x (-13) 13).toNat := handr _ _ (fun h => hp13 (-13) (h))
      have e8834 : (x (-14) 2 && x (-14) 14).toNat = (x (-14) 2).toNat := handl _ _ (fun h => hp2 (-14) (h))
      have b8835 := hb (x (-15) 3)
      have b8836 := hb (x (-14) 2)
      have b8837 := hb (x (-13) 13)
      have b8838 := hb (x (-12) 12)
      clear * - r8832 e8833 e8834 b8835 b8836 b8837 b8838 d8814
      omega
    have d8839 : (x (-12) 1 && x (-12) 12).toNat = 0 := by
      have r8840 := hand2 (x (-12) 1) (x (-12) 12)
      have b8841 := hb (x (-12) 12)
      have b8842 := hb (x (-12) 1 && x (-12) 12)
      clear * - r8840 b8841 b8842 d8831
      omega
    have d8843 : (x (-12) 4).toNat = 0 := by
      have r8844 : (x (-12) 4).toNat ≤ (x (-12) 12).toNat := himp _ _ (hp4 (-12))
      have b8845 := hb (x (-12) 4)
      have b8846 := hb (x (-12) 12)
      clear * - r8844 b8845 b8846 d8831
      omega
    have d8847 : (x (-10) 2 && x (-10) 13).toNat = 1 := by
      have r8848 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := by have q := hcov11 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8849 := hb (x (-12) 4)
      have b8850 := hb (x (-8) 11)
      have b8851 := hb (x (-9) 1 && x (-9) 12)
      have b8852 := hb (x (-10) 2 && x (-10) 13)
      have b8853 := hb (x (-11) 3 && x (-11) 14)
      clear * - r8848 b8849 b8850 b8851 b8852 b8853 d8617 d8746 d8738 d8843
      omega
    have d8854 : (x (-10) 13).toNat = 1 := by
      have r8855 := hand2 (x (-10) 2) (x (-10) 13)
      have b8856 := hb (x (-10) 13)
      have b8857 := hb (x (-10) 2 && x (-10) 13)
      clear * - r8855 b8856 b8857 d8847
      omega
    have d8858 : (x (-9) 12).toNat = 0 := by
      have r8859 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8860 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
      have e8861 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
      have b8862 := hb (x (-12) 3)
      have b8863 := hb (x (-11) 2)
      have b8864 := hb (x (-10) 13)
      have b8865 := hb (x (-9) 12)
      clear * - r8859 e8860 e8861 b8862 b8863 b8864 b8865 d8854
      omega
    have d8866 : (x (-11) 2).toNat = 0 := by
      have r8867 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8868 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
      have e8869 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
      have b8870 := hb (x (-12) 3)
      have b8871 := hb (x (-11) 2)
      have b8872 := hb (x (-10) 13)
      have b8873 := hb (x (-9) 12)
      clear * - r8867 e8868 e8869 b8870 b8871 b8872 b8873 d8858 d8854
      omega
    have d8874 : (x (-11) 10).toNat = 0 := by
      have r8875 : (x (-11) 10).toNat ≤ (x (-11) 2).toNat := himp _ _ (hp10 (-11))
      have b8876 := hb (x (-11) 2)
      have b8877 := hb (x (-11) 10)
      clear * - r8875 b8876 b8877 d8866
      omega
    have d8878 : (x (-12) 3).toNat = 0 := by
      have r8879 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8880 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
      have e8881 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
      have b8882 := hb (x (-12) 3)
      have b8883 := hb (x (-11) 2)
      have b8884 := hb (x (-10) 13)
      have b8885 := hb (x (-9) 12)
      clear * - r8879 e8880 e8881 b8882 b8883 b8884 b8885 d8858 d8854 d8866
      omega
    have d8886 : (x (-12) 11).toNat = 0 := by
      have r8887 : (x (-12) 11).toNat ≤ (x (-12) 3).toNat := himp _ _ (hp11 (-12))
      have b8888 := hb (x (-12) 3)
      have b8889 := hb (x (-12) 11)
      clear * - r8887 b8888 b8889 d8878
      omega
    have d8890 : (x (-12) 1 && x (-12) 11).toNat = 0 := by
      have r8891 := hand2 (x (-12) 1) (x (-12) 11)
      have b8892 := hb (x (-12) 11)
      have b8893 := hb (x (-12) 1 && x (-12) 11)
      clear * - r8891 b8892 b8893 d8886
      omega
    have d8894 : (x (-14) 3).toNat = 0 := by
      have r8895 : (x (-11) 12).toNat + (x (-12) 1 && x (-12) 13).toNat + (x (-13) 2 && x (-13) 14).toNat + (x (-14) 3).toNat = 1 := by have q := hd12 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8896 : (x (-12) 1 && x (-12) 13).toNat = (x (-12) 13).toNat := handr _ _ (fun h => hp13 (-12) (h))
      have e8897 : (x (-13) 2 && x (-13) 14).toNat = (x (-13) 2).toNat := handl _ _ (fun h => hp2 (-13) (h))
      have b8898 := hb (x (-14) 3)
      have b8899 := hb (x (-13) 2)
      have b8900 := hb (x (-12) 13)
      have b8901 := hb (x (-11) 12)
      clear * - r8895 e8896 e8897 b8898 b8899 b8900 b8901 d8769 d8773 d8781
      omega
    have d8902 : (x (-14) 3 && x (-14) 14).toNat = 0 := by
      have r8903 := hand1 (x (-14) 3) (x (-14) 14)
      have b8904 := hb (x (-14) 3)
      have b8905 := hb (x (-14) 3 && x (-14) 14)
      clear * - r8903 b8904 b8905 d8894
      omega
    have d8906 : (x (-15) 4).toNat = 1 := by
      have r8907 : 1 ≤ (x (-11) 11).toNat + (x (-12) 1 && x (-12) 12).toNat + (x (-13) 2 && x (-13) 13).toNat + (x (-14) 3 && x (-14) 14).toNat + (x (-15) 4).toNat := by have q := hcov11 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8908 := hb (x (-15) 4)
      have b8909 := hb (x (-11) 11)
      have b8910 := hb (x (-12) 1 && x (-12) 12)
      have b8911 := hb (x (-13) 2 && x (-13) 13)
      have b8912 := hb (x (-14) 3 && x (-14) 14)
      clear * - r8907 b8908 b8909 b8910 b8911 b8912 d8742 d8839 d8789 d8902
      omega
    have d8913 : (x (-15) 12).toNat = 1 := by
      have r8914 : (x (-15) 4).toNat ≤ (x (-15) 12).toNat := himp _ _ (hp4 (-15))
      have b8915 := hb (x (-15) 4)
      have b8916 := hb (x (-15) 12)
      clear * - r8914 b8915 b8916 d8906
      omega
    have d8917 : (x (-16) 13).toNat = 0 := by
      have r8918 : (x (-15) 12).toNat + (x (-16) 1 && x (-16) 13).toNat + (x (-17) 2 && x (-17) 14).toNat + (x (-18) 3).toNat = 1 := by have q := hd12 (-15); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8919 : (x (-16) 1 && x (-16) 13).toNat = (x (-16) 13).toNat := handr _ _ (fun h => hp13 (-16) (h))
      have e8920 : (x (-17) 2 && x (-17) 14).toNat = (x (-17) 2).toNat := handl _ _ (fun h => hp2 (-17) (h))
      have b8921 := hb (x (-18) 3)
      have b8922 := hb (x (-17) 2)
      have b8923 := hb (x (-16) 13)
      have b8924 := hb (x (-15) 12)
      clear * - r8918 e8919 e8920 b8921 b8922 b8923 b8924 d8913
      omega
    have d8925 : (x (-16) 5).toNat = 0 := by
      have r8926 : (x (-16) 5).toNat ≤ (x (-16) 13).toNat := himp _ _ (hp5 (-16))
      have b8927 := hb (x (-16) 5)
      have b8928 := hb (x (-16) 13)
      clear * - r8926 b8927 b8928 d8917
      omega
    have d8929 : (x (-17) 2).toNat = 0 := by
      have r8930 : (x (-15) 12).toNat + (x (-16) 1 && x (-16) 13).toNat + (x (-17) 2 && x (-17) 14).toNat + (x (-18) 3).toNat = 1 := by have q := hd12 (-15); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8931 : (x (-16) 1 && x (-16) 13).toNat = (x (-16) 13).toNat := handr _ _ (fun h => hp13 (-16) (h))
      have e8932 : (x (-17) 2 && x (-17) 14).toNat = (x (-17) 2).toNat := handl _ _ (fun h => hp2 (-17) (h))
      have b8933 := hb (x (-18) 3)
      have b8934 := hb (x (-17) 2)
      have b8935 := hb (x (-16) 13)
      have b8936 := hb (x (-15) 12)
      clear * - r8930 e8931 e8932 b8933 b8934 b8935 b8936 d8913 d8917
      omega
    have d8937 : (x (-16) 1 && x (-16) 14).toNat = 1 := by
      have r8938 : 1 ≤ (x (-15) 13).toNat + (x (-16) 1 && x (-16) 14).toNat + (x (-17) 2).toNat := by have q := hcov13 (-15); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8939 := hb (x (-17) 2)
      have b8940 := hb (x (-15) 13)
      have b8941 := hb (x (-16) 1 && x (-16) 14)
      clear * - r8938 b8939 b8940 b8941 d8827 d8929
      omega
    have d8942 : (x (-16) 1).toNat = 1 := by
      have r8943 := hand1 (x (-16) 1) (x (-16) 14)
      have b8944 := hb (x (-16) 1)
      have b8945 := hb (x (-16) 1 && x (-16) 14)
      clear * - r8943 b8944 b8945 d8937
      omega
    have d8946 : (x (-15) 14).toNat = 0 := by
      have r8947 : (x (-15) 14).toNat + (x (-16) 1).toNat = 1 := by have q := hd14 (-15); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8948 := hb (x (-16) 1)
      have b8949 := hb (x (-15) 14)
      clear * - r8947 b8948 b8949 d8942
      omega
    have d8950 : (x (-15) 4 && x (-15) 14).toNat = 0 := by
      have r8951 := hand2 (x (-15) 4) (x (-15) 14)
      have b8952 := hb (x (-15) 14)
      have b8953 := hb (x (-15) 4 && x (-15) 14)
      clear * - r8951 b8952 b8953 d8946
      omega
    have d8954 : (x (-14) 3 && x (-14) 13).toNat = 1 := by
      have r8955 : 1 ≤ (x (-11) 10).toNat + (x (-12) 1 && x (-12) 11).toNat + (x (-13) 2 && x (-13) 12).toNat + (x (-14) 3 && x (-14) 13).toNat + (x (-15) 4 && x (-15) 14).toNat + (x (-16) 5).toNat := by have q := hcov10 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8956 := hb (x (-16) 5)
      have b8957 := hb (x (-11) 10)
      have b8958 := hb (x (-12) 1 && x (-12) 11)
      have b8959 := hb (x (-13) 2 && x (-13) 12)
      have b8960 := hb (x (-14) 3 && x (-14) 13)
      have b8961 := hb (x (-15) 4 && x (-15) 14)
      clear * - r8955 b8956 b8957 b8958 b8959 b8960 b8961 d8874 d8890 d8793 d8950 d8925
      omega
    have r8962 := hand1 (x (-14) 3) (x (-14) 13)
    have b8963 := hb (x (-14) 3)
    have b8964 := hb (x (-14) 3 && x (-14) 13)
    linarith only [r8962, b8963, b8964, d8954, d8894]
  · have f8965 : (x 0 9).toNat = 1 := by rw [h8459]; rfl
    have d8966 : (x 1 8).toNat = 0 := by
      have r8967 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8968 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e8969 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e8970 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e8971 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e8972 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e8973 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b8974 := hb (x (-6) 7)
      have b8975 := hb (x (-5) 6)
      have b8976 := hb (x (-4) 5)
      have b8977 := hb (x (-3) 4)
      have b8978 := hb (x (-2) 11)
      have b8979 := hb (x (-1) 10)
      have b8980 := hb (x 0 9)
      have b8981 := hb (x 1 8)
      clear * - r8967 e8968 e8969 e8970 e8971 e8972 e8973 b8974 b8975 b8976 b8977 b8978 b8979 b8980 b8981 f8965 g6 g3
      omega
    have d8982 : (x (-3) 4).toNat = 0 := by
      have r8983 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8984 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e8985 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e8986 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e8987 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e8988 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e8989 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b8990 := hb (x (-6) 7)
      have b8991 := hb (x (-5) 6)
      have b8992 := hb (x (-4) 5)
      have b8993 := hb (x (-3) 4)
      have b8994 := hb (x (-2) 11)
      have b8995 := hb (x (-1) 10)
      have b8996 := hb (x 0 9)
      have b8997 := hb (x 1 8)
      clear * - r8983 e8984 e8985 e8986 e8987 e8988 e8989 b8990 b8991 b8992 b8993 b8994 b8995 b8996 b8997 d8966 f8965 g6 g3
      omega
    have d8998 : (x (-3) 4 && x (-3) 10).toNat = 0 := by
      have r8999 := hand1 (x (-3) 4) (x (-3) 10)
      have b9000 := hb (x (-3) 4)
      have b9001 := hb (x (-3) 4 && x (-3) 10)
      clear * - r8999 b9000 b9001 d8982
      omega
    have d9002 : (x 0 1 && x 0 12).toNat = 1 := by
      have r9003 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9004 := hb (x (-3) 4)
      have b9005 := hb (x 1 11)
      have b9006 := hb (x 0 1 && x 0 12)
      have b9007 := hb (x (-1) 2 && x (-1) 13)
      have b9008 := hb (x (-2) 3 && x (-2) 14)
      clear * - r9003 b9004 b9005 b9006 b9007 b9008 g15 g85 g86 d8982
      omega
    have d9009 : (x 0 12).toNat = 1 := by
      have r9010 := hand2 (x 0 1) (x 0 12)
      have b9011 := hb (x 0 12)
      have b9012 := hb (x 0 1 && x 0 12)
      clear * - r9010 b9011 b9012 d9002
      omega
    have d9013 : (x (-2) 2).toNat = 0 := by
      have r9014 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9015 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e9016 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have b9017 := hb (x (-3) 3)
      have b9018 := hb (x (-2) 2)
      have b9019 := hb (x (-1) 13)
      have b9020 := hb (x 0 12)
      clear * - r9014 e9015 e9016 b9017 b9018 b9019 b9020 d9009 g8
      omega
    have d9021 : (x (-2) 2 && x (-2) 12).toNat = 0 := by
      have r9022 := hand1 (x (-2) 2) (x (-2) 12)
      have b9023 := hb (x (-2) 2)
      have b9024 := hb (x (-2) 2 && x (-2) 12)
      clear * - r9022 b9023 b9024 d9013
      omega
    have d9025 : (x 0 10).toNat = 1 := by
      have r9026 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9027 := hb (x (-5) 5)
      have b9028 := hb (x 0 10)
      have b9029 := hb (x (-1) 1 && x (-1) 11)
      have b9030 := hb (x (-2) 2 && x (-2) 12)
      have b9031 := hb (x (-3) 3 && x (-3) 13)
      have b9032 := hb (x (-4) 4 && x (-4) 14)
      clear * - r9026 b9027 b9028 b9029 b9030 b9031 b9032 g81 d9021 g82 d8351 d8371
      omega
    have d9033 : (x 2 8).toNat = 0 := by
      have r9034 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9035 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e9036 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e9037 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e9038 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e9039 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e9040 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b9041 := hb (x (-5) 7)
      have b9042 := hb (x (-4) 6)
      have b9043 := hb (x (-3) 5)
      have b9044 := hb (x (-2) 4)
      have b9045 := hb (x (-1) 11)
      have b9046 := hb (x 0 10)
      have b9047 := hb (x 1 9)
      have b9048 := hb (x 2 8)
      clear * - r9034 e9035 e9036 e9037 e9038 e9039 e9040 b9041 b9042 b9043 b9044 b9045 b9046 b9047 b9048 g14 d9025 g7 g0
      omega
    have d9049 : (x (-2) 4).toNat = 0 := by
      have r9050 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9051 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e9052 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e9053 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e9054 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e9055 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e9056 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b9057 := hb (x (-5) 7)
      have b9058 := hb (x (-4) 6)
      have b9059 := hb (x (-3) 5)
      have b9060 := hb (x (-2) 4)
      have b9061 := hb (x (-1) 11)
      have b9062 := hb (x 0 10)
      have b9063 := hb (x 1 9)
      have b9064 := hb (x 2 8)
      clear * - r9050 e9051 e9052 e9053 e9054 e9055 e9056 b9057 b9058 b9059 b9060 b9061 b9062 b9063 b9064 d9033 g14 d9025 g7 g0
      omega
    have d9065 : (x (-2) 4 && x (-2) 9).toNat = 0 := by
      have r9066 := hand1 (x (-2) 4) (x (-2) 9)
      have b9067 := hb (x (-2) 4)
      have b9068 := hb (x (-2) 4 && x (-2) 9)
      clear * - r9066 b9067 b9068 d9049
      omega
    have d9069 : (x (-4) 6).toNat = 0 := by
      have r9070 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9071 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e9072 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e9073 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e9074 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e9075 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e9076 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b9077 := hb (x (-5) 7)
      have b9078 := hb (x (-4) 6)
      have b9079 := hb (x (-3) 5)
      have b9080 := hb (x (-2) 4)
      have b9081 := hb (x (-1) 11)
      have b9082 := hb (x 0 10)
      have b9083 := hb (x 1 9)
      have b9084 := hb (x 2 8)
      clear * - r9070 e9071 e9072 e9073 e9074 e9075 e9076 b9077 b9078 b9079 b9080 b9081 b9082 b9083 b9084 d9033 g14 d9025 g7 d9049 g0
      omega
    have d9085 : (x (-4) 6 && x (-4) 11).toNat = 0 := by
      have r9086 := hand1 (x (-4) 6) (x (-4) 11)
      have b9087 := hb (x (-4) 6)
      have b9088 := hb (x (-4) 6 && x (-4) 11)
      clear * - r9086 b9087 b9088 d9069
      omega
    have d9089 : (x (-5) 7).toNat = 0 := by
      have r9090 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9091 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e9092 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e9093 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e9094 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e9095 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e9096 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b9097 := hb (x (-5) 7)
      have b9098 := hb (x (-4) 6)
      have b9099 := hb (x (-3) 5)
      have b9100 := hb (x (-2) 4)
      have b9101 := hb (x (-1) 11)
      have b9102 := hb (x 0 10)
      have b9103 := hb (x 1 9)
      have b9104 := hb (x 2 8)
      clear * - r9090 e9091 e9092 e9093 e9094 e9095 e9096 b9097 b9098 b9099 b9100 b9101 b9102 b9103 b9104 d9033 g14 d9025 g7 d9049 g0 d9069
      omega
    have d9105 : (x (-5) 7 && x (-5) 12).toNat = 0 := by
      have r9106 := hand1 (x (-5) 7) (x (-5) 12)
      have b9107 := hb (x (-5) 7)
      have b9108 := hb (x (-5) 7 && x (-5) 12)
      clear * - r9106 b9107 b9108 d9089
      omega
    have d9109 : (x (-2) 2 && x (-2) 9).toNat = 0 := by
      have r9110 := hand1 (x (-2) 2) (x (-2) 9)
      have b9111 := hb (x (-2) 2)
      have b9112 := hb (x (-2) 2 && x (-2) 9)
      clear * - r9110 b9111 b9112 d9013
      omega
    have d9113 : (x (-2) 2 && x (-2) 8).toNat = 0 := by
      have r9114 := hand1 (x (-2) 2) (x (-2) 8)
      have b9115 := hb (x (-2) 2)
      have b9116 := hb (x (-2) 2 && x (-2) 8)
      clear * - r9114 b9115 b9116 d9013
      omega
    have d9117 : (x (-2) 2 && x (-2) 6).toNat = 0 := by
      have r9118 := hand1 (x (-2) 2) (x (-2) 6)
      have b9119 := hb (x (-2) 2)
      have b9120 := hb (x (-2) 2 && x (-2) 6)
      clear * - r9118 b9119 b9120 d9013
      omega
    have d9121 : (x (-3) 3).toNat = 0 := by
      have r9122 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9123 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e9124 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have b9125 := hb (x (-3) 3)
      have b9126 := hb (x (-2) 2)
      have b9127 := hb (x (-1) 13)
      have b9128 := hb (x 0 12)
      clear * - r9122 e9123 e9124 b9125 b9126 b9127 b9128 d9009 g8 d9013
      omega
    have d9129 : (x (-3) 3 && x (-3) 10).toNat = 0 := by
      have r9130 := hand1 (x (-3) 3) (x (-3) 10)
      have b9131 := hb (x (-3) 3)
      have b9132 := hb (x (-3) 3 && x (-3) 10)
      clear * - r9130 b9131 b9132 d9121
      omega
    have d9133 : (x (-4) 5).toNat = 0 := by
      have r9134 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9135 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e9136 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e9137 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e9138 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e9139 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e9140 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b9141 := hb (x (-6) 7)
      have b9142 := hb (x (-5) 6)
      have b9143 := hb (x (-4) 5)
      have b9144 := hb (x (-3) 4)
      have b9145 := hb (x (-2) 11)
      have b9146 := hb (x (-1) 10)
      have b9147 := hb (x 0 9)
      have b9148 := hb (x 1 8)
      clear * - r9134 e9135 e9136 e9137 e9138 e9139 e9140 b9141 b9142 b9143 b9144 b9145 b9146 b9147 b9148 d8966 f8965 g6 g3 d8982
      omega
    have d9149 : (x (-4) 5 && x (-4) 11).toNat = 0 := by
      have r9150 := hand1 (x (-4) 5) (x (-4) 11)
      have b9151 := hb (x (-4) 5)
      have b9152 := hb (x (-4) 5 && x (-4) 11)
      clear * - r9150 b9151 b9152 d9133
      omega
    have d9153 : (x (-5) 6).toNat = 0 := by
      have r9154 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9155 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e9156 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e9157 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e9158 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e9159 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e9160 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b9161 := hb (x (-6) 7)
      have b9162 := hb (x (-5) 6)
      have b9163 := hb (x (-4) 5)
      have b9164 := hb (x (-3) 4)
      have b9165 := hb (x (-2) 11)
      have b9166 := hb (x (-1) 10)
      have b9167 := hb (x 0 9)
      have b9168 := hb (x 1 8)
      clear * - r9154 e9155 e9156 e9157 e9158 e9159 e9160 b9161 b9162 b9163 b9164 b9165 b9166 b9167 b9168 d8966 f8965 g6 g3 d8982 d9133
      omega
    have d9169 : (x (-5) 6 && x (-5) 12).toNat = 0 := by
      have r9170 := hand1 (x (-5) 6) (x (-5) 12)
      have b9171 := hb (x (-5) 6)
      have b9172 := hb (x (-5) 6 && x (-5) 12)
      clear * - r9170 b9171 b9172 d9153
      omega
    have d9173 : (x (-6) 7).toNat = 0 := by
      have r9174 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9175 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e9176 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e9177 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e9178 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e9179 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e9180 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b9181 := hb (x (-6) 7)
      have b9182 := hb (x (-5) 6)
      have b9183 := hb (x (-4) 5)
      have b9184 := hb (x (-3) 4)
      have b9185 := hb (x (-2) 11)
      have b9186 := hb (x (-1) 10)
      have b9187 := hb (x 0 9)
      have b9188 := hb (x 1 8)
      clear * - r9174 e9175 e9176 e9177 e9178 e9179 e9180 b9181 b9182 b9183 b9184 b9185 b9186 b9187 b9188 d8966 f8965 g6 g3 d8982 d9133 d9153
      omega
    have d9189 : (x (-6) 7 && x (-6) 13).toNat = 0 := by
      have r9190 := hand1 (x (-6) 7) (x (-6) 13)
      have b9191 := hb (x (-6) 7)
      have b9192 := hb (x (-6) 7 && x (-6) 13)
      clear * - r9190 b9191 b9192 d9173
      omega
    have d9193 : (x (-8) 8).toNat = 1 := by
      have r9194 : 1 ≤ (x 0 7).toNat + (x (-1) 1 && x (-1) 8).toNat + (x (-2) 2 && x (-2) 9).toNat + (x (-3) 3 && x (-3) 10).toNat + (x (-4) 4 && x (-4) 11).toNat + (x (-5) 5 && x (-5) 12).toNat + (x (-6) 6 && x (-6) 13).toNat + (x (-7) 7 && x (-7) 14).toNat + (x (-8) 8).toNat := by have q := hcov7 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9195 := hb (x (-8) 8)
      have b9196 := hb (x 0 7)
      have b9197 := hb (x (-1) 1 && x (-1) 8)
      have b9198 := hb (x (-2) 2 && x (-2) 9)
      have b9199 := hb (x (-3) 3 && x (-3) 10)
      have b9200 := hb (x (-4) 4 && x (-4) 11)
      have b9201 := hb (x (-5) 5 && x (-5) 12)
      have b9202 := hb (x (-6) 6 && x (-6) 13)
      have b9203 := hb (x (-7) 7 && x (-7) 14)
      clear * - r9194 b9195 b9196 b9197 b9198 b9199 b9200 b9201 b9202 b9203 g11 g70 d9109 d9129 d8359 d8391 d8419 d8447
      omega
    have d9204 : (x (-9) 9).toNat = 0 := by
      have r9205 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9206 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
      have e9207 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
      have e9208 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
      have e9209 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
      have e9210 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
      have e9211 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
      have b9212 := hb (x (-15) 7)
      have b9213 := hb (x (-14) 6)
      have b9214 := hb (x (-13) 5)
      have b9215 := hb (x (-12) 4)
      have b9216 := hb (x (-11) 11)
      have b9217 := hb (x (-10) 10)
      have b9218 := hb (x (-9) 9)
      have b9219 := hb (x (-8) 8)
      clear * - r9205 e9206 e9207 e9208 e9209 e9210 e9211 b9212 b9213 b9214 b9215 b9216 b9217 b9218 b9219 d9193
      omega
    have d9220 : (x (-9) 9 && x (-9) 13).toNat = 0 := by
      have r9221 := hand1 (x (-9) 9) (x (-9) 13)
      have b9222 := hb (x (-9) 9)
      have b9223 := hb (x (-9) 9 && x (-9) 13)
      clear * - r9221 b9222 b9223 d9204
      omega
    have d9224 : (x (-10) 10).toNat = 0 := by
      have r9225 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9226 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
      have e9227 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
      have e9228 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
      have e9229 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
      have e9230 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
      have e9231 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
      have b9232 := hb (x (-15) 7)
      have b9233 := hb (x (-14) 6)
      have b9234 := hb (x (-13) 5)
      have b9235 := hb (x (-12) 4)
      have b9236 := hb (x (-11) 11)
      have b9237 := hb (x (-10) 10)
      have b9238 := hb (x (-9) 9)
      have b9239 := hb (x (-8) 8)
      clear * - r9225 e9226 e9227 e9228 e9229 e9230 e9231 b9232 b9233 b9234 b9235 b9236 b9237 b9238 b9239 d9193 d9204
      omega
    have d9240 : (x (-11) 11).toNat = 0 := by
      have r9241 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9242 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
      have e9243 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
      have e9244 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
      have e9245 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
      have e9246 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
      have e9247 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
      have b9248 := hb (x (-15) 7)
      have b9249 := hb (x (-14) 6)
      have b9250 := hb (x (-13) 5)
      have b9251 := hb (x (-12) 4)
      have b9252 := hb (x (-11) 11)
      have b9253 := hb (x (-10) 10)
      have b9254 := hb (x (-9) 9)
      have b9255 := hb (x (-8) 8)
      clear * - r9241 e9242 e9243 e9244 e9245 e9246 e9247 b9248 b9249 b9250 b9251 b9252 b9253 b9254 b9255 d9193 d9204 d9224
      omega
    have d9256 : (x (-8) 8 && x (-8) 14).toNat = 1 := by
      have r9257 : 1 ≤ (x 0 6).toNat + (x (-1) 1 && x (-1) 7).toNat + (x (-2) 2 && x (-2) 8).toNat + (x (-3) 3 && x (-3) 9).toNat + (x (-4) 4 && x (-4) 10).toNat + (x (-5) 5 && x (-5) 11).toNat + (x (-6) 6 && x (-6) 12).toNat + (x (-7) 7 && x (-7) 13).toNat + (x (-8) 8 && x (-8) 14).toNat + (x (-9) 9).toNat := by have q := hcov6 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9258 := hb (x (-9) 9)
      have b9259 := hb (x 0 6)
      have b9260 := hb (x (-1) 1 && x (-1) 7)
      have b9261 := hb (x (-2) 2 && x (-2) 8)
      have b9262 := hb (x (-3) 3 && x (-3) 9)
      have b9263 := hb (x (-4) 4 && x (-4) 10)
      have b9264 := hb (x (-5) 5 && x (-5) 11)
      have b9265 := hb (x (-6) 6 && x (-6) 12)
      have b9266 := hb (x (-7) 7 && x (-7) 13)
      have b9267 := hb (x (-8) 8 && x (-8) 14)
      clear * - r9257 b9258 b9259 b9260 b9261 b9262 b9263 b9264 b9265 b9266 b9267 g10 g50 d9113 g51 d8363 d8395 d8423 d8451 d9204
      omega
    have d9268 : (x (-8) 14).toNat = 1 := by
      have r9269 := hand2 (x (-8) 8) (x (-8) 14)
      have b9270 := hb (x (-8) 14)
      have b9271 := hb (x (-8) 8 && x (-8) 14)
      clear * - r9269 b9270 b9271 d9256
      omega
    have d9272 : (x (-9) 1).toNat = 0 := by
      have r9273 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9274 := hb (x (-9) 1)
      have b9275 := hb (x (-8) 14)
      clear * - r9273 b9274 b9275 d9268
      omega
    have d9276 : (x (-9) 1 && x (-9) 14).toNat = 0 := by
      have r9277 := hand1 (x (-9) 1) (x (-9) 14)
      have b9278 := hb (x (-9) 1)
      have b9279 := hb (x (-9) 1 && x (-9) 14)
      clear * - r9277 b9278 b9279 d9272
      omega
    have d9280 : (x (-9) 13).toNat = 0 := by
      have r9281 : (x (-9) 13).toNat ≤ (x (-9) 1).toNat := himp _ _ (hp13 (-9))
      have b9282 := hb (x (-9) 1)
      have b9283 := hb (x (-9) 13)
      clear * - r9281 b9282 b9283 d9272
      omega
    have d9284 : (x (-8) 8 && x (-8) 12).toNat = 1 := by
      have r9285 : 1 ≤ (x 0 4).toNat + (x (-1) 1 && x (-1) 5).toNat + (x (-2) 2 && x (-2) 6).toNat + (x (-3) 3 && x (-3) 7).toNat + (x (-4) 4 && x (-4) 8).toNat + (x (-5) 5 && x (-5) 9).toNat + (x (-6) 6 && x (-6) 10).toNat + (x (-7) 7 && x (-7) 11).toNat + (x (-8) 8 && x (-8) 12).toNat + (x (-9) 9 && x (-9) 13).toNat + (x (-10) 10 && x (-10) 14).toNat + (x (-11) 11).toNat := by have q := hcov4 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9286 : (x (-1) 1 && x (-1) 5).toNat = (x (-1) 5).toNat := handr _ _ (fun h => hp13 (-1) (hp5 (-1) (h)))
      have e9287 : (x (-10) 10 && x (-10) 14).toNat = (x (-10) 10).toNat := handl _ _ (fun h => hp2 (-10) (hp10 (-10) (h)))
      have b9288 := hb (x (-11) 11)
      have b9289 := hb (x (-10) 10)
      have b9290 := hb (x (-1) 5)
      have b9291 := hb (x 0 4)
      have b9292 := hb (x (-2) 2 && x (-2) 6)
      have b9293 := hb (x (-3) 3 && x (-3) 7)
      have b9294 := hb (x (-4) 4 && x (-4) 8)
      have b9295 := hb (x (-5) 5 && x (-5) 9)
      have b9296 := hb (x (-6) 6 && x (-6) 10)
      have b9297 := hb (x (-7) 7 && x (-7) 11)
      have b9298 := hb (x (-8) 8 && x (-8) 12)
      have b9299 := hb (x (-9) 9 && x (-9) 13)
      clear * - r9285 e9286 e9287 b9288 b9289 b9290 b9291 b9292 b9293 b9294 b9295 b9296 b9297 b9298 b9299 g9 g4 d9117 g45 d8367 d8399 d8427 d8455 d9220 d9224 d9240
      omega
    have d9300 : (x (-8) 12).toNat = 1 := by
      have r9301 := hand2 (x (-8) 8) (x (-8) 12)
      have b9302 := hb (x (-8) 12)
      have b9303 := hb (x (-8) 8 && x (-8) 12)
      clear * - r9301 b9302 b9303 d9284
      omega
    have d9304 : (x (-10) 2).toNat = 0 := by
      have r9305 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9306 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
      have e9307 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
      have b9308 := hb (x (-11) 3)
      have b9309 := hb (x (-10) 2)
      have b9310 := hb (x (-9) 13)
      have b9311 := hb (x (-8) 12)
      clear * - r9305 e9306 e9307 b9308 b9309 b9310 b9311 d9300 d9280
      omega
    have d9312 : (x (-8) 13).toNat = 1 := by
      have r9313 : 1 ≤ (x (-8) 13).toNat + (x (-9) 1 && x (-9) 14).toNat + (x (-10) 2).toNat := by have q := hcov13 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9314 := hb (x (-10) 2)
      have b9315 := hb (x (-8) 13)
      have b9316 := hb (x (-9) 1 && x (-9) 14)
      clear * - r9313 b9314 b9315 b9316 d9276 d9304
      omega
    have d9317 : (x (-8) 1).toNat = 1 := by
      have r9318 : (x (-8) 13).toNat ≤ (x (-8) 1).toNat := himp _ _ (hp13 (-8))
      have b9319 := hb (x (-8) 1)
      have b9320 := hb (x (-8) 13)
      clear * - r9318 b9319 b9320 d9312
      omega
    have d9321 : (x (-7) 14).toNat = 0 := by
      have r9322 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9323 := hb (x (-8) 1)
      have b9324 := hb (x (-7) 14)
      clear * - r9322 b9323 b9324 d9317
      omega
    have d9325 : (x (-7) 8 && x (-7) 14).toNat = 0 := by
      have r9326 := hand2 (x (-7) 8) (x (-7) 14)
      have b9327 := hb (x (-7) 14)
      have b9328 := hb (x (-7) 8 && x (-7) 14)
      clear * - r9326 b9327 b9328 d9321
      omega
    have d9329 : (x (-8) 9).toNat = 1 := by
      have r9330 : 1 ≤ (x 1 6).toNat + (x 0 1 && x 0 7).toNat + (x (-1) 2 && x (-1) 8).toNat + (x (-2) 3 && x (-2) 9).toNat + (x (-3) 4 && x (-3) 10).toNat + (x (-4) 5 && x (-4) 11).toNat + (x (-5) 6 && x (-5) 12).toNat + (x (-6) 7 && x (-6) 13).toNat + (x (-7) 8 && x (-7) 14).toNat + (x (-8) 9).toNat := by have q := hcov6 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9331 := hb (x (-8) 9)
      have b9332 := hb (x 1 6)
      have b9333 := hb (x 0 1 && x 0 7)
      have b9334 := hb (x (-1) 2 && x (-1) 8)
      have b9335 := hb (x (-2) 3 && x (-2) 9)
      have b9336 := hb (x (-3) 4 && x (-3) 10)
      have b9337 := hb (x (-4) 5 && x (-4) 11)
      have b9338 := hb (x (-5) 6 && x (-5) 12)
      have b9339 := hb (x (-6) 7 && x (-6) 13)
      have b9340 := hb (x (-7) 8 && x (-7) 14)
      clear * - r9330 b9331 b9332 b9333 b9334 b9335 b9336 b9337 b9338 b9339 b9340 g13 g52 g53 g54 d8998 d9149 d9169 d9189 d9325
      omega
    have d9341 : (x (-7) 8).toNat = 0 := by
      have r9342 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9343 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
      have e9344 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
      have e9345 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
      have e9346 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
      have e9347 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
      have e9348 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
      have b9349 := hb (x (-14) 7)
      have b9350 := hb (x (-13) 6)
      have b9351 := hb (x (-12) 5)
      have b9352 := hb (x (-11) 4)
      have b9353 := hb (x (-10) 11)
      have b9354 := hb (x (-9) 10)
      have b9355 := hb (x (-8) 9)
      have b9356 := hb (x (-7) 8)
      clear * - r9342 e9343 e9344 e9345 e9346 e9347 e9348 b9349 b9350 b9351 b9352 b9353 b9354 b9355 b9356 d9329
      omega
    have d9357 : (x (-9) 10).toNat = 0 := by
      have r9358 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9359 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
      have e9360 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
      have e9361 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
      have e9362 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
      have e9363 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
      have e9364 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
      have b9365 := hb (x (-14) 7)
      have b9366 := hb (x (-13) 6)
      have b9367 := hb (x (-12) 5)
      have b9368 := hb (x (-11) 4)
      have b9369 := hb (x (-10) 11)
      have b9370 := hb (x (-9) 10)
      have b9371 := hb (x (-8) 9)
      have b9372 := hb (x (-7) 8)
      clear * - r9358 e9359 e9360 e9361 e9362 e9363 e9364 b9365 b9366 b9367 b9368 b9369 b9370 b9371 b9372 d9341 d9329
      omega
    have d9373 : (x (-10) 11).toNat = 0 := by
      have r9374 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9375 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
      have e9376 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
      have e9377 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
      have e9378 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
      have e9379 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
      have e9380 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
      have b9381 := hb (x (-14) 7)
      have b9382 := hb (x (-13) 6)
      have b9383 := hb (x (-12) 5)
      have b9384 := hb (x (-11) 4)
      have b9385 := hb (x (-10) 11)
      have b9386 := hb (x (-9) 10)
      have b9387 := hb (x (-8) 9)
      have b9388 := hb (x (-7) 8)
      clear * - r9374 e9375 e9376 e9377 e9378 e9379 e9380 b9381 b9382 b9383 b9384 b9385 b9386 b9387 b9388 d9341 d9329 d9357
      omega
    have d9389 : (x (-11) 4).toNat = 0 := by
      have r9390 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9391 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
      have e9392 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
      have e9393 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
      have e9394 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
      have e9395 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
      have e9396 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
      have b9397 := hb (x (-14) 7)
      have b9398 := hb (x (-13) 6)
      have b9399 := hb (x (-12) 5)
      have b9400 := hb (x (-11) 4)
      have b9401 := hb (x (-10) 11)
      have b9402 := hb (x (-9) 10)
      have b9403 := hb (x (-8) 9)
      have b9404 := hb (x (-7) 8)
      clear * - r9390 e9391 e9392 e9393 e9394 e9395 e9396 b9397 b9398 b9399 b9400 b9401 b9402 b9403 b9404 d9341 d9329 d9357 d9373
      omega
    have d9405 : (x (-11) 4 && x (-11) 14).toNat = 0 := by
      have r9406 := hand1 (x (-11) 4) (x (-11) 14)
      have b9407 := hb (x (-11) 4)
      have b9408 := hb (x (-11) 4 && x (-11) 14)
      clear * - r9406 b9407 b9408 d9389
      omega
    have d9409 : (x (-12) 5).toNat = 0 := by
      have r9410 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9411 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
      have e9412 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
      have e9413 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
      have e9414 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
      have e9415 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
      have e9416 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
      have b9417 := hb (x (-14) 7)
      have b9418 := hb (x (-13) 6)
      have b9419 := hb (x (-12) 5)
      have b9420 := hb (x (-11) 4)
      have b9421 := hb (x (-10) 11)
      have b9422 := hb (x (-9) 10)
      have b9423 := hb (x (-8) 9)
      have b9424 := hb (x (-7) 8)
      clear * - r9410 e9411 e9412 e9413 e9414 e9415 e9416 b9417 b9418 b9419 b9420 b9421 b9422 b9423 b9424 d9341 d9329 d9357 d9373 d9389
      omega
    have d9425 : (x (-7) 9 && x (-7) 14).toNat = 0 := by
      have r9426 := hand2 (x (-7) 9) (x (-7) 14)
      have b9427 := hb (x (-7) 14)
      have b9428 := hb (x (-7) 9 && x (-7) 14)
      clear * - r9426 b9427 b9428 d9321
      omega
    have d9429 : (x (-7) 6).toNat = 0 := by
      have r9430 : (x (-7) 6).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp6 (-7))
      have b9431 := hb (x (-7) 6)
      have b9432 := hb (x (-7) 14)
      clear * - r9430 b9431 b9432 d9321
      omega
    have d9433 : (x (-7) 2).toNat = 0 := by
      have r9434 : (x (-7) 2).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp2 (-7))
      have b9435 := hb (x (-7) 2)
      have b9436 := hb (x (-7) 14)
      clear * - r9434 b9435 b9436 d9321
      omega
    have d9437 : (x (-7) 10).toNat = 0 := by
      have r9438 : (x (-7) 10).toNat ≤ (x (-7) 2).toNat := himp _ _ (hp10 (-7))
      have b9439 := hb (x (-7) 2)
      have b9440 := hb (x (-7) 10)
      clear * - r9438 b9439 b9440 d9433
      omega
    have d9441 : (x (-7) 12).toNat = 0 := by
      have r9442 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9443 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
      have e9444 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
      have b9445 := hb (x (-10) 3)
      have b9446 := hb (x (-9) 2)
      have b9447 := hb (x (-8) 13)
      have b9448 := hb (x (-7) 12)
      clear * - r9442 e9443 e9444 b9445 b9446 b9447 b9448 d9312
      omega
    have d9449 : (x (-9) 2).toNat = 0 := by
      have r9450 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9451 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
      have e9452 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
      have b9453 := hb (x (-10) 3)
      have b9454 := hb (x (-9) 2)
      have b9455 := hb (x (-8) 13)
      have b9456 := hb (x (-7) 12)
      clear * - r9450 e9451 e9452 b9453 b9454 b9455 b9456 d9441 d9312
      omega
    have d9457 : (x (-9) 2 && x (-9) 12).toNat = 0 := by
      have r9458 := hand1 (x (-9) 2) (x (-9) 12)
      have b9459 := hb (x (-9) 2)
      have b9460 := hb (x (-9) 2 && x (-9) 12)
      clear * - r9458 b9459 b9460 d9449
      omega
    have d9461 : (x (-10) 3).toNat = 0 := by
      have r9462 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9463 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
      have e9464 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
      have b9465 := hb (x (-10) 3)
      have b9466 := hb (x (-9) 2)
      have b9467 := hb (x (-8) 13)
      have b9468 := hb (x (-7) 12)
      clear * - r9462 e9463 e9464 b9465 b9466 b9467 b9468 d9441 d9312 d9449
      omega
    have d9469 : (x (-10) 3 && x (-10) 13).toNat = 0 := by
      have r9470 := hand1 (x (-10) 3) (x (-10) 13)
      have b9471 := hb (x (-10) 3)
      have b9472 := hb (x (-10) 3 && x (-10) 13)
      clear * - r9470 b9471 b9472 d9461
      omega
    have d9473 : (x (-8) 1 && x (-8) 11).toNat = 1 := by
      have r9474 : 1 ≤ (x (-7) 10).toNat + (x (-8) 1 && x (-8) 11).toNat + (x (-9) 2 && x (-9) 12).toNat + (x (-10) 3 && x (-10) 13).toNat + (x (-11) 4 && x (-11) 14).toNat + (x (-12) 5).toNat := by have q := hcov10 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9475 := hb (x (-12) 5)
      have b9476 := hb (x (-7) 10)
      have b9477 := hb (x (-8) 1 && x (-8) 11)
      have b9478 := hb (x (-9) 2 && x (-9) 12)
      have b9479 := hb (x (-10) 3 && x (-10) 13)
      have b9480 := hb (x (-11) 4 && x (-11) 14)
      clear * - r9474 b9475 b9476 b9477 b9478 b9479 b9480 d9437 d9457 d9469 d9405 d9409
      omega
    have d9481 : (x (-8) 11).toNat = 1 := by
      have r9482 := hand2 (x (-8) 1) (x (-8) 11)
      have b9483 := hb (x (-8) 11)
      have b9484 := hb (x (-8) 1 && x (-8) 11)
      clear * - r9482 b9483 b9484 d9473
      omega
    have d9485 : (x (-8) 3).toNat = 1 := by
      have r9486 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
      have b9487 := hb (x (-8) 3)
      have b9488 := hb (x (-8) 11)
      clear * - r9486 b9487 b9488 d9481
      omega
    have d9489 : (x (-5) 12).toNat = 0 := by
      have r9490 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9491 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
      have e9492 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
      have b9493 := hb (x (-8) 3)
      have b9494 := hb (x (-7) 2)
      have b9495 := hb (x (-6) 13)
      have b9496 := hb (x (-5) 12)
      clear * - r9490 e9491 e9492 b9493 b9494 b9495 b9496 d9433 d9485
      omega
    have d9497 : (x (-5) 4).toNat = 0 := by
      have r9498 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
      have b9499 := hb (x (-5) 4)
      have b9500 := hb (x (-5) 12)
      clear * - r9498 b9499 b9500 d9489
      omega
    have d9501 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
      have r9502 := hand1 (x (-5) 4) (x (-5) 13)
      have b9503 := hb (x (-5) 4)
      have b9504 := hb (x (-5) 4 && x (-5) 13)
      clear * - r9502 b9503 b9504 d9497
      omega
    have d9505 : (x (-6) 13).toNat = 0 := by
      have r9506 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9507 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
      have e9508 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
      have b9509 := hb (x (-8) 3)
      have b9510 := hb (x (-7) 2)
      have b9511 := hb (x (-6) 13)
      have b9512 := hb (x (-5) 12)
      clear * - r9506 e9507 e9508 b9509 b9510 b9511 b9512 d9489 d9433 d9485
      omega
    have d9513 : (x (-6) 8 && x (-6) 13).toNat = 0 := by
      have r9514 := hand2 (x (-6) 8) (x (-6) 13)
      have b9515 := hb (x (-6) 13)
      have b9516 := hb (x (-6) 8 && x (-6) 13)
      clear * - r9514 b9515 b9516 d9505
      omega
    have d9517 : (x (-8) 10).toNat = 1 := by
      have r9518 : 1 ≤ (x 2 5).toNat + (x 1 1 && x 1 6).toNat + (x 0 2 && x 0 7).toNat + (x (-1) 3 && x (-1) 8).toNat + (x (-2) 4 && x (-2) 9).toNat + (x (-3) 5 && x (-3) 10).toNat + (x (-4) 6 && x (-4) 11).toNat + (x (-5) 7 && x (-5) 12).toNat + (x (-6) 8 && x (-6) 13).toNat + (x (-7) 9 && x (-7) 14).toNat + (x (-8) 10).toNat := by have q := hcov5 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9519 := hb (x (-8) 10)
      have b9520 := hb (x 2 5)
      have b9521 := hb (x 1 1 && x 1 6)
      have b9522 := hb (x 0 2 && x 0 7)
      have b9523 := hb (x (-1) 3 && x (-1) 8)
      have b9524 := hb (x (-2) 4 && x (-2) 9)
      have b9525 := hb (x (-3) 5 && x (-3) 10)
      have b9526 := hb (x (-4) 6 && x (-4) 11)
      have b9527 := hb (x (-5) 7 && x (-5) 12)
      have b9528 := hb (x (-6) 8 && x (-6) 13)
      have b9529 := hb (x (-7) 9 && x (-7) 14)
      clear * - r9518 b9519 b9520 b9521 b9522 b9523 b9524 b9525 b9526 b9527 b9528 b9529 g16 g46 g47 g48 d9065 g49 d9085 d9105 d9513 d9425
      omega
    have d9530 : (x (-8) 2).toNat = 1 := by
      have r9531 : (x (-8) 10).toNat ≤ (x (-8) 2).toNat := himp _ _ (hp10 (-8))
      have b9532 := hb (x (-8) 2)
      have b9533 := hb (x (-8) 10)
      clear * - r9531 b9532 b9533 d9517
      omega
    have d9534 : (x (-6) 12).toNat = 0 := by
      have r9535 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9536 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
      have e9537 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
      have b9538 := hb (x (-9) 3)
      have b9539 := hb (x (-8) 2)
      have b9540 := hb (x (-7) 13)
      have b9541 := hb (x (-6) 12)
      clear * - r9535 e9536 e9537 b9538 b9539 b9540 b9541 d9530
      omega
    have d9542 : (x (-6) 4).toNat = 0 := by
      have r9543 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
      have b9544 := hb (x (-6) 4)
      have b9545 := hb (x (-6) 12)
      clear * - r9543 b9544 b9545 d9534
      omega
    have d9546 : (x (-6) 4 && x (-6) 14).toNat = 0 := by
      have r9547 := hand1 (x (-6) 4) (x (-6) 14)
      have b9548 := hb (x (-6) 4)
      have b9549 := hb (x (-6) 4 && x (-6) 14)
      clear * - r9547 b9548 b9549 d9542
      omega
    have d9550 : (x (-7) 13).toNat = 0 := by
      have r9551 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9552 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
      have e9553 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
      have b9554 := hb (x (-9) 3)
      have b9555 := hb (x (-8) 2)
      have b9556 := hb (x (-7) 13)
      have b9557 := hb (x (-6) 12)
      clear * - r9551 e9552 e9553 b9554 b9555 b9556 b9557 d9534 d9530
      omega
    have d9558 : (x (-7) 5).toNat = 0 := by
      have r9559 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
      have b9560 := hb (x (-7) 5)
      have b9561 := hb (x (-7) 13)
      clear * - r9559 b9560 b9561 d9550
      omega
    have d9562 : (x (-6) 5).toNat = 0 := by
      have r9563 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
      have b9564 := hb (x (-6) 5)
      have b9565 := hb (x (-6) 13)
      clear * - r9563 b9564 b9565 d9505
      omega
    have d9566 : (x (-6) 5 && x (-6) 14).toNat = 0 := by
      have r9567 := hand1 (x (-6) 5) (x (-6) 14)
      have b9568 := hb (x (-6) 5)
      have b9569 := hb (x (-6) 5 && x (-6) 14)
      clear * - r9567 b9568 b9569 d9562
      omega
    have d9570 : (x (-4) 3 && x (-4) 12).toNat = 1 := by
      have r9571 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9572 := hb (x (-7) 6)
      have b9573 := hb (x (-1) 9)
      have b9574 := hb (x (-2) 1 && x (-2) 10)
      have b9575 := hb (x (-3) 2 && x (-3) 11)
      have b9576 := hb (x (-4) 3 && x (-4) 12)
      have b9577 := hb (x (-5) 4 && x (-5) 13)
      have b9578 := hb (x (-6) 5 && x (-6) 14)
      clear * - r9571 b9572 b9573 b9574 b9575 b9576 b9577 b9578 g5 d8311 d8331 d9501 d9566 d9429
      omega
    have d9579 : (x (-4) 12).toNat = 1 := by
      have r9580 := hand2 (x (-4) 3) (x (-4) 12)
      have b9581 := hb (x (-4) 12)
      have b9582 := hb (x (-4) 3 && x (-4) 12)
      clear * - r9580 b9581 b9582 d9570
      omega
    have d9583 : (x (-5) 13).toNat = 0 := by
      have r9584 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9585 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e9586 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have b9587 := hb (x (-7) 3)
      have b9588 := hb (x (-6) 2)
      have b9589 := hb (x (-5) 13)
      have b9590 := hb (x (-4) 12)
      clear * - r9584 e9585 e9586 b9587 b9588 b9589 b9590 d9579
      omega
    have d9591 : (x (-5) 3 && x (-5) 13).toNat = 0 := by
      have r9592 := hand2 (x (-5) 3) (x (-5) 13)
      have b9593 := hb (x (-5) 13)
      have b9594 := hb (x (-5) 3 && x (-5) 13)
      clear * - r9592 b9593 b9594 d9583
      omega
    have d9595 : (x (-4) 2 && x (-4) 12).toNat = 1 := by
      have r9596 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9597 := hb (x (-7) 5)
      have b9598 := hb (x (-2) 10)
      have b9599 := hb (x (-3) 1 && x (-3) 11)
      have b9600 := hb (x (-4) 2 && x (-4) 12)
      have b9601 := hb (x (-5) 3 && x (-5) 13)
      have b9602 := hb (x (-6) 4 && x (-6) 14)
      clear * - r9596 b9597 b9598 b9599 b9600 b9601 b9602 d8295 g80 d9591 d9546 d9558
      omega
    have d9603 : (x (-4) 2).toNat = 1 := by
      have r9604 := hand1 (x (-4) 2) (x (-4) 12)
      have b9605 := hb (x (-4) 2)
      have b9606 := hb (x (-4) 2 && x (-4) 12)
      clear * - r9604 b9605 b9606 d9595
      omega
    have d9607 : (x (-4) 14).toNat = 1 := by
      have r9608 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
      have b9609 := hb (x (-4) 2)
      have b9610 := hb (x (-4) 14)
      clear * - r9608 b9609 b9610 d9603
      omega
    have d9611 : (x (-2) 12).toNat = 0 := by
      have r9612 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9613 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e9614 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have b9615 := hb (x (-5) 3)
      have b9616 := hb (x (-4) 2)
      have b9617 := hb (x (-3) 13)
      have b9618 := hb (x (-2) 12)
      clear * - r9612 e9613 e9614 b9615 b9616 b9617 b9618 g2 d9603
      omega
    have d9619 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
      have r9620 := hand2 (x (-2) 1) (x (-2) 12)
      have b9621 := hb (x (-2) 12)
      have b9622 := hb (x (-2) 1 && x (-2) 12)
      clear * - r9620 b9621 b9622 d9611
      omega
    have d9623 : (x (-4) 3 && x (-4) 14).toNat = 1 := by
      have r9624 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9625 := hb (x (-5) 4)
      have b9626 := hb (x (-1) 11)
      have b9627 := hb (x (-2) 1 && x (-2) 12)
      have b9628 := hb (x (-3) 2 && x (-3) 13)
      have b9629 := hb (x (-4) 3 && x (-4) 14)
      clear * - r9624 b9625 b9626 b9627 b9628 b9629 g7 d9619 g84 d9497
      omega
    have d9630 : (x (-4) 3).toNat = 1 := by
      have r9631 := hand1 (x (-4) 3) (x (-4) 14)
      have b9632 := hb (x (-4) 3)
      have b9633 := hb (x (-4) 3 && x (-4) 14)
      clear * - r9631 b9632 b9633 d9623
      omega
    have d9634 : (x (-1) 12).toNat = 0 := by
      have r9635 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9636 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e9637 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b9638 := hb (x (-4) 3)
      have b9639 := hb (x (-3) 2)
      have b9640 := hb (x (-2) 13)
      have b9641 := hb (x (-1) 12)
      clear * - r9635 e9636 e9637 b9638 b9639 b9640 b9641 d9630
      omega
    have d9642 : (x (-2) 13).toNat = 0 := by
      have r9643 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9644 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e9645 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b9646 := hb (x (-4) 3)
      have b9647 := hb (x (-3) 2)
      have b9648 := hb (x (-2) 13)
      have b9649 := hb (x (-1) 12)
      clear * - r9643 e9644 e9645 b9646 b9647 b9648 b9649 d9634 d9630
      omega
    have d9650 : (x (-3) 2).toNat = 0 := by
      have r9651 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9652 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e9653 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b9654 := hb (x (-4) 3)
      have b9655 := hb (x (-3) 2)
      have b9656 := hb (x (-2) 13)
      have b9657 := hb (x (-1) 12)
      clear * - r9651 e9652 e9653 b9654 b9655 b9656 b9657 d9634 d9642 d9630
      omega
    have d9658 : (x (-3) 10).toNat = 0 := by
      have r9659 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
      have b9660 := hb (x (-3) 2)
      have b9661 := hb (x (-3) 10)
      clear * - r9659 b9660 b9661 d9650
      omega
    have d9662 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
      have r9663 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9664 := hb (x (-3) 2)
      have b9665 := hb (x (-1) 13)
      have b9666 := hb (x (-2) 1 && x (-2) 14)
      clear * - r9663 b9664 b9665 b9666 g8 d9650
      omega
    have d9667 : (x (-2) 1).toNat = 1 := by
      have r9668 := hand1 (x (-2) 1) (x (-2) 14)
      have b9669 := hb (x (-2) 1)
      have b9670 := hb (x (-2) 1 && x (-2) 14)
      clear * - r9668 b9669 b9670 d9662
      omega
    have d9671 : (x (-1) 14).toNat = 0 := by
      have r9672 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9673 := hb (x (-2) 1)
      have b9674 := hb (x (-1) 14)
      clear * - r9672 b9673 b9674 d9667
      omega
    have d9675 : (x (-1) 8 && x (-1) 14).toNat = 0 := by
      have r9676 := hand2 (x (-1) 8) (x (-1) 14)
      have b9677 := hb (x (-1) 14)
      have b9678 := hb (x (-1) 8 && x (-1) 14)
      clear * - r9676 b9677 b9678 d9671
      omega
    have d9679 : (x (-2) 9 && x (-2) 12).toNat = 0 := by
      have r9680 := hand2 (x (-2) 9) (x (-2) 12)
      have b9681 := hb (x (-2) 12)
      have b9682 := hb (x (-2) 9 && x (-2) 12)
      clear * - r9680 b9681 b9682 d9611
      omega
    have d9683 : (x (-5) 3).toNat = 0 := by
      have r9684 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9685 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e9686 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have b9687 := hb (x (-5) 3)
      have b9688 := hb (x (-4) 2)
      have b9689 := hb (x (-3) 13)
      have b9690 := hb (x (-2) 12)
      clear * - r9684 e9685 e9686 b9687 b9688 b9689 b9690 d9611 g2 d9603
      omega
    have d9691 : (x (-5) 3 && x (-5) 14).toNat = 0 := by
      have r9692 := hand1 (x (-5) 3) (x (-5) 14)
      have b9693 := hb (x (-5) 3)
      have b9694 := hb (x (-5) 3 && x (-5) 14)
      clear * - r9692 b9693 b9694 d9683
      omega
    have d9695 : (x (-4) 2 && x (-4) 13).toNat = 1 := by
      have r9696 : 1 ≤ (x (-2) 11).toNat + (x (-3) 1 && x (-3) 12).toNat + (x (-4) 2 && x (-4) 13).toNat + (x (-5) 3 && x (-5) 14).toNat + (x (-6) 4).toNat := by have q := hcov11 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9697 := hb (x (-6) 4)
      have b9698 := hb (x (-2) 11)
      have b9699 := hb (x (-3) 1 && x (-3) 12)
      have b9700 := hb (x (-4) 2 && x (-4) 13)
      have b9701 := hb (x (-5) 3 && x (-5) 14)
      clear * - r9696 b9697 b9698 b9699 b9700 b9701 g3 g83 d9691 d9542
      omega
    have d9702 : (x (-4) 13).toNat = 1 := by
      have r9703 := hand2 (x (-4) 2) (x (-4) 13)
      have b9704 := hb (x (-4) 13)
      have b9705 := hb (x (-4) 2 && x (-4) 13)
      clear * - r9703 b9704 b9705 d9695
      omega
    have d9706 : (x (-3) 12).toNat = 0 := by
      have r9707 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9708 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e9709 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b9710 := hb (x (-6) 3)
      have b9711 := hb (x (-5) 2)
      have b9712 := hb (x (-4) 13)
      have b9713 := hb (x (-3) 12)
      clear * - r9707 e9708 e9709 b9710 b9711 b9712 b9713 d9702
      omega
    have d9714 : (x (-5) 11).toNat = 0 := by
      have r9715 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
      have b9716 := hb (x (-5) 3)
      have b9717 := hb (x (-5) 11)
      clear * - r9715 b9716 b9717 d9683
      omega
    have d9718 : (x (-5) 11 && x (-5) 14).toNat = 0 := by
      have r9719 := hand1 (x (-5) 11) (x (-5) 14)
      have b9720 := hb (x (-5) 11)
      have b9721 := hb (x (-5) 11 && x (-5) 14)
      clear * - r9719 b9720 b9721 d9714
      omega
    have d9722 : (x (-6) 1 && x (-6) 14).toNat = 1 := by
      have r9723 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9724 := hb (x (-7) 2)
      have b9725 := hb (x (-5) 13)
      have b9726 := hb (x (-6) 1 && x (-6) 14)
      clear * - r9723 b9724 b9725 b9726 d9583 d9433
      omega
    have d9727 : (x (-6) 14).toNat = 1 := by
      have r9728 := hand2 (x (-6) 1) (x (-6) 14)
      have b9729 := hb (x (-6) 14)
      have b9730 := hb (x (-6) 1 && x (-6) 14)
      clear * - r9728 b9729 b9730 d9722
      omega
    have d9731 : (x (-6) 1).toNat = 1 := by
      have r9732 := hand1 (x (-6) 1) (x (-6) 14)
      have b9733 := hb (x (-6) 1)
      have b9734 := hb (x (-6) 1 && x (-6) 14)
      clear * - r9732 b9733 b9734 d9722
      omega
    have d9735 : (x (-5) 14).toNat = 0 := by
      have r9736 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9737 := hb (x (-6) 1)
      have b9738 := hb (x (-5) 14)
      clear * - r9736 b9737 b9738 d9731
      omega
    have d9739 : (x 7 1).toNat = 0 := by
      have r9740 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9741 := hb (x (-6) 14)
      have b9742 := hb (x (-5) 13)
      have b9743 := hb (x (-4) 12)
      have b9744 := hb (x (-3) 11)
      have b9745 := hb (x (-2) 10)
      have b9746 := hb (x (-1) 9)
      have b9747 := hb (x 0 8)
      have b9748 := hb (x 1 7)
      have b9749 := hb (x 2 6)
      have b9750 := hb (x 3 5)
      have b9751 := hb (x 4 4)
      have b9752 := hb (x 5 3)
      have b9753 := hb (x 6 2)
      have b9754 := hb (x 7 1)
      clear * - r9740 b9741 b9742 b9743 b9744 b9745 b9746 b9747 b9748 b9749 b9750 b9751 b9752 b9753 b9754 g18 g12 g5 d8295 d8315 d9579 d9583 d9727
      omega
    have d9755 : (x 7 1 && x 7 14).toNat = 0 := by
      have r9756 := hand1 (x 7 1) (x 7 14)
      have b9757 := hb (x 7 1)
      have b9758 := hb (x 7 1 && x 7 14)
      clear * - r9756 b9757 b9758 d9739
      omega
    have d9759 : (x 7 13).toNat = 0 := by
      have r9760 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
      have b9761 := hb (x 7 1)
      have b9762 := hb (x 7 13)
      clear * - r9760 b9761 b9762 d9739
      omega
    have d9763 : (x 7 5).toNat = 0 := by
      have r9764 : (x 7 5).toNat ≤ (x 7 13).toNat := himp _ _ (hp5 7)
      have b9765 := hb (x 7 5)
      have b9766 := hb (x 7 13)
      clear * - r9764 b9765 b9766 d9759
      omega
    have d9767 : (x 7 5 && x 7 11).toNat = 0 := by
      have r9768 := hand1 (x 7 5) (x 7 11)
      have b9769 := hb (x 7 5)
      have b9770 := hb (x 7 5 && x 7 11)
      clear * - r9768 b9769 b9770 d9763
      omega
    have d9771 : (x 6 1 && x 6 14).toNat = 1 := by
      have r9772 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9773 := hb (x 5 2)
      have b9774 := hb (x 7 13)
      have b9775 := hb (x 6 1 && x 6 14)
      clear * - r9772 b9773 b9774 b9775 d9759 g23
      omega
    have d9776 : (x 6 14).toNat = 1 := by
      have r9777 := hand2 (x 6 1) (x 6 14)
      have b9778 := hb (x 6 14)
      have b9779 := hb (x 6 1 && x 6 14)
      clear * - r9777 b9778 b9779 d9771
      omega
    have d9780 : (x 5 1).toNat = 0 := by
      have r9781 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9782 := hb (x 5 1)
      have b9783 := hb (x 6 14)
      clear * - r9781 b9782 b9783 d9776
      omega
    have d9784 : (x 5 1 && x 5 7).toNat = 0 := by
      have r9785 := hand1 (x 5 1) (x 5 7)
      have b9786 := hb (x 5 1)
      have b9787 := hb (x 5 1 && x 5 7)
      clear * - r9785 b9786 b9787 d9780
      omega
    have d9788 : (x 5 1 && x 5 4).toNat = 0 := by
      have r9789 := hand1 (x 5 1) (x 5 4)
      have b9790 := hb (x 5 1)
      have b9791 := hb (x 5 1 && x 5 4)
      clear * - r9789 b9790 b9791 d9780
      omega
    have d9792 : (x 6 1).toNat = 1 := by
      have r9793 := hand1 (x 6 1) (x 6 14)
      have b9794 := hb (x 6 1)
      have b9795 := hb (x 6 1 && x 6 14)
      clear * - r9793 b9794 b9795 d9771
      omega
    have d9796 : (x 7 14).toNat = 0 := by
      have r9797 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9798 := hb (x 6 1)
      have b9799 := hb (x 7 14)
      clear * - r9797 b9798 b9799 d9792
      omega
    have d9800 : (x 7 7 && x 7 14).toNat = 0 := by
      have r9801 := hand2 (x 7 7) (x 7 14)
      have b9802 := hb (x 7 14)
      have b9803 := hb (x 7 7 && x 7 14)
      clear * - r9801 b9802 b9803 d9796
      omega
    have d9804 : (x 7 6).toNat = 0 := by
      have r9805 : (x 7 6).toNat ≤ (x 7 14).toNat := himp _ _ (hp6 7)
      have b9806 := hb (x 7 6)
      have b9807 := hb (x 7 14)
      clear * - r9805 b9806 b9807 d9796
      omega
    have d9808 : (x 7 2).toNat = 0 := by
      have r9809 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
      have b9810 := hb (x 7 2)
      have b9811 := hb (x 7 14)
      clear * - r9809 b9810 b9811 d9796
      omega
    have d9812 : (x 7 2 && x 7 11).toNat = 0 := by
      have r9813 := hand1 (x 7 2) (x 7 11)
      have b9814 := hb (x 7 2)
      have b9815 := hb (x 7 2 && x 7 11)
      clear * - r9813 b9814 b9815 d9808
      omega
    have d9816 : (x 7 9).toNat = 0 := by
      have r9817 : (x 7 9).toNat ≤ (x 7 1).toNat := himp _ _ (hp9 7)
      have b9818 := hb (x 7 1)
      have b9819 := hb (x 7 9)
      clear * - r9817 b9818 b9819 d9739
      omega
    have d9820 : (x 6 2).toNat = 0 := by
      have r9821 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9822 := hb (x (-6) 14)
      have b9823 := hb (x (-5) 13)
      have b9824 := hb (x (-4) 12)
      have b9825 := hb (x (-3) 11)
      have b9826 := hb (x (-2) 10)
      have b9827 := hb (x (-1) 9)
      have b9828 := hb (x 0 8)
      have b9829 := hb (x 1 7)
      have b9830 := hb (x 2 6)
      have b9831 := hb (x 3 5)
      have b9832 := hb (x 4 4)
      have b9833 := hb (x 5 3)
      have b9834 := hb (x 6 2)
      have b9835 := hb (x 7 1)
      clear * - r9821 b9822 b9823 b9824 b9825 b9826 b9827 b9828 b9829 b9830 b9831 b9832 b9833 b9834 b9835 d9739 g18 g12 g5 d8295 d8315 d9579 d9583 d9727
      omega
    have d9836 : (x 6 10).toNat = 0 := by
      have r9837 : (x 6 10).toNat ≤ (x 6 2).toNat := himp _ _ (hp10 6)
      have b9838 := hb (x 6 2)
      have b9839 := hb (x 6 10)
      clear * - r9837 b9838 b9839 d9820
      omega
    have d9840 : (x 6 1 && x 6 10).toNat = 0 := by
      have r9841 := hand2 (x 6 1) (x 6 10)
      have b9842 := hb (x 6 10)
      have b9843 := hb (x 6 1 && x 6 10)
      clear * - r9841 b9842 b9843 d9836
      omega
    have d9844 : (x 4 3 && x 4 12).toNat = 1 := by
      have r9845 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9846 := hb (x 1 6)
      have b9847 := hb (x 7 9)
      have b9848 := hb (x 6 1 && x 6 10)
      have b9849 := hb (x 5 2 && x 5 11)
      have b9850 := hb (x 4 3 && x 4 12)
      have b9851 := hb (x 3 4 && x 3 13)
      have b9852 := hb (x 2 5 && x 2 14)
      clear * - r9845 b9846 b9847 b9848 b9849 b9850 b9851 b9852 d9816 d9840 g73 g74 g75 g13
      omega
    have d9853 : (x 4 12).toNat = 1 := by
      have r9854 := hand2 (x 4 3) (x 4 12)
      have b9855 := hb (x 4 12)
      have b9856 := hb (x 4 3 && x 4 12)
      clear * - r9854 b9855 b9856 d9844
      omega
    have d9857 : (x 2 2).toNat = 0 := by
      have r9858 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9859 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e9860 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b9861 := hb (x 1 3)
      have b9862 := hb (x 2 2)
      have b9863 := hb (x 3 13)
      have b9864 := hb (x 4 12)
      clear * - r9858 e9859 e9860 b9861 b9862 b9863 b9864 d9853 g21
      omega
    have d9865 : (x 4 13).toNat = 1 := by
      have r9866 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9867 := hb (x 2 2)
      have b9868 := hb (x 4 13)
      have b9869 := hb (x 3 1 && x 3 14)
      clear * - r9866 b9867 b9868 b9869 g87 d9857
      omega
    have d9870 : (x 5 12).toNat = 0 := by
      have r9871 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9872 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e9873 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b9874 := hb (x 2 3)
      have b9875 := hb (x 3 2)
      have b9876 := hb (x 4 13)
      have b9877 := hb (x 5 12)
      clear * - r9871 e9872 e9873 b9874 b9875 b9876 b9877 d9865 g17
      omega
    have d9878 : (x 5 4).toNat = 0 := by
      have r9879 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
      have b9880 := hb (x 5 4)
      have b9881 := hb (x 5 12)
      clear * - r9879 b9880 b9881 d9870
      omega
    have d9882 : (x 8 13).toNat = 1 := by
      have r9883 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9884 := hb (x 6 2)
      have b9885 := hb (x 8 13)
      have b9886 := hb (x 7 1 && x 7 14)
      clear * - r9883 b9884 b9885 b9886 d9755 d9820
      omega
    have d9887 : (x 8 1).toNat = 1 := by
      have r9888 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
      have b9889 := hb (x 8 1)
      have b9890 := hb (x 8 13)
      clear * - r9888 b9889 b9890 d9882
      omega
    have d9891 : (x 9 14).toNat = 0 := by
      have r9892 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9893 := hb (x 8 1)
      have b9894 := hb (x 9 14)
      clear * - r9892 b9893 b9894 d9887
      omega
    have d9895 : (x 9 1 && x 9 14).toNat = 0 := by
      have r9896 := hand2 (x 9 1) (x 9 14)
      have b9897 := hb (x 9 14)
      have b9898 := hb (x 9 1 && x 9 14)
      clear * - r9896 b9897 b9898 d9891
      omega
    have d9899 : (x 9 3 && x 9 14).toNat = 0 := by
      have r9900 := hand2 (x 9 3) (x 9 14)
      have b9901 := hb (x 9 14)
      have b9902 := hb (x 9 3 && x 9 14)
      clear * - r9900 b9901 b9902 d9891
      omega
    have d9903 : (x 9 4 && x 9 14).toNat = 0 := by
      have r9904 := hand2 (x 9 4) (x 9 14)
      have b9905 := hb (x 9 14)
      have b9906 := hb (x 9 4 && x 9 14)
      clear * - r9904 b9905 b9906 d9891
      omega
    have d9907 : (x 9 2).toNat = 0 := by
      have r9908 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
      have b9909 := hb (x 9 2)
      have b9910 := hb (x 9 14)
      clear * - r9908 b9909 b9910 d9891
      omega
    have d9911 : (x 9 2 && x 9 11).toNat = 0 := by
      have r9912 := hand1 (x 9 2) (x 9 11)
      have b9913 := hb (x 9 2)
      have b9914 := hb (x 9 2 && x 9 11)
      clear * - r9912 b9913 b9914 d9907
      omega
    have d9915 : (x 6 3).toNat = 0 := by
      have r9916 : (x 8 1).toNat + (x 7 2).toNat + (x 6 3).toNat + (x 5 4).toNat + (x 4 5).toNat + (x 3 6).toNat + (x 2 7).toNat + (x 1 8).toNat + (x 0 9).toNat + (x (-1) 10).toNat + (x (-2) 11).toNat + (x (-3) 12).toNat + (x (-4) 13).toNat + (x (-5) 14).toNat = 3 := by have q := hcount 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9917 := hb (x (-5) 14)
      have b9918 := hb (x (-4) 13)
      have b9919 := hb (x (-3) 12)
      have b9920 := hb (x (-2) 11)
      have b9921 := hb (x (-1) 10)
      have b9922 := hb (x 0 9)
      have b9923 := hb (x 1 8)
      have b9924 := hb (x 2 7)
      have b9925 := hb (x 3 6)
      have b9926 := hb (x 4 5)
      have b9927 := hb (x 5 4)
      have b9928 := hb (x 6 3)
      have b9929 := hb (x 7 2)
      have b9930 := hb (x 8 1)
      clear * - r9916 b9917 b9918 b9919 b9920 b9921 b9922 b9923 b9924 b9925 b9926 b9927 b9928 b9929 b9930 d9887 d9808 d9878 g19 d8966 f8965 g6 g3 d9706 d9702 d9735
      omega
    have d9931 : (x 4 5).toNat = 0 := by
      have r9932 : (x 8 1).toNat + (x 7 2).toNat + (x 6 3).toNat + (x 5 4).toNat + (x 4 5).toNat + (x 3 6).toNat + (x 2 7).toNat + (x 1 8).toNat + (x 0 9).toNat + (x (-1) 10).toNat + (x (-2) 11).toNat + (x (-3) 12).toNat + (x (-4) 13).toNat + (x (-5) 14).toNat = 3 := by have q := hcount 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9933 := hb (x (-5) 14)
      have b9934 := hb (x (-4) 13)
      have b9935 := hb (x (-3) 12)
      have b9936 := hb (x (-2) 11)
      have b9937 := hb (x (-1) 10)
      have b9938 := hb (x 0 9)
      have b9939 := hb (x 1 8)
      have b9940 := hb (x 2 7)
      have b9941 := hb (x 3 6)
      have b9942 := hb (x 4 5)
      have b9943 := hb (x 5 4)
      have b9944 := hb (x 6 3)
      have b9945 := hb (x 7 2)
      have b9946 := hb (x 8 1)
      clear * - r9932 b9933 b9934 b9935 b9936 b9937 b9938 b9939 b9940 b9941 b9942 b9943 b9944 b9945 b9946 d9887 d9808 d9915 d9878 g19 d8966 f8965 g6 g3 d9706 d9702 d9735
      omega
    have d9947 : (x 4 5 && x 4 14).toNat = 0 := by
      have r9948 := hand1 (x 4 5) (x 4 14)
      have b9949 := hb (x 4 5)
      have b9950 := hb (x 4 5 && x 4 14)
      clear * - r9948 b9949 b9950 d9931
      omega
    have d9951 : (x 4 2 && x 4 5).toNat = 0 := by
      have r9952 := hand2 (x 4 2) (x 4 5)
      have b9953 := hb (x 4 5)
      have b9954 := hb (x 4 2 && x 4 5)
      clear * - r9952 b9953 b9954 d9931
      omega
    have d9955 : (x (-4) 10 && x (-4) 13).toNat = 1 := by
      have r9956 : 1 ≤ (x 6 3).toNat + (x 5 1 && x 5 4).toNat + (x 4 2 && x 4 5).toNat + (x 3 3 && x 3 6).toNat + (x 2 4 && x 2 7).toNat + (x 1 5 && x 1 8).toNat + (x 0 6 && x 0 9).toNat + (x (-1) 7 && x (-1) 10).toNat + (x (-2) 8 && x (-2) 11).toNat + (x (-3) 9 && x (-3) 12).toNat + (x (-4) 10 && x (-4) 13).toNat + (x (-5) 11 && x (-5) 14).toNat + (x (-6) 12).toNat := by have q := hcov3 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9957 := hb (x (-6) 12)
      have b9958 := hb (x 6 3)
      have b9959 := hb (x 5 1 && x 5 4)
      have b9960 := hb (x 4 2 && x 4 5)
      have b9961 := hb (x 3 3 && x 3 6)
      have b9962 := hb (x 2 4 && x 2 7)
      have b9963 := hb (x 1 5 && x 1 8)
      have b9964 := hb (x 0 6 && x 0 9)
      have b9965 := hb (x (-1) 7 && x (-1) 10)
      have b9966 := hb (x (-2) 8 && x (-2) 11)
      have b9967 := hb (x (-3) 9 && x (-3) 12)
      have b9968 := hb (x (-4) 10 && x (-4) 13)
      have b9969 := hb (x (-5) 11 && x (-5) 14)
      clear * - r9956 b9957 b9958 b9959 b9960 b9961 b9962 b9963 b9964 b9965 b9966 b9967 b9968 b9969 d9915 d9788 d9951 g30 g31 g32 g33 g34 g35 g36 d9718 d9534
      omega
    have d9970 : (x (-4) 10).toNat = 1 := by
      have r9971 := hand1 (x (-4) 10) (x (-4) 13)
      have b9972 := hb (x (-4) 10)
      have b9973 := hb (x (-4) 10 && x (-4) 13)
      clear * - r9971 b9972 b9973 d9955
      omega
    have d9974 : (x (-2) 8).toNat = 0 := by
      have r9975 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9976 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
      have e9977 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
      have e9978 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
      have e9979 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
      have e9980 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
      have e9981 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
      have b9982 := hb (x (-9) 7)
      have b9983 := hb (x (-8) 6)
      have b9984 := hb (x (-7) 5)
      have b9985 := hb (x (-6) 4)
      have b9986 := hb (x (-5) 11)
      have b9987 := hb (x (-4) 10)
      have b9988 := hb (x (-3) 9)
      have b9989 := hb (x (-2) 8)
      clear * - r9975 e9976 e9977 e9978 e9979 e9980 e9981 b9982 b9983 b9984 b9985 b9986 b9987 b9988 b9989 g1 d9970 d9714 d9542 d9558
      omega
    have d9990 : (x (-2) 8 && x (-2) 14).toNat = 0 := by
      have r9991 := hand1 (x (-2) 8) (x (-2) 14)
      have b9992 := hb (x (-2) 8)
      have b9993 := hb (x (-2) 8 && x (-2) 14)
      clear * - r9991 b9992 b9993 d9974
      omega
    have d9994 : (x 6 6).toNat = 1 := by
      have r9995 : 1 ≤ (x 6 6).toNat + (x 5 1 && x 5 7).toNat + (x 4 2 && x 4 8).toNat + (x 3 3 && x 3 9).toNat + (x 2 4 && x 2 10).toNat + (x 1 5 && x 1 11).toNat + (x 0 6 && x 0 12).toNat + (x (-1) 7 && x (-1) 13).toNat + (x (-2) 8 && x (-2) 14).toNat + (x (-3) 9).toNat := by have q := hcov6 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b9996 := hb (x (-3) 9)
      have b9997 := hb (x 6 6)
      have b9998 := hb (x 5 1 && x 5 7)
      have b9999 := hb (x 4 2 && x 4 8)
      have b10000 := hb (x 3 3 && x 3 9)
      have b10001 := hb (x 2 4 && x 2 10)
      have b10002 := hb (x 1 5 && x 1 11)
      have b10003 := hb (x 0 6 && x 0 12)
      have b10004 := hb (x (-1) 7 && x (-1) 13)
      have b10005 := hb (x (-2) 8 && x (-2) 14)
      clear * - r9995 b9996 b9997 b9998 b9999 b10000 b10001 b10002 b10003 b10004 b10005 d9784 g55 g56 g57 g58 g59 g60 d9990 g1
      omega
    have d10006 : (x 12 8).toNat = 0 := by
      have r10007 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10008 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
      have e10009 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
      have e10010 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
      have e10011 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
      have e10012 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
      have e10013 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
      have b10014 := hb (x 5 7)
      have b10015 := hb (x 6 6)
      have b10016 := hb (x 7 5)
      have b10017 := hb (x 8 4)
      have b10018 := hb (x 9 11)
      have b10019 := hb (x 10 10)
      have b10020 := hb (x 11 9)
      have b10021 := hb (x 12 8)
      clear * - r10007 e10008 e10009 e10010 e10011 e10012 e10013 b10014 b10015 b10016 b10017 b10018 b10019 b10020 b10021 d9763 d9994
      omega
    have d10022 : (x 11 9).toNat = 0 := by
      have r10023 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10024 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
      have e10025 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
      have e10026 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
      have e10027 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
      have e10028 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
      have e10029 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
      have b10030 := hb (x 5 7)
      have b10031 := hb (x 6 6)
      have b10032 := hb (x 7 5)
      have b10033 := hb (x 8 4)
      have b10034 := hb (x 9 11)
      have b10035 := hb (x 10 10)
      have b10036 := hb (x 11 9)
      have b10037 := hb (x 12 8)
      clear * - r10023 e10024 e10025 e10026 e10027 e10028 e10029 b10030 b10031 b10032 b10033 b10034 b10035 b10036 b10037 d10006 d9763 d9994
      omega
    have d10038 : (x 10 10).toNat = 0 := by
      have r10039 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10040 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
      have e10041 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
      have e10042 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
      have e10043 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
      have e10044 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
      have e10045 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
      have b10046 := hb (x 5 7)
      have b10047 := hb (x 6 6)
      have b10048 := hb (x 7 5)
      have b10049 := hb (x 8 4)
      have b10050 := hb (x 9 11)
      have b10051 := hb (x 10 10)
      have b10052 := hb (x 11 9)
      have b10053 := hb (x 12 8)
      clear * - r10039 e10040 e10041 e10042 e10043 e10044 e10045 b10046 b10047 b10048 b10049 b10050 b10051 b10052 b10053 d10006 d10022 d9763 d9994
      omega
    have d10054 : (x 10 1 && x 10 10).toNat = 0 := by
      have r10055 := hand2 (x 10 1) (x 10 10)
      have b10056 := hb (x 10 10)
      have b10057 := hb (x 10 1 && x 10 10)
      clear * - r10055 b10056 b10057 d10038
      omega
    have d10058 : (x 8 3 && x 8 12).toNat = 1 := by
      have r10059 : 1 ≤ (x 11 9).toNat + (x 10 1 && x 10 10).toNat + (x 9 2 && x 9 11).toNat + (x 8 3 && x 8 12).toNat + (x 7 4 && x 7 13).toNat + (x 6 5 && x 6 14).toNat + (x 5 6).toNat := by have q := hcov9 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b10060 := hb (x 5 6)
      have b10061 := hb (x 11 9)
      have b10062 := hb (x 10 1 && x 10 10)
      have b10063 := hb (x 9 2 && x 9 11)
      have b10064 := hb (x 8 3 && x 8 12)
      have b10065 := hb (x 7 4 && x 7 13)
      have b10066 := hb (x 6 5 && x 6 14)
      clear * - r10059 b10060 b10061 b10062 b10063 b10064 b10065 b10066 d10022 d10054 d9911 g78 g79 g25
      omega
    have d10067 : (x 8 3).toNat = 1 := by
      have r10068 := hand1 (x 8 3) (x 8 12)
      have b10069 := hb (x 8 3)
      have b10070 := hb (x 8 3 && x 8 12)
      clear * - r10068 b10069 b10070 d10058
      omega
    have d10071 : (x 11 12).toNat = 0 := by
      have r10072 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10073 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
      have e10074 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
      have b10075 := hb (x 8 3)
      have b10076 := hb (x 9 2)
      have b10077 := hb (x 10 13)
      have b10078 := hb (x 11 12)
      clear * - r10072 e10073 e10074 b10075 b10076 b10077 b10078 d9907 d10067
      omega
    have d10079 : (x 11 1 && x 11 12).toNat = 0 := by
      have r10080 := hand2 (x 11 1) (x 11 12)
      have b10081 := hb (x 11 12)
      have b10082 := hb (x 11 1 && x 11 12)
      clear * - r10080 b10081 b10082 d10071
      omega
    have d10083 : (x 11 2 && x 11 12).toNat = 0 := by
      have r10084 := hand2 (x 11 2) (x 11 12)
      have b10085 := hb (x 11 12)
      have b10086 := hb (x 11 2 && x 11 12)
      clear * - r10084 b10085 b10086 d10071
      omega
    have d10087 : (x 10 13).toNat = 0 := by
      have r10088 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10089 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
      have e10090 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
      have b10091 := hb (x 8 3)
      have b10092 := hb (x 9 2)
      have b10093 := hb (x 10 13)
      have b10094 := hb (x 11 12)
      clear * - r10088 e10089 e10090 b10091 b10092 b10093 b10094 d10071 d9907 d10067
      omega
    have d10095 : (x 10 2 && x 10 13).toNat = 0 := by
      have r10096 := hand2 (x 10 2) (x 10 13)
      have b10097 := hb (x 10 13)
      have b10098 := hb (x 10 2 && x 10 13)
      clear * - r10096 b10097 b10098 d10087
      omega
    have d10099 : (x 10 3 && x 10 13).toNat = 0 := by
      have r10100 := hand2 (x 10 3) (x 10 13)
      have b10101 := hb (x 10 13)
      have b10102 := hb (x 10 3 && x 10 13)
      clear * - r10100 b10101 b10102 d10087
      omega
    have d10103 : (x 8 2).toNat = 1 := by
      have r10104 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b10105 := hb (x 8 2)
      have b10106 := hb (x 10 13)
      have b10107 := hb (x 9 1 && x 9 14)
      clear * - r10104 b10105 b10106 b10107 d10087 d9895
      omega
    have d10108 : (x 10 12).toNat = 0 := by
      have r10109 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10110 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e10111 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b10112 := hb (x 7 3)
      have b10113 := hb (x 8 2)
      have b10114 := hb (x 9 13)
      have b10115 := hb (x 10 12)
      clear * - r10109 e10110 e10111 b10112 b10113 b10114 b10115 d10103
      omega
    have d10116 : (x 10 2 && x 10 12).toNat = 0 := by
      have r10117 := hand2 (x 10 2) (x 10 12)
      have b10118 := hb (x 10 12)
      have b10119 := hb (x 10 2 && x 10 12)
      clear * - r10117 b10118 b10119 d10108
      omega
    have d10120 : (x 10 4).toNat = 0 := by
      have r10121 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
      have b10122 := hb (x 10 4)
      have b10123 := hb (x 10 12)
      clear * - r10121 b10122 b10123 d10108
      omega
    have d10124 : (x 10 4 && x 10 11).toNat = 0 := by
      have r10125 := hand1 (x 10 4) (x 10 11)
      have b10126 := hb (x 10 4)
      have b10127 := hb (x 10 4 && x 10 11)
      clear * - r10125 b10126 b10127 d10120
      omega
    have d10128 : (x 9 13).toNat = 0 := by
      have r10129 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10130 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e10131 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b10132 := hb (x 7 3)
      have b10133 := hb (x 8 2)
      have b10134 := hb (x 9 13)
      have b10135 := hb (x 10 12)
      clear * - r10129 e10130 e10131 b10132 b10133 b10134 b10135 d10108 d10103
      omega
    have d10136 : (x 9 3 && x 9 13).toNat = 0 := by
      have r10137 := hand2 (x 9 3) (x 9 13)
      have b10138 := hb (x 9 13)
      have b10139 := hb (x 9 3 && x 9 13)
      clear * - r10137 b10138 b10139 d10128
      omega
    have d10140 : (x 9 5).toNat = 0 := by
      have r10141 : (x 9 5).toNat ≤ (x 9 13).toNat := himp _ _ (hp5 9)
      have b10142 := hb (x 9 5)
      have b10143 := hb (x 9 13)
      clear * - r10141 b10142 b10143 d10128
      omega
    have d10144 : (x 9 5 && x 9 12).toNat = 0 := by
      have r10145 := hand1 (x 9 5) (x 9 12)
      have b10146 := hb (x 9 5)
      have b10147 := hb (x 9 5 && x 9 12)
      clear * - r10145 b10146 b10147 d10140
      omega
    have d10148 : (x 7 3).toNat = 0 := by
      have r10149 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10150 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e10151 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b10152 := hb (x 7 3)
      have b10153 := hb (x 8 2)
      have b10154 := hb (x 9 13)
      have b10155 := hb (x 10 12)
      clear * - r10149 e10150 e10151 b10152 b10153 b10154 b10155 d10108 d10128 d10103
      omega
    have d10156 : (x 7 11).toNat = 0 := by
      have r10157 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
      have b10158 := hb (x 7 3)
      have b10159 := hb (x 7 11)
      clear * - r10157 b10158 b10159 d10148
      omega
    have d10160 : (x 9 1).toNat = 0 := by
      have r10161 : (x 9 1).toNat + (x 8 2).toNat + (x 7 3).toNat + (x 6 4).toNat + (x 5 5).toNat + (x 4 6).toNat + (x 3 7).toNat + (x 2 8).toNat + (x 1 9).toNat + (x 0 10).toNat + (x (-1) 11).toNat + (x (-2) 12).toNat + (x (-3) 13).toNat + (x (-4) 14).toNat = 3 := by have q := hcount 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b10162 := hb (x (-4) 14)
      have b10163 := hb (x (-3) 13)
      have b10164 := hb (x (-2) 12)
      have b10165 := hb (x (-1) 11)
      have b10166 := hb (x 0 10)
      have b10167 := hb (x 1 9)
      have b10168 := hb (x 2 8)
      have b10169 := hb (x 3 7)
      have b10170 := hb (x 4 6)
      have b10171 := hb (x 5 5)
      have b10172 := hb (x 6 4)
      have b10173 := hb (x 7 3)
      have b10174 := hb (x 8 2)
      have b10175 := hb (x 9 1)
      clear * - r10161 b10162 b10163 b10164 b10165 b10166 b10167 b10168 b10169 b10170 b10171 b10172 b10173 b10174 b10175 d10103 d10148 g27 g24 d9033 g14 d9025 g7 d9611 g2 d9607
      omega
    have d10176 : (x 9 9).toNat = 0 := by
      have r10177 : (x 9 9).toNat ≤ (x 9 1).toNat := himp _ _ (hp9 9)
      have b10178 := hb (x 9 1)
      have b10179 := hb (x 9 9)
      clear * - r10177 b10178 b10179 d10160
      omega
    have d10180 : (x 9 3 && x 9 9).toNat = 0 := by
      have r10181 := hand2 (x 9 3) (x 9 9)
      have b10182 := hb (x 9 9)
      have b10183 := hb (x 9 3 && x 9 9)
      clear * - r10181 b10182 b10183 d10176
      omega
    have d10184 : (x 8 1 && x 8 10).toNat = 1 := by
      have r10185 : 1 ≤ (x 9 9).toNat + (x 8 1 && x 8 10).toNat + (x 7 2 && x 7 11).toNat + (x 6 3 && x 6 12).toNat + (x 5 4 && x 5 13).toNat + (x 4 5 && x 4 14).toNat + (x 3 6).toNat := by have q := hcov9 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b10186 := hb (x 3 6)
      have b10187 := hb (x 9 9)
      have b10188 := hb (x 8 1 && x 8 10)
      have b10189 := hb (x 7 2 && x 7 11)
      have b10190 := hb (x 6 3 && x 6 12)
      have b10191 := hb (x 5 4 && x 5 13)
      have b10192 := hb (x 4 5 && x 4 14)
      clear * - r10185 b10186 b10187 b10188 b10189 b10190 b10191 b10192 d10176 d9812 g76 g77 d9947 g19
      omega
    have d10193 : (x 8 10).toNat = 1 := by
      have r10194 := hand2 (x 8 1) (x 8 10)
      have b10195 := hb (x 8 10)
      have b10196 := hb (x 8 1 && x 8 10)
      clear * - r10194 b10195 b10196 d10184
      omega
    have d10197 : (x 10 8).toNat = 0 := by
      have r10198 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10199 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
      have e10200 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
      have e10201 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
      have e10202 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
      have e10203 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
      have e10204 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
      have b10205 := hb (x 3 7)
      have b10206 := hb (x 4 6)
      have b10207 := hb (x 5 5)
      have b10208 := hb (x 6 4)
      have b10209 := hb (x 7 11)
      have b10210 := hb (x 8 10)
      have b10211 := hb (x 9 9)
      have b10212 := hb (x 10 8)
      clear * - r10198 e10199 e10200 e10201 e10202 e10203 e10204 b10205 b10206 b10207 b10208 b10209 b10210 b10211 b10212 d10176 d10193 d10156 g27 g24
      omega
    have d10213 : (x 10 2 && x 10 8).toNat = 0 := by
      have r10214 := hand2 (x 10 2) (x 10 8)
      have b10215 := hb (x 10 8)
      have b10216 := hb (x 10 2 && x 10 8)
      clear * - r10214 b10215 b10216 d10197
      omega
    have d10217 : (x 4 6).toNat = 0 := by
      have r10218 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10219 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
      have e10220 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
      have e10221 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
      have e10222 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
      have e10223 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
      have e10224 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
      have b10225 := hb (x 3 7)
      have b10226 := hb (x 4 6)
      have b10227 := hb (x 5 5)
      have b10228 := hb (x 6 4)
      have b10229 := hb (x 7 11)
      have b10230 := hb (x 8 10)
      have b10231 := hb (x 9 9)
      have b10232 := hb (x 10 8)
      clear * - r10218 e10219 e10220 e10221 e10222 e10223 e10224 b10225 b10226 b10227 b10228 b10229 b10230 b10231 b10232 d10197 d10176 d10193 d10156 g27 g24
      omega
    have d10233 : (x 4 3 && x 4 6).toNat = 0 := by
      have r10234 := hand2 (x 4 3) (x 4 6)
      have b10235 := hb (x 4 6)
      have b10236 := hb (x 4 3 && x 4 6)
      clear * - r10234 b10235 b10236 d10217
      omega
    have d10237 : (x (-4) 11 && x (-4) 14).toNat = 1 := by
      have r10238 : 1 ≤ (x 7 3).toNat + (x 6 1 && x 6 4).toNat + (x 5 2 && x 5 5).toNat + (x 4 3 && x 4 6).toNat + (x 3 4 && x 3 7).toNat + (x 2 5 && x 2 8).toNat + (x 1 6 && x 1 9).toNat + (x 0 7 && x 0 10).toNat + (x (-1) 8 && x (-1) 11).toNat + (x (-2) 9 && x (-2) 12).toNat + (x (-3) 10 && x (-3) 13).toNat + (x (-4) 11 && x (-4) 14).toNat + (x (-5) 12).toNat := by have q := hcov3 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b10239 := hb (x (-5) 12)
      have b10240 := hb (x 7 3)
      have b10241 := hb (x 6 1 && x 6 4)
      have b10242 := hb (x 5 2 && x 5 5)
      have b10243 := hb (x 4 3 && x 4 6)
      have b10244 := hb (x 3 4 && x 3 7)
      have b10245 := hb (x 2 5 && x 2 8)
      have b10246 := hb (x 1 6 && x 1 9)
      have b10247 := hb (x 0 7 && x 0 10)
      have b10248 := hb (x (-1) 8 && x (-1) 11)
      have b10249 := hb (x (-2) 9 && x (-2) 12)
      have b10250 := hb (x (-3) 10 && x (-3) 13)
      have b10251 := hb (x (-4) 11 && x (-4) 14)
      clear * - r10238 b10239 b10240 b10241 b10242 b10243 b10244 b10245 b10246 b10247 b10248 b10249 b10250 b10251 d10148 g37 g38 d10233 g39 g40 g41 g42 g43 d9679 g44 d9489
      omega
    have d10252 : (x (-4) 11).toNat = 1 := by
      have r10253 := hand1 (x (-4) 11) (x (-4) 14)
      have b10254 := hb (x (-4) 11)
      have b10255 := hb (x (-4) 11 && x (-4) 14)
      clear * - r10253 b10254 b10255 d10237
      omega
    have d10256 : (x (-1) 8).toNat = 0 := by
      have r10257 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10258 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
      have e10259 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
      have e10260 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
      have e10261 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
      have e10262 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
      have e10263 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
      have b10264 := hb (x (-8) 7)
      have b10265 := hb (x (-7) 6)
      have b10266 := hb (x (-6) 5)
      have b10267 := hb (x (-5) 4)
      have b10268 := hb (x (-4) 11)
      have b10269 := hb (x (-3) 10)
      have b10270 := hb (x (-2) 9)
      have b10271 := hb (x (-1) 8)
      clear * - r10257 e10258 e10259 e10260 e10261 e10262 e10263 b10264 b10265 b10266 b10267 b10268 b10269 b10270 b10271 d9658 d10252 d9497 d9562 d9429
      omega
    have d10272 : (x (-2) 9).toNat = 0 := by
      have r10273 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10274 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
      have e10275 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
      have e10276 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
      have e10277 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
      have e10278 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
      have e10279 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
      have b10280 := hb (x (-8) 7)
      have b10281 := hb (x (-7) 6)
      have b10282 := hb (x (-6) 5)
      have b10283 := hb (x (-5) 4)
      have b10284 := hb (x (-4) 11)
      have b10285 := hb (x (-3) 10)
      have b10286 := hb (x (-2) 9)
      have b10287 := hb (x (-1) 8)
      clear * - r10273 e10274 e10275 e10276 e10277 e10278 e10279 b10280 b10281 b10282 b10283 b10284 b10285 b10286 b10287 d10256 d9658 d10252 d9497 d9562 d9429
      omega
    have d10288 : (x 6 1 && x 6 7).toNat = 1 := by
      have r10289 : 1 ≤ (x 7 6).toNat + (x 6 1 && x 6 7).toNat + (x 5 2 && x 5 8).toNat + (x 4 3 && x 4 9).toNat + (x 3 4 && x 3 10).toNat + (x 2 5 && x 2 11).toNat + (x 1 6 && x 1 12).toNat + (x 0 7 && x 0 13).toNat + (x (-1) 8 && x (-1) 14).toNat + (x (-2) 9).toNat := by have q := hcov6 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b10290 := hb (x (-2) 9)
      have b10291 := hb (x 7 6)
      have b10292 := hb (x 6 1 && x 6 7)
      have b10293 := hb (x 5 2 && x 5 8)
      have b10294 := hb (x 4 3 && x 4 9)
      have b10295 := hb (x 3 4 && x 3 10)
      have b10296 := hb (x 2 5 && x 2 11)
      have b10297 := hb (x 1 6 && x 1 12)
      have b10298 := hb (x 0 7 && x 0 13)
      have b10299 := hb (x (-1) 8 && x (-1) 14)
      clear * - r10289 b10290 b10291 b10292 b10293 b10294 b10295 b10296 b10297 b10298 b10299 d9804 g61 g62 g63 g64 g65 g66 d9675 d10272
      omega
    have d10300 : (x 6 7).toNat = 1 := by
      have r10301 := hand2 (x 6 1) (x 6 7)
      have b10302 := hb (x 6 7)
      have b10303 := hb (x 6 1 && x 6 7)
      clear * - r10301 b10302 b10303 d10288
      omega
    have d10304 : (x 13 8).toNat = 0 := by
      have r10305 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10306 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
      have e10307 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
      have e10308 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
      have e10309 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
      have e10310 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
      have e10311 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
      have b10312 := hb (x 6 7)
      have b10313 := hb (x 7 6)
      have b10314 := hb (x 8 5)
      have b10315 := hb (x 9 4)
      have b10316 := hb (x 10 11)
      have b10317 := hb (x 11 10)
      have b10318 := hb (x 12 9)
      have b10319 := hb (x 13 8)
      clear * - r10305 e10306 e10307 e10308 e10309 e10310 e10311 b10312 b10313 b10314 b10315 b10316 b10317 b10318 b10319 d9804 d10300
      omega
    have d10320 : (x 13 1 && x 13 8).toNat = 0 := by
      have r10321 := hand2 (x 13 1) (x 13 8)
      have b10322 := hb (x 13 8)
      have b10323 := hb (x 13 1 && x 13 8)
      clear * - r10321 b10322 b10323 d10304
      omega
    have d10324 : (x 12 9).toNat = 0 := by
      have r10325 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10326 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
      have e10327 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
      have e10328 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
      have e10329 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
      have e10330 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
      have e10331 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
      have b10332 := hb (x 6 7)
      have b10333 := hb (x 7 6)
      have b10334 := hb (x 8 5)
      have b10335 := hb (x 9 4)
      have b10336 := hb (x 10 11)
      have b10337 := hb (x 11 10)
      have b10338 := hb (x 12 9)
      have b10339 := hb (x 13 8)
      clear * - r10325 e10326 e10327 e10328 e10329 e10330 e10331 b10332 b10333 b10334 b10335 b10336 b10337 b10338 b10339 d10304 d9804 d10300
      omega
    have d10340 : (x 12 2 && x 12 9).toNat = 0 := by
      have r10341 := hand2 (x 12 2) (x 12 9)
      have b10342 := hb (x 12 9)
      have b10343 := hb (x 12 2 && x 12 9)
      clear * - r10341 b10342 b10343 d10324
      omega
    have d10344 : (x 11 10).toNat = 0 := by
      have r10345 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10346 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
      have e10347 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
      have e10348 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
      have e10349 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
      have e10350 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
      have e10351 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
      have b10352 := hb (x 6 7)
      have b10353 := hb (x 7 6)
      have b10354 := hb (x 8 5)
      have b10355 := hb (x 9 4)
      have b10356 := hb (x 10 11)
      have b10357 := hb (x 11 10)
      have b10358 := hb (x 12 9)
      have b10359 := hb (x 13 8)
      clear * - r10345 e10346 e10347 e10348 e10349 e10350 e10351 b10352 b10353 b10354 b10355 b10356 b10357 b10358 b10359 d10304 d10324 d9804 d10300
      omega
    have d10360 : (x 11 3 && x 11 10).toNat = 0 := by
      have r10361 := hand2 (x 11 3) (x 11 10)
      have b10362 := hb (x 11 10)
      have b10363 := hb (x 11 3 && x 11 10)
      clear * - r10361 b10362 b10363 d10344
      omega
    have d10364 : (x 10 11).toNat = 0 := by
      have r10365 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10366 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
      have e10367 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
      have e10368 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
      have e10369 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
      have e10370 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
      have e10371 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
      have b10372 := hb (x 6 7)
      have b10373 := hb (x 7 6)
      have b10374 := hb (x 8 5)
      have b10375 := hb (x 9 4)
      have b10376 := hb (x 10 11)
      have b10377 := hb (x 11 10)
      have b10378 := hb (x 12 9)
      have b10379 := hb (x 13 8)
      clear * - r10365 e10366 e10367 e10368 e10369 e10370 e10371 b10372 b10373 b10374 b10375 b10376 b10377 b10378 b10379 d10304 d10324 d10344 d9804 d10300
      omega
    have d10380 : (x 9 4).toNat = 0 := by
      have r10381 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10382 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
      have e10383 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
      have e10384 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
      have e10385 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
      have e10386 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
      have e10387 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
      have b10388 := hb (x 6 7)
      have b10389 := hb (x 7 6)
      have b10390 := hb (x 8 5)
      have b10391 := hb (x 9 4)
      have b10392 := hb (x 10 11)
      have b10393 := hb (x 11 10)
      have b10394 := hb (x 12 9)
      have b10395 := hb (x 13 8)
      clear * - r10381 e10382 e10383 e10384 e10385 e10386 e10387 b10388 b10389 b10390 b10391 b10392 b10393 b10394 b10395 d10304 d10324 d10344 d10364 d9804 d10300
      omega
    have d10396 : (x 8 5).toNat = 0 := by
      have r10397 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10398 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
      have e10399 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
      have e10400 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
      have e10401 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
      have e10402 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
      have e10403 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
      have b10404 := hb (x 6 7)
      have b10405 := hb (x 7 6)
      have b10406 := hb (x 8 5)
      have b10407 := hb (x 9 4)
      have b10408 := hb (x 10 11)
      have b10409 := hb (x 11 10)
      have b10410 := hb (x 12 9)
      have b10411 := hb (x 13 8)
      clear * - r10397 e10398 e10399 e10400 e10401 e10402 e10403 b10404 b10405 b10406 b10407 b10408 b10409 b10410 b10411 d10304 d10324 d10344 d10364 d10380 d9804 d10300
      omega
    have d10412 : (x 9 11).toNat = 0 := by
      have r10413 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10414 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
      have e10415 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
      have e10416 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
      have e10417 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
      have e10418 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
      have e10419 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
      have b10420 := hb (x 5 7)
      have b10421 := hb (x 6 6)
      have b10422 := hb (x 7 5)
      have b10423 := hb (x 8 4)
      have b10424 := hb (x 9 11)
      have b10425 := hb (x 10 10)
      have b10426 := hb (x 11 9)
      have b10427 := hb (x 12 8)
      clear * - r10413 e10414 e10415 e10416 e10417 e10418 e10419 b10420 b10421 b10422 b10423 b10424 b10425 b10426 b10427 d10006 d10022 d10038 d9763 d9994
      omega
    have d10428 : (x 8 4).toNat = 0 := by
      have r10429 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10430 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
      have e10431 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
      have e10432 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
      have e10433 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
      have e10434 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
      have e10435 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
      have b10436 := hb (x 5 7)
      have b10437 := hb (x 6 6)
      have b10438 := hb (x 7 5)
      have b10439 := hb (x 8 4)
      have b10440 := hb (x 9 11)
      have b10441 := hb (x 10 10)
      have b10442 := hb (x 11 9)
      have b10443 := hb (x 12 8)
      clear * - r10429 e10430 e10431 e10432 e10433 e10434 e10435 b10436 b10437 b10438 b10439 b10440 b10441 b10442 b10443 d10006 d10022 d10038 d10412 d9763 d9994
      omega
    have d10444 : (x 8 4 && x 8 14).toNat = 0 := by
      have r10445 := hand1 (x 8 4) (x 8 14)
      have b10446 := hb (x 8 4)
      have b10447 := hb (x 8 4 && x 8 14)
      clear * - r10445 b10446 b10447 d10428
      omega
    have d10448 : (x 8 4 && x 8 10).toNat = 0 := by
      have r10449 := hand1 (x 8 4) (x 8 10)
      have b10450 := hb (x 8 4)
      have b10451 := hb (x 8 4 && x 8 10)
      clear * - r10449 b10450 b10451 d10428
      omega
    have d10452 : (x 12 11).toNat = 1 := by
      have r10453 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b10454 := hb (x 8 4)
      have b10455 := hb (x 12 11)
      have b10456 := hb (x 11 1 && x 11 12)
      have b10457 := hb (x 10 2 && x 10 13)
      have b10458 := hb (x 9 3 && x 9 14)
      clear * - r10453 b10454 b10455 b10456 b10457 b10458 d10079 d10095 d9899 d10428
      omega
    have d10459 : (x 12 3).toNat = 1 := by
      have r10460 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
      have b10461 := hb (x 12 3)
      have b10462 := hb (x 12 11)
      clear * - r10460 b10461 b10462 d10452
      omega
    have d10463 : (x 15 12).toNat = 0 := by
      have r10464 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10465 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
      have e10466 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
      have b10467 := hb (x 12 3)
      have b10468 := hb (x 13 2)
      have b10469 := hb (x 14 13)
      have b10470 := hb (x 15 12)
      clear * - r10464 e10465 e10466 b10467 b10468 b10469 b10470 d10459
      omega
    have d10471 : (x 15 4).toNat = 0 := by
      have r10472 : (x 15 4).toNat ≤ (x 15 12).toNat := himp _ _ (hp4 15)
      have b10473 := hb (x 15 4)
      have b10474 := hb (x 15 12)
      clear * - r10472 b10473 b10474 d10463
      omega
    have d10475 : (x 15 4 && x 15 14).toNat = 0 := by
      have r10476 := hand1 (x 15 4) (x 15 14)
      have b10477 := hb (x 15 4)
      have b10478 := hb (x 15 4 && x 15 14)
      clear * - r10476 b10477 b10478 d10471
      omega
    have d10479 : (x 14 13).toNat = 0 := by
      have r10480 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10481 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
      have e10482 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
      have b10483 := hb (x 12 3)
      have b10484 := hb (x 13 2)
      have b10485 := hb (x 14 13)
      have b10486 := hb (x 15 12)
      clear * - r10480 e10481 e10482 b10483 b10484 b10485 b10486 d10463 d10459
      omega
    have d10487 : (x 14 5).toNat = 0 := by
      have r10488 : (x 14 5).toNat ≤ (x 14 13).toNat := himp _ _ (hp5 14)
      have b10489 := hb (x 14 5)
      have b10490 := hb (x 14 13)
      clear * - r10488 b10489 b10490 d10479
      omega
    have d10491 : (x 13 2).toNat = 0 := by
      have r10492 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10493 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
      have e10494 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
      have b10495 := hb (x 12 3)
      have b10496 := hb (x 13 2)
      have b10497 := hb (x 14 13)
      have b10498 := hb (x 15 12)
      clear * - r10492 e10493 e10494 b10495 b10496 b10497 b10498 d10463 d10479 d10459
      omega
    have d10499 : (x 13 10).toNat = 0 := by
      have r10500 : (x 13 10).toNat ≤ (x 13 2).toNat := himp _ _ (hp10 13)
      have b10501 := hb (x 13 2)
      have b10502 := hb (x 13 10)
      clear * - r10500 b10501 b10502 d10491
      omega
    have d10503 : (x 12 1 && x 12 11).toNat = 1 := by
      have r10504 : 1 ≤ (x 13 10).toNat + (x 12 1 && x 12 11).toNat + (x 11 2 && x 11 12).toNat + (x 10 3 && x 10 13).toNat + (x 9 4 && x 9 14).toNat + (x 8 5).toNat := by have q := hcov10 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b10505 := hb (x 8 5)
      have b10506 := hb (x 13 10)
      have b10507 := hb (x 12 1 && x 12 11)
      have b10508 := hb (x 11 2 && x 11 12)
      have b10509 := hb (x 10 3 && x 10 13)
      have b10510 := hb (x 9 4 && x 9 14)
      clear * - r10504 b10505 b10506 b10507 b10508 b10509 b10510 d10499 d10083 d10099 d9903 d10396
      omega
    have d10511 : (x 12 1).toNat = 1 := by
      have r10512 := hand1 (x 12 1) (x 12 11)
      have b10513 := hb (x 12 1)
      have b10514 := hb (x 12 1 && x 12 11)
      clear * - r10512 b10513 b10514 d10503
      omega
    have d10515 : (x 13 14).toNat = 0 := by
      have r10516 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b10517 := hb (x 12 1)
      have b10518 := hb (x 13 14)
      clear * - r10516 b10517 b10518 d10511
      omega
    have d10519 : (x 13 1 && x 13 14).toNat = 0 := by
      have r10520 := hand2 (x 13 1) (x 13 14)
      have b10521 := hb (x 13 14)
      have b10522 := hb (x 13 1 && x 13 14)
      clear * - r10520 b10521 b10522 d10515
      omega
    have d10523 : (x 12 2).toNat = 1 := by
      have r10524 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b10525 := hb (x 12 2)
      have b10526 := hb (x 14 13)
      have b10527 := hb (x 13 1 && x 13 14)
      clear * - r10524 b10525 b10526 b10527 d10479 d10519
      omega
    have d10528 : (x 12 14).toNat = 1 := by
      have r10529 : (x 12 2).toNat ≤ (x 12 14).toNat := himp _ _ (hp2 12)
      have b10530 := hb (x 12 2)
      have b10531 := hb (x 12 14)
      clear * - r10529 b10530 b10531 d10523
      omega
    have d10532 : (x 11 1).toNat = 0 := by
      have r10533 : (x 12 14).toNat + (x 11 1).toNat = 1 := by have q := hd14 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b10534 := hb (x 11 1)
      have b10535 := hb (x 12 14)
      clear * - r10533 b10534 b10535 d10528
      omega
    have d10536 : (x 11 1 && x 11 11).toNat = 0 := by
      have r10537 := hand1 (x 11 1) (x 11 11)
      have b10538 := hb (x 11 1)
      have b10539 := hb (x 11 1 && x 11 11)
      clear * - r10537 b10538 b10539 d10532
      omega
    have d10540 : (x 12 10).toNat = 1 := by
      have r10541 : 1 ≤ (x 12 10).toNat + (x 11 1 && x 11 11).toNat + (x 10 2 && x 10 12).toNat + (x 9 3 && x 9 13).toNat + (x 8 4 && x 8 14).toNat + (x 7 5).toNat := by have q := hcov10 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b10542 := hb (x 7 5)
      have b10543 := hb (x 12 10)
      have b10544 := hb (x 11 1 && x 11 11)
      have b10545 := hb (x 10 2 && x 10 12)
      have b10546 := hb (x 9 3 && x 9 13)
      have b10547 := hb (x 8 4 && x 8 14)
      clear * - r10541 b10542 b10543 b10544 b10545 b10546 b10547 d10536 d10116 d10136 d10444 d9763
      omega
    have d10548 : (x 14 8).toNat = 0 := by
      have r10549 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10550 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
      have e10551 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
      have e10552 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
      have e10553 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
      have e10554 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
      have e10555 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
      have b10556 := hb (x 7 7)
      have b10557 := hb (x 8 6)
      have b10558 := hb (x 9 5)
      have b10559 := hb (x 10 4)
      have b10560 := hb (x 11 11)
      have b10561 := hb (x 12 10)
      have b10562 := hb (x 13 9)
      have b10563 := hb (x 14 8)
      clear * - r10549 e10550 e10551 e10552 e10553 e10554 e10555 b10556 b10557 b10558 b10559 b10560 b10561 b10562 b10563 d10540 d10120 d10140
      omega
    have d10564 : (x 13 9).toNat = 0 := by
      have r10565 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10566 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
      have e10567 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
      have e10568 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
      have e10569 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
      have e10570 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
      have e10571 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
      have b10572 := hb (x 7 7)
      have b10573 := hb (x 8 6)
      have b10574 := hb (x 9 5)
      have b10575 := hb (x 10 4)
      have b10576 := hb (x 11 11)
      have b10577 := hb (x 12 10)
      have b10578 := hb (x 13 9)
      have b10579 := hb (x 14 8)
      clear * - r10565 e10566 e10567 e10568 e10569 e10570 e10571 b10572 b10573 b10574 b10575 b10576 b10577 b10578 b10579 d10548 d10540 d10120 d10140
      omega
    have d10580 : (x 11 11).toNat = 0 := by
      have r10581 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10582 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
      have e10583 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
      have e10584 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
      have e10585 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
      have e10586 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
      have e10587 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
      have b10588 := hb (x 7 7)
      have b10589 := hb (x 8 6)
      have b10590 := hb (x 9 5)
      have b10591 := hb (x 10 4)
      have b10592 := hb (x 11 11)
      have b10593 := hb (x 12 10)
      have b10594 := hb (x 13 9)
      have b10595 := hb (x 14 8)
      clear * - r10581 e10582 e10583 e10584 e10585 e10586 e10587 b10588 b10589 b10590 b10591 b10592 b10593 b10594 b10595 d10548 d10564 d10540 d10120 d10140
      omega
    have d10596 : (x 8 6).toNat = 0 := by
      have r10597 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10598 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
      have e10599 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
      have e10600 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
      have e10601 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
      have e10602 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
      have e10603 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
      have b10604 := hb (x 7 7)
      have b10605 := hb (x 8 6)
      have b10606 := hb (x 9 5)
      have b10607 := hb (x 10 4)
      have b10608 := hb (x 11 11)
      have b10609 := hb (x 12 10)
      have b10610 := hb (x 13 9)
      have b10611 := hb (x 14 8)
      clear * - r10597 e10598 e10599 e10600 e10601 e10602 e10603 b10604 b10605 b10606 b10607 b10608 b10609 b10610 b10611 d10548 d10564 d10540 d10580 d10120 d10140
      omega
    have d10612 : (x 8 6 && x 8 13).toNat = 0 := by
      have r10613 := hand1 (x 8 6) (x 8 13)
      have b10614 := hb (x 8 6)
      have b10615 := hb (x 8 6 && x 8 13)
      clear * - r10613 b10614 b10615 d10596
      omega
    have d10616 : (x 14 7).toNat = 1 := by
      have r10617 : 1 ≤ (x 14 7).toNat + (x 13 1 && x 13 8).toNat + (x 12 2 && x 12 9).toNat + (x 11 3 && x 11 10).toNat + (x 10 4 && x 10 11).toNat + (x 9 5 && x 9 12).toNat + (x 8 6 && x 8 13).toNat + (x 7 7 && x 7 14).toNat + (x 6 8).toNat := by have q := hcov7 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b10618 := hb (x 6 8)
      have b10619 := hb (x 14 7)
      have b10620 := hb (x 13 1 && x 13 8)
      have b10621 := hb (x 12 2 && x 12 9)
      have b10622 := hb (x 11 3 && x 11 10)
      have b10623 := hb (x 10 4 && x 10 11)
      have b10624 := hb (x 9 5 && x 9 12)
      have b10625 := hb (x 8 6 && x 8 13)
      have b10626 := hb (x 7 7 && x 7 14)
      clear * - r10617 b10618 b10619 b10620 b10621 b10622 b10623 b10624 b10625 b10626 d10320 d10340 d10360 d10124 d10144 d10612 d9800 g28
      omega
    have d10627 : (x 21 8).toNat = 0 := by
      have r10628 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10629 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
      have e10630 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
      have e10631 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
      have e10632 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
      have e10633 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
      have e10634 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
      have b10635 := hb (x 14 7)
      have b10636 := hb (x 15 6)
      have b10637 := hb (x 16 5)
      have b10638 := hb (x 17 4)
      have b10639 := hb (x 18 11)
      have b10640 := hb (x 19 10)
      have b10641 := hb (x 20 9)
      have b10642 := hb (x 21 8)
      clear * - r10628 e10629 e10630 e10631 e10632 e10633 e10634 b10635 b10636 b10637 b10638 b10639 b10640 b10641 b10642 d10616
      omega
    have d10643 : (x 20 9).toNat = 0 := by
      have r10644 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10645 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
      have e10646 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
      have e10647 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
      have e10648 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
      have e10649 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
      have e10650 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
      have b10651 := hb (x 14 7)
      have b10652 := hb (x 15 6)
      have b10653 := hb (x 16 5)
      have b10654 := hb (x 17 4)
      have b10655 := hb (x 18 11)
      have b10656 := hb (x 19 10)
      have b10657 := hb (x 20 9)
      have b10658 := hb (x 21 8)
      clear * - r10644 e10645 e10646 e10647 e10648 e10649 e10650 b10651 b10652 b10653 b10654 b10655 b10656 b10657 b10658 d10627 d10616
      omega
    have d10659 : (x 19 10).toNat = 0 := by
      have r10660 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10661 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
      have e10662 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
      have e10663 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
      have e10664 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
      have e10665 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
      have e10666 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
      have b10667 := hb (x 14 7)
      have b10668 := hb (x 15 6)
      have b10669 := hb (x 16 5)
      have b10670 := hb (x 17 4)
      have b10671 := hb (x 18 11)
      have b10672 := hb (x 19 10)
      have b10673 := hb (x 20 9)
      have b10674 := hb (x 21 8)
      clear * - r10660 e10661 e10662 e10663 e10664 e10665 e10666 b10667 b10668 b10669 b10670 b10671 b10672 b10673 b10674 d10627 d10643 d10616
      omega
    have d10675 : (x 19 1 && x 19 10).toNat = 0 := by
      have r10676 := hand2 (x 19 1) (x 19 10)
      have b10677 := hb (x 19 10)
      have b10678 := hb (x 19 1 && x 19 10)
      clear * - r10676 b10677 b10678 d10659
      omega
    have d10679 : (x 18 11).toNat = 0 := by
      have r10680 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10681 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
      have e10682 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
      have e10683 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
      have e10684 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
      have e10685 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
      have e10686 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
      have b10687 := hb (x 14 7)
      have b10688 := hb (x 15 6)
      have b10689 := hb (x 16 5)
      have b10690 := hb (x 17 4)
      have b10691 := hb (x 18 11)
      have b10692 := hb (x 19 10)
      have b10693 := hb (x 20 9)
      have b10694 := hb (x 21 8)
      clear * - r10680 e10681 e10682 e10683 e10684 e10685 e10686 b10687 b10688 b10689 b10690 b10691 b10692 b10693 b10694 d10627 d10643 d10659 d10616
      omega
    have d10695 : (x 18 1 && x 18 11).toNat = 0 := by
      have r10696 := hand2 (x 18 1) (x 18 11)
      have b10697 := hb (x 18 11)
      have b10698 := hb (x 18 1 && x 18 11)
      clear * - r10696 b10697 b10698 d10679
      omega
    have d10699 : (x 18 2 && x 18 11).toNat = 0 := by
      have r10700 := hand2 (x 18 2) (x 18 11)
      have b10701 := hb (x 18 11)
      have b10702 := hb (x 18 2 && x 18 11)
      clear * - r10700 b10701 b10702 d10679
      omega
    have d10703 : (x 11 1 && x 11 7).toNat = 0 := by
      have r10704 := hand1 (x 11 1) (x 11 7)
      have b10705 := hb (x 11 1)
      have b10706 := hb (x 11 1 && x 11 7)
      clear * - r10704 b10705 b10706 d10532
      omega
    have d10707 : (x 12 6).toNat = 1 := by
      have r10708 : 1 ≤ (x 12 6).toNat + (x 11 1 && x 11 7).toNat + (x 10 2 && x 10 8).toNat + (x 9 3 && x 9 9).toNat + (x 8 4 && x 8 10).toNat + (x 7 5 && x 7 11).toNat + (x 6 6 && x 6 12).toNat + (x 5 7 && x 5 13).toNat + (x 4 8 && x 4 14).toNat + (x 3 9).toNat := by have q := hcov6 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b10709 := hb (x 3 9)
      have b10710 := hb (x 12 6)
      have b10711 := hb (x 11 1 && x 11 7)
      have b10712 := hb (x 10 2 && x 10 8)
      have b10713 := hb (x 9 3 && x 9 9)
      have b10714 := hb (x 8 4 && x 8 10)
      have b10715 := hb (x 7 5 && x 7 11)
      have b10716 := hb (x 6 6 && x 6 12)
      have b10717 := hb (x 5 7 && x 5 13)
      have b10718 := hb (x 4 8 && x 4 14)
      clear * - r10708 b10709 b10710 b10711 b10712 b10713 b10714 b10715 b10716 b10717 b10718 d10703 d10213 d10180 d10448 d9767 g67 g68 g69 g20
      omega
    have d10719 : (x 18 8).toNat = 0 := by
      have r10720 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10721 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
      have e10722 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
      have e10723 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
      have e10724 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
      have e10725 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
      have e10726 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
      have b10727 := hb (x 11 7)
      have b10728 := hb (x 12 6)
      have b10729 := hb (x 13 5)
      have b10730 := hb (x 14 4)
      have b10731 := hb (x 15 11)
      have b10732 := hb (x 16 10)
      have b10733 := hb (x 17 9)
      have b10734 := hb (x 18 8)
      clear * - r10720 e10721 e10722 e10723 e10724 e10725 e10726 b10727 b10728 b10729 b10730 b10731 b10732 b10733 b10734 d10707
      omega
    have d10735 : (x 17 9).toNat = 0 := by
      have r10736 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10737 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
      have e10738 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
      have e10739 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
      have e10740 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
      have e10741 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
      have e10742 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
      have b10743 := hb (x 11 7)
      have b10744 := hb (x 12 6)
      have b10745 := hb (x 13 5)
      have b10746 := hb (x 14 4)
      have b10747 := hb (x 15 11)
      have b10748 := hb (x 16 10)
      have b10749 := hb (x 17 9)
      have b10750 := hb (x 18 8)
      clear * - r10736 e10737 e10738 e10739 e10740 e10741 e10742 b10743 b10744 b10745 b10746 b10747 b10748 b10749 b10750 d10719 d10707
      omega
    have d10751 : (x 16 10).toNat = 0 := by
      have r10752 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10753 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
      have e10754 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
      have e10755 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
      have e10756 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
      have e10757 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
      have e10758 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
      have b10759 := hb (x 11 7)
      have b10760 := hb (x 12 6)
      have b10761 := hb (x 13 5)
      have b10762 := hb (x 14 4)
      have b10763 := hb (x 15 11)
      have b10764 := hb (x 16 10)
      have b10765 := hb (x 17 9)
      have b10766 := hb (x 18 8)
      clear * - r10752 e10753 e10754 e10755 e10756 e10757 e10758 b10759 b10760 b10761 b10762 b10763 b10764 b10765 b10766 d10719 d10735 d10707
      omega
    have d10767 : (x 15 11).toNat = 0 := by
      have r10768 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10769 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
      have e10770 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
      have e10771 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
      have e10772 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
      have e10773 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
      have e10774 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
      have b10775 := hb (x 11 7)
      have b10776 := hb (x 12 6)
      have b10777 := hb (x 13 5)
      have b10778 := hb (x 14 4)
      have b10779 := hb (x 15 11)
      have b10780 := hb (x 16 10)
      have b10781 := hb (x 17 9)
      have b10782 := hb (x 18 8)
      clear * - r10768 e10769 e10770 e10771 e10772 e10773 e10774 b10775 b10776 b10777 b10778 b10779 b10780 b10781 b10782 d10719 d10735 d10751 d10707
      omega
    have d10783 : (x 14 4).toNat = 0 := by
      have r10784 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10785 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
      have e10786 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
      have e10787 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
      have e10788 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
      have e10789 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
      have e10790 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
      have b10791 := hb (x 11 7)
      have b10792 := hb (x 12 6)
      have b10793 := hb (x 13 5)
      have b10794 := hb (x 14 4)
      have b10795 := hb (x 15 11)
      have b10796 := hb (x 16 10)
      have b10797 := hb (x 17 9)
      have b10798 := hb (x 18 8)
      clear * - r10784 e10785 e10786 e10787 e10788 e10789 e10790 b10791 b10792 b10793 b10794 b10795 b10796 b10797 b10798 d10719 d10735 d10751 d10767 d10707
      omega
    have d10799 : (x 14 4 && x 14 14).toNat = 0 := by
      have r10800 := hand1 (x 14 4) (x 14 14)
      have b10801 := hb (x 14 4)
      have b10802 := hb (x 14 4 && x 14 14)
      clear * - r10800 b10801 b10802 d10783
      omega
    have d10803 : (x 13 5).toNat = 0 := by
      have r10804 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10805 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
      have e10806 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
      have e10807 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
      have e10808 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
      have e10809 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
      have e10810 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
      have b10811 := hb (x 11 7)
      have b10812 := hb (x 12 6)
      have b10813 := hb (x 13 5)
      have b10814 := hb (x 14 4)
      have b10815 := hb (x 15 11)
      have b10816 := hb (x 16 10)
      have b10817 := hb (x 17 9)
      have b10818 := hb (x 18 8)
      clear * - r10804 e10805 e10806 e10807 e10808 e10809 e10810 b10811 b10812 b10813 b10814 b10815 b10816 b10817 b10818 d10719 d10735 d10751 d10767 d10783 d10707
      omega
    have d10819 : (x 11 7).toNat = 0 := by
      have r10820 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10821 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
      have e10822 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
      have e10823 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
      have e10824 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
      have e10825 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
      have e10826 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
      have b10827 := hb (x 11 7)
      have b10828 := hb (x 12 6)
      have b10829 := hb (x 13 5)
      have b10830 := hb (x 14 4)
      have b10831 := hb (x 15 11)
      have b10832 := hb (x 16 10)
      have b10833 := hb (x 17 9)
      have b10834 := hb (x 18 8)
      clear * - r10820 e10821 e10822 e10823 e10824 e10825 e10826 b10827 b10828 b10829 b10830 b10831 b10832 b10833 b10834 d10719 d10735 d10751 d10767 d10783 d10803 d10707
      omega
    have d10835 : (x 17 1).toNat = 0 := by
      have r10836 : (x 17 1).toNat + (x 16 2).toNat + (x 15 3).toNat + (x 14 4).toNat + (x 13 5).toNat + (x 12 6).toNat + (x 11 7).toNat + (x 10 8).toNat + (x 9 9).toNat + (x 8 10).toNat + (x 7 11).toNat + (x 6 12).toNat + (x 5 13).toNat + (x 4 14).toNat = 3 := by have q := hcount 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b10837 := hb (x 4 14)
      have b10838 := hb (x 5 13)
      have b10839 := hb (x 6 12)
      have b10840 := hb (x 7 11)
      have b10841 := hb (x 8 10)
      have b10842 := hb (x 9 9)
      have b10843 := hb (x 10 8)
      have b10844 := hb (x 11 7)
      have b10845 := hb (x 12 6)
      have b10846 := hb (x 13 5)
      have b10847 := hb (x 14 4)
      have b10848 := hb (x 15 3)
      have b10849 := hb (x 16 2)
      have b10850 := hb (x 17 1)
      clear * - r10836 b10837 b10838 b10839 b10840 b10841 b10842 b10843 b10844 b10845 b10846 b10847 b10848 b10849 b10850 d10783 d10803 d10707 d10819 d10197 d10176 d10193 d10156 g29 g26 g22
      omega
    have d10851 : (x 17 1 && x 17 14).toNat = 0 := by
      have r10852 := hand1 (x 17 1) (x 17 14)
      have b10853 := hb (x 17 1)
      have b10854 := hb (x 17 1 && x 17 14)
      clear * - r10852 b10853 b10854 d10835
      omega
    have d10855 : (x 17 1 && x 17 11).toNat = 0 := by
      have r10856 := hand1 (x 17 1) (x 17 11)
      have b10857 := hb (x 17 1)
      have b10858 := hb (x 17 1 && x 17 11)
      clear * - r10856 b10857 b10858 d10835
      omega
    have d10859 : (x 17 13).toNat = 0 := by
      have r10860 : (x 17 13).toNat ≤ (x 17 1).toNat := himp _ _ (hp13 17)
      have b10861 := hb (x 17 1)
      have b10862 := hb (x 17 13)
      clear * - r10860 b10861 b10862 d10835
      omega
    have d10863 : (x 16 2).toNat = 0 := by
      have r10864 : (x 17 1).toNat + (x 16 2).toNat + (x 15 3).toNat + (x 14 4).toNat + (x 13 5).toNat + (x 12 6).toNat + (x 11 7).toNat + (x 10 8).toNat + (x 9 9).toNat + (x 8 10).toNat + (x 7 11).toNat + (x 6 12).toNat + (x 5 13).toNat + (x 4 14).toNat = 3 := by have q := hcount 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b10865 := hb (x 4 14)
      have b10866 := hb (x 5 13)
      have b10867 := hb (x 6 12)
      have b10868 := hb (x 7 11)
      have b10869 := hb (x 8 10)
      have b10870 := hb (x 9 9)
      have b10871 := hb (x 10 8)
      have b10872 := hb (x 11 7)
      have b10873 := hb (x 12 6)
      have b10874 := hb (x 13 5)
      have b10875 := hb (x 14 4)
      have b10876 := hb (x 15 3)
      have b10877 := hb (x 16 2)
      have b10878 := hb (x 17 1)
      clear * - r10864 b10865 b10866 b10867 b10868 b10869 b10870 b10871 b10872 b10873 b10874 b10875 b10876 b10877 b10878 d10835 d10783 d10803 d10707 d10819 d10197 d10176 d10193 d10156 g29 g26 g22
      omega
    have d10879 : (x 16 2 && x 16 12).toNat = 0 := by
      have r10880 := hand1 (x 16 2) (x 16 12)
      have b10881 := hb (x 16 2)
      have b10882 := hb (x 16 2 && x 16 12)
      clear * - r10880 b10881 b10882 d10863
      omega
    have d10883 : (x 18 13).toNat = 1 := by
      have r10884 : 1 ≤ (x 18 13).toNat + (x 17 1 && x 17 14).toNat + (x 16 2).toNat := by have q := hcov13 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b10885 := hb (x 16 2)
      have b10886 := hb (x 18 13)
      have b10887 := hb (x 17 1 && x 17 14)
      clear * - r10884 b10885 b10886 b10887 d10851 d10863
      omega
    have d10888 : (x 19 12).toNat = 0 := by
      have r10889 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10890 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
      have e10891 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
      have b10892 := hb (x 16 3)
      have b10893 := hb (x 17 2)
      have b10894 := hb (x 18 13)
      have b10895 := hb (x 19 12)
      clear * - r10889 e10890 e10891 b10892 b10893 b10894 b10895 d10883
      omega
    have d10896 : (x 17 2).toNat = 0 := by
      have r10897 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10898 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
      have e10899 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
      have b10900 := hb (x 16 3)
      have b10901 := hb (x 17 2)
      have b10902 := hb (x 18 13)
      have b10903 := hb (x 19 12)
      clear * - r10897 e10898 e10899 b10900 b10901 b10902 b10903 d10888 d10883
      omega
    have d10904 : (x 17 2 && x 17 12).toNat = 0 := by
      have r10905 := hand1 (x 17 2) (x 17 12)
      have b10906 := hb (x 17 2)
      have b10907 := hb (x 17 2 && x 17 12)
      clear * - r10905 b10906 b10907 d10896
      omega
    have d10908 : (x 16 3 && x 16 13).toNat = 1 := by
      have r10909 : 1 ≤ (x 19 10).toNat + (x 18 1 && x 18 11).toNat + (x 17 2 && x 17 12).toNat + (x 16 3 && x 16 13).toNat + (x 15 4 && x 15 14).toNat + (x 14 5).toNat := by have q := hcov10 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b10910 := hb (x 14 5)
      have b10911 := hb (x 19 10)
      have b10912 := hb (x 18 1 && x 18 11)
      have b10913 := hb (x 17 2 && x 17 12)
      have b10914 := hb (x 16 3 && x 16 13)
      have b10915 := hb (x 15 4 && x 15 14)
      clear * - r10909 b10910 b10911 b10912 b10913 b10914 b10915 d10659 d10695 d10904 d10475 d10487
      omega
    have d10916 : (x 16 13).toNat = 1 := by
      have r10917 := hand2 (x 16 3) (x 16 13)
      have b10918 := hb (x 16 13)
      have b10919 := hb (x 16 3 && x 16 13)
      clear * - r10917 b10918 b10919 d10908
      omega
    have d10920 : (x 17 12).toNat = 0 := by
      have r10921 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10922 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
      have e10923 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
      have b10924 := hb (x 14 3)
      have b10925 := hb (x 15 2)
      have b10926 := hb (x 16 13)
      have b10927 := hb (x 17 12)
      clear * - r10921 e10922 e10923 b10924 b10925 b10926 b10927 d10916
      omega
    have d10928 : (x 17 3 && x 17 12).toNat = 0 := by
      have r10929 := hand2 (x 17 3) (x 17 12)
      have b10930 := hb (x 17 12)
      have b10931 := hb (x 17 3 && x 17 12)
      clear * - r10929 b10930 b10931 d10920
      omega
    have d10932 : (x 15 2).toNat = 0 := by
      have r10933 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10934 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
      have e10935 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
      have b10936 := hb (x 14 3)
      have b10937 := hb (x 15 2)
      have b10938 := hb (x 16 13)
      have b10939 := hb (x 17 12)
      clear * - r10933 e10934 e10935 b10936 b10937 b10938 b10939 d10920 d10916
      omega
    have d10940 : (x 16 1 && x 16 14).toNat = 1 := by
      have r10941 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := by have q := hcov13 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b10942 := hb (x 15 2)
      have b10943 := hb (x 17 13)
      have b10944 := hb (x 16 1 && x 16 14)
      clear * - r10941 b10942 b10943 b10944 d10859 d10932
      omega
    have d10945 : (x 16 14).toNat = 1 := by
      have r10946 := hand2 (x 16 1) (x 16 14)
      have b10947 := hb (x 16 14)
      have b10948 := hb (x 16 1 && x 16 14)
      clear * - r10946 b10947 b10948 d10940
      omega
    have d10949 : (x 15 1).toNat = 0 := by
      have r10950 : (x 16 14).toNat + (x 15 1).toNat = 1 := by have q := hd14 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b10951 := hb (x 15 1)
      have b10952 := hb (x 16 14)
      clear * - r10950 b10951 b10952 d10945
      omega
    have d10953 : (x 15 13).toNat = 0 := by
      have r10954 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
      have b10955 := hb (x 15 1)
      have b10956 := hb (x 15 13)
      clear * - r10954 b10955 b10956 d10949
      omega
    have d10957 : (x 15 3 && x 15 13).toNat = 0 := by
      have r10958 := hand2 (x 15 3) (x 15 13)
      have b10959 := hb (x 15 13)
      have b10960 := hb (x 15 3 && x 15 13)
      clear * - r10958 b10959 b10960 d10953
      omega
    have d10961 : (x 18 10).toNat = 1 := by
      have r10962 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := by have q := hcov10 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b10963 := hb (x 13 5)
      have b10964 := hb (x 18 10)
      have b10965 := hb (x 17 1 && x 17 11)
      have b10966 := hb (x 16 2 && x 16 12)
      have b10967 := hb (x 15 3 && x 15 13)
      have b10968 := hb (x 14 4 && x 14 14)
      clear * - r10962 b10963 b10964 b10965 b10966 b10967 b10968 d10855 d10879 d10957 d10799 d10803
      omega
    have d10969 : (x 18 2).toNat = 1 := by
      have r10970 : (x 18 10).toNat ≤ (x 18 2).toNat := himp _ _ (hp10 18)
      have b10971 := hb (x 18 2)
      have b10972 := hb (x 18 10)
      clear * - r10970 b10971 b10972 d10961
      omega
    have d10973 : (x 20 12).toNat = 0 := by
      have r10974 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10975 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
      have e10976 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
      have b10977 := hb (x 17 3)
      have b10978 := hb (x 18 2)
      have b10979 := hb (x 19 13)
      have b10980 := hb (x 20 12)
      clear * - r10974 e10975 e10976 b10977 b10978 b10979 b10980 d10969
      omega
    have d10981 : (x 19 13).toNat = 0 := by
      have r10982 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10983 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
      have e10984 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
      have b10985 := hb (x 17 3)
      have b10986 := hb (x 18 2)
      have b10987 := hb (x 19 13)
      have b10988 := hb (x 20 12)
      clear * - r10982 e10983 e10984 b10985 b10986 b10987 b10988 d10973 d10969
      omega
    have d10989 : (x 17 3).toNat = 0 := by
      have r10990 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10991 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
      have e10992 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
      have b10993 := hb (x 17 3)
      have b10994 := hb (x 18 2)
      have b10995 := hb (x 19 13)
      have b10996 := hb (x 20 12)
      clear * - r10990 e10991 e10992 b10993 b10994 b10995 b10996 d10973 d10981 d10969
      omega
    have d10997 : (x 17 11).toNat = 0 := by
      have r10998 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
      have b10999 := hb (x 17 3)
      have b11000 := hb (x 17 11)
      clear * - r10998 b10999 b11000 d10989
      omega
    have d11001 : (x 20 8).toNat = 0 := by
      have r11002 : (x 20 8).toNat + (x 19 1 && x 19 9).toNat + (x 18 2 && x 18 10).toNat + (x 17 3 && x 17 11).toNat + (x 16 4 && x 16 12).toNat + (x 15 5 && x 15 13).toNat + (x 14 6 && x 14 14).toNat + (x 13 7).toNat = 1 := by have q := hd8 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e11003 : (x 19 1 && x 19 9).toNat = (x 19 9).toNat := handr _ _ (fun h => hp9 19 (h))
      have e11004 : (x 18 2 && x 18 10).toNat = (x 18 10).toNat := handr _ _ (fun h => hp10 18 (h))
      have e11005 : (x 17 3 && x 17 11).toNat = (x 17 11).toNat := handr _ _ (fun h => hp11 17 (h))
      have e11006 : (x 16 4 && x 16 12).toNat = (x 16 4).toNat := handl _ _ (fun h => hp4 16 (h))
      have e11007 : (x 15 5 && x 15 13).toNat = (x 15 5).toNat := handl _ _ (fun h => hp5 15 (h))
      have e11008 : (x 14 6 && x 14 14).toNat = (x 14 6).toNat := handl _ _ (fun h => hp6 14 (h))
      have b11009 := hb (x 13 7)
      have b11010 := hb (x 14 6)
      have b11011 := hb (x 15 5)
      have b11012 := hb (x 16 4)
      have b11013 := hb (x 17 11)
      have b11014 := hb (x 18 10)
      have b11015 := hb (x 19 9)
      have b11016 := hb (x 20 8)
      clear * - r11002 e11003 e11004 e11005 e11006 e11007 e11008 b11009 b11010 b11011 b11012 b11013 b11014 b11015 b11016 d10961 d10997
      omega
    have d11017 : (x 19 9).toNat = 0 := by
      have r11018 : (x 20 8).toNat + (x 19 1 && x 19 9).toNat + (x 18 2 && x 18 10).toNat + (x 17 3 && x 17 11).toNat + (x 16 4 && x 16 12).toNat + (x 15 5 && x 15 13).toNat + (x 14 6 && x 14 14).toNat + (x 13 7).toNat = 1 := by have q := hd8 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e11019 : (x 19 1 && x 19 9).toNat = (x 19 9).toNat := handr _ _ (fun h => hp9 19 (h))
      have e11020 : (x 18 2 && x 18 10).toNat = (x 18 10).toNat := handr _ _ (fun h => hp10 18 (h))
      have e11021 : (x 17 3 && x 17 11).toNat = (x 17 11).toNat := handr _ _ (fun h => hp11 17 (h))
      have e11022 : (x 16 4 && x 16 12).toNat = (x 16 4).toNat := handl _ _ (fun h => hp4 16 (h))
      have e11023 : (x 15 5 && x 15 13).toNat = (x 15 5).toNat := handl _ _ (fun h => hp5 15 (h))
      have e11024 : (x 14 6 && x 14 14).toNat = (x 14 6).toNat := handl _ _ (fun h => hp6 14 (h))
      have b11025 := hb (x 13 7)
      have b11026 := hb (x 14 6)
      have b11027 := hb (x 15 5)
      have b11028 := hb (x 16 4)
      have b11029 := hb (x 17 11)
      have b11030 := hb (x 18 10)
      have b11031 := hb (x 19 9)
      have b11032 := hb (x 20 8)
      clear * - r11018 e11019 e11020 e11021 e11022 e11023 e11024 b11025 b11026 b11027 b11028 b11029 b11030 b11031 b11032 d11001 d10961 d10997
      omega
    have d11033 : (x 16 4).toNat = 0 := by
      have r11034 : (x 20 8).toNat + (x 19 1 && x 19 9).toNat + (x 18 2 && x 18 10).toNat + (x 17 3 && x 17 11).toNat + (x 16 4 && x 16 12).toNat + (x 15 5 && x 15 13).toNat + (x 14 6 && x 14 14).toNat + (x 13 7).toNat = 1 := by have q := hd8 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e11035 : (x 19 1 && x 19 9).toNat = (x 19 9).toNat := handr _ _ (fun h => hp9 19 (h))
      have e11036 : (x 18 2 && x 18 10).toNat = (x 18 10).toNat := handr _ _ (fun h => hp10 18 (h))
      have e11037 : (x 17 3 && x 17 11).toNat = (x 17 11).toNat := handr _ _ (fun h => hp11 17 (h))
      have e11038 : (x 16 4 && x 16 12).toNat = (x 16 4).toNat := handl _ _ (fun h => hp4 16 (h))
      have e11039 : (x 15 5 && x 15 13).toNat = (x 15 5).toNat := handl _ _ (fun h => hp5 15 (h))
      have e11040 : (x 14 6 && x 14 14).toNat = (x 14 6).toNat := handl _ _ (fun h => hp6 14 (h))
      have b11041 := hb (x 13 7)
      have b11042 := hb (x 14 6)
      have b11043 := hb (x 15 5)
      have b11044 := hb (x 16 4)
      have b11045 := hb (x 17 11)
      have b11046 := hb (x 18 10)
      have b11047 := hb (x 19 9)
      have b11048 := hb (x 20 8)
      clear * - r11034 e11035 e11036 e11037 e11038 e11039 e11040 b11041 b11042 b11043 b11044 b11045 b11046 b11047 b11048 d11001 d11017 d10961 d10997
      omega
    have d11049 : (x 16 4 && x 16 13).toNat = 0 := by
      have r11050 := hand1 (x 16 4) (x 16 13)
      have b11051 := hb (x 16 4)
      have b11052 := hb (x 16 4 && x 16 13)
      clear * - r11050 b11051 b11052 d11033
      omega
    have d11053 : (x 15 5).toNat = 0 := by
      have r11054 : (x 20 8).toNat + (x 19 1 && x 19 9).toNat + (x 18 2 && x 18 10).toNat + (x 17 3 && x 17 11).toNat + (x 16 4 && x 16 12).toNat + (x 15 5 && x 15 13).toNat + (x 14 6 && x 14 14).toNat + (x 13 7).toNat = 1 := by have q := hd8 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e11055 : (x 19 1 && x 19 9).toNat = (x 19 9).toNat := handr _ _ (fun h => hp9 19 (h))
      have e11056 : (x 18 2 && x 18 10).toNat = (x 18 10).toNat := handr _ _ (fun h => hp10 18 (h))
      have e11057 : (x 17 3 && x 17 11).toNat = (x 17 11).toNat := handr _ _ (fun h => hp11 17 (h))
      have e11058 : (x 16 4 && x 16 12).toNat = (x 16 4).toNat := handl _ _ (fun h => hp4 16 (h))
      have e11059 : (x 15 5 && x 15 13).toNat = (x 15 5).toNat := handl _ _ (fun h => hp5 15 (h))
      have e11060 : (x 14 6 && x 14 14).toNat = (x 14 6).toNat := handl _ _ (fun h => hp6 14 (h))
      have b11061 := hb (x 13 7)
      have b11062 := hb (x 14 6)
      have b11063 := hb (x 15 5)
      have b11064 := hb (x 16 4)
      have b11065 := hb (x 17 11)
      have b11066 := hb (x 18 10)
      have b11067 := hb (x 19 9)
      have b11068 := hb (x 20 8)
      clear * - r11054 e11055 e11056 e11057 e11058 e11059 e11060 b11061 b11062 b11063 b11064 b11065 b11066 b11067 b11068 d11001 d11017 d10961 d10997 d11033
      omega
    have d11069 : (x 15 5 && x 15 14).toNat = 0 := by
      have r11070 := hand1 (x 15 5) (x 15 14)
      have b11071 := hb (x 15 5)
      have b11072 := hb (x 15 5 && x 15 14)
      clear * - r11070 b11071 b11072 d11053
      omega
    have d11073 : (x 14 6).toNat = 1 := by
      have r11074 : 1 ≤ (x 20 9).toNat + (x 19 1 && x 19 10).toNat + (x 18 2 && x 18 11).toNat + (x 17 3 && x 17 12).toNat + (x 16 4 && x 16 13).toNat + (x 15 5 && x 15 14).toNat + (x 14 6).toNat := by have q := hcov9 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b11075 := hb (x 14 6)
      have b11076 := hb (x 20 9)
      have b11077 := hb (x 19 1 && x 19 10)
      have b11078 := hb (x 18 2 && x 18 11)
      have b11079 := hb (x 17 3 && x 17 12)
      have b11080 := hb (x 16 4 && x 16 13)
      have b11081 := hb (x 15 5 && x 15 14)
      clear * - r11074 b11075 b11076 b11077 b11078 b11079 b11080 b11081 d10643 d10675 d10699 d10928 d11049 d11069
      omega
    have r11082 : (x 20 8).toNat + (x 19 1 && x 19 9).toNat + (x 18 2 && x 18 10).toNat + (x 17 3 && x 17 11).toNat + (x 16 4 && x 16 12).toNat + (x 15 5 && x 15 13).toNat + (x 14 6 && x 14 14).toNat + (x 13 7).toNat = 1 := by have q := hd8 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11083 : (x 19 1 && x 19 9).toNat = (x 19 9).toNat := handr _ _ (fun h => hp9 19 (h))
    have e11084 : (x 18 2 && x 18 10).toNat = (x 18 10).toNat := handr _ _ (fun h => hp10 18 (h))
    have e11085 : (x 17 3 && x 17 11).toNat = (x 17 11).toNat := handr _ _ (fun h => hp11 17 (h))
    have e11086 : (x 16 4 && x 16 12).toNat = (x 16 4).toNat := handl _ _ (fun h => hp4 16 (h))
    have e11087 : (x 15 5 && x 15 13).toNat = (x 15 5).toNat := handl _ _ (fun h => hp5 15 (h))
    have e11088 : (x 14 6 && x 14 14).toNat = (x 14 6).toNat := handl _ _ (fun h => hp6 14 (h))
    have b11089 := hb (x 13 7)
    have b11090 := hb (x 14 6)
    have b11091 := hb (x 15 5)
    have b11092 := hb (x 16 4)
    have b11093 := hb (x 17 11)
    have b11094 := hb (x 18 10)
    have b11095 := hb (x 19 9)
    have b11096 := hb (x 20 8)
    linarith only [r11082, e11083, e11084, e11085, e11086, e11087, e11088, b11089, b11090, b11091, b11092, b11093, b11094, b11095, b11096, d11001, d11017, d10961, d10997, d11033, d11053, d11073]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_four_iff_five_core_b11 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-1) 5).toNat = 0)
    (g1 : (x 0 6).toNat = 1)
    (g2 : (x 1 2).toNat = 0)
    (g3 : (x 1 5).toNat = 0)
    (g4 : (x 2 4).toNat = 0)
    (g5 : (x 3 4).toNat = 0)
    (g6 : (x 5 2).toNat = 0)
    (g7 : (x 6 13).toNat = 0)
    (g8 : (x 2 2 && x 2 12).toNat = 0)
    (g9 : (x 1 3 && x 1 13).toNat = 0)
    (g10 : (x 0 4 && x 0 14).toNat = 0)
    (g11 : (x 7 2 && x 7 12).toNat = 0)
    (g12 : (x 6 3 && x 6 13).toNat = 0)
    (g13 : (x 5 2 && x 5 13).toNat = 0)
    (g14 : (x 7 1 && x 7 12).toNat = 0)
    (g15 : (x 6 2 && x 6 13).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d11098 : (x 6 8).toNat = 0 := by
    have r11099 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11100 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e11101 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e11102 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e11103 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e11104 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e11105 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b11106 := hb (x (-1) 7)
    have b11107 := hb (x 0 6)
    have b11108 := hb (x 1 5)
    have b11109 := hb (x 2 4)
    have b11110 := hb (x 3 11)
    have b11111 := hb (x 4 10)
    have b11112 := hb (x 5 9)
    have b11113 := hb (x 6 8)
    clear * - r11099 e11100 e11101 e11102 e11103 e11104 e11105 b11106 b11107 b11108 b11109 b11110 b11111 b11112 b11113 g4 g3 g1
    omega
  have d11114 : (x 5 9).toNat = 0 := by
    have r11115 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11116 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e11117 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e11118 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e11119 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e11120 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e11121 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b11122 := hb (x (-1) 7)
    have b11123 := hb (x 0 6)
    have b11124 := hb (x 1 5)
    have b11125 := hb (x 2 4)
    have b11126 := hb (x 3 11)
    have b11127 := hb (x 4 10)
    have b11128 := hb (x 5 9)
    have b11129 := hb (x 6 8)
    clear * - r11115 e11116 e11117 e11118 e11119 e11120 e11121 b11122 b11123 b11124 b11125 b11126 b11127 b11128 b11129 d11098 g4 g3 g1
    omega
  have d11130 : (x 4 10).toNat = 0 := by
    have r11131 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11132 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e11133 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e11134 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e11135 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e11136 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e11137 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b11138 := hb (x (-1) 7)
    have b11139 := hb (x 0 6)
    have b11140 := hb (x 1 5)
    have b11141 := hb (x 2 4)
    have b11142 := hb (x 3 11)
    have b11143 := hb (x 4 10)
    have b11144 := hb (x 5 9)
    have b11145 := hb (x 6 8)
    clear * - r11131 e11132 e11133 e11134 e11135 e11136 e11137 b11138 b11139 b11140 b11141 b11142 b11143 b11144 b11145 d11098 d11114 g4 g3 g1
    omega
  have d11146 : (x 3 1 && x 3 11).toNat = 1 := by
    have r11147 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11148 := hb (x (-1) 5)
    have b11149 := hb (x 4 10)
    have b11150 := hb (x 3 1 && x 3 11)
    have b11151 := hb (x 2 2 && x 2 12)
    have b11152 := hb (x 1 3 && x 1 13)
    have b11153 := hb (x 0 4 && x 0 14)
    clear * - r11147 b11148 b11149 b11150 b11151 b11152 b11153 d11130 g8 g9 g10 g0
    omega
  have d11154 : (x 3 11).toNat = 1 := by
    have r11155 := hand2 (x 3 1) (x 3 11)
    have b11156 := hb (x 3 11)
    have b11157 := hb (x 3 1 && x 3 11)
    clear * - r11155 b11156 b11157 d11146
    omega
  have d11158 : (x 3 3).toNat = 1 := by
    have r11159 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
    have b11160 := hb (x 3 3)
    have b11161 := hb (x 3 11)
    clear * - r11159 b11160 b11161 d11154
    omega
  have d11162 : (x 6 12).toNat = 0 := by
    have r11163 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11164 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e11165 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b11166 := hb (x 3 3)
    have b11167 := hb (x 4 2)
    have b11168 := hb (x 5 13)
    have b11169 := hb (x 6 12)
    clear * - r11163 e11164 e11165 b11166 b11167 b11168 b11169 d11158
    omega
  have d11170 : (x 6 1 && x 6 12).toNat = 0 := by
    have r11171 := hand2 (x 6 1) (x 6 12)
    have b11172 := hb (x 6 12)
    have b11173 := hb (x 6 1 && x 6 12)
    clear * - r11171 b11172 b11173 d11162
    omega
  have d11174 : (x 5 13).toNat = 0 := by
    have r11175 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11176 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e11177 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b11178 := hb (x 3 3)
    have b11179 := hb (x 4 2)
    have b11180 := hb (x 5 13)
    have b11181 := hb (x 6 12)
    clear * - r11175 e11176 e11177 b11178 b11179 b11180 b11181 d11162 d11158
    omega
  have d11182 : (x 4 2).toNat = 0 := by
    have r11183 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11184 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e11185 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b11186 := hb (x 3 3)
    have b11187 := hb (x 4 2)
    have b11188 := hb (x 5 13)
    have b11189 := hb (x 6 12)
    clear * - r11183 e11184 e11185 b11186 b11187 b11188 b11189 d11162 d11174 d11158
    omega
  have d11190 : (x 5 1 && x 5 14).toNat = 1 := by
    have r11191 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11192 := hb (x 4 2)
    have b11193 := hb (x 6 13)
    have b11194 := hb (x 5 1 && x 5 14)
    clear * - r11191 b11192 b11193 b11194 g7 d11182
    omega
  have d11195 : (x 5 14).toNat = 1 := by
    have r11196 := hand2 (x 5 1) (x 5 14)
    have b11197 := hb (x 5 14)
    have b11198 := hb (x 5 1 && x 5 14)
    clear * - r11196 b11197 b11198 d11190
    omega
  have d11199 : (x 4 1).toNat = 0 := by
    have r11200 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11201 := hb (x 4 1)
    have b11202 := hb (x 5 14)
    clear * - r11200 b11201 b11202 d11195
    omega
  have d11203 : (x 4 1 && x 4 14).toNat = 0 := by
    have r11204 := hand1 (x 4 1) (x 4 14)
    have b11205 := hb (x 4 1)
    have b11206 := hb (x 4 1 && x 4 14)
    clear * - r11204 b11205 b11206 d11199
    omega
  have d11207 : (x 3 2).toNat = 1 := by
    have r11208 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11209 := hb (x 3 2)
    have b11210 := hb (x 5 13)
    have b11211 := hb (x 4 1 && x 4 14)
    clear * - r11208 b11209 b11210 b11211 d11174 d11203
    omega
  have d11212 : (x 3 14).toNat = 1 := by
    have r11213 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
    have b11214 := hb (x 3 2)
    have b11215 := hb (x 3 14)
    clear * - r11213 b11214 b11215 d11207
    omega
  have d11216 : (x 2 1).toNat = 0 := by
    have r11217 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11218 := hb (x 2 1)
    have b11219 := hb (x 3 14)
    clear * - r11217 b11218 b11219 d11212
    omega
  have d11220 : (x 2 1 && x 2 14).toNat = 0 := by
    have r11221 := hand1 (x 2 1) (x 2 14)
    have b11222 := hb (x 2 1)
    have b11223 := hb (x 2 1 && x 2 14)
    clear * - r11221 b11222 b11223 d11216
    omega
  have d11224 : (x 3 13).toNat = 1 := by
    have r11225 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11226 := hb (x 1 2)
    have b11227 := hb (x 3 13)
    have b11228 := hb (x 2 1 && x 2 14)
    clear * - r11225 b11226 b11227 b11228 d11220 g2
    omega
  have d11229 : (x 3 1).toNat = 1 := by
    have r11230 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
    have b11231 := hb (x 3 1)
    have b11232 := hb (x 3 13)
    clear * - r11230 b11231 b11232 d11224
    omega
  have d11233 : (x 4 14).toNat = 0 := by
    have r11234 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11235 := hb (x 3 1)
    have b11236 := hb (x 4 14)
    clear * - r11234 b11235 b11236 d11229
    omega
  have d11237 : (x 4 3 && x 4 14).toNat = 0 := by
    have r11238 := hand2 (x 4 3) (x 4 14)
    have b11239 := hb (x 4 14)
    have b11240 := hb (x 4 3 && x 4 14)
    clear * - r11238 b11239 b11240 d11233
    omega
  have d11241 : (x 7 11).toNat = 1 := by
    have r11242 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11243 := hb (x 3 4)
    have b11244 := hb (x 7 11)
    have b11245 := hb (x 6 1 && x 6 12)
    have b11246 := hb (x 5 2 && x 5 13)
    have b11247 := hb (x 4 3 && x 4 14)
    clear * - r11242 b11243 b11244 b11245 b11246 b11247 d11170 g13 d11237 g5
    omega
  have d11248 : (x 7 3).toNat = 1 := by
    have r11249 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
    have b11250 := hb (x 7 3)
    have b11251 := hb (x 7 11)
    clear * - r11249 b11250 b11251 d11241
    omega
  have d11252 : (x 10 12).toNat = 0 := by
    have r11253 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11254 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e11255 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b11256 := hb (x 7 3)
    have b11257 := hb (x 8 2)
    have b11258 := hb (x 9 13)
    have b11259 := hb (x 10 12)
    clear * - r11253 e11254 e11255 b11256 b11257 b11258 b11259 d11248
    omega
  have d11260 : (x 9 13).toNat = 0 := by
    have r11261 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11262 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e11263 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b11264 := hb (x 7 3)
    have b11265 := hb (x 8 2)
    have b11266 := hb (x 9 13)
    have b11267 := hb (x 10 12)
    clear * - r11261 e11262 e11263 b11264 b11265 b11266 b11267 d11252 d11248
    omega
  have d11268 : (x 8 2).toNat = 0 := by
    have r11269 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11270 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e11271 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b11272 := hb (x 7 3)
    have b11273 := hb (x 8 2)
    have b11274 := hb (x 9 13)
    have b11275 := hb (x 10 12)
    clear * - r11269 e11270 e11271 b11272 b11273 b11274 b11275 d11252 d11260 d11248
    omega
  have d11276 : (x 4 12).toNat = 0 := by
    have r11277 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11278 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e11279 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b11280 := hb (x 1 3)
    have b11281 := hb (x 2 2)
    have b11282 := hb (x 3 13)
    have b11283 := hb (x 4 12)
    clear * - r11277 e11278 e11279 b11280 b11281 b11282 b11283 d11224
    omega
  have d11284 : (x 4 4).toNat = 0 := by
    have r11285 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
    have b11286 := hb (x 4 4)
    have b11287 := hb (x 4 12)
    clear * - r11285 b11286 b11287 d11276
    omega
  have d11288 : (x 5 12).toNat = 0 := by
    have r11289 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11290 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e11291 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b11292 := hb (x 2 3)
    have b11293 := hb (x 3 2)
    have b11294 := hb (x 4 13)
    have b11295 := hb (x 5 12)
    clear * - r11289 e11290 e11291 b11292 b11293 b11294 b11295 d11207
    omega
  have d11296 : (x 5 4).toNat = 0 := by
    have r11297 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
    have b11298 := hb (x 5 4)
    have b11299 := hb (x 5 12)
    clear * - r11297 b11298 b11299 d11288
    omega
  have d11300 : (x 5 4 && x 5 14).toNat = 0 := by
    have r11301 := hand1 (x 5 4) (x 5 14)
    have b11302 := hb (x 5 4)
    have b11303 := hb (x 5 4 && x 5 14)
    clear * - r11301 b11302 b11303 d11296
    omega
  have d11304 : (x 4 13).toNat = 0 := by
    have r11305 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11306 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e11307 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b11308 := hb (x 2 3)
    have b11309 := hb (x 3 2)
    have b11310 := hb (x 4 13)
    have b11311 := hb (x 5 12)
    clear * - r11305 e11306 e11307 b11308 b11309 b11310 b11311 d11288 d11207
    omega
  have d11312 : (x 4 5).toNat = 0 := by
    have r11313 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
    have b11314 := hb (x 4 5)
    have b11315 := hb (x 4 13)
    clear * - r11313 b11314 b11315 d11304
    omega
  have d11316 : (x 5 1).toNat = 1 := by
    have r11317 := hand1 (x 5 1) (x 5 14)
    have b11318 := hb (x 5 1)
    have b11319 := hb (x 5 1 && x 5 14)
    clear * - r11317 b11318 b11319 d11190
    omega
  have d11320 : (x 6 14).toNat = 0 := by
    have r11321 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11322 := hb (x 5 1)
    have b11323 := hb (x 6 14)
    clear * - r11321 b11322 b11323 d11316
    omega
  have d11324 : (x 6 1 && x 6 14).toNat = 0 := by
    have r11325 := hand2 (x 6 1) (x 6 14)
    have b11326 := hb (x 6 14)
    have b11327 := hb (x 6 1 && x 6 14)
    clear * - r11325 b11326 b11327 d11320
    omega
  have d11328 : (x 7 13).toNat = 1 := by
    have r11329 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11330 := hb (x 5 2)
    have b11331 := hb (x 7 13)
    have b11332 := hb (x 6 1 && x 6 14)
    clear * - r11329 b11330 b11331 b11332 d11324 g6
    omega
  have d11333 : (x 8 12).toNat = 0 := by
    have r11334 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11335 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e11336 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b11337 := hb (x 5 3)
    have b11338 := hb (x 6 2)
    have b11339 := hb (x 7 13)
    have b11340 := hb (x 8 12)
    clear * - r11334 e11335 e11336 b11337 b11338 b11339 b11340 d11328
    omega
  have d11341 : (x 6 2).toNat = 0 := by
    have r11342 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11343 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e11344 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b11345 := hb (x 5 3)
    have b11346 := hb (x 6 2)
    have b11347 := hb (x 7 13)
    have b11348 := hb (x 8 12)
    clear * - r11342 e11343 e11344 b11345 b11346 b11347 b11348 d11333 d11328
    omega
  have d11349 : (x 5 3).toNat = 0 := by
    have r11350 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11351 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e11352 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b11353 := hb (x 5 3)
    have b11354 := hb (x 6 2)
    have b11355 := hb (x 7 13)
    have b11356 := hb (x 8 12)
    clear * - r11350 e11351 e11352 b11353 b11354 b11355 b11356 d11333 d11328 d11341
    omega
  have d11357 : (x 5 3 && x 5 14).toNat = 0 := by
    have r11358 := hand1 (x 5 3) (x 5 14)
    have b11359 := hb (x 5 3)
    have b11360 := hb (x 5 3 && x 5 14)
    clear * - r11358 b11359 b11360 d11349
    omega
  have d11361 : (x 8 11).toNat = 1 := by
    have r11362 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11363 := hb (x 4 4)
    have b11364 := hb (x 8 11)
    have b11365 := hb (x 7 1 && x 7 12)
    have b11366 := hb (x 6 2 && x 6 13)
    have b11367 := hb (x 5 3 && x 5 14)
    clear * - r11362 b11363 b11364 b11365 b11366 b11367 g14 g15 d11357 d11284
    omega
  have d11368 : (x 8 3).toNat = 1 := by
    have r11369 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
    have b11370 := hb (x 8 3)
    have b11371 := hb (x 8 11)
    clear * - r11369 b11370 b11371 d11361
    omega
  have d11372 : (x 11 12).toNat = 0 := by
    have r11373 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11374 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e11375 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b11376 := hb (x 8 3)
    have b11377 := hb (x 9 2)
    have b11378 := hb (x 10 13)
    have b11379 := hb (x 11 12)
    clear * - r11373 e11374 e11375 b11376 b11377 b11378 b11379 d11368
    omega
  have d11380 : (x 10 13).toNat = 0 := by
    have r11381 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11382 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e11383 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b11384 := hb (x 8 3)
    have b11385 := hb (x 9 2)
    have b11386 := hb (x 10 13)
    have b11387 := hb (x 11 12)
    clear * - r11381 e11382 e11383 b11384 b11385 b11386 b11387 d11372 d11368
    omega
  have d11388 : (x 9 1 && x 9 14).toNat = 1 := by
    have r11389 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11390 := hb (x 8 2)
    have b11391 := hb (x 10 13)
    have b11392 := hb (x 9 1 && x 9 14)
    clear * - r11389 b11390 b11391 b11392 d11380 d11268
    omega
  have d11393 : (x 9 14).toNat = 1 := by
    have r11394 := hand2 (x 9 1) (x 9 14)
    have b11395 := hb (x 9 14)
    have b11396 := hb (x 9 1 && x 9 14)
    clear * - r11394 b11395 b11396 d11388
    omega
  have d11397 : (x 8 1).toNat = 0 := by
    have r11398 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11399 := hb (x 8 1)
    have b11400 := hb (x 9 14)
    clear * - r11398 b11399 b11400 d11393
    omega
  have d11401 : (x 8 1 && x 8 11).toNat = 0 := by
    have r11402 := hand1 (x 8 1) (x 8 11)
    have b11403 := hb (x 8 1)
    have b11404 := hb (x 8 1 && x 8 11)
    clear * - r11402 b11403 b11404 d11397
    omega
  have d11405 : (x 9 10).toNat = 1 := by
    have r11406 : 1 ≤ (x 9 10).toNat + (x 8 1 && x 8 11).toNat + (x 7 2 && x 7 12).toNat + (x 6 3 && x 6 13).toNat + (x 5 4 && x 5 14).toNat + (x 4 5).toNat := by have q := hcov10 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11407 := hb (x 4 5)
    have b11408 := hb (x 9 10)
    have b11409 := hb (x 8 1 && x 8 11)
    have b11410 := hb (x 7 2 && x 7 12)
    have b11411 := hb (x 6 3 && x 6 13)
    have b11412 := hb (x 5 4 && x 5 14)
    clear * - r11406 b11407 b11408 b11409 b11410 b11411 b11412 d11401 g11 g12 d11300 d11312
    omega
  have d11413 : (x 9 2).toNat = 1 := by
    have r11414 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
    have b11415 := hb (x 9 2)
    have b11416 := hb (x 9 10)
    clear * - r11414 b11415 b11416 d11405
    omega
  have r11417 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e11418 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
  have e11419 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
  have b11420 := hb (x 8 3)
  have b11421 := hb (x 9 2)
  have b11422 := hb (x 10 13)
  have b11423 := hb (x 11 12)
  linarith only [r11417, e11418, e11419, b11420, b11421, b11422, b11423, d11372, d11380, d11413, d11368]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_four_iff_five_core_a0000_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-2) 2).toNat = 0)
    (g1 : (x (-1) 13).toNat = 0)
    (g2 : (x 0 1).toNat = 0)
    (g3 : (x 0 11).toNat = 0)
    (g4 : (x 1 11).toNat = 0)
    (g5 : (x (-2) 2 && x (-2) 13).toNat = 0)
    (g6 : (x (-3) 3 && x (-3) 14).toNat = 0)
    (g7 : (x (-1) 2 && x (-1) 13).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d11856 : (x 0 1 && x 0 12).toNat = 0 := by
    have r11857 := hand1 (x 0 1) (x 0 12)
    have b11858 := hb (x 0 1)
    have b11859 := hb (x 0 1 && x 0 12)
    clear * - r11857 b11858 b11859 g2
    omega
  have d11860 : (x 0 13).toNat = 0 := by
    have r11861 : (x 0 13).toNat ≤ (x 0 1).toNat := himp _ _ (hp13 0)
    have b11862 := hb (x 0 1)
    have b11863 := hb (x 0 13)
    clear * - r11861 b11862 b11863 g2
    omega
  have d11864 : (x (-1) 1 && x (-1) 14).toNat = 1 := by
    have r11865 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11866 := hb (x (-2) 2)
    have b11867 := hb (x 0 13)
    have b11868 := hb (x (-1) 1 && x (-1) 14)
    clear * - r11865 b11866 b11867 b11868 d11860 g0
    omega
  have d11869 : (x (-1) 14).toNat = 1 := by
    have r11870 := hand2 (x (-1) 1) (x (-1) 14)
    have b11871 := hb (x (-1) 14)
    have b11872 := hb (x (-1) 1 && x (-1) 14)
    clear * - r11870 b11871 b11872 d11864
    omega
  have d11873 : (x (-2) 1).toNat = 0 := by
    have r11874 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11875 := hb (x (-2) 1)
    have b11876 := hb (x (-1) 14)
    clear * - r11874 b11875 b11876 d11869
    omega
  have d11877 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
    have r11878 := hand1 (x (-2) 1) (x (-2) 14)
    have b11879 := hb (x (-2) 1)
    have b11880 := hb (x (-2) 1 && x (-2) 14)
    clear * - r11878 b11879 b11880 d11873
    omega
  have d11881 : (x (-2) 13).toNat = 0 := by
    have r11882 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
    have b11883 := hb (x (-2) 1)
    have b11884 := hb (x (-2) 13)
    clear * - r11882 b11883 b11884 d11873
    omega
  have d11885 : (x (-3) 2).toNat = 1 := by
    have r11886 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11887 := hb (x (-3) 2)
    have b11888 := hb (x (-1) 13)
    have b11889 := hb (x (-2) 1 && x (-2) 14)
    clear * - r11886 b11887 b11888 b11889 g1 d11877
    omega
  have d11890 : (x (-3) 14).toNat = 1 := by
    have r11891 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
    have b11892 := hb (x (-3) 2)
    have b11893 := hb (x (-3) 14)
    clear * - r11891 b11892 b11893 d11885
    omega
  have d11894 : (x (-4) 1).toNat = 0 := by
    have r11895 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11896 := hb (x (-4) 1)
    have b11897 := hb (x (-3) 14)
    clear * - r11895 b11896 b11897 d11890
    omega
  have d11898 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
    have r11899 := hand1 (x (-4) 1) (x (-4) 14)
    have b11900 := hb (x (-4) 1)
    have b11901 := hb (x (-4) 1 && x (-4) 14)
    clear * - r11899 b11900 b11901 d11894
    omega
  have d11902 : (x (-4) 13).toNat = 0 := by
    have r11903 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
    have b11904 := hb (x (-4) 1)
    have b11905 := hb (x (-4) 13)
    clear * - r11903 b11904 b11905 d11894
    omega
  have d11906 : (x (-1) 12).toNat = 0 := by
    have r11907 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11908 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e11909 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b11910 := hb (x (-4) 3)
    have b11911 := hb (x (-3) 2)
    have b11912 := hb (x (-2) 13)
    have b11913 := hb (x (-1) 12)
    clear * - r11907 e11908 e11909 b11910 b11911 b11912 b11913 d11881 d11885
    omega
  have d11914 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
    have r11915 := hand2 (x (-1) 1) (x (-1) 12)
    have b11916 := hb (x (-1) 12)
    have b11917 := hb (x (-1) 1 && x (-1) 12)
    clear * - r11915 b11916 b11917 d11906
    omega
  have d11918 : (x (-4) 3).toNat = 0 := by
    have r11919 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11920 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e11921 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b11922 := hb (x (-4) 3)
    have b11923 := hb (x (-3) 2)
    have b11924 := hb (x (-2) 13)
    have b11925 := hb (x (-1) 12)
    clear * - r11919 e11920 e11921 b11922 b11923 b11924 b11925 d11906 d11881 d11885
    omega
  have d11926 : (x (-4) 11).toNat = 0 := by
    have r11927 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
    have b11928 := hb (x (-4) 3)
    have b11929 := hb (x (-4) 11)
    clear * - r11927 b11928 b11929 d11918
    omega
  have d11930 : (x (-4) 4).toNat = 1 := by
    have r11931 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11932 := hb (x (-4) 4)
    have b11933 := hb (x 0 11)
    have b11934 := hb (x (-1) 1 && x (-1) 12)
    have b11935 := hb (x (-2) 2 && x (-2) 13)
    have b11936 := hb (x (-3) 3 && x (-3) 14)
    clear * - r11931 b11932 b11933 b11934 b11935 b11936 g3 d11914 g5 g6
    omega
  have d11937 : (x (-4) 12).toNat = 1 := by
    have r11938 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
    have b11939 := hb (x (-4) 4)
    have b11940 := hb (x (-4) 12)
    clear * - r11938 b11939 b11940 d11930
    omega
  have d11941 : (x (-5) 13).toNat = 0 := by
    have r11942 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11943 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e11944 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b11945 := hb (x (-7) 3)
    have b11946 := hb (x (-6) 2)
    have b11947 := hb (x (-5) 13)
    have b11948 := hb (x (-4) 12)
    clear * - r11942 e11943 e11944 b11945 b11946 b11947 b11948 d11937
    omega
  have d11949 : (x (-6) 2).toNat = 0 := by
    have r11950 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11951 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e11952 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b11953 := hb (x (-7) 3)
    have b11954 := hb (x (-6) 2)
    have b11955 := hb (x (-5) 13)
    have b11956 := hb (x (-4) 12)
    clear * - r11950 e11951 e11952 b11953 b11954 b11955 b11956 d11937 d11941
    omega
  have d11957 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
    have r11958 := hand1 (x (-6) 2) (x (-6) 13)
    have b11959 := hb (x (-6) 2)
    have b11960 := hb (x (-6) 2 && x (-6) 13)
    clear * - r11958 b11959 b11960 d11949
    omega
  have d11961 : (x (-6) 2 && x (-6) 12).toNat = 0 := by
    have r11962 := hand1 (x (-6) 2) (x (-6) 12)
    have b11963 := hb (x (-6) 2)
    have b11964 := hb (x (-6) 2 && x (-6) 12)
    clear * - r11962 b11963 b11964 d11949
    omega
  have d11965 : (x (-5) 1 && x (-5) 14).toNat = 1 := by
    have r11966 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11967 := hb (x (-6) 2)
    have b11968 := hb (x (-4) 13)
    have b11969 := hb (x (-5) 1 && x (-5) 14)
    clear * - r11966 b11967 b11968 b11969 d11902 d11949
    omega
  have d11970 : (x (-5) 14).toNat = 1 := by
    have r11971 := hand2 (x (-5) 1) (x (-5) 14)
    have b11972 := hb (x (-5) 14)
    have b11973 := hb (x (-5) 1 && x (-5) 14)
    clear * - r11971 b11972 b11973 d11965
    omega
  have d11974 : (x (-6) 1).toNat = 0 := by
    have r11975 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11976 := hb (x (-6) 1)
    have b11977 := hb (x (-5) 14)
    clear * - r11975 b11976 b11977 d11970
    omega
  have d11978 : (x (-6) 1 && x (-6) 14).toNat = 0 := by
    have r11979 := hand1 (x (-6) 1) (x (-6) 14)
    have b11980 := hb (x (-6) 1)
    have b11981 := hb (x (-6) 1 && x (-6) 14)
    clear * - r11979 b11980 b11981 d11974
    omega
  have d11982 : (x (-7) 2).toNat = 1 := by
    have r11983 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11984 := hb (x (-7) 2)
    have b11985 := hb (x (-5) 13)
    have b11986 := hb (x (-6) 1 && x (-6) 14)
    clear * - r11983 b11984 b11985 b11986 d11941 d11978
    omega
  have d11987 : (x (-7) 14).toNat = 1 := by
    have r11988 : (x (-7) 2).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp2 (-7))
    have b11989 := hb (x (-7) 2)
    have b11990 := hb (x (-7) 14)
    clear * - r11988 b11989 b11990 d11982
    omega
  have d11991 : (x (-8) 1).toNat = 0 := by
    have r11992 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11993 := hb (x (-8) 1)
    have b11994 := hb (x (-7) 14)
    clear * - r11992 b11993 b11994 d11987
    omega
  have d11995 : (x (-8) 13).toNat = 0 := by
    have r11996 : (x (-8) 13).toNat ≤ (x (-8) 1).toNat := himp _ _ (hp13 (-8))
    have b11997 := hb (x (-8) 1)
    have b11998 := hb (x (-8) 13)
    clear * - r11996 b11997 b11998 d11991
    omega
  have d11999 : (x (-5) 12).toNat = 0 := by
    have r12000 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12001 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
    have e12002 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
    have b12003 := hb (x (-8) 3)
    have b12004 := hb (x (-7) 2)
    have b12005 := hb (x (-6) 13)
    have b12006 := hb (x (-5) 12)
    clear * - r12000 e12001 e12002 b12003 b12004 b12005 b12006 d11982
    omega
  have d12007 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
    have r12008 := hand2 (x (-5) 1) (x (-5) 12)
    have b12009 := hb (x (-5) 12)
    have b12010 := hb (x (-5) 1 && x (-5) 12)
    clear * - r12008 b12009 b12010 d11999
    omega
  have d12011 : (x (-5) 1).toNat = 1 := by
    have r12012 := hand1 (x (-5) 1) (x (-5) 14)
    have b12013 := hb (x (-5) 1)
    have b12014 := hb (x (-5) 1 && x (-5) 14)
    clear * - r12012 b12013 b12014 d11965
    omega
  have d12015 : (x (-4) 14).toNat = 0 := by
    have r12016 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12017 := hb (x (-5) 1)
    have b12018 := hb (x (-4) 14)
    clear * - r12016 b12017 b12018 d12011
    omega
  have d12019 : (x (-4) 2).toNat = 0 := by
    have r12020 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
    have b12021 := hb (x (-4) 2)
    have b12022 := hb (x (-4) 14)
    clear * - r12020 b12021 b12022 d12015
    omega
  have d12023 : (x (-4) 10).toNat = 0 := by
    have r12024 : (x (-4) 10).toNat ≤ (x (-4) 2).toNat := himp _ _ (hp10 (-4))
    have b12025 := hb (x (-4) 2)
    have b12026 := hb (x (-4) 10)
    clear * - r12024 b12025 b12026 d12019
    omega
  have d12027 : (x (-3) 1 && x (-3) 14).toNat = 1 := by
    have r12028 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12029 := hb (x (-4) 2)
    have b12030 := hb (x (-2) 13)
    have b12031 := hb (x (-3) 1 && x (-3) 14)
    clear * - r12028 b12029 b12030 b12031 d11881 d12019
    omega
  have d12032 : (x (-3) 1).toNat = 1 := by
    have r12033 := hand1 (x (-3) 1) (x (-3) 14)
    have b12034 := hb (x (-3) 1)
    have b12035 := hb (x (-3) 1 && x (-3) 14)
    clear * - r12033 b12034 b12035 d12027
    omega
  have d12036 : (x (-2) 14).toNat = 0 := by
    have r12037 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12038 := hb (x (-3) 1)
    have b12039 := hb (x (-2) 14)
    clear * - r12037 b12038 b12039 d12032
    omega
  have d12040 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
    have r12041 := hand2 (x (-2) 3) (x (-2) 14)
    have b12042 := hb (x (-2) 14)
    have b12043 := hb (x (-2) 3 && x (-2) 14)
    clear * - r12041 b12042 b12043 d12036
    omega
  have d12044 : (x (-3) 4).toNat = 1 := by
    have r12045 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12046 := hb (x (-3) 4)
    have b12047 := hb (x 1 11)
    have b12048 := hb (x 0 1 && x 0 12)
    have b12049 := hb (x (-1) 2 && x (-1) 13)
    have b12050 := hb (x (-2) 3 && x (-2) 14)
    clear * - r12045 b12046 b12047 b12048 b12049 b12050 g4 d11856 g7 d12040
    omega
  have d12051 : (x (-3) 12).toNat = 1 := by
    have r12052 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
    have b12053 := hb (x (-3) 4)
    have b12054 := hb (x (-3) 12)
    clear * - r12052 b12053 b12054 d12044
    omega
  have d12055 : (x (-5) 2).toNat = 0 := by
    have r12056 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12057 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
    have e12058 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
    have b12059 := hb (x (-6) 3)
    have b12060 := hb (x (-5) 2)
    have b12061 := hb (x (-4) 13)
    have b12062 := hb (x (-3) 12)
    clear * - r12056 e12057 e12058 b12059 b12060 b12061 b12062 d12051 d11902
    omega
  have d12063 : (x (-3) 13).toNat = 1 := by
    have r12064 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12065 := hb (x (-5) 2)
    have b12066 := hb (x (-3) 13)
    have b12067 := hb (x (-4) 1 && x (-4) 14)
    clear * - r12064 b12065 b12066 b12067 d11898 d12055
    omega
  have d12068 : (x (-2) 12).toNat = 0 := by
    have r12069 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12070 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
    have e12071 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
    have b12072 := hb (x (-5) 3)
    have b12073 := hb (x (-4) 2)
    have b12074 := hb (x (-3) 13)
    have b12075 := hb (x (-2) 12)
    clear * - r12069 e12070 e12071 b12072 b12073 b12074 b12075 d12063 d12019
    omega
  have d12076 : (x (-5) 3).toNat = 0 := by
    have r12077 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12078 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
    have e12079 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
    have b12080 := hb (x (-5) 3)
    have b12081 := hb (x (-4) 2)
    have b12082 := hb (x (-3) 13)
    have b12083 := hb (x (-2) 12)
    clear * - r12077 e12078 e12079 b12080 b12081 b12082 b12083 d12068 d12063 d12019
    omega
  have d12084 : (x (-5) 11).toNat = 0 := by
    have r12085 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
    have b12086 := hb (x (-5) 3)
    have b12087 := hb (x (-5) 11)
    clear * - r12085 b12086 b12087 d12076
    omega
  have d12088 : (x (-5) 1 && x (-5) 11).toNat = 0 := by
    have r12089 := hand2 (x (-5) 1) (x (-5) 11)
    have b12090 := hb (x (-5) 11)
    have b12091 := hb (x (-5) 1 && x (-5) 11)
    clear * - r12089 b12090 b12091 d12084
    omega
  have d12092 : (x (-7) 3).toNat = 0 := by
    have r12093 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12094 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e12095 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b12096 := hb (x (-7) 3)
    have b12097 := hb (x (-6) 2)
    have b12098 := hb (x (-5) 13)
    have b12099 := hb (x (-4) 12)
    clear * - r12093 e12094 e12095 b12096 b12097 b12098 b12099 d11937 d11941 d11949
    omega
  have d12100 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
    have r12101 := hand1 (x (-7) 3) (x (-7) 14)
    have b12102 := hb (x (-7) 3)
    have b12103 := hb (x (-7) 3 && x (-7) 14)
    clear * - r12101 b12102 b12103 d12092
    omega
  have d12104 : (x (-7) 3 && x (-7) 13).toNat = 0 := by
    have r12105 := hand1 (x (-7) 3) (x (-7) 13)
    have b12106 := hb (x (-7) 3)
    have b12107 := hb (x (-7) 3 && x (-7) 13)
    clear * - r12105 b12106 b12107 d12092
    omega
  have d12108 : (x (-8) 4).toNat = 1 := by
    have r12109 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12110 := hb (x (-8) 4)
    have b12111 := hb (x (-4) 11)
    have b12112 := hb (x (-5) 1 && x (-5) 12)
    have b12113 := hb (x (-6) 2 && x (-6) 13)
    have b12114 := hb (x (-7) 3 && x (-7) 14)
    clear * - r12109 b12110 b12111 b12112 b12113 b12114 d11926 d12007 d11957 d12100
    omega
  have d12115 : (x (-8) 12).toNat = 1 := by
    have r12116 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
    have b12117 := hb (x (-8) 4)
    have b12118 := hb (x (-8) 12)
    clear * - r12116 b12117 b12118 d12108
    omega
  have d12119 : (x (-9) 13).toNat = 0 := by
    have r12120 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12121 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
    have e12122 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
    have b12123 := hb (x (-11) 3)
    have b12124 := hb (x (-10) 2)
    have b12125 := hb (x (-9) 13)
    have b12126 := hb (x (-8) 12)
    clear * - r12120 e12121 e12122 b12123 b12124 b12125 b12126 d12115
    omega
  have d12127 : (x (-9) 5).toNat = 0 := by
    have r12128 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
    have b12129 := hb (x (-9) 5)
    have b12130 := hb (x (-9) 13)
    clear * - r12128 b12129 b12130 d12119
    omega
  have d12131 : (x (-10) 2).toNat = 0 := by
    have r12132 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12133 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
    have e12134 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
    have b12135 := hb (x (-11) 3)
    have b12136 := hb (x (-10) 2)
    have b12137 := hb (x (-9) 13)
    have b12138 := hb (x (-8) 12)
    clear * - r12132 e12133 e12134 b12135 b12136 b12137 b12138 d12115 d12119
    omega
  have d12139 : (x (-9) 1 && x (-9) 14).toNat = 1 := by
    have r12140 : 1 ≤ (x (-8) 13).toNat + (x (-9) 1 && x (-9) 14).toNat + (x (-10) 2).toNat := by have q := hcov13 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12141 := hb (x (-10) 2)
    have b12142 := hb (x (-8) 13)
    have b12143 := hb (x (-9) 1 && x (-9) 14)
    clear * - r12140 b12141 b12142 b12143 d11995 d12131
    omega
  have d12144 : (x (-9) 1).toNat = 1 := by
    have r12145 := hand1 (x (-9) 1) (x (-9) 14)
    have b12146 := hb (x (-9) 1)
    have b12147 := hb (x (-9) 1 && x (-9) 14)
    clear * - r12145 b12146 b12147 d12139
    omega
  have d12148 : (x (-8) 14).toNat = 0 := by
    have r12149 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12150 := hb (x (-9) 1)
    have b12151 := hb (x (-8) 14)
    clear * - r12149 b12150 b12151 d12144
    omega
  have d12152 : (x (-8) 4 && x (-8) 14).toNat = 0 := by
    have r12153 := hand2 (x (-8) 4) (x (-8) 14)
    have b12154 := hb (x (-8) 14)
    have b12155 := hb (x (-8) 4 && x (-8) 14)
    clear * - r12153 b12154 b12155 d12148
    omega
  have r12156 : 1 ≤ (x (-4) 10).toNat + (x (-5) 1 && x (-5) 11).toNat + (x (-6) 2 && x (-6) 12).toNat + (x (-7) 3 && x (-7) 13).toNat + (x (-8) 4 && x (-8) 14).toNat + (x (-9) 5).toNat := by have q := hcov10 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have b12157 := hb (x (-9) 5)
  have b12158 := hb (x (-4) 10)
  have b12159 := hb (x (-5) 1 && x (-5) 11)
  have b12160 := hb (x (-6) 2 && x (-6) 12)
  have b12161 := hb (x (-7) 3 && x (-7) 13)
  have b12162 := hb (x (-8) 4 && x (-8) 14)
  linarith only [r12156, b12157, b12158, b12159, b12160, b12161, b12162, d12023, d12088, d11961, d12104, d12152, d12127]

theorem cycle_power_fifteen_tight_type_sequence_four_iff_five_core_a0000 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-2) 2).toNat = 0)
    (g1 : (x (-1) 13).toNat = 0)
    (g2 : (x 0 1).toNat = 0)
    (g3 : (x 0 11).toNat = 0)
    (g4 : (x 1 11).toNat = 0)
    (g5 : (x (-2) 2 && x (-2) 13).toNat = 0)
    (g6 : (x (-3) 3 && x (-3) 14).toNat = 0)
    (g7 : (x (-1) 2 && x (-1) 13).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_four_iff_five_core_a0000_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7
