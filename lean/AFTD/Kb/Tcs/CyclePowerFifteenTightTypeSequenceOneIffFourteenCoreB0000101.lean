import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b0000101

Topic: combinatorics   Node: 7f02d296f755

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core: under the layer-free tight-cover constraints for k = 15 and 84 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b0000101_aux (x : ℤ → Fin 16 → Bool)
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
    (g4 : (x (-2) 14).toNat = 1)
    (g5 : (x (-1) 5).toNat = 0)
    (g6 : (x (-1) 9).toNat = 0)
    (g7 : (x (-1) 13).toNat = 0)
    (g8 : (x 0 2).toNat = 0)
    (g9 : (x 0 3).toNat = 0)
    (g10 : (x 0 4).toNat = 0)
    (g11 : (x 0 5).toNat = 0)
    (g12 : (x 0 7).toNat = 0)
    (g13 : (x 0 8).toNat = 0)
    (g14 : (x 0 9).toNat = 0)
    (g15 : (x 0 10).toNat = 0)
    (g16 : (x 0 11).toNat = 0)
    (g17 : (x 0 12).toNat = 0)
    (g18 : (x 0 13).toNat = 0)
    (g19 : (x 0 14).toNat = 1)
    (g20 : (x 1 4).toNat = 1)
    (g21 : (x 1 8).toNat = 0)
    (g22 : (x 1 14).toNat = 1)
    (g23 : (x 2 2).toNat = 0)
    (g24 : (x 2 10).toNat = 0)
    (g25 : (x 3 5).toNat = 0)
    (g26 : (x 3 13).toNat = 0)
    (g27 : (x 4 4).toNat = 0)
    (g28 : (x 4 12).toNat = 0)
    (g29 : (x 2 2 && x 2 6).toNat = 0)
    (g30 : (x 0 4 && x 0 8).toNat = 0)
    (g31 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g32 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g33 : (x 4 4 && x 4 8).toNat = 0)
    (g34 : (x 3 5 && x 3 9).toNat = 0)
    (g35 : (x 2 6 && x 2 10).toNat = 0)
    (g36 : (x 0 8 && x 0 12).toNat = 0)
    (g37 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g38 : (x 1 8 && x 1 12).toNat = 0)
    (g39 : (x 0 9 && x 0 13).toNat = 0)
    (g40 : (x 2 5 && x 2 10).toNat = 0)
    (g41 : (x 0 7 && x 0 12).toNat = 0)
    (g42 : (x (-1) 8 && x (-1) 13).toNat = 0)
    (g43 : (x 1 8 && x 1 13).toNat = 0)
    (g44 : (x 0 9 && x 0 14).toNat = 0)
    (g45 : (x 4 7 && x 4 12).toNat = 0)
    (g46 : (x 3 8 && x 3 13).toNat = 0)
    (g47 : (x 4 4 && x 4 10).toNat = 0)
    (g48 : (x 3 5 && x 3 11).toNat = 0)
    (g49 : (x 0 8 && x 0 14).toNat = 0)
    (g50 : (x 1 8 && x 1 14).toNat = 0)
    (g51 : (x 4 6 && x 4 12).toNat = 0)
    (g52 : (x 3 7 && x 3 13).toNat = 0)
    (g53 : (x 0 7 && x 0 14).toNat = 0)
    (g54 : (x 4 4 && x 4 11).toNat = 0)
    (g55 : (x 3 5 && x 3 12).toNat = 0)
    (g56 : (x 4 5 && x 4 12).toNat = 0)
    (g57 : (x 3 6 && x 3 13).toNat = 0)
    (g58 : (x (-3) 1 && x (-3) 10).toNat = 0)
    (g59 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g60 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g61 : (x (-3) 3 && x (-3) 12).toNat = 0)
    (g62 : (x 0 1 && x 0 10).toNat = 0)
    (g63 : (x (-3) 4 && x (-3) 13).toNat = 0)
    (g64 : (x 0 2 && x 0 11).toNat = 0)
    (g65 : (x (-3) 5 && x (-3) 14).toNat = 0)
    (g66 : (x 4 3 && x 4 12).toNat = 0)
    (g67 : (x 3 4 && x 3 13).toNat = 0)
    (g68 : (x 4 4 && x 4 13).toNat = 0)
    (g69 : (x 3 5 && x 3 14).toNat = 0)
    (g70 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g71 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g72 : (x 0 2 && x 0 12).toNat = 0)
    (g73 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g74 : (x 4 2 && x 4 12).toNat = 0)
    (g75 : (x 3 3 && x 3 13).toNat = 0)
    (g76 : (x 4 4 && x 4 14).toNat = 0)
    (g77 : (x (-3) 2 && x (-3) 13).toNat = 0)
    (g78 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g79 : (x (-3) 3 && x (-3) 14).toNat = 0)
    (g80 : (x 0 1 && x 0 12).toNat = 0)
    (g81 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g82 : (x (-3) 1 && x (-3) 14).toNat = 0)
    (g83 : (x 0 1 && x 0 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d6299 : (x 1 12).toNat = 1 := by
    have r6300 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
    have b6301 := hb (x 1 4)
    have b6302 := hb (x 1 12)
    clear * - r6300 b6301 b6302 g20
    omega
  have d6303 : (x (-1) 2).toNat = 0 := by
    have r6304 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
    have e6305 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e6306 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b6307 := hb (x (-2) 3)
    have b6308 := hb (x (-1) 2)
    have b6309 := hb (x 0 13)
    have b6310 := hb (x 1 12)
    clear * - r6304 e6305 e6306 b6307 b6308 b6309 b6310 d6299 g18
    omega
  have d6311 : (x (-1) 2 && x (-1) 11).toNat = 0 := by
    have r6312 := hand1 (x (-1) 2) (x (-1) 11)
    have b6313 := hb (x (-1) 2)
    have b6314 := hb (x (-1) 2 && x (-1) 11)
    clear * - r6312 b6313 b6314 d6303
    omega
  have d6315 : (x (-1) 10).toNat = 0 := by
    have r6316 : (x (-1) 10).toNat ≤ (x (-1) 2).toNat := himp _ _ (hp10 (-1))
    have b6317 := hb (x (-1) 2)
    have b6318 := hb (x (-1) 10)
    clear * - r6316 b6317 b6318 d6303
    omega
  have d6319 : (x 1 13).toNat = 1 := by
    have r6320 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := hcov13 1
    have b6321 := hb (x (-1) 2)
    have b6322 := hb (x 1 13)
    have b6323 := hb (x 0 1 && x 0 14)
    clear * - r6320 b6321 b6322 b6323 g83 d6303
    omega
  have d6324 : (x 1 1).toNat = 1 := by
    have r6325 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
    have b6326 := hb (x 1 1)
    have b6327 := hb (x 1 13)
    clear * - r6325 b6326 b6327 d6319
    omega
  have d6328 : (x 2 14).toNat = 0 := by
    have r6329 : (x 2 14).toNat + (x 1 1).toNat = 1 := hd14 2
    have b6330 := hb (x 1 1)
    have b6331 := hb (x 2 14)
    clear * - r6329 b6330 b6331 d6324
    omega
  have d6332 : (x 2 1 && x 2 14).toNat = 0 := by
    have r6333 := hand2 (x 2 1) (x 2 14)
    have b6334 := hb (x 2 14)
    have b6335 := hb (x 2 1 && x 2 14)
    clear * - r6333 b6334 b6335 d6328
    omega
  have d6336 : (x 1 2).toNat = 1 := by
    have r6337 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := hcov13 3
    have b6338 := hb (x 1 2)
    have b6339 := hb (x 3 13)
    have b6340 := hb (x 2 1 && x 2 14)
    clear * - r6337 b6338 b6339 b6340 g26 d6332
    omega
  have d6341 : (x 3 12).toNat = 0 := by
    have r6342 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := hd12 3
    have e6343 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e6344 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b6345 := hb (x 0 3)
    have b6346 := hb (x 1 2)
    have b6347 := hb (x 2 13)
    have b6348 := hb (x 3 12)
    clear * - r6342 e6343 e6344 b6345 b6346 b6347 b6348 d6336 g9
    omega
  have d6349 : (x 3 3 && x 3 12).toNat = 0 := by
    have r6350 := hand2 (x 3 3) (x 3 12)
    have b6351 := hb (x 3 12)
    have b6352 := hb (x 3 3 && x 3 12)
    clear * - r6350 b6351 b6352 d6341
    omega
  have d6353 : (x 3 6 && x 3 12).toNat = 0 := by
    have r6354 := hand2 (x 3 6) (x 3 12)
    have b6355 := hb (x 3 12)
    have b6356 := hb (x 3 6 && x 3 12)
    clear * - r6354 b6355 b6356 d6341
    omega
  have d6357 : (x 3 4).toNat = 0 := by
    have r6358 : (x 3 4).toNat ≤ (x 3 12).toNat := himp _ _ (hp4 3)
    have b6359 := hb (x 3 4)
    have b6360 := hb (x 3 12)
    clear * - r6358 b6359 b6360 d6341
    omega
  have d6361 : (x 3 4 && x 3 14).toNat = 0 := by
    have r6362 := hand1 (x 3 4) (x 3 14)
    have b6363 := hb (x 3 4)
    have b6364 := hb (x 3 4 && x 3 14)
    clear * - r6362 b6363 b6364 d6357
    omega
  have d6365 : (x 3 4 && x 3 11).toNat = 0 := by
    have r6366 := hand1 (x 3 4) (x 3 11)
    have b6367 := hb (x 3 4)
    have b6368 := hb (x 3 4 && x 3 11)
    clear * - r6366 b6367 b6368 d6357
    omega
  have d6369 : (x 3 4 && x 3 9).toNat = 0 := by
    have r6370 := hand1 (x 3 4) (x 3 9)
    have b6371 := hb (x 3 4)
    have b6372 := hb (x 3 4 && x 3 9)
    clear * - r6370 b6371 b6372 d6357
    omega
  have d6373 : (x 2 13).toNat = 0 := by
    have r6374 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := hd12 3
    have e6375 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e6376 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b6377 := hb (x 0 3)
    have b6378 := hb (x 1 2)
    have b6379 := hb (x 2 13)
    have b6380 := hb (x 3 12)
    clear * - r6374 e6375 e6376 b6377 b6378 b6379 b6380 d6341 d6336 g9
    omega
  have d6381 : (x 2 4 && x 2 13).toNat = 0 := by
    have r6382 := hand2 (x 2 4) (x 2 13)
    have b6383 := hb (x 2 13)
    have b6384 := hb (x 2 4 && x 2 13)
    clear * - r6382 b6383 b6384 d6373
    omega
  have d6385 : (x 2 6 && x 2 13).toNat = 0 := by
    have r6386 := hand2 (x 2 6) (x 2 13)
    have b6387 := hb (x 2 13)
    have b6388 := hb (x 2 6 && x 2 13)
    clear * - r6386 b6387 b6388 d6373
    omega
  have d6389 : (x 2 7 && x 2 13).toNat = 0 := by
    have r6390 := hand2 (x 2 7) (x 2 13)
    have b6391 := hb (x 2 13)
    have b6392 := hb (x 2 7 && x 2 13)
    clear * - r6390 b6391 b6392 d6373
    omega
  have d6393 : (x 2 5).toNat = 0 := by
    have r6394 : (x 2 5).toNat ≤ (x 2 13).toNat := himp _ _ (hp5 2)
    have b6395 := hb (x 2 5)
    have b6396 := hb (x 2 13)
    clear * - r6394 b6395 b6396 d6373
    omega
  have d6397 : (x 2 5 && x 2 14).toNat = 0 := by
    have r6398 := hand1 (x 2 5) (x 2 14)
    have b6399 := hb (x 2 5)
    have b6400 := hb (x 2 5 && x 2 14)
    clear * - r6398 b6399 b6400 d6393
    omega
  have d6401 : (x 2 5 && x 2 12).toNat = 0 := by
    have r6402 := hand1 (x 2 5) (x 2 12)
    have b6403 := hb (x 2 5)
    have b6404 := hb (x 2 5 && x 2 12)
    clear * - r6402 b6403 b6404 d6393
    omega
  have d6405 : (x 2 4 && x 2 14).toNat = 0 := by
    have r6406 := hand2 (x 2 4) (x 2 14)
    have b6407 := hb (x 2 14)
    have b6408 := hb (x 2 4 && x 2 14)
    clear * - r6406 b6407 b6408 d6328
    omega
  have d6409 : (x 2 7 && x 2 14).toNat = 0 := by
    have r6410 := hand2 (x 2 7) (x 2 14)
    have b6411 := hb (x 2 14)
    have b6412 := hb (x 2 7 && x 2 14)
    clear * - r6410 b6411 b6412 d6328
    omega
  have d6413 : (x 2 8 && x 2 14).toNat = 0 := by
    have r6414 := hand2 (x 2 8) (x 2 14)
    have b6415 := hb (x 2 14)
    have b6416 := hb (x 2 8 && x 2 14)
    clear * - r6414 b6415 b6416 d6328
    omega
  have d6417 : (x 2 9 && x 2 14).toNat = 0 := by
    have r6418 := hand2 (x 2 9) (x 2 14)
    have b6419 := hb (x 2 14)
    have b6420 := hb (x 2 9 && x 2 14)
    clear * - r6418 b6419 b6420 d6328
    omega
  have d6421 : (x 2 6).toNat = 0 := by
    have r6422 : (x 2 6).toNat ≤ (x 2 14).toNat := himp _ _ (hp6 2)
    have b6423 := hb (x 2 6)
    have b6424 := hb (x 2 14)
    clear * - r6422 b6423 b6424 d6328
    omega
  have d6425 : (x 2 6 && x 2 12).toNat = 0 := by
    have r6426 := hand1 (x 2 6) (x 2 12)
    have b6427 := hb (x 2 6)
    have b6428 := hb (x 2 6 && x 2 12)
    clear * - r6426 b6427 b6428 d6421
    omega
  have d6429 : (x 2 12).toNat = 0 := by
    have r6430 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := hd12 2
    have e6431 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e6432 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b6433 := hb (x (-1) 3)
    have b6434 := hb (x 0 2)
    have b6435 := hb (x 1 13)
    have b6436 := hb (x 2 12)
    clear * - r6430 e6431 e6432 b6433 b6434 b6435 b6436 d6319 g8
    omega
  have d6437 : (x 2 7 && x 2 12).toNat = 0 := by
    have r6438 := hand2 (x 2 7) (x 2 12)
    have b6439 := hb (x 2 12)
    have b6440 := hb (x 2 7 && x 2 12)
    clear * - r6438 b6439 b6440 d6429
    omega
  have d6441 : (x 2 4).toNat = 0 := by
    have r6442 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
    have b6443 := hb (x 2 4)
    have b6444 := hb (x 2 12)
    clear * - r6442 b6443 b6444 d6429
    omega
  have d6445 : (x (-1) 3).toNat = 0 := by
    have r6446 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := hd12 2
    have e6447 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e6448 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b6449 := hb (x (-1) 3)
    have b6450 := hb (x 0 2)
    have b6451 := hb (x 1 13)
    have b6452 := hb (x 2 12)
    clear * - r6446 e6447 e6448 b6449 b6450 b6451 b6452 d6429 d6319 g8
    omega
  have d6453 : (x (-1) 3 && x (-1) 12).toNat = 0 := by
    have r6454 := hand1 (x (-1) 3) (x (-1) 12)
    have b6455 := hb (x (-1) 3)
    have b6456 := hb (x (-1) 3 && x (-1) 12)
    clear * - r6454 b6455 b6456 d6445
    omega
  have d6457 : (x (-1) 11).toNat = 0 := by
    have r6458 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
    have b6459 := hb (x (-1) 3)
    have b6460 := hb (x (-1) 11)
    clear * - r6458 b6459 b6460 d6445
    omega
  have d6461 : (x (-2) 3).toNat = 0 := by
    have r6462 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
    have e6463 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e6464 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b6465 := hb (x (-2) 3)
    have b6466 := hb (x (-1) 2)
    have b6467 := hb (x 0 13)
    have b6468 := hb (x 1 12)
    clear * - r6462 e6463 e6464 b6465 b6466 b6467 b6468 d6299 g18 d6303
    omega
  have d6469 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
    have r6470 := hand1 (x (-2) 3) (x (-2) 14)
    have b6471 := hb (x (-2) 3)
    have b6472 := hb (x (-2) 3 && x (-2) 14)
    clear * - r6470 b6471 b6472 d6461
    omega
  have d6473 : (x (-2) 3 && x (-2) 12).toNat = 0 := by
    have r6474 := hand1 (x (-2) 3) (x (-2) 12)
    have b6475 := hb (x (-2) 3)
    have b6476 := hb (x (-2) 3 && x (-2) 12)
    clear * - r6474 b6475 b6476 d6461
    omega
  have d6477 : (x (-2) 11).toNat = 0 := by
    have r6478 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
    have b6479 := hb (x (-2) 3)
    have b6480 := hb (x (-2) 11)
    clear * - r6478 b6479 b6480 d6461
    omega
  have d6481 : (x (-2) 1 && x (-2) 11).toNat = 0 := by
    have r6482 := hand2 (x (-2) 1) (x (-2) 11)
    have b6483 := hb (x (-2) 11)
    have b6484 := hb (x (-2) 1 && x (-2) 11)
    clear * - r6482 b6483 b6484 d6477
    omega
  have d6485 : (x (-2) 2 && x (-2) 11).toNat = 0 := by
    have r6486 := hand2 (x (-2) 2) (x (-2) 11)
    have b6487 := hb (x (-2) 11)
    have b6488 := hb (x (-2) 2 && x (-2) 11)
    clear * - r6486 b6487 b6488 d6477
    omega
  have d6489 : (x 5 8).toNat = 0 := by
    have r6490 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := hd8 5
    have e6491 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e6492 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e6493 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e6494 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e6495 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e6496 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b6497 := hb (x (-2) 7)
    have b6498 := hb (x (-1) 6)
    have b6499 := hb (x 0 5)
    have b6500 := hb (x 1 4)
    have b6501 := hb (x 2 11)
    have b6502 := hb (x 3 10)
    have b6503 := hb (x 4 9)
    have b6504 := hb (x 5 8)
    clear * - r6490 e6491 e6492 e6493 e6494 e6495 e6496 b6497 b6498 b6499 b6500 b6501 b6502 b6503 b6504 g20 g11
    omega
  have d6505 : (x 5 4 && x 5 8).toNat = 0 := by
    have r6506 := hand2 (x 5 4) (x 5 8)
    have b6507 := hb (x 5 8)
    have b6508 := hb (x 5 4 && x 5 8)
    clear * - r6506 b6507 b6508 d6489
    omega
  have d6509 : (x 4 9).toNat = 0 := by
    have r6510 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := hd8 5
    have e6511 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e6512 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e6513 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e6514 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e6515 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e6516 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b6517 := hb (x (-2) 7)
    have b6518 := hb (x (-1) 6)
    have b6519 := hb (x 0 5)
    have b6520 := hb (x 1 4)
    have b6521 := hb (x 2 11)
    have b6522 := hb (x 3 10)
    have b6523 := hb (x 4 9)
    have b6524 := hb (x 5 8)
    clear * - r6510 e6511 e6512 e6513 e6514 e6515 e6516 b6517 b6518 b6519 b6520 b6521 b6522 b6523 b6524 d6489 g20 g11
    omega
  have d6525 : (x 4 5 && x 4 9).toNat = 0 := by
    have r6526 := hand2 (x 4 5) (x 4 9)
    have b6527 := hb (x 4 9)
    have b6528 := hb (x 4 5 && x 4 9)
    clear * - r6526 b6527 b6528 d6509
    omega
  have d6529 : (x 3 10).toNat = 0 := by
    have r6530 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := hd8 5
    have e6531 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e6532 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e6533 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e6534 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e6535 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e6536 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b6537 := hb (x (-2) 7)
    have b6538 := hb (x (-1) 6)
    have b6539 := hb (x 0 5)
    have b6540 := hb (x 1 4)
    have b6541 := hb (x 2 11)
    have b6542 := hb (x 3 10)
    have b6543 := hb (x 4 9)
    have b6544 := hb (x 5 8)
    clear * - r6530 e6531 e6532 e6533 e6534 e6535 e6536 b6537 b6538 b6539 b6540 b6541 b6542 b6543 b6544 d6489 d6509 g20 g11
    omega
  have d6545 : (x 3 6 && x 3 10).toNat = 0 := by
    have r6546 := hand2 (x 3 6) (x 3 10)
    have b6547 := hb (x 3 10)
    have b6548 := hb (x 3 6 && x 3 10)
    clear * - r6546 b6547 b6548 d6529
    omega
  have d6549 : (x 2 11).toNat = 0 := by
    have r6550 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := hd8 5
    have e6551 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e6552 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e6553 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e6554 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e6555 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e6556 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b6557 := hb (x (-2) 7)
    have b6558 := hb (x (-1) 6)
    have b6559 := hb (x 0 5)
    have b6560 := hb (x 1 4)
    have b6561 := hb (x 2 11)
    have b6562 := hb (x 3 10)
    have b6563 := hb (x 4 9)
    have b6564 := hb (x 5 8)
    clear * - r6550 e6551 e6552 e6553 e6554 e6555 e6556 b6557 b6558 b6559 b6560 b6561 b6562 b6563 b6564 d6489 d6509 d6529 g20 g11
    omega
  have d6565 : (x 2 7 && x 2 11).toNat = 0 := by
    have r6566 := hand2 (x 2 7) (x 2 11)
    have b6567 := hb (x 2 11)
    have b6568 := hb (x 2 7 && x 2 11)
    clear * - r6566 b6567 b6568 d6549
    omega
  cases h6569 : x 0 6
  · have f6570 : (x 0 6).toNat = 0 := by rw [h6569]; rfl
    cases h6571 : x (-1) 4
    · have f6572 : (x (-1) 4).toNat = 0 := by rw [h6571]; rfl
      cases h6573 : x 1 5
      · have f6574 : (x 1 5).toNat = 0 := by rw [h6573]; rfl
        have d6575 : (x 1 5 && x 1 14).toNat = 0 := by
          have r6576 := hand1 (x 1 5) (x 1 14)
          have b6577 := hb (x 1 5)
          have b6578 := hb (x 1 5 && x 1 14)
          clear * - r6576 b6577 b6578 f6574
          omega
        cases h6579 : x 1 6
        · have f6580 : (x 1 6).toNat = 0 := by rw [h6579]; rfl
          have d6581 : (x 1 6 && x 1 13).toNat = 0 := by
            have r6582 := hand1 (x 1 6) (x 1 13)
            have b6583 := hb (x 1 6)
            have b6584 := hb (x 1 6 && x 1 13)
            clear * - r6582 b6583 b6584 f6580
            omega
          have d6585 : (x 1 6 && x 1 11).toNat = 0 := by
            have r6586 := hand1 (x 1 6) (x 1 11)
            have b6587 := hb (x 1 6)
            have b6588 := hb (x 1 6 && x 1 11)
            clear * - r6586 b6587 b6588 f6580
            omega
          cases h6589 : x 1 7
          · have f6590 : (x 1 7).toNat = 0 := by rw [h6589]; rfl
            have d6591 : (x 1 7 && x 1 13).toNat = 0 := by
              have r6592 := hand1 (x 1 7) (x 1 13)
              have b6593 := hb (x 1 7)
              have b6594 := hb (x 1 7 && x 1 13)
              clear * - r6592 b6593 b6594 f6590
              omega
            have d6595 : (x 1 7 && x 1 11).toNat = 0 := by
              have r6596 := hand1 (x 1 7) (x 1 11)
              have b6597 := hb (x 1 7)
              have b6598 := hb (x 1 7 && x 1 11)
              clear * - r6596 b6597 b6598 f6590
              omega
            cases h6599 : x (-1) 8
            · have f6600 : (x (-1) 8).toNat = 0 := by rw [h6599]; rfl
              cases h6601 : x 1 9
              · have f6602 : (x 1 9).toNat = 0 := by rw [h6601]; rfl
                have r6603 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := hcount 12
                have r6604 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := hcount 14
                have r6605 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
                have e6606 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                have e6607 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                have e6608 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                have e6609 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                have e6610 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                have e6611 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                have r6612 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
                have e6613 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                have e6614 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                have e6615 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                have e6616 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                have e6617 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                have e6618 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                have r6619 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
                have e6620 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                have e6621 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                have r6622 : 1 ≤ (x 8 4).toNat + (x 7 1 && x 7 5).toNat + (x 6 2 && x 6 6).toNat + (x 5 3 && x 5 7).toNat + (x 4 4 && x 4 8).toNat + (x 3 5 && x 3 9).toNat + (x 2 6 && x 2 10).toNat + (x 1 7 && x 1 11).toNat + (x 0 8 && x 0 12).toNat + (x (-1) 9 && x (-1) 13).toNat + (x (-2) 10 && x (-2) 14).toNat + (x (-3) 11).toNat := hcov4 8
                have e6623 : (x 7 1 && x 7 5).toNat = (x 7 5).toNat := handr _ _ (fun h => hp13 7 (hp5 7 (h)))
                have e6624 : (x (-2) 10 && x (-2) 14).toNat = (x (-2) 10).toNat := handl _ _ (fun h => hp2 (-2) (hp10 (-2) (h)))
                have r6625 : 1 ≤ (x 7 7).toNat + (x 6 1 && x 6 8).toNat + (x 5 2 && x 5 9).toNat + (x 4 3 && x 4 10).toNat + (x 3 4 && x 3 11).toNat + (x 2 5 && x 2 12).toNat + (x 1 6 && x 1 13).toNat + (x 0 7 && x 0 14).toNat + (x (-1) 8).toNat := hcov7 7
                have r6626 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := hcov9 0
                have r6627 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := hcov9 1
                have r6628 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := hcov10 6
                have r6629 : 1 ≤ (x 12 10).toNat + (x 11 1 && x 11 11).toNat + (x 10 2 && x 10 12).toNat + (x 9 3 && x 9 13).toNat + (x 8 4 && x 8 14).toNat + (x 7 5).toNat := hcov10 12
                have r6630 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := hcov11 1
                have r6631 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
                have r6632 : (x 6 10).toNat ≤ (x 6 2).toNat := himp _ _ (hp10 6)
                have r6633 : (x 7 5).toNat ≤ (x 7 13).toNat := himp _ _ (hp5 7)
                have r6634 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
                have r6635 : (x 12 10).toNat ≤ (x 12 2).toNat := himp _ _ (hp10 12)
                have r6636 := hand2 (x 6 2) (x 6 6)
                have r6637 := hand2 (x 5 3) (x 5 7)
                have r6638 := hand2 (x 6 1) (x 6 8)
                have r6639 := hand2 (x 5 2) (x 5 9)
                have r6640 := hand2 (x 4 3) (x 4 10)
                have r6641 := hand1 (x (-4) 4) (x (-4) 13)
                have r6642 := hand1 (x (-5) 5) (x (-5) 14)
                have r6643 := hand1 (x (-4) 5) (x (-4) 14)
                have r6644 := hand2 (x 5 1) (x 5 11)
                have r6645 := hand1 (x 11 1) (x 11 11)
                have r6646 := hand1 (x 10 2) (x 10 12)
                have r6647 := hand1 (x 9 3) (x 9 13)
                have r6648 := hand1 (x 8 4) (x 8 14)
                have b6649 := hb (x (-7) 7)
                have b6650 := hb (x (-6) 6)
                have b6651 := hb (x (-6) 7)
                have b6652 := hb (x (-5) 5)
                have b6653 := hb (x (-5) 6)
                have b6654 := hb (x (-4) 4)
                have b6655 := hb (x (-4) 5)
                have b6656 := hb (x (-3) 4)
                have b6657 := hb (x (-3) 11)
                have b6658 := hb (x (-2) 10)
                have b6659 := hb (x (-2) 11)
                have b6660 := hb (x (-2) 14)
                have b6661 := hb (x (-1) 8)
                have b6662 := hb (x (-1) 9)
                have b6663 := hb (x (-1) 10)
                have b6664 := hb (x (-1) 13)
                have b6665 := hb (x 0 8)
                have b6666 := hb (x 0 9)
                have b6667 := hb (x 0 12)
                have b6668 := hb (x 0 14)
                have b6669 := hb (x 1 5)
                have b6670 := hb (x 1 8)
                have b6671 := hb (x 1 9)
                have b6672 := hb (x 1 11)
                have b6673 := hb (x 1 13)
                have b6674 := hb (x 2 10)
                have b6675 := hb (x 2 12)
                have b6676 := hb (x 3 9)
                have b6677 := hb (x 3 11)
                have b6678 := hb (x 4 8)
                have b6679 := hb (x 4 10)
                have b6680 := hb (x 5 3)
                have b6681 := hb (x 5 7)
                have b6682 := hb (x 5 9)
                have b6683 := hb (x 5 11)
                have b6684 := hb (x 6 2)
                have b6685 := hb (x 6 6)
                have b6686 := hb (x 6 8)
                have b6687 := hb (x 6 10)
                have b6688 := hb (x 7 5)
                have b6689 := hb (x 7 7)
                have b6690 := hb (x 7 13)
                have b6691 := hb (x 8 4)
                have b6692 := hb (x 8 6)
                have b6693 := hb (x 8 12)
                have b6694 := hb (x 9 3)
                have b6695 := hb (x 9 5)
                have b6696 := hb (x 10 2)
                have b6697 := hb (x 10 4)
                have b6698 := hb (x 11 1)
                have b6699 := hb (x 11 3)
                have b6700 := hb (x 12 2)
                have b6701 := hb (x 12 10)
                have b6702 := hb (x 13 1)
                have b6703 := hb (x 6 2 && x 6 6)
                have b6704 := hb (x 5 3 && x 5 7)
                have b6705 := hb (x 4 4 && x 4 8)
                have b6706 := hb (x 3 5 && x 3 9)
                have b6707 := hb (x 2 6 && x 2 10)
                have b6708 := hb (x 1 7 && x 1 11)
                have b6709 := hb (x 0 8 && x 0 12)
                have b6710 := hb (x (-1) 9 && x (-1) 13)
                have b6711 := hb (x 6 1 && x 6 8)
                have b6712 := hb (x 5 2 && x 5 9)
                have b6713 := hb (x 4 3 && x 4 10)
                have b6714 := hb (x 3 4 && x 3 11)
                have b6715 := hb (x 2 5 && x 2 12)
                have b6716 := hb (x 1 6 && x 1 13)
                have b6717 := hb (x 0 7 && x 0 14)
                have b6718 := hb (x (-1) 1 && x (-1) 10)
                have b6719 := hb (x (-2) 2 && x (-2) 11)
                have b6720 := hb (x (-3) 3 && x (-3) 12)
                have b6721 := hb (x (-4) 4 && x (-4) 13)
                have b6722 := hb (x (-5) 5 && x (-5) 14)
                have b6723 := hb (x 0 1 && x 0 10)
                have b6724 := hb (x (-1) 2 && x (-1) 11)
                have b6725 := hb (x (-2) 3 && x (-2) 12)
                have b6726 := hb (x (-3) 4 && x (-3) 13)
                have b6727 := hb (x (-4) 5 && x (-4) 14)
                have b6728 := hb (x 5 1 && x 5 11)
                have b6729 := hb (x 4 2 && x 4 12)
                have b6730 := hb (x 3 3 && x 3 13)
                have b6731 := hb (x 2 4 && x 2 14)
                have b6732 := hb (x 11 1 && x 11 11)
                have b6733 := hb (x 10 2 && x 10 12)
                have b6734 := hb (x 9 3 && x 9 13)
                have b6735 := hb (x 8 4 && x 8 14)
                have b6736 := hb (x 0 1 && x 0 12)
                have b6737 := hb (x (-1) 2 && x (-1) 13)
                have b6738 := hb (x (-2) 3 && x (-2) 14)
                linarith only [r6603, r6604, r6605, e6606, e6607, e6608, e6609, e6610, e6611, r6612, e6613, e6614, e6615, e6616, e6617, e6618, r6619, e6620, e6621, r6622, e6623, e6624, r6625, r6626, r6627, r6628, r6629, r6630, r6631, r6632, r6633, r6634, r6635, r6636, r6637, r6638, r6639, r6640, r6641, r6642, r6643, r6644, r6645, r6646, r6647, r6648, b6649, b6650, b6651, b6652, b6653, b6654, b6655, b6656, b6657, b6658, b6659, b6660, b6661, b6662, b6663, b6664, b6665, b6666, b6667, b6668, b6669, b6670, b6671, b6672, b6673, b6674, b6675, b6676, b6677, b6678, b6679, b6680, b6681, b6682, b6683, b6684, b6685, b6686, b6687, b6688, b6689, b6690, b6691, b6692, b6693, b6694, b6695, b6696, b6697, b6698, b6699, b6700, b6701, b6702, b6703, b6704, b6705, b6706, b6707, b6708, b6709, b6710, b6711, b6712, b6713, b6714, b6715, b6716, b6717, b6718, b6719, b6720, b6721, b6722, b6723, b6724, b6725, b6726, b6727, b6728, b6729, b6730, b6731, b6732, b6733, b6734, b6735, b6736, b6737, b6738, g2, d6477, g4, f6600, g6, d6315, g7, g13, g14, g17, g19, f6574, g21, f6602, d6319, g24, d6429, g33, g34, g35, d6595, g36, g37, d6365, d6401, d6581, g53, g60, d6485, g61, g62, d6311, d6473, g63, g74, g75, d6405, g80, g81, d6469]
              · have f6739 : (x 1 9).toNat = 1 := by rw [h6601]; rfl
                have d6740 : (x 2 8).toNat = 0 := by
                  have r6741 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := hd8 2
                  have e6742 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                  have e6743 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                  have e6744 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                  have e6745 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                  have e6746 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                  have e6747 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                  have b6748 := hb (x (-5) 7)
                  have b6749 := hb (x (-4) 6)
                  have b6750 := hb (x (-3) 5)
                  have b6751 := hb (x (-2) 4)
                  have b6752 := hb (x (-1) 11)
                  have b6753 := hb (x 0 10)
                  have b6754 := hb (x 1 9)
                  have b6755 := hb (x 2 8)
                  clear * - r6741 e6742 e6743 e6744 e6745 e6746 e6747 b6748 b6749 b6750 b6751 b6752 b6753 b6754 b6755 f6739 g15 d6457 g0
                  omega
                have d6756 : (x (-2) 4).toNat = 0 := by
                  have r6757 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := hd8 2
                  have e6758 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                  have e6759 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                  have e6760 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                  have e6761 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                  have e6762 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                  have e6763 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                  have b6764 := hb (x (-5) 7)
                  have b6765 := hb (x (-4) 6)
                  have b6766 := hb (x (-3) 5)
                  have b6767 := hb (x (-2) 4)
                  have b6768 := hb (x (-1) 11)
                  have b6769 := hb (x 0 10)
                  have b6770 := hb (x 1 9)
                  have b6771 := hb (x 2 8)
                  clear * - r6757 e6758 e6759 e6760 e6761 e6762 e6763 b6764 b6765 b6766 b6767 b6768 b6769 b6770 b6771 d6740 f6739 g15 d6457 g0
                  omega
                have d6772 : (x (-2) 4 && x (-2) 14).toNat = 0 := by
                  have r6773 := hand1 (x (-2) 4) (x (-2) 14)
                  have b6774 := hb (x (-2) 4)
                  have b6775 := hb (x (-2) 4 && x (-2) 14)
                  clear * - r6773 b6774 b6775 d6756
                  omega
                have d6776 : (x 1 1 && x 1 11).toNat = 1 := by
                  have r6777 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := hcov10 2
                  have b6778 := hb (x (-3) 5)
                  have b6779 := hb (x 2 10)
                  have b6780 := hb (x 1 1 && x 1 11)
                  have b6781 := hb (x 0 2 && x 0 12)
                  have b6782 := hb (x (-1) 3 && x (-1) 13)
                  have b6783 := hb (x (-2) 4 && x (-2) 14)
                  clear * - r6777 b6778 b6779 b6780 b6781 b6782 b6783 g24 g72 g73 d6772 g0
                  omega
                have d6784 : (x 1 11).toNat = 1 := by
                  have r6785 := hand2 (x 1 1) (x 1 11)
                  have b6786 := hb (x 1 11)
                  have b6787 := hb (x 1 1 && x 1 11)
                  clear * - r6785 b6786 b6787 d6776
                  omega
                have d6788 : (x 4 8).toNat = 0 := by
                  have r6789 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := hd8 4
                  have e6790 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
                  have e6791 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
                  have e6792 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
                  have e6793 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
                  have e6794 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
                  have e6795 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
                  have b6796 := hb (x (-3) 7)
                  have b6797 := hb (x (-2) 6)
                  have b6798 := hb (x (-1) 5)
                  have b6799 := hb (x 0 4)
                  have b6800 := hb (x 1 11)
                  have b6801 := hb (x 2 10)
                  have b6802 := hb (x 3 9)
                  have b6803 := hb (x 4 8)
                  clear * - r6789 e6790 e6791 e6792 e6793 e6794 e6795 b6796 b6797 b6798 b6799 b6800 b6801 b6802 b6803 g24 d6784 g10 g5
                  omega
                have d6804 : (x 3 9).toNat = 0 := by
                  have r6805 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := hd8 4
                  have e6806 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
                  have e6807 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
                  have e6808 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
                  have e6809 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
                  have e6810 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
                  have e6811 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
                  have b6812 := hb (x (-3) 7)
                  have b6813 := hb (x (-2) 6)
                  have b6814 := hb (x (-1) 5)
                  have b6815 := hb (x 0 4)
                  have b6816 := hb (x 1 11)
                  have b6817 := hb (x 2 10)
                  have b6818 := hb (x 3 9)
                  have b6819 := hb (x 4 8)
                  clear * - r6805 e6806 e6807 e6808 e6809 e6810 e6811 b6812 b6813 b6814 b6815 b6816 b6817 b6818 b6819 d6788 g24 d6784 g10 g5
                  omega
                have r6820 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := hcount 12
                have r6821 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := hcount 14
                have r6822 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
                have e6823 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                have e6824 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                have e6825 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                have e6826 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                have e6827 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                have e6828 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                have r6829 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
                have e6830 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                have e6831 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                have r6832 : 1 ≤ (x 8 4).toNat + (x 7 1 && x 7 5).toNat + (x 6 2 && x 6 6).toNat + (x 5 3 && x 5 7).toNat + (x 4 4 && x 4 8).toNat + (x 3 5 && x 3 9).toNat + (x 2 6 && x 2 10).toNat + (x 1 7 && x 1 11).toNat + (x 0 8 && x 0 12).toNat + (x (-1) 9 && x (-1) 13).toNat + (x (-2) 10 && x (-2) 14).toNat + (x (-3) 11).toNat := hcov4 8
                have e6833 : (x 7 1 && x 7 5).toNat = (x 7 5).toNat := handr _ _ (fun h => hp13 7 (hp5 7 (h)))
                have e6834 : (x (-2) 10 && x (-2) 14).toNat = (x (-2) 10).toNat := handl _ _ (fun h => hp2 (-2) (hp10 (-2) (h)))
                have r6835 : 1 ≤ (x 7 7).toNat + (x 6 1 && x 6 8).toNat + (x 5 2 && x 5 9).toNat + (x 4 3 && x 4 10).toNat + (x 3 4 && x 3 11).toNat + (x 2 5 && x 2 12).toNat + (x 1 6 && x 1 13).toNat + (x 0 7 && x 0 14).toNat + (x (-1) 8).toNat := hcov7 7
                have r6836 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := hcov9 0
                have r6837 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := hcov10 6
                have r6838 : 1 ≤ (x 12 10).toNat + (x 11 1 && x 11 11).toNat + (x 10 2 && x 10 12).toNat + (x 9 3 && x 9 13).toNat + (x 8 4 && x 8 14).toNat + (x 7 5).toNat := hcov10 12
                have r6839 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
                have r6840 : (x 6 10).toNat ≤ (x 6 2).toNat := himp _ _ (hp10 6)
                have r6841 : (x 7 5).toNat ≤ (x 7 13).toNat := himp _ _ (hp5 7)
                have r6842 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
                have r6843 : (x 12 10).toNat ≤ (x 12 2).toNat := himp _ _ (hp10 12)
                have r6844 := hand2 (x 6 2) (x 6 6)
                have r6845 := hand2 (x 5 3) (x 5 7)
                have r6846 := hand2 (x 6 1) (x 6 8)
                have r6847 := hand2 (x 5 2) (x 5 9)
                have r6848 := hand2 (x 4 3) (x 4 10)
                have r6849 := hand1 (x (-4) 4) (x (-4) 13)
                have r6850 := hand1 (x (-5) 5) (x (-5) 14)
                have r6851 := hand2 (x 5 1) (x 5 11)
                have r6852 := hand1 (x 11 1) (x 11 11)
                have r6853 := hand1 (x 10 2) (x 10 12)
                have r6854 := hand1 (x 9 3) (x 9 13)
                have r6855 := hand1 (x 8 4) (x 8 14)
                have b6856 := hb (x (-7) 7)
                have b6857 := hb (x (-6) 6)
                have b6858 := hb (x (-5) 5)
                have b6859 := hb (x (-4) 4)
                have b6860 := hb (x (-3) 11)
                have b6861 := hb (x (-2) 10)
                have b6862 := hb (x (-2) 14)
                have b6863 := hb (x (-1) 8)
                have b6864 := hb (x (-1) 9)
                have b6865 := hb (x (-1) 13)
                have b6866 := hb (x 0 8)
                have b6867 := hb (x 0 9)
                have b6868 := hb (x 0 12)
                have b6869 := hb (x 0 14)
                have b6870 := hb (x 1 5)
                have b6871 := hb (x 1 11)
                have b6872 := hb (x 1 13)
                have b6873 := hb (x 2 10)
                have b6874 := hb (x 2 12)
                have b6875 := hb (x 3 9)
                have b6876 := hb (x 3 11)
                have b6877 := hb (x 4 8)
                have b6878 := hb (x 4 10)
                have b6879 := hb (x 5 3)
                have b6880 := hb (x 5 7)
                have b6881 := hb (x 5 9)
                have b6882 := hb (x 5 11)
                have b6883 := hb (x 6 2)
                have b6884 := hb (x 6 6)
                have b6885 := hb (x 6 8)
                have b6886 := hb (x 6 10)
                have b6887 := hb (x 7 5)
                have b6888 := hb (x 7 7)
                have b6889 := hb (x 7 13)
                have b6890 := hb (x 8 4)
                have b6891 := hb (x 8 6)
                have b6892 := hb (x 8 12)
                have b6893 := hb (x 9 3)
                have b6894 := hb (x 9 5)
                have b6895 := hb (x 10 2)
                have b6896 := hb (x 10 4)
                have b6897 := hb (x 11 1)
                have b6898 := hb (x 11 3)
                have b6899 := hb (x 12 2)
                have b6900 := hb (x 12 10)
                have b6901 := hb (x 13 1)
                have b6902 := hb (x 6 2 && x 6 6)
                have b6903 := hb (x 5 3 && x 5 7)
                have b6904 := hb (x 4 4 && x 4 8)
                have b6905 := hb (x 3 5 && x 3 9)
                have b6906 := hb (x 2 6 && x 2 10)
                have b6907 := hb (x 1 7 && x 1 11)
                have b6908 := hb (x 0 8 && x 0 12)
                have b6909 := hb (x (-1) 9 && x (-1) 13)
                have b6910 := hb (x 6 1 && x 6 8)
                have b6911 := hb (x 5 2 && x 5 9)
                have b6912 := hb (x 4 3 && x 4 10)
                have b6913 := hb (x 3 4 && x 3 11)
                have b6914 := hb (x 2 5 && x 2 12)
                have b6915 := hb (x 1 6 && x 1 13)
                have b6916 := hb (x 0 7 && x 0 14)
                have b6917 := hb (x (-1) 1 && x (-1) 10)
                have b6918 := hb (x (-2) 2 && x (-2) 11)
                have b6919 := hb (x (-3) 3 && x (-3) 12)
                have b6920 := hb (x (-4) 4 && x (-4) 13)
                have b6921 := hb (x (-5) 5 && x (-5) 14)
                have b6922 := hb (x 5 1 && x 5 11)
                have b6923 := hb (x 4 2 && x 4 12)
                have b6924 := hb (x 3 3 && x 3 13)
                have b6925 := hb (x 2 4 && x 2 14)
                have b6926 := hb (x 11 1 && x 11 11)
                have b6927 := hb (x 10 2 && x 10 12)
                have b6928 := hb (x 9 3 && x 9 13)
                have b6929 := hb (x 8 4 && x 8 14)
                linarith only [r6820, r6821, r6822, e6823, e6824, e6825, e6826, e6827, e6828, r6829, e6830, e6831, r6832, e6833, e6834, r6835, r6836, r6837, r6838, r6839, r6840, r6841, r6842, r6843, r6844, r6845, r6846, r6847, r6848, r6849, r6850, r6851, r6852, r6853, r6854, r6855, b6856, b6857, b6858, b6859, b6860, b6861, b6862, b6863, b6864, b6865, b6866, b6867, b6868, b6869, b6870, b6871, b6872, b6873, b6874, b6875, b6876, b6877, b6878, b6879, b6880, b6881, b6882, b6883, b6884, b6885, b6886, b6887, b6888, b6889, b6890, b6891, b6892, b6893, b6894, b6895, b6896, b6897, b6898, b6899, b6900, b6901, b6902, b6903, b6904, b6905, b6906, b6907, b6908, b6909, b6910, b6911, b6912, b6913, b6914, b6915, b6916, b6917, b6918, b6919, b6920, b6921, b6922, b6923, b6924, b6925, b6926, b6927, b6928, b6929, g2, g4, f6600, g6, g7, g13, g14, g17, g19, f6574, d6784, d6319, g24, d6429, d6804, d6788, g33, g34, g35, d6595, g36, g37, d6365, d6401, d6581, g53, g60, d6485, g61, g74, g75, d6405]
            · have f6930 : (x (-1) 8).toNat = 1 := by rw [h6599]; rfl
              have d6931 : (x (-2) 9).toNat = 0 := by
                have r6932 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
                have e6933 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e6934 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e6935 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e6936 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e6937 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e6938 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have b6939 := hb (x (-8) 7)
                have b6940 := hb (x (-7) 6)
                have b6941 := hb (x (-6) 5)
                have b6942 := hb (x (-5) 4)
                have b6943 := hb (x (-4) 11)
                have b6944 := hb (x (-3) 10)
                have b6945 := hb (x (-2) 9)
                have b6946 := hb (x (-1) 8)
                clear * - r6932 e6933 e6934 e6935 e6936 e6937 e6938 b6939 b6940 b6941 b6942 b6943 b6944 b6945 b6946 f6930
                omega
              have d6947 : (x (-2) 9 && x (-2) 14).toNat = 0 := by
                have r6948 := hand1 (x (-2) 9) (x (-2) 14)
                have b6949 := hb (x (-2) 9)
                have b6950 := hb (x (-2) 9 && x (-2) 14)
                clear * - r6948 b6949 b6950 d6931
                omega
              have d6951 : (x (-3) 10).toNat = 0 := by
                have r6952 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
                have e6953 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e6954 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e6955 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e6956 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e6957 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e6958 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have b6959 := hb (x (-8) 7)
                have b6960 := hb (x (-7) 6)
                have b6961 := hb (x (-6) 5)
                have b6962 := hb (x (-5) 4)
                have b6963 := hb (x (-4) 11)
                have b6964 := hb (x (-3) 10)
                have b6965 := hb (x (-2) 9)
                have b6966 := hb (x (-1) 8)
                clear * - r6952 e6953 e6954 e6955 e6956 e6957 e6958 b6959 b6960 b6961 b6962 b6963 b6964 b6965 b6966 f6930 d6931
                omega
              have d6967 : (x (-4) 11).toNat = 0 := by
                have r6968 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
                have e6969 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e6970 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e6971 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e6972 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e6973 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e6974 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have b6975 := hb (x (-8) 7)
                have b6976 := hb (x (-7) 6)
                have b6977 := hb (x (-6) 5)
                have b6978 := hb (x (-5) 4)
                have b6979 := hb (x (-4) 11)
                have b6980 := hb (x (-3) 10)
                have b6981 := hb (x (-2) 9)
                have b6982 := hb (x (-1) 8)
                clear * - r6968 e6969 e6970 e6971 e6972 e6973 e6974 b6975 b6976 b6977 b6978 b6979 b6980 b6981 b6982 f6930 d6931 d6951
                omega
              have d6983 : (x (-5) 4).toNat = 0 := by
                have r6984 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
                have e6985 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e6986 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e6987 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e6988 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e6989 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e6990 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have b6991 := hb (x (-8) 7)
                have b6992 := hb (x (-7) 6)
                have b6993 := hb (x (-6) 5)
                have b6994 := hb (x (-5) 4)
                have b6995 := hb (x (-4) 11)
                have b6996 := hb (x (-3) 10)
                have b6997 := hb (x (-2) 9)
                have b6998 := hb (x (-1) 8)
                clear * - r6984 e6985 e6986 e6987 e6988 e6989 e6990 b6991 b6992 b6993 b6994 b6995 b6996 b6997 b6998 f6930 d6931 d6951 d6967
                omega
              have d6999 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
                have r7000 := hand1 (x (-5) 4) (x (-5) 14)
                have b7001 := hb (x (-5) 4)
                have b7002 := hb (x (-5) 4 && x (-5) 14)
                clear * - r7000 b7001 b7002 d6983
                omega
              have d7003 : (x (-6) 5).toNat = 0 := by
                have r7004 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
                have e7005 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e7006 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e7007 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e7008 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e7009 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e7010 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have b7011 := hb (x (-8) 7)
                have b7012 := hb (x (-7) 6)
                have b7013 := hb (x (-6) 5)
                have b7014 := hb (x (-5) 4)
                have b7015 := hb (x (-4) 11)
                have b7016 := hb (x (-3) 10)
                have b7017 := hb (x (-2) 9)
                have b7018 := hb (x (-1) 8)
                clear * - r7004 e7005 e7006 e7007 e7008 e7009 e7010 b7011 b7012 b7013 b7014 b7015 b7016 b7017 b7018 f6930 d6931 d6951 d6967 d6983
                omega
              have r7019 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := hcount 12
              have r7020 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := hcount 14
              have r7021 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
              have e7022 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
              have e7023 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
              have e7024 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
              have e7025 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
              have e7026 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
              have e7027 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
              have r7028 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := hd12 (-3)
              have e7029 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
              have e7030 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
              have r7031 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
              have e7032 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e7033 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have r7034 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
              have e7035 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
              have e7036 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
              have r7037 : 1 ≤ (x 7 5).toNat + (x 6 1 && x 6 6).toNat + (x 5 2 && x 5 7).toNat + (x 4 3 && x 4 8).toNat + (x 3 4 && x 3 9).toNat + (x 2 5 && x 2 10).toNat + (x 1 6 && x 1 11).toNat + (x 0 7 && x 0 12).toNat + (x (-1) 8 && x (-1) 13).toNat + (x (-2) 9 && x (-2) 14).toNat + (x (-3) 10).toNat := hcov5 7
              have r7038 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := hcov6 8
              have r7039 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := hcov9 0
              have r7040 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := hcov10 (-1)
              have r7041 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := hcov11 0
              have r7042 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := hcov11 1
              have r7043 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := hcov11 12
              have r7044 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
              have r7045 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
              have r7046 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
              have r7047 := hand2 (x 6 1) (x 6 6)
              have r7048 := hand2 (x 5 2) (x 5 7)
              have r7049 := hand2 (x 4 3) (x 4 8)
              have r7050 := hand2 (x 7 1) (x 7 7)
              have r7051 := hand2 (x 6 2) (x 6 8)
              have r7052 := hand2 (x 5 3) (x 5 9)
              have r7053 := hand2 (x (-4) 4) (x (-4) 13)
              have r7054 := hand1 (x (-5) 5) (x (-5) 14)
              have r7055 := hand1 (x (-3) 2) (x (-3) 12)
              have r7056 := hand2 (x (-4) 3) (x (-4) 13)
              have r7057 := hand2 (x (-2) 2) (x (-2) 13)
              have r7058 := hand1 (x 11 1) (x 11 12)
              have r7059 := hand1 (x 10 2) (x 10 13)
              have r7060 := hand1 (x 9 3) (x 9 14)
              have r7061 := hand1 (x 13 1) (x 13 14)
              have b7062 := hb (x (-7) 7)
              have b7063 := hb (x (-6) 3)
              have b7064 := hb (x (-6) 5)
              have b7065 := hb (x (-6) 6)
              have b7066 := hb (x (-5) 2)
              have b7067 := hb (x (-5) 5)
              have b7068 := hb (x (-4) 3)
              have b7069 := hb (x (-4) 4)
              have b7070 := hb (x (-4) 13)
              have b7071 := hb (x (-3) 2)
              have b7072 := hb (x (-3) 4)
              have b7073 := hb (x (-3) 10)
              have b7074 := hb (x (-3) 11)
              have b7075 := hb (x (-3) 12)
              have b7076 := hb (x (-2) 10)
              have b7077 := hb (x (-2) 13)
              have b7078 := hb (x (-2) 14)
              have b7079 := hb (x (-1) 9)
              have b7080 := hb (x (-1) 10)
              have b7081 := hb (x (-1) 12)
              have b7082 := hb (x (-1) 13)
              have b7083 := hb (x 0 8)
              have b7084 := hb (x 0 9)
              have b7085 := hb (x 0 11)
              have b7086 := hb (x 0 12)
              have b7087 := hb (x 0 14)
              have b7088 := hb (x 1 11)
              have b7089 := hb (x 1 13)
              have b7090 := hb (x 2 10)
              have b7091 := hb (x 2 12)
              have b7092 := hb (x 3 9)
              have b7093 := hb (x 3 11)
              have b7094 := hb (x 4 8)
              have b7095 := hb (x 4 10)
              have b7096 := hb (x 5 7)
              have b7097 := hb (x 5 9)
              have b7098 := hb (x 6 6)
              have b7099 := hb (x 6 8)
              have b7100 := hb (x 7 5)
              have b7101 := hb (x 7 7)
              have b7102 := hb (x 8 4)
              have b7103 := hb (x 8 6)
              have b7104 := hb (x 9 3)
              have b7105 := hb (x 9 5)
              have b7106 := hb (x 10 2)
              have b7107 := hb (x 10 4)
              have b7108 := hb (x 11 1)
              have b7109 := hb (x 11 3)
              have b7110 := hb (x 12 2)
              have b7111 := hb (x 12 3)
              have b7112 := hb (x 12 11)
              have b7113 := hb (x 13 1)
              have b7114 := hb (x 13 2)
              have b7115 := hb (x 14 13)
              have b7116 := hb (x 15 12)
              have b7117 := hb (x 6 1 && x 6 6)
              have b7118 := hb (x 5 2 && x 5 7)
              have b7119 := hb (x 4 3 && x 4 8)
              have b7120 := hb (x 3 4 && x 3 9)
              have b7121 := hb (x 2 5 && x 2 10)
              have b7122 := hb (x 1 6 && x 1 11)
              have b7123 := hb (x 0 7 && x 0 12)
              have b7124 := hb (x (-1) 8 && x (-1) 13)
              have b7125 := hb (x (-2) 9 && x (-2) 14)
              have b7126 := hb (x 7 1 && x 7 7)
              have b7127 := hb (x 6 2 && x 6 8)
              have b7128 := hb (x 5 3 && x 5 9)
              have b7129 := hb (x 4 4 && x 4 10)
              have b7130 := hb (x 3 5 && x 3 11)
              have b7131 := hb (x 2 6 && x 2 12)
              have b7132 := hb (x 1 7 && x 1 13)
              have b7133 := hb (x 0 8 && x 0 14)
              have b7134 := hb (x (-1) 1 && x (-1) 10)
              have b7135 := hb (x (-2) 2 && x (-2) 11)
              have b7136 := hb (x (-3) 3 && x (-3) 12)
              have b7137 := hb (x (-4) 4 && x (-4) 13)
              have b7138 := hb (x (-5) 5 && x (-5) 14)
              have b7139 := hb (x (-2) 1 && x (-2) 11)
              have b7140 := hb (x (-3) 2 && x (-3) 12)
              have b7141 := hb (x (-4) 3 && x (-4) 13)
              have b7142 := hb (x (-5) 4 && x (-5) 14)
              have b7143 := hb (x (-1) 1 && x (-1) 12)
              have b7144 := hb (x (-2) 2 && x (-2) 13)
              have b7145 := hb (x (-3) 3 && x (-3) 14)
              have b7146 := hb (x 0 1 && x 0 12)
              have b7147 := hb (x (-1) 2 && x (-1) 13)
              have b7148 := hb (x (-2) 3 && x (-2) 14)
              have b7149 := hb (x 11 1 && x 11 12)
              have b7150 := hb (x 10 2 && x 10 13)
              have b7151 := hb (x 9 3 && x 9 14)
              have b7152 := hb (x 13 1 && x 13 14)
              linarith only [r7019, r7020, r7021, e7022, e7023, e7024, e7025, e7026, e7027, r7028, e7029, e7030, r7031, e7032, e7033, r7034, e7035, e7036, r7037, r7038, r7039, r7040, r7041, r7042, r7043, r7044, r7045, r7046, r7047, r7048, r7049, r7050, r7051, r7052, r7053, r7054, r7055, r7056, r7057, r7058, r7059, r7060, r7061, b7062, b7063, b7064, b7065, b7066, b7067, b7068, b7069, b7070, b7071, b7072, b7073, b7074, b7075, b7076, b7077, b7078, b7079, b7080, b7081, b7082, b7083, b7084, b7085, b7086, b7087, b7088, b7089, b7090, b7091, b7092, b7093, b7094, b7095, b7096, b7097, b7098, b7099, b7100, b7101, b7102, b7103, b7104, b7105, b7106, b7107, b7108, b7109, b7110, b7111, b7112, b7113, b7114, b7115, b7116, b7117, b7118, b7119, b7120, b7121, b7122, b7123, b7124, b7125, b7126, b7127, b7128, b7129, b7130, b7131, b7132, b7133, b7134, b7135, b7136, b7137, b7138, b7139, b7140, b7141, b7142, b7143, b7144, b7145, b7146, b7147, b7148, b7149, b7150, b7151, b7152, d7003, d6951, g2, g4, g6, d6315, g7, g13, g14, g16, g17, g19, d6319, g24, d6429, d6369, g40, d6585, g41, g42, d6947, g47, g48, d6425, d6591, g49, g60, d6485, g61, d6481, d6999, g78, g79, g80, g81, d6469]
          · have f7153 : (x 1 7).toNat = 1 := by rw [h6589]; rfl
            have d7154 : (x 8 8).toNat = 0 := by
              have r7155 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
              have e7156 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e7157 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e7158 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e7159 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e7160 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e7161 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b7162 := hb (x 1 7)
              have b7163 := hb (x 2 6)
              have b7164 := hb (x 3 5)
              have b7165 := hb (x 4 4)
              have b7166 := hb (x 5 11)
              have b7167 := hb (x 6 10)
              have b7168 := hb (x 7 9)
              have b7169 := hb (x 8 8)
              clear * - r7155 e7156 e7157 e7158 e7159 e7160 e7161 b7162 b7163 b7164 b7165 b7166 b7167 b7168 b7169 g27 g25 d6421 f7153
              omega
            have d7170 : (x 7 9).toNat = 0 := by
              have r7171 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
              have e7172 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e7173 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e7174 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e7175 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e7176 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e7177 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b7178 := hb (x 1 7)
              have b7179 := hb (x 2 6)
              have b7180 := hb (x 3 5)
              have b7181 := hb (x 4 4)
              have b7182 := hb (x 5 11)
              have b7183 := hb (x 6 10)
              have b7184 := hb (x 7 9)
              have b7185 := hb (x 8 8)
              clear * - r7171 e7172 e7173 e7174 e7175 e7176 e7177 b7178 b7179 b7180 b7181 b7182 b7183 b7184 b7185 d7154 g27 g25 d6421 f7153
              omega
            have d7186 : (x 6 10).toNat = 0 := by
              have r7187 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
              have e7188 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e7189 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e7190 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e7191 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e7192 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e7193 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b7194 := hb (x 1 7)
              have b7195 := hb (x 2 6)
              have b7196 := hb (x 3 5)
              have b7197 := hb (x 4 4)
              have b7198 := hb (x 5 11)
              have b7199 := hb (x 6 10)
              have b7200 := hb (x 7 9)
              have b7201 := hb (x 8 8)
              clear * - r7187 e7188 e7189 e7190 e7191 e7192 e7193 b7194 b7195 b7196 b7197 b7198 b7199 b7200 b7201 d7154 d7170 g27 g25 d6421 f7153
              omega
            have d7202 : (x 6 1 && x 6 10).toNat = 0 := by
              have r7203 := hand2 (x 6 1) (x 6 10)
              have b7204 := hb (x 6 10)
              have b7205 := hb (x 6 1 && x 6 10)
              clear * - r7203 b7204 b7205 d7186
              omega
            have d7206 : (x 5 2 && x 5 11).toNat = 1 := by
              have r7207 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := hcov9 7
              have b7208 := hb (x 1 6)
              have b7209 := hb (x 7 9)
              have b7210 := hb (x 6 1 && x 6 10)
              have b7211 := hb (x 5 2 && x 5 11)
              have b7212 := hb (x 4 3 && x 4 12)
              have b7213 := hb (x 3 4 && x 3 13)
              have b7214 := hb (x 2 5 && x 2 14)
              clear * - r7207 b7208 b7209 b7210 b7211 b7212 b7213 b7214 d7170 d7202 g66 g67 d6397 f6580
              omega
            have d7215 : (x 5 11).toNat = 1 := by
              have r7216 := hand2 (x 5 2) (x 5 11)
              have b7217 := hb (x 5 11)
              have b7218 := hb (x 5 2 && x 5 11)
              clear * - r7216 b7217 b7218 d7206
              omega
            have r7219 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
            have e7220 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e7221 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e7222 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e7223 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e7224 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e7225 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have b7226 := hb (x 1 7)
            have b7227 := hb (x 2 6)
            have b7228 := hb (x 3 5)
            have b7229 := hb (x 4 4)
            have b7230 := hb (x 5 11)
            have b7231 := hb (x 6 10)
            have b7232 := hb (x 7 9)
            have b7233 := hb (x 8 8)
            linarith only [r7219, e7220, e7221, e7222, e7223, e7224, e7225, b7226, b7227, b7228, b7229, b7230, b7231, b7232, b7233, d7154, d7170, d7186, d7215, g27, g25, d6421, f7153]
        · have f7234 : (x 1 6).toNat = 1 := by rw [h6579]; rfl
          have d7235 : (x 7 8).toNat = 0 := by
            have r7236 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
            have e7237 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
            have e7238 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
            have e7239 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
            have e7240 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
            have e7241 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
            have e7242 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
            have b7243 := hb (x 0 7)
            have b7244 := hb (x 1 6)
            have b7245 := hb (x 2 5)
            have b7246 := hb (x 3 4)
            have b7247 := hb (x 4 11)
            have b7248 := hb (x 5 10)
            have b7249 := hb (x 6 9)
            have b7250 := hb (x 7 8)
            clear * - r7236 e7237 e7238 e7239 e7240 e7241 e7242 b7243 b7244 b7245 b7246 b7247 b7248 b7249 b7250 d6357 d6393 f7234 g12
            omega
          have d7251 : (x 6 9).toNat = 0 := by
            have r7252 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
            have e7253 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
            have e7254 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
            have e7255 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
            have e7256 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
            have e7257 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
            have e7258 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
            have b7259 := hb (x 0 7)
            have b7260 := hb (x 1 6)
            have b7261 := hb (x 2 5)
            have b7262 := hb (x 3 4)
            have b7263 := hb (x 4 11)
            have b7264 := hb (x 5 10)
            have b7265 := hb (x 6 9)
            have b7266 := hb (x 7 8)
            clear * - r7252 e7253 e7254 e7255 e7256 e7257 e7258 b7259 b7260 b7261 b7262 b7263 b7264 b7265 b7266 d7235 d6357 d6393 f7234 g12
            omega
          have d7267 : (x 5 10).toNat = 0 := by
            have r7268 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
            have e7269 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
            have e7270 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
            have e7271 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
            have e7272 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
            have e7273 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
            have e7274 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
            have b7275 := hb (x 0 7)
            have b7276 := hb (x 1 6)
            have b7277 := hb (x 2 5)
            have b7278 := hb (x 3 4)
            have b7279 := hb (x 4 11)
            have b7280 := hb (x 5 10)
            have b7281 := hb (x 6 9)
            have b7282 := hb (x 7 8)
            clear * - r7268 e7269 e7270 e7271 e7272 e7273 e7274 b7275 b7276 b7277 b7278 b7279 b7280 b7281 b7282 d7235 d7251 d6357 d6393 f7234 g12
            omega
          have d7283 : (x 5 1 && x 5 10).toNat = 0 := by
            have r7284 := hand2 (x 5 1) (x 5 10)
            have b7285 := hb (x 5 10)
            have b7286 := hb (x 5 1 && x 5 10)
            clear * - r7284 b7285 b7286 d7267
            omega
          have d7287 : (x 4 2 && x 4 11).toNat = 1 := by
            have r7288 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := hcov9 6
            have b7289 := hb (x 0 6)
            have b7290 := hb (x 6 9)
            have b7291 := hb (x 5 1 && x 5 10)
            have b7292 := hb (x 4 2 && x 4 11)
            have b7293 := hb (x 3 3 && x 3 12)
            have b7294 := hb (x 2 4 && x 2 13)
            have b7295 := hb (x 1 5 && x 1 14)
            clear * - r7288 b7289 b7290 b7291 b7292 b7293 b7294 b7295 d7251 d7283 d6349 d6381 d6575 f6570
            omega
          have d7296 : (x 4 11).toNat = 1 := by
            have r7297 := hand2 (x 4 2) (x 4 11)
            have b7298 := hb (x 4 11)
            have b7299 := hb (x 4 2 && x 4 11)
            clear * - r7297 b7298 b7299 d7287
            omega
          have r7300 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
          have e7301 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e7302 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e7303 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e7304 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e7305 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e7306 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have b7307 := hb (x 0 7)
          have b7308 := hb (x 1 6)
          have b7309 := hb (x 2 5)
          have b7310 := hb (x 3 4)
          have b7311 := hb (x 4 11)
          have b7312 := hb (x 5 10)
          have b7313 := hb (x 6 9)
          have b7314 := hb (x 7 8)
          linarith only [r7300, e7301, e7302, e7303, e7304, e7305, e7306, b7307, b7308, b7309, b7310, b7311, b7312, b7313, b7314, d7235, d7251, d7267, d7296, d6357, d6393, f7234, g12]
      · have f7315 : (x 1 5).toNat = 1 := by rw [h6573]; rfl
        have d7316 : (x 6 8).toNat = 0 := by
          have r7317 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
          have e7318 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
          have e7319 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
          have e7320 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
          have e7321 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
          have e7322 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
          have e7323 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
          have b7324 := hb (x (-1) 7)
          have b7325 := hb (x 0 6)
          have b7326 := hb (x 1 5)
          have b7327 := hb (x 2 4)
          have b7328 := hb (x 3 11)
          have b7329 := hb (x 4 10)
          have b7330 := hb (x 5 9)
          have b7331 := hb (x 6 8)
          clear * - r7317 e7318 e7319 e7320 e7321 e7322 e7323 b7324 b7325 b7326 b7327 b7328 b7329 b7330 b7331 d6441 f7315 f6570
          omega
        have d7332 : (x 6 1 && x 6 8).toNat = 0 := by
          have r7333 := hand2 (x 6 1) (x 6 8)
          have b7334 := hb (x 6 8)
          have b7335 := hb (x 6 1 && x 6 8)
          clear * - r7333 b7334 b7335 d7316
          omega
        have d7336 : (x 6 2 && x 6 8).toNat = 0 := by
          have r7337 := hand2 (x 6 2) (x 6 8)
          have b7338 := hb (x 6 8)
          have b7339 := hb (x 6 2 && x 6 8)
          clear * - r7337 b7338 b7339 d7316
          omega
        have d7340 : (x 6 3 && x 6 8).toNat = 0 := by
          have r7341 := hand2 (x 6 3) (x 6 8)
          have b7342 := hb (x 6 8)
          have b7343 := hb (x 6 3 && x 6 8)
          clear * - r7341 b7342 b7343 d7316
          omega
        have d7344 : (x 5 9).toNat = 0 := by
          have r7345 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
          have e7346 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
          have e7347 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
          have e7348 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
          have e7349 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
          have e7350 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
          have e7351 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
          have b7352 := hb (x (-1) 7)
          have b7353 := hb (x 0 6)
          have b7354 := hb (x 1 5)
          have b7355 := hb (x 2 4)
          have b7356 := hb (x 3 11)
          have b7357 := hb (x 4 10)
          have b7358 := hb (x 5 9)
          have b7359 := hb (x 6 8)
          clear * - r7345 e7346 e7347 e7348 e7349 e7350 e7351 b7352 b7353 b7354 b7355 b7356 b7357 b7358 b7359 d7316 d6441 f7315 f6570
          omega
        have d7360 : (x 5 2 && x 5 9).toNat = 0 := by
          have r7361 := hand2 (x 5 2) (x 5 9)
          have b7362 := hb (x 5 9)
          have b7363 := hb (x 5 2 && x 5 9)
          clear * - r7361 b7362 b7363 d7344
          omega
        have d7364 : (x 5 3 && x 5 9).toNat = 0 := by
          have r7365 := hand2 (x 5 3) (x 5 9)
          have b7366 := hb (x 5 9)
          have b7367 := hb (x 5 3 && x 5 9)
          clear * - r7365 b7366 b7367 d7344
          omega
        have d7368 : (x 5 4 && x 5 9).toNat = 0 := by
          have r7369 := hand2 (x 5 4) (x 5 9)
          have b7370 := hb (x 5 9)
          have b7371 := hb (x 5 4 && x 5 9)
          clear * - r7369 b7370 b7371 d7344
          omega
        have d7372 : (x 4 10).toNat = 0 := by
          have r7373 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
          have e7374 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
          have e7375 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
          have e7376 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
          have e7377 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
          have e7378 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
          have e7379 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
          have b7380 := hb (x (-1) 7)
          have b7381 := hb (x 0 6)
          have b7382 := hb (x 1 5)
          have b7383 := hb (x 2 4)
          have b7384 := hb (x 3 11)
          have b7385 := hb (x 4 10)
          have b7386 := hb (x 5 9)
          have b7387 := hb (x 6 8)
          clear * - r7373 e7374 e7375 e7376 e7377 e7378 e7379 b7380 b7381 b7382 b7383 b7384 b7385 b7386 b7387 d7316 d7344 d6441 f7315 f6570
          omega
        have d7388 : (x 4 3 && x 4 10).toNat = 0 := by
          have r7389 := hand2 (x 4 3) (x 4 10)
          have b7390 := hb (x 4 10)
          have b7391 := hb (x 4 3 && x 4 10)
          clear * - r7389 b7390 b7391 d7372
          omega
        have d7392 : (x 4 5 && x 4 10).toNat = 0 := by
          have r7393 := hand2 (x 4 5) (x 4 10)
          have b7394 := hb (x 4 10)
          have b7395 := hb (x 4 5 && x 4 10)
          clear * - r7393 b7394 b7395 d7372
          omega
        have d7396 : (x 3 11).toNat = 0 := by
          have r7397 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
          have e7398 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
          have e7399 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
          have e7400 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
          have e7401 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
          have e7402 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
          have e7403 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
          have b7404 := hb (x (-1) 7)
          have b7405 := hb (x 0 6)
          have b7406 := hb (x 1 5)
          have b7407 := hb (x 2 4)
          have b7408 := hb (x 3 11)
          have b7409 := hb (x 4 10)
          have b7410 := hb (x 5 9)
          have b7411 := hb (x 6 8)
          clear * - r7397 e7398 e7399 e7400 e7401 e7402 e7403 b7404 b7405 b7406 b7407 b7408 b7409 b7410 b7411 d7316 d7344 d7372 d6441 f7315 f6570
          omega
        have d7412 : (x 3 6 && x 3 11).toNat = 0 := by
          have r7413 := hand2 (x 3 6) (x 3 11)
          have b7414 := hb (x 3 11)
          have b7415 := hb (x 3 6 && x 3 11)
          clear * - r7413 b7414 b7415 d7396
          omega
        cases h7416 : x 1 6
        · have f7417 : (x 1 6).toNat = 0 := by rw [h7416]; rfl
          have d7418 : (x 1 6 && x 1 13).toNat = 0 := by
            have r7419 := hand1 (x 1 6) (x 1 13)
            have b7420 := hb (x 1 6)
            have b7421 := hb (x 1 6 && x 1 13)
            clear * - r7419 b7420 b7421 f7417
            omega
          have d7422 : (x 1 6 && x 1 11).toNat = 0 := by
            have r7423 := hand1 (x 1 6) (x 1 11)
            have b7424 := hb (x 1 6)
            have b7425 := hb (x 1 6 && x 1 11)
            clear * - r7423 b7424 b7425 f7417
            omega
          cases h7426 : x 1 7
          · have f7427 : (x 1 7).toNat = 0 := by rw [h7426]; rfl
            have d7428 : (x 1 7 && x 1 13).toNat = 0 := by
              have r7429 := hand1 (x 1 7) (x 1 13)
              have b7430 := hb (x 1 7)
              have b7431 := hb (x 1 7 && x 1 13)
              clear * - r7429 b7430 b7431 f7427
              omega
            cases h7432 : x (-1) 8
            · have f7433 : (x (-1) 8).toNat = 0 := by rw [h7432]; rfl
              have d7434 : (x 7 7).toNat = 1 := by
                have r7435 : 1 ≤ (x 7 7).toNat + (x 6 1 && x 6 8).toNat + (x 5 2 && x 5 9).toNat + (x 4 3 && x 4 10).toNat + (x 3 4 && x 3 11).toNat + (x 2 5 && x 2 12).toNat + (x 1 6 && x 1 13).toNat + (x 0 7 && x 0 14).toNat + (x (-1) 8).toNat := hcov7 7
                have b7436 := hb (x (-1) 8)
                have b7437 := hb (x 7 7)
                have b7438 := hb (x 6 1 && x 6 8)
                have b7439 := hb (x 5 2 && x 5 9)
                have b7440 := hb (x 4 3 && x 4 10)
                have b7441 := hb (x 3 4 && x 3 11)
                have b7442 := hb (x 2 5 && x 2 12)
                have b7443 := hb (x 1 6 && x 1 13)
                have b7444 := hb (x 0 7 && x 0 14)
                clear * - r7435 b7436 b7437 b7438 b7439 b7440 b7441 b7442 b7443 b7444 d7332 d7360 d7388 d6365 d6401 d7418 g53 f7433
                omega
              have d7445 : (x 14 8).toNat = 0 := by
                have r7446 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := hd8 14
                have e7447 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                have e7448 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                have e7449 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                have e7450 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                have e7451 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                have e7452 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                have b7453 := hb (x 7 7)
                have b7454 := hb (x 8 6)
                have b7455 := hb (x 9 5)
                have b7456 := hb (x 10 4)
                have b7457 := hb (x 11 11)
                have b7458 := hb (x 12 10)
                have b7459 := hb (x 13 9)
                have b7460 := hb (x 14 8)
                clear * - r7446 e7447 e7448 e7449 e7450 e7451 e7452 b7453 b7454 b7455 b7456 b7457 b7458 b7459 b7460 d7434
                omega
              have d7461 : (x 14 8 && x 14 9).toNat = 0 := by
                have r7462 := hand1 (x 14 8) (x 14 9)
                have b7463 := hb (x 14 8)
                have b7464 := hb (x 14 8 && x 14 9)
                clear * - r7462 b7463 b7464 d7445
                omega
              have d7465 : (x 13 9).toNat = 0 := by
                have r7466 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := hd8 14
                have e7467 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                have e7468 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                have e7469 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                have e7470 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                have e7471 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                have e7472 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                have b7473 := hb (x 7 7)
                have b7474 := hb (x 8 6)
                have b7475 := hb (x 9 5)
                have b7476 := hb (x 10 4)
                have b7477 := hb (x 11 11)
                have b7478 := hb (x 12 10)
                have b7479 := hb (x 13 9)
                have b7480 := hb (x 14 8)
                clear * - r7466 e7467 e7468 e7469 e7470 e7471 e7472 b7473 b7474 b7475 b7476 b7477 b7478 b7479 b7480 d7445 d7434
                omega
              have d7481 : (x 13 9 && x 13 10).toNat = 0 := by
                have r7482 := hand1 (x 13 9) (x 13 10)
                have b7483 := hb (x 13 9)
                have b7484 := hb (x 13 9 && x 13 10)
                clear * - r7482 b7483 b7484 d7465
                omega
              have d7485 : (x 12 10).toNat = 0 := by
                have r7486 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := hd8 14
                have e7487 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                have e7488 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                have e7489 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                have e7490 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                have e7491 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                have e7492 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                have b7493 := hb (x 7 7)
                have b7494 := hb (x 8 6)
                have b7495 := hb (x 9 5)
                have b7496 := hb (x 10 4)
                have b7497 := hb (x 11 11)
                have b7498 := hb (x 12 10)
                have b7499 := hb (x 13 9)
                have b7500 := hb (x 14 8)
                clear * - r7486 e7487 e7488 e7489 e7490 e7491 e7492 b7493 b7494 b7495 b7496 b7497 b7498 b7499 b7500 d7445 d7465 d7434
                omega
              have d7501 : (x 12 10 && x 12 11).toNat = 0 := by
                have r7502 := hand1 (x 12 10) (x 12 11)
                have b7503 := hb (x 12 10)
                have b7504 := hb (x 12 10 && x 12 11)
                clear * - r7502 b7503 b7504 d7485
                omega
              have d7505 : (x 11 11).toNat = 0 := by
                have r7506 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := hd8 14
                have e7507 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                have e7508 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                have e7509 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                have e7510 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                have e7511 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                have e7512 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                have b7513 := hb (x 7 7)
                have b7514 := hb (x 8 6)
                have b7515 := hb (x 9 5)
                have b7516 := hb (x 10 4)
                have b7517 := hb (x 11 11)
                have b7518 := hb (x 12 10)
                have b7519 := hb (x 13 9)
                have b7520 := hb (x 14 8)
                clear * - r7506 e7507 e7508 e7509 e7510 e7511 e7512 b7513 b7514 b7515 b7516 b7517 b7518 b7519 b7520 d7445 d7465 d7485 d7434
                omega
              have d7521 : (x 11 11 && x 11 12).toNat = 0 := by
                have r7522 := hand1 (x 11 11) (x 11 12)
                have b7523 := hb (x 11 11)
                have b7524 := hb (x 11 11 && x 11 12)
                clear * - r7522 b7523 b7524 d7505
                omega
              have d7525 : (x 10 4).toNat = 0 := by
                have r7526 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := hd8 14
                have e7527 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                have e7528 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                have e7529 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                have e7530 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                have e7531 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                have e7532 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                have b7533 := hb (x 7 7)
                have b7534 := hb (x 8 6)
                have b7535 := hb (x 9 5)
                have b7536 := hb (x 10 4)
                have b7537 := hb (x 11 11)
                have b7538 := hb (x 12 10)
                have b7539 := hb (x 13 9)
                have b7540 := hb (x 14 8)
                clear * - r7526 e7527 e7528 e7529 e7530 e7531 e7532 b7533 b7534 b7535 b7536 b7537 b7538 b7539 b7540 d7445 d7465 d7485 d7505 d7434
                omega
              have d7541 : (x 10 4 && x 10 14).toNat = 0 := by
                have r7542 := hand1 (x 10 4) (x 10 14)
                have b7543 := hb (x 10 4)
                have b7544 := hb (x 10 4 && x 10 14)
                clear * - r7542 b7543 b7544 d7525
                omega
              have d7545 : (x 10 4 && x 10 13).toNat = 0 := by
                have r7546 := hand1 (x 10 4) (x 10 13)
                have b7547 := hb (x 10 4)
                have b7548 := hb (x 10 4 && x 10 13)
                clear * - r7546 b7547 b7548 d7525
                omega
              have d7549 : (x 9 5).toNat = 0 := by
                have r7550 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := hd8 14
                have e7551 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                have e7552 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                have e7553 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                have e7554 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                have e7555 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                have e7556 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                have b7557 := hb (x 7 7)
                have b7558 := hb (x 8 6)
                have b7559 := hb (x 9 5)
                have b7560 := hb (x 10 4)
                have b7561 := hb (x 11 11)
                have b7562 := hb (x 12 10)
                have b7563 := hb (x 13 9)
                have b7564 := hb (x 14 8)
                clear * - r7550 e7551 e7552 e7553 e7554 e7555 e7556 b7557 b7558 b7559 b7560 b7561 b7562 b7563 b7564 d7445 d7465 d7485 d7505 d7525 d7434
                omega
              have d7565 : (x 9 5 && x 9 14).toNat = 0 := by
                have r7566 := hand1 (x 9 5) (x 9 14)
                have b7567 := hb (x 9 5)
                have b7568 := hb (x 9 5 && x 9 14)
                clear * - r7566 b7567 b7568 d7549
                omega
              have d7569 : (x 8 6).toNat = 0 := by
                have r7570 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := hd8 14
                have e7571 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                have e7572 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                have e7573 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                have e7574 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                have e7575 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                have e7576 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                have b7577 := hb (x 7 7)
                have b7578 := hb (x 8 6)
                have b7579 := hb (x 9 5)
                have b7580 := hb (x 10 4)
                have b7581 := hb (x 11 11)
                have b7582 := hb (x 12 10)
                have b7583 := hb (x 13 9)
                have b7584 := hb (x 14 8)
                clear * - r7570 e7571 e7572 e7573 e7574 e7575 e7576 b7577 b7578 b7579 b7580 b7581 b7582 b7583 b7584 d7445 d7465 d7485 d7505 d7525 d7549 d7434
                omega
              have d7585 : (x 8 1 && x 8 6).toNat = 0 := by
                have r7586 := hand2 (x 8 1) (x 8 6)
                have b7587 := hb (x 8 6)
                have b7588 := hb (x 8 1 && x 8 6)
                clear * - r7586 b7587 b7588 d7569
                omega
              have d7589 : (x 7 1 && x 7 7).toNat = 1 := by
                have r7590 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := hcov6 8
                have b7591 := hb (x (-1) 9)
                have b7592 := hb (x 8 6)
                have b7593 := hb (x 7 1 && x 7 7)
                have b7594 := hb (x 6 2 && x 6 8)
                have b7595 := hb (x 5 3 && x 5 9)
                have b7596 := hb (x 4 4 && x 4 10)
                have b7597 := hb (x 3 5 && x 3 11)
                have b7598 := hb (x 2 6 && x 2 12)
                have b7599 := hb (x 1 7 && x 1 13)
                have b7600 := hb (x 0 8 && x 0 14)
                clear * - r7590 b7591 b7592 b7593 b7594 b7595 b7596 b7597 b7598 b7599 b7600 d7569 d7336 d7364 g47 g48 d6425 d7428 g49 g6
                omega
              have d7601 : (x 7 1).toNat = 1 := by
                have r7602 := hand1 (x 7 1) (x 7 7)
                have b7603 := hb (x 7 1)
                have b7604 := hb (x 7 1 && x 7 7)
                clear * - r7602 b7603 b7604 d7589
                omega
              have d7605 : (x 8 14).toNat = 0 := by
                have r7606 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
                have b7607 := hb (x 7 1)
                have b7608 := hb (x 8 14)
                clear * - r7606 b7607 b7608 d7601
                omega
              have d7609 : (x 8 2).toNat = 0 := by
                have r7610 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
                have b7611 := hb (x 8 2)
                have b7612 := hb (x 8 14)
                clear * - r7610 b7611 b7612 d7605
                omega
              have d7613 : (x 8 10).toNat = 0 := by
                have r7614 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
                have b7615 := hb (x 8 2)
                have b7616 := hb (x 8 10)
                clear * - r7614 b7615 b7616 d7609
                omega
              have d7617 : (x 7 2 && x 7 7).toNat = 1 := by
                have r7618 : 1 ≤ (x 9 5).toNat + (x 8 1 && x 8 6).toNat + (x 7 2 && x 7 7).toNat + (x 6 3 && x 6 8).toNat + (x 5 4 && x 5 9).toNat + (x 4 5 && x 4 10).toNat + (x 3 6 && x 3 11).toNat + (x 2 7 && x 2 12).toNat + (x 1 8 && x 1 13).toNat + (x 0 9 && x 0 14).toNat + (x (-1) 10).toNat := hcov5 9
                have b7619 := hb (x (-1) 10)
                have b7620 := hb (x 9 5)
                have b7621 := hb (x 8 1 && x 8 6)
                have b7622 := hb (x 7 2 && x 7 7)
                have b7623 := hb (x 6 3 && x 6 8)
                have b7624 := hb (x 5 4 && x 5 9)
                have b7625 := hb (x 4 5 && x 4 10)
                have b7626 := hb (x 3 6 && x 3 11)
                have b7627 := hb (x 2 7 && x 2 12)
                have b7628 := hb (x 1 8 && x 1 13)
                have b7629 := hb (x 0 9 && x 0 14)
                clear * - r7618 b7619 b7620 b7621 b7622 b7623 b7624 b7625 b7626 b7627 b7628 b7629 d7549 d7585 d7340 d7368 d7392 d7412 d6437 g43 g44 d6315
                omega
              have d7630 : (x 7 2).toNat = 1 := by
                have r7631 := hand1 (x 7 2) (x 7 7)
                have b7632 := hb (x 7 2)
                have b7633 := hb (x 7 2 && x 7 7)
                clear * - r7631 b7632 b7633 d7617
                omega
              have d7634 : (x 7 14).toNat = 1 := by
                have r7635 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
                have b7636 := hb (x 7 2)
                have b7637 := hb (x 7 14)
                clear * - r7635 b7636 b7637 d7630
                omega
              have d7638 : (x 6 1).toNat = 0 := by
                have r7639 : (x 7 14).toNat + (x 6 1).toNat = 1 := hd14 7
                have b7640 := hb (x 6 1)
                have b7641 := hb (x 7 14)
                clear * - r7639 b7640 b7641 d7634
                omega
              have d7642 : (x 6 1 && x 6 14).toNat = 0 := by
                have r7643 := hand1 (x 6 1) (x 6 14)
                have b7644 := hb (x 6 1)
                have b7645 := hb (x 6 1 && x 6 14)
                clear * - r7643 b7644 b7645 d7638
                omega
              have d7646 : (x 6 1 && x 6 10).toNat = 0 := by
                have r7647 := hand1 (x 6 1) (x 6 10)
                have b7648 := hb (x 6 1)
                have b7649 := hb (x 6 1 && x 6 10)
                clear * - r7647 b7648 b7649 d7638
                omega
              have d7650 : (x 6 13).toNat = 0 := by
                have r7651 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
                have b7652 := hb (x 6 1)
                have b7653 := hb (x 6 13)
                clear * - r7651 b7652 b7653 d7638
                omega
              have d7654 : (x 6 5).toNat = 0 := by
                have r7655 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
                have b7656 := hb (x 6 5)
                have b7657 := hb (x 6 13)
                clear * - r7655 b7656 b7657 d7650
                omega
              have d7658 : (x 6 9).toNat = 0 := by
                have r7659 : (x 6 9).toNat ≤ (x 6 1).toNat := himp _ _ (hp9 6)
                have b7660 := hb (x 6 1)
                have b7661 := hb (x 6 9)
                clear * - r7659 b7660 b7661 d7638
                omega
              have d7662 : (x 9 12).toNat = 0 := by
                have r7663 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
                have e7664 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                have e7665 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                have b7666 := hb (x 6 3)
                have b7667 := hb (x 7 2)
                have b7668 := hb (x 8 13)
                have b7669 := hb (x 9 12)
                clear * - r7663 e7664 e7665 b7666 b7667 b7668 b7669 d7630
                omega
              have d7670 : (x 9 2 && x 9 12).toNat = 0 := by
                have r7671 := hand2 (x 9 2) (x 9 12)
                have b7672 := hb (x 9 12)
                have b7673 := hb (x 9 2 && x 9 12)
                clear * - r7671 b7672 b7673 d7662
                omega
              have d7674 : (x 9 4).toNat = 0 := by
                have r7675 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
                have b7676 := hb (x 9 4)
                have b7677 := hb (x 9 12)
                clear * - r7675 b7676 b7677 d7662
                omega
              have d7678 : (x 9 4 && x 9 14).toNat = 0 := by
                have r7679 := hand1 (x 9 4) (x 9 14)
                have b7680 := hb (x 9 4)
                have b7681 := hb (x 9 4 && x 9 14)
                clear * - r7679 b7680 b7681 d7674
                omega
              have d7682 : (x 8 13).toNat = 0 := by
                have r7683 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
                have e7684 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                have e7685 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                have b7686 := hb (x 6 3)
                have b7687 := hb (x 7 2)
                have b7688 := hb (x 8 13)
                have b7689 := hb (x 9 12)
                clear * - r7683 e7684 e7685 b7686 b7687 b7688 b7689 d7662 d7630
                omega
              have d7690 : (x 8 3 && x 8 13).toNat = 0 := by
                have r7691 := hand2 (x 8 3) (x 8 13)
                have b7692 := hb (x 8 13)
                have b7693 := hb (x 8 3 && x 8 13)
                clear * - r7691 b7692 b7693 d7682
                omega
              have d7694 : (x 8 5).toNat = 0 := by
                have r7695 : (x 8 5).toNat ≤ (x 8 13).toNat := himp _ _ (hp5 8)
                have b7696 := hb (x 8 5)
                have b7697 := hb (x 8 13)
                clear * - r7695 b7696 b7697 d7682
                omega
              have d7698 : (x 6 3).toNat = 0 := by
                have r7699 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
                have e7700 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                have e7701 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                have b7702 := hb (x 6 3)
                have b7703 := hb (x 7 2)
                have b7704 := hb (x 8 13)
                have b7705 := hb (x 9 12)
                clear * - r7699 e7700 e7701 b7702 b7703 b7704 b7705 d7662 d7682 d7630
                omega
              have d7706 : (x 6 3 && x 6 7).toNat = 0 := by
                have r7707 := hand1 (x 6 3) (x 6 7)
                have b7708 := hb (x 6 3)
                have b7709 := hb (x 6 3 && x 6 7)
                clear * - r7707 b7708 b7709 d7698
                omega
              have d7710 : (x 7 2 && x 7 6).toNat = 1 := by
                have r7711 : 1 ≤ (x 9 4).toNat + (x 8 1 && x 8 5).toNat + (x 7 2 && x 7 6).toNat + (x 6 3 && x 6 7).toNat + (x 5 4 && x 5 8).toNat + (x 4 5 && x 4 9).toNat + (x 3 6 && x 3 10).toNat + (x 2 7 && x 2 11).toNat + (x 1 8 && x 1 12).toNat + (x 0 9 && x 0 13).toNat + (x (-1) 10 && x (-1) 14).toNat + (x (-2) 11).toNat := hcov4 9
                have e7712 : (x 8 1 && x 8 5).toNat = (x 8 5).toNat := handr _ _ (fun h => hp13 8 (hp5 8 (h)))
                have e7713 : (x (-1) 10 && x (-1) 14).toNat = (x (-1) 10).toNat := handl _ _ (fun h => hp2 (-1) (hp10 (-1) (h)))
                have b7714 := hb (x (-2) 11)
                have b7715 := hb (x (-1) 10)
                have b7716 := hb (x 8 5)
                have b7717 := hb (x 9 4)
                have b7718 := hb (x 7 2 && x 7 6)
                have b7719 := hb (x 6 3 && x 6 7)
                have b7720 := hb (x 5 4 && x 5 8)
                have b7721 := hb (x 4 5 && x 4 9)
                have b7722 := hb (x 3 6 && x 3 10)
                have b7723 := hb (x 2 7 && x 2 11)
                have b7724 := hb (x 1 8 && x 1 12)
                have b7725 := hb (x 0 9 && x 0 13)
                clear * - r7711 e7712 e7713 b7714 b7715 b7716 b7717 b7718 b7719 b7720 b7721 b7722 b7723 b7724 b7725 d7674 d7694 d7706 d6505 d6525 d6545 d6565 g38 g39 d6315 d6477
                omega
              have d7726 : (x 7 6).toNat = 1 := by
                have r7727 := hand2 (x 7 2) (x 7 6)
                have b7728 := hb (x 7 6)
                have b7729 := hb (x 7 2 && x 7 6)
                clear * - r7727 b7728 b7729 d7710
                omega
              have d7730 : (x 13 8).toNat = 0 := by
                have r7731 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := hd8 13
                have e7732 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                have e7733 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                have e7734 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                have e7735 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                have e7736 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                have e7737 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                have b7738 := hb (x 6 7)
                have b7739 := hb (x 7 6)
                have b7740 := hb (x 8 5)
                have b7741 := hb (x 9 4)
                have b7742 := hb (x 10 11)
                have b7743 := hb (x 11 10)
                have b7744 := hb (x 12 9)
                have b7745 := hb (x 13 8)
                clear * - r7731 e7732 e7733 e7734 e7735 e7736 e7737 b7738 b7739 b7740 b7741 b7742 b7743 b7744 b7745 d7674 d7694 d7726
                omega
              have d7746 : (x 12 9).toNat = 0 := by
                have r7747 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := hd8 13
                have e7748 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                have e7749 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                have e7750 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                have e7751 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                have e7752 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                have e7753 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                have b7754 := hb (x 6 7)
                have b7755 := hb (x 7 6)
                have b7756 := hb (x 8 5)
                have b7757 := hb (x 9 4)
                have b7758 := hb (x 10 11)
                have b7759 := hb (x 11 10)
                have b7760 := hb (x 12 9)
                have b7761 := hb (x 13 8)
                clear * - r7747 e7748 e7749 e7750 e7751 e7752 e7753 b7754 b7755 b7756 b7757 b7758 b7759 b7760 b7761 d7730 d7674 d7694 d7726
                omega
              have d7762 : (x 11 10).toNat = 0 := by
                have r7763 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := hd8 13
                have e7764 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                have e7765 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                have e7766 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                have e7767 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                have e7768 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                have e7769 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                have b7770 := hb (x 6 7)
                have b7771 := hb (x 7 6)
                have b7772 := hb (x 8 5)
                have b7773 := hb (x 9 4)
                have b7774 := hb (x 10 11)
                have b7775 := hb (x 11 10)
                have b7776 := hb (x 12 9)
                have b7777 := hb (x 13 8)
                clear * - r7763 e7764 e7765 e7766 e7767 e7768 e7769 b7770 b7771 b7772 b7773 b7774 b7775 b7776 b7777 d7730 d7746 d7674 d7694 d7726
                omega
              have d7778 : (x 10 11).toNat = 0 := by
                have r7779 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := hd8 13
                have e7780 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                have e7781 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                have e7782 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                have e7783 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                have e7784 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                have e7785 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                have b7786 := hb (x 6 7)
                have b7787 := hb (x 7 6)
                have b7788 := hb (x 8 5)
                have b7789 := hb (x 9 4)
                have b7790 := hb (x 10 11)
                have b7791 := hb (x 11 10)
                have b7792 := hb (x 12 9)
                have b7793 := hb (x 13 8)
                clear * - r7779 e7780 e7781 e7782 e7783 e7784 e7785 b7786 b7787 b7788 b7789 b7790 b7791 b7792 b7793 d7730 d7746 d7762 d7674 d7694 d7726
                omega
              have d7794 : (x 10 1 && x 10 11).toNat = 0 := by
                have r7795 := hand2 (x 10 1) (x 10 11)
                have b7796 := hb (x 10 11)
                have b7797 := hb (x 10 1 && x 10 11)
                clear * - r7795 b7796 b7797 d7778
                omega
              have d7798 : (x 7 4 && x 7 14).toNat = 1 := by
                have r7799 : 1 ≤ (x 11 10).toNat + (x 10 1 && x 10 11).toNat + (x 9 2 && x 9 12).toNat + (x 8 3 && x 8 13).toNat + (x 7 4 && x 7 14).toNat + (x 6 5).toNat := hcov10 11
                have b7800 := hb (x 6 5)
                have b7801 := hb (x 11 10)
                have b7802 := hb (x 10 1 && x 10 11)
                have b7803 := hb (x 9 2 && x 9 12)
                have b7804 := hb (x 8 3 && x 8 13)
                have b7805 := hb (x 7 4 && x 7 14)
                clear * - r7799 b7800 b7801 b7802 b7803 b7804 b7805 d7762 d7794 d7670 d7690 d7654
                omega
              have d7806 : (x 7 4).toNat = 1 := by
                have r7807 := hand1 (x 7 4) (x 7 14)
                have b7808 := hb (x 7 4)
                have b7809 := hb (x 7 4 && x 7 14)
                clear * - r7807 b7808 b7809 d7798
                omega
              have d7810 : (x 7 12).toNat = 1 := by
                have r7811 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
                have b7812 := hb (x 7 4)
                have b7813 := hb (x 7 12)
                clear * - r7811 b7812 b7813 d7806
                omega
              have d7814 : (x 5 2).toNat = 0 := by
                have r7815 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
                have e7816 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                have e7817 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                have b7818 := hb (x 4 3)
                have b7819 := hb (x 5 2)
                have b7820 := hb (x 6 13)
                have b7821 := hb (x 7 12)
                clear * - r7815 e7816 e7817 b7818 b7819 b7820 b7821 d7810 d7650
                omega
              have d7822 : (x 5 2 && x 5 11).toNat = 0 := by
                have r7823 := hand1 (x 5 2) (x 5 11)
                have b7824 := hb (x 5 2)
                have b7825 := hb (x 5 2 && x 5 11)
                clear * - r7823 b7824 b7825 d7814
                omega
              have d7826 : (x 7 9).toNat = 1 := by
                have r7827 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := hcov9 7
                have b7828 := hb (x 1 6)
                have b7829 := hb (x 7 9)
                have b7830 := hb (x 6 1 && x 6 10)
                have b7831 := hb (x 5 2 && x 5 11)
                have b7832 := hb (x 4 3 && x 4 12)
                have b7833 := hb (x 3 4 && x 3 13)
                have b7834 := hb (x 2 5 && x 2 14)
                clear * - r7827 b7828 b7829 b7830 b7831 b7832 b7833 b7834 d7646 d7822 g66 g67 d6397 f7417
                omega
              have d7835 : (x 8 8).toNat = 0 := by
                have r7836 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
                have e7837 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e7838 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e7839 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e7840 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e7841 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e7842 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b7843 := hb (x 1 7)
                have b7844 := hb (x 2 6)
                have b7845 := hb (x 3 5)
                have b7846 := hb (x 4 4)
                have b7847 := hb (x 5 11)
                have b7848 := hb (x 6 10)
                have b7849 := hb (x 7 9)
                have b7850 := hb (x 8 8)
                clear * - r7836 e7837 e7838 e7839 e7840 e7841 e7842 b7843 b7844 b7845 b7846 b7847 b7848 b7849 b7850 d7826 g27 g25 d6421 f7427
                omega
              have d7851 : (x 6 10).toNat = 0 := by
                have r7852 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
                have e7853 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e7854 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e7855 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e7856 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e7857 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e7858 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b7859 := hb (x 1 7)
                have b7860 := hb (x 2 6)
                have b7861 := hb (x 3 5)
                have b7862 := hb (x 4 4)
                have b7863 := hb (x 5 11)
                have b7864 := hb (x 6 10)
                have b7865 := hb (x 7 9)
                have b7866 := hb (x 8 8)
                clear * - r7852 e7853 e7854 e7855 e7856 e7857 e7858 b7859 b7860 b7861 b7862 b7863 b7864 b7865 b7866 d7835 d7826 g27 g25 d6421 f7427
                omega
              have d7867 : (x 5 11).toNat = 0 := by
                have r7868 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
                have e7869 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e7870 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e7871 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e7872 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e7873 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e7874 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b7875 := hb (x 1 7)
                have b7876 := hb (x 2 6)
                have b7877 := hb (x 3 5)
                have b7878 := hb (x 4 4)
                have b7879 := hb (x 5 11)
                have b7880 := hb (x 6 10)
                have b7881 := hb (x 7 9)
                have b7882 := hb (x 8 8)
                clear * - r7868 e7869 e7870 e7871 e7872 e7873 e7874 b7875 b7876 b7877 b7878 b7879 b7880 b7881 b7882 d7835 d7826 d7851 g27 g25 d6421 f7427
                omega
              have d7883 : (x 5 10).toNat = 0 := by
                have r7884 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
                have b7885 := hb (x 5 2)
                have b7886 := hb (x 5 10)
                clear * - r7884 b7885 b7886 d7814
                omega
              have d7887 : (x 7 13).toNat = 1 := by
                have r7888 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
                have b7889 := hb (x 5 2)
                have b7890 := hb (x 7 13)
                have b7891 := hb (x 6 1 && x 6 14)
                clear * - r7888 b7889 b7890 b7891 d7642 d7814
                omega
              have d7892 : (x 8 12).toNat = 0 := by
                have r7893 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
                have e7894 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                have e7895 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                have b7896 := hb (x 5 3)
                have b7897 := hb (x 6 2)
                have b7898 := hb (x 7 13)
                have b7899 := hb (x 8 12)
                clear * - r7893 e7894 e7895 b7896 b7897 b7898 b7899 d7887
                omega
              have d7900 : (x 6 2).toNat = 0 := by
                have r7901 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
                have e7902 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                have e7903 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                have b7904 := hb (x 5 3)
                have b7905 := hb (x 6 2)
                have b7906 := hb (x 7 13)
                have b7907 := hb (x 8 12)
                clear * - r7901 e7902 e7903 b7904 b7905 b7906 b7907 d7892 d7887
                omega
              have d7908 : (x 6 2 && x 6 12).toNat = 0 := by
                have r7909 := hand1 (x 6 2) (x 6 12)
                have b7910 := hb (x 6 2)
                have b7911 := hb (x 6 2 && x 6 12)
                clear * - r7909 b7910 b7911 d7900
                omega
              have d7912 : (x 5 3).toNat = 0 := by
                have r7913 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
                have e7914 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                have e7915 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                have b7916 := hb (x 5 3)
                have b7917 := hb (x 6 2)
                have b7918 := hb (x 7 13)
                have b7919 := hb (x 8 12)
                clear * - r7913 e7914 e7915 b7916 b7917 b7918 b7919 d7892 d7887 d7900
                omega
              have d7920 : (x 5 3 && x 5 13).toNat = 0 := by
                have r7921 := hand1 (x 5 3) (x 5 13)
                have b7922 := hb (x 5 3)
                have b7923 := hb (x 5 3 && x 5 13)
                clear * - r7921 b7922 b7923 d7912
                omega
              have d7924 : (x 7 1 && x 7 11).toNat = 1 := by
                have r7925 : 1 ≤ (x 8 10).toNat + (x 7 1 && x 7 11).toNat + (x 6 2 && x 6 12).toNat + (x 5 3 && x 5 13).toNat + (x 4 4 && x 4 14).toNat + (x 3 5).toNat := hcov10 8
                have b7926 := hb (x 3 5)
                have b7927 := hb (x 8 10)
                have b7928 := hb (x 7 1 && x 7 11)
                have b7929 := hb (x 6 2 && x 6 12)
                have b7930 := hb (x 5 3 && x 5 13)
                have b7931 := hb (x 4 4 && x 4 14)
                clear * - r7925 b7926 b7927 b7928 b7929 b7930 b7931 d7613 d7908 d7920 g76 g25
                omega
              have d7932 : (x 7 11).toNat = 1 := by
                have r7933 := hand2 (x 7 1) (x 7 11)
                have b7934 := hb (x 7 11)
                have b7935 := hb (x 7 1 && x 7 11)
                clear * - r7933 b7934 b7935 d7924
                omega
              have d7936 : (x 7 3).toNat = 1 := by
                have r7937 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
                have b7938 := hb (x 7 3)
                have b7939 := hb (x 7 11)
                clear * - r7937 b7938 b7939 d7932
                omega
              have d7940 : (x 10 12).toNat = 0 := by
                have r7941 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
                have e7942 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                have e7943 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                have b7944 := hb (x 7 3)
                have b7945 := hb (x 8 2)
                have b7946 := hb (x 9 13)
                have b7947 := hb (x 10 12)
                clear * - r7941 e7942 e7943 b7944 b7945 b7946 b7947 d7609 d7936
                omega
              have d7948 : (x 10 12 && x 10 13).toNat = 0 := by
                have r7949 := hand1 (x 10 12) (x 10 13)
                have b7950 := hb (x 10 12)
                have b7951 := hb (x 10 12 && x 10 13)
                clear * - r7949 b7950 b7951 d7940
                omega
              have d7952 : (x 9 13).toNat = 0 := by
                have r7953 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
                have e7954 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                have e7955 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                have b7956 := hb (x 7 3)
                have b7957 := hb (x 8 2)
                have b7958 := hb (x 9 13)
                have b7959 := hb (x 10 12)
                clear * - r7953 e7954 e7955 b7956 b7957 b7958 b7959 d7940 d7609 d7936
                omega
              have d7960 : (x 9 13 && x 9 14).toNat = 0 := by
                have r7961 := hand1 (x 9 13) (x 9 14)
                have b7962 := hb (x 9 13)
                have b7963 := hb (x 9 13 && x 9 14)
                clear * - r7961 b7962 b7963 d7952
                omega
              have d7964 : (x 4 3).toNat = 0 := by
                have r7965 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
                have e7966 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                have e7967 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                have b7968 := hb (x 4 3)
                have b7969 := hb (x 5 2)
                have b7970 := hb (x 6 13)
                have b7971 := hb (x 7 12)
                clear * - r7965 e7966 e7967 b7968 b7969 b7970 b7971 d7810 d7650 d7814
                omega
              have d7972 : (x 4 11).toNat = 0 := by
                have r7973 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
                have b7974 := hb (x 4 3)
                have b7975 := hb (x 4 11)
                clear * - r7973 b7974 b7975 d7964
                omega
              have d7976 : (x 7 8).toNat = 1 := by
                have r7977 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
                have e7978 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
                have e7979 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
                have e7980 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
                have e7981 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
                have e7982 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
                have e7983 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
                have b7984 := hb (x 0 7)
                have b7985 := hb (x 1 6)
                have b7986 := hb (x 2 5)
                have b7987 := hb (x 3 4)
                have b7988 := hb (x 4 11)
                have b7989 := hb (x 5 10)
                have b7990 := hb (x 6 9)
                have b7991 := hb (x 7 8)
                clear * - r7977 e7978 e7979 e7980 e7981 e7982 e7983 b7984 b7985 b7986 b7987 b7988 b7989 b7990 b7991 d7658 d7883 d7972 d6357 d6393 f7417 g12
                omega
              have d7992 : (x 6 7).toNat = 0 := by
                have r7993 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := hd8 13
                have e7994 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                have e7995 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                have e7996 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                have e7997 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                have e7998 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                have e7999 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                have b8000 := hb (x 6 7)
                have b8001 := hb (x 7 6)
                have b8002 := hb (x 8 5)
                have b8003 := hb (x 9 4)
                have b8004 := hb (x 10 11)
                have b8005 := hb (x 11 10)
                have b8006 := hb (x 12 9)
                have b8007 := hb (x 13 8)
                clear * - r7993 e7994 e7995 e7996 e7997 e7998 e7999 b8000 b8001 b8002 b8003 b8004 b8005 b8006 b8007 d7730 d7746 d7762 d7778 d7674 d7694 d7726
                omega
              have d8008 : (x 13 1).toNat = 0 := by
                have r8009 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := hcount 14
                have b8010 := hb (x 0 14)
                have b8011 := hb (x 1 13)
                have b8012 := hb (x 2 12)
                have b8013 := hb (x 3 11)
                have b8014 := hb (x 4 10)
                have b8015 := hb (x 5 9)
                have b8016 := hb (x 6 8)
                have b8017 := hb (x 7 7)
                have b8018 := hb (x 8 6)
                have b8019 := hb (x 9 5)
                have b8020 := hb (x 10 4)
                have b8021 := hb (x 11 3)
                have b8022 := hb (x 12 2)
                have b8023 := hb (x 13 1)
                clear * - r8009 b8010 b8011 b8012 b8013 b8014 b8015 b8016 b8017 b8018 b8019 b8020 b8021 b8022 b8023 d7525 d7549 d7569 d7434 d7316 d7344 d7372 d7396 d6429 d6319 g19
                omega
              have d8024 : (x 13 1 && x 13 14).toNat = 0 := by
                have r8025 := hand1 (x 13 1) (x 13 14)
                have b8026 := hb (x 13 1)
                have b8027 := hb (x 13 1 && x 13 14)
                clear * - r8025 b8026 b8027 d8008
                omega
              have d8028 : (x 13 1 && x 13 11).toNat = 0 := by
                have r8029 := hand1 (x 13 1) (x 13 11)
                have b8030 := hb (x 13 1)
                have b8031 := hb (x 13 1 && x 13 11)
                clear * - r8029 b8030 b8031 d8008
                omega
              have d8032 : (x 13 1 && x 13 10).toNat = 0 := by
                have r8033 := hand1 (x 13 1) (x 13 10)
                have b8034 := hb (x 13 1)
                have b8035 := hb (x 13 1 && x 13 10)
                clear * - r8033 b8034 b8035 d8008
                omega
              have d8036 : (x 13 13).toNat = 0 := by
                have r8037 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
                have b8038 := hb (x 13 1)
                have b8039 := hb (x 13 13)
                clear * - r8037 b8038 b8039 d8008
                omega
              have d8040 : (x 12 2).toNat = 0 := by
                have r8041 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := hcount 14
                have b8042 := hb (x 0 14)
                have b8043 := hb (x 1 13)
                have b8044 := hb (x 2 12)
                have b8045 := hb (x 3 11)
                have b8046 := hb (x 4 10)
                have b8047 := hb (x 5 9)
                have b8048 := hb (x 6 8)
                have b8049 := hb (x 7 7)
                have b8050 := hb (x 8 6)
                have b8051 := hb (x 9 5)
                have b8052 := hb (x 10 4)
                have b8053 := hb (x 11 3)
                have b8054 := hb (x 12 2)
                have b8055 := hb (x 13 1)
                clear * - r8041 b8042 b8043 b8044 b8045 b8046 b8047 b8048 b8049 b8050 b8051 b8052 b8053 b8054 b8055 d8008 d7525 d7549 d7569 d7434 d7316 d7344 d7372 d7396 d6429 d6319 g19
                omega
              have d8056 : (x 12 2 && x 12 12).toNat = 0 := by
                have r8057 := hand1 (x 12 2) (x 12 12)
                have b8058 := hb (x 12 2)
                have b8059 := hb (x 12 2 && x 12 12)
                clear * - r8057 b8058 b8059 d8040
                omega
              have d8060 : (x 12 2 && x 12 11).toNat = 0 := by
                have r8061 := hand1 (x 12 2) (x 12 11)
                have b8062 := hb (x 12 2)
                have b8063 := hb (x 12 2 && x 12 11)
                clear * - r8061 b8062 b8063 d8040
                omega
              have d8064 : (x 14 13).toNat = 1 := by
                have r8065 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
                have b8066 := hb (x 12 2)
                have b8067 := hb (x 14 13)
                have b8068 := hb (x 13 1 && x 13 14)
                clear * - r8065 b8066 b8067 b8068 d8024 d8040
                omega
              have d8069 : (x 14 1).toNat = 1 := by
                have r8070 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
                have b8071 := hb (x 14 1)
                have b8072 := hb (x 14 13)
                clear * - r8070 b8071 b8072 d8064
                omega
              have d8073 : (x 15 14).toNat = 0 := by
                have r8074 : (x 15 14).toNat + (x 14 1).toNat = 1 := hd14 15
                have b8075 := hb (x 14 1)
                have b8076 := hb (x 15 14)
                clear * - r8074 b8075 b8076 d8069
                omega
              have d8077 : (x 15 1 && x 15 14).toNat = 0 := by
                have r8078 := hand2 (x 15 1) (x 15 14)
                have b8079 := hb (x 15 14)
                have b8080 := hb (x 15 1 && x 15 14)
                clear * - r8078 b8079 b8080 d8073
                omega
              have d8081 : (x 15 2).toNat = 0 := by
                have r8082 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
                have b8083 := hb (x 15 2)
                have b8084 := hb (x 15 14)
                clear * - r8082 b8083 b8084 d8073
                omega
              have d8085 : (x 15 10).toNat = 0 := by
                have r8086 : (x 15 10).toNat ≤ (x 15 2).toNat := himp _ _ (hp10 15)
                have b8087 := hb (x 15 2)
                have b8088 := hb (x 15 10)
                clear * - r8086 b8087 b8088 d8081
                omega
              have d8089 : (x 13 2).toNat = 0 := by
                have r8090 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := hcount 15
                have b8091 := hb (x 1 14)
                have b8092 := hb (x 2 13)
                have b8093 := hb (x 3 12)
                have b8094 := hb (x 4 11)
                have b8095 := hb (x 5 10)
                have b8096 := hb (x 6 9)
                have b8097 := hb (x 7 8)
                have b8098 := hb (x 8 7)
                have b8099 := hb (x 9 6)
                have b8100 := hb (x 10 5)
                have b8101 := hb (x 11 4)
                have b8102 := hb (x 12 3)
                have b8103 := hb (x 13 2)
                have b8104 := hb (x 14 1)
                clear * - r8090 b8091 b8092 b8093 b8094 b8095 b8096 b8097 b8098 b8099 b8100 b8101 b8102 b8103 b8104 d8069 d7976 d7658 d7883 d7972 d6341 d6373 g22
                omega
              have d8105 : (x 13 2 && x 13 12).toNat = 0 := by
                have r8106 := hand1 (x 13 2) (x 13 12)
                have b8107 := hb (x 13 2)
                have b8108 := hb (x 13 2 && x 13 12)
                clear * - r8106 b8107 b8108 d8089
                omega
              have d8109 : (x 13 10).toNat = 0 := by
                have r8110 : (x 13 10).toNat ≤ (x 13 2).toNat := himp _ _ (hp10 13)
                have b8111 := hb (x 13 2)
                have b8112 := hb (x 13 10)
                clear * - r8110 b8111 b8112 d8089
                omega
              have d8113 : (x 12 3).toNat = 0 := by
                have r8114 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := hcount 15
                have b8115 := hb (x 1 14)
                have b8116 := hb (x 2 13)
                have b8117 := hb (x 3 12)
                have b8118 := hb (x 4 11)
                have b8119 := hb (x 5 10)
                have b8120 := hb (x 6 9)
                have b8121 := hb (x 7 8)
                have b8122 := hb (x 8 7)
                have b8123 := hb (x 9 6)
                have b8124 := hb (x 10 5)
                have b8125 := hb (x 11 4)
                have b8126 := hb (x 12 3)
                have b8127 := hb (x 13 2)
                have b8128 := hb (x 14 1)
                clear * - r8114 b8115 b8116 b8117 b8118 b8119 b8120 b8121 b8122 b8123 b8124 b8125 b8126 b8127 b8128 d8069 d8089 d7976 d7658 d7883 d7972 d6341 d6373 g22
                omega
              have d8129 : (x 12 3 && x 12 13).toNat = 0 := by
                have r8130 := hand1 (x 12 3) (x 12 13)
                have b8131 := hb (x 12 3)
                have b8132 := hb (x 12 3 && x 12 13)
                clear * - r8130 b8131 b8132 d8113
                omega
              have d8133 : (x 12 11).toNat = 0 := by
                have r8134 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
                have b8135 := hb (x 12 3)
                have b8136 := hb (x 12 11)
                clear * - r8134 b8135 b8136 d8113
                omega
              have d8137 : (x 12 1 && x 12 11).toNat = 0 := by
                have r8138 := hand2 (x 12 1) (x 12 11)
                have b8139 := hb (x 12 11)
                have b8140 := hb (x 12 1 && x 12 11)
                clear * - r8138 b8139 b8140 d8133
                omega
              have d8141 : (x 11 4).toNat = 0 := by
                have r8142 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := hcount 15
                have b8143 := hb (x 1 14)
                have b8144 := hb (x 2 13)
                have b8145 := hb (x 3 12)
                have b8146 := hb (x 4 11)
                have b8147 := hb (x 5 10)
                have b8148 := hb (x 6 9)
                have b8149 := hb (x 7 8)
                have b8150 := hb (x 8 7)
                have b8151 := hb (x 9 6)
                have b8152 := hb (x 10 5)
                have b8153 := hb (x 11 4)
                have b8154 := hb (x 12 3)
                have b8155 := hb (x 13 2)
                have b8156 := hb (x 14 1)
                clear * - r8142 b8143 b8144 b8145 b8146 b8147 b8148 b8149 b8150 b8151 b8152 b8153 b8154 b8155 b8156 d8069 d8089 d8113 d7976 d7658 d7883 d7972 d6341 d6373 g22
                omega
              have d8157 : (x 11 4 && x 11 14).toNat = 0 := by
                have r8158 := hand1 (x 11 4) (x 11 14)
                have b8159 := hb (x 11 4)
                have b8160 := hb (x 11 4 && x 11 14)
                clear * - r8158 b8159 b8160 d8141
                omega
              have d8161 : (x 10 5).toNat = 0 := by
                have r8162 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := hcount 15
                have b8163 := hb (x 1 14)
                have b8164 := hb (x 2 13)
                have b8165 := hb (x 3 12)
                have b8166 := hb (x 4 11)
                have b8167 := hb (x 5 10)
                have b8168 := hb (x 6 9)
                have b8169 := hb (x 7 8)
                have b8170 := hb (x 8 7)
                have b8171 := hb (x 9 6)
                have b8172 := hb (x 10 5)
                have b8173 := hb (x 11 4)
                have b8174 := hb (x 12 3)
                have b8175 := hb (x 13 2)
                have b8176 := hb (x 14 1)
                clear * - r8162 b8163 b8164 b8165 b8166 b8167 b8168 b8169 b8170 b8171 b8172 b8173 b8174 b8175 b8176 d8069 d8089 d8113 d8141 d7976 d7658 d7883 d7972 d6341 d6373 g22
                omega
              have d8177 : (x 14 1 && x 14 11).toNat = 1 := by
                have r8178 : 1 ≤ (x 15 10).toNat + (x 14 1 && x 14 11).toNat + (x 13 2 && x 13 12).toNat + (x 12 3 && x 12 13).toNat + (x 11 4 && x 11 14).toNat + (x 10 5).toNat := hcov10 15
                have b8179 := hb (x 10 5)
                have b8180 := hb (x 15 10)
                have b8181 := hb (x 14 1 && x 14 11)
                have b8182 := hb (x 13 2 && x 13 12)
                have b8183 := hb (x 12 3 && x 12 13)
                have b8184 := hb (x 11 4 && x 11 14)
                clear * - r8178 b8179 b8180 b8181 b8182 b8183 b8184 d8085 d8105 d8129 d8157 d8161
                omega
              have d8185 : (x 14 11).toNat = 1 := by
                have r8186 := hand2 (x 14 1) (x 14 11)
                have b8187 := hb (x 14 11)
                have b8188 := hb (x 14 1 && x 14 11)
                clear * - r8186 b8187 b8188 d8177
                omega
              have d8189 : (x 14 3).toNat = 1 := by
                have r8190 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
                have b8191 := hb (x 14 3)
                have b8192 := hb (x 14 11)
                clear * - r8190 b8191 b8192 d8185
                omega
              have d8193 : (x 17 12).toNat = 0 := by
                have r8194 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
                have e8195 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                have e8196 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                have b8197 := hb (x 14 3)
                have b8198 := hb (x 15 2)
                have b8199 := hb (x 16 13)
                have b8200 := hb (x 17 12)
                clear * - r8194 e8195 e8196 b8197 b8198 b8199 b8200 d8081 d8189
                omega
              have d8201 : (x 16 13).toNat = 0 := by
                have r8202 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
                have e8203 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                have e8204 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                have b8205 := hb (x 14 3)
                have b8206 := hb (x 15 2)
                have b8207 := hb (x 16 13)
                have b8208 := hb (x 17 12)
                clear * - r8202 e8203 e8204 b8205 b8206 b8207 b8208 d8193 d8081 d8189
                omega
              have d8209 : (x 14 2).toNat = 1 := by
                have r8210 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := hcov13 16
                have b8211 := hb (x 14 2)
                have b8212 := hb (x 16 13)
                have b8213 := hb (x 15 1 && x 15 14)
                clear * - r8210 b8211 b8212 b8213 d8201 d8077
                omega
              have d8214 : (x 16 12).toNat = 0 := by
                have r8215 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
                have e8216 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                have e8217 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                have b8218 := hb (x 13 3)
                have b8219 := hb (x 14 2)
                have b8220 := hb (x 15 13)
                have b8221 := hb (x 16 12)
                clear * - r8215 e8216 e8217 b8218 b8219 b8220 b8221 d8209
                omega
              have d8222 : (x 15 13).toNat = 0 := by
                have r8223 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
                have e8224 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                have e8225 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                have b8226 := hb (x 13 3)
                have b8227 := hb (x 14 2)
                have b8228 := hb (x 15 13)
                have b8229 := hb (x 16 12)
                clear * - r8223 e8224 e8225 b8226 b8227 b8228 b8229 d8214 d8209
                omega
              have d8230 : (x 13 3).toNat = 0 := by
                have r8231 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
                have e8232 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                have e8233 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                have b8234 := hb (x 13 3)
                have b8235 := hb (x 14 2)
                have b8236 := hb (x 15 13)
                have b8237 := hb (x 16 12)
                clear * - r8231 e8232 e8233 b8234 b8235 b8236 b8237 d8214 d8222 d8209
                omega
              have d8238 : (x 13 11).toNat = 0 := by
                have r8239 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
                have b8240 := hb (x 13 3)
                have b8241 := hb (x 13 11)
                clear * - r8239 b8240 b8241 d8230
                omega
              have d8242 : (x 9 6).toNat = 0 := by
                have r8243 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := hcount 15
                have b8244 := hb (x 1 14)
                have b8245 := hb (x 2 13)
                have b8246 := hb (x 3 12)
                have b8247 := hb (x 4 11)
                have b8248 := hb (x 5 10)
                have b8249 := hb (x 6 9)
                have b8250 := hb (x 7 8)
                have b8251 := hb (x 8 7)
                have b8252 := hb (x 9 6)
                have b8253 := hb (x 10 5)
                have b8254 := hb (x 11 4)
                have b8255 := hb (x 12 3)
                have b8256 := hb (x 13 2)
                have b8257 := hb (x 14 1)
                clear * - r8243 b8244 b8245 b8246 b8247 b8248 b8249 b8250 b8251 b8252 b8253 b8254 b8255 b8256 b8257 d8069 d8089 d8113 d8141 d8161 d7976 d7658 d7883 d7972 d6341 d6373 g22
                omega
              have d8258 : (x 8 7).toNat = 0 := by
                have r8259 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := hcount 15
                have b8260 := hb (x 1 14)
                have b8261 := hb (x 2 13)
                have b8262 := hb (x 3 12)
                have b8263 := hb (x 4 11)
                have b8264 := hb (x 5 10)
                have b8265 := hb (x 6 9)
                have b8266 := hb (x 7 8)
                have b8267 := hb (x 8 7)
                have b8268 := hb (x 9 6)
                have b8269 := hb (x 10 5)
                have b8270 := hb (x 11 4)
                have b8271 := hb (x 12 3)
                have b8272 := hb (x 13 2)
                have b8273 := hb (x 14 1)
                clear * - r8259 b8260 b8261 b8262 b8263 b8264 b8265 b8266 b8267 b8268 b8269 b8270 b8271 b8272 b8273 d8069 d8089 d8113 d8141 d8161 d8242 d7976 d7658 d7883 d7972 d6341 d6373 g22
                omega
              have d8274 : (x 11 3).toNat = 0 := by
                have r8275 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := hcount 14
                have b8276 := hb (x 0 14)
                have b8277 := hb (x 1 13)
                have b8278 := hb (x 2 12)
                have b8279 := hb (x 3 11)
                have b8280 := hb (x 4 10)
                have b8281 := hb (x 5 9)
                have b8282 := hb (x 6 8)
                have b8283 := hb (x 7 7)
                have b8284 := hb (x 8 6)
                have b8285 := hb (x 9 5)
                have b8286 := hb (x 10 4)
                have b8287 := hb (x 11 3)
                have b8288 := hb (x 12 2)
                have b8289 := hb (x 13 1)
                clear * - r8275 b8276 b8277 b8278 b8279 b8280 b8281 b8282 b8283 b8284 b8285 b8286 b8287 b8288 b8289 d8008 d8040 d7525 d7549 d7569 d7434 d7316 d7344 d7372 d7396 d6429 d6319 g19
                omega
              have d8290 : (x 11 3 && x 11 13).toNat = 0 := by
                have r8291 := hand1 (x 11 3) (x 11 13)
                have b8292 := hb (x 11 3)
                have b8293 := hb (x 11 3 && x 11 13)
                clear * - r8291 b8292 b8293 d8274
                omega
              have d8294 : (x 14 10).toNat = 1 := by
                have r8295 : 1 ≤ (x 14 10).toNat + (x 13 1 && x 13 11).toNat + (x 12 2 && x 12 12).toNat + (x 11 3 && x 11 13).toNat + (x 10 4 && x 10 14).toNat + (x 9 5).toNat := hcov10 14
                have b8296 := hb (x 9 5)
                have b8297 := hb (x 14 10)
                have b8298 := hb (x 13 1 && x 13 11)
                have b8299 := hb (x 12 2 && x 12 12)
                have b8300 := hb (x 11 3 && x 11 13)
                have b8301 := hb (x 10 4 && x 10 14)
                clear * - r8295 b8296 b8297 b8298 b8299 b8300 b8301 d8028 d8056 d8290 d7541 d7549
                omega
              have d8302 : (x 16 8).toNat = 0 := by
                have r8303 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := hd8 16
                have e8304 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
                have e8305 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
                have e8306 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
                have e8307 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
                have e8308 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
                have e8309 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
                have b8310 := hb (x 9 7)
                have b8311 := hb (x 10 6)
                have b8312 := hb (x 11 5)
                have b8313 := hb (x 12 4)
                have b8314 := hb (x 13 11)
                have b8315 := hb (x 14 10)
                have b8316 := hb (x 15 9)
                have b8317 := hb (x 16 8)
                clear * - r8303 e8304 e8305 e8306 e8307 e8308 e8309 b8310 b8311 b8312 b8313 b8314 b8315 b8316 b8317 d8294 d8238
                omega
              have d8318 : (x 15 9).toNat = 0 := by
                have r8319 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := hd8 16
                have e8320 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
                have e8321 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
                have e8322 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
                have e8323 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
                have e8324 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
                have e8325 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
                have b8326 := hb (x 9 7)
                have b8327 := hb (x 10 6)
                have b8328 := hb (x 11 5)
                have b8329 := hb (x 12 4)
                have b8330 := hb (x 13 11)
                have b8331 := hb (x 14 10)
                have b8332 := hb (x 15 9)
                have b8333 := hb (x 16 8)
                clear * - r8319 e8320 e8321 e8322 e8323 e8324 e8325 b8326 b8327 b8328 b8329 b8330 b8331 b8332 b8333 d8302 d8294 d8238
                omega
              have d8334 : (x 12 4).toNat = 0 := by
                have r8335 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := hd8 16
                have e8336 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
                have e8337 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
                have e8338 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
                have e8339 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
                have e8340 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
                have e8341 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
                have b8342 := hb (x 9 7)
                have b8343 := hb (x 10 6)
                have b8344 := hb (x 11 5)
                have b8345 := hb (x 12 4)
                have b8346 := hb (x 13 11)
                have b8347 := hb (x 14 10)
                have b8348 := hb (x 15 9)
                have b8349 := hb (x 16 8)
                clear * - r8335 e8336 e8337 e8338 e8339 e8340 e8341 b8342 b8343 b8344 b8345 b8346 b8347 b8348 b8349 d8302 d8318 d8294 d8238
                omega
              have d8350 : (x 11 5).toNat = 0 := by
                have r8351 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := hd8 16
                have e8352 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
                have e8353 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
                have e8354 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
                have e8355 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
                have e8356 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
                have e8357 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
                have b8358 := hb (x 9 7)
                have b8359 := hb (x 10 6)
                have b8360 := hb (x 11 5)
                have b8361 := hb (x 12 4)
                have b8362 := hb (x 13 11)
                have b8363 := hb (x 14 10)
                have b8364 := hb (x 15 9)
                have b8365 := hb (x 16 8)
                clear * - r8351 e8352 e8353 e8354 e8355 e8356 e8357 b8358 b8359 b8360 b8361 b8362 b8363 b8364 b8365 d8302 d8318 d8294 d8238 d8334
                omega
              have d8366 : (x 10 6).toNat = 0 := by
                have r8367 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := hd8 16
                have e8368 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
                have e8369 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
                have e8370 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
                have e8371 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
                have e8372 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
                have e8373 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
                have b8374 := hb (x 9 7)
                have b8375 := hb (x 10 6)
                have b8376 := hb (x 11 5)
                have b8377 := hb (x 12 4)
                have b8378 := hb (x 13 11)
                have b8379 := hb (x 14 10)
                have b8380 := hb (x 15 9)
                have b8381 := hb (x 16 8)
                clear * - r8367 e8368 e8369 e8370 e8371 e8372 e8373 b8374 b8375 b8376 b8377 b8378 b8379 b8380 b8381 d8302 d8318 d8294 d8238 d8334 d8350
                omega
              have d8382 : (x 9 7).toNat = 0 := by
                have r8383 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := hd8 16
                have e8384 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
                have e8385 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
                have e8386 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
                have e8387 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
                have e8388 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
                have e8389 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
                have b8390 := hb (x 9 7)
                have b8391 := hb (x 10 6)
                have b8392 := hb (x 11 5)
                have b8393 := hb (x 12 4)
                have b8394 := hb (x 13 11)
                have b8395 := hb (x 14 10)
                have b8396 := hb (x 15 9)
                have b8397 := hb (x 16 8)
                clear * - r8383 e8384 e8385 e8386 e8387 e8388 e8389 b8390 b8391 b8392 b8393 b8394 b8395 b8396 b8397 d8302 d8318 d8294 d8238 d8334 d8350 d8366
                omega
              have d8398 : (x 15 1).toNat = 1 := by
                have r8399 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := hcount 16
                have b8400 := hb (x 2 14)
                have b8401 := hb (x 3 13)
                have b8402 := hb (x 4 12)
                have b8403 := hb (x 5 11)
                have b8404 := hb (x 6 10)
                have b8405 := hb (x 7 9)
                have b8406 := hb (x 8 8)
                have b8407 := hb (x 9 7)
                have b8408 := hb (x 10 6)
                have b8409 := hb (x 11 5)
                have b8410 := hb (x 12 4)
                have b8411 := hb (x 13 3)
                have b8412 := hb (x 14 2)
                have b8413 := hb (x 15 1)
                clear * - r8399 b8400 b8401 b8402 b8403 b8404 b8405 b8406 b8407 b8408 b8409 b8410 b8411 b8412 b8413 d8209 d8230 d8334 d8350 d8366 d8382 d7835 d7826 d7851 d7867 g28 g26 d6328
                omega
              have d8414 : (x 16 14).toNat = 0 := by
                have r8415 : (x 16 14).toNat + (x 15 1).toNat = 1 := hd14 16
                have b8416 := hb (x 15 1)
                have b8417 := hb (x 16 14)
                clear * - r8415 b8416 b8417 d8398
                omega
              have d8418 : (x 16 1 && x 16 14).toNat = 0 := by
                have r8419 := hand2 (x 16 1) (x 16 14)
                have b8420 := hb (x 16 14)
                have b8421 := hb (x 16 1 && x 16 14)
                clear * - r8419 b8420 b8421 d8414
                omega
              have d8422 : (x 17 13).toNat = 1 := by
                have r8423 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := hcov13 17
                have b8424 := hb (x 15 2)
                have b8425 := hb (x 17 13)
                have b8426 := hb (x 16 1 && x 16 14)
                clear * - r8423 b8424 b8425 b8426 d8418 d8081
                omega
              have d8427 : (x 18 12).toNat = 0 := by
                have r8428 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
                have e8429 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
                have e8430 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
                have b8431 := hb (x 15 3)
                have b8432 := hb (x 16 2)
                have b8433 := hb (x 17 13)
                have b8434 := hb (x 18 12)
                clear * - r8428 e8429 e8430 b8431 b8432 b8433 b8434 d8422
                omega
              have d8435 : (x 18 4).toNat = 0 := by
                have r8436 : (x 18 4).toNat ≤ (x 18 12).toNat := himp _ _ (hp4 18)
                have b8437 := hb (x 18 4)
                have b8438 := hb (x 18 12)
                clear * - r8436 b8437 b8438 d8427
                omega
              have d8439 : (x 18 4 && x 18 5).toNat = 0 := by
                have r8440 := hand1 (x 18 4) (x 18 5)
                have b8441 := hb (x 18 4)
                have b8442 := hb (x 18 4 && x 18 5)
                clear * - r8440 b8441 b8442 d8435
                omega
              have d8443 : (x 16 6).toNat = 0 := by
                have r8444 : (x 16 6).toNat ≤ (x 16 14).toNat := himp _ _ (hp6 16)
                have b8445 := hb (x 16 6)
                have b8446 := hb (x 16 14)
                clear * - r8444 b8445 b8446 d8414
                omega
              have d8447 : (x 16 6 && x 16 7).toNat = 0 := by
                have r8448 := hand1 (x 16 6) (x 16 7)
                have b8449 := hb (x 16 6)
                have b8450 := hb (x 16 6 && x 16 7)
                clear * - r8448 b8449 b8450 d8443
                omega
              have d8451 : (x 11 3 && x 11 12).toNat = 0 := by
                have r8452 := hand1 (x 11 3) (x 11 12)
                have b8453 := hb (x 11 3)
                have b8454 := hb (x 11 3 && x 11 12)
                clear * - r8452 b8453 b8454 d8274
                omega
              have d8455 : (x 14 9).toNat = 1 := by
                have r8456 : 1 ≤ (x 14 9).toNat + (x 13 1 && x 13 10).toNat + (x 12 2 && x 12 11).toNat + (x 11 3 && x 11 12).toNat + (x 10 4 && x 10 13).toNat + (x 9 5 && x 9 14).toNat + (x 8 6).toNat := hcov9 14
                have b8457 := hb (x 8 6)
                have b8458 := hb (x 14 9)
                have b8459 := hb (x 13 1 && x 13 10)
                have b8460 := hb (x 12 2 && x 12 11)
                have b8461 := hb (x 11 3 && x 11 12)
                have b8462 := hb (x 10 4 && x 10 13)
                have b8463 := hb (x 9 5 && x 9 14)
                clear * - r8456 b8457 b8458 b8459 b8460 b8461 b8462 b8463 d8032 d8060 d8451 d7545 d7565 d7569
                omega
              have d8464 : (x 15 8).toNat = 0 := by
                have r8465 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
                have e8466 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                have e8467 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                have e8468 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                have e8469 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                have e8470 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                have e8471 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                have b8472 := hb (x 8 7)
                have b8473 := hb (x 9 6)
                have b8474 := hb (x 10 5)
                have b8475 := hb (x 11 4)
                have b8476 := hb (x 12 11)
                have b8477 := hb (x 13 10)
                have b8478 := hb (x 14 9)
                have b8479 := hb (x 15 8)
                clear * - r8465 e8466 e8467 e8468 e8469 e8470 e8471 b8472 b8473 b8474 b8475 b8476 b8477 b8478 b8479 d8455 d8109 d8133 d8141 d8161 d8242 d8258
                omega
              have d8480 : (x 15 7 && x 15 8).toNat = 0 := by
                have r8481 := hand2 (x 15 7) (x 15 8)
                have b8482 := hb (x 15 8)
                have b8483 := hb (x 15 7 && x 15 8)
                clear * - r8481 b8482 b8483 d8464
                omega
              have r8484 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := hcount 13
              have r8485 : (x 22 1).toNat + (x 21 2).toNat + (x 20 3).toNat + (x 19 4).toNat + (x 18 5).toNat + (x 17 6).toNat + (x 16 7).toNat + (x 15 8).toNat + (x 14 9).toNat + (x 13 10).toNat + (x 12 11).toNat + (x 11 12).toNat + (x 10 13).toNat + (x 9 14).toNat = 3 := hcount 23
              have r8486 : 1 ≤ (x 22 1).toNat + (x 21 1 && x 21 2).toNat + (x 20 2 && x 20 3).toNat + (x 19 3 && x 19 4).toNat + (x 18 4 && x 18 5).toNat + (x 17 5 && x 17 6).toNat + (x 16 6 && x 16 7).toNat + (x 15 7 && x 15 8).toNat + (x 14 8 && x 14 9).toNat + (x 13 9 && x 13 10).toNat + (x 12 10 && x 12 11).toNat + (x 11 11 && x 11 12).toNat + (x 10 12 && x 10 13).toNat + (x 9 13 && x 9 14).toNat + (x 8 14).toNat := hcov1 22
              have r8487 : 1 ≤ (x 13 10).toNat + (x 12 1 && x 12 11).toNat + (x 11 2 && x 11 12).toNat + (x 10 3 && x 10 13).toNat + (x 9 4 && x 9 14).toNat + (x 8 5).toNat := hcov10 13
              have r8488 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := hcov13 10
              have r8489 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := hcov13 13
              have r8490 := hand2 (x 21 1) (x 21 2)
              have r8491 := hand2 (x 20 2) (x 20 3)
              have r8492 := hand2 (x 19 3) (x 19 4)
              have r8493 := hand2 (x 17 5) (x 17 6)
              have r8494 := hand2 (x 11 2) (x 11 12)
              have r8495 := hand1 (x 10 3) (x 10 13)
              have r8496 := hand2 (x 9 1) (x 9 14)
              have r8497 := hand1 (x 12 1) (x 12 14)
              have b8498 := hb (x (-1) 14)
              have b8499 := hb (x 0 13)
              have b8500 := hb (x 1 12)
              have b8501 := hb (x 2 11)
              have b8502 := hb (x 3 10)
              have b8503 := hb (x 4 9)
              have b8504 := hb (x 5 8)
              have b8505 := hb (x 6 7)
              have b8506 := hb (x 7 6)
              have b8507 := hb (x 8 2)
              have b8508 := hb (x 8 5)
              have b8509 := hb (x 8 14)
              have b8510 := hb (x 9 4)
              have b8511 := hb (x 9 14)
              have b8512 := hb (x 10 3)
              have b8513 := hb (x 10 13)
              have b8514 := hb (x 11 2)
              have b8515 := hb (x 11 12)
              have b8516 := hb (x 12 1)
              have b8517 := hb (x 12 11)
              have b8518 := hb (x 13 10)
              have b8519 := hb (x 13 13)
              have b8520 := hb (x 14 9)
              have b8521 := hb (x 15 8)
              have b8522 := hb (x 16 7)
              have b8523 := hb (x 17 6)
              have b8524 := hb (x 18 5)
              have b8525 := hb (x 19 4)
              have b8526 := hb (x 20 3)
              have b8527 := hb (x 21 2)
              have b8528 := hb (x 22 1)
              have b8529 := hb (x 21 1 && x 21 2)
              have b8530 := hb (x 20 2 && x 20 3)
              have b8531 := hb (x 19 3 && x 19 4)
              have b8532 := hb (x 18 4 && x 18 5)
              have b8533 := hb (x 17 5 && x 17 6)
              have b8534 := hb (x 16 6 && x 16 7)
              have b8535 := hb (x 15 7 && x 15 8)
              have b8536 := hb (x 14 8 && x 14 9)
              have b8537 := hb (x 13 9 && x 13 10)
              have b8538 := hb (x 12 10 && x 12 11)
              have b8539 := hb (x 11 11 && x 11 12)
              have b8540 := hb (x 10 12 && x 10 13)
              have b8541 := hb (x 9 13 && x 9 14)
              have b8542 := hb (x 12 1 && x 12 11)
              have b8543 := hb (x 11 2 && x 11 12)
              have b8544 := hb (x 10 3 && x 10 13)
              have b8545 := hb (x 9 4 && x 9 14)
              have b8546 := hb (x 9 1 && x 9 14)
              have b8547 := hb (x 12 1 && x 12 14)
              linarith only [r8484, r8485, r8486, r8487, r8488, r8489, r8490, r8491, r8492, r8493, r8494, r8495, r8496, r8497, b8498, b8499, b8500, b8501, b8502, b8503, b8504, b8505, b8506, b8507, b8508, b8509, b8510, b8511, b8512, b8513, b8514, b8515, b8516, b8517, b8518, b8519, b8520, b8521, b8522, b8523, b8524, b8525, b8526, b8527, b8528, b8529, b8530, b8531, b8532, b8533, b8534, b8535, b8536, b8537, b8538, b8539, b8540, b8541, b8542, b8543, b8544, b8545, b8546, b8547, g18, d6299, d6549, d6529, d6509, d6489, d7992, d7726, d7609, d7694, d7605, d7674, d8133, d8109, d8036, d8455, d8464, d8439, d8447, d8480, d7461, d7481, d7501, d7521, d7948, d7960, d8137, d7678]
            · have f8548 : (x (-1) 8).toNat = 1 := by rw [h7432]; rfl
              have d8549 : (x (-2) 9).toNat = 0 := by
                have r8550 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
                have e8551 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e8552 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e8553 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e8554 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e8555 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e8556 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have b8557 := hb (x (-8) 7)
                have b8558 := hb (x (-7) 6)
                have b8559 := hb (x (-6) 5)
                have b8560 := hb (x (-5) 4)
                have b8561 := hb (x (-4) 11)
                have b8562 := hb (x (-3) 10)
                have b8563 := hb (x (-2) 9)
                have b8564 := hb (x (-1) 8)
                clear * - r8550 e8551 e8552 e8553 e8554 e8555 e8556 b8557 b8558 b8559 b8560 b8561 b8562 b8563 b8564 f8548
                omega
              have d8565 : (x (-2) 9 && x (-2) 14).toNat = 0 := by
                have r8566 := hand1 (x (-2) 9) (x (-2) 14)
                have b8567 := hb (x (-2) 9)
                have b8568 := hb (x (-2) 9 && x (-2) 14)
                clear * - r8566 b8567 b8568 d8549
                omega
              have d8569 : (x (-3) 10).toNat = 0 := by
                have r8570 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
                have e8571 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e8572 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e8573 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e8574 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e8575 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e8576 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have b8577 := hb (x (-8) 7)
                have b8578 := hb (x (-7) 6)
                have b8579 := hb (x (-6) 5)
                have b8580 := hb (x (-5) 4)
                have b8581 := hb (x (-4) 11)
                have b8582 := hb (x (-3) 10)
                have b8583 := hb (x (-2) 9)
                have b8584 := hb (x (-1) 8)
                clear * - r8570 e8571 e8572 e8573 e8574 e8575 e8576 b8577 b8578 b8579 b8580 b8581 b8582 b8583 b8584 f8548 d8549
                omega
              have d8585 : (x (-4) 11).toNat = 0 := by
                have r8586 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
                have e8587 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e8588 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e8589 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e8590 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e8591 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e8592 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have b8593 := hb (x (-8) 7)
                have b8594 := hb (x (-7) 6)
                have b8595 := hb (x (-6) 5)
                have b8596 := hb (x (-5) 4)
                have b8597 := hb (x (-4) 11)
                have b8598 := hb (x (-3) 10)
                have b8599 := hb (x (-2) 9)
                have b8600 := hb (x (-1) 8)
                clear * - r8586 e8587 e8588 e8589 e8590 e8591 e8592 b8593 b8594 b8595 b8596 b8597 b8598 b8599 b8600 f8548 d8549 d8569
                omega
              have d8601 : (x (-5) 4).toNat = 0 := by
                have r8602 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
                have e8603 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e8604 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e8605 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e8606 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e8607 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e8608 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have b8609 := hb (x (-8) 7)
                have b8610 := hb (x (-7) 6)
                have b8611 := hb (x (-6) 5)
                have b8612 := hb (x (-5) 4)
                have b8613 := hb (x (-4) 11)
                have b8614 := hb (x (-3) 10)
                have b8615 := hb (x (-2) 9)
                have b8616 := hb (x (-1) 8)
                clear * - r8602 e8603 e8604 e8605 e8606 e8607 e8608 b8609 b8610 b8611 b8612 b8613 b8614 b8615 b8616 f8548 d8549 d8569 d8585
                omega
              have d8617 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
                have r8618 := hand1 (x (-5) 4) (x (-5) 14)
                have b8619 := hb (x (-5) 4)
                have b8620 := hb (x (-5) 4 && x (-5) 14)
                clear * - r8618 b8619 b8620 d8601
                omega
              have d8621 : (x (-6) 5).toNat = 0 := by
                have r8622 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
                have e8623 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e8624 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e8625 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e8626 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e8627 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e8628 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have b8629 := hb (x (-8) 7)
                have b8630 := hb (x (-7) 6)
                have b8631 := hb (x (-6) 5)
                have b8632 := hb (x (-5) 4)
                have b8633 := hb (x (-4) 11)
                have b8634 := hb (x (-3) 10)
                have b8635 := hb (x (-2) 9)
                have b8636 := hb (x (-1) 8)
                clear * - r8622 e8623 e8624 e8625 e8626 e8627 e8628 b8629 b8630 b8631 b8632 b8633 b8634 b8635 b8636 f8548 d8549 d8569 d8585 d8601
                omega
              have r8637 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := hcount 12
              have r8638 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := hcount 14
              have r8639 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := hd12 (-2)
              have e8640 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
              have e8641 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
              have r8642 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
              have e8643 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e8644 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have r8645 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
              have e8646 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
              have e8647 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
              have r8648 : 1 ≤ (x 7 5).toNat + (x 6 1 && x 6 6).toNat + (x 5 2 && x 5 7).toNat + (x 4 3 && x 4 8).toNat + (x 3 4 && x 3 9).toNat + (x 2 5 && x 2 10).toNat + (x 1 6 && x 1 11).toNat + (x 0 7 && x 0 12).toNat + (x (-1) 8 && x (-1) 13).toNat + (x (-2) 9 && x (-2) 14).toNat + (x (-3) 10).toNat := hcov5 7
              have r8649 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := hcov6 8
              have r8650 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := hcov10 (-1)
              have r8651 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := hcov10 2
              have r8652 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := hcov11 12
              have r8653 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := hcov13 (-2)
              have r8654 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
              have r8655 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
              have r8656 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
              have r8657 := hand2 (x 6 1) (x 6 6)
              have r8658 := hand2 (x 5 2) (x 5 7)
              have r8659 := hand2 (x 4 3) (x 4 8)
              have r8660 := hand2 (x 7 1) (x 7 7)
              have r8661 := hand1 (x (-3) 2) (x (-3) 12)
              have r8662 := hand1 (x (-4) 3) (x (-4) 13)
              have r8663 := hand2 (x 1 1) (x 1 11)
              have r8664 := hand1 (x (-2) 4) (x (-2) 14)
              have r8665 := hand1 (x 11 1) (x 11 12)
              have r8666 := hand1 (x 10 2) (x 10 13)
              have r8667 := hand1 (x 9 3) (x 9 14)
              have r8668 := hand1 (x 13 1) (x 13 14)
              have b8669 := hb (x (-6) 5)
              have b8670 := hb (x (-5) 3)
              have b8671 := hb (x (-4) 2)
              have b8672 := hb (x (-4) 3)
              have b8673 := hb (x (-3) 2)
              have b8674 := hb (x (-3) 5)
              have b8675 := hb (x (-3) 10)
              have b8676 := hb (x (-3) 13)
              have b8677 := hb (x (-2) 4)
              have b8678 := hb (x (-2) 12)
              have b8679 := hb (x (-2) 13)
              have b8680 := hb (x (-2) 14)
              have b8681 := hb (x (-1) 9)
              have b8682 := hb (x (-1) 10)
              have b8683 := hb (x (-1) 12)
              have b8684 := hb (x (-1) 13)
              have b8685 := hb (x 0 12)
              have b8686 := hb (x 0 14)
              have b8687 := hb (x 1 11)
              have b8688 := hb (x 1 13)
              have b8689 := hb (x 2 10)
              have b8690 := hb (x 2 12)
              have b8691 := hb (x 3 9)
              have b8692 := hb (x 3 11)
              have b8693 := hb (x 4 8)
              have b8694 := hb (x 4 10)
              have b8695 := hb (x 5 7)
              have b8696 := hb (x 5 9)
              have b8697 := hb (x 6 6)
              have b8698 := hb (x 6 8)
              have b8699 := hb (x 7 5)
              have b8700 := hb (x 7 7)
              have b8701 := hb (x 8 4)
              have b8702 := hb (x 8 6)
              have b8703 := hb (x 9 3)
              have b8704 := hb (x 9 5)
              have b8705 := hb (x 10 2)
              have b8706 := hb (x 10 4)
              have b8707 := hb (x 11 1)
              have b8708 := hb (x 11 3)
              have b8709 := hb (x 12 2)
              have b8710 := hb (x 12 3)
              have b8711 := hb (x 12 11)
              have b8712 := hb (x 13 1)
              have b8713 := hb (x 13 2)
              have b8714 := hb (x 14 13)
              have b8715 := hb (x 15 12)
              have b8716 := hb (x 6 1 && x 6 6)
              have b8717 := hb (x 5 2 && x 5 7)
              have b8718 := hb (x 4 3 && x 4 8)
              have b8719 := hb (x 3 4 && x 3 9)
              have b8720 := hb (x 2 5 && x 2 10)
              have b8721 := hb (x 1 6 && x 1 11)
              have b8722 := hb (x 0 7 && x 0 12)
              have b8723 := hb (x (-1) 8 && x (-1) 13)
              have b8724 := hb (x (-2) 9 && x (-2) 14)
              have b8725 := hb (x 7 1 && x 7 7)
              have b8726 := hb (x 6 2 && x 6 8)
              have b8727 := hb (x 5 3 && x 5 9)
              have b8728 := hb (x 4 4 && x 4 10)
              have b8729 := hb (x 3 5 && x 3 11)
              have b8730 := hb (x 2 6 && x 2 12)
              have b8731 := hb (x 1 7 && x 1 13)
              have b8732 := hb (x 0 8 && x 0 14)
              have b8733 := hb (x (-2) 1 && x (-2) 11)
              have b8734 := hb (x (-3) 2 && x (-3) 12)
              have b8735 := hb (x (-4) 3 && x (-4) 13)
              have b8736 := hb (x (-5) 4 && x (-5) 14)
              have b8737 := hb (x 1 1 && x 1 11)
              have b8738 := hb (x 0 2 && x 0 12)
              have b8739 := hb (x (-1) 3 && x (-1) 13)
              have b8740 := hb (x (-2) 4 && x (-2) 14)
              have b8741 := hb (x 11 1 && x 11 12)
              have b8742 := hb (x 10 2 && x 10 13)
              have b8743 := hb (x 9 3 && x 9 14)
              have b8744 := hb (x (-3) 1 && x (-3) 14)
              have b8745 := hb (x 13 1 && x 13 14)
              linarith only [r8637, r8638, r8639, e8640, e8641, r8642, e8643, e8644, r8645, e8646, e8647, r8648, r8649, r8650, r8651, r8652, r8653, r8654, r8655, r8656, r8657, r8658, r8659, r8660, r8661, r8662, r8663, r8664, r8665, r8666, r8667, r8668, b8669, b8670, b8671, b8672, b8673, b8674, b8675, b8676, b8677, b8678, b8679, b8680, b8681, b8682, b8683, b8684, b8685, b8686, b8687, b8688, b8689, b8690, b8691, b8692, b8693, b8694, b8695, b8696, b8697, b8698, b8699, b8700, b8701, b8702, b8703, b8704, b8705, b8706, b8707, b8708, b8709, b8710, b8711, b8712, b8713, b8714, b8715, b8716, b8717, b8718, b8719, b8720, b8721, b8722, b8723, b8724, b8725, b8726, b8727, b8728, b8729, b8730, b8731, b8732, b8733, b8734, b8735, b8736, b8737, b8738, b8739, b8740, b8741, b8742, b8743, b8744, b8745, d8621, g0, d8569, g3, g4, g6, d6315, g7, g17, g19, d6319, g24, d6429, d7396, d7372, d7344, d7316, d6369, g40, d7422, g41, g42, d8565, d7336, d7364, g47, g48, d6425, d7428, g49, d6481, d8617, g72, g73, g82]
          · have f8746 : (x 1 7).toNat = 1 := by rw [h7426]; rfl
            have d8747 : (x 8 8).toNat = 0 := by
              have r8748 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
              have e8749 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e8750 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e8751 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e8752 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e8753 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e8754 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b8755 := hb (x 1 7)
              have b8756 := hb (x 2 6)
              have b8757 := hb (x 3 5)
              have b8758 := hb (x 4 4)
              have b8759 := hb (x 5 11)
              have b8760 := hb (x 6 10)
              have b8761 := hb (x 7 9)
              have b8762 := hb (x 8 8)
              clear * - r8748 e8749 e8750 e8751 e8752 e8753 e8754 b8755 b8756 b8757 b8758 b8759 b8760 b8761 b8762 g27 g25 d6421 f8746
              omega
            have d8763 : (x 7 9).toNat = 0 := by
              have r8764 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
              have e8765 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e8766 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e8767 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e8768 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e8769 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e8770 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b8771 := hb (x 1 7)
              have b8772 := hb (x 2 6)
              have b8773 := hb (x 3 5)
              have b8774 := hb (x 4 4)
              have b8775 := hb (x 5 11)
              have b8776 := hb (x 6 10)
              have b8777 := hb (x 7 9)
              have b8778 := hb (x 8 8)
              clear * - r8764 e8765 e8766 e8767 e8768 e8769 e8770 b8771 b8772 b8773 b8774 b8775 b8776 b8777 b8778 d8747 g27 g25 d6421 f8746
              omega
            have d8779 : (x 6 10).toNat = 0 := by
              have r8780 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
              have e8781 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e8782 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e8783 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e8784 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e8785 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e8786 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b8787 := hb (x 1 7)
              have b8788 := hb (x 2 6)
              have b8789 := hb (x 3 5)
              have b8790 := hb (x 4 4)
              have b8791 := hb (x 5 11)
              have b8792 := hb (x 6 10)
              have b8793 := hb (x 7 9)
              have b8794 := hb (x 8 8)
              clear * - r8780 e8781 e8782 e8783 e8784 e8785 e8786 b8787 b8788 b8789 b8790 b8791 b8792 b8793 b8794 d8747 d8763 g27 g25 d6421 f8746
              omega
            have d8795 : (x 6 1 && x 6 10).toNat = 0 := by
              have r8796 := hand2 (x 6 1) (x 6 10)
              have b8797 := hb (x 6 10)
              have b8798 := hb (x 6 1 && x 6 10)
              clear * - r8796 b8797 b8798 d8779
              omega
            have d8799 : (x 5 2 && x 5 11).toNat = 1 := by
              have r8800 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := hcov9 7
              have b8801 := hb (x 1 6)
              have b8802 := hb (x 7 9)
              have b8803 := hb (x 6 1 && x 6 10)
              have b8804 := hb (x 5 2 && x 5 11)
              have b8805 := hb (x 4 3 && x 4 12)
              have b8806 := hb (x 3 4 && x 3 13)
              have b8807 := hb (x 2 5 && x 2 14)
              clear * - r8800 b8801 b8802 b8803 b8804 b8805 b8806 b8807 d8763 d8795 g66 g67 d6397 f7417
              omega
            have d8808 : (x 5 11).toNat = 1 := by
              have r8809 := hand2 (x 5 2) (x 5 11)
              have b8810 := hb (x 5 11)
              have b8811 := hb (x 5 2 && x 5 11)
              clear * - r8809 b8810 b8811 d8799
              omega
            have r8812 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
            have e8813 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e8814 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e8815 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e8816 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e8817 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e8818 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have b8819 := hb (x 1 7)
            have b8820 := hb (x 2 6)
            have b8821 := hb (x 3 5)
            have b8822 := hb (x 4 4)
            have b8823 := hb (x 5 11)
            have b8824 := hb (x 6 10)
            have b8825 := hb (x 7 9)
            have b8826 := hb (x 8 8)
            linarith only [r8812, e8813, e8814, e8815, e8816, e8817, e8818, b8819, b8820, b8821, b8822, b8823, b8824, b8825, b8826, d8747, d8763, d8779, d8808, g27, g25, d6421, f8746]
        · have f8827 : (x 1 6).toNat = 1 := by rw [h7416]; rfl
          have d8828 : (x 7 8).toNat = 0 := by
            have r8829 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
            have e8830 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
            have e8831 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
            have e8832 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
            have e8833 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
            have e8834 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
            have e8835 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
            have b8836 := hb (x 0 7)
            have b8837 := hb (x 1 6)
            have b8838 := hb (x 2 5)
            have b8839 := hb (x 3 4)
            have b8840 := hb (x 4 11)
            have b8841 := hb (x 5 10)
            have b8842 := hb (x 6 9)
            have b8843 := hb (x 7 8)
            clear * - r8829 e8830 e8831 e8832 e8833 e8834 e8835 b8836 b8837 b8838 b8839 b8840 b8841 b8842 b8843 d6357 d6393 f8827 g12
            omega
          have d8844 : (x 7 1 && x 7 8).toNat = 0 := by
            have r8845 := hand2 (x 7 1) (x 7 8)
            have b8846 := hb (x 7 8)
            have b8847 := hb (x 7 1 && x 7 8)
            clear * - r8845 b8846 b8847 d8828
            omega
          have d8848 : (x 7 2 && x 7 8).toNat = 0 := by
            have r8849 := hand2 (x 7 2) (x 7 8)
            have b8850 := hb (x 7 8)
            have b8851 := hb (x 7 2 && x 7 8)
            clear * - r8849 b8850 b8851 d8828
            omega
          have d8852 : (x 6 9).toNat = 0 := by
            have r8853 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
            have e8854 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
            have e8855 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
            have e8856 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
            have e8857 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
            have e8858 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
            have e8859 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
            have b8860 := hb (x 0 7)
            have b8861 := hb (x 1 6)
            have b8862 := hb (x 2 5)
            have b8863 := hb (x 3 4)
            have b8864 := hb (x 4 11)
            have b8865 := hb (x 5 10)
            have b8866 := hb (x 6 9)
            have b8867 := hb (x 7 8)
            clear * - r8853 e8854 e8855 e8856 e8857 e8858 e8859 b8860 b8861 b8862 b8863 b8864 b8865 b8866 b8867 d8828 d6357 d6393 f8827 g12
            omega
          have d8868 : (x 6 2 && x 6 9).toNat = 0 := by
            have r8869 := hand2 (x 6 2) (x 6 9)
            have b8870 := hb (x 6 9)
            have b8871 := hb (x 6 2 && x 6 9)
            clear * - r8869 b8870 b8871 d8852
            omega
          have d8872 : (x 6 3 && x 6 9).toNat = 0 := by
            have r8873 := hand2 (x 6 3) (x 6 9)
            have b8874 := hb (x 6 9)
            have b8875 := hb (x 6 3 && x 6 9)
            clear * - r8873 b8874 b8875 d8852
            omega
          have d8876 : (x 5 10).toNat = 0 := by
            have r8877 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
            have e8878 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
            have e8879 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
            have e8880 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
            have e8881 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
            have e8882 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
            have e8883 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
            have b8884 := hb (x 0 7)
            have b8885 := hb (x 1 6)
            have b8886 := hb (x 2 5)
            have b8887 := hb (x 3 4)
            have b8888 := hb (x 4 11)
            have b8889 := hb (x 5 10)
            have b8890 := hb (x 6 9)
            have b8891 := hb (x 7 8)
            clear * - r8877 e8878 e8879 e8880 e8881 e8882 e8883 b8884 b8885 b8886 b8887 b8888 b8889 b8890 b8891 d8828 d8852 d6357 d6393 f8827 g12
            omega
          have d8892 : (x 5 3 && x 5 10).toNat = 0 := by
            have r8893 := hand2 (x 5 3) (x 5 10)
            have b8894 := hb (x 5 10)
            have b8895 := hb (x 5 3 && x 5 10)
            clear * - r8893 b8894 b8895 d8876
            omega
          have d8896 : (x 5 4 && x 5 10).toNat = 0 := by
            have r8897 := hand2 (x 5 4) (x 5 10)
            have b8898 := hb (x 5 10)
            have b8899 := hb (x 5 4 && x 5 10)
            clear * - r8897 b8898 b8899 d8876
            omega
          have d8900 : (x 4 11).toNat = 0 := by
            have r8901 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
            have e8902 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
            have e8903 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
            have e8904 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
            have e8905 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
            have e8906 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
            have e8907 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
            have b8908 := hb (x 0 7)
            have b8909 := hb (x 1 6)
            have b8910 := hb (x 2 5)
            have b8911 := hb (x 3 4)
            have b8912 := hb (x 4 11)
            have b8913 := hb (x 5 10)
            have b8914 := hb (x 6 9)
            have b8915 := hb (x 7 8)
            clear * - r8901 e8902 e8903 e8904 e8905 e8906 e8907 b8908 b8909 b8910 b8911 b8912 b8913 b8914 b8915 d8828 d8852 d8876 d6357 d6393 f8827 g12
            omega
          have d8916 : (x 4 5 && x 4 11).toNat = 0 := by
            have r8917 := hand2 (x 4 5) (x 4 11)
            have b8918 := hb (x 4 11)
            have b8919 := hb (x 4 5 && x 4 11)
            clear * - r8917 b8918 b8919 d8900
            omega
          cases h8920 : x 1 7
          · have f8921 : (x 1 7).toNat = 0 := by rw [h8920]; rfl
            have d8922 : (x 1 7 && x 1 14).toNat = 0 := by
              have r8923 := hand1 (x 1 7) (x 1 14)
              have b8924 := hb (x 1 7)
              have b8925 := hb (x 1 7 && x 1 14)
              clear * - r8923 b8924 b8925 f8921
              omega
            have d8926 : (x 1 7 && x 1 13).toNat = 0 := by
              have r8927 := hand1 (x 1 7) (x 1 13)
              have b8928 := hb (x 1 7)
              have b8929 := hb (x 1 7 && x 1 13)
              clear * - r8927 b8928 b8929 f8921
              omega
            have d8930 : (x 1 7 && x 1 11).toNat = 0 := by
              have r8931 := hand1 (x 1 7) (x 1 11)
              have b8932 := hb (x 1 7)
              have b8933 := hb (x 1 7 && x 1 11)
              clear * - r8931 b8932 b8933 f8921
              omega
            have d8934 : (x 8 7).toNat = 1 := by
              have r8935 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := hcov7 8
              have b8936 := hb (x 0 8)
              have b8937 := hb (x 8 7)
              have b8938 := hb (x 7 1 && x 7 8)
              have b8939 := hb (x 6 2 && x 6 9)
              have b8940 := hb (x 5 3 && x 5 10)
              have b8941 := hb (x 4 4 && x 4 11)
              have b8942 := hb (x 3 5 && x 3 12)
              have b8943 := hb (x 2 6 && x 2 13)
              have b8944 := hb (x 1 7 && x 1 14)
              clear * - r8935 b8936 b8937 b8938 b8939 b8940 b8941 b8942 b8943 b8944 d8844 d8868 d8892 g54 g55 d6385 d8922 g13
              omega
            have d8945 : (x 15 8).toNat = 0 := by
              have r8946 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
              have e8947 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
              have e8948 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
              have e8949 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
              have e8950 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
              have e8951 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
              have e8952 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
              have b8953 := hb (x 8 7)
              have b8954 := hb (x 9 6)
              have b8955 := hb (x 10 5)
              have b8956 := hb (x 11 4)
              have b8957 := hb (x 12 11)
              have b8958 := hb (x 13 10)
              have b8959 := hb (x 14 9)
              have b8960 := hb (x 15 8)
              clear * - r8946 e8947 e8948 e8949 e8950 e8951 e8952 b8953 b8954 b8955 b8956 b8957 b8958 b8959 b8960 d8934
              omega
            have d8961 : (x 14 9).toNat = 0 := by
              have r8962 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
              have e8963 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
              have e8964 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
              have e8965 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
              have e8966 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
              have e8967 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
              have e8968 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
              have b8969 := hb (x 8 7)
              have b8970 := hb (x 9 6)
              have b8971 := hb (x 10 5)
              have b8972 := hb (x 11 4)
              have b8973 := hb (x 12 11)
              have b8974 := hb (x 13 10)
              have b8975 := hb (x 14 9)
              have b8976 := hb (x 15 8)
              clear * - r8962 e8963 e8964 e8965 e8966 e8967 e8968 b8969 b8970 b8971 b8972 b8973 b8974 b8975 b8976 d8945 d8934
              omega
            have d8977 : (x 13 10).toNat = 0 := by
              have r8978 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
              have e8979 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
              have e8980 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
              have e8981 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
              have e8982 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
              have e8983 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
              have e8984 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
              have b8985 := hb (x 8 7)
              have b8986 := hb (x 9 6)
              have b8987 := hb (x 10 5)
              have b8988 := hb (x 11 4)
              have b8989 := hb (x 12 11)
              have b8990 := hb (x 13 10)
              have b8991 := hb (x 14 9)
              have b8992 := hb (x 15 8)
              clear * - r8978 e8979 e8980 e8981 e8982 e8983 e8984 b8985 b8986 b8987 b8988 b8989 b8990 b8991 b8992 d8945 d8961 d8934
              omega
            have d8993 : (x 13 1 && x 13 10).toNat = 0 := by
              have r8994 := hand2 (x 13 1) (x 13 10)
              have b8995 := hb (x 13 10)
              have b8996 := hb (x 13 1 && x 13 10)
              clear * - r8994 b8995 b8996 d8977
              omega
            have d8997 : (x 12 11).toNat = 0 := by
              have r8998 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
              have e8999 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
              have e9000 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
              have e9001 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
              have e9002 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
              have e9003 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
              have e9004 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
              have b9005 := hb (x 8 7)
              have b9006 := hb (x 9 6)
              have b9007 := hb (x 10 5)
              have b9008 := hb (x 11 4)
              have b9009 := hb (x 12 11)
              have b9010 := hb (x 13 10)
              have b9011 := hb (x 14 9)
              have b9012 := hb (x 15 8)
              clear * - r8998 e8999 e9000 e9001 e9002 e9003 e9004 b9005 b9006 b9007 b9008 b9009 b9010 b9011 b9012 d8945 d8961 d8977 d8934
              omega
            have d9013 : (x 12 2 && x 12 11).toNat = 0 := by
              have r9014 := hand2 (x 12 2) (x 12 11)
              have b9015 := hb (x 12 11)
              have b9016 := hb (x 12 2 && x 12 11)
              clear * - r9014 b9015 b9016 d8997
              omega
            have d9017 : (x 11 4).toNat = 0 := by
              have r9018 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
              have e9019 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
              have e9020 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
              have e9021 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
              have e9022 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
              have e9023 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
              have e9024 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
              have b9025 := hb (x 8 7)
              have b9026 := hb (x 9 6)
              have b9027 := hb (x 10 5)
              have b9028 := hb (x 11 4)
              have b9029 := hb (x 12 11)
              have b9030 := hb (x 13 10)
              have b9031 := hb (x 14 9)
              have b9032 := hb (x 15 8)
              clear * - r9018 e9019 e9020 e9021 e9022 e9023 e9024 b9025 b9026 b9027 b9028 b9029 b9030 b9031 b9032 d8945 d8961 d8977 d8997 d8934
              omega
            have d9033 : (x 10 5).toNat = 0 := by
              have r9034 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
              have e9035 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
              have e9036 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
              have e9037 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
              have e9038 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
              have e9039 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
              have e9040 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
              have b9041 := hb (x 8 7)
              have b9042 := hb (x 9 6)
              have b9043 := hb (x 10 5)
              have b9044 := hb (x 11 4)
              have b9045 := hb (x 12 11)
              have b9046 := hb (x 13 10)
              have b9047 := hb (x 14 9)
              have b9048 := hb (x 15 8)
              clear * - r9034 e9035 e9036 e9037 e9038 e9039 e9040 b9041 b9042 b9043 b9044 b9045 b9046 b9047 b9048 d8945 d8961 d8977 d8997 d9017 d8934
              omega
            have d9049 : (x 9 6).toNat = 0 := by
              have r9050 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
              have e9051 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
              have e9052 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
              have e9053 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
              have e9054 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
              have e9055 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
              have e9056 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
              have b9057 := hb (x 8 7)
              have b9058 := hb (x 9 6)
              have b9059 := hb (x 10 5)
              have b9060 := hb (x 11 4)
              have b9061 := hb (x 12 11)
              have b9062 := hb (x 13 10)
              have b9063 := hb (x 14 9)
              have b9064 := hb (x 15 8)
              clear * - r9050 e9051 e9052 e9053 e9054 e9055 e9056 b9057 b9058 b9059 b9060 b9061 b9062 b9063 b9064 d8945 d8961 d8977 d8997 d9017 d9033 d8934
              omega
            have d9065 : (x 8 1 && x 8 7).toNat = 1 := by
              have r9066 : 1 ≤ (x 9 6).toNat + (x 8 1 && x 8 7).toNat + (x 7 2 && x 7 8).toNat + (x 6 3 && x 6 9).toNat + (x 5 4 && x 5 10).toNat + (x 4 5 && x 4 11).toNat + (x 3 6 && x 3 12).toNat + (x 2 7 && x 2 13).toNat + (x 1 8 && x 1 14).toNat + (x 0 9).toNat := hcov6 9
              have b9067 := hb (x 0 9)
              have b9068 := hb (x 9 6)
              have b9069 := hb (x 8 1 && x 8 7)
              have b9070 := hb (x 7 2 && x 7 8)
              have b9071 := hb (x 6 3 && x 6 9)
              have b9072 := hb (x 5 4 && x 5 10)
              have b9073 := hb (x 4 5 && x 4 11)
              have b9074 := hb (x 3 6 && x 3 12)
              have b9075 := hb (x 2 7 && x 2 13)
              have b9076 := hb (x 1 8 && x 1 14)
              clear * - r9066 b9067 b9068 b9069 b9070 b9071 b9072 b9073 b9074 b9075 b9076 d9049 d8848 d8872 d8896 d8916 d6353 d6389 g50 g14
              omega
            have d9077 : (x 8 1).toNat = 1 := by
              have r9078 := hand1 (x 8 1) (x 8 7)
              have b9079 := hb (x 8 1)
              have b9080 := hb (x 8 1 && x 8 7)
              clear * - r9078 b9079 b9080 d9065
              omega
            have d9081 : (x 9 14).toNat = 0 := by
              have r9082 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
              have b9083 := hb (x 8 1)
              have b9084 := hb (x 9 14)
              clear * - r9082 b9083 b9084 d9077
              omega
            have d9085 : (x 9 3 && x 9 14).toNat = 0 := by
              have r9086 := hand2 (x 9 3) (x 9 14)
              have b9087 := hb (x 9 14)
              have b9088 := hb (x 9 3 && x 9 14)
              clear * - r9086 b9087 b9088 d9081
              omega
            have d9089 : (x 9 5 && x 9 14).toNat = 0 := by
              have r9090 := hand2 (x 9 5) (x 9 14)
              have b9091 := hb (x 9 14)
              have b9092 := hb (x 9 5 && x 9 14)
              clear * - r9090 b9091 b9092 d9081
              omega
            have r9093 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := hcount 8
            have r9094 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := hcount 12
            have r9095 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := hcount 14
            have r9096 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
            have e9097 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
            have e9098 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
            have e9099 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
            have e9100 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
            have e9101 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
            have e9102 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
            have r9103 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := hd12 (-4)
            have e9104 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
            have e9105 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
            have r9106 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := hd12 (-3)
            have e9107 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
            have e9108 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
            have r9109 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
            have e9110 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
            have e9111 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
            have r9112 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := hd14 (-4)
            have r9113 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
            have r9114 : 1 ≤ (x 8 4).toNat + (x 7 1 && x 7 5).toNat + (x 6 2 && x 6 6).toNat + (x 5 3 && x 5 7).toNat + (x 4 4 && x 4 8).toNat + (x 3 5 && x 3 9).toNat + (x 2 6 && x 2 10).toNat + (x 1 7 && x 1 11).toNat + (x 0 8 && x 0 12).toNat + (x (-1) 9 && x (-1) 13).toNat + (x (-2) 10 && x (-2) 14).toNat + (x (-3) 11).toNat := hcov4 8
            have e9115 : (x 7 1 && x 7 5).toNat = (x 7 5).toNat := handr _ _ (fun h => hp13 7 (hp5 7 (h)))
            have e9116 : (x (-2) 10 && x (-2) 14).toNat = (x (-2) 10).toNat := handl _ _ (fun h => hp2 (-2) (hp10 (-2) (h)))
            have r9117 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := hcov6 8
            have r9118 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := hcov9 0
            have r9119 : 1 ≤ (x 14 9).toNat + (x 13 1 && x 13 10).toNat + (x 12 2 && x 12 11).toNat + (x 11 3 && x 11 12).toNat + (x 10 4 && x 10 13).toNat + (x 9 5 && x 9 14).toNat + (x 8 6).toNat := hcov9 14
            have r9120 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := hcov11 1
            have r9121 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := hcov11 12
            have r9122 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := hcov13 (-4)
            have r9123 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := hcov13 (-3)
            have r9124 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
            have r9125 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
            have r9126 : (x 8 6).toNat ≤ (x 8 14).toNat := himp _ _ (hp6 8)
            have r9127 := hand2 (x 6 2) (x 6 6)
            have r9128 := hand2 (x 5 3) (x 5 7)
            have r9129 := hand2 (x 7 1) (x 7 7)
            have r9130 := hand1 (x (-4) 4) (x (-4) 13)
            have r9131 := hand1 (x (-5) 5) (x (-5) 14)
            have r9132 := hand1 (x 11 3) (x 11 12)
            have r9133 := hand1 (x 10 4) (x 10 13)
            have r9134 := hand1 (x 11 1) (x 11 12)
            have r9135 := hand1 (x 10 2) (x 10 13)
            have r9136 := hand1 (x (-5) 1) (x (-5) 14)
            have r9137 := hand2 (x (-4) 1) (x (-4) 14)
            have b9138 := hb (x (-7) 3)
            have b9139 := hb (x (-7) 7)
            have b9140 := hb (x (-6) 2)
            have b9141 := hb (x (-6) 3)
            have b9142 := hb (x (-6) 6)
            have b9143 := hb (x (-6) 14)
            have b9144 := hb (x (-5) 1)
            have b9145 := hb (x (-5) 2)
            have b9146 := hb (x (-5) 5)
            have b9147 := hb (x (-5) 13)
            have b9148 := hb (x (-4) 4)
            have b9149 := hb (x (-4) 12)
            have b9150 := hb (x (-4) 13)
            have b9151 := hb (x (-4) 14)
            have b9152 := hb (x (-3) 4)
            have b9153 := hb (x (-3) 11)
            have b9154 := hb (x (-3) 12)
            have b9155 := hb (x (-3) 13)
            have b9156 := hb (x (-2) 10)
            have b9157 := hb (x (-2) 14)
            have b9158 := hb (x (-1) 9)
            have b9159 := hb (x (-1) 13)
            have b9160 := hb (x 0 8)
            have b9161 := hb (x 0 9)
            have b9162 := hb (x 0 12)
            have b9163 := hb (x 0 14)
            have b9164 := hb (x 1 7)
            have b9165 := hb (x 1 11)
            have b9166 := hb (x 1 13)
            have b9167 := hb (x 2 6)
            have b9168 := hb (x 2 10)
            have b9169 := hb (x 2 12)
            have b9170 := hb (x 3 5)
            have b9171 := hb (x 3 9)
            have b9172 := hb (x 3 11)
            have b9173 := hb (x 4 4)
            have b9174 := hb (x 4 8)
            have b9175 := hb (x 4 10)
            have b9176 := hb (x 5 3)
            have b9177 := hb (x 5 7)
            have b9178 := hb (x 5 9)
            have b9179 := hb (x 6 2)
            have b9180 := hb (x 6 6)
            have b9181 := hb (x 6 8)
            have b9182 := hb (x 7 1)
            have b9183 := hb (x 7 5)
            have b9184 := hb (x 7 7)
            have b9185 := hb (x 7 13)
            have b9186 := hb (x 8 4)
            have b9187 := hb (x 8 6)
            have b9188 := hb (x 8 12)
            have b9189 := hb (x 8 14)
            have b9190 := hb (x 9 3)
            have b9191 := hb (x 9 5)
            have b9192 := hb (x 10 2)
            have b9193 := hb (x 10 4)
            have b9194 := hb (x 11 1)
            have b9195 := hb (x 11 3)
            have b9196 := hb (x 12 2)
            have b9197 := hb (x 12 11)
            have b9198 := hb (x 13 1)
            have b9199 := hb (x 14 9)
            have b9200 := hb (x 6 2 && x 6 6)
            have b9201 := hb (x 5 3 && x 5 7)
            have b9202 := hb (x 4 4 && x 4 8)
            have b9203 := hb (x 3 5 && x 3 9)
            have b9204 := hb (x 2 6 && x 2 10)
            have b9205 := hb (x 1 7 && x 1 11)
            have b9206 := hb (x 0 8 && x 0 12)
            have b9207 := hb (x (-1) 9 && x (-1) 13)
            have b9208 := hb (x 7 1 && x 7 7)
            have b9209 := hb (x 6 2 && x 6 8)
            have b9210 := hb (x 5 3 && x 5 9)
            have b9211 := hb (x 4 4 && x 4 10)
            have b9212 := hb (x 3 5 && x 3 11)
            have b9213 := hb (x 2 6 && x 2 12)
            have b9214 := hb (x 1 7 && x 1 13)
            have b9215 := hb (x 0 8 && x 0 14)
            have b9216 := hb (x (-1) 1 && x (-1) 10)
            have b9217 := hb (x (-2) 2 && x (-2) 11)
            have b9218 := hb (x (-3) 3 && x (-3) 12)
            have b9219 := hb (x (-4) 4 && x (-4) 13)
            have b9220 := hb (x (-5) 5 && x (-5) 14)
            have b9221 := hb (x 13 1 && x 13 10)
            have b9222 := hb (x 12 2 && x 12 11)
            have b9223 := hb (x 11 3 && x 11 12)
            have b9224 := hb (x 10 4 && x 10 13)
            have b9225 := hb (x 9 5 && x 9 14)
            have b9226 := hb (x 0 1 && x 0 12)
            have b9227 := hb (x (-1) 2 && x (-1) 13)
            have b9228 := hb (x (-2) 3 && x (-2) 14)
            have b9229 := hb (x 11 1 && x 11 12)
            have b9230 := hb (x 10 2 && x 10 13)
            have b9231 := hb (x 9 3 && x 9 14)
            have b9232 := hb (x (-5) 1 && x (-5) 14)
            have b9233 := hb (x (-4) 1 && x (-4) 14)
            linarith only [r9093, r9094, r9095, r9096, e9097, e9098, e9099, e9100, e9101, e9102, r9103, e9104, e9105, r9106, e9107, e9108, r9109, e9110, e9111, r9112, r9113, r9114, e9115, e9116, r9117, r9118, r9119, r9120, r9121, r9122, r9123, r9124, r9125, r9126, r9127, r9128, r9129, r9130, r9131, r9132, r9133, r9134, r9135, r9136, r9137, b9138, b9139, b9140, b9141, b9142, b9143, b9144, b9145, b9146, b9147, b9148, b9149, b9150, b9151, b9152, b9153, b9154, b9155, b9156, b9157, b9158, b9159, b9160, b9161, b9162, b9163, b9164, b9165, b9166, b9167, b9168, b9169, b9170, b9171, b9172, b9173, b9174, b9175, b9176, b9177, b9178, b9179, b9180, b9181, b9182, b9183, b9184, b9185, b9186, b9187, b9188, b9189, b9190, b9191, b9192, b9193, b9194, b9195, b9196, b9197, b9198, b9199, b9200, b9201, b9202, b9203, b9204, b9205, b9206, b9207, b9208, b9209, b9210, b9211, b9212, b9213, b9214, b9215, b9216, b9217, b9218, b9219, b9220, b9221, b9222, b9223, b9224, b9225, b9226, b9227, b9228, b9229, b9230, b9231, b9232, b9233, g2, g3, g4, g6, g7, g13, g14, g17, g19, f8921, d6319, d6421, g24, d6429, g25, d7396, g27, d7372, d7344, d7316, d8997, d8961, g33, g34, g35, d8930, g36, g37, d7336, d7364, g47, g48, d6425, d8926, g49, g60, d6485, g61, d8993, d9013, d9089, g80, g81, d6469, d9085]
          · have f9234 : (x 1 7).toNat = 1 := by rw [h8920]; rfl
            have d9235 : (x 8 8).toNat = 0 := by
              have r9236 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
              have e9237 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e9238 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e9239 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e9240 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e9241 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e9242 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b9243 := hb (x 1 7)
              have b9244 := hb (x 2 6)
              have b9245 := hb (x 3 5)
              have b9246 := hb (x 4 4)
              have b9247 := hb (x 5 11)
              have b9248 := hb (x 6 10)
              have b9249 := hb (x 7 9)
              have b9250 := hb (x 8 8)
              clear * - r9236 e9237 e9238 e9239 e9240 e9241 e9242 b9243 b9244 b9245 b9246 b9247 b9248 b9249 b9250 g27 g25 d6421 f9234
              omega
            have d9251 : (x 8 1 && x 8 8).toNat = 0 := by
              have r9252 := hand2 (x 8 1) (x 8 8)
              have b9253 := hb (x 8 8)
              have b9254 := hb (x 8 1 && x 8 8)
              clear * - r9252 b9253 b9254 d9235
              omega
            have d9255 : (x 8 2 && x 8 8).toNat = 0 := by
              have r9256 := hand2 (x 8 2) (x 8 8)
              have b9257 := hb (x 8 8)
              have b9258 := hb (x 8 2 && x 8 8)
              clear * - r9256 b9257 b9258 d9235
              omega
            have d9259 : (x 8 3 && x 8 8).toNat = 0 := by
              have r9260 := hand2 (x 8 3) (x 8 8)
              have b9261 := hb (x 8 8)
              have b9262 := hb (x 8 3 && x 8 8)
              clear * - r9260 b9261 b9262 d9235
              omega
            have d9263 : (x 7 9).toNat = 0 := by
              have r9264 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
              have e9265 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e9266 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e9267 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e9268 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e9269 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e9270 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b9271 := hb (x 1 7)
              have b9272 := hb (x 2 6)
              have b9273 := hb (x 3 5)
              have b9274 := hb (x 4 4)
              have b9275 := hb (x 5 11)
              have b9276 := hb (x 6 10)
              have b9277 := hb (x 7 9)
              have b9278 := hb (x 8 8)
              clear * - r9264 e9265 e9266 e9267 e9268 e9269 e9270 b9271 b9272 b9273 b9274 b9275 b9276 b9277 b9278 d9235 g27 g25 d6421 f9234
              omega
            have d9279 : (x 7 2 && x 7 9).toNat = 0 := by
              have r9280 := hand2 (x 7 2) (x 7 9)
              have b9281 := hb (x 7 9)
              have b9282 := hb (x 7 2 && x 7 9)
              clear * - r9280 b9281 b9282 d9263
              omega
            have d9283 : (x 7 3 && x 7 9).toNat = 0 := by
              have r9284 := hand2 (x 7 3) (x 7 9)
              have b9285 := hb (x 7 9)
              have b9286 := hb (x 7 3 && x 7 9)
              clear * - r9284 b9285 b9286 d9263
              omega
            have d9287 : (x 7 4 && x 7 9).toNat = 0 := by
              have r9288 := hand2 (x 7 4) (x 7 9)
              have b9289 := hb (x 7 9)
              have b9290 := hb (x 7 4 && x 7 9)
              clear * - r9288 b9289 b9290 d9263
              omega
            have d9291 : (x 6 10).toNat = 0 := by
              have r9292 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
              have e9293 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e9294 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e9295 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e9296 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e9297 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e9298 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b9299 := hb (x 1 7)
              have b9300 := hb (x 2 6)
              have b9301 := hb (x 3 5)
              have b9302 := hb (x 4 4)
              have b9303 := hb (x 5 11)
              have b9304 := hb (x 6 10)
              have b9305 := hb (x 7 9)
              have b9306 := hb (x 8 8)
              clear * - r9292 e9293 e9294 e9295 e9296 e9297 e9298 b9299 b9300 b9301 b9302 b9303 b9304 b9305 b9306 d9235 d9263 g27 g25 d6421 f9234
              omega
            have d9307 : (x 6 3 && x 6 10).toNat = 0 := by
              have r9308 := hand2 (x 6 3) (x 6 10)
              have b9309 := hb (x 6 10)
              have b9310 := hb (x 6 3 && x 6 10)
              clear * - r9308 b9309 b9310 d9291
              omega
            have d9311 : (x 6 4 && x 6 10).toNat = 0 := by
              have r9312 := hand2 (x 6 4) (x 6 10)
              have b9313 := hb (x 6 10)
              have b9314 := hb (x 6 4 && x 6 10)
              clear * - r9312 b9313 b9314 d9291
              omega
            have d9315 : (x 6 5 && x 6 10).toNat = 0 := by
              have r9316 := hand2 (x 6 5) (x 6 10)
              have b9317 := hb (x 6 10)
              have b9318 := hb (x 6 5 && x 6 10)
              clear * - r9316 b9317 b9318 d9291
              omega
            have d9319 : (x 5 11).toNat = 0 := by
              have r9320 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
              have e9321 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e9322 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e9323 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e9324 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e9325 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e9326 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b9327 := hb (x 1 7)
              have b9328 := hb (x 2 6)
              have b9329 := hb (x 3 5)
              have b9330 := hb (x 4 4)
              have b9331 := hb (x 5 11)
              have b9332 := hb (x 6 10)
              have b9333 := hb (x 7 9)
              have b9334 := hb (x 8 8)
              clear * - r9320 e9321 e9322 e9323 e9324 e9325 e9326 b9327 b9328 b9329 b9330 b9331 b9332 b9333 b9334 d9235 d9263 d9291 g27 g25 d6421 f9234
              omega
            have d9335 : (x 5 4 && x 5 11).toNat = 0 := by
              have r9336 := hand2 (x 5 4) (x 5 11)
              have b9337 := hb (x 5 11)
              have b9338 := hb (x 5 4 && x 5 11)
              clear * - r9336 b9337 b9338 d9319
              omega
            have d9339 : (x 5 5 && x 5 11).toNat = 0 := by
              have r9340 := hand2 (x 5 5) (x 5 11)
              have b9341 := hb (x 5 11)
              have b9342 := hb (x 5 5 && x 5 11)
              clear * - r9340 b9341 b9342 d9319
              omega
            have d9343 : (x 5 6 && x 5 11).toNat = 0 := by
              have r9344 := hand2 (x 5 6) (x 5 11)
              have b9345 := hb (x 5 11)
              have b9346 := hb (x 5 6 && x 5 11)
              clear * - r9344 b9345 b9346 d9319
              omega
            have d9347 : (x 9 7).toNat = 1 := by
              have r9348 : 1 ≤ (x 9 7).toNat + (x 8 1 && x 8 8).toNat + (x 7 2 && x 7 9).toNat + (x 6 3 && x 6 10).toNat + (x 5 4 && x 5 11).toNat + (x 4 5 && x 4 12).toNat + (x 3 6 && x 3 13).toNat + (x 2 7 && x 2 14).toNat + (x 1 8).toNat := hcov7 9
              have b9349 := hb (x 1 8)
              have b9350 := hb (x 9 7)
              have b9351 := hb (x 8 1 && x 8 8)
              have b9352 := hb (x 7 2 && x 7 9)
              have b9353 := hb (x 6 3 && x 6 10)
              have b9354 := hb (x 5 4 && x 5 11)
              have b9355 := hb (x 4 5 && x 4 12)
              have b9356 := hb (x 3 6 && x 3 13)
              have b9357 := hb (x 2 7 && x 2 14)
              clear * - r9348 b9349 b9350 b9351 b9352 b9353 b9354 b9355 b9356 b9357 d9251 d9279 d9307 d9335 g56 g57 d6409 g21
              omega
            have d9358 : (x 16 8).toNat = 0 := by
              have r9359 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := hd8 16
              have e9360 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
              have e9361 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
              have e9362 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
              have e9363 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
              have e9364 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
              have e9365 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
              have b9366 := hb (x 9 7)
              have b9367 := hb (x 10 6)
              have b9368 := hb (x 11 5)
              have b9369 := hb (x 12 4)
              have b9370 := hb (x 13 11)
              have b9371 := hb (x 14 10)
              have b9372 := hb (x 15 9)
              have b9373 := hb (x 16 8)
              clear * - r9359 e9360 e9361 e9362 e9363 e9364 e9365 b9366 b9367 b9368 b9369 b9370 b9371 b9372 b9373 d9347
              omega
            have d9374 : (x 15 9).toNat = 0 := by
              have r9375 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := hd8 16
              have e9376 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
              have e9377 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
              have e9378 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
              have e9379 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
              have e9380 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
              have e9381 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
              have b9382 := hb (x 9 7)
              have b9383 := hb (x 10 6)
              have b9384 := hb (x 11 5)
              have b9385 := hb (x 12 4)
              have b9386 := hb (x 13 11)
              have b9387 := hb (x 14 10)
              have b9388 := hb (x 15 9)
              have b9389 := hb (x 16 8)
              clear * - r9375 e9376 e9377 e9378 e9379 e9380 e9381 b9382 b9383 b9384 b9385 b9386 b9387 b9388 b9389 d9358 d9347
              omega
            have d9390 : (x 14 10).toNat = 0 := by
              have r9391 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := hd8 16
              have e9392 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
              have e9393 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
              have e9394 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
              have e9395 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
              have e9396 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
              have e9397 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
              have b9398 := hb (x 9 7)
              have b9399 := hb (x 10 6)
              have b9400 := hb (x 11 5)
              have b9401 := hb (x 12 4)
              have b9402 := hb (x 13 11)
              have b9403 := hb (x 14 10)
              have b9404 := hb (x 15 9)
              have b9405 := hb (x 16 8)
              clear * - r9391 e9392 e9393 e9394 e9395 e9396 e9397 b9398 b9399 b9400 b9401 b9402 b9403 b9404 b9405 d9358 d9374 d9347
              omega
            have d9406 : (x 14 1 && x 14 10).toNat = 0 := by
              have r9407 := hand2 (x 14 1) (x 14 10)
              have b9408 := hb (x 14 10)
              have b9409 := hb (x 14 1 && x 14 10)
              clear * - r9407 b9408 b9409 d9390
              omega
            have d9410 : (x 13 11).toNat = 0 := by
              have r9411 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := hd8 16
              have e9412 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
              have e9413 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
              have e9414 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
              have e9415 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
              have e9416 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
              have e9417 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
              have b9418 := hb (x 9 7)
              have b9419 := hb (x 10 6)
              have b9420 := hb (x 11 5)
              have b9421 := hb (x 12 4)
              have b9422 := hb (x 13 11)
              have b9423 := hb (x 14 10)
              have b9424 := hb (x 15 9)
              have b9425 := hb (x 16 8)
              clear * - r9411 e9412 e9413 e9414 e9415 e9416 e9417 b9418 b9419 b9420 b9421 b9422 b9423 b9424 b9425 d9358 d9374 d9390 d9347
              omega
            have d9426 : (x 13 1 && x 13 11).toNat = 0 := by
              have r9427 := hand2 (x 13 1) (x 13 11)
              have b9428 := hb (x 13 11)
              have b9429 := hb (x 13 1 && x 13 11)
              clear * - r9427 b9428 b9429 d9410
              omega
            have d9430 : (x 13 2 && x 13 11).toNat = 0 := by
              have r9431 := hand2 (x 13 2) (x 13 11)
              have b9432 := hb (x 13 11)
              have b9433 := hb (x 13 2 && x 13 11)
              clear * - r9431 b9432 b9433 d9410
              omega
            have d9434 : (x 12 4).toNat = 0 := by
              have r9435 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := hd8 16
              have e9436 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
              have e9437 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
              have e9438 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
              have e9439 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
              have e9440 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
              have e9441 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
              have b9442 := hb (x 9 7)
              have b9443 := hb (x 10 6)
              have b9444 := hb (x 11 5)
              have b9445 := hb (x 12 4)
              have b9446 := hb (x 13 11)
              have b9447 := hb (x 14 10)
              have b9448 := hb (x 15 9)
              have b9449 := hb (x 16 8)
              clear * - r9435 e9436 e9437 e9438 e9439 e9440 e9441 b9442 b9443 b9444 b9445 b9446 b9447 b9448 b9449 d9358 d9374 d9390 d9410 d9347
              omega
            have d9450 : (x 11 5).toNat = 0 := by
              have r9451 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := hd8 16
              have e9452 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
              have e9453 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
              have e9454 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
              have e9455 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
              have e9456 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
              have e9457 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
              have b9458 := hb (x 9 7)
              have b9459 := hb (x 10 6)
              have b9460 := hb (x 11 5)
              have b9461 := hb (x 12 4)
              have b9462 := hb (x 13 11)
              have b9463 := hb (x 14 10)
              have b9464 := hb (x 15 9)
              have b9465 := hb (x 16 8)
              clear * - r9451 e9452 e9453 e9454 e9455 e9456 e9457 b9458 b9459 b9460 b9461 b9462 b9463 b9464 b9465 d9358 d9374 d9390 d9410 d9434 d9347
              omega
            have d9466 : (x 10 6).toNat = 0 := by
              have r9467 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := hd8 16
              have e9468 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
              have e9469 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
              have e9470 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
              have e9471 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
              have e9472 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
              have e9473 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
              have b9474 := hb (x 9 7)
              have b9475 := hb (x 10 6)
              have b9476 := hb (x 11 5)
              have b9477 := hb (x 12 4)
              have b9478 := hb (x 13 11)
              have b9479 := hb (x 14 10)
              have b9480 := hb (x 15 9)
              have b9481 := hb (x 16 8)
              clear * - r9467 e9468 e9469 e9470 e9471 e9472 e9473 b9474 b9475 b9476 b9477 b9478 b9479 b9480 b9481 d9358 d9374 d9390 d9410 d9434 d9450 d9347
              omega
            have d9482 : (x 10 1 && x 10 6).toNat = 0 := by
              have r9483 := hand2 (x 10 1) (x 10 6)
              have b9484 := hb (x 10 6)
              have b9485 := hb (x 10 1 && x 10 6)
              clear * - r9483 b9484 b9485 d9466
              omega
            cases h9486 : x (-1) 8
            · have f9487 : (x (-1) 8).toNat = 0 := by rw [h9486]; rfl
              cases h9488 : x 1 9
              · have f9489 : (x 1 9).toNat = 0 := by rw [h9488]; rfl
                have d9490 : (x 9 1 && x 9 7).toNat = 1 := by
                  have r9491 : 1 ≤ (x 10 6).toNat + (x 9 1 && x 9 7).toNat + (x 8 2 && x 8 8).toNat + (x 7 3 && x 7 9).toNat + (x 6 4 && x 6 10).toNat + (x 5 5 && x 5 11).toNat + (x 4 6 && x 4 12).toNat + (x 3 7 && x 3 13).toNat + (x 2 8 && x 2 14).toNat + (x 1 9).toNat := hcov6 10
                  have b9492 := hb (x 1 9)
                  have b9493 := hb (x 10 6)
                  have b9494 := hb (x 9 1 && x 9 7)
                  have b9495 := hb (x 8 2 && x 8 8)
                  have b9496 := hb (x 7 3 && x 7 9)
                  have b9497 := hb (x 6 4 && x 6 10)
                  have b9498 := hb (x 5 5 && x 5 11)
                  have b9499 := hb (x 4 6 && x 4 12)
                  have b9500 := hb (x 3 7 && x 3 13)
                  have b9501 := hb (x 2 8 && x 2 14)
                  clear * - r9491 b9492 b9493 b9494 b9495 b9496 b9497 b9498 b9499 b9500 b9501 d9466 d9255 d9283 d9311 d9339 g51 g52 d6413 f9489
                  omega
                have d9502 : (x 9 1).toNat = 1 := by
                  have r9503 := hand1 (x 9 1) (x 9 7)
                  have b9504 := hb (x 9 1)
                  have b9505 := hb (x 9 1 && x 9 7)
                  clear * - r9503 b9504 b9505 d9490
                  omega
                have d9506 : (x 10 14).toNat = 0 := by
                  have r9507 : (x 10 14).toNat + (x 9 1).toNat = 1 := hd14 10
                  have b9508 := hb (x 9 1)
                  have b9509 := hb (x 10 14)
                  clear * - r9507 b9508 b9509 d9502
                  omega
                have d9510 : (x 10 4 && x 10 14).toNat = 0 := by
                  have r9511 := hand2 (x 10 4) (x 10 14)
                  have b9512 := hb (x 10 14)
                  have b9513 := hb (x 10 4 && x 10 14)
                  clear * - r9511 b9512 b9513 d9506
                  omega
                have d9514 : (x 10 2).toNat = 0 := by
                  have r9515 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
                  have b9516 := hb (x 10 2)
                  have b9517 := hb (x 10 14)
                  clear * - r9515 b9516 b9517 d9506
                  omega
                have d9518 : (x 10 2 && x 10 13).toNat = 0 := by
                  have r9519 := hand1 (x 10 2) (x 10 13)
                  have b9520 := hb (x 10 2)
                  have b9521 := hb (x 10 2 && x 10 13)
                  clear * - r9519 b9520 b9521 d9514
                  omega
                have d9522 : (x 10 2 && x 10 7).toNat = 0 := by
                  have r9523 := hand1 (x 10 2) (x 10 7)
                  have b9524 := hb (x 10 2)
                  have b9525 := hb (x 10 2 && x 10 7)
                  clear * - r9523 b9524 b9525 d9514
                  omega
                have r9526 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := hcount 12
                have r9527 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := hcount 14
                have r9528 : (x 16 1).toNat + (x 15 2).toNat + (x 14 3).toNat + (x 13 4).toNat + (x 12 5).toNat + (x 11 6).toNat + (x 10 7).toNat + (x 9 8).toNat + (x 8 9).toNat + (x 7 10).toNat + (x 6 11).toNat + (x 5 12).toNat + (x 4 13).toNat + (x 3 14).toNat = 3 := hcount 17
                have r9529 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
                have e9530 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                have e9531 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                have e9532 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                have e9533 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                have e9534 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                have e9535 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                have r9536 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
                have e9537 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                have e9538 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                have e9539 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                have e9540 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                have e9541 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                have e9542 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                have r9543 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
                have e9544 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                have e9545 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                have r9546 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
                have e9547 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                have e9548 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                have r9549 : 1 ≤ (x 9 5).toNat + (x 8 1 && x 8 6).toNat + (x 7 2 && x 7 7).toNat + (x 6 3 && x 6 8).toNat + (x 5 4 && x 5 9).toNat + (x 4 5 && x 4 10).toNat + (x 3 6 && x 3 11).toNat + (x 2 7 && x 2 12).toNat + (x 1 8 && x 1 13).toNat + (x 0 9 && x 0 14).toNat + (x (-1) 10).toNat := hcov5 9
                have r9550 : 1 ≤ (x 12 5).toNat + (x 11 1 && x 11 6).toNat + (x 10 2 && x 10 7).toNat + (x 9 3 && x 9 8).toNat + (x 8 4 && x 8 9).toNat + (x 7 5 && x 7 10).toNat + (x 6 6 && x 6 11).toNat + (x 5 7 && x 5 12).toNat + (x 4 8 && x 4 13).toNat + (x 3 9 && x 3 14).toNat + (x 2 10).toNat := hcov5 12
                have r9551 : 1 ≤ (x 9 6).toNat + (x 8 1 && x 8 7).toNat + (x 7 2 && x 7 8).toNat + (x 6 3 && x 6 9).toNat + (x 5 4 && x 5 10).toNat + (x 4 5 && x 4 11).toNat + (x 3 6 && x 3 12).toNat + (x 2 7 && x 2 13).toNat + (x 1 8 && x 1 14).toNat + (x 0 9).toNat := hcov6 9
                have r9552 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := hcov9 1
                have r9553 : 1 ≤ (x 8 9).toNat + (x 7 1 && x 7 10).toNat + (x 6 2 && x 6 11).toNat + (x 5 3 && x 5 12).toNat + (x 4 4 && x 4 13).toNat + (x 3 5 && x 3 14).toNat + (x 2 6).toNat := hcov9 8
                have r9554 : 1 ≤ (x 8 10).toNat + (x 7 1 && x 7 11).toNat + (x 6 2 && x 6 12).toNat + (x 5 3 && x 5 13).toNat + (x 4 4 && x 4 14).toNat + (x 3 5).toNat := hcov10 8
                have r9555 : 1 ≤ (x 14 10).toNat + (x 13 1 && x 13 11).toNat + (x 12 2 && x 12 12).toNat + (x 11 3 && x 11 13).toNat + (x 10 4 && x 10 14).toNat + (x 9 5).toNat := hcov10 14
                have r9556 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := hcov11 1
                have r9557 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := hcov11 12
                have r9558 : 1 ≤ (x 14 11).toNat + (x 13 1 && x 13 12).toNat + (x 12 2 && x 12 13).toNat + (x 11 3 && x 11 14).toNat + (x 10 4).toNat := hcov11 14
                have r9559 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
                have r9560 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
                have r9561 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
                have r9562 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
                have r9563 : (x 9 5).toNat ≤ (x 9 13).toNat := himp _ _ (hp5 9)
                have r9564 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
                have r9565 := hand2 (x 8 1) (x 8 6)
                have r9566 := hand2 (x 7 2) (x 7 7)
                have r9567 := hand2 (x 11 1) (x 11 6)
                have r9568 := hand2 (x 9 3) (x 9 8)
                have r9569 := hand1 (x 8 4) (x 8 9)
                have r9570 := hand1 (x 7 5) (x 7 10)
                have r9571 := hand1 (x 6 6) (x 6 11)
                have r9572 := hand1 (x 5 7) (x 5 12)
                have r9573 := hand1 (x 4 8) (x 4 13)
                have r9574 := hand1 (x 3 9) (x 3 14)
                have r9575 := hand2 (x 8 1) (x 8 7)
                have r9576 := hand1 (x (-4) 5) (x (-4) 14)
                have r9577 := hand2 (x 7 1) (x 7 10)
                have r9578 := hand2 (x 6 2) (x 6 11)
                have r9579 := hand2 (x 5 3) (x 5 12)
                have r9580 := hand2 (x 7 1) (x 7 11)
                have r9581 := hand1 (x 6 2) (x 6 12)
                have r9582 := hand1 (x 5 3) (x 5 13)
                have r9583 := hand1 (x 12 2) (x 12 12)
                have r9584 := hand1 (x 11 3) (x 11 13)
                have r9585 := hand1 (x 11 1) (x 11 12)
                have r9586 := hand1 (x 9 3) (x 9 14)
                have r9587 := hand1 (x 13 1) (x 13 12)
                have r9588 := hand1 (x 12 2) (x 12 13)
                have r9589 := hand1 (x 11 3) (x 11 14)
                have r9590 := hand2 (x 3 1) (x 3 14)
                have b9591 := hb (x (-6) 7)
                have b9592 := hb (x (-5) 6)
                have b9593 := hb (x (-4) 5)
                have b9594 := hb (x (-3) 4)
                have b9595 := hb (x (-2) 11)
                have b9596 := hb (x (-2) 14)
                have b9597 := hb (x (-1) 10)
                have b9598 := hb (x (-1) 13)
                have b9599 := hb (x 0 9)
                have b9600 := hb (x 0 12)
                have b9601 := hb (x 0 14)
                have b9602 := hb (x 1 8)
                have b9603 := hb (x 1 9)
                have b9604 := hb (x 1 11)
                have b9605 := hb (x 1 13)
                have b9606 := hb (x 2 2)
                have b9607 := hb (x 2 6)
                have b9608 := hb (x 2 10)
                have b9609 := hb (x 2 12)
                have b9610 := hb (x 3 5)
                have b9611 := hb (x 3 9)
                have b9612 := hb (x 3 11)
                have b9613 := hb (x 3 14)
                have b9614 := hb (x 4 8)
                have b9615 := hb (x 4 10)
                have b9616 := hb (x 4 13)
                have b9617 := hb (x 5 3)
                have b9618 := hb (x 5 7)
                have b9619 := hb (x 5 9)
                have b9620 := hb (x 5 12)
                have b9621 := hb (x 6 2)
                have b9622 := hb (x 6 6)
                have b9623 := hb (x 6 8)
                have b9624 := hb (x 6 11)
                have b9625 := hb (x 7 3)
                have b9626 := hb (x 7 5)
                have b9627 := hb (x 7 7)
                have b9628 := hb (x 7 10)
                have b9629 := hb (x 7 11)
                have b9630 := hb (x 7 13)
                have b9631 := hb (x 8 2)
                have b9632 := hb (x 8 4)
                have b9633 := hb (x 8 6)
                have b9634 := hb (x 8 7)
                have b9635 := hb (x 8 9)
                have b9636 := hb (x 8 10)
                have b9637 := hb (x 8 12)
                have b9638 := hb (x 9 3)
                have b9639 := hb (x 9 5)
                have b9640 := hb (x 9 6)
                have b9641 := hb (x 9 8)
                have b9642 := hb (x 9 13)
                have b9643 := hb (x 10 2)
                have b9644 := hb (x 10 4)
                have b9645 := hb (x 10 5)
                have b9646 := hb (x 10 7)
                have b9647 := hb (x 10 12)
                have b9648 := hb (x 11 1)
                have b9649 := hb (x 11 3)
                have b9650 := hb (x 11 4)
                have b9651 := hb (x 11 6)
                have b9652 := hb (x 12 2)
                have b9653 := hb (x 12 5)
                have b9654 := hb (x 12 11)
                have b9655 := hb (x 13 1)
                have b9656 := hb (x 13 4)
                have b9657 := hb (x 13 10)
                have b9658 := hb (x 14 3)
                have b9659 := hb (x 14 9)
                have b9660 := hb (x 14 10)
                have b9661 := hb (x 14 11)
                have b9662 := hb (x 15 2)
                have b9663 := hb (x 15 8)
                have b9664 := hb (x 16 1)
                have b9665 := hb (x 8 1 && x 8 6)
                have b9666 := hb (x 7 2 && x 7 7)
                have b9667 := hb (x 6 3 && x 6 8)
                have b9668 := hb (x 5 4 && x 5 9)
                have b9669 := hb (x 4 5 && x 4 10)
                have b9670 := hb (x 3 6 && x 3 11)
                have b9671 := hb (x 2 7 && x 2 12)
                have b9672 := hb (x 1 8 && x 1 13)
                have b9673 := hb (x 0 9 && x 0 14)
                have b9674 := hb (x 11 1 && x 11 6)
                have b9675 := hb (x 10 2 && x 10 7)
                have b9676 := hb (x 9 3 && x 9 8)
                have b9677 := hb (x 8 4 && x 8 9)
                have b9678 := hb (x 7 5 && x 7 10)
                have b9679 := hb (x 6 6 && x 6 11)
                have b9680 := hb (x 5 7 && x 5 12)
                have b9681 := hb (x 4 8 && x 4 13)
                have b9682 := hb (x 3 9 && x 3 14)
                have b9683 := hb (x 8 1 && x 8 7)
                have b9684 := hb (x 7 2 && x 7 8)
                have b9685 := hb (x 6 3 && x 6 9)
                have b9686 := hb (x 5 4 && x 5 10)
                have b9687 := hb (x 4 5 && x 4 11)
                have b9688 := hb (x 3 6 && x 3 12)
                have b9689 := hb (x 2 7 && x 2 13)
                have b9690 := hb (x 1 8 && x 1 14)
                have b9691 := hb (x 0 1 && x 0 10)
                have b9692 := hb (x (-1) 2 && x (-1) 11)
                have b9693 := hb (x (-2) 3 && x (-2) 12)
                have b9694 := hb (x (-3) 4 && x (-3) 13)
                have b9695 := hb (x (-4) 5 && x (-4) 14)
                have b9696 := hb (x 7 1 && x 7 10)
                have b9697 := hb (x 6 2 && x 6 11)
                have b9698 := hb (x 5 3 && x 5 12)
                have b9699 := hb (x 4 4 && x 4 13)
                have b9700 := hb (x 3 5 && x 3 14)
                have b9701 := hb (x 7 1 && x 7 11)
                have b9702 := hb (x 6 2 && x 6 12)
                have b9703 := hb (x 5 3 && x 5 13)
                have b9704 := hb (x 4 4 && x 4 14)
                have b9705 := hb (x 13 1 && x 13 11)
                have b9706 := hb (x 12 2 && x 12 12)
                have b9707 := hb (x 11 3 && x 11 13)
                have b9708 := hb (x 10 4 && x 10 14)
                have b9709 := hb (x 0 1 && x 0 12)
                have b9710 := hb (x (-1) 2 && x (-1) 13)
                have b9711 := hb (x (-2) 3 && x (-2) 14)
                have b9712 := hb (x 11 1 && x 11 12)
                have b9713 := hb (x 10 2 && x 10 13)
                have b9714 := hb (x 9 3 && x 9 14)
                have b9715 := hb (x 13 1 && x 13 12)
                have b9716 := hb (x 12 2 && x 12 13)
                have b9717 := hb (x 11 3 && x 11 14)
                have b9718 := hb (x 3 1 && x 3 14)
                linarith only [r9526, r9527, r9528, r9529, e9530, e9531, e9532, e9533, e9534, e9535, r9536, e9537, e9538, e9539, e9540, e9541, e9542, r9543, e9544, e9545, r9546, e9547, e9548, r9549, r9550, r9551, r9552, r9553, r9554, r9555, r9556, r9557, r9558, r9559, r9560, r9561, r9562, r9563, r9564, r9565, r9566, r9567, r9568, r9569, r9570, r9571, r9572, r9573, r9574, r9575, r9576, r9577, r9578, r9579, r9580, r9581, r9582, r9583, r9584, r9585, r9586, r9587, r9588, r9589, r9590, b9591, b9592, b9593, b9594, b9595, b9596, b9597, b9598, b9599, b9600, b9601, b9602, b9603, b9604, b9605, b9606, b9607, b9608, b9609, b9610, b9611, b9612, b9613, b9614, b9615, b9616, b9617, b9618, b9619, b9620, b9621, b9622, b9623, b9624, b9625, b9626, b9627, b9628, b9629, b9630, b9631, b9632, b9633, b9634, b9635, b9636, b9637, b9638, b9639, b9640, b9641, b9642, b9643, b9644, b9645, b9646, b9647, b9648, b9649, b9650, b9651, b9652, b9653, b9654, b9655, b9656, b9657, b9658, b9659, b9660, b9661, b9662, b9663, b9664, b9665, b9666, b9667, b9668, b9669, b9670, b9671, b9672, b9673, b9674, b9675, b9676, b9677, b9678, b9679, b9680, b9681, b9682, b9683, b9684, b9685, b9686, b9687, b9688, b9689, b9690, b9691, b9692, b9693, b9694, b9695, b9696, b9697, b9698, b9699, b9700, b9701, b9702, b9703, b9704, b9705, b9706, b9707, b9708, b9709, b9710, b9711, b9712, b9713, b9714, b9715, b9716, b9717, b9718, d6477, g4, d6315, g7, g14, g17, g19, g21, f9489, d6319, g23, d6421, g24, d6429, g25, d7396, d7372, d7344, d7316, d9514, d9390, d7340, d7368, d7392, d7412, d6437, g43, g44, d9522, d8848, d8872, d8896, d8916, d6353, d6389, g50, g62, d6311, d6473, g63, g68, g69, g76, d9426, d9510, g80, g81, d6469, d9518]
              · have f9719 : (x 1 9).toNat = 1 := by rw [h9488]; rfl
                have d9720 : (x 2 8).toNat = 0 := by
                  have r9721 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := hd8 2
                  have e9722 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                  have e9723 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                  have e9724 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                  have e9725 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                  have e9726 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                  have e9727 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                  have b9728 := hb (x (-5) 7)
                  have b9729 := hb (x (-4) 6)
                  have b9730 := hb (x (-3) 5)
                  have b9731 := hb (x (-2) 4)
                  have b9732 := hb (x (-1) 11)
                  have b9733 := hb (x 0 10)
                  have b9734 := hb (x 1 9)
                  have b9735 := hb (x 2 8)
                  clear * - r9721 e9722 e9723 e9724 e9725 e9726 e9727 b9728 b9729 b9730 b9731 b9732 b9733 b9734 b9735 f9719 g15 d6457 g0
                  omega
                have d9736 : (x (-2) 4).toNat = 0 := by
                  have r9737 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := hd8 2
                  have e9738 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                  have e9739 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                  have e9740 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                  have e9741 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                  have e9742 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                  have e9743 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                  have b9744 := hb (x (-5) 7)
                  have b9745 := hb (x (-4) 6)
                  have b9746 := hb (x (-3) 5)
                  have b9747 := hb (x (-2) 4)
                  have b9748 := hb (x (-1) 11)
                  have b9749 := hb (x 0 10)
                  have b9750 := hb (x 1 9)
                  have b9751 := hb (x 2 8)
                  clear * - r9737 e9738 e9739 e9740 e9741 e9742 e9743 b9744 b9745 b9746 b9747 b9748 b9749 b9750 b9751 d9720 f9719 g15 d6457 g0
                  omega
                have d9752 : (x (-2) 4 && x (-2) 14).toNat = 0 := by
                  have r9753 := hand1 (x (-2) 4) (x (-2) 14)
                  have b9754 := hb (x (-2) 4)
                  have b9755 := hb (x (-2) 4 && x (-2) 14)
                  clear * - r9753 b9754 b9755 d9736
                  omega
                have d9756 : (x 1 1 && x 1 11).toNat = 1 := by
                  have r9757 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := hcov10 2
                  have b9758 := hb (x (-3) 5)
                  have b9759 := hb (x 2 10)
                  have b9760 := hb (x 1 1 && x 1 11)
                  have b9761 := hb (x 0 2 && x 0 12)
                  have b9762 := hb (x (-1) 3 && x (-1) 13)
                  have b9763 := hb (x (-2) 4 && x (-2) 14)
                  clear * - r9757 b9758 b9759 b9760 b9761 b9762 b9763 g24 g72 g73 d9752 g0
                  omega
                have d9764 : (x 1 11).toNat = 1 := by
                  have r9765 := hand2 (x 1 1) (x 1 11)
                  have b9766 := hb (x 1 11)
                  have b9767 := hb (x 1 1 && x 1 11)
                  clear * - r9765 b9766 b9767 d9756
                  omega
                have d9768 : (x 4 8).toNat = 0 := by
                  have r9769 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := hd8 4
                  have e9770 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
                  have e9771 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
                  have e9772 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
                  have e9773 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
                  have e9774 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
                  have e9775 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
                  have b9776 := hb (x (-3) 7)
                  have b9777 := hb (x (-2) 6)
                  have b9778 := hb (x (-1) 5)
                  have b9779 := hb (x 0 4)
                  have b9780 := hb (x 1 11)
                  have b9781 := hb (x 2 10)
                  have b9782 := hb (x 3 9)
                  have b9783 := hb (x 4 8)
                  clear * - r9769 e9770 e9771 e9772 e9773 e9774 e9775 b9776 b9777 b9778 b9779 b9780 b9781 b9782 b9783 g24 d9764 g10 g5
                  omega
                have d9784 : (x 4 8 && x 4 13).toNat = 0 := by
                  have r9785 := hand1 (x 4 8) (x 4 13)
                  have b9786 := hb (x 4 8)
                  have b9787 := hb (x 4 8 && x 4 13)
                  clear * - r9785 b9786 b9787 d9768
                  omega
                have d9788 : (x 3 9).toNat = 0 := by
                  have r9789 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := hd8 4
                  have e9790 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
                  have e9791 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
                  have e9792 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
                  have e9793 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
                  have e9794 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
                  have e9795 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
                  have b9796 := hb (x (-3) 7)
                  have b9797 := hb (x (-2) 6)
                  have b9798 := hb (x (-1) 5)
                  have b9799 := hb (x 0 4)
                  have b9800 := hb (x 1 11)
                  have b9801 := hb (x 2 10)
                  have b9802 := hb (x 3 9)
                  have b9803 := hb (x 4 8)
                  clear * - r9789 e9790 e9791 e9792 e9793 e9794 e9795 b9796 b9797 b9798 b9799 b9800 b9801 b9802 b9803 d9768 g24 d9764 g10 g5
                  omega
                have d9804 : (x 3 9 && x 3 14).toNat = 0 := by
                  have r9805 := hand1 (x 3 9) (x 3 14)
                  have b9806 := hb (x 3 9)
                  have b9807 := hb (x 3 9 && x 3 14)
                  clear * - r9805 b9806 b9807 d9788
                  omega
                have d9808 : (x (-2) 4 && x (-2) 13).toNat = 0 := by
                  have r9809 := hand1 (x (-2) 4) (x (-2) 13)
                  have b9810 := hb (x (-2) 4)
                  have b9811 := hb (x (-2) 4 && x (-2) 13)
                  clear * - r9809 b9810 b9811 d9736
                  omega
                have d9812 : (x (-4) 6).toNat = 0 := by
                  have r9813 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := hd8 2
                  have e9814 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                  have e9815 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                  have e9816 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                  have e9817 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                  have e9818 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                  have e9819 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                  have b9820 := hb (x (-5) 7)
                  have b9821 := hb (x (-4) 6)
                  have b9822 := hb (x (-3) 5)
                  have b9823 := hb (x (-2) 4)
                  have b9824 := hb (x (-1) 11)
                  have b9825 := hb (x 0 10)
                  have b9826 := hb (x 1 9)
                  have b9827 := hb (x 2 8)
                  clear * - r9813 e9814 e9815 e9816 e9817 e9818 e9819 b9820 b9821 b9822 b9823 b9824 b9825 b9826 b9827 d9720 f9719 g15 d6457 d9736 g0
                  omega
                cases h9828 : x 1 10
                · have f9829 : (x 1 10).toNat = 0 := by rw [h9828]; rfl
                  have d9830 : (x 1 1 && x 1 10).toNat = 0 := by
                    have r9831 := hand2 (x 1 1) (x 1 10)
                    have b9832 := hb (x 1 10)
                    have b9833 := hb (x 1 1 && x 1 10)
                    clear * - r9831 b9832 b9833 f9829
                    omega
                  have d9834 : (x 2 9).toNat = 1 := by
                    have r9835 : 1 ≤ (x 2 9).toNat + (x 1 1 && x 1 10).toNat + (x 0 2 && x 0 11).toNat + (x (-1) 3 && x (-1) 12).toNat + (x (-2) 4 && x (-2) 13).toNat + (x (-3) 5 && x (-3) 14).toNat + (x (-4) 6).toNat := hcov9 2
                    have b9836 := hb (x (-4) 6)
                    have b9837 := hb (x 2 9)
                    have b9838 := hb (x 1 1 && x 1 10)
                    have b9839 := hb (x 0 2 && x 0 11)
                    have b9840 := hb (x (-1) 3 && x (-1) 12)
                    have b9841 := hb (x (-2) 4 && x (-2) 13)
                    have b9842 := hb (x (-3) 5 && x (-3) 14)
                    clear * - r9835 b9836 b9837 b9838 b9839 b9840 b9841 b9842 d9830 g64 d6453 d9808 g65 d9812
                    omega
                  have d9843 : (x 2 1).toNat = 1 := by
                    have r9844 : (x 2 9).toNat ≤ (x 2 1).toNat := himp _ _ (hp9 2)
                    have b9845 := hb (x 2 1)
                    have b9846 := hb (x 2 9)
                    clear * - r9844 b9845 b9846 d9834
                    omega
                  have d9847 : (x 3 14).toNat = 0 := by
                    have r9848 : (x 3 14).toNat + (x 2 1).toNat = 1 := hd14 3
                    have b9849 := hb (x 2 1)
                    have b9850 := hb (x 3 14)
                    clear * - r9848 b9849 b9850 d9843
                    omega
                  have d9851 : (x 3 1 && x 3 14).toNat = 0 := by
                    have r9852 := hand2 (x 3 1) (x 3 14)
                    have b9853 := hb (x 3 14)
                    have b9854 := hb (x 3 1 && x 3 14)
                    clear * - r9852 b9853 b9854 d9847
                    omega
                  have d9855 : (x 4 13).toNat = 1 := by
                    have r9856 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
                    have b9857 := hb (x 2 2)
                    have b9858 := hb (x 4 13)
                    have b9859 := hb (x 3 1 && x 3 14)
                    clear * - r9856 b9857 b9858 b9859 d9851 g23
                    omega
                  have d9860 : (x 5 12).toNat = 0 := by
                    have r9861 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
                    have e9862 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                    have e9863 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                    have b9864 := hb (x 2 3)
                    have b9865 := hb (x 3 2)
                    have b9866 := hb (x 4 13)
                    have b9867 := hb (x 5 12)
                    clear * - r9861 e9862 e9863 b9864 b9865 b9866 b9867 d9855
                    omega
                  have d9868 : (x 5 3 && x 5 12).toNat = 0 := by
                    have r9869 := hand2 (x 5 3) (x 5 12)
                    have b9870 := hb (x 5 12)
                    have b9871 := hb (x 5 3 && x 5 12)
                    clear * - r9869 b9870 b9871 d9860
                    omega
                  have d9872 : (x 9 2 && x 9 7).toNat = 1 := by
                    have r9873 : 1 ≤ (x 11 5).toNat + (x 10 1 && x 10 6).toNat + (x 9 2 && x 9 7).toNat + (x 8 3 && x 8 8).toNat + (x 7 4 && x 7 9).toNat + (x 6 5 && x 6 10).toNat + (x 5 6 && x 5 11).toNat + (x 4 7 && x 4 12).toNat + (x 3 8 && x 3 13).toNat + (x 2 9 && x 2 14).toNat + (x 1 10).toNat := hcov5 11
                    have b9874 := hb (x 1 10)
                    have b9875 := hb (x 11 5)
                    have b9876 := hb (x 10 1 && x 10 6)
                    have b9877 := hb (x 9 2 && x 9 7)
                    have b9878 := hb (x 8 3 && x 8 8)
                    have b9879 := hb (x 7 4 && x 7 9)
                    have b9880 := hb (x 6 5 && x 6 10)
                    have b9881 := hb (x 5 6 && x 5 11)
                    have b9882 := hb (x 4 7 && x 4 12)
                    have b9883 := hb (x 3 8 && x 3 13)
                    have b9884 := hb (x 2 9 && x 2 14)
                    clear * - r9873 b9874 b9875 b9876 b9877 b9878 b9879 b9880 b9881 b9882 b9883 b9884 d9450 d9482 d9259 d9287 d9315 d9343 g45 g46 d6417 f9829
                    omega
                  have d9885 : (x 9 2).toNat = 1 := by
                    have r9886 := hand1 (x 9 2) (x 9 7)
                    have b9887 := hb (x 9 2)
                    have b9888 := hb (x 9 2 && x 9 7)
                    clear * - r9886 b9887 b9888 d9872
                    omega
                  have d9889 : (x 9 14).toNat = 1 := by
                    have r9890 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
                    have b9891 := hb (x 9 2)
                    have b9892 := hb (x 9 14)
                    clear * - r9890 b9891 b9892 d9885
                    omega
                  have d9893 : (x 8 1).toNat = 0 := by
                    have r9894 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
                    have b9895 := hb (x 8 1)
                    have b9896 := hb (x 9 14)
                    clear * - r9894 b9895 b9896 d9889
                    omega
                  have d9897 : (x 8 1 && x 8 7).toNat = 0 := by
                    have r9898 := hand1 (x 8 1) (x 8 7)
                    have b9899 := hb (x 8 1)
                    have b9900 := hb (x 8 1 && x 8 7)
                    clear * - r9898 b9899 b9900 d9893
                    omega
                  have d9901 : (x 9 6).toNat = 1 := by
                    have r9902 : 1 ≤ (x 9 6).toNat + (x 8 1 && x 8 7).toNat + (x 7 2 && x 7 8).toNat + (x 6 3 && x 6 9).toNat + (x 5 4 && x 5 10).toNat + (x 4 5 && x 4 11).toNat + (x 3 6 && x 3 12).toNat + (x 2 7 && x 2 13).toNat + (x 1 8 && x 1 14).toNat + (x 0 9).toNat := hcov6 9
                    have b9903 := hb (x 0 9)
                    have b9904 := hb (x 9 6)
                    have b9905 := hb (x 8 1 && x 8 7)
                    have b9906 := hb (x 7 2 && x 7 8)
                    have b9907 := hb (x 6 3 && x 6 9)
                    have b9908 := hb (x 5 4 && x 5 10)
                    have b9909 := hb (x 4 5 && x 4 11)
                    have b9910 := hb (x 3 6 && x 3 12)
                    have b9911 := hb (x 2 7 && x 2 13)
                    have b9912 := hb (x 1 8 && x 1 14)
                    clear * - r9902 b9903 b9904 b9905 b9906 b9907 b9908 b9909 b9910 b9911 b9912 d9897 d8848 d8872 d8896 d8916 d6353 d6389 g50 g14
                    omega
                  have d9913 : (x 15 8).toNat = 0 := by
                    have r9914 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
                    have e9915 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                    have e9916 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                    have e9917 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                    have e9918 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                    have e9919 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                    have e9920 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                    have b9921 := hb (x 8 7)
                    have b9922 := hb (x 9 6)
                    have b9923 := hb (x 10 5)
                    have b9924 := hb (x 11 4)
                    have b9925 := hb (x 12 11)
                    have b9926 := hb (x 13 10)
                    have b9927 := hb (x 14 9)
                    have b9928 := hb (x 15 8)
                    clear * - r9914 e9915 e9916 e9917 e9918 e9919 e9920 b9921 b9922 b9923 b9924 b9925 b9926 b9927 b9928 d9901
                    omega
                  have d9929 : (x 14 9).toNat = 0 := by
                    have r9930 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
                    have e9931 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                    have e9932 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                    have e9933 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                    have e9934 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                    have e9935 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                    have e9936 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                    have b9937 := hb (x 8 7)
                    have b9938 := hb (x 9 6)
                    have b9939 := hb (x 10 5)
                    have b9940 := hb (x 11 4)
                    have b9941 := hb (x 12 11)
                    have b9942 := hb (x 13 10)
                    have b9943 := hb (x 14 9)
                    have b9944 := hb (x 15 8)
                    clear * - r9930 e9931 e9932 e9933 e9934 e9935 e9936 b9937 b9938 b9939 b9940 b9941 b9942 b9943 b9944 d9913 d9901
                    omega
                  have d9945 : (x 13 10).toNat = 0 := by
                    have r9946 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
                    have e9947 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                    have e9948 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                    have e9949 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                    have e9950 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                    have e9951 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                    have e9952 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                    have b9953 := hb (x 8 7)
                    have b9954 := hb (x 9 6)
                    have b9955 := hb (x 10 5)
                    have b9956 := hb (x 11 4)
                    have b9957 := hb (x 12 11)
                    have b9958 := hb (x 13 10)
                    have b9959 := hb (x 14 9)
                    have b9960 := hb (x 15 8)
                    clear * - r9946 e9947 e9948 e9949 e9950 e9951 e9952 b9953 b9954 b9955 b9956 b9957 b9958 b9959 b9960 d9913 d9929 d9901
                    omega
                  have d9961 : (x 12 11).toNat = 0 := by
                    have r9962 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
                    have e9963 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                    have e9964 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                    have e9965 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                    have e9966 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                    have e9967 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                    have e9968 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                    have b9969 := hb (x 8 7)
                    have b9970 := hb (x 9 6)
                    have b9971 := hb (x 10 5)
                    have b9972 := hb (x 11 4)
                    have b9973 := hb (x 12 11)
                    have b9974 := hb (x 13 10)
                    have b9975 := hb (x 14 9)
                    have b9976 := hb (x 15 8)
                    clear * - r9962 e9963 e9964 e9965 e9966 e9967 e9968 b9969 b9970 b9971 b9972 b9973 b9974 b9975 b9976 d9913 d9929 d9945 d9901
                    omega
                  have d9977 : (x 12 1 && x 12 11).toNat = 0 := by
                    have r9978 := hand2 (x 12 1) (x 12 11)
                    have b9979 := hb (x 12 11)
                    have b9980 := hb (x 12 1 && x 12 11)
                    clear * - r9978 b9979 b9980 d9961
                    omega
                  have d9981 : (x 8 13).toNat = 0 := by
                    have r9982 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
                    have b9983 := hb (x 8 1)
                    have b9984 := hb (x 8 13)
                    clear * - r9982 b9983 b9984 d9893
                    omega
                  have d9985 : (x 8 5).toNat = 0 := by
                    have r9986 : (x 8 5).toNat ≤ (x 8 13).toNat := himp _ _ (hp5 8)
                    have b9987 := hb (x 8 5)
                    have b9988 := hb (x 8 13)
                    clear * - r9986 b9987 b9988 d9981
                    omega
                  have d9989 : (x 8 9).toNat = 0 := by
                    have r9990 : (x 8 9).toNat ≤ (x 8 1).toNat := himp _ _ (hp9 8)
                    have b9991 := hb (x 8 1)
                    have b9992 := hb (x 8 9)
                    clear * - r9990 b9991 b9992 d9893
                    omega
                  have d9993 : (x 11 12).toNat = 0 := by
                    have r9994 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
                    have e9995 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                    have e9996 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                    have b9997 := hb (x 8 3)
                    have b9998 := hb (x 9 2)
                    have b9999 := hb (x 10 13)
                    have b10000 := hb (x 11 12)
                    clear * - r9994 e9995 e9996 b9997 b9998 b9999 b10000 d9885
                    omega
                  have d10001 : (x 11 2 && x 11 12).toNat = 0 := by
                    have r10002 := hand2 (x 11 2) (x 11 12)
                    have b10003 := hb (x 11 12)
                    have b10004 := hb (x 11 2 && x 11 12)
                    clear * - r10002 b10003 b10004 d9993
                    omega
                  have d10005 : (x 10 13).toNat = 0 := by
                    have r10006 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
                    have e10007 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                    have e10008 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                    have b10009 := hb (x 8 3)
                    have b10010 := hb (x 9 2)
                    have b10011 := hb (x 10 13)
                    have b10012 := hb (x 11 12)
                    clear * - r10006 e10007 e10008 b10009 b10010 b10011 b10012 d9993 d9885
                    omega
                  have d10013 : (x 10 3 && x 10 13).toNat = 0 := by
                    have r10014 := hand2 (x 10 3) (x 10 13)
                    have b10015 := hb (x 10 13)
                    have b10016 := hb (x 10 3 && x 10 13)
                    clear * - r10014 b10015 b10016 d10005
                    omega
                  have d10017 : (x 9 4 && x 9 14).toNat = 1 := by
                    have r10018 : 1 ≤ (x 13 10).toNat + (x 12 1 && x 12 11).toNat + (x 11 2 && x 11 12).toNat + (x 10 3 && x 10 13).toNat + (x 9 4 && x 9 14).toNat + (x 8 5).toNat := hcov10 13
                    have b10019 := hb (x 8 5)
                    have b10020 := hb (x 13 10)
                    have b10021 := hb (x 12 1 && x 12 11)
                    have b10022 := hb (x 11 2 && x 11 12)
                    have b10023 := hb (x 10 3 && x 10 13)
                    have b10024 := hb (x 9 4 && x 9 14)
                    clear * - r10018 b10019 b10020 b10021 b10022 b10023 b10024 d9945 d9977 d10001 d10013 d9985
                    omega
                  have d10025 : (x 9 4).toNat = 1 := by
                    have r10026 := hand1 (x 9 4) (x 9 14)
                    have b10027 := hb (x 9 4)
                    have b10028 := hb (x 9 4 && x 9 14)
                    clear * - r10026 b10027 b10028 d10017
                    omega
                  have d10029 : (x 9 12).toNat = 1 := by
                    have r10030 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
                    have b10031 := hb (x 9 4)
                    have b10032 := hb (x 9 12)
                    clear * - r10030 b10031 b10032 d10025
                    omega
                  have d10033 : (x 7 2).toNat = 0 := by
                    have r10034 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
                    have e10035 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                    have e10036 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                    have b10037 := hb (x 6 3)
                    have b10038 := hb (x 7 2)
                    have b10039 := hb (x 8 13)
                    have b10040 := hb (x 9 12)
                    clear * - r10034 e10035 e10036 b10037 b10038 b10039 b10040 d10029 d9981
                    omega
                  have d10041 : (x 7 10).toNat = 0 := by
                    have r10042 : (x 7 10).toNat ≤ (x 7 2).toNat := himp _ _ (hp10 7)
                    have b10043 := hb (x 7 2)
                    have b10044 := hb (x 7 10)
                    clear * - r10042 b10043 b10044 d10033
                    omega
                  have d10045 : (x 7 1 && x 7 10).toNat = 0 := by
                    have r10046 := hand2 (x 7 1) (x 7 10)
                    have b10047 := hb (x 7 10)
                    have b10048 := hb (x 7 1 && x 7 10)
                    clear * - r10046 b10047 b10048 d10041
                    omega
                  have d10049 : (x 6 2 && x 6 11).toNat = 1 := by
                    have r10050 : 1 ≤ (x 8 9).toNat + (x 7 1 && x 7 10).toNat + (x 6 2 && x 6 11).toNat + (x 5 3 && x 5 12).toNat + (x 4 4 && x 4 13).toNat + (x 3 5 && x 3 14).toNat + (x 2 6).toNat := hcov9 8
                    have b10051 := hb (x 2 6)
                    have b10052 := hb (x 8 9)
                    have b10053 := hb (x 7 1 && x 7 10)
                    have b10054 := hb (x 6 2 && x 6 11)
                    have b10055 := hb (x 5 3 && x 5 12)
                    have b10056 := hb (x 4 4 && x 4 13)
                    have b10057 := hb (x 3 5 && x 3 14)
                    clear * - r10050 b10051 b10052 b10053 b10054 b10055 b10056 b10057 d9989 d10045 d9868 g68 g69 d6421
                    omega
                  have d10058 : (x 6 11).toNat = 1 := by
                    have r10059 := hand2 (x 6 2) (x 6 11)
                    have b10060 := hb (x 6 11)
                    have b10061 := hb (x 6 2 && x 6 11)
                    clear * - r10059 b10060 b10061 d10049
                    omega
                  have d10062 : (x 6 3).toNat = 1 := by
                    have r10063 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
                    have b10064 := hb (x 6 3)
                    have b10065 := hb (x 6 11)
                    clear * - r10063 b10064 b10065 d10058
                    omega
                  have r10066 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
                  have e10067 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                  have e10068 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                  have b10069 := hb (x 6 3)
                  have b10070 := hb (x 7 2)
                  have b10071 := hb (x 8 13)
                  have b10072 := hb (x 9 12)
                  linarith only [r10066, e10067, e10068, b10069, b10070, b10071, b10072, d10029, d9981, d10033, d10062]
                · have f10073 : (x 1 10).toNat = 1 := by rw [h9828]; rfl
                  cases h10074 : x (-1) 12
                  · have f10075 : (x (-1) 12).toNat = 0 := by rw [h10074]; rfl
                    cases h10076 : x (-1) 14
                    · have f10077 : (x (-1) 14).toNat = 0 := by rw [h10076]; rfl
                      cases h10078 : x 2 1
                      · have f10079 : (x 2 1).toNat = 0 := by rw [h10078]; rfl
                        have d10080 : (x 3 14).toNat = 1 := by
                          have r10081 : (x 3 14).toNat + (x 2 1).toNat = 1 := hd14 3
                          have b10082 := hb (x 2 1)
                          have b10083 := hb (x 3 14)
                          clear * - r10081 b10082 b10083 f10079
                          omega
                        have r10084 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := hcount 12
                        have r10085 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := hcount 14
                        have r10086 : (x 16 1).toNat + (x 15 2).toNat + (x 14 3).toNat + (x 13 4).toNat + (x 12 5).toNat + (x 11 6).toNat + (x 10 7).toNat + (x 9 8).toNat + (x 8 9).toNat + (x 7 10).toNat + (x 6 11).toNat + (x 5 12).toNat + (x 4 13).toNat + (x 3 14).toNat = 3 := hcount 17
                        have r10087 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
                        have e10088 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                        have e10089 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                        have e10090 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                        have e10091 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                        have e10092 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                        have e10093 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                        have r10094 : 1 ≤ (x 9 5).toNat + (x 8 1 && x 8 6).toNat + (x 7 2 && x 7 7).toNat + (x 6 3 && x 6 8).toNat + (x 5 4 && x 5 9).toNat + (x 4 5 && x 4 10).toNat + (x 3 6 && x 3 11).toNat + (x 2 7 && x 2 12).toNat + (x 1 8 && x 1 13).toNat + (x 0 9 && x 0 14).toNat + (x (-1) 10).toNat := hcov5 9
                        have r10095 : 1 ≤ (x 12 5).toNat + (x 11 1 && x 11 6).toNat + (x 10 2 && x 10 7).toNat + (x 9 3 && x 9 8).toNat + (x 8 4 && x 8 9).toNat + (x 7 5 && x 7 10).toNat + (x 6 6 && x 6 11).toNat + (x 5 7 && x 5 12).toNat + (x 4 8 && x 4 13).toNat + (x 3 9 && x 3 14).toNat + (x 2 10).toNat := hcov5 12
                        have r10096 : 1 ≤ (x 9 6).toNat + (x 8 1 && x 8 7).toNat + (x 7 2 && x 7 8).toNat + (x 6 3 && x 6 9).toNat + (x 5 4 && x 5 10).toNat + (x 4 5 && x 4 11).toNat + (x 3 6 && x 3 12).toNat + (x 2 7 && x 2 13).toNat + (x 1 8 && x 1 14).toNat + (x 0 9).toNat := hcov6 9
                        have r10097 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := hcov10 7
                        have r10098 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := hcov11 12
                        have r10099 : 1 ≤ (x 14 11).toNat + (x 13 1 && x 13 12).toNat + (x 12 2 && x 12 13).toNat + (x 11 3 && x 11 14).toNat + (x 10 4).toNat := hcov11 14
                        have r10100 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
                        have r10101 := hand2 (x 8 1) (x 8 6)
                        have r10102 := hand2 (x 7 2) (x 7 7)
                        have r10103 := hand2 (x 11 1) (x 11 6)
                        have r10104 := hand2 (x 10 2) (x 10 7)
                        have r10105 := hand2 (x 9 3) (x 9 8)
                        have r10106 := hand2 (x 8 4) (x 8 9)
                        have r10107 := hand1 (x 7 5) (x 7 10)
                        have r10108 := hand1 (x 6 6) (x 6 11)
                        have r10109 := hand1 (x 5 7) (x 5 12)
                        have r10110 := hand2 (x 8 1) (x 8 7)
                        have r10111 := hand2 (x 6 1) (x 6 11)
                        have r10112 := hand2 (x 5 2) (x 5 12)
                        have r10113 := hand2 (x 4 3) (x 4 13)
                        have r10114 := hand1 (x 11 1) (x 11 12)
                        have r10115 := hand1 (x 10 2) (x 10 13)
                        have r10116 := hand1 (x 9 3) (x 9 14)
                        have r10117 := hand1 (x 13 1) (x 13 12)
                        have r10118 := hand1 (x 12 2) (x 12 13)
                        have r10119 := hand1 (x 11 3) (x 11 14)
                        have b10120 := hb (x (-2) 14)
                        have b10121 := hb (x (-1) 10)
                        have b10122 := hb (x (-1) 13)
                        have b10123 := hb (x 0 9)
                        have b10124 := hb (x 0 12)
                        have b10125 := hb (x 0 14)
                        have b10126 := hb (x 1 11)
                        have b10127 := hb (x 1 13)
                        have b10128 := hb (x 2 5)
                        have b10129 := hb (x 2 10)
                        have b10130 := hb (x 2 12)
                        have b10131 := hb (x 3 9)
                        have b10132 := hb (x 3 11)
                        have b10133 := hb (x 3 14)
                        have b10134 := hb (x 4 8)
                        have b10135 := hb (x 4 10)
                        have b10136 := hb (x 4 13)
                        have b10137 := hb (x 5 7)
                        have b10138 := hb (x 5 9)
                        have b10139 := hb (x 5 12)
                        have b10140 := hb (x 6 6)
                        have b10141 := hb (x 6 8)
                        have b10142 := hb (x 6 11)
                        have b10143 := hb (x 7 5)
                        have b10144 := hb (x 7 7)
                        have b10145 := hb (x 7 10)
                        have b10146 := hb (x 8 4)
                        have b10147 := hb (x 8 6)
                        have b10148 := hb (x 8 7)
                        have b10149 := hb (x 8 9)
                        have b10150 := hb (x 9 3)
                        have b10151 := hb (x 9 5)
                        have b10152 := hb (x 9 6)
                        have b10153 := hb (x 9 8)
                        have b10154 := hb (x 10 2)
                        have b10155 := hb (x 10 4)
                        have b10156 := hb (x 10 5)
                        have b10157 := hb (x 10 7)
                        have b10158 := hb (x 11 1)
                        have b10159 := hb (x 11 3)
                        have b10160 := hb (x 11 4)
                        have b10161 := hb (x 11 6)
                        have b10162 := hb (x 12 2)
                        have b10163 := hb (x 12 5)
                        have b10164 := hb (x 12 11)
                        have b10165 := hb (x 13 1)
                        have b10166 := hb (x 13 4)
                        have b10167 := hb (x 13 10)
                        have b10168 := hb (x 14 3)
                        have b10169 := hb (x 14 9)
                        have b10170 := hb (x 14 11)
                        have b10171 := hb (x 15 2)
                        have b10172 := hb (x 15 8)
                        have b10173 := hb (x 16 1)
                        have b10174 := hb (x 8 1 && x 8 6)
                        have b10175 := hb (x 7 2 && x 7 7)
                        have b10176 := hb (x 6 3 && x 6 8)
                        have b10177 := hb (x 5 4 && x 5 9)
                        have b10178 := hb (x 4 5 && x 4 10)
                        have b10179 := hb (x 3 6 && x 3 11)
                        have b10180 := hb (x 2 7 && x 2 12)
                        have b10181 := hb (x 1 8 && x 1 13)
                        have b10182 := hb (x 0 9 && x 0 14)
                        have b10183 := hb (x 11 1 && x 11 6)
                        have b10184 := hb (x 10 2 && x 10 7)
                        have b10185 := hb (x 9 3 && x 9 8)
                        have b10186 := hb (x 8 4 && x 8 9)
                        have b10187 := hb (x 7 5 && x 7 10)
                        have b10188 := hb (x 6 6 && x 6 11)
                        have b10189 := hb (x 5 7 && x 5 12)
                        have b10190 := hb (x 4 8 && x 4 13)
                        have b10191 := hb (x 3 9 && x 3 14)
                        have b10192 := hb (x 8 1 && x 8 7)
                        have b10193 := hb (x 7 2 && x 7 8)
                        have b10194 := hb (x 6 3 && x 6 9)
                        have b10195 := hb (x 5 4 && x 5 10)
                        have b10196 := hb (x 4 5 && x 4 11)
                        have b10197 := hb (x 3 6 && x 3 12)
                        have b10198 := hb (x 2 7 && x 2 13)
                        have b10199 := hb (x 1 8 && x 1 14)
                        have b10200 := hb (x 6 1 && x 6 11)
                        have b10201 := hb (x 5 2 && x 5 12)
                        have b10202 := hb (x 4 3 && x 4 13)
                        have b10203 := hb (x 3 4 && x 3 14)
                        have b10204 := hb (x 11 1 && x 11 12)
                        have b10205 := hb (x 10 2 && x 10 13)
                        have b10206 := hb (x 9 3 && x 9 14)
                        have b10207 := hb (x 13 1 && x 13 12)
                        have b10208 := hb (x 12 2 && x 12 13)
                        have b10209 := hb (x 11 3 && x 11 14)
                        linarith only [r10084, r10085, r10086, r10087, e10088, e10089, e10090, e10091, e10092, e10093, r10094, r10095, r10096, r10097, r10098, r10099, r10100, r10101, r10102, r10103, r10104, r10105, r10106, r10107, r10108, r10109, r10110, r10111, r10112, r10113, r10114, r10115, r10116, r10117, r10118, r10119, b10120, b10121, b10122, b10123, b10124, b10125, b10126, b10127, b10128, b10129, b10130, b10131, b10132, b10133, b10134, b10135, b10136, b10137, b10138, b10139, b10140, b10141, b10142, b10143, b10144, b10145, b10146, b10147, b10148, b10149, b10150, b10151, b10152, b10153, b10154, b10155, b10156, b10157, b10158, b10159, b10160, b10161, b10162, b10163, b10164, b10165, b10166, b10167, b10168, b10169, b10170, b10171, b10172, b10173, b10174, b10175, b10176, b10177, b10178, b10179, b10180, b10181, b10182, b10183, b10184, b10185, b10186, b10187, b10188, b10189, b10190, b10191, b10192, b10193, b10194, b10195, b10196, b10197, b10198, b10199, b10200, b10201, b10202, b10203, b10204, b10205, b10206, b10207, b10208, b10209, g4, d6315, g7, g14, g17, g19, d9764, d6319, d6393, g24, d6429, d9788, d7396, d10080, d9768, d7372, d7344, d7316, d7340, d7368, d7392, d7412, d6437, g43, g44, d9784, d9804, d8848, d8872, d8896, d8916, d6353, d6389, g50, d6361]
                      · have f10210 : (x 2 1).toNat = 1 := by rw [h10078]; rfl
                        have d10211 : (x 3 14).toNat = 0 := by
                          have r10212 : (x 3 14).toNat + (x 2 1).toNat = 1 := hd14 3
                          have b10213 := hb (x 2 1)
                          have b10214 := hb (x 3 14)
                          clear * - r10212 b10213 b10214 f10210
                          omega
                        have d10215 : (x 3 1 && x 3 14).toNat = 0 := by
                          have r10216 := hand2 (x 3 1) (x 3 14)
                          have b10217 := hb (x 3 14)
                          have b10218 := hb (x 3 1 && x 3 14)
                          clear * - r10216 b10217 b10218 d10211
                          omega
                        have d10219 : (x 3 6).toNat = 0 := by
                          have r10220 : (x 3 6).toNat ≤ (x 3 14).toNat := himp _ _ (hp6 3)
                          have b10221 := hb (x 3 6)
                          have b10222 := hb (x 3 14)
                          clear * - r10220 b10221 b10222 d10211
                          omega
                        have d10223 : (x 3 2).toNat = 0 := by
                          have r10224 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
                          have b10225 := hb (x 3 2)
                          have b10226 := hb (x 3 14)
                          clear * - r10224 b10225 b10226 d10211
                          omega
                        have d10227 : (x 4 13).toNat = 1 := by
                          have r10228 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
                          have b10229 := hb (x 2 2)
                          have b10230 := hb (x 4 13)
                          have b10231 := hb (x 3 1 && x 3 14)
                          clear * - r10228 b10229 b10230 b10231 d10215 g23
                          omega
                        have d10232 : (x 5 12).toNat = 0 := by
                          have r10233 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
                          have e10234 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                          have e10235 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                          have b10236 := hb (x 2 3)
                          have b10237 := hb (x 3 2)
                          have b10238 := hb (x 4 13)
                          have b10239 := hb (x 5 12)
                          clear * - r10233 e10234 e10235 b10236 b10237 b10238 b10239 d10227 d10223
                          omega
                        have d10240 : (x 5 3 && x 5 12).toNat = 0 := by
                          have r10241 := hand2 (x 5 3) (x 5 12)
                          have b10242 := hb (x 5 12)
                          have b10243 := hb (x 5 3 && x 5 12)
                          clear * - r10241 b10242 b10243 d10232
                          omega
                        have d10244 : (x 5 4).toNat = 0 := by
                          have r10245 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
                          have b10246 := hb (x 5 4)
                          have b10247 := hb (x 5 12)
                          clear * - r10245 b10246 b10247 d10232
                          omega
                        have r10248 : (x 8 1).toNat + (x 7 2).toNat + (x 6 3).toNat + (x 5 4).toNat + (x 4 5).toNat + (x 3 6).toNat + (x 2 7).toNat + (x 1 8).toNat + (x 0 9).toNat + (x (-1) 10).toNat + (x (-2) 11).toNat + (x (-3) 12).toNat + (x (-4) 13).toNat + (x (-5) 14).toNat = 3 := hcount 9
                        have r10249 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := hcount 12
                        have r10250 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := hcount 14
                        have r10251 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := hd8 9
                        have e10252 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                        have e10253 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                        have e10254 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                        have e10255 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                        have e10256 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                        have e10257 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                        have r10258 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := hd8 13
                        have e10259 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                        have e10260 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                        have e10261 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                        have e10262 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                        have e10263 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                        have e10264 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                        have r10265 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
                        have e10266 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                        have e10267 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                        have e10268 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                        have e10269 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                        have e10270 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                        have e10271 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                        have r10272 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := hd12 (-3)
                        have e10273 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                        have e10274 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                        have r10275 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
                        have e10276 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                        have e10277 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                        have r10278 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
                        have e10279 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
                        have e10280 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
                        have r10281 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
                        have r10282 : 1 ≤ (x 9 4).toNat + (x 8 1 && x 8 5).toNat + (x 7 2 && x 7 6).toNat + (x 6 3 && x 6 7).toNat + (x 5 4 && x 5 8).toNat + (x 4 5 && x 4 9).toNat + (x 3 6 && x 3 10).toNat + (x 2 7 && x 2 11).toNat + (x 1 8 && x 1 12).toNat + (x 0 9 && x 0 13).toNat + (x (-1) 10 && x (-1) 14).toNat + (x (-2) 11).toNat := hcov4 9
                        have e10283 : (x 8 1 && x 8 5).toNat = (x 8 5).toNat := handr _ _ (fun h => hp13 8 (hp5 8 (h)))
                        have e10284 : (x (-1) 10 && x (-1) 14).toNat = (x (-1) 10).toNat := handl _ _ (fun h => hp2 (-1) (hp10 (-1) (h)))
                        have r10285 : 1 ≤ (x 9 5).toNat + (x 8 1 && x 8 6).toNat + (x 7 2 && x 7 7).toNat + (x 6 3 && x 6 8).toNat + (x 5 4 && x 5 9).toNat + (x 4 5 && x 4 10).toNat + (x 3 6 && x 3 11).toNat + (x 2 7 && x 2 12).toNat + (x 1 8 && x 1 13).toNat + (x 0 9 && x 0 14).toNat + (x (-1) 10).toNat := hcov5 9
                        have r10286 : 1 ≤ (x 9 6).toNat + (x 8 1 && x 8 7).toNat + (x 7 2 && x 7 8).toNat + (x 6 3 && x 6 9).toNat + (x 5 4 && x 5 10).toNat + (x 4 5 && x 4 11).toNat + (x 3 6 && x 3 12).toNat + (x 2 7 && x 2 13).toNat + (x 1 8 && x 1 14).toNat + (x 0 9).toNat := hcov6 9
                        have r10287 : 1 ≤ (x 8 9).toNat + (x 7 1 && x 7 10).toNat + (x 6 2 && x 6 11).toNat + (x 5 3 && x 5 12).toNat + (x 4 4 && x 4 13).toNat + (x 3 5 && x 3 14).toNat + (x 2 6).toNat := hcov9 8
                        have r10288 : 1 ≤ (x 12 9).toNat + (x 11 1 && x 11 10).toNat + (x 10 2 && x 10 11).toNat + (x 9 3 && x 9 12).toNat + (x 8 4 && x 8 13).toNat + (x 7 5 && x 7 14).toNat + (x 6 6).toNat := hcov9 12
                        have r10289 : 1 ≤ (x 15 9).toNat + (x 14 1 && x 14 10).toNat + (x 13 2 && x 13 11).toNat + (x 12 3 && x 12 12).toNat + (x 11 4 && x 11 13).toNat + (x 10 5 && x 10 14).toNat + (x 9 6).toNat := hcov9 15
                        have r10290 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := hcov11 12
                        have r10291 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
                        have r10292 : (x 9 6).toNat ≤ (x 9 14).toNat := himp _ _ (hp6 9)
                        have r10293 := hand2 (x 7 2) (x 7 6)
                        have r10294 := hand2 (x 6 3) (x 6 7)
                        have r10295 := hand2 (x 8 1) (x 8 6)
                        have r10296 := hand2 (x 7 2) (x 7 7)
                        have r10297 := hand2 (x 8 1) (x 8 7)
                        have r10298 := hand2 (x 7 1) (x 7 10)
                        have r10299 := hand2 (x 6 2) (x 6 11)
                        have r10300 := hand2 (x 11 1) (x 11 10)
                        have r10301 := hand2 (x 10 2) (x 10 11)
                        have r10302 := hand2 (x 9 3) (x 9 12)
                        have r10303 := hand2 (x 8 4) (x 8 13)
                        have r10304 := hand1 (x 7 5) (x 7 14)
                        have r10305 := hand1 (x 12 3) (x 12 12)
                        have r10306 := hand1 (x 11 4) (x 11 13)
                        have r10307 := hand1 (x 10 5) (x 10 14)
                        have r10308 := hand1 (x 11 1) (x 11 12)
                        have r10309 := hand1 (x 10 2) (x 10 13)
                        have r10310 := hand1 (x 9 3) (x 9 14)
                        have r10311 := hand1 (x 13 1) (x 13 14)
                        have b10312 := hb (x (-6) 3)
                        have b10313 := hb (x (-5) 2)
                        have b10314 := hb (x (-5) 14)
                        have b10315 := hb (x (-4) 13)
                        have b10316 := hb (x (-3) 12)
                        have b10317 := hb (x (-2) 11)
                        have b10318 := hb (x (-2) 14)
                        have b10319 := hb (x (-1) 10)
                        have b10320 := hb (x (-1) 13)
                        have b10321 := hb (x 0 9)
                        have b10322 := hb (x 0 12)
                        have b10323 := hb (x 0 14)
                        have b10324 := hb (x 1 8)
                        have b10325 := hb (x 1 11)
                        have b10326 := hb (x 1 13)
                        have b10327 := hb (x 2 6)
                        have b10328 := hb (x 2 7)
                        have b10329 := hb (x 2 10)
                        have b10330 := hb (x 2 12)
                        have b10331 := hb (x 3 6)
                        have b10332 := hb (x 3 9)
                        have b10333 := hb (x 3 11)
                        have b10334 := hb (x 4 5)
                        have b10335 := hb (x 4 8)
                        have b10336 := hb (x 4 10)
                        have b10337 := hb (x 5 4)
                        have b10338 := hb (x 5 7)
                        have b10339 := hb (x 5 9)
                        have b10340 := hb (x 6 3)
                        have b10341 := hb (x 6 6)
                        have b10342 := hb (x 6 7)
                        have b10343 := hb (x 6 8)
                        have b10344 := hb (x 6 11)
                        have b10345 := hb (x 7 2)
                        have b10346 := hb (x 7 5)
                        have b10347 := hb (x 7 6)
                        have b10348 := hb (x 7 7)
                        have b10349 := hb (x 7 10)
                        have b10350 := hb (x 8 1)
                        have b10351 := hb (x 8 4)
                        have b10352 := hb (x 8 5)
                        have b10353 := hb (x 8 6)
                        have b10354 := hb (x 8 7)
                        have b10355 := hb (x 8 9)
                        have b10356 := hb (x 8 13)
                        have b10357 := hb (x 9 3)
                        have b10358 := hb (x 9 4)
                        have b10359 := hb (x 9 5)
                        have b10360 := hb (x 9 6)
                        have b10361 := hb (x 9 8)
                        have b10362 := hb (x 9 12)
                        have b10363 := hb (x 9 14)
                        have b10364 := hb (x 10 2)
                        have b10365 := hb (x 10 4)
                        have b10366 := hb (x 10 5)
                        have b10367 := hb (x 10 11)
                        have b10368 := hb (x 11 1)
                        have b10369 := hb (x 11 3)
                        have b10370 := hb (x 11 4)
                        have b10371 := hb (x 11 10)
                        have b10372 := hb (x 12 2)
                        have b10373 := hb (x 12 3)
                        have b10374 := hb (x 12 9)
                        have b10375 := hb (x 12 11)
                        have b10376 := hb (x 13 1)
                        have b10377 := hb (x 13 2)
                        have b10378 := hb (x 13 8)
                        have b10379 := hb (x 13 10)
                        have b10380 := hb (x 14 9)
                        have b10381 := hb (x 14 13)
                        have b10382 := hb (x 15 8)
                        have b10383 := hb (x 15 9)
                        have b10384 := hb (x 15 12)
                        have b10385 := hb (x 7 2 && x 7 6)
                        have b10386 := hb (x 6 3 && x 6 7)
                        have b10387 := hb (x 5 4 && x 5 8)
                        have b10388 := hb (x 4 5 && x 4 9)
                        have b10389 := hb (x 3 6 && x 3 10)
                        have b10390 := hb (x 2 7 && x 2 11)
                        have b10391 := hb (x 1 8 && x 1 12)
                        have b10392 := hb (x 0 9 && x 0 13)
                        have b10393 := hb (x 8 1 && x 8 6)
                        have b10394 := hb (x 7 2 && x 7 7)
                        have b10395 := hb (x 6 3 && x 6 8)
                        have b10396 := hb (x 5 4 && x 5 9)
                        have b10397 := hb (x 4 5 && x 4 10)
                        have b10398 := hb (x 3 6 && x 3 11)
                        have b10399 := hb (x 2 7 && x 2 12)
                        have b10400 := hb (x 1 8 && x 1 13)
                        have b10401 := hb (x 0 9 && x 0 14)
                        have b10402 := hb (x 8 1 && x 8 7)
                        have b10403 := hb (x 7 2 && x 7 8)
                        have b10404 := hb (x 6 3 && x 6 9)
                        have b10405 := hb (x 5 4 && x 5 10)
                        have b10406 := hb (x 4 5 && x 4 11)
                        have b10407 := hb (x 3 6 && x 3 12)
                        have b10408 := hb (x 2 7 && x 2 13)
                        have b10409 := hb (x 1 8 && x 1 14)
                        have b10410 := hb (x 7 1 && x 7 10)
                        have b10411 := hb (x 6 2 && x 6 11)
                        have b10412 := hb (x 5 3 && x 5 12)
                        have b10413 := hb (x 4 4 && x 4 13)
                        have b10414 := hb (x 3 5 && x 3 14)
                        have b10415 := hb (x 11 1 && x 11 10)
                        have b10416 := hb (x 10 2 && x 10 11)
                        have b10417 := hb (x 9 3 && x 9 12)
                        have b10418 := hb (x 8 4 && x 8 13)
                        have b10419 := hb (x 7 5 && x 7 14)
                        have b10420 := hb (x 14 1 && x 14 10)
                        have b10421 := hb (x 13 2 && x 13 11)
                        have b10422 := hb (x 12 3 && x 12 12)
                        have b10423 := hb (x 11 4 && x 11 13)
                        have b10424 := hb (x 10 5 && x 10 14)
                        have b10425 := hb (x 11 1 && x 11 12)
                        have b10426 := hb (x 10 2 && x 10 13)
                        have b10427 := hb (x 9 3 && x 9 14)
                        have b10428 := hb (x 13 1 && x 13 14)
                        linarith only [r10248, r10249, r10250, r10251, e10252, e10253, e10254, e10255, e10256, e10257, r10258, e10259, e10260, e10261, e10262, e10263, e10264, r10265, e10266, e10267, e10268, e10269, e10270, e10271, r10272, e10273, e10274, r10275, e10276, e10277, r10278, e10279, e10280, r10281, r10282, e10283, e10284, r10285, r10286, r10287, r10288, r10289, r10290, r10291, r10292, r10293, r10294, r10295, r10296, r10297, r10298, r10299, r10300, r10301, r10302, r10303, r10304, r10305, r10306, r10307, r10308, r10309, r10310, r10311, b10312, b10313, b10314, b10315, b10316, b10317, b10318, b10319, b10320, b10321, b10322, b10323, b10324, b10325, b10326, b10327, b10328, b10329, b10330, b10331, b10332, b10333, b10334, b10335, b10336, b10337, b10338, b10339, b10340, b10341, b10342, b10343, b10344, b10345, b10346, b10347, b10348, b10349, b10350, b10351, b10352, b10353, b10354, b10355, b10356, b10357, b10358, b10359, b10360, b10361, b10362, b10363, b10364, b10365, b10366, b10367, b10368, b10369, b10370, b10371, b10372, b10373, b10374, b10375, b10376, b10377, b10378, b10379, b10380, b10381, b10382, b10383, b10384, b10385, b10386, b10387, b10388, b10389, b10390, b10391, b10392, b10393, b10394, b10395, b10396, b10397, b10398, b10399, b10400, b10401, b10402, b10403, b10404, b10405, b10406, b10407, b10408, b10409, b10410, b10411, b10412, b10413, b10414, b10415, b10416, b10417, b10418, b10419, b10420, b10421, b10422, b10423, b10424, b10425, b10426, b10427, b10428, d6477, g4, d6315, g7, g14, g17, g19, g21, d9764, d6319, d6421, g24, d6429, d10219, d9788, d7396, d9768, d7372, d10244, d7344, d7316, d9374, d6505, d6525, d6545, d6565, g38, g39, d7340, d7368, d7392, d7412, d6437, g43, g44, d8848, d8872, d8896, d8916, d6353, d6389, g50, d10240, g68, g69, d9406, d9430]
                    · have f10429 : (x (-1) 14).toNat = 1 := by rw [h10076]; rfl
                      have d10430 : (x (-2) 1).toNat = 0 := by
                        have r10431 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := hd14 (-1)
                        have b10432 := hb (x (-2) 1)
                        have b10433 := hb (x (-1) 14)
                        clear * - r10431 b10432 b10433 f10429
                        omega
                      have d10434 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
                        have r10435 := hand1 (x (-2) 1) (x (-2) 14)
                        have b10436 := hb (x (-2) 1)
                        have b10437 := hb (x (-2) 1 && x (-2) 14)
                        clear * - r10435 b10436 b10437 d10430
                        omega
                      have d10438 : (x (-2) 13).toNat = 0 := by
                        have r10439 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
                        have b10440 := hb (x (-2) 1)
                        have b10441 := hb (x (-2) 13)
                        clear * - r10439 b10440 b10441 d10430
                        omega
                      have d10442 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
                        have r10443 := hand2 (x (-2) 2) (x (-2) 13)
                        have b10444 := hb (x (-2) 13)
                        have b10445 := hb (x (-2) 2 && x (-2) 13)
                        clear * - r10443 b10444 b10445 d10438
                        omega
                      have d10446 : (x (-3) 2).toNat = 1 := by
                        have r10447 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := hcov13 (-1)
                        have b10448 := hb (x (-3) 2)
                        have b10449 := hb (x (-1) 13)
                        have b10450 := hb (x (-2) 1 && x (-2) 14)
                        clear * - r10447 b10448 b10449 b10450 g7 d10434
                        omega
                      have d10451 : (x (-3) 14).toNat = 1 := by
                        have r10452 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
                        have b10453 := hb (x (-3) 2)
                        have b10454 := hb (x (-3) 14)
                        clear * - r10452 b10453 b10454 d10446
                        omega
                      have d10455 : (x (-4) 1).toNat = 0 := by
                        have r10456 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := hd14 (-3)
                        have b10457 := hb (x (-4) 1)
                        have b10458 := hb (x (-3) 14)
                        clear * - r10456 b10457 b10458 d10451
                        omega
                      have d10459 : (x (-4) 13).toNat = 0 := by
                        have r10460 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
                        have b10461 := hb (x (-4) 1)
                        have b10462 := hb (x (-4) 13)
                        clear * - r10460 b10461 b10462 d10455
                        omega
                      have d10463 : (x (-4) 2).toNat = 1 := by
                        have r10464 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := hcov13 (-2)
                        have b10465 := hb (x (-4) 2)
                        have b10466 := hb (x (-2) 13)
                        have b10467 := hb (x (-3) 1 && x (-3) 14)
                        clear * - r10464 b10465 b10466 b10467 d10438 g82
                        omega
                      have d10468 : (x (-4) 14).toNat = 1 := by
                        have r10469 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
                        have b10470 := hb (x (-4) 2)
                        have b10471 := hb (x (-4) 14)
                        clear * - r10469 b10470 b10471 d10463
                        omega
                      have d10472 : (x (-5) 1).toNat = 0 := by
                        have r10473 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := hd14 (-4)
                        have b10474 := hb (x (-5) 1)
                        have b10475 := hb (x (-4) 14)
                        clear * - r10473 b10474 b10475 d10468
                        omega
                      have d10476 : (x (-5) 1 && x (-5) 14).toNat = 0 := by
                        have r10477 := hand1 (x (-5) 1) (x (-5) 14)
                        have b10478 := hb (x (-5) 1)
                        have b10479 := hb (x (-5) 1 && x (-5) 14)
                        clear * - r10477 b10478 b10479 d10472
                        omega
                      have d10480 : (x (-5) 13).toNat = 0 := by
                        have r10481 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
                        have b10482 := hb (x (-5) 1)
                        have b10483 := hb (x (-5) 13)
                        clear * - r10481 b10482 b10483 d10472
                        omega
                      have d10484 : (x (-6) 2).toNat = 1 := by
                        have r10485 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := hcov13 (-4)
                        have b10486 := hb (x (-6) 2)
                        have b10487 := hb (x (-4) 13)
                        have b10488 := hb (x (-5) 1 && x (-5) 14)
                        clear * - r10485 b10486 b10487 b10488 d10459 d10476
                        omega
                      have d10489 : (x (-4) 12).toNat = 0 := by
                        have r10490 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := hd12 (-4)
                        have e10491 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                        have e10492 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                        have b10493 := hb (x (-7) 3)
                        have b10494 := hb (x (-6) 2)
                        have b10495 := hb (x (-5) 13)
                        have b10496 := hb (x (-4) 12)
                        clear * - r10490 e10491 e10492 b10493 b10494 b10495 b10496 d10480 d10484
                        omega
                      have d10497 : (x (-4) 4).toNat = 0 := by
                        have r10498 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
                        have b10499 := hb (x (-4) 4)
                        have b10500 := hb (x (-4) 12)
                        clear * - r10498 b10499 b10500 d10489
                        omega
                      have r10501 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := hcov11 0
                      have b10502 := hb (x (-4) 4)
                      have b10503 := hb (x 0 11)
                      have b10504 := hb (x (-1) 1 && x (-1) 12)
                      have b10505 := hb (x (-2) 2 && x (-2) 13)
                      have b10506 := hb (x (-3) 3 && x (-3) 14)
                      linarith only [r10501, b10502, b10503, b10504, b10505, b10506, g16, g78, d10442, g79, d10497]
                  · have f10507 : (x (-1) 12).toNat = 1 := by rw [h10074]; rfl
                    have d10508 : (x (-2) 13).toNat = 0 := by
                      have r10509 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
                      have e10510 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                      have e10511 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                      have b10512 := hb (x (-4) 3)
                      have b10513 := hb (x (-3) 2)
                      have b10514 := hb (x (-2) 13)
                      have b10515 := hb (x (-1) 12)
                      clear * - r10509 e10510 e10511 b10512 b10513 b10514 b10515 f10507
                      omega
                    have d10516 : (x (-4) 2).toNat = 1 := by
                      have r10517 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := hcov13 (-2)
                      have b10518 := hb (x (-4) 2)
                      have b10519 := hb (x (-2) 13)
                      have b10520 := hb (x (-3) 1 && x (-3) 14)
                      clear * - r10517 b10518 b10519 b10520 d10508 g82
                      omega
                    have d10521 : (x (-4) 14).toNat = 1 := by
                      have r10522 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
                      have b10523 := hb (x (-4) 2)
                      have b10524 := hb (x (-4) 14)
                      clear * - r10522 b10523 b10524 d10516
                      omega
                    have d10525 : (x (-5) 1).toNat = 0 := by
                      have r10526 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := hd14 (-4)
                      have b10527 := hb (x (-5) 1)
                      have b10528 := hb (x (-4) 14)
                      clear * - r10526 b10527 b10528 d10521
                      omega
                    have d10529 : (x (-5) 13).toNat = 0 := by
                      have r10530 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
                      have b10531 := hb (x (-5) 1)
                      have b10532 := hb (x (-5) 13)
                      clear * - r10530 b10531 b10532 d10525
                      omega
                    have d10533 : (x (-3) 2).toNat = 0 := by
                      have r10534 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
                      have e10535 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                      have e10536 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                      have b10537 := hb (x (-4) 3)
                      have b10538 := hb (x (-3) 2)
                      have b10539 := hb (x (-2) 13)
                      have b10540 := hb (x (-1) 12)
                      clear * - r10534 e10535 e10536 b10537 b10538 b10539 b10540 f10507 d10508
                      omega
                    have d10541 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
                      have r10542 := hand1 (x (-3) 2) (x (-3) 12)
                      have b10543 := hb (x (-3) 2)
                      have b10544 := hb (x (-3) 2 && x (-3) 12)
                      clear * - r10542 b10543 b10544 d10533
                      omega
                    have d10545 : (x (-4) 3).toNat = 0 := by
                      have r10546 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
                      have e10547 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                      have e10548 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                      have b10549 := hb (x (-4) 3)
                      have b10550 := hb (x (-3) 2)
                      have b10551 := hb (x (-2) 13)
                      have b10552 := hb (x (-1) 12)
                      clear * - r10546 e10547 e10548 b10549 b10550 b10551 b10552 f10507 d10508 d10533
                      omega
                    have d10553 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
                      have r10554 := hand1 (x (-4) 3) (x (-4) 14)
                      have b10555 := hb (x (-4) 3)
                      have b10556 := hb (x (-4) 3 && x (-4) 14)
                      clear * - r10554 b10555 b10556 d10545
                      omega
                    have d10557 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
                      have r10558 := hand1 (x (-4) 3) (x (-4) 13)
                      have b10559 := hb (x (-4) 3)
                      have b10560 := hb (x (-4) 3 && x (-4) 13)
                      clear * - r10558 b10559 b10560 d10545
                      omega
                    have d10561 : (x (-2) 12).toNat = 0 := by
                      have r10562 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := hd12 (-2)
                      have e10563 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                      have e10564 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                      have b10565 := hb (x (-5) 3)
                      have b10566 := hb (x (-4) 2)
                      have b10567 := hb (x (-3) 13)
                      have b10568 := hb (x (-2) 12)
                      clear * - r10562 e10563 e10564 b10565 b10566 b10567 b10568 g3 d10516
                      omega
                    have d10569 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
                      have r10570 := hand2 (x (-2) 1) (x (-2) 12)
                      have b10571 := hb (x (-2) 12)
                      have b10572 := hb (x (-2) 1 && x (-2) 12)
                      clear * - r10570 b10571 b10572 d10561
                      omega
                    have d10573 : (x (-5) 4).toNat = 1 := by
                      have r10574 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := hcov11 (-1)
                      have b10575 := hb (x (-5) 4)
                      have b10576 := hb (x (-1) 11)
                      have b10577 := hb (x (-2) 1 && x (-2) 12)
                      have b10578 := hb (x (-3) 2 && x (-3) 13)
                      have b10579 := hb (x (-4) 3 && x (-4) 14)
                      clear * - r10574 b10575 b10576 b10577 b10578 b10579 d6457 d10569 g77 d10553
                      omega
                    have d10580 : (x (-5) 12).toNat = 1 := by
                      have r10581 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
                      have b10582 := hb (x (-5) 4)
                      have b10583 := hb (x (-5) 12)
                      clear * - r10581 b10582 b10583 d10573
                      omega
                    have d10584 : (x (-6) 13).toNat = 0 := by
                      have r10585 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := hd12 (-5)
                      have e10586 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                      have e10587 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                      have b10588 := hb (x (-8) 3)
                      have b10589 := hb (x (-7) 2)
                      have b10590 := hb (x (-6) 13)
                      have b10591 := hb (x (-5) 12)
                      clear * - r10585 e10586 e10587 b10588 b10589 b10590 b10591 d10580
                      omega
                    have d10592 : (x (-6) 5).toNat = 0 := by
                      have r10593 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
                      have b10594 := hb (x (-6) 5)
                      have b10595 := hb (x (-6) 13)
                      clear * - r10593 b10594 b10595 d10584
                      omega
                    have d10596 : (x (-7) 2).toNat = 0 := by
                      have r10597 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := hd12 (-5)
                      have e10598 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                      have e10599 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                      have b10600 := hb (x (-8) 3)
                      have b10601 := hb (x (-7) 2)
                      have b10602 := hb (x (-6) 13)
                      have b10603 := hb (x (-5) 12)
                      clear * - r10597 e10598 e10599 b10600 b10601 b10602 b10603 d10580 d10584
                      omega
                    have d10604 : (x (-6) 1 && x (-6) 14).toNat = 1 := by
                      have r10605 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := hcov13 (-5)
                      have b10606 := hb (x (-7) 2)
                      have b10607 := hb (x (-5) 13)
                      have b10608 := hb (x (-6) 1 && x (-6) 14)
                      clear * - r10605 b10606 b10607 b10608 d10529 d10596
                      omega
                    have d10609 : (x (-6) 1).toNat = 1 := by
                      have r10610 := hand1 (x (-6) 1) (x (-6) 14)
                      have b10611 := hb (x (-6) 1)
                      have b10612 := hb (x (-6) 1 && x (-6) 14)
                      clear * - r10610 b10611 b10612 d10604
                      omega
                    have d10613 : (x (-5) 14).toNat = 0 := by
                      have r10614 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := hd14 (-5)
                      have b10615 := hb (x (-6) 1)
                      have b10616 := hb (x (-5) 14)
                      clear * - r10614 b10615 b10616 d10609
                      omega
                    have d10617 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
                      have r10618 := hand2 (x (-5) 4) (x (-5) 14)
                      have b10619 := hb (x (-5) 14)
                      have b10620 := hb (x (-5) 4 && x (-5) 14)
                      clear * - r10618 b10619 b10620 d10613
                      omega
                    have r10621 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := hcov10 (-1)
                    have b10622 := hb (x (-6) 5)
                    have b10623 := hb (x (-1) 10)
                    have b10624 := hb (x (-2) 1 && x (-2) 11)
                    have b10625 := hb (x (-3) 2 && x (-3) 12)
                    have b10626 := hb (x (-4) 3 && x (-4) 13)
                    have b10627 := hb (x (-5) 4 && x (-5) 14)
                    linarith only [r10621, b10622, b10623, b10624, b10625, b10626, b10627, d6315, d6481, d10541, d10557, d10617, d10592]
            · have f10628 : (x (-1) 8).toNat = 1 := by rw [h9486]; rfl
              have d10629 : (x (-2) 9).toNat = 0 := by
                have r10630 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
                have e10631 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e10632 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e10633 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e10634 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e10635 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e10636 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have b10637 := hb (x (-8) 7)
                have b10638 := hb (x (-7) 6)
                have b10639 := hb (x (-6) 5)
                have b10640 := hb (x (-5) 4)
                have b10641 := hb (x (-4) 11)
                have b10642 := hb (x (-3) 10)
                have b10643 := hb (x (-2) 9)
                have b10644 := hb (x (-1) 8)
                clear * - r10630 e10631 e10632 e10633 e10634 e10635 e10636 b10637 b10638 b10639 b10640 b10641 b10642 b10643 b10644 f10628
                omega
              have d10645 : (x (-3) 10).toNat = 0 := by
                have r10646 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
                have e10647 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e10648 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e10649 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e10650 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e10651 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e10652 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have b10653 := hb (x (-8) 7)
                have b10654 := hb (x (-7) 6)
                have b10655 := hb (x (-6) 5)
                have b10656 := hb (x (-5) 4)
                have b10657 := hb (x (-4) 11)
                have b10658 := hb (x (-3) 10)
                have b10659 := hb (x (-2) 9)
                have b10660 := hb (x (-1) 8)
                clear * - r10646 e10647 e10648 e10649 e10650 e10651 e10652 b10653 b10654 b10655 b10656 b10657 b10658 b10659 b10660 f10628 d10629
                omega
              have d10661 : (x (-4) 11).toNat = 0 := by
                have r10662 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
                have e10663 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e10664 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e10665 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e10666 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e10667 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e10668 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have b10669 := hb (x (-8) 7)
                have b10670 := hb (x (-7) 6)
                have b10671 := hb (x (-6) 5)
                have b10672 := hb (x (-5) 4)
                have b10673 := hb (x (-4) 11)
                have b10674 := hb (x (-3) 10)
                have b10675 := hb (x (-2) 9)
                have b10676 := hb (x (-1) 8)
                clear * - r10662 e10663 e10664 e10665 e10666 e10667 e10668 b10669 b10670 b10671 b10672 b10673 b10674 b10675 b10676 f10628 d10629 d10645
                omega
              have d10677 : (x (-5) 4).toNat = 0 := by
                have r10678 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
                have e10679 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e10680 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e10681 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e10682 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e10683 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e10684 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have b10685 := hb (x (-8) 7)
                have b10686 := hb (x (-7) 6)
                have b10687 := hb (x (-6) 5)
                have b10688 := hb (x (-5) 4)
                have b10689 := hb (x (-4) 11)
                have b10690 := hb (x (-3) 10)
                have b10691 := hb (x (-2) 9)
                have b10692 := hb (x (-1) 8)
                clear * - r10678 e10679 e10680 e10681 e10682 e10683 e10684 b10685 b10686 b10687 b10688 b10689 b10690 b10691 b10692 f10628 d10629 d10645 d10661
                omega
              have d10693 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
                have r10694 := hand1 (x (-5) 4) (x (-5) 13)
                have b10695 := hb (x (-5) 4)
                have b10696 := hb (x (-5) 4 && x (-5) 13)
                clear * - r10694 b10695 b10696 d10677
                omega
              have d10697 : (x (-6) 5).toNat = 0 := by
                have r10698 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
                have e10699 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e10700 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e10701 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e10702 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e10703 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e10704 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have b10705 := hb (x (-8) 7)
                have b10706 := hb (x (-7) 6)
                have b10707 := hb (x (-6) 5)
                have b10708 := hb (x (-5) 4)
                have b10709 := hb (x (-4) 11)
                have b10710 := hb (x (-3) 10)
                have b10711 := hb (x (-2) 9)
                have b10712 := hb (x (-1) 8)
                clear * - r10698 e10699 e10700 e10701 e10702 e10703 e10704 b10705 b10706 b10707 b10708 b10709 b10710 b10711 b10712 f10628 d10629 d10645 d10661 d10677
                omega
              have d10713 : (x (-6) 5 && x (-6) 14).toNat = 0 := by
                have r10714 := hand1 (x (-6) 5) (x (-6) 14)
                have b10715 := hb (x (-6) 5)
                have b10716 := hb (x (-6) 5 && x (-6) 14)
                clear * - r10714 b10715 b10716 d10697
                omega
              have d10717 : (x (-7) 6).toNat = 0 := by
                have r10718 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
                have e10719 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e10720 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e10721 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e10722 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e10723 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e10724 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have b10725 := hb (x (-8) 7)
                have b10726 := hb (x (-7) 6)
                have b10727 := hb (x (-6) 5)
                have b10728 := hb (x (-5) 4)
                have b10729 := hb (x (-4) 11)
                have b10730 := hb (x (-3) 10)
                have b10731 := hb (x (-2) 9)
                have b10732 := hb (x (-1) 8)
                clear * - r10718 e10719 e10720 e10721 e10722 e10723 e10724 b10725 b10726 b10727 b10728 b10729 b10730 b10731 b10732 f10628 d10629 d10645 d10661 d10677 d10697
                omega
              have r10733 : (x 6 1).toNat + (x 5 2).toNat + (x 4 3).toNat + (x 3 4).toNat + (x 2 5).toNat + (x 1 6).toNat + (x 0 7).toNat + (x (-1) 8).toNat + (x (-2) 9).toNat + (x (-3) 10).toNat + (x (-4) 11).toNat + (x (-5) 12).toNat + (x (-6) 13).toNat + (x (-7) 14).toNat = 3 := hcount 7
              have r10734 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := hcount 8
              have r10735 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := hcount 14
              have r10736 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
              have e10737 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
              have e10738 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
              have r10739 : 1 ≤ (x 9 5).toNat + (x 8 1 && x 8 6).toNat + (x 7 2 && x 7 7).toNat + (x 6 3 && x 6 8).toNat + (x 5 4 && x 5 9).toNat + (x 4 5 && x 4 10).toNat + (x 3 6 && x 3 11).toNat + (x 2 7 && x 2 12).toNat + (x 1 8 && x 1 13).toNat + (x 0 9 && x 0 14).toNat + (x (-1) 10).toNat := hcov5 9
              have r10740 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := hcov9 (-1)
              have r10741 : 1 ≤ (x 8 10).toNat + (x 7 1 && x 7 11).toNat + (x 6 2 && x 6 12).toNat + (x 5 3 && x 5 13).toNat + (x 4 4 && x 4 14).toNat + (x 3 5).toNat := hcov10 8
              have r10742 : 1 ≤ (x 14 10).toNat + (x 13 1 && x 13 11).toNat + (x 12 2 && x 12 12).toNat + (x 11 3 && x 11 13).toNat + (x 10 4 && x 10 14).toNat + (x 9 5).toNat := hcov10 14
              have r10743 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := hcov13 (-5)
              have r10744 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
              have r10745 : (x (-7) 2).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp2 (-7))
              have r10746 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
              have r10747 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
              have r10748 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
              have r10749 : (x 9 5).toNat ≤ (x 9 13).toNat := himp _ _ (hp5 9)
              have r10750 := hand2 (x 8 1) (x 8 6)
              have r10751 := hand2 (x 7 2) (x 7 7)
              have r10752 := hand2 (x (-2) 1) (x (-2) 10)
              have r10753 := hand2 (x (-4) 3) (x (-4) 12)
              have r10754 := hand2 (x 7 1) (x 7 11)
              have r10755 := hand1 (x 6 2) (x 6 12)
              have r10756 := hand1 (x 5 3) (x 5 13)
              have r10757 := hand1 (x 12 2) (x 12 12)
              have r10758 := hand1 (x 11 3) (x 11 13)
              have r10759 := hand1 (x 10 4) (x 10 14)
              have r10760 := hand2 (x (-6) 1) (x (-6) 14)
              have r10761 := hand1 (x 6 1) (x 6 14)
              have b10762 := hb (x (-7) 2)
              have b10763 := hb (x (-7) 6)
              have b10764 := hb (x (-7) 14)
              have b10765 := hb (x (-6) 13)
              have b10766 := hb (x (-6) 14)
              have b10767 := hb (x (-5) 12)
              have b10768 := hb (x (-5) 13)
              have b10769 := hb (x (-4) 11)
              have b10770 := hb (x (-4) 12)
              have b10771 := hb (x (-3) 10)
              have b10772 := hb (x (-3) 11)
              have b10773 := hb (x (-2) 9)
              have b10774 := hb (x (-2) 10)
              have b10775 := hb (x (-1) 8)
              have b10776 := hb (x (-1) 9)
              have b10777 := hb (x (-1) 10)
              have b10778 := hb (x 0 7)
              have b10779 := hb (x 0 8)
              have b10780 := hb (x 0 14)
              have b10781 := hb (x 1 6)
              have b10782 := hb (x 1 7)
              have b10783 := hb (x 1 13)
              have b10784 := hb (x 2 5)
              have b10785 := hb (x 2 6)
              have b10786 := hb (x 2 12)
              have b10787 := hb (x 3 4)
              have b10788 := hb (x 3 5)
              have b10789 := hb (x 3 11)
              have b10790 := hb (x 4 3)
              have b10791 := hb (x 4 4)
              have b10792 := hb (x 4 10)
              have b10793 := hb (x 5 2)
              have b10794 := hb (x 5 3)
              have b10795 := hb (x 5 9)
              have b10796 := hb (x 6 1)
              have b10797 := hb (x 6 2)
              have b10798 := hb (x 6 8)
              have b10799 := hb (x 7 1)
              have b10800 := hb (x 7 3)
              have b10801 := hb (x 7 7)
              have b10802 := hb (x 7 11)
              have b10803 := hb (x 7 13)
              have b10804 := hb (x 8 2)
              have b10805 := hb (x 8 6)
              have b10806 := hb (x 8 10)
              have b10807 := hb (x 9 5)
              have b10808 := hb (x 9 13)
              have b10809 := hb (x 10 4)
              have b10810 := hb (x 10 12)
              have b10811 := hb (x 11 3)
              have b10812 := hb (x 12 2)
              have b10813 := hb (x 13 1)
              have b10814 := hb (x 14 10)
              have b10815 := hb (x 8 1 && x 8 6)
              have b10816 := hb (x 7 2 && x 7 7)
              have b10817 := hb (x 6 3 && x 6 8)
              have b10818 := hb (x 5 4 && x 5 9)
              have b10819 := hb (x 4 5 && x 4 10)
              have b10820 := hb (x 3 6 && x 3 11)
              have b10821 := hb (x 2 7 && x 2 12)
              have b10822 := hb (x 1 8 && x 1 13)
              have b10823 := hb (x 0 9 && x 0 14)
              have b10824 := hb (x (-2) 1 && x (-2) 10)
              have b10825 := hb (x (-3) 2 && x (-3) 11)
              have b10826 := hb (x (-4) 3 && x (-4) 12)
              have b10827 := hb (x (-5) 4 && x (-5) 13)
              have b10828 := hb (x (-6) 5 && x (-6) 14)
              have b10829 := hb (x 7 1 && x 7 11)
              have b10830 := hb (x 6 2 && x 6 12)
              have b10831 := hb (x 5 3 && x 5 13)
              have b10832 := hb (x 4 4 && x 4 14)
              have b10833 := hb (x 13 1 && x 13 11)
              have b10834 := hb (x 12 2 && x 12 12)
              have b10835 := hb (x 11 3 && x 11 13)
              have b10836 := hb (x 10 4 && x 10 14)
              have b10837 := hb (x (-6) 1 && x (-6) 14)
              have b10838 := hb (x 6 1 && x 6 14)
              linarith only [r10733, r10734, r10735, r10736, e10737, e10738, r10739, r10740, r10741, r10742, r10743, r10744, r10745, r10746, r10747, r10748, r10749, r10750, r10751, r10752, r10753, r10754, r10755, r10756, r10757, r10758, r10759, r10760, r10761, b10762, b10763, b10764, b10765, b10766, b10767, b10768, b10769, b10770, b10771, b10772, b10773, b10774, b10775, b10776, b10777, b10778, b10779, b10780, b10781, b10782, b10783, b10784, b10785, b10786, b10787, b10788, b10789, b10790, b10791, b10792, b10793, b10794, b10795, b10796, b10797, b10798, b10799, b10800, b10801, b10802, b10803, b10804, b10805, b10806, b10807, b10808, b10809, b10810, b10811, b10812, b10813, b10814, b10815, b10816, b10817, b10818, b10819, b10820, b10821, b10822, b10823, b10824, b10825, b10826, b10827, b10828, b10829, b10830, b10831, b10832, b10833, b10834, b10835, b10836, b10837, b10838, d10717, d10661, d10645, g2, d10629, f10628, g6, d6315, g12, g13, g19, f8827, f9234, d6319, d6393, d6421, d6429, d6357, g25, d7396, g27, d7372, d7344, d7316, d9390, d7340, d7368, d7392, d7412, d6437, g43, g44, g59, d10693, d10713, g76, d9426]
    · have f10839 : (x (-1) 4).toNat = 1 := by rw [h6571]; rfl
      have d10840 : (x (-1) 12).toNat = 1 := by
        have r10841 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
        have b10842 := hb (x (-1) 4)
        have b10843 := hb (x (-1) 12)
        clear * - r10841 b10842 b10843 f10839
        omega
      have d10844 : (x (-2) 13).toNat = 0 := by
        have r10845 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
        have e10846 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e10847 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b10848 := hb (x (-4) 3)
        have b10849 := hb (x (-3) 2)
        have b10850 := hb (x (-2) 13)
        have b10851 := hb (x (-1) 12)
        clear * - r10845 e10846 e10847 b10848 b10849 b10850 b10851 d10840
        omega
      have d10852 : (x (-4) 2).toNat = 1 := by
        have r10853 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := hcov13 (-2)
        have b10854 := hb (x (-4) 2)
        have b10855 := hb (x (-2) 13)
        have b10856 := hb (x (-3) 1 && x (-3) 14)
        clear * - r10853 b10854 b10855 b10856 d10844 g82
        omega
      have d10857 : (x (-4) 14).toNat = 1 := by
        have r10858 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
        have b10859 := hb (x (-4) 2)
        have b10860 := hb (x (-4) 14)
        clear * - r10858 b10859 b10860 d10852
        omega
      have d10861 : (x (-5) 1).toNat = 0 := by
        have r10862 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := hd14 (-4)
        have b10863 := hb (x (-5) 1)
        have b10864 := hb (x (-4) 14)
        clear * - r10862 b10863 b10864 d10857
        omega
      have d10865 : (x (-5) 13).toNat = 0 := by
        have r10866 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
        have b10867 := hb (x (-5) 1)
        have b10868 := hb (x (-5) 13)
        clear * - r10866 b10867 b10868 d10861
        omega
      have d10869 : (x (-3) 2).toNat = 0 := by
        have r10870 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
        have e10871 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e10872 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b10873 := hb (x (-4) 3)
        have b10874 := hb (x (-3) 2)
        have b10875 := hb (x (-2) 13)
        have b10876 := hb (x (-1) 12)
        clear * - r10870 e10871 e10872 b10873 b10874 b10875 b10876 d10840 d10844
        omega
      have d10877 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
        have r10878 := hand1 (x (-3) 2) (x (-3) 12)
        have b10879 := hb (x (-3) 2)
        have b10880 := hb (x (-3) 2 && x (-3) 12)
        clear * - r10878 b10879 b10880 d10869
        omega
      have d10881 : (x (-4) 3).toNat = 0 := by
        have r10882 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
        have e10883 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e10884 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b10885 := hb (x (-4) 3)
        have b10886 := hb (x (-3) 2)
        have b10887 := hb (x (-2) 13)
        have b10888 := hb (x (-1) 12)
        clear * - r10882 e10883 e10884 b10885 b10886 b10887 b10888 d10840 d10844 d10869
        omega
      have d10889 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
        have r10890 := hand1 (x (-4) 3) (x (-4) 14)
        have b10891 := hb (x (-4) 3)
        have b10892 := hb (x (-4) 3 && x (-4) 14)
        clear * - r10890 b10891 b10892 d10881
        omega
      have d10893 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
        have r10894 := hand1 (x (-4) 3) (x (-4) 13)
        have b10895 := hb (x (-4) 3)
        have b10896 := hb (x (-4) 3 && x (-4) 13)
        clear * - r10894 b10895 b10896 d10881
        omega
      have d10897 : (x (-2) 12).toNat = 0 := by
        have r10898 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := hd12 (-2)
        have e10899 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e10900 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have b10901 := hb (x (-5) 3)
        have b10902 := hb (x (-4) 2)
        have b10903 := hb (x (-3) 13)
        have b10904 := hb (x (-2) 12)
        clear * - r10898 e10899 e10900 b10901 b10902 b10903 b10904 g3 d10852
        omega
      have d10905 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
        have r10906 := hand2 (x (-2) 1) (x (-2) 12)
        have b10907 := hb (x (-2) 12)
        have b10908 := hb (x (-2) 1 && x (-2) 12)
        clear * - r10906 b10907 b10908 d10897
        omega
      have d10909 : (x (-5) 4).toNat = 1 := by
        have r10910 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := hcov11 (-1)
        have b10911 := hb (x (-5) 4)
        have b10912 := hb (x (-1) 11)
        have b10913 := hb (x (-2) 1 && x (-2) 12)
        have b10914 := hb (x (-3) 2 && x (-3) 13)
        have b10915 := hb (x (-4) 3 && x (-4) 14)
        clear * - r10910 b10911 b10912 b10913 b10914 b10915 d6457 d10905 g77 d10889
        omega
      have d10916 : (x (-5) 12).toNat = 1 := by
        have r10917 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
        have b10918 := hb (x (-5) 4)
        have b10919 := hb (x (-5) 12)
        clear * - r10917 b10918 b10919 d10909
        omega
      have d10920 : (x (-6) 13).toNat = 0 := by
        have r10921 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := hd12 (-5)
        have e10922 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
        have e10923 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
        have b10924 := hb (x (-8) 3)
        have b10925 := hb (x (-7) 2)
        have b10926 := hb (x (-6) 13)
        have b10927 := hb (x (-5) 12)
        clear * - r10921 e10922 e10923 b10924 b10925 b10926 b10927 d10916
        omega
      have d10928 : (x (-6) 5).toNat = 0 := by
        have r10929 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
        have b10930 := hb (x (-6) 5)
        have b10931 := hb (x (-6) 13)
        clear * - r10929 b10930 b10931 d10920
        omega
      have d10932 : (x (-7) 2).toNat = 0 := by
        have r10933 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := hd12 (-5)
        have e10934 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
        have e10935 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
        have b10936 := hb (x (-8) 3)
        have b10937 := hb (x (-7) 2)
        have b10938 := hb (x (-6) 13)
        have b10939 := hb (x (-5) 12)
        clear * - r10933 e10934 e10935 b10936 b10937 b10938 b10939 d10916 d10920
        omega
      have d10940 : (x (-6) 1 && x (-6) 14).toNat = 1 := by
        have r10941 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := hcov13 (-5)
        have b10942 := hb (x (-7) 2)
        have b10943 := hb (x (-5) 13)
        have b10944 := hb (x (-6) 1 && x (-6) 14)
        clear * - r10941 b10942 b10943 b10944 d10865 d10932
        omega
      have d10945 : (x (-6) 1).toNat = 1 := by
        have r10946 := hand1 (x (-6) 1) (x (-6) 14)
        have b10947 := hb (x (-6) 1)
        have b10948 := hb (x (-6) 1 && x (-6) 14)
        clear * - r10946 b10947 b10948 d10940
        omega
      have d10949 : (x (-5) 14).toNat = 0 := by
        have r10950 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := hd14 (-5)
        have b10951 := hb (x (-6) 1)
        have b10952 := hb (x (-5) 14)
        clear * - r10950 b10951 b10952 d10945
        omega
      have d10953 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
        have r10954 := hand2 (x (-5) 4) (x (-5) 14)
        have b10955 := hb (x (-5) 14)
        have b10956 := hb (x (-5) 4 && x (-5) 14)
        clear * - r10954 b10955 b10956 d10949
        omega
      have r10957 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := hcov10 (-1)
      have b10958 := hb (x (-6) 5)
      have b10959 := hb (x (-1) 10)
      have b10960 := hb (x (-2) 1 && x (-2) 11)
      have b10961 := hb (x (-3) 2 && x (-3) 12)
      have b10962 := hb (x (-4) 3 && x (-4) 13)
      have b10963 := hb (x (-5) 4 && x (-5) 14)
      linarith only [r10957, b10958, b10959, b10960, b10961, b10962, b10963, d6315, d6481, d10877, d10893, d10953, d10928]
  · have f10964 : (x 0 6).toNat = 1 := by rw [h6569]; rfl
    have d10965 : (x 6 8).toNat = 0 := by
      have r10966 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
      have e10967 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e10968 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e10969 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e10970 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e10971 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e10972 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b10973 := hb (x (-1) 7)
      have b10974 := hb (x 0 6)
      have b10975 := hb (x 1 5)
      have b10976 := hb (x 2 4)
      have b10977 := hb (x 3 11)
      have b10978 := hb (x 4 10)
      have b10979 := hb (x 5 9)
      have b10980 := hb (x 6 8)
      clear * - r10966 e10967 e10968 e10969 e10970 e10971 e10972 b10973 b10974 b10975 b10976 b10977 b10978 b10979 b10980 d6441 f10964
      omega
    have d10981 : (x 6 2 && x 6 8).toNat = 0 := by
      have r10982 := hand2 (x 6 2) (x 6 8)
      have b10983 := hb (x 6 8)
      have b10984 := hb (x 6 2 && x 6 8)
      clear * - r10982 b10983 b10984 d10965
      omega
    have d10985 : (x 5 9).toNat = 0 := by
      have r10986 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
      have e10987 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e10988 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e10989 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e10990 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e10991 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e10992 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b10993 := hb (x (-1) 7)
      have b10994 := hb (x 0 6)
      have b10995 := hb (x 1 5)
      have b10996 := hb (x 2 4)
      have b10997 := hb (x 3 11)
      have b10998 := hb (x 4 10)
      have b10999 := hb (x 5 9)
      have b11000 := hb (x 6 8)
      clear * - r10986 e10987 e10988 e10989 e10990 e10991 e10992 b10993 b10994 b10995 b10996 b10997 b10998 b10999 b11000 d10965 d6441 f10964
      omega
    have d11001 : (x 5 3 && x 5 9).toNat = 0 := by
      have r11002 := hand2 (x 5 3) (x 5 9)
      have b11003 := hb (x 5 9)
      have b11004 := hb (x 5 3 && x 5 9)
      clear * - r11002 b11003 b11004 d10985
      omega
    have d11005 : (x 4 10).toNat = 0 := by
      have r11006 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
      have e11007 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e11008 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e11009 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e11010 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e11011 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e11012 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b11013 := hb (x (-1) 7)
      have b11014 := hb (x 0 6)
      have b11015 := hb (x 1 5)
      have b11016 := hb (x 2 4)
      have b11017 := hb (x 3 11)
      have b11018 := hb (x 4 10)
      have b11019 := hb (x 5 9)
      have b11020 := hb (x 6 8)
      clear * - r11006 e11007 e11008 e11009 e11010 e11011 e11012 b11013 b11014 b11015 b11016 b11017 b11018 b11019 b11020 d10965 d10985 d6441 f10964
      omega
    have d11021 : (x 3 11).toNat = 0 := by
      have r11022 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
      have e11023 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e11024 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e11025 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e11026 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e11027 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e11028 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b11029 := hb (x (-1) 7)
      have b11030 := hb (x 0 6)
      have b11031 := hb (x 1 5)
      have b11032 := hb (x 2 4)
      have b11033 := hb (x 3 11)
      have b11034 := hb (x 4 10)
      have b11035 := hb (x 5 9)
      have b11036 := hb (x 6 8)
      clear * - r11022 e11023 e11024 e11025 e11026 e11027 e11028 b11029 b11030 b11031 b11032 b11033 b11034 b11035 b11036 d10965 d10985 d11005 d6441 f10964
      omega
    have d11037 : (x 1 5).toNat = 0 := by
      have r11038 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
      have e11039 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e11040 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e11041 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e11042 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e11043 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e11044 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b11045 := hb (x (-1) 7)
      have b11046 := hb (x 0 6)
      have b11047 := hb (x 1 5)
      have b11048 := hb (x 2 4)
      have b11049 := hb (x 3 11)
      have b11050 := hb (x 4 10)
      have b11051 := hb (x 5 9)
      have b11052 := hb (x 6 8)
      clear * - r11038 e11039 e11040 e11041 e11042 e11043 e11044 b11045 b11046 b11047 b11048 b11049 b11050 b11051 b11052 d10965 d10985 d11005 d11021 d6441 f10964
      omega
    cases h11053 : x (-1) 4
    · have f11054 : (x (-1) 4).toNat = 0 := by rw [h11053]; rfl
      cases h11055 : x 1 7
      · have f11056 : (x 1 7).toNat = 0 := by rw [h11055]; rfl
        have d11057 : (x 1 7 && x 1 13).toNat = 0 := by
          have r11058 := hand1 (x 1 7) (x 1 13)
          have b11059 := hb (x 1 7)
          have b11060 := hb (x 1 7 && x 1 13)
          clear * - r11058 b11059 b11060 f11056
          omega
        have d11061 : (x 1 7 && x 1 11).toNat = 0 := by
          have r11062 := hand1 (x 1 7) (x 1 11)
          have b11063 := hb (x 1 7)
          have b11064 := hb (x 1 7 && x 1 11)
          clear * - r11062 b11063 b11064 f11056
          omega
        have d11065 : (x 1 3 && x 1 7).toNat = 0 := by
          have r11066 := hand2 (x 1 3) (x 1 7)
          have b11067 := hb (x 1 7)
          have b11068 := hb (x 1 3 && x 1 7)
          clear * - r11066 b11067 b11068 f11056
          omega
        cases h11069 : x (-1) 8
        · have f11070 : (x (-1) 8).toNat = 0 := by rw [h11069]; rfl
          cases h11071 : x 1 11
          · have f11072 : (x 1 11).toNat = 0 := by rw [h11071]; rfl
            have d11073 : (x (-3) 4).toNat = 1 := by
              have r11074 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := hcov11 1
              have b11075 := hb (x (-3) 4)
              have b11076 := hb (x 1 11)
              have b11077 := hb (x 0 1 && x 0 12)
              have b11078 := hb (x (-1) 2 && x (-1) 13)
              have b11079 := hb (x (-2) 3 && x (-2) 14)
              clear * - r11074 b11075 b11076 b11077 b11078 b11079 f11072 g80 g81 d6469
              omega
            have d11080 : (x (-3) 12).toNat = 1 := by
              have r11081 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
              have b11082 := hb (x (-3) 4)
              have b11083 := hb (x (-3) 12)
              clear * - r11081 b11082 b11083 d11073
              omega
            have d11084 : (x (-4) 13).toNat = 0 := by
              have r11085 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := hd12 (-3)
              have e11086 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
              have e11087 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
              have b11088 := hb (x (-6) 3)
              have b11089 := hb (x (-5) 2)
              have b11090 := hb (x (-4) 13)
              have b11091 := hb (x (-3) 12)
              clear * - r11085 e11086 e11087 b11088 b11089 b11090 b11091 d11080
              omega
            have d11092 : (x (-5) 2).toNat = 0 := by
              have r11093 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := hd12 (-3)
              have e11094 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
              have e11095 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
              have b11096 := hb (x (-6) 3)
              have b11097 := hb (x (-5) 2)
              have b11098 := hb (x (-4) 13)
              have b11099 := hb (x (-3) 12)
              clear * - r11093 e11094 e11095 b11096 b11097 b11098 b11099 d11080 d11084
              omega
            have d11100 : (x (-5) 2 && x (-5) 13).toNat = 0 := by
              have r11101 := hand1 (x (-5) 2) (x (-5) 13)
              have b11102 := hb (x (-5) 2)
              have b11103 := hb (x (-5) 2 && x (-5) 13)
              clear * - r11101 b11102 b11103 d11092
              omega
            have d11104 : (x (-5) 2 && x (-5) 12).toNat = 0 := by
              have r11105 := hand1 (x (-5) 2) (x (-5) 12)
              have b11106 := hb (x (-5) 2)
              have b11107 := hb (x (-5) 2 && x (-5) 12)
              clear * - r11105 b11106 b11107 d11092
              omega
            have d11108 : (x (-4) 1 && x (-4) 14).toNat = 1 := by
              have r11109 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := hcov13 (-3)
              have b11110 := hb (x (-5) 2)
              have b11111 := hb (x (-3) 13)
              have b11112 := hb (x (-4) 1 && x (-4) 14)
              clear * - r11109 b11110 b11111 b11112 g3 d11092
              omega
            have d11113 : (x (-4) 14).toNat = 1 := by
              have r11114 := hand2 (x (-4) 1) (x (-4) 14)
              have b11115 := hb (x (-4) 14)
              have b11116 := hb (x (-4) 1 && x (-4) 14)
              clear * - r11114 b11115 b11116 d11108
              omega
            have d11117 : (x (-5) 1).toNat = 0 := by
              have r11118 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := hd14 (-4)
              have b11119 := hb (x (-5) 1)
              have b11120 := hb (x (-4) 14)
              clear * - r11118 b11119 b11120 d11113
              omega
            have d11121 : (x (-5) 1 && x (-5) 14).toNat = 0 := by
              have r11122 := hand1 (x (-5) 1) (x (-5) 14)
              have b11123 := hb (x (-5) 1)
              have b11124 := hb (x (-5) 1 && x (-5) 14)
              clear * - r11122 b11123 b11124 d11117
              omega
            have d11125 : (x (-6) 2).toNat = 1 := by
              have r11126 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := hcov13 (-4)
              have b11127 := hb (x (-6) 2)
              have b11128 := hb (x (-4) 13)
              have b11129 := hb (x (-5) 1 && x (-5) 14)
              clear * - r11126 b11127 b11128 b11129 d11084 d11121
              omega
            have d11130 : (x (-6) 14).toNat = 1 := by
              have r11131 : (x (-6) 2).toNat ≤ (x (-6) 14).toNat := himp _ _ (hp2 (-6))
              have b11132 := hb (x (-6) 2)
              have b11133 := hb (x (-6) 14)
              clear * - r11131 b11132 b11133 d11125
              omega
            have d11134 : (x (-7) 1).toNat = 0 := by
              have r11135 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := hd14 (-6)
              have b11136 := hb (x (-7) 1)
              have b11137 := hb (x (-6) 14)
              clear * - r11135 b11136 b11137 d11130
              omega
            have d11138 : (x (-7) 13).toNat = 0 := by
              have r11139 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
              have b11140 := hb (x (-7) 1)
              have b11141 := hb (x (-7) 13)
              clear * - r11139 b11140 b11141 d11134
              omega
            have d11142 : (x (-4) 12).toNat = 0 := by
              have r11143 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := hd12 (-4)
              have e11144 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
              have e11145 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
              have b11146 := hb (x (-7) 3)
              have b11147 := hb (x (-6) 2)
              have b11148 := hb (x (-5) 13)
              have b11149 := hb (x (-4) 12)
              clear * - r11143 e11144 e11145 b11146 b11147 b11148 b11149 d11125
              omega
            have d11150 : (x (-4) 1 && x (-4) 12).toNat = 0 := by
              have r11151 := hand2 (x (-4) 1) (x (-4) 12)
              have b11152 := hb (x (-4) 12)
              have b11153 := hb (x (-4) 1 && x (-4) 12)
              clear * - r11151 b11152 b11153 d11142
              omega
            have d11154 : (x (-4) 4).toNat = 0 := by
              have r11155 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
              have b11156 := hb (x (-4) 4)
              have b11157 := hb (x (-4) 12)
              clear * - r11155 b11156 b11157 d11142
              omega
            have d11158 : (x (-4) 1).toNat = 1 := by
              have r11159 := hand1 (x (-4) 1) (x (-4) 14)
              have b11160 := hb (x (-4) 1)
              have b11161 := hb (x (-4) 1 && x (-4) 14)
              clear * - r11159 b11160 b11161 d11108
              omega
            have d11162 : (x (-3) 14).toNat = 0 := by
              have r11163 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := hd14 (-3)
              have b11164 := hb (x (-4) 1)
              have b11165 := hb (x (-3) 14)
              clear * - r11163 b11164 b11165 d11158
              omega
            have d11166 : (x (-3) 2).toNat = 0 := by
              have r11167 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
              have b11168 := hb (x (-3) 2)
              have b11169 := hb (x (-3) 14)
              clear * - r11167 b11168 b11169 d11162
              omega
            have d11170 : (x (-3) 10).toNat = 0 := by
              have r11171 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
              have b11172 := hb (x (-3) 2)
              have b11173 := hb (x (-3) 10)
              clear * - r11171 b11172 b11173 d11166
              omega
            have d11174 : (x (-6) 3).toNat = 0 := by
              have r11175 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := hd12 (-3)
              have e11176 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
              have e11177 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
              have b11178 := hb (x (-6) 3)
              have b11179 := hb (x (-5) 2)
              have b11180 := hb (x (-4) 13)
              have b11181 := hb (x (-3) 12)
              clear * - r11175 e11176 e11177 b11178 b11179 b11180 b11181 d11080 d11084 d11092
              omega
            have d11182 : (x (-6) 3 && x (-6) 14).toNat = 0 := by
              have r11183 := hand1 (x (-6) 3) (x (-6) 14)
              have b11184 := hb (x (-6) 3)
              have b11185 := hb (x (-6) 3 && x (-6) 14)
              clear * - r11183 b11184 b11185 d11174
              omega
            have d11186 : (x (-6) 3 && x (-6) 13).toNat = 0 := by
              have r11187 := hand1 (x (-6) 3) (x (-6) 13)
              have b11188 := hb (x (-6) 3)
              have b11189 := hb (x (-6) 3 && x (-6) 13)
              clear * - r11187 b11188 b11189 d11174
              omega
            have d11190 : (x (-2) 2 && x (-2) 13).toNat = 1 := by
              have r11191 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := hcov11 0
              have b11192 := hb (x (-4) 4)
              have b11193 := hb (x 0 11)
              have b11194 := hb (x (-1) 1 && x (-1) 12)
              have b11195 := hb (x (-2) 2 && x (-2) 13)
              have b11196 := hb (x (-3) 3 && x (-3) 14)
              clear * - r11191 b11192 b11193 b11194 b11195 b11196 g16 g78 g79 d11154
              omega
            have d11197 : (x (-2) 13).toNat = 1 := by
              have r11198 := hand2 (x (-2) 2) (x (-2) 13)
              have b11199 := hb (x (-2) 13)
              have b11200 := hb (x (-2) 2 && x (-2) 13)
              clear * - r11198 b11199 b11200 d11190
              omega
            have d11201 : (x (-1) 12).toNat = 0 := by
              have r11202 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
              have e11203 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e11204 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b11205 := hb (x (-4) 3)
              have b11206 := hb (x (-3) 2)
              have b11207 := hb (x (-2) 13)
              have b11208 := hb (x (-1) 12)
              clear * - r11202 e11203 e11204 b11205 b11206 b11207 b11208 d11197 d11166
              omega
            have d11209 : (x (-4) 3).toNat = 0 := by
              have r11210 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
              have e11211 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e11212 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b11213 := hb (x (-4) 3)
              have b11214 := hb (x (-3) 2)
              have b11215 := hb (x (-2) 13)
              have b11216 := hb (x (-1) 12)
              clear * - r11210 e11211 e11212 b11213 b11214 b11215 b11216 d11201 d11197 d11166
              omega
            have d11217 : (x (-4) 11).toNat = 0 := by
              have r11218 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
              have b11219 := hb (x (-4) 3)
              have b11220 := hb (x (-4) 11)
              clear * - r11218 b11219 b11220 d11209
              omega
            have d11221 : (x (-4) 1 && x (-4) 11).toNat = 0 := by
              have r11222 := hand2 (x (-4) 1) (x (-4) 11)
              have b11223 := hb (x (-4) 11)
              have b11224 := hb (x (-4) 1 && x (-4) 11)
              clear * - r11222 b11223 b11224 d11217
              omega
            have d11225 : (x (-7) 4).toNat = 1 := by
              have r11226 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := hcov11 (-3)
              have b11227 := hb (x (-7) 4)
              have b11228 := hb (x (-3) 11)
              have b11229 := hb (x (-4) 1 && x (-4) 12)
              have b11230 := hb (x (-5) 2 && x (-5) 13)
              have b11231 := hb (x (-6) 3 && x (-6) 14)
              clear * - r11226 b11227 b11228 b11229 b11230 b11231 g2 d11150 d11100 d11182
              omega
            have d11232 : (x (-7) 12).toNat = 1 := by
              have r11233 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
              have b11234 := hb (x (-7) 4)
              have b11235 := hb (x (-7) 12)
              clear * - r11233 b11234 b11235 d11225
              omega
            have d11236 : (x (-8) 13).toNat = 0 := by
              have r11237 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := hd12 (-7)
              have e11238 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
              have e11239 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
              have b11240 := hb (x (-10) 3)
              have b11241 := hb (x (-9) 2)
              have b11242 := hb (x (-8) 13)
              have b11243 := hb (x (-7) 12)
              clear * - r11237 e11238 e11239 b11240 b11241 b11242 b11243 d11232
              omega
            have d11244 : (x (-8) 5).toNat = 0 := by
              have r11245 : (x (-8) 5).toNat ≤ (x (-8) 13).toNat := himp _ _ (hp5 (-8))
              have b11246 := hb (x (-8) 5)
              have b11247 := hb (x (-8) 13)
              clear * - r11245 b11246 b11247 d11236
              omega
            have d11248 : (x (-9) 2).toNat = 0 := by
              have r11249 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := hd12 (-7)
              have e11250 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
              have e11251 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
              have b11252 := hb (x (-10) 3)
              have b11253 := hb (x (-9) 2)
              have b11254 := hb (x (-8) 13)
              have b11255 := hb (x (-7) 12)
              clear * - r11249 e11250 e11251 b11252 b11253 b11254 b11255 d11232 d11236
              omega
            have d11256 : (x (-8) 1 && x (-8) 14).toNat = 1 := by
              have r11257 : 1 ≤ (x (-7) 13).toNat + (x (-8) 1 && x (-8) 14).toNat + (x (-9) 2).toNat := hcov13 (-7)
              have b11258 := hb (x (-9) 2)
              have b11259 := hb (x (-7) 13)
              have b11260 := hb (x (-8) 1 && x (-8) 14)
              clear * - r11257 b11258 b11259 b11260 d11138 d11248
              omega
            have d11261 : (x (-8) 1).toNat = 1 := by
              have r11262 := hand1 (x (-8) 1) (x (-8) 14)
              have b11263 := hb (x (-8) 1)
              have b11264 := hb (x (-8) 1 && x (-8) 14)
              clear * - r11262 b11263 b11264 d11256
              omega
            have d11265 : (x (-7) 14).toNat = 0 := by
              have r11266 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := hd14 (-7)
              have b11267 := hb (x (-8) 1)
              have b11268 := hb (x (-7) 14)
              clear * - r11266 b11267 b11268 d11261
              omega
            have d11269 : (x (-7) 4 && x (-7) 14).toNat = 0 := by
              have r11270 := hand2 (x (-7) 4) (x (-7) 14)
              have b11271 := hb (x (-7) 14)
              have b11272 := hb (x (-7) 4 && x (-7) 14)
              clear * - r11270 b11271 b11272 d11265
              omega
            have r11273 : 1 ≤ (x (-3) 10).toNat + (x (-4) 1 && x (-4) 11).toNat + (x (-5) 2 && x (-5) 12).toNat + (x (-6) 3 && x (-6) 13).toNat + (x (-7) 4 && x (-7) 14).toNat + (x (-8) 5).toNat := hcov10 (-3)
            have b11274 := hb (x (-8) 5)
            have b11275 := hb (x (-3) 10)
            have b11276 := hb (x (-4) 1 && x (-4) 11)
            have b11277 := hb (x (-5) 2 && x (-5) 12)
            have b11278 := hb (x (-6) 3 && x (-6) 13)
            have b11279 := hb (x (-7) 4 && x (-7) 14)
            linarith only [r11273, b11274, b11275, b11276, b11277, b11278, b11279, d11170, d11221, d11104, d11186, d11269, d11244]
          · have f11280 : (x 1 11).toNat = 1 := by rw [h11071]; rfl
            have d11281 : (x 4 8).toNat = 0 := by
              have r11282 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := hd8 4
              have e11283 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
              have e11284 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
              have e11285 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
              have e11286 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
              have e11287 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
              have e11288 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
              have b11289 := hb (x (-3) 7)
              have b11290 := hb (x (-2) 6)
              have b11291 := hb (x (-1) 5)
              have b11292 := hb (x 0 4)
              have b11293 := hb (x 1 11)
              have b11294 := hb (x 2 10)
              have b11295 := hb (x 3 9)
              have b11296 := hb (x 4 8)
              clear * - r11282 e11283 e11284 e11285 e11286 e11287 e11288 b11289 b11290 b11291 b11292 b11293 b11294 b11295 b11296 g24 f11280 g10 g5
              omega
            have d11297 : (x 3 9).toNat = 0 := by
              have r11298 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := hd8 4
              have e11299 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
              have e11300 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
              have e11301 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
              have e11302 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
              have e11303 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
              have e11304 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
              have b11305 := hb (x (-3) 7)
              have b11306 := hb (x (-2) 6)
              have b11307 := hb (x (-1) 5)
              have b11308 := hb (x 0 4)
              have b11309 := hb (x 1 11)
              have b11310 := hb (x 2 10)
              have b11311 := hb (x 3 9)
              have b11312 := hb (x 4 8)
              clear * - r11298 e11299 e11300 e11301 e11302 e11303 e11304 b11305 b11306 b11307 b11308 b11309 b11310 b11311 b11312 d11281 g24 f11280 g10 g5
              omega
            have r11313 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := hcount 12
            have r11314 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
            have e11315 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
            have e11316 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
            have e11317 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
            have e11318 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
            have e11319 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
            have e11320 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
            have r11321 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := hd8 14
            have e11322 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
            have e11323 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
            have e11324 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
            have e11325 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
            have e11326 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
            have e11327 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
            have r11328 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
            have e11329 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
            have e11330 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
            have r11331 : 1 ≤ (x 8 4).toNat + (x 7 1 && x 7 5).toNat + (x 6 2 && x 6 6).toNat + (x 5 3 && x 5 7).toNat + (x 4 4 && x 4 8).toNat + (x 3 5 && x 3 9).toNat + (x 2 6 && x 2 10).toNat + (x 1 7 && x 1 11).toNat + (x 0 8 && x 0 12).toNat + (x (-1) 9 && x (-1) 13).toNat + (x (-2) 10 && x (-2) 14).toNat + (x (-3) 11).toNat := hcov4 8
            have e11332 : (x 7 1 && x 7 5).toNat = (x 7 5).toNat := handr _ _ (fun h => hp13 7 (hp5 7 (h)))
            have e11333 : (x (-2) 10 && x (-2) 14).toNat = (x (-2) 10).toNat := handl _ _ (fun h => hp2 (-2) (hp10 (-2) (h)))
            have r11334 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := hcov6 8
            have r11335 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := hcov9 0
            have r11336 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := hcov10 6
            have r11337 : 1 ≤ (x 12 10).toNat + (x 11 1 && x 11 11).toNat + (x 10 2 && x 10 12).toNat + (x 9 3 && x 9 13).toNat + (x 8 4 && x 8 14).toNat + (x 7 5).toNat := hcov10 12
            have r11338 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
            have r11339 : (x 6 10).toNat ≤ (x 6 2).toNat := himp _ _ (hp10 6)
            have r11340 : (x 7 5).toNat ≤ (x 7 13).toNat := himp _ _ (hp5 7)
            have r11341 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
            have r11342 := hand2 (x 6 2) (x 6 6)
            have r11343 := hand2 (x 5 3) (x 5 7)
            have r11344 := hand2 (x 7 1) (x 7 7)
            have r11345 := hand1 (x (-4) 4) (x (-4) 13)
            have r11346 := hand1 (x (-5) 5) (x (-5) 14)
            have r11347 := hand2 (x 5 1) (x 5 11)
            have r11348 := hand2 (x 11 1) (x 11 11)
            have r11349 := hand1 (x 10 2) (x 10 12)
            have r11350 := hand1 (x 9 3) (x 9 13)
            have r11351 := hand1 (x 8 4) (x 8 14)
            have b11352 := hb (x (-7) 7)
            have b11353 := hb (x (-6) 6)
            have b11354 := hb (x (-5) 5)
            have b11355 := hb (x (-4) 4)
            have b11356 := hb (x (-3) 11)
            have b11357 := hb (x (-2) 10)
            have b11358 := hb (x (-2) 14)
            have b11359 := hb (x (-1) 9)
            have b11360 := hb (x (-1) 13)
            have b11361 := hb (x 0 8)
            have b11362 := hb (x 0 9)
            have b11363 := hb (x 0 12)
            have b11364 := hb (x 1 5)
            have b11365 := hb (x 1 11)
            have b11366 := hb (x 2 10)
            have b11367 := hb (x 3 9)
            have b11368 := hb (x 4 8)
            have b11369 := hb (x 5 3)
            have b11370 := hb (x 5 7)
            have b11371 := hb (x 5 11)
            have b11372 := hb (x 6 2)
            have b11373 := hb (x 6 6)
            have b11374 := hb (x 6 10)
            have b11375 := hb (x 7 5)
            have b11376 := hb (x 7 7)
            have b11377 := hb (x 7 13)
            have b11378 := hb (x 8 4)
            have b11379 := hb (x 8 6)
            have b11380 := hb (x 8 12)
            have b11381 := hb (x 9 3)
            have b11382 := hb (x 9 5)
            have b11383 := hb (x 10 2)
            have b11384 := hb (x 10 4)
            have b11385 := hb (x 11 1)
            have b11386 := hb (x 11 11)
            have b11387 := hb (x 12 10)
            have b11388 := hb (x 13 9)
            have b11389 := hb (x 14 8)
            have b11390 := hb (x 6 2 && x 6 6)
            have b11391 := hb (x 5 3 && x 5 7)
            have b11392 := hb (x 4 4 && x 4 8)
            have b11393 := hb (x 3 5 && x 3 9)
            have b11394 := hb (x 2 6 && x 2 10)
            have b11395 := hb (x 1 7 && x 1 11)
            have b11396 := hb (x 0 8 && x 0 12)
            have b11397 := hb (x (-1) 9 && x (-1) 13)
            have b11398 := hb (x 7 1 && x 7 7)
            have b11399 := hb (x 6 2 && x 6 8)
            have b11400 := hb (x 5 3 && x 5 9)
            have b11401 := hb (x 4 4 && x 4 10)
            have b11402 := hb (x 3 5 && x 3 11)
            have b11403 := hb (x 2 6 && x 2 12)
            have b11404 := hb (x 1 7 && x 1 13)
            have b11405 := hb (x 0 8 && x 0 14)
            have b11406 := hb (x (-1) 1 && x (-1) 10)
            have b11407 := hb (x (-2) 2 && x (-2) 11)
            have b11408 := hb (x (-3) 3 && x (-3) 12)
            have b11409 := hb (x (-4) 4 && x (-4) 13)
            have b11410 := hb (x (-5) 5 && x (-5) 14)
            have b11411 := hb (x 5 1 && x 5 11)
            have b11412 := hb (x 4 2 && x 4 12)
            have b11413 := hb (x 3 3 && x 3 13)
            have b11414 := hb (x 2 4 && x 2 14)
            have b11415 := hb (x 11 1 && x 11 11)
            have b11416 := hb (x 10 2 && x 10 12)
            have b11417 := hb (x 9 3 && x 9 13)
            have b11418 := hb (x 8 4 && x 8 14)
            linarith only [r11313, r11314, e11315, e11316, e11317, e11318, e11319, e11320, r11321, e11322, e11323, e11324, e11325, e11326, e11327, r11328, e11329, e11330, r11331, e11332, e11333, r11334, r11335, r11336, r11337, r11338, r11339, r11340, r11341, r11342, r11343, r11344, r11345, r11346, r11347, r11348, r11349, r11350, r11351, b11352, b11353, b11354, b11355, b11356, b11357, b11358, b11359, b11360, b11361, b11362, b11363, b11364, b11365, b11366, b11367, b11368, b11369, b11370, b11371, b11372, b11373, b11374, b11375, b11376, b11377, b11378, b11379, b11380, b11381, b11382, b11383, b11384, b11385, b11386, b11387, b11388, b11389, b11390, b11391, b11392, b11393, b11394, b11395, b11396, b11397, b11398, b11399, b11400, b11401, b11402, b11403, b11404, b11405, b11406, b11407, b11408, b11409, b11410, b11411, b11412, b11413, b11414, b11415, b11416, b11417, b11418, g2, g4, g6, g7, g13, g14, g17, d11037, f11280, g24, d11297, d11281, g33, g34, g35, d11061, g36, g37, d10981, d11001, g47, g48, d6425, d11057, g49, g60, d6485, g61, g74, g75, d6405]
        · have f11419 : (x (-1) 8).toNat = 1 := by rw [h11069]; rfl
          have d11420 : (x (-2) 9).toNat = 0 := by
            have r11421 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
            have e11422 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e11423 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e11424 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e11425 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e11426 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e11427 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have b11428 := hb (x (-8) 7)
            have b11429 := hb (x (-7) 6)
            have b11430 := hb (x (-6) 5)
            have b11431 := hb (x (-5) 4)
            have b11432 := hb (x (-4) 11)
            have b11433 := hb (x (-3) 10)
            have b11434 := hb (x (-2) 9)
            have b11435 := hb (x (-1) 8)
            clear * - r11421 e11422 e11423 e11424 e11425 e11426 e11427 b11428 b11429 b11430 b11431 b11432 b11433 b11434 b11435 f11419
            omega
          have d11436 : (x (-3) 10).toNat = 0 := by
            have r11437 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
            have e11438 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e11439 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e11440 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e11441 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e11442 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e11443 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have b11444 := hb (x (-8) 7)
            have b11445 := hb (x (-7) 6)
            have b11446 := hb (x (-6) 5)
            have b11447 := hb (x (-5) 4)
            have b11448 := hb (x (-4) 11)
            have b11449 := hb (x (-3) 10)
            have b11450 := hb (x (-2) 9)
            have b11451 := hb (x (-1) 8)
            clear * - r11437 e11438 e11439 e11440 e11441 e11442 e11443 b11444 b11445 b11446 b11447 b11448 b11449 b11450 b11451 f11419 d11420
            omega
          have d11452 : (x (-4) 11).toNat = 0 := by
            have r11453 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
            have e11454 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e11455 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e11456 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e11457 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e11458 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e11459 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have b11460 := hb (x (-8) 7)
            have b11461 := hb (x (-7) 6)
            have b11462 := hb (x (-6) 5)
            have b11463 := hb (x (-5) 4)
            have b11464 := hb (x (-4) 11)
            have b11465 := hb (x (-3) 10)
            have b11466 := hb (x (-2) 9)
            have b11467 := hb (x (-1) 8)
            clear * - r11453 e11454 e11455 e11456 e11457 e11458 e11459 b11460 b11461 b11462 b11463 b11464 b11465 b11466 b11467 f11419 d11420 d11436
            omega
          have d11468 : (x (-4) 2 && x (-4) 11).toNat = 0 := by
            have r11469 := hand2 (x (-4) 2) (x (-4) 11)
            have b11470 := hb (x (-4) 11)
            have b11471 := hb (x (-4) 2 && x (-4) 11)
            clear * - r11469 b11470 b11471 d11452
            omega
          have d11472 : (x (-5) 4).toNat = 0 := by
            have r11473 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
            have e11474 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e11475 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e11476 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e11477 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e11478 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e11479 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have b11480 := hb (x (-8) 7)
            have b11481 := hb (x (-7) 6)
            have b11482 := hb (x (-6) 5)
            have b11483 := hb (x (-5) 4)
            have b11484 := hb (x (-4) 11)
            have b11485 := hb (x (-3) 10)
            have b11486 := hb (x (-2) 9)
            have b11487 := hb (x (-1) 8)
            clear * - r11473 e11474 e11475 e11476 e11477 e11478 e11479 b11480 b11481 b11482 b11483 b11484 b11485 b11486 b11487 f11419 d11420 d11436 d11452
            omega
          have d11488 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
            have r11489 := hand1 (x (-5) 4) (x (-5) 14)
            have b11490 := hb (x (-5) 4)
            have b11491 := hb (x (-5) 4 && x (-5) 14)
            clear * - r11489 b11490 b11491 d11472
            omega
          have d11492 : (x (-6) 5).toNat = 0 := by
            have r11493 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
            have e11494 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e11495 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e11496 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e11497 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e11498 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e11499 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have b11500 := hb (x (-8) 7)
            have b11501 := hb (x (-7) 6)
            have b11502 := hb (x (-6) 5)
            have b11503 := hb (x (-5) 4)
            have b11504 := hb (x (-4) 11)
            have b11505 := hb (x (-3) 10)
            have b11506 := hb (x (-2) 9)
            have b11507 := hb (x (-1) 8)
            clear * - r11493 e11494 e11495 e11496 e11497 e11498 e11499 b11500 b11501 b11502 b11503 b11504 b11505 b11506 b11507 f11419 d11420 d11436 d11452 d11472
            omega
          have r11508 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := hd8 (-4)
          have e11509 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
          have e11510 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
          have e11511 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
          have e11512 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
          have e11513 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
          have e11514 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
          have r11515 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := hd8 (-2)
          have e11516 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
          have e11517 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
          have e11518 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
          have e11519 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
          have e11520 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
          have e11521 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
          have r11522 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
          have e11523 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e11524 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e11525 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e11526 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e11527 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e11528 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have r11529 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := hd12 (-4)
          have e11530 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
          have e11531 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
          have r11532 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := hd12 (-2)
          have e11533 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
          have e11534 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
          have r11535 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
          have e11536 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e11537 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have r11538 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := hcov4 4
          have e11539 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
          have e11540 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
          have r11541 : 1 ≤ (x (-2) 9).toNat + (x (-3) 1 && x (-3) 10).toNat + (x (-4) 2 && x (-4) 11).toNat + (x (-5) 3 && x (-5) 12).toNat + (x (-6) 4 && x (-6) 13).toNat + (x (-7) 5 && x (-7) 14).toNat + (x (-8) 6).toNat := hcov9 (-2)
          have r11542 : 1 ≤ (x (-4) 10).toNat + (x (-5) 1 && x (-5) 11).toNat + (x (-6) 2 && x (-6) 12).toNat + (x (-7) 3 && x (-7) 13).toNat + (x (-8) 4 && x (-8) 14).toNat + (x (-9) 5).toNat := hcov10 (-4)
          have r11543 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := hcov10 (-1)
          have r11544 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := hcov10 0
          have r11545 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := hcov13 (-2)
          have r11546 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
          have r11547 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
          have r11548 := hand2 (x (-2) 6) (x (-2) 10)
          have r11549 := hand1 (x (-4) 8) (x (-4) 12)
          have r11550 := hand1 (x (-5) 9) (x (-5) 13)
          have r11551 := hand1 (x (-5) 3) (x (-5) 12)
          have r11552 := hand1 (x (-6) 4) (x (-6) 13)
          have r11553 := hand1 (x (-7) 5) (x (-7) 14)
          have r11554 := hand2 (x (-5) 1) (x (-5) 11)
          have r11555 := hand1 (x (-6) 2) (x (-6) 12)
          have r11556 := hand1 (x (-7) 3) (x (-7) 13)
          have r11557 := hand1 (x (-8) 4) (x (-8) 14)
          have r11558 := hand1 (x (-3) 2) (x (-3) 12)
          have r11559 := hand1 (x (-4) 3) (x (-4) 13)
          have r11560 := hand2 (x (-2) 2) (x (-2) 12)
          have r11561 := hand1 (x (-4) 4) (x (-4) 14)
          have b11562 := hb (x (-11) 7)
          have b11563 := hb (x (-10) 6)
          have b11564 := hb (x (-9) 5)
          have b11565 := hb (x (-9) 7)
          have b11566 := hb (x (-8) 4)
          have b11567 := hb (x (-8) 6)
          have b11568 := hb (x (-7) 3)
          have b11569 := hb (x (-7) 5)
          have b11570 := hb (x (-7) 7)
          have b11571 := hb (x (-7) 11)
          have b11572 := hb (x (-6) 2)
          have b11573 := hb (x (-6) 4)
          have b11574 := hb (x (-6) 5)
          have b11575 := hb (x (-6) 6)
          have b11576 := hb (x (-6) 10)
          have b11577 := hb (x (-5) 3)
          have b11578 := hb (x (-5) 5)
          have b11579 := hb (x (-5) 9)
          have b11580 := hb (x (-5) 11)
          have b11581 := hb (x (-5) 13)
          have b11582 := hb (x (-4) 2)
          have b11583 := hb (x (-4) 3)
          have b11584 := hb (x (-4) 4)
          have b11585 := hb (x (-4) 8)
          have b11586 := hb (x (-4) 10)
          have b11587 := hb (x (-4) 12)
          have b11588 := hb (x (-3) 2)
          have b11589 := hb (x (-3) 9)
          have b11590 := hb (x (-3) 11)
          have b11591 := hb (x (-3) 13)
          have b11592 := hb (x (-2) 8)
          have b11593 := hb (x (-2) 9)
          have b11594 := hb (x (-2) 10)
          have b11595 := hb (x (-2) 12)
          have b11596 := hb (x (-2) 13)
          have b11597 := hb (x (-1) 9)
          have b11598 := hb (x (-1) 10)
          have b11599 := hb (x (-1) 12)
          have b11600 := hb (x 0 8)
          have b11601 := hb (x 0 10)
          have b11602 := hb (x 3 5)
          have b11603 := hb (x 4 4)
          have b11604 := hb (x 2 2 && x 2 6)
          have b11605 := hb (x 1 3 && x 1 7)
          have b11606 := hb (x 0 4 && x 0 8)
          have b11607 := hb (x (-1) 5 && x (-1) 9)
          have b11608 := hb (x (-2) 6 && x (-2) 10)
          have b11609 := hb (x (-3) 7 && x (-3) 11)
          have b11610 := hb (x (-4) 8 && x (-4) 12)
          have b11611 := hb (x (-5) 9 && x (-5) 13)
          have b11612 := hb (x (-3) 1 && x (-3) 10)
          have b11613 := hb (x (-4) 2 && x (-4) 11)
          have b11614 := hb (x (-5) 3 && x (-5) 12)
          have b11615 := hb (x (-6) 4 && x (-6) 13)
          have b11616 := hb (x (-7) 5 && x (-7) 14)
          have b11617 := hb (x (-5) 1 && x (-5) 11)
          have b11618 := hb (x (-6) 2 && x (-6) 12)
          have b11619 := hb (x (-7) 3 && x (-7) 13)
          have b11620 := hb (x (-8) 4 && x (-8) 14)
          have b11621 := hb (x (-2) 1 && x (-2) 11)
          have b11622 := hb (x (-3) 2 && x (-3) 12)
          have b11623 := hb (x (-4) 3 && x (-4) 13)
          have b11624 := hb (x (-5) 4 && x (-5) 14)
          have b11625 := hb (x (-1) 1 && x (-1) 11)
          have b11626 := hb (x (-2) 2 && x (-2) 12)
          have b11627 := hb (x (-3) 3 && x (-3) 13)
          have b11628 := hb (x (-4) 4 && x (-4) 14)
          have b11629 := hb (x (-3) 1 && x (-3) 14)
          linarith only [r11508, e11509, e11510, e11511, e11512, e11513, e11514, r11515, e11516, e11517, e11518, e11519, e11520, e11521, r11522, e11523, e11524, e11525, e11526, e11527, e11528, r11529, e11530, e11531, r11532, e11533, e11534, r11535, e11536, e11537, r11538, e11539, e11540, r11541, r11542, r11543, r11544, r11545, r11546, r11547, r11548, r11549, r11550, r11551, r11552, r11553, r11554, r11555, r11556, r11557, r11558, r11559, r11560, r11561, b11562, b11563, b11564, b11565, b11566, b11567, b11568, b11569, b11570, b11571, b11572, b11573, b11574, b11575, b11576, b11577, b11578, b11579, b11580, b11581, b11582, b11583, b11584, b11585, b11586, b11587, b11588, b11589, b11590, b11591, b11592, b11593, b11594, b11595, b11596, b11597, b11598, b11599, b11600, b11601, b11602, b11603, b11604, b11605, b11606, b11607, b11608, b11609, b11610, b11611, b11612, b11613, b11614, b11615, b11616, b11617, b11618, b11619, b11620, b11621, b11622, b11623, b11624, b11625, b11626, b11627, b11628, b11629, d11492, g1, g2, g3, d11420, g6, d6315, g13, g15, g25, g27, g29, d11065, g30, g31, g32, g58, d11468, d6481, d11488, g70, g71, g82]
      · have f11630 : (x 1 7).toNat = 1 := by rw [h11055]; rfl
        have d11631 : (x 8 8).toNat = 0 := by
          have r11632 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
          have e11633 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e11634 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e11635 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e11636 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e11637 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e11638 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have b11639 := hb (x 1 7)
          have b11640 := hb (x 2 6)
          have b11641 := hb (x 3 5)
          have b11642 := hb (x 4 4)
          have b11643 := hb (x 5 11)
          have b11644 := hb (x 6 10)
          have b11645 := hb (x 7 9)
          have b11646 := hb (x 8 8)
          clear * - r11632 e11633 e11634 e11635 e11636 e11637 e11638 b11639 b11640 b11641 b11642 b11643 b11644 b11645 b11646 g27 g25 d6421 f11630
          omega
        have d11647 : (x 7 9).toNat = 0 := by
          have r11648 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
          have e11649 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e11650 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e11651 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e11652 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e11653 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e11654 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have b11655 := hb (x 1 7)
          have b11656 := hb (x 2 6)
          have b11657 := hb (x 3 5)
          have b11658 := hb (x 4 4)
          have b11659 := hb (x 5 11)
          have b11660 := hb (x 6 10)
          have b11661 := hb (x 7 9)
          have b11662 := hb (x 8 8)
          clear * - r11648 e11649 e11650 e11651 e11652 e11653 e11654 b11655 b11656 b11657 b11658 b11659 b11660 b11661 b11662 d11631 g27 g25 d6421 f11630
          omega
        have d11663 : (x 6 10).toNat = 0 := by
          have r11664 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
          have e11665 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e11666 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e11667 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e11668 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e11669 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e11670 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have b11671 := hb (x 1 7)
          have b11672 := hb (x 2 6)
          have b11673 := hb (x 3 5)
          have b11674 := hb (x 4 4)
          have b11675 := hb (x 5 11)
          have b11676 := hb (x 6 10)
          have b11677 := hb (x 7 9)
          have b11678 := hb (x 8 8)
          clear * - r11664 e11665 e11666 e11667 e11668 e11669 e11670 b11671 b11672 b11673 b11674 b11675 b11676 b11677 b11678 d11631 d11647 g27 g25 d6421 f11630
          omega
        have d11679 : (x 5 1 && x 5 11).toNat = 1 := by
          have r11680 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := hcov10 6
          have b11681 := hb (x 1 5)
          have b11682 := hb (x 6 10)
          have b11683 := hb (x 5 1 && x 5 11)
          have b11684 := hb (x 4 2 && x 4 12)
          have b11685 := hb (x 3 3 && x 3 13)
          have b11686 := hb (x 2 4 && x 2 14)
          clear * - r11680 b11681 b11682 b11683 b11684 b11685 b11686 d11663 g74 g75 d6405 d11037
          omega
        have d11687 : (x 5 11).toNat = 1 := by
          have r11688 := hand2 (x 5 1) (x 5 11)
          have b11689 := hb (x 5 11)
          have b11690 := hb (x 5 1 && x 5 11)
          clear * - r11688 b11689 b11690 d11679
          omega
        have r11691 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
        have e11692 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e11693 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e11694 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e11695 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e11696 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e11697 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b11698 := hb (x 1 7)
        have b11699 := hb (x 2 6)
        have b11700 := hb (x 3 5)
        have b11701 := hb (x 4 4)
        have b11702 := hb (x 5 11)
        have b11703 := hb (x 6 10)
        have b11704 := hb (x 7 9)
        have b11705 := hb (x 8 8)
        linarith only [r11691, e11692, e11693, e11694, e11695, e11696, e11697, b11698, b11699, b11700, b11701, b11702, b11703, b11704, b11705, d11631, d11647, d11663, d11687, g27, g25, d6421, f11630]
    · have f11706 : (x (-1) 4).toNat = 1 := by rw [h11053]; rfl
      have d11707 : (x (-1) 12).toNat = 1 := by
        have r11708 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
        have b11709 := hb (x (-1) 4)
        have b11710 := hb (x (-1) 12)
        clear * - r11708 b11709 b11710 f11706
        omega
      have d11711 : (x (-2) 13).toNat = 0 := by
        have r11712 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
        have e11713 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e11714 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b11715 := hb (x (-4) 3)
        have b11716 := hb (x (-3) 2)
        have b11717 := hb (x (-2) 13)
        have b11718 := hb (x (-1) 12)
        clear * - r11712 e11713 e11714 b11715 b11716 b11717 b11718 d11707
        omega
      have d11719 : (x (-4) 2).toNat = 1 := by
        have r11720 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := hcov13 (-2)
        have b11721 := hb (x (-4) 2)
        have b11722 := hb (x (-2) 13)
        have b11723 := hb (x (-3) 1 && x (-3) 14)
        clear * - r11720 b11721 b11722 b11723 d11711 g82
        omega
      have d11724 : (x (-4) 14).toNat = 1 := by
        have r11725 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
        have b11726 := hb (x (-4) 2)
        have b11727 := hb (x (-4) 14)
        clear * - r11725 b11726 b11727 d11719
        omega
      have d11728 : (x (-5) 1).toNat = 0 := by
        have r11729 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := hd14 (-4)
        have b11730 := hb (x (-5) 1)
        have b11731 := hb (x (-4) 14)
        clear * - r11729 b11730 b11731 d11724
        omega
      have d11732 : (x (-5) 13).toNat = 0 := by
        have r11733 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
        have b11734 := hb (x (-5) 1)
        have b11735 := hb (x (-5) 13)
        clear * - r11733 b11734 b11735 d11728
        omega
      have d11736 : (x (-3) 2).toNat = 0 := by
        have r11737 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
        have e11738 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e11739 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b11740 := hb (x (-4) 3)
        have b11741 := hb (x (-3) 2)
        have b11742 := hb (x (-2) 13)
        have b11743 := hb (x (-1) 12)
        clear * - r11737 e11738 e11739 b11740 b11741 b11742 b11743 d11707 d11711
        omega
      have d11744 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
        have r11745 := hand1 (x (-3) 2) (x (-3) 12)
        have b11746 := hb (x (-3) 2)
        have b11747 := hb (x (-3) 2 && x (-3) 12)
        clear * - r11745 b11746 b11747 d11736
        omega
      have d11748 : (x (-4) 3).toNat = 0 := by
        have r11749 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
        have e11750 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e11751 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b11752 := hb (x (-4) 3)
        have b11753 := hb (x (-3) 2)
        have b11754 := hb (x (-2) 13)
        have b11755 := hb (x (-1) 12)
        clear * - r11749 e11750 e11751 b11752 b11753 b11754 b11755 d11707 d11711 d11736
        omega
      have d11756 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
        have r11757 := hand1 (x (-4) 3) (x (-4) 14)
        have b11758 := hb (x (-4) 3)
        have b11759 := hb (x (-4) 3 && x (-4) 14)
        clear * - r11757 b11758 b11759 d11748
        omega
      have d11760 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
        have r11761 := hand1 (x (-4) 3) (x (-4) 13)
        have b11762 := hb (x (-4) 3)
        have b11763 := hb (x (-4) 3 && x (-4) 13)
        clear * - r11761 b11762 b11763 d11748
        omega
      have d11764 : (x (-2) 12).toNat = 0 := by
        have r11765 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := hd12 (-2)
        have e11766 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e11767 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have b11768 := hb (x (-5) 3)
        have b11769 := hb (x (-4) 2)
        have b11770 := hb (x (-3) 13)
        have b11771 := hb (x (-2) 12)
        clear * - r11765 e11766 e11767 b11768 b11769 b11770 b11771 g3 d11719
        omega
      have d11772 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
        have r11773 := hand2 (x (-2) 1) (x (-2) 12)
        have b11774 := hb (x (-2) 12)
        have b11775 := hb (x (-2) 1 && x (-2) 12)
        clear * - r11773 b11774 b11775 d11764
        omega
      have d11776 : (x (-5) 4).toNat = 1 := by
        have r11777 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := hcov11 (-1)
        have b11778 := hb (x (-5) 4)
        have b11779 := hb (x (-1) 11)
        have b11780 := hb (x (-2) 1 && x (-2) 12)
        have b11781 := hb (x (-3) 2 && x (-3) 13)
        have b11782 := hb (x (-4) 3 && x (-4) 14)
        clear * - r11777 b11778 b11779 b11780 b11781 b11782 d6457 d11772 g77 d11756
        omega
      have d11783 : (x (-5) 12).toNat = 1 := by
        have r11784 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
        have b11785 := hb (x (-5) 4)
        have b11786 := hb (x (-5) 12)
        clear * - r11784 b11785 b11786 d11776
        omega
      have d11787 : (x (-6) 13).toNat = 0 := by
        have r11788 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := hd12 (-5)
        have e11789 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
        have e11790 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
        have b11791 := hb (x (-8) 3)
        have b11792 := hb (x (-7) 2)
        have b11793 := hb (x (-6) 13)
        have b11794 := hb (x (-5) 12)
        clear * - r11788 e11789 e11790 b11791 b11792 b11793 b11794 d11783
        omega
      have d11795 : (x (-6) 5).toNat = 0 := by
        have r11796 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
        have b11797 := hb (x (-6) 5)
        have b11798 := hb (x (-6) 13)
        clear * - r11796 b11797 b11798 d11787
        omega
      have d11799 : (x (-7) 2).toNat = 0 := by
        have r11800 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := hd12 (-5)
        have e11801 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
        have e11802 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
        have b11803 := hb (x (-8) 3)
        have b11804 := hb (x (-7) 2)
        have b11805 := hb (x (-6) 13)
        have b11806 := hb (x (-5) 12)
        clear * - r11800 e11801 e11802 b11803 b11804 b11805 b11806 d11783 d11787
        omega
      have d11807 : (x (-6) 1 && x (-6) 14).toNat = 1 := by
        have r11808 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := hcov13 (-5)
        have b11809 := hb (x (-7) 2)
        have b11810 := hb (x (-5) 13)
        have b11811 := hb (x (-6) 1 && x (-6) 14)
        clear * - r11808 b11809 b11810 b11811 d11732 d11799
        omega
      have d11812 : (x (-6) 1).toNat = 1 := by
        have r11813 := hand1 (x (-6) 1) (x (-6) 14)
        have b11814 := hb (x (-6) 1)
        have b11815 := hb (x (-6) 1 && x (-6) 14)
        clear * - r11813 b11814 b11815 d11807
        omega
      have d11816 : (x (-5) 14).toNat = 0 := by
        have r11817 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := hd14 (-5)
        have b11818 := hb (x (-6) 1)
        have b11819 := hb (x (-5) 14)
        clear * - r11817 b11818 b11819 d11812
        omega
      have d11820 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
        have r11821 := hand2 (x (-5) 4) (x (-5) 14)
        have b11822 := hb (x (-5) 14)
        have b11823 := hb (x (-5) 4 && x (-5) 14)
        clear * - r11821 b11822 b11823 d11816
        omega
      have r11824 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := hcov10 (-1)
      have b11825 := hb (x (-6) 5)
      have b11826 := hb (x (-1) 10)
      have b11827 := hb (x (-2) 1 && x (-2) 11)
      have b11828 := hb (x (-3) 2 && x (-3) 12)
      have b11829 := hb (x (-4) 3 && x (-4) 13)
      have b11830 := hb (x (-5) 4 && x (-5) 14)
      linarith only [r11824, b11825, b11826, b11827, b11828, b11829, b11830, d6315, d6481, d11744, d11760, d11820, d11795]

theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b0000101 (x : ℤ → Fin 16 → Bool)
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
    (g4 : (x (-2) 14).toNat = 1)
    (g5 : (x (-1) 5).toNat = 0)
    (g6 : (x (-1) 9).toNat = 0)
    (g7 : (x (-1) 13).toNat = 0)
    (g8 : (x 0 2).toNat = 0)
    (g9 : (x 0 3).toNat = 0)
    (g10 : (x 0 4).toNat = 0)
    (g11 : (x 0 5).toNat = 0)
    (g12 : (x 0 7).toNat = 0)
    (g13 : (x 0 8).toNat = 0)
    (g14 : (x 0 9).toNat = 0)
    (g15 : (x 0 10).toNat = 0)
    (g16 : (x 0 11).toNat = 0)
    (g17 : (x 0 12).toNat = 0)
    (g18 : (x 0 13).toNat = 0)
    (g19 : (x 0 14).toNat = 1)
    (g20 : (x 1 4).toNat = 1)
    (g21 : (x 1 8).toNat = 0)
    (g22 : (x 1 14).toNat = 1)
    (g23 : (x 2 2).toNat = 0)
    (g24 : (x 2 10).toNat = 0)
    (g25 : (x 3 5).toNat = 0)
    (g26 : (x 3 13).toNat = 0)
    (g27 : (x 4 4).toNat = 0)
    (g28 : (x 4 12).toNat = 0)
    (g29 : (x 2 2 && x 2 6).toNat = 0)
    (g30 : (x 0 4 && x 0 8).toNat = 0)
    (g31 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g32 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g33 : (x 4 4 && x 4 8).toNat = 0)
    (g34 : (x 3 5 && x 3 9).toNat = 0)
    (g35 : (x 2 6 && x 2 10).toNat = 0)
    (g36 : (x 0 8 && x 0 12).toNat = 0)
    (g37 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g38 : (x 1 8 && x 1 12).toNat = 0)
    (g39 : (x 0 9 && x 0 13).toNat = 0)
    (g40 : (x 2 5 && x 2 10).toNat = 0)
    (g41 : (x 0 7 && x 0 12).toNat = 0)
    (g42 : (x (-1) 8 && x (-1) 13).toNat = 0)
    (g43 : (x 1 8 && x 1 13).toNat = 0)
    (g44 : (x 0 9 && x 0 14).toNat = 0)
    (g45 : (x 4 7 && x 4 12).toNat = 0)
    (g46 : (x 3 8 && x 3 13).toNat = 0)
    (g47 : (x 4 4 && x 4 10).toNat = 0)
    (g48 : (x 3 5 && x 3 11).toNat = 0)
    (g49 : (x 0 8 && x 0 14).toNat = 0)
    (g50 : (x 1 8 && x 1 14).toNat = 0)
    (g51 : (x 4 6 && x 4 12).toNat = 0)
    (g52 : (x 3 7 && x 3 13).toNat = 0)
    (g53 : (x 0 7 && x 0 14).toNat = 0)
    (g54 : (x 4 4 && x 4 11).toNat = 0)
    (g55 : (x 3 5 && x 3 12).toNat = 0)
    (g56 : (x 4 5 && x 4 12).toNat = 0)
    (g57 : (x 3 6 && x 3 13).toNat = 0)
    (g58 : (x (-3) 1 && x (-3) 10).toNat = 0)
    (g59 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g60 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g61 : (x (-3) 3 && x (-3) 12).toNat = 0)
    (g62 : (x 0 1 && x 0 10).toNat = 0)
    (g63 : (x (-3) 4 && x (-3) 13).toNat = 0)
    (g64 : (x 0 2 && x 0 11).toNat = 0)
    (g65 : (x (-3) 5 && x (-3) 14).toNat = 0)
    (g66 : (x 4 3 && x 4 12).toNat = 0)
    (g67 : (x 3 4 && x 3 13).toNat = 0)
    (g68 : (x 4 4 && x 4 13).toNat = 0)
    (g69 : (x 3 5 && x 3 14).toNat = 0)
    (g70 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g71 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g72 : (x 0 2 && x 0 12).toNat = 0)
    (g73 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g74 : (x 4 2 && x 4 12).toNat = 0)
    (g75 : (x 3 3 && x 3 13).toNat = 0)
    (g76 : (x 4 4 && x 4 14).toNat = 0)
    (g77 : (x (-3) 2 && x (-3) 13).toNat = 0)
    (g78 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g79 : (x (-3) 3 && x (-3) 14).toNat = 0)
    (g80 : (x 0 1 && x 0 12).toNat = 0)
    (g81 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g82 : (x (-3) 1 && x (-3) 14).toNat = 0)
    (g83 : (x 0 1 && x 0 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b0000101_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83
