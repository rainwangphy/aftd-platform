import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0000101

Topic: combinatorics   Node: 5e4b88c904d1

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core: under the layer-free tight-cover constraints for k = 15 and 35 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0000101_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-2) 5).toNat = 0)
    (g1 : (x (-2) 11).toNat = 0)
    (g2 : (x (-2) 13).toNat = 0)
    (g3 : (x 0 3).toNat = 0)
    (g4 : (x 0 6).toNat = 0)
    (g5 : (x 0 7).toNat = 0)
    (g6 : (x 0 9).toNat = 1)
    (g7 : (x 0 11).toNat = 0)
    (g8 : (x 1 2).toNat = 0)
    (g9 : (x 1 4).toNat = 0)
    (g10 : (x 1 6).toNat = 0)
    (g11 : (x 1 10).toNat = 0)
    (g12 : (x 2 1).toNat = 1)
    (g13 : (x 2 4).toNat = 0)
    (g14 : (x 3 2).toNat = 0)
    (g15 : (x 3 4).toNat = 0)
    (g16 : (x 1 2 && x 1 6).toNat = 0)
    (g17 : (x 0 3 && x 0 7).toNat = 0)
    (g18 : (x (-1) 4 && x (-1) 8).toNat = 0)
    (g19 : (x (-2) 5 && x (-2) 9).toNat = 0)
    (g20 : (x 0 1 && x 0 7).toNat = 0)
    (g21 : (x (-1) 2 && x (-1) 8).toNat = 0)
    (g22 : (x (-2) 3 && x (-2) 9).toNat = 0)
    (g23 : (x 3 3 && x 3 12).toNat = 0)
    (g24 : (x 2 4 && x 2 13).toNat = 0)
    (g25 : (x 1 5 && x 1 14).toNat = 0)
    (g26 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g27 : (x 0 1 && x 0 11).toNat = 0)
    (g28 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g29 : (x 2 1 && x 2 12).toNat = 0)
    (g30 : (x 1 2 && x 1 13).toNat = 0)
    (g31 : (x 0 3 && x 0 14).toNat = 0)
    (g32 : (x 3 2 && x 3 13).toNat = 0)
    (g33 : (x 3 3 && x 3 14).toNat = 0)
    (g34 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d28372 : (x 1 8).toNat = 0 := by
    have r28373 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
    have e28374 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e28375 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e28376 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e28377 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e28378 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e28379 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b28380 := hb (x (-6) 7)
    have b28381 := hb (x (-5) 6)
    have b28382 := hb (x (-4) 5)
    have b28383 := hb (x (-3) 4)
    have b28384 := hb (x (-2) 11)
    have b28385 := hb (x (-1) 10)
    have b28386 := hb (x 0 9)
    have b28387 := hb (x 1 8)
    clear * - r28373 e28374 e28375 e28376 e28377 e28378 e28379 b28380 b28381 b28382 b28383 b28384 b28385 b28386 b28387 g6 g1
    omega
  have d28388 : (x (-1) 10).toNat = 0 := by
    have r28389 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
    have e28390 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e28391 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e28392 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e28393 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e28394 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e28395 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b28396 := hb (x (-6) 7)
    have b28397 := hb (x (-5) 6)
    have b28398 := hb (x (-4) 5)
    have b28399 := hb (x (-3) 4)
    have b28400 := hb (x (-2) 11)
    have b28401 := hb (x (-1) 10)
    have b28402 := hb (x 0 9)
    have b28403 := hb (x 1 8)
    clear * - r28389 e28390 e28391 e28392 e28393 e28394 e28395 b28396 b28397 b28398 b28399 b28400 b28401 b28402 b28403 d28372 g6 g1
    omega
  have d28404 : (x (-3) 4).toNat = 0 := by
    have r28405 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
    have e28406 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e28407 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e28408 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e28409 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e28410 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e28411 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b28412 := hb (x (-6) 7)
    have b28413 := hb (x (-5) 6)
    have b28414 := hb (x (-4) 5)
    have b28415 := hb (x (-3) 4)
    have b28416 := hb (x (-2) 11)
    have b28417 := hb (x (-1) 10)
    have b28418 := hb (x 0 9)
    have b28419 := hb (x 1 8)
    clear * - r28405 e28406 e28407 e28408 e28409 e28410 e28411 b28412 b28413 b28414 b28415 b28416 b28417 b28418 b28419 d28372 g6 d28388 g1
    omega
  have d28420 : (x (-3) 4 && x (-3) 14).toNat = 0 := by
    have r28421 := hand1 (x (-3) 4) (x (-3) 14)
    have b28422 := hb (x (-3) 4)
    have b28423 := hb (x (-3) 4 && x (-3) 14)
    clear * - r28421 b28422 b28423 d28404
    omega
  have d28424 : (x (-3) 4 && x (-3) 10).toNat = 0 := by
    have r28425 := hand1 (x (-3) 4) (x (-3) 10)
    have b28426 := hb (x (-3) 4)
    have b28427 := hb (x (-3) 4 && x (-3) 10)
    clear * - r28425 b28426 b28427 d28404
    omega
  have d28428 : (x (-4) 5).toNat = 0 := by
    have r28429 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
    have e28430 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e28431 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e28432 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e28433 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e28434 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e28435 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b28436 := hb (x (-6) 7)
    have b28437 := hb (x (-5) 6)
    have b28438 := hb (x (-4) 5)
    have b28439 := hb (x (-3) 4)
    have b28440 := hb (x (-2) 11)
    have b28441 := hb (x (-1) 10)
    have b28442 := hb (x 0 9)
    have b28443 := hb (x 1 8)
    clear * - r28429 e28430 e28431 e28432 e28433 e28434 e28435 b28436 b28437 b28438 b28439 b28440 b28441 b28442 b28443 d28372 g6 d28388 g1 d28404
    omega
  have d28444 : (x (-4) 5 && x (-4) 11).toNat = 0 := by
    have r28445 := hand1 (x (-4) 5) (x (-4) 11)
    have b28446 := hb (x (-4) 5)
    have b28447 := hb (x (-4) 5 && x (-4) 11)
    clear * - r28445 b28446 b28447 d28428
    omega
  have d28448 : (x (-1) 2 && x (-1) 12).toNat = 1 := by
    have r28449 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := hcov10 1
    have b28450 := hb (x (-4) 5)
    have b28451 := hb (x 1 10)
    have b28452 := hb (x 0 1 && x 0 11)
    have b28453 := hb (x (-1) 2 && x (-1) 12)
    have b28454 := hb (x (-2) 3 && x (-2) 13)
    have b28455 := hb (x (-3) 4 && x (-3) 14)
    clear * - r28449 b28450 b28451 b28452 b28453 b28454 b28455 g11 g27 g28 d28420 d28428
    omega
  have d28456 : (x (-1) 12).toNat = 1 := by
    have r28457 := hand2 (x (-1) 2) (x (-1) 12)
    have b28458 := hb (x (-1) 12)
    have b28459 := hb (x (-1) 2 && x (-1) 12)
    clear * - r28457 b28458 b28459 d28448
    omega
  have d28460 : (x (-3) 2).toNat = 0 := by
    have r28461 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
    have e28462 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e28463 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b28464 := hb (x (-4) 3)
    have b28465 := hb (x (-3) 2)
    have b28466 := hb (x (-2) 13)
    have b28467 := hb (x (-1) 12)
    clear * - r28461 e28462 e28463 b28464 b28465 b28466 b28467 d28456 g2
    omega
  have d28468 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
    have r28469 := hand1 (x (-3) 2) (x (-3) 12)
    have b28470 := hb (x (-3) 2)
    have b28471 := hb (x (-3) 2 && x (-3) 12)
    clear * - r28469 b28470 b28471 d28460
    omega
  have d28472 : (x (-3) 10).toNat = 0 := by
    have r28473 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
    have b28474 := hb (x (-3) 2)
    have b28475 := hb (x (-3) 10)
    clear * - r28473 b28474 b28475 d28460
    omega
  have d28476 : (x (-3) 6 && x (-3) 10).toNat = 0 := by
    have r28477 := hand2 (x (-3) 6) (x (-3) 10)
    have b28478 := hb (x (-3) 10)
    have b28479 := hb (x (-3) 6 && x (-3) 10)
    clear * - r28477 b28478 b28479 d28472
    omega
  have d28480 : (x (-4) 3).toNat = 0 := by
    have r28481 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
    have e28482 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e28483 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b28484 := hb (x (-4) 3)
    have b28485 := hb (x (-3) 2)
    have b28486 := hb (x (-2) 13)
    have b28487 := hb (x (-1) 12)
    clear * - r28481 e28482 e28483 b28484 b28485 b28486 b28487 d28456 g2 d28460
    omega
  have d28488 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
    have r28489 := hand1 (x (-4) 3) (x (-4) 13)
    have b28490 := hb (x (-4) 3)
    have b28491 := hb (x (-4) 3 && x (-4) 13)
    clear * - r28489 b28490 b28491 d28480
    omega
  have d28492 : (x (-4) 11).toNat = 0 := by
    have r28493 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
    have b28494 := hb (x (-4) 3)
    have b28495 := hb (x (-4) 11)
    clear * - r28493 b28494 b28495 d28480
    omega
  have d28496 : (x (-4) 7 && x (-4) 11).toNat = 0 := by
    have r28497 := hand2 (x (-4) 7) (x (-4) 11)
    have b28498 := hb (x (-4) 11)
    have b28499 := hb (x (-4) 7 && x (-4) 11)
    clear * - r28497 b28498 b28499 d28492
    omega
  have d28500 : (x (-5) 6).toNat = 0 := by
    have r28501 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
    have e28502 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e28503 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e28504 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e28505 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e28506 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e28507 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b28508 := hb (x (-6) 7)
    have b28509 := hb (x (-5) 6)
    have b28510 := hb (x (-4) 5)
    have b28511 := hb (x (-3) 4)
    have b28512 := hb (x (-2) 11)
    have b28513 := hb (x (-1) 10)
    have b28514 := hb (x 0 9)
    have b28515 := hb (x 1 8)
    clear * - r28501 e28502 e28503 e28504 e28505 e28506 e28507 b28508 b28509 b28510 b28511 b28512 b28513 b28514 b28515 d28372 g6 d28388 g1 d28404 d28428
    omega
  have d28516 : (x (-5) 6 && x (-5) 12).toNat = 0 := by
    have r28517 := hand1 (x (-5) 6) (x (-5) 12)
    have b28518 := hb (x (-5) 6)
    have b28519 := hb (x (-5) 6 && x (-5) 12)
    clear * - r28517 b28518 b28519 d28500
    omega
  have d28520 : (x (-6) 7).toNat = 0 := by
    have r28521 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
    have e28522 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e28523 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e28524 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e28525 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e28526 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e28527 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b28528 := hb (x (-6) 7)
    have b28529 := hb (x (-5) 6)
    have b28530 := hb (x (-4) 5)
    have b28531 := hb (x (-3) 4)
    have b28532 := hb (x (-2) 11)
    have b28533 := hb (x (-1) 10)
    have b28534 := hb (x 0 9)
    have b28535 := hb (x 1 8)
    clear * - r28521 e28522 e28523 e28524 e28525 e28526 e28527 b28528 b28529 b28530 b28531 b28532 b28533 b28534 b28535 d28372 g6 d28388 g1 d28404 d28428 d28500
    omega
  have d28536 : (x (-6) 7 && x (-6) 13).toNat = 0 := by
    have r28537 := hand1 (x (-6) 7) (x (-6) 13)
    have b28538 := hb (x (-6) 7)
    have b28539 := hb (x (-6) 7 && x (-6) 13)
    clear * - r28537 b28538 b28539 d28520
    omega
  cases h28540 : x 1 1
  · have f28541 : (x 1 1).toNat = 0 := by rw [h28540]; rfl
    cases h28542 : x 1 3
    · have f28543 : (x 1 3).toNat = 0 := by rw [h28542]; rfl
      cases h28544 : x (-1) 4
      · have f28545 : (x (-1) 4).toNat = 0 := by rw [h28544]; rfl
        have d28546 : (x 3 11).toNat = 1 := by
          have r28547 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := hcov11 3
          have b28548 := hb (x (-1) 4)
          have b28549 := hb (x 3 11)
          have b28550 := hb (x 2 1 && x 2 12)
          have b28551 := hb (x 1 2 && x 1 13)
          have b28552 := hb (x 0 3 && x 0 14)
          clear * - r28547 b28548 b28549 b28550 b28551 b28552 g29 g30 g31 f28545
          omega
        have d28553 : (x 3 3).toNat = 1 := by
          have r28554 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
          have b28555 := hb (x 3 3)
          have b28556 := hb (x 3 11)
          clear * - r28554 b28555 b28556 d28546
          omega
        have d28557 : (x 6 12).toNat = 0 := by
          have r28558 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
          have e28559 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e28560 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b28561 := hb (x 3 3)
          have b28562 := hb (x 4 2)
          have b28563 := hb (x 5 13)
          have b28564 := hb (x 6 12)
          clear * - r28558 e28559 e28560 b28561 b28562 b28563 b28564 d28553
          omega
        have d28565 : (x 6 1 && x 6 12).toNat = 0 := by
          have r28566 := hand2 (x 6 1) (x 6 12)
          have b28567 := hb (x 6 12)
          have b28568 := hb (x 6 1 && x 6 12)
          clear * - r28566 b28567 b28568 d28557
          omega
        have d28569 : (x 6 4).toNat = 0 := by
          have r28570 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
          have b28571 := hb (x 6 4)
          have b28572 := hb (x 6 12)
          clear * - r28570 b28571 b28572 d28557
          omega
        have d28573 : (x 5 13).toNat = 0 := by
          have r28574 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
          have e28575 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e28576 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b28577 := hb (x 3 3)
          have b28578 := hb (x 4 2)
          have b28579 := hb (x 5 13)
          have b28580 := hb (x 6 12)
          clear * - r28574 e28575 e28576 b28577 b28578 b28579 b28580 d28557 d28553
          omega
        have d28581 : (x 5 2 && x 5 13).toNat = 0 := by
          have r28582 := hand2 (x 5 2) (x 5 13)
          have b28583 := hb (x 5 13)
          have b28584 := hb (x 5 2 && x 5 13)
          clear * - r28582 b28583 b28584 d28573
          omega
        have d28585 : (x 4 1 && x 4 14).toNat = 1 := by
          have r28586 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := hcov13 5
          have b28587 := hb (x 3 2)
          have b28588 := hb (x 5 13)
          have b28589 := hb (x 4 1 && x 4 14)
          clear * - r28586 b28587 b28588 b28589 d28573 g14
          omega
        have d28590 : (x 4 1).toNat = 1 := by
          have r28591 := hand1 (x 4 1) (x 4 14)
          have b28592 := hb (x 4 1)
          have b28593 := hb (x 4 1 && x 4 14)
          clear * - r28591 b28592 b28593 d28585
          omega
        have d28594 : (x 5 14).toNat = 0 := by
          have r28595 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
          have b28596 := hb (x 4 1)
          have b28597 := hb (x 5 14)
          clear * - r28595 b28596 b28597 d28590
          omega
        have d28598 : (x 5 1 && x 5 14).toNat = 0 := by
          have r28599 := hand2 (x 5 1) (x 5 14)
          have b28600 := hb (x 5 14)
          have b28601 := hb (x 5 1 && x 5 14)
          clear * - r28599 b28600 b28601 d28594
          omega
        have d28602 : (x 5 2).toNat = 0 := by
          have r28603 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
          have b28604 := hb (x 5 2)
          have b28605 := hb (x 5 14)
          clear * - r28603 b28604 b28605 d28594
          omega
        have d28606 : (x 4 2).toNat = 0 := by
          have r28607 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
          have e28608 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e28609 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b28610 := hb (x 3 3)
          have b28611 := hb (x 4 2)
          have b28612 := hb (x 5 13)
          have b28613 := hb (x 6 12)
          clear * - r28607 e28608 e28609 b28610 b28611 b28612 b28613 d28557 d28573 d28553
          omega
        have d28614 : (x 4 2 && x 4 13).toNat = 0 := by
          have r28615 := hand1 (x 4 2) (x 4 13)
          have b28616 := hb (x 4 2)
          have b28617 := hb (x 4 2 && x 4 13)
          clear * - r28615 b28616 b28617 d28606
          omega
        have d28618 : (x 6 13).toNat = 1 := by
          have r28619 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := hcov13 6
          have b28620 := hb (x 4 2)
          have b28621 := hb (x 6 13)
          have b28622 := hb (x 5 1 && x 5 14)
          clear * - r28619 b28620 b28621 b28622 d28598 d28606
          omega
        have d28623 : (x 6 1).toNat = 1 := by
          have r28624 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
          have b28625 := hb (x 6 1)
          have b28626 := hb (x 6 13)
          clear * - r28624 b28625 b28626 d28618
          omega
        have d28627 : (x 7 14).toNat = 0 := by
          have r28628 : (x 7 14).toNat + (x 6 1).toNat = 1 := hd14 7
          have b28629 := hb (x 6 1)
          have b28630 := hb (x 7 14)
          clear * - r28628 b28629 b28630 d28623
          omega
        have d28631 : (x 7 3 && x 7 14).toNat = 0 := by
          have r28632 := hand2 (x 7 3) (x 7 14)
          have b28633 := hb (x 7 14)
          have b28634 := hb (x 7 3 && x 7 14)
          clear * - r28632 b28633 b28634 d28627
          omega
        have d28635 : (x 7 2).toNat = 0 := by
          have r28636 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
          have b28637 := hb (x 7 2)
          have b28638 := hb (x 7 14)
          clear * - r28636 b28637 b28638 d28627
          omega
        have d28639 : (x 7 12).toNat = 0 := by
          have r28640 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
          have e28641 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
          have e28642 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
          have b28643 := hb (x 4 3)
          have b28644 := hb (x 5 2)
          have b28645 := hb (x 6 13)
          have b28646 := hb (x 7 12)
          clear * - r28640 e28641 e28642 b28643 b28644 b28645 b28646 d28618 d28602
          omega
        have d28647 : (x 7 4).toNat = 0 := by
          have r28648 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
          have b28649 := hb (x 7 4)
          have b28650 := hb (x 7 12)
          clear * - r28648 b28649 b28650 d28639
          omega
        have d28651 : (x 4 3).toNat = 0 := by
          have r28652 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
          have e28653 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
          have e28654 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
          have b28655 := hb (x 4 3)
          have b28656 := hb (x 5 2)
          have b28657 := hb (x 6 13)
          have b28658 := hb (x 7 12)
          clear * - r28652 e28653 e28654 b28655 b28656 b28657 b28658 d28639 d28618 d28602
          omega
        have d28659 : (x 4 3 && x 4 14).toNat = 0 := by
          have r28660 := hand1 (x 4 3) (x 4 14)
          have b28661 := hb (x 4 3)
          have b28662 := hb (x 4 3 && x 4 14)
          clear * - r28660 b28661 b28662 d28651
          omega
        have d28663 : (x 7 11).toNat = 1 := by
          have r28664 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := hcov11 7
          have b28665 := hb (x 3 4)
          have b28666 := hb (x 7 11)
          have b28667 := hb (x 6 1 && x 6 12)
          have b28668 := hb (x 5 2 && x 5 13)
          have b28669 := hb (x 4 3 && x 4 14)
          clear * - r28664 b28665 b28666 b28667 b28668 b28669 d28565 d28581 d28659 g15
          omega
        have d28670 : (x 7 3).toNat = 1 := by
          have r28671 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
          have b28672 := hb (x 7 3)
          have b28673 := hb (x 7 11)
          clear * - r28671 b28672 b28673 d28663
          omega
        have d28674 : (x 10 12).toNat = 0 := by
          have r28675 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
          have e28676 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
          have e28677 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
          have b28678 := hb (x 7 3)
          have b28679 := hb (x 8 2)
          have b28680 := hb (x 9 13)
          have b28681 := hb (x 10 12)
          clear * - r28675 e28676 e28677 b28678 b28679 b28680 b28681 d28670
          omega
        have d28682 : (x 10 1 && x 10 12).toNat = 0 := by
          have r28683 := hand2 (x 10 1) (x 10 12)
          have b28684 := hb (x 10 12)
          have b28685 := hb (x 10 1 && x 10 12)
          clear * - r28683 b28684 b28685 d28674
          omega
        have d28686 : (x 10 4).toNat = 0 := by
          have r28687 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
          have b28688 := hb (x 10 4)
          have b28689 := hb (x 10 12)
          clear * - r28687 b28688 b28689 d28674
          omega
        have d28690 : (x 9 13).toNat = 0 := by
          have r28691 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
          have e28692 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
          have e28693 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
          have b28694 := hb (x 7 3)
          have b28695 := hb (x 8 2)
          have b28696 := hb (x 9 13)
          have b28697 := hb (x 10 12)
          clear * - r28691 e28692 e28693 b28694 b28695 b28696 b28697 d28674 d28670
          omega
        have d28698 : (x 9 2 && x 9 13).toNat = 0 := by
          have r28699 := hand2 (x 9 2) (x 9 13)
          have b28700 := hb (x 9 13)
          have b28701 := hb (x 9 2 && x 9 13)
          clear * - r28699 b28700 b28701 d28690
          omega
        have d28702 : (x 8 1 && x 8 14).toNat = 1 := by
          have r28703 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := hcov13 9
          have b28704 := hb (x 7 2)
          have b28705 := hb (x 9 13)
          have b28706 := hb (x 8 1 && x 8 14)
          clear * - r28703 b28704 b28705 b28706 d28690 d28635
          omega
        have d28707 : (x 8 14).toNat = 1 := by
          have r28708 := hand2 (x 8 1) (x 8 14)
          have b28709 := hb (x 8 14)
          have b28710 := hb (x 8 1 && x 8 14)
          clear * - r28708 b28709 b28710 d28702
          omega
        have d28711 : (x 7 1).toNat = 0 := by
          have r28712 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
          have b28713 := hb (x 7 1)
          have b28714 := hb (x 8 14)
          clear * - r28712 b28713 b28714 d28707
          omega
        have d28715 : (x 7 13).toNat = 0 := by
          have r28716 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
          have b28717 := hb (x 7 1)
          have b28718 := hb (x 7 13)
          clear * - r28716 b28717 b28718 d28711
          omega
        have d28719 : (x 6 1 && x 6 14).toNat = 1 := by
          have r28720 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
          have b28721 := hb (x 5 2)
          have b28722 := hb (x 7 13)
          have b28723 := hb (x 6 1 && x 6 14)
          clear * - r28720 b28721 b28722 b28723 d28715 d28602
          omega
        have d28724 : (x 6 14).toNat = 1 := by
          have r28725 := hand2 (x 6 1) (x 6 14)
          have b28726 := hb (x 6 14)
          have b28727 := hb (x 6 1 && x 6 14)
          clear * - r28725 b28726 b28727 d28719
          omega
        have d28728 : (x 5 1).toNat = 0 := by
          have r28729 : (x 6 14).toNat + (x 5 1).toNat = 1 := hd14 6
          have b28730 := hb (x 5 1)
          have b28731 := hb (x 6 14)
          clear * - r28729 b28730 b28731 d28724
          omega
        have d28732 : (x 5 1 && x 5 12).toNat = 0 := by
          have r28733 := hand1 (x 5 1) (x 5 12)
          have b28734 := hb (x 5 1)
          have b28735 := hb (x 5 1 && x 5 12)
          clear * - r28733 b28734 b28735 d28728
          omega
        have d28736 : (x 6 11).toNat = 1 := by
          have r28737 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := hcov11 6
          have b28738 := hb (x 2 4)
          have b28739 := hb (x 6 11)
          have b28740 := hb (x 5 1 && x 5 12)
          have b28741 := hb (x 4 2 && x 4 13)
          have b28742 := hb (x 3 3 && x 3 14)
          clear * - r28737 b28738 b28739 b28740 b28741 b28742 d28732 d28614 g33 g13
          omega
        have d28743 : (x 6 3).toNat = 1 := by
          have r28744 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
          have b28745 := hb (x 6 3)
          have b28746 := hb (x 6 11)
          clear * - r28744 b28745 b28746 d28736
          omega
        have d28747 : (x 9 12).toNat = 0 := by
          have r28748 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
          have e28749 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
          have e28750 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
          have b28751 := hb (x 6 3)
          have b28752 := hb (x 7 2)
          have b28753 := hb (x 8 13)
          have b28754 := hb (x 9 12)
          clear * - r28748 e28749 e28750 b28751 b28752 b28753 b28754 d28635 d28743
          omega
        have d28755 : (x 9 1 && x 9 12).toNat = 0 := by
          have r28756 := hand2 (x 9 1) (x 9 12)
          have b28757 := hb (x 9 12)
          have b28758 := hb (x 9 1 && x 9 12)
          clear * - r28756 b28757 b28758 d28747
          omega
        have d28759 : (x 8 13).toNat = 0 := by
          have r28760 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
          have e28761 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
          have e28762 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
          have b28763 := hb (x 6 3)
          have b28764 := hb (x 7 2)
          have b28765 := hb (x 8 13)
          have b28766 := hb (x 9 12)
          clear * - r28760 e28761 e28762 b28763 b28764 b28765 b28766 d28747 d28635 d28743
          omega
        have d28767 : (x 8 2 && x 8 13).toNat = 0 := by
          have r28768 := hand2 (x 8 2) (x 8 13)
          have b28769 := hb (x 8 13)
          have b28770 := hb (x 8 2 && x 8 13)
          clear * - r28768 b28769 b28770 d28759
          omega
        have d28771 : (x 10 11).toNat = 1 := by
          have r28772 : 1 ≤ (x 10 11).toNat + (x 9 1 && x 9 12).toNat + (x 8 2 && x 8 13).toNat + (x 7 3 && x 7 14).toNat + (x 6 4).toNat := hcov11 10
          have b28773 := hb (x 6 4)
          have b28774 := hb (x 10 11)
          have b28775 := hb (x 9 1 && x 9 12)
          have b28776 := hb (x 8 2 && x 8 13)
          have b28777 := hb (x 7 3 && x 7 14)
          clear * - r28772 b28773 b28774 b28775 b28776 b28777 d28755 d28767 d28631 d28569
          omega
        have d28778 : (x 10 3).toNat = 1 := by
          have r28779 : (x 10 11).toNat ≤ (x 10 3).toNat := himp _ _ (hp11 10)
          have b28780 := hb (x 10 3)
          have b28781 := hb (x 10 11)
          clear * - r28779 b28780 b28781 d28771
          omega
        have d28782 : (x 13 12).toNat = 0 := by
          have r28783 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
          have e28784 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
          have e28785 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
          have b28786 := hb (x 10 3)
          have b28787 := hb (x 11 2)
          have b28788 := hb (x 12 13)
          have b28789 := hb (x 13 12)
          clear * - r28783 e28784 e28785 b28786 b28787 b28788 b28789 d28778
          omega
        have d28790 : (x 13 1 && x 13 12).toNat = 0 := by
          have r28791 := hand2 (x 13 1) (x 13 12)
          have b28792 := hb (x 13 12)
          have b28793 := hb (x 13 1 && x 13 12)
          clear * - r28791 b28792 b28793 d28782
          omega
        have d28794 : (x 12 13).toNat = 0 := by
          have r28795 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
          have e28796 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
          have e28797 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
          have b28798 := hb (x 10 3)
          have b28799 := hb (x 11 2)
          have b28800 := hb (x 12 13)
          have b28801 := hb (x 13 12)
          clear * - r28795 e28796 e28797 b28798 b28799 b28800 b28801 d28782 d28778
          omega
        have d28802 : (x 12 2 && x 12 13).toNat = 0 := by
          have r28803 := hand2 (x 12 2) (x 12 13)
          have b28804 := hb (x 12 13)
          have b28805 := hb (x 12 2 && x 12 13)
          clear * - r28803 b28804 b28805 d28794
          omega
        have d28806 : (x 11 2).toNat = 0 := by
          have r28807 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
          have e28808 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
          have e28809 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
          have b28810 := hb (x 10 3)
          have b28811 := hb (x 11 2)
          have b28812 := hb (x 12 13)
          have b28813 := hb (x 13 12)
          clear * - r28807 e28808 e28809 b28810 b28811 b28812 b28813 d28782 d28794 d28778
          omega
        have d28814 : (x 8 1).toNat = 1 := by
          have r28815 := hand1 (x 8 1) (x 8 14)
          have b28816 := hb (x 8 1)
          have b28817 := hb (x 8 1 && x 8 14)
          clear * - r28815 b28816 b28817 d28702
          omega
        have d28818 : (x 9 14).toNat = 0 := by
          have r28819 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
          have b28820 := hb (x 8 1)
          have b28821 := hb (x 9 14)
          clear * - r28819 b28820 b28821 d28814
          omega
        have d28822 : (x 9 1 && x 9 14).toNat = 0 := by
          have r28823 := hand2 (x 9 1) (x 9 14)
          have b28824 := hb (x 9 14)
          have b28825 := hb (x 9 1 && x 9 14)
          clear * - r28823 b28824 b28825 d28818
          omega
        have d28826 : (x 9 2).toNat = 0 := by
          have r28827 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
          have b28828 := hb (x 9 2)
          have b28829 := hb (x 9 14)
          clear * - r28827 b28828 b28829 d28818
          omega
        have d28830 : (x 8 2).toNat = 0 := by
          have r28831 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
          have e28832 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
          have e28833 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
          have b28834 := hb (x 7 3)
          have b28835 := hb (x 8 2)
          have b28836 := hb (x 9 13)
          have b28837 := hb (x 10 12)
          clear * - r28831 e28832 e28833 b28834 b28835 b28836 b28837 d28674 d28690 d28670
          omega
        have d28838 : (x 10 13).toNat = 1 := by
          have r28839 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := hcov13 10
          have b28840 := hb (x 8 2)
          have b28841 := hb (x 10 13)
          have b28842 := hb (x 9 1 && x 9 14)
          clear * - r28839 b28840 b28841 b28842 d28822 d28830
          omega
        have d28843 : (x 10 1).toNat = 1 := by
          have r28844 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
          have b28845 := hb (x 10 1)
          have b28846 := hb (x 10 13)
          clear * - r28844 b28845 b28846 d28838
          omega
        have d28847 : (x 11 14).toNat = 0 := by
          have r28848 : (x 11 14).toNat + (x 10 1).toNat = 1 := hd14 11
          have b28849 := hb (x 10 1)
          have b28850 := hb (x 11 14)
          clear * - r28848 b28849 b28850 d28843
          omega
        have d28851 : (x 11 1 && x 11 14).toNat = 0 := by
          have r28852 := hand2 (x 11 1) (x 11 14)
          have b28853 := hb (x 11 14)
          have b28854 := hb (x 11 1 && x 11 14)
          clear * - r28852 b28853 b28854 d28847
          omega
        have d28855 : (x 10 2).toNat = 1 := by
          have r28856 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := hcov13 12
          have b28857 := hb (x 10 2)
          have b28858 := hb (x 12 13)
          have b28859 := hb (x 11 1 && x 11 14)
          clear * - r28856 b28857 b28858 b28859 d28794 d28851
          omega
        have d28860 : (x 12 12).toNat = 0 := by
          have r28861 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
          have e28862 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
          have e28863 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
          have b28864 := hb (x 9 3)
          have b28865 := hb (x 10 2)
          have b28866 := hb (x 11 13)
          have b28867 := hb (x 12 12)
          clear * - r28861 e28862 e28863 b28864 b28865 b28866 b28867 d28855
          omega
        have d28868 : (x 12 4).toNat = 0 := by
          have r28869 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
          have b28870 := hb (x 12 4)
          have b28871 := hb (x 12 12)
          clear * - r28869 b28870 b28871 d28860
          omega
        have d28872 : (x 12 4 && x 12 14).toNat = 0 := by
          have r28873 := hand1 (x 12 4) (x 12 14)
          have b28874 := hb (x 12 4)
          have b28875 := hb (x 12 4 && x 12 14)
          clear * - r28873 b28874 b28875 d28868
          omega
        have d28876 : (x 11 13).toNat = 0 := by
          have r28877 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
          have e28878 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
          have e28879 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
          have b28880 := hb (x 9 3)
          have b28881 := hb (x 10 2)
          have b28882 := hb (x 11 13)
          have b28883 := hb (x 12 12)
          clear * - r28877 e28878 e28879 b28880 b28881 b28882 b28883 d28860 d28855
          omega
        have d28884 : (x 11 5).toNat = 0 := by
          have r28885 : (x 11 5).toNat ≤ (x 11 13).toNat := himp _ _ (hp5 11)
          have b28886 := hb (x 11 5)
          have b28887 := hb (x 11 13)
          clear * - r28885 b28886 b28887 d28876
          omega
        have d28888 : (x 11 3 && x 11 14).toNat = 0 := by
          have r28889 := hand2 (x 11 3) (x 11 14)
          have b28890 := hb (x 11 14)
          have b28891 := hb (x 11 3 && x 11 14)
          clear * - r28889 b28890 b28891 d28847
          omega
        have d28892 : (x 14 11).toNat = 1 := by
          have r28893 : 1 ≤ (x 14 11).toNat + (x 13 1 && x 13 12).toNat + (x 12 2 && x 12 13).toNat + (x 11 3 && x 11 14).toNat + (x 10 4).toNat := hcov11 14
          have b28894 := hb (x 10 4)
          have b28895 := hb (x 14 11)
          have b28896 := hb (x 13 1 && x 13 12)
          have b28897 := hb (x 12 2 && x 12 13)
          have b28898 := hb (x 11 3 && x 11 14)
          clear * - r28893 b28894 b28895 b28896 b28897 b28898 d28790 d28802 d28888 d28686
          omega
        have d28899 : (x 14 3).toNat = 1 := by
          have r28900 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
          have b28901 := hb (x 14 3)
          have b28902 := hb (x 14 11)
          clear * - r28900 b28901 b28902 d28892
          omega
        have d28903 : (x 17 12).toNat = 0 := by
          have r28904 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
          have e28905 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
          have e28906 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
          have b28907 := hb (x 14 3)
          have b28908 := hb (x 15 2)
          have b28909 := hb (x 16 13)
          have b28910 := hb (x 17 12)
          clear * - r28904 e28905 e28906 b28907 b28908 b28909 b28910 d28899
          omega
        have d28911 : (x 16 13).toNat = 0 := by
          have r28912 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
          have e28913 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
          have e28914 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
          have b28915 := hb (x 14 3)
          have b28916 := hb (x 15 2)
          have b28917 := hb (x 16 13)
          have b28918 := hb (x 17 12)
          clear * - r28912 e28913 e28914 b28915 b28916 b28917 b28918 d28903 d28899
          omega
        have d28919 : (x 15 2).toNat = 0 := by
          have r28920 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
          have e28921 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
          have e28922 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
          have b28923 := hb (x 14 3)
          have b28924 := hb (x 15 2)
          have b28925 := hb (x 16 13)
          have b28926 := hb (x 17 12)
          clear * - r28920 e28921 e28922 b28923 b28924 b28925 b28926 d28903 d28911 d28899
          omega
        have d28927 : (x 11 12).toNat = 0 := by
          have r28928 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
          have e28929 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e28930 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have b28931 := hb (x 8 3)
          have b28932 := hb (x 9 2)
          have b28933 := hb (x 10 13)
          have b28934 := hb (x 11 12)
          clear * - r28928 e28929 e28930 b28931 b28932 b28933 b28934 d28838 d28826
          omega
        have d28935 : (x 11 4).toNat = 0 := by
          have r28936 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
          have b28937 := hb (x 11 4)
          have b28938 := hb (x 11 12)
          clear * - r28936 b28937 b28938 d28927
          omega
        have d28939 : (x 8 3).toNat = 0 := by
          have r28940 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
          have e28941 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e28942 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have b28943 := hb (x 8 3)
          have b28944 := hb (x 9 2)
          have b28945 := hb (x 10 13)
          have b28946 := hb (x 11 12)
          clear * - r28940 e28941 e28942 b28943 b28944 b28945 b28946 d28927 d28838 d28826
          omega
        have d28947 : (x 8 3 && x 8 14).toNat = 0 := by
          have r28948 := hand1 (x 8 3) (x 8 14)
          have b28949 := hb (x 8 3)
          have b28950 := hb (x 8 3 && x 8 14)
          clear * - r28948 b28949 b28950 d28939
          omega
        have d28951 : (x 11 11).toNat = 1 := by
          have r28952 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := hcov11 11
          have b28953 := hb (x 7 4)
          have b28954 := hb (x 11 11)
          have b28955 := hb (x 10 1 && x 10 12)
          have b28956 := hb (x 9 2 && x 9 13)
          have b28957 := hb (x 8 3 && x 8 14)
          clear * - r28952 b28953 b28954 b28955 b28956 b28957 d28682 d28698 d28947 d28647
          omega
        have d28958 : (x 11 3).toNat = 1 := by
          have r28959 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
          have b28960 := hb (x 11 3)
          have b28961 := hb (x 11 11)
          clear * - r28959 b28960 b28961 d28951
          omega
        have d28962 : (x 14 12).toNat = 0 := by
          have r28963 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
          have e28964 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
          have e28965 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
          have b28966 := hb (x 11 3)
          have b28967 := hb (x 12 2)
          have b28968 := hb (x 13 13)
          have b28969 := hb (x 14 12)
          clear * - r28963 e28964 e28965 b28966 b28967 b28968 b28969 d28958
          omega
        have d28970 : (x 14 1 && x 14 12).toNat = 0 := by
          have r28971 := hand2 (x 14 1) (x 14 12)
          have b28972 := hb (x 14 12)
          have b28973 := hb (x 14 1 && x 14 12)
          clear * - r28971 b28972 b28973 d28962
          omega
        have d28974 : (x 14 2 && x 14 12).toNat = 0 := by
          have r28975 := hand2 (x 14 2) (x 14 12)
          have b28976 := hb (x 14 12)
          have b28977 := hb (x 14 2 && x 14 12)
          clear * - r28975 b28976 b28977 d28962
          omega
        have d28978 : (x 13 13).toNat = 0 := by
          have r28979 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
          have e28980 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
          have e28981 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
          have b28982 := hb (x 11 3)
          have b28983 := hb (x 12 2)
          have b28984 := hb (x 13 13)
          have b28985 := hb (x 14 12)
          clear * - r28979 e28980 e28981 b28982 b28983 b28984 b28985 d28962 d28958
          omega
        have d28986 : (x 13 2 && x 13 13).toNat = 0 := by
          have r28987 := hand2 (x 13 2) (x 13 13)
          have b28988 := hb (x 13 13)
          have b28989 := hb (x 13 2 && x 13 13)
          clear * - r28987 b28988 b28989 d28978
          omega
        have d28990 : (x 13 3 && x 13 13).toNat = 0 := by
          have r28991 := hand2 (x 13 3) (x 13 13)
          have b28992 := hb (x 13 13)
          have b28993 := hb (x 13 3 && x 13 13)
          clear * - r28991 b28992 b28993 d28978
          omega
        have d28994 : (x 12 1 && x 12 14).toNat = 1 := by
          have r28995 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := hcov13 13
          have b28996 := hb (x 11 2)
          have b28997 := hb (x 13 13)
          have b28998 := hb (x 12 1 && x 12 14)
          clear * - r28995 b28996 b28997 b28998 d28978 d28806
          omega
        have d28999 : (x 12 1).toNat = 1 := by
          have r29000 := hand1 (x 12 1) (x 12 14)
          have b29001 := hb (x 12 1)
          have b29002 := hb (x 12 1 && x 12 14)
          clear * - r29000 b29001 b29002 d28994
          omega
        have d29003 : (x 13 14).toNat = 0 := by
          have r29004 : (x 13 14).toNat + (x 12 1).toNat = 1 := hd14 13
          have b29005 := hb (x 12 1)
          have b29006 := hb (x 13 14)
          clear * - r29004 b29005 b29006 d28999
          omega
        have d29007 : (x 13 1 && x 13 14).toNat = 0 := by
          have r29008 := hand2 (x 13 1) (x 13 14)
          have b29009 := hb (x 13 14)
          have b29010 := hb (x 13 1 && x 13 14)
          clear * - r29008 b29009 b29010 d29003
          omega
        have d29011 : (x 13 2).toNat = 0 := by
          have r29012 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
          have b29013 := hb (x 13 2)
          have b29014 := hb (x 13 14)
          clear * - r29012 b29013 b29014 d29003
          omega
        have d29015 : (x 12 2).toNat = 0 := by
          have r29016 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
          have e29017 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
          have e29018 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
          have b29019 := hb (x 11 3)
          have b29020 := hb (x 12 2)
          have b29021 := hb (x 13 13)
          have b29022 := hb (x 14 12)
          clear * - r29016 e29017 e29018 b29019 b29020 b29021 b29022 d28962 d28978 d28958
          omega
        have d29023 : (x 14 13).toNat = 1 := by
          have r29024 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
          have b29025 := hb (x 12 2)
          have b29026 := hb (x 14 13)
          have b29027 := hb (x 13 1 && x 13 14)
          clear * - r29024 b29025 b29026 b29027 d29007 d29015
          omega
        have d29028 : (x 15 12).toNat = 0 := by
          have r29029 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
          have e29030 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
          have e29031 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
          have b29032 := hb (x 12 3)
          have b29033 := hb (x 13 2)
          have b29034 := hb (x 14 13)
          have b29035 := hb (x 15 12)
          clear * - r29029 e29030 e29031 b29032 b29033 b29034 b29035 d29023 d29011
          omega
        have d29036 : (x 12 3).toNat = 0 := by
          have r29037 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
          have e29038 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
          have e29039 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
          have b29040 := hb (x 12 3)
          have b29041 := hb (x 13 2)
          have b29042 := hb (x 14 13)
          have b29043 := hb (x 15 12)
          clear * - r29037 e29038 e29039 b29040 b29041 b29042 b29043 d29028 d29023 d29011
          omega
        have d29044 : (x 12 3 && x 12 14).toNat = 0 := by
          have r29045 := hand1 (x 12 3) (x 12 14)
          have b29046 := hb (x 12 3)
          have b29047 := hb (x 12 3 && x 12 14)
          clear * - r29045 b29046 b29047 d29036
          omega
        have d29048 : (x 15 11).toNat = 1 := by
          have r29049 : 1 ≤ (x 15 11).toNat + (x 14 1 && x 14 12).toNat + (x 13 2 && x 13 13).toNat + (x 12 3 && x 12 14).toNat + (x 11 4).toNat := hcov11 15
          have b29050 := hb (x 11 4)
          have b29051 := hb (x 15 11)
          have b29052 := hb (x 14 1 && x 14 12)
          have b29053 := hb (x 13 2 && x 13 13)
          have b29054 := hb (x 12 3 && x 12 14)
          clear * - r29049 b29050 b29051 b29052 b29053 b29054 d28970 d28986 d29044 d28935
          omega
        have d29055 : (x 15 3).toNat = 1 := by
          have r29056 : (x 15 11).toNat ≤ (x 15 3).toNat := himp _ _ (hp11 15)
          have b29057 := hb (x 15 3)
          have b29058 := hb (x 15 11)
          clear * - r29056 b29057 b29058 d29048
          omega
        have d29059 : (x 18 12).toNat = 0 := by
          have r29060 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
          have e29061 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
          have e29062 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
          have b29063 := hb (x 15 3)
          have b29064 := hb (x 16 2)
          have b29065 := hb (x 17 13)
          have b29066 := hb (x 18 12)
          clear * - r29060 e29061 e29062 b29063 b29064 b29065 b29066 d29055
          omega
        have d29067 : (x 17 13).toNat = 0 := by
          have r29068 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
          have e29069 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
          have e29070 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
          have b29071 := hb (x 15 3)
          have b29072 := hb (x 16 2)
          have b29073 := hb (x 17 13)
          have b29074 := hb (x 18 12)
          clear * - r29068 e29069 e29070 b29071 b29072 b29073 b29074 d29059 d29055
          omega
        have d29075 : (x 16 1 && x 16 14).toNat = 1 := by
          have r29076 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := hcov13 17
          have b29077 := hb (x 15 2)
          have b29078 := hb (x 17 13)
          have b29079 := hb (x 16 1 && x 16 14)
          clear * - r29076 b29077 b29078 b29079 d29067 d28919
          omega
        have d29080 : (x 16 14).toNat = 1 := by
          have r29081 := hand2 (x 16 1) (x 16 14)
          have b29082 := hb (x 16 14)
          have b29083 := hb (x 16 1 && x 16 14)
          clear * - r29081 b29082 b29083 d29075
          omega
        have d29084 : (x 15 1).toNat = 0 := by
          have r29085 : (x 16 14).toNat + (x 15 1).toNat = 1 := hd14 16
          have b29086 := hb (x 15 1)
          have b29087 := hb (x 16 14)
          clear * - r29085 b29086 b29087 d29080
          omega
        have d29088 : (x 15 1 && x 15 11).toNat = 0 := by
          have r29089 := hand1 (x 15 1) (x 15 11)
          have b29090 := hb (x 15 1)
          have b29091 := hb (x 15 1 && x 15 11)
          clear * - r29089 b29090 b29091 d29084
          omega
        have d29092 : (x 16 2).toNat = 0 := by
          have r29093 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
          have e29094 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
          have e29095 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
          have b29096 := hb (x 15 3)
          have b29097 := hb (x 16 2)
          have b29098 := hb (x 17 13)
          have b29099 := hb (x 18 12)
          clear * - r29093 e29094 e29095 b29096 b29097 b29098 b29099 d29059 d29067 d29055
          omega
        have d29100 : (x 16 10).toNat = 0 := by
          have r29101 : (x 16 10).toNat ≤ (x 16 2).toNat := himp _ _ (hp10 16)
          have b29102 := hb (x 16 2)
          have b29103 := hb (x 16 10)
          clear * - r29101 b29102 b29103 d29092
          omega
        have r29104 : 1 ≤ (x 16 10).toNat + (x 15 1 && x 15 11).toNat + (x 14 2 && x 14 12).toNat + (x 13 3 && x 13 13).toNat + (x 12 4 && x 12 14).toNat + (x 11 5).toNat := hcov10 16
        have b29105 := hb (x 11 5)
        have b29106 := hb (x 16 10)
        have b29107 := hb (x 15 1 && x 15 11)
        have b29108 := hb (x 14 2 && x 14 12)
        have b29109 := hb (x 13 3 && x 13 13)
        have b29110 := hb (x 12 4 && x 12 14)
        linarith only [r29104, b29105, b29106, b29107, b29108, b29109, b29110, d29100, d29088, d28974, d28990, d28872, d28884]
      · have f29111 : (x (-1) 4).toNat = 1 := by rw [h28544]; rfl
        have d29112 : (x 3 8).toNat = 0 := by
          have r29113 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := hd8 3
          have e29114 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e29115 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e29116 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e29117 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e29118 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e29119 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b29120 := hb (x (-4) 7)
          have b29121 := hb (x (-3) 6)
          have b29122 := hb (x (-2) 5)
          have b29123 := hb (x (-1) 4)
          have b29124 := hb (x 0 11)
          have b29125 := hb (x 1 10)
          have b29126 := hb (x 2 9)
          have b29127 := hb (x 3 8)
          clear * - r29113 e29114 e29115 e29116 e29117 e29118 e29119 b29120 b29121 b29122 b29123 b29124 b29125 b29126 b29127 g11 g7 f29111 g0
          omega
        have d29128 : (x 2 9).toNat = 0 := by
          have r29129 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := hd8 3
          have e29130 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e29131 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e29132 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e29133 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e29134 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e29135 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b29136 := hb (x (-4) 7)
          have b29137 := hb (x (-3) 6)
          have b29138 := hb (x (-2) 5)
          have b29139 := hb (x (-1) 4)
          have b29140 := hb (x 0 11)
          have b29141 := hb (x 1 10)
          have b29142 := hb (x 2 9)
          have b29143 := hb (x 3 8)
          clear * - r29129 e29130 e29131 e29132 e29133 e29134 e29135 b29136 b29137 b29138 b29139 b29140 b29141 b29142 b29143 d29112 g11 g7 f29111 g0
          omega
        have d29144 : (x (-3) 6).toNat = 0 := by
          have r29145 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := hd8 3
          have e29146 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e29147 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e29148 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e29149 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e29150 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e29151 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b29152 := hb (x (-4) 7)
          have b29153 := hb (x (-3) 6)
          have b29154 := hb (x (-2) 5)
          have b29155 := hb (x (-1) 4)
          have b29156 := hb (x 0 11)
          have b29157 := hb (x 1 10)
          have b29158 := hb (x 2 9)
          have b29159 := hb (x 3 8)
          clear * - r29145 e29146 e29147 e29148 e29149 e29150 e29151 b29152 b29153 b29154 b29155 b29156 b29157 b29158 b29159 d29112 d29128 g11 g7 f29111 g0
          omega
        have d29160 : (x (-4) 7).toNat = 0 := by
          have r29161 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := hd8 3
          have e29162 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e29163 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e29164 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e29165 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e29166 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e29167 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b29168 := hb (x (-4) 7)
          have b29169 := hb (x (-3) 6)
          have b29170 := hb (x (-2) 5)
          have b29171 := hb (x (-1) 4)
          have b29172 := hb (x 0 11)
          have b29173 := hb (x 1 10)
          have b29174 := hb (x 2 9)
          have b29175 := hb (x 3 8)
          clear * - r29161 e29162 e29163 e29164 e29165 e29166 e29167 b29168 b29169 b29170 b29171 b29172 b29173 b29174 b29175 d29112 d29128 g11 g7 f29111 g0 d29144
          omega
        have r29176 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := hcount 3
        have r29177 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := hd8 (-7)
        have e29178 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
        have e29179 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
        have e29180 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
        have e29181 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
        have e29182 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
        have e29183 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
        have r29184 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
        have e29185 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e29186 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e29187 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e29188 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e29189 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e29190 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have r29191 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := hd12 (-5)
        have e29192 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
        have e29193 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
        have r29194 : 1 ≤ (x 3 4).toNat + (x 2 1 && x 2 5).toNat + (x 1 2 && x 1 6).toNat + (x 0 3 && x 0 7).toNat + (x (-1) 4 && x (-1) 8).toNat + (x (-2) 5 && x (-2) 9).toNat + (x (-3) 6 && x (-3) 10).toNat + (x (-4) 7 && x (-4) 11).toNat + (x (-5) 8 && x (-5) 12).toNat + (x (-6) 9 && x (-6) 13).toNat + (x (-7) 10 && x (-7) 14).toNat + (x (-8) 11).toNat := hcov4 3
        have e29195 : (x 2 1 && x 2 5).toNat = (x 2 5).toNat := handr _ _ (fun h => hp13 2 (hp5 2 (h)))
        have e29196 : (x (-7) 10 && x (-7) 14).toNat = (x (-7) 10).toNat := handl _ _ (fun h => hp2 (-7) (hp10 (-7) (h)))
        have r29197 : 1 ≤ (x 1 6).toNat + (x 0 1 && x 0 7).toNat + (x (-1) 2 && x (-1) 8).toNat + (x (-2) 3 && x (-2) 9).toNat + (x (-3) 4 && x (-3) 10).toNat + (x (-4) 5 && x (-4) 11).toNat + (x (-5) 6 && x (-5) 12).toNat + (x (-6) 7 && x (-6) 13).toNat + (x (-7) 8 && x (-7) 14).toNat + (x (-8) 9).toNat := hcov6 1
        have r29198 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := hcov9 6
        have r29199 : 1 ≤ (x (-7) 10).toNat + (x (-8) 1 && x (-8) 11).toNat + (x (-9) 2 && x (-9) 12).toNat + (x (-10) 3 && x (-10) 13).toNat + (x (-11) 4 && x (-11) 14).toNat + (x (-12) 5).toNat := hcov10 (-7)
        have r29200 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := hcov10 (-1)
        have r29201 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
        have r29202 : (x (-7) 10).toNat ≤ (x (-7) 2).toNat := himp _ _ (hp10 (-7))
        have r29203 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
        have r29204 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
        have r29205 := hand1 (x (-5) 8) (x (-5) 12)
        have r29206 := hand1 (x (-6) 9) (x (-6) 13)
        have r29207 := hand1 (x (-7) 8) (x (-7) 14)
        have r29208 := hand2 (x 5 1) (x 5 10)
        have r29209 := hand2 (x 4 2) (x 4 11)
        have r29210 := hand2 (x (-8) 1) (x (-8) 11)
        have r29211 := hand2 (x (-9) 2) (x (-9) 12)
        have r29212 := hand2 (x (-10) 3) (x (-10) 13)
        have r29213 := hand2 (x (-11) 4) (x (-11) 14)
        have r29214 := hand1 (x (-5) 4) (x (-5) 14)
        have b29215 := hb (x (-14) 7)
        have b29216 := hb (x (-13) 6)
        have b29217 := hb (x (-12) 5)
        have b29218 := hb (x (-11) 4)
        have b29219 := hb (x (-11) 14)
        have b29220 := hb (x (-10) 11)
        have b29221 := hb (x (-10) 13)
        have b29222 := hb (x (-9) 10)
        have b29223 := hb (x (-9) 12)
        have b29224 := hb (x (-8) 3)
        have b29225 := hb (x (-8) 9)
        have b29226 := hb (x (-8) 11)
        have b29227 := hb (x (-7) 2)
        have b29228 := hb (x (-7) 8)
        have b29229 := hb (x (-7) 10)
        have b29230 := hb (x (-6) 5)
        have b29231 := hb (x (-6) 9)
        have b29232 := hb (x (-6) 13)
        have b29233 := hb (x (-5) 4)
        have b29234 := hb (x (-5) 8)
        have b29235 := hb (x (-5) 12)
        have b29236 := hb (x (-4) 7)
        have b29237 := hb (x (-3) 6)
        have b29238 := hb (x (-2) 5)
        have b29239 := hb (x (-1) 4)
        have b29240 := hb (x (-1) 10)
        have b29241 := hb (x 0 3)
        have b29242 := hb (x 0 6)
        have b29243 := hb (x 0 7)
        have b29244 := hb (x 1 2)
        have b29245 := hb (x 1 6)
        have b29246 := hb (x 2 1)
        have b29247 := hb (x 2 5)
        have b29248 := hb (x 3 4)
        have b29249 := hb (x 4 11)
        have b29250 := hb (x 5 10)
        have b29251 := hb (x 6 9)
        have b29252 := hb (x 7 8)
        have b29253 := hb (x 1 2 && x 1 6)
        have b29254 := hb (x 0 3 && x 0 7)
        have b29255 := hb (x (-1) 4 && x (-1) 8)
        have b29256 := hb (x (-2) 5 && x (-2) 9)
        have b29257 := hb (x (-3) 6 && x (-3) 10)
        have b29258 := hb (x (-4) 7 && x (-4) 11)
        have b29259 := hb (x (-5) 8 && x (-5) 12)
        have b29260 := hb (x (-6) 9 && x (-6) 13)
        have b29261 := hb (x 0 1 && x 0 7)
        have b29262 := hb (x (-1) 2 && x (-1) 8)
        have b29263 := hb (x (-2) 3 && x (-2) 9)
        have b29264 := hb (x (-3) 4 && x (-3) 10)
        have b29265 := hb (x (-4) 5 && x (-4) 11)
        have b29266 := hb (x (-5) 6 && x (-5) 12)
        have b29267 := hb (x (-6) 7 && x (-6) 13)
        have b29268 := hb (x (-7) 8 && x (-7) 14)
        have b29269 := hb (x 5 1 && x 5 10)
        have b29270 := hb (x 4 2 && x 4 11)
        have b29271 := hb (x 3 3 && x 3 12)
        have b29272 := hb (x 2 4 && x 2 13)
        have b29273 := hb (x 1 5 && x 1 14)
        have b29274 := hb (x (-8) 1 && x (-8) 11)
        have b29275 := hb (x (-9) 2 && x (-9) 12)
        have b29276 := hb (x (-10) 3 && x (-10) 13)
        have b29277 := hb (x (-11) 4 && x (-11) 14)
        have b29278 := hb (x (-2) 1 && x (-2) 11)
        have b29279 := hb (x (-3) 2 && x (-3) 12)
        have b29280 := hb (x (-4) 3 && x (-4) 13)
        have b29281 := hb (x (-5) 4 && x (-5) 14)
        linarith only [r29176, r29177, e29178, e29179, e29180, e29181, e29182, e29183, r29184, e29185, e29186, e29187, e29188, e29189, e29190, r29191, e29192, e29193, r29194, e29195, e29196, r29197, r29198, r29199, r29200, r29201, r29202, r29203, r29204, r29205, r29206, r29207, r29208, r29209, r29210, r29211, r29212, r29213, r29214, b29215, b29216, b29217, b29218, b29219, b29220, b29221, b29222, b29223, b29224, b29225, b29226, b29227, b29228, b29229, b29230, b29231, b29232, b29233, b29234, b29235, b29236, b29237, b29238, b29239, b29240, b29241, b29242, b29243, b29244, b29245, b29246, b29247, b29248, b29249, b29250, b29251, b29252, b29253, b29254, b29255, b29256, b29257, b29258, b29259, b29260, b29261, b29262, b29263, b29264, b29265, b29266, b29267, b29268, b29269, b29270, b29271, b29272, b29273, b29274, b29275, b29276, b29277, b29278, b29279, b29280, b29281, d29160, d29144, g0, f29111, d28388, g3, g4, g5, g8, g10, g12, g15, g16, g17, g18, g19, d28476, d28496, g20, g21, g22, d28424, d28444, d28516, d28536, g23, g24, g25, g26, d28468, d28488]
    · have f29282 : (x 1 3).toNat = 1 := by rw [h28542]; rfl
      have d29283 : (x 4 12).toNat = 0 := by
        have r29284 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
        have e29285 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e29286 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b29287 := hb (x 1 3)
        have b29288 := hb (x 2 2)
        have b29289 := hb (x 3 13)
        have b29290 := hb (x 4 12)
        clear * - r29284 e29285 e29286 b29287 b29288 b29289 b29290 f29282
        omega
      have d29291 : (x 4 1 && x 4 12).toNat = 0 := by
        have r29292 := hand2 (x 4 1) (x 4 12)
        have b29293 := hb (x 4 12)
        have b29294 := hb (x 4 1 && x 4 12)
        clear * - r29292 b29293 b29294 d29283
        omega
      have d29295 : (x 4 4).toNat = 0 := by
        have r29296 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
        have b29297 := hb (x 4 4)
        have b29298 := hb (x 4 12)
        clear * - r29296 b29297 b29298 d29283
        omega
      have d29299 : (x 3 13).toNat = 0 := by
        have r29300 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
        have e29301 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e29302 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b29303 := hb (x 1 3)
        have b29304 := hb (x 2 2)
        have b29305 := hb (x 3 13)
        have b29306 := hb (x 4 12)
        clear * - r29300 e29301 e29302 b29303 b29304 b29305 b29306 d29283 f29282
        omega
      have d29307 : (x 2 2).toNat = 0 := by
        have r29308 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
        have e29309 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e29310 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b29311 := hb (x 1 3)
        have b29312 := hb (x 2 2)
        have b29313 := hb (x 3 13)
        have b29314 := hb (x 4 12)
        clear * - r29308 e29309 e29310 b29311 b29312 b29313 b29314 d29283 d29299 f29282
        omega
      have d29315 : (x 4 13).toNat = 1 := by
        have r29316 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
        have b29317 := hb (x 2 2)
        have b29318 := hb (x 4 13)
        have b29319 := hb (x 3 1 && x 3 14)
        clear * - r29316 b29317 b29318 b29319 g34 d29307
        omega
      have d29320 : (x 4 1).toNat = 1 := by
        have r29321 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
        have b29322 := hb (x 4 1)
        have b29323 := hb (x 4 13)
        clear * - r29321 b29322 b29323 d29315
        omega
      have d29324 : (x 5 14).toNat = 0 := by
        have r29325 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
        have b29326 := hb (x 4 1)
        have b29327 := hb (x 5 14)
        clear * - r29325 b29326 b29327 d29320
        omega
      have d29328 : (x 5 3 && x 5 14).toNat = 0 := by
        have r29329 := hand2 (x 5 3) (x 5 14)
        have b29330 := hb (x 5 14)
        have b29331 := hb (x 5 3 && x 5 14)
        clear * - r29329 b29330 b29331 d29324
        omega
      have d29332 : (x 5 2).toNat = 0 := by
        have r29333 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
        have b29334 := hb (x 5 2)
        have b29335 := hb (x 5 14)
        clear * - r29333 b29334 b29335 d29324
        omega
      have d29336 : (x 5 12).toNat = 0 := by
        have r29337 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
        have e29338 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e29339 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b29340 := hb (x 2 3)
        have b29341 := hb (x 3 2)
        have b29342 := hb (x 4 13)
        have b29343 := hb (x 5 12)
        clear * - r29337 e29338 e29339 b29340 b29341 b29342 b29343 d29315 g14
        omega
      have d29344 : (x 5 4).toNat = 0 := by
        have r29345 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
        have b29346 := hb (x 5 4)
        have b29347 := hb (x 5 12)
        clear * - r29345 b29346 b29347 d29336
        omega
      have d29348 : (x 2 3).toNat = 0 := by
        have r29349 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
        have e29350 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e29351 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b29352 := hb (x 2 3)
        have b29353 := hb (x 3 2)
        have b29354 := hb (x 4 13)
        have b29355 := hb (x 5 12)
        clear * - r29349 e29350 e29351 b29352 b29353 b29354 b29355 d29336 d29315 g14
        omega
      have d29356 : (x 2 3 && x 2 14).toNat = 0 := by
        have r29357 := hand1 (x 2 3) (x 2 14)
        have b29358 := hb (x 2 3)
        have b29359 := hb (x 2 3 && x 2 14)
        clear * - r29357 b29358 b29359 d29348
        omega
      have d29360 : (x 5 11).toNat = 1 := by
        have r29361 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := hcov11 5
        have b29362 := hb (x 1 4)
        have b29363 := hb (x 5 11)
        have b29364 := hb (x 4 1 && x 4 12)
        have b29365 := hb (x 3 2 && x 3 13)
        have b29366 := hb (x 2 3 && x 2 14)
        clear * - r29361 b29362 b29363 b29364 b29365 b29366 d29291 g32 d29356 g9
        omega
      have d29367 : (x 5 3).toNat = 1 := by
        have r29368 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
        have b29369 := hb (x 5 3)
        have b29370 := hb (x 5 11)
        clear * - r29368 b29369 b29370 d29360
        omega
      have d29371 : (x 8 12).toNat = 0 := by
        have r29372 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
        have e29373 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e29374 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have b29375 := hb (x 5 3)
        have b29376 := hb (x 6 2)
        have b29377 := hb (x 7 13)
        have b29378 := hb (x 8 12)
        clear * - r29372 e29373 e29374 b29375 b29376 b29377 b29378 d29367
        omega
      have d29379 : (x 8 1 && x 8 12).toNat = 0 := by
        have r29380 := hand2 (x 8 1) (x 8 12)
        have b29381 := hb (x 8 12)
        have b29382 := hb (x 8 1 && x 8 12)
        clear * - r29380 b29381 b29382 d29371
        omega
      have d29383 : (x 8 4).toNat = 0 := by
        have r29384 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
        have b29385 := hb (x 8 4)
        have b29386 := hb (x 8 12)
        clear * - r29384 b29385 b29386 d29371
        omega
      have d29387 : (x 7 13).toNat = 0 := by
        have r29388 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
        have e29389 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e29390 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have b29391 := hb (x 5 3)
        have b29392 := hb (x 6 2)
        have b29393 := hb (x 7 13)
        have b29394 := hb (x 8 12)
        clear * - r29388 e29389 e29390 b29391 b29392 b29393 b29394 d29371 d29367
        omega
      have d29395 : (x 7 2 && x 7 13).toNat = 0 := by
        have r29396 := hand2 (x 7 2) (x 7 13)
        have b29397 := hb (x 7 13)
        have b29398 := hb (x 7 2 && x 7 13)
        clear * - r29396 b29397 b29398 d29387
        omega
      have d29399 : (x 6 1 && x 6 14).toNat = 1 := by
        have r29400 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
        have b29401 := hb (x 5 2)
        have b29402 := hb (x 7 13)
        have b29403 := hb (x 6 1 && x 6 14)
        clear * - r29400 b29401 b29402 b29403 d29387 d29332
        omega
      have d29404 : (x 6 1).toNat = 1 := by
        have r29405 := hand1 (x 6 1) (x 6 14)
        have b29406 := hb (x 6 1)
        have b29407 := hb (x 6 1 && x 6 14)
        clear * - r29405 b29406 b29407 d29399
        omega
      have d29408 : (x 7 14).toNat = 0 := by
        have r29409 : (x 7 14).toNat + (x 6 1).toNat = 1 := hd14 7
        have b29410 := hb (x 6 1)
        have b29411 := hb (x 7 14)
        clear * - r29409 b29410 b29411 d29404
        omega
      have d29412 : (x 7 1 && x 7 14).toNat = 0 := by
        have r29413 := hand2 (x 7 1) (x 7 14)
        have b29414 := hb (x 7 14)
        have b29415 := hb (x 7 1 && x 7 14)
        clear * - r29413 b29414 b29415 d29408
        omega
      have d29416 : (x 7 2).toNat = 0 := by
        have r29417 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
        have b29418 := hb (x 7 2)
        have b29419 := hb (x 7 14)
        clear * - r29417 b29418 b29419 d29408
        omega
      have d29420 : (x 6 2).toNat = 0 := by
        have r29421 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
        have e29422 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e29423 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have b29424 := hb (x 5 3)
        have b29425 := hb (x 6 2)
        have b29426 := hb (x 7 13)
        have b29427 := hb (x 8 12)
        clear * - r29421 e29422 e29423 b29424 b29425 b29426 b29427 d29371 d29387 d29367
        omega
      have d29428 : (x 6 2 && x 6 13).toNat = 0 := by
        have r29429 := hand1 (x 6 2) (x 6 13)
        have b29430 := hb (x 6 2)
        have b29431 := hb (x 6 2 && x 6 13)
        clear * - r29429 b29430 b29431 d29420
        omega
      have d29432 : (x 8 13).toNat = 1 := by
        have r29433 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := hcov13 8
        have b29434 := hb (x 6 2)
        have b29435 := hb (x 8 13)
        have b29436 := hb (x 7 1 && x 7 14)
        clear * - r29433 b29434 b29435 b29436 d29412 d29420
        omega
      have d29437 : (x 8 1).toNat = 1 := by
        have r29438 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
        have b29439 := hb (x 8 1)
        have b29440 := hb (x 8 13)
        clear * - r29438 b29439 b29440 d29432
        omega
      have d29441 : (x 9 14).toNat = 0 := by
        have r29442 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
        have b29443 := hb (x 8 1)
        have b29444 := hb (x 9 14)
        clear * - r29442 b29443 b29444 d29437
        omega
      have d29445 : (x 9 3 && x 9 14).toNat = 0 := by
        have r29446 := hand2 (x 9 3) (x 9 14)
        have b29447 := hb (x 9 14)
        have b29448 := hb (x 9 3 && x 9 14)
        clear * - r29446 b29447 b29448 d29441
        omega
      have d29449 : (x 9 2).toNat = 0 := by
        have r29450 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
        have b29451 := hb (x 9 2)
        have b29452 := hb (x 9 14)
        clear * - r29450 b29451 b29452 d29441
        omega
      have d29453 : (x 9 12).toNat = 0 := by
        have r29454 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
        have e29455 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
        have e29456 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
        have b29457 := hb (x 6 3)
        have b29458 := hb (x 7 2)
        have b29459 := hb (x 8 13)
        have b29460 := hb (x 9 12)
        clear * - r29454 e29455 e29456 b29457 b29458 b29459 b29460 d29432 d29416
        omega
      have d29461 : (x 9 4).toNat = 0 := by
        have r29462 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
        have b29463 := hb (x 9 4)
        have b29464 := hb (x 9 12)
        clear * - r29462 b29463 b29464 d29453
        omega
      have d29465 : (x 6 3).toNat = 0 := by
        have r29466 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
        have e29467 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
        have e29468 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
        have b29469 := hb (x 6 3)
        have b29470 := hb (x 7 2)
        have b29471 := hb (x 8 13)
        have b29472 := hb (x 9 12)
        clear * - r29466 e29467 e29468 b29469 b29470 b29471 b29472 d29453 d29432 d29416
        omega
      have d29473 : (x 6 3 && x 6 14).toNat = 0 := by
        have r29474 := hand1 (x 6 3) (x 6 14)
        have b29475 := hb (x 6 3)
        have b29476 := hb (x 6 3 && x 6 14)
        clear * - r29474 b29475 b29476 d29465
        omega
      have d29477 : (x 9 11).toNat = 1 := by
        have r29478 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := hcov11 9
        have b29479 := hb (x 5 4)
        have b29480 := hb (x 9 11)
        have b29481 := hb (x 8 1 && x 8 12)
        have b29482 := hb (x 7 2 && x 7 13)
        have b29483 := hb (x 6 3 && x 6 14)
        clear * - r29478 b29479 b29480 b29481 b29482 b29483 d29379 d29395 d29473 d29344
        omega
      have d29484 : (x 9 3).toNat = 1 := by
        have r29485 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
        have b29486 := hb (x 9 3)
        have b29487 := hb (x 9 11)
        clear * - r29485 b29486 b29487 d29477
        omega
      have d29488 : (x 12 12).toNat = 0 := by
        have r29489 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
        have e29490 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
        have e29491 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
        have b29492 := hb (x 9 3)
        have b29493 := hb (x 10 2)
        have b29494 := hb (x 11 13)
        have b29495 := hb (x 12 12)
        clear * - r29489 e29490 e29491 b29492 b29493 b29494 b29495 d29484
        omega
      have d29496 : (x 12 1 && x 12 12).toNat = 0 := by
        have r29497 := hand2 (x 12 1) (x 12 12)
        have b29498 := hb (x 12 12)
        have b29499 := hb (x 12 1 && x 12 12)
        clear * - r29497 b29498 b29499 d29488
        omega
      have d29500 : (x 12 4).toNat = 0 := by
        have r29501 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
        have b29502 := hb (x 12 4)
        have b29503 := hb (x 12 12)
        clear * - r29501 b29502 b29503 d29488
        omega
      have d29504 : (x 11 13).toNat = 0 := by
        have r29505 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
        have e29506 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
        have e29507 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
        have b29508 := hb (x 9 3)
        have b29509 := hb (x 10 2)
        have b29510 := hb (x 11 13)
        have b29511 := hb (x 12 12)
        clear * - r29505 e29506 e29507 b29508 b29509 b29510 b29511 d29488 d29484
        omega
      have d29512 : (x 11 2 && x 11 13).toNat = 0 := by
        have r29513 := hand2 (x 11 2) (x 11 13)
        have b29514 := hb (x 11 13)
        have b29515 := hb (x 11 2 && x 11 13)
        clear * - r29513 b29514 b29515 d29504
        omega
      have d29516 : (x 10 1 && x 10 14).toNat = 1 := by
        have r29517 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := hcov13 11
        have b29518 := hb (x 9 2)
        have b29519 := hb (x 11 13)
        have b29520 := hb (x 10 1 && x 10 14)
        clear * - r29517 b29518 b29519 b29520 d29504 d29449
        omega
      have d29521 : (x 10 14).toNat = 1 := by
        have r29522 := hand2 (x 10 1) (x 10 14)
        have b29523 := hb (x 10 14)
        have b29524 := hb (x 10 1 && x 10 14)
        clear * - r29522 b29523 b29524 d29516
        omega
      have d29525 : (x 9 1).toNat = 0 := by
        have r29526 : (x 10 14).toNat + (x 9 1).toNat = 1 := hd14 10
        have b29527 := hb (x 9 1)
        have b29528 := hb (x 10 14)
        clear * - r29526 b29527 b29528 d29521
        omega
      have d29529 : (x 9 13).toNat = 0 := by
        have r29530 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
        have b29531 := hb (x 9 1)
        have b29532 := hb (x 9 13)
        clear * - r29530 b29531 b29532 d29525
        omega
      have d29533 : (x 8 1 && x 8 14).toNat = 1 := by
        have r29534 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := hcov13 9
        have b29535 := hb (x 7 2)
        have b29536 := hb (x 9 13)
        have b29537 := hb (x 8 1 && x 8 14)
        clear * - r29534 b29535 b29536 b29537 d29529 d29416
        omega
      have d29538 : (x 8 14).toNat = 1 := by
        have r29539 := hand2 (x 8 1) (x 8 14)
        have b29540 := hb (x 8 14)
        have b29541 := hb (x 8 1 && x 8 14)
        clear * - r29539 b29540 b29541 d29533
        omega
      have d29542 : (x 7 1).toNat = 0 := by
        have r29543 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
        have b29544 := hb (x 7 1)
        have b29545 := hb (x 8 14)
        clear * - r29543 b29544 b29545 d29538
        omega
      have d29546 : (x 7 1 && x 7 12).toNat = 0 := by
        have r29547 := hand1 (x 7 1) (x 7 12)
        have b29548 := hb (x 7 1)
        have b29549 := hb (x 7 1 && x 7 12)
        clear * - r29547 b29548 b29549 d29542
        omega
      have d29550 : (x 8 11).toNat = 1 := by
        have r29551 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := hcov11 8
        have b29552 := hb (x 4 4)
        have b29553 := hb (x 8 11)
        have b29554 := hb (x 7 1 && x 7 12)
        have b29555 := hb (x 6 2 && x 6 13)
        have b29556 := hb (x 5 3 && x 5 14)
        clear * - r29551 b29552 b29553 b29554 b29555 b29556 d29546 d29428 d29328 d29295
        omega
      have d29557 : (x 8 3).toNat = 1 := by
        have r29558 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
        have b29559 := hb (x 8 3)
        have b29560 := hb (x 8 11)
        clear * - r29558 b29559 b29560 d29550
        omega
      have d29561 : (x 11 12).toNat = 0 := by
        have r29562 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
        have e29563 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e29564 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b29565 := hb (x 8 3)
        have b29566 := hb (x 9 2)
        have b29567 := hb (x 10 13)
        have b29568 := hb (x 11 12)
        clear * - r29562 e29563 e29564 b29565 b29566 b29567 b29568 d29449 d29557
        omega
      have d29569 : (x 11 1 && x 11 12).toNat = 0 := by
        have r29570 := hand2 (x 11 1) (x 11 12)
        have b29571 := hb (x 11 12)
        have b29572 := hb (x 11 1 && x 11 12)
        clear * - r29570 b29571 b29572 d29561
        omega
      have d29573 : (x 10 13).toNat = 0 := by
        have r29574 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
        have e29575 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e29576 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b29577 := hb (x 8 3)
        have b29578 := hb (x 9 2)
        have b29579 := hb (x 10 13)
        have b29580 := hb (x 11 12)
        clear * - r29574 e29575 e29576 b29577 b29578 b29579 b29580 d29561 d29449 d29557
        omega
      have d29581 : (x 10 2 && x 10 13).toNat = 0 := by
        have r29582 := hand2 (x 10 2) (x 10 13)
        have b29583 := hb (x 10 13)
        have b29584 := hb (x 10 2 && x 10 13)
        clear * - r29582 b29583 b29584 d29573
        omega
      have d29585 : (x 12 11).toNat = 1 := by
        have r29586 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := hcov11 12
        have b29587 := hb (x 8 4)
        have b29588 := hb (x 12 11)
        have b29589 := hb (x 11 1 && x 11 12)
        have b29590 := hb (x 10 2 && x 10 13)
        have b29591 := hb (x 9 3 && x 9 14)
        clear * - r29586 b29587 b29588 b29589 b29590 b29591 d29569 d29581 d29445 d29383
        omega
      have d29592 : (x 12 3).toNat = 1 := by
        have r29593 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
        have b29594 := hb (x 12 3)
        have b29595 := hb (x 12 11)
        clear * - r29593 b29594 b29595 d29585
        omega
      have d29596 : (x 15 12).toNat = 0 := by
        have r29597 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
        have e29598 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e29599 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b29600 := hb (x 12 3)
        have b29601 := hb (x 13 2)
        have b29602 := hb (x 14 13)
        have b29603 := hb (x 15 12)
        clear * - r29597 e29598 e29599 b29600 b29601 b29602 b29603 d29592
        omega
      have d29604 : (x 15 1 && x 15 12).toNat = 0 := by
        have r29605 := hand2 (x 15 1) (x 15 12)
        have b29606 := hb (x 15 12)
        have b29607 := hb (x 15 1 && x 15 12)
        clear * - r29605 b29606 b29607 d29596
        omega
      have d29608 : (x 14 13).toNat = 0 := by
        have r29609 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
        have e29610 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e29611 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b29612 := hb (x 12 3)
        have b29613 := hb (x 13 2)
        have b29614 := hb (x 14 13)
        have b29615 := hb (x 15 12)
        clear * - r29609 e29610 e29611 b29612 b29613 b29614 b29615 d29596 d29592
        omega
      have d29616 : (x 14 2 && x 14 13).toNat = 0 := by
        have r29617 := hand2 (x 14 2) (x 14 13)
        have b29618 := hb (x 14 13)
        have b29619 := hb (x 14 2 && x 14 13)
        clear * - r29617 b29618 b29619 d29608
        omega
      have d29620 : (x 13 2).toNat = 0 := by
        have r29621 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
        have e29622 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e29623 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b29624 := hb (x 12 3)
        have b29625 := hb (x 13 2)
        have b29626 := hb (x 14 13)
        have b29627 := hb (x 15 12)
        clear * - r29621 e29622 e29623 b29624 b29625 b29626 b29627 d29596 d29608 d29592
        omega
      have d29628 : (x 10 1).toNat = 1 := by
        have r29629 := hand1 (x 10 1) (x 10 14)
        have b29630 := hb (x 10 1)
        have b29631 := hb (x 10 1 && x 10 14)
        clear * - r29629 b29630 b29631 d29516
        omega
      have d29632 : (x 11 14).toNat = 0 := by
        have r29633 : (x 11 14).toNat + (x 10 1).toNat = 1 := hd14 11
        have b29634 := hb (x 10 1)
        have b29635 := hb (x 11 14)
        clear * - r29633 b29634 b29635 d29628
        omega
      have d29636 : (x 11 1 && x 11 14).toNat = 0 := by
        have r29637 := hand2 (x 11 1) (x 11 14)
        have b29638 := hb (x 11 14)
        have b29639 := hb (x 11 1 && x 11 14)
        clear * - r29637 b29638 b29639 d29632
        omega
      have d29640 : (x 11 2).toNat = 0 := by
        have r29641 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
        have b29642 := hb (x 11 2)
        have b29643 := hb (x 11 14)
        clear * - r29641 b29642 b29643 d29632
        omega
      have d29644 : (x 10 2).toNat = 0 := by
        have r29645 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
        have e29646 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
        have e29647 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
        have b29648 := hb (x 9 3)
        have b29649 := hb (x 10 2)
        have b29650 := hb (x 11 13)
        have b29651 := hb (x 12 12)
        clear * - r29645 e29646 e29647 b29648 b29649 b29650 b29651 d29488 d29504 d29484
        omega
      have d29652 : (x 12 13).toNat = 1 := by
        have r29653 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := hcov13 12
        have b29654 := hb (x 10 2)
        have b29655 := hb (x 12 13)
        have b29656 := hb (x 11 1 && x 11 14)
        clear * - r29653 b29654 b29655 b29656 d29636 d29644
        omega
      have d29657 : (x 12 1).toNat = 1 := by
        have r29658 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
        have b29659 := hb (x 12 1)
        have b29660 := hb (x 12 13)
        clear * - r29658 b29659 b29660 d29652
        omega
      have d29661 : (x 13 14).toNat = 0 := by
        have r29662 : (x 13 14).toNat + (x 12 1).toNat = 1 := hd14 13
        have b29663 := hb (x 12 1)
        have b29664 := hb (x 13 14)
        clear * - r29662 b29663 b29664 d29657
        omega
      have d29665 : (x 13 1 && x 13 14).toNat = 0 := by
        have r29666 := hand2 (x 13 1) (x 13 14)
        have b29667 := hb (x 13 14)
        have b29668 := hb (x 13 1 && x 13 14)
        clear * - r29666 b29667 b29668 d29661
        omega
      have d29669 : (x 12 2).toNat = 1 := by
        have r29670 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
        have b29671 := hb (x 12 2)
        have b29672 := hb (x 14 13)
        have b29673 := hb (x 13 1 && x 13 14)
        clear * - r29670 b29671 b29672 b29673 d29608 d29665
        omega
      have d29674 : (x 14 12).toNat = 0 := by
        have r29675 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
        have e29676 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
        have e29677 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
        have b29678 := hb (x 11 3)
        have b29679 := hb (x 12 2)
        have b29680 := hb (x 13 13)
        have b29681 := hb (x 14 12)
        clear * - r29675 e29676 e29677 b29678 b29679 b29680 b29681 d29669
        omega
      have d29682 : (x 14 4).toNat = 0 := by
        have r29683 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
        have b29684 := hb (x 14 4)
        have b29685 := hb (x 14 12)
        clear * - r29683 b29684 b29685 d29674
        omega
      have d29686 : (x 14 4 && x 14 14).toNat = 0 := by
        have r29687 := hand1 (x 14 4) (x 14 14)
        have b29688 := hb (x 14 4)
        have b29689 := hb (x 14 4 && x 14 14)
        clear * - r29687 b29688 b29689 d29682
        omega
      have d29690 : (x 13 13).toNat = 0 := by
        have r29691 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
        have e29692 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
        have e29693 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
        have b29694 := hb (x 11 3)
        have b29695 := hb (x 12 2)
        have b29696 := hb (x 13 13)
        have b29697 := hb (x 14 12)
        clear * - r29691 e29692 e29693 b29694 b29695 b29696 b29697 d29674 d29669
        omega
      have d29698 : (x 13 5).toNat = 0 := by
        have r29699 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
        have b29700 := hb (x 13 5)
        have b29701 := hb (x 13 13)
        clear * - r29699 b29700 b29701 d29690
        omega
      have d29702 : (x 13 3 && x 13 14).toNat = 0 := by
        have r29703 := hand2 (x 13 3) (x 13 14)
        have b29704 := hb (x 13 14)
        have b29705 := hb (x 13 3 && x 13 14)
        clear * - r29703 b29704 b29705 d29661
        omega
      have d29706 : (x 16 11).toNat = 1 := by
        have r29707 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := hcov11 16
        have b29708 := hb (x 12 4)
        have b29709 := hb (x 16 11)
        have b29710 := hb (x 15 1 && x 15 12)
        have b29711 := hb (x 14 2 && x 14 13)
        have b29712 := hb (x 13 3 && x 13 14)
        clear * - r29707 b29708 b29709 b29710 b29711 b29712 d29604 d29616 d29702 d29500
        omega
      have d29713 : (x 16 3).toNat = 1 := by
        have r29714 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
        have b29715 := hb (x 16 3)
        have b29716 := hb (x 16 11)
        clear * - r29714 b29715 b29716 d29706
        omega
      have d29717 : (x 19 12).toNat = 0 := by
        have r29718 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
        have e29719 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
        have e29720 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
        have b29721 := hb (x 16 3)
        have b29722 := hb (x 17 2)
        have b29723 := hb (x 18 13)
        have b29724 := hb (x 19 12)
        clear * - r29718 e29719 e29720 b29721 b29722 b29723 b29724 d29713
        omega
      have d29725 : (x 18 13).toNat = 0 := by
        have r29726 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
        have e29727 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
        have e29728 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
        have b29729 := hb (x 16 3)
        have b29730 := hb (x 17 2)
        have b29731 := hb (x 18 13)
        have b29732 := hb (x 19 12)
        clear * - r29726 e29727 e29728 b29729 b29730 b29731 b29732 d29717 d29713
        omega
      have d29733 : (x 17 2).toNat = 0 := by
        have r29734 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
        have e29735 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
        have e29736 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
        have b29737 := hb (x 16 3)
        have b29738 := hb (x 17 2)
        have b29739 := hb (x 18 13)
        have b29740 := hb (x 19 12)
        clear * - r29734 e29735 e29736 b29737 b29738 b29739 b29740 d29717 d29725 d29713
        omega
      have d29741 : (x 13 12).toNat = 0 := by
        have r29742 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
        have e29743 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
        have e29744 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
        have b29745 := hb (x 10 3)
        have b29746 := hb (x 11 2)
        have b29747 := hb (x 12 13)
        have b29748 := hb (x 13 12)
        clear * - r29742 e29743 e29744 b29745 b29746 b29747 b29748 d29652 d29640
        omega
      have d29749 : (x 13 4).toNat = 0 := by
        have r29750 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
        have b29751 := hb (x 13 4)
        have b29752 := hb (x 13 12)
        clear * - r29750 b29751 b29752 d29741
        omega
      have d29753 : (x 10 3).toNat = 0 := by
        have r29754 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
        have e29755 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
        have e29756 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
        have b29757 := hb (x 10 3)
        have b29758 := hb (x 11 2)
        have b29759 := hb (x 12 13)
        have b29760 := hb (x 13 12)
        clear * - r29754 e29755 e29756 b29757 b29758 b29759 b29760 d29741 d29652 d29640
        omega
      have d29761 : (x 10 3 && x 10 14).toNat = 0 := by
        have r29762 := hand1 (x 10 3) (x 10 14)
        have b29763 := hb (x 10 3)
        have b29764 := hb (x 10 3 && x 10 14)
        clear * - r29762 b29763 b29764 d29753
        omega
      have d29765 : (x 13 11).toNat = 1 := by
        have r29766 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := hcov11 13
        have b29767 := hb (x 9 4)
        have b29768 := hb (x 13 11)
        have b29769 := hb (x 12 1 && x 12 12)
        have b29770 := hb (x 11 2 && x 11 13)
        have b29771 := hb (x 10 3 && x 10 14)
        clear * - r29766 b29767 b29768 b29769 b29770 b29771 d29496 d29512 d29761 d29461
        omega
      have d29772 : (x 13 3).toNat = 1 := by
        have r29773 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
        have b29774 := hb (x 13 3)
        have b29775 := hb (x 13 11)
        clear * - r29773 b29774 b29775 d29765
        omega
      have d29776 : (x 16 12).toNat = 0 := by
        have r29777 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
        have e29778 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
        have e29779 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
        have b29780 := hb (x 13 3)
        have b29781 := hb (x 14 2)
        have b29782 := hb (x 15 13)
        have b29783 := hb (x 16 12)
        clear * - r29777 e29778 e29779 b29780 b29781 b29782 b29783 d29772
        omega
      have d29784 : (x 16 1 && x 16 12).toNat = 0 := by
        have r29785 := hand2 (x 16 1) (x 16 12)
        have b29786 := hb (x 16 12)
        have b29787 := hb (x 16 1 && x 16 12)
        clear * - r29785 b29786 b29787 d29776
        omega
      have d29788 : (x 16 2 && x 16 12).toNat = 0 := by
        have r29789 := hand2 (x 16 2) (x 16 12)
        have b29790 := hb (x 16 12)
        have b29791 := hb (x 16 2 && x 16 12)
        clear * - r29789 b29790 b29791 d29776
        omega
      have d29792 : (x 15 13).toNat = 0 := by
        have r29793 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
        have e29794 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
        have e29795 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
        have b29796 := hb (x 13 3)
        have b29797 := hb (x 14 2)
        have b29798 := hb (x 15 13)
        have b29799 := hb (x 16 12)
        clear * - r29793 e29794 e29795 b29796 b29797 b29798 b29799 d29776 d29772
        omega
      have d29800 : (x 15 2 && x 15 13).toNat = 0 := by
        have r29801 := hand2 (x 15 2) (x 15 13)
        have b29802 := hb (x 15 13)
        have b29803 := hb (x 15 2 && x 15 13)
        clear * - r29801 b29802 b29803 d29792
        omega
      have d29804 : (x 15 3 && x 15 13).toNat = 0 := by
        have r29805 := hand2 (x 15 3) (x 15 13)
        have b29806 := hb (x 15 13)
        have b29807 := hb (x 15 3 && x 15 13)
        clear * - r29805 b29806 b29807 d29792
        omega
      have d29808 : (x 14 1 && x 14 14).toNat = 1 := by
        have r29809 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := hcov13 15
        have b29810 := hb (x 13 2)
        have b29811 := hb (x 15 13)
        have b29812 := hb (x 14 1 && x 14 14)
        clear * - r29809 b29810 b29811 b29812 d29792 d29620
        omega
      have d29813 : (x 14 1).toNat = 1 := by
        have r29814 := hand1 (x 14 1) (x 14 14)
        have b29815 := hb (x 14 1)
        have b29816 := hb (x 14 1 && x 14 14)
        clear * - r29814 b29815 b29816 d29808
        omega
      have d29817 : (x 15 14).toNat = 0 := by
        have r29818 : (x 15 14).toNat + (x 14 1).toNat = 1 := hd14 15
        have b29819 := hb (x 14 1)
        have b29820 := hb (x 15 14)
        clear * - r29818 b29819 b29820 d29813
        omega
      have d29821 : (x 15 1 && x 15 14).toNat = 0 := by
        have r29822 := hand2 (x 15 1) (x 15 14)
        have b29823 := hb (x 15 14)
        have b29824 := hb (x 15 1 && x 15 14)
        clear * - r29822 b29823 b29824 d29817
        omega
      have d29825 : (x 15 2).toNat = 0 := by
        have r29826 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
        have b29827 := hb (x 15 2)
        have b29828 := hb (x 15 14)
        clear * - r29826 b29827 b29828 d29817
        omega
      have d29829 : (x 14 2).toNat = 0 := by
        have r29830 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
        have e29831 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
        have e29832 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
        have b29833 := hb (x 13 3)
        have b29834 := hb (x 14 2)
        have b29835 := hb (x 15 13)
        have b29836 := hb (x 16 12)
        clear * - r29830 e29831 e29832 b29833 b29834 b29835 b29836 d29776 d29792 d29772
        omega
      have d29837 : (x 16 13).toNat = 1 := by
        have r29838 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := hcov13 16
        have b29839 := hb (x 14 2)
        have b29840 := hb (x 16 13)
        have b29841 := hb (x 15 1 && x 15 14)
        clear * - r29838 b29839 b29840 b29841 d29821 d29829
        omega
      have d29842 : (x 17 12).toNat = 0 := by
        have r29843 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
        have e29844 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
        have e29845 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
        have b29846 := hb (x 14 3)
        have b29847 := hb (x 15 2)
        have b29848 := hb (x 16 13)
        have b29849 := hb (x 17 12)
        clear * - r29843 e29844 e29845 b29846 b29847 b29848 b29849 d29837 d29825
        omega
      have d29850 : (x 14 3).toNat = 0 := by
        have r29851 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
        have e29852 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
        have e29853 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
        have b29854 := hb (x 14 3)
        have b29855 := hb (x 15 2)
        have b29856 := hb (x 16 13)
        have b29857 := hb (x 17 12)
        clear * - r29851 e29852 e29853 b29854 b29855 b29856 b29857 d29842 d29837 d29825
        omega
      have d29858 : (x 14 3 && x 14 14).toNat = 0 := by
        have r29859 := hand1 (x 14 3) (x 14 14)
        have b29860 := hb (x 14 3)
        have b29861 := hb (x 14 3 && x 14 14)
        clear * - r29859 b29860 b29861 d29850
        omega
      have d29862 : (x 17 11).toNat = 1 := by
        have r29863 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := hcov11 17
        have b29864 := hb (x 13 4)
        have b29865 := hb (x 17 11)
        have b29866 := hb (x 16 1 && x 16 12)
        have b29867 := hb (x 15 2 && x 15 13)
        have b29868 := hb (x 14 3 && x 14 14)
        clear * - r29863 b29864 b29865 b29866 b29867 b29868 d29784 d29800 d29858 d29749
        omega
      have d29869 : (x 17 3).toNat = 1 := by
        have r29870 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
        have b29871 := hb (x 17 3)
        have b29872 := hb (x 17 11)
        clear * - r29870 b29871 b29872 d29862
        omega
      have d29873 : (x 20 12).toNat = 0 := by
        have r29874 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
        have e29875 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
        have e29876 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
        have b29877 := hb (x 17 3)
        have b29878 := hb (x 18 2)
        have b29879 := hb (x 19 13)
        have b29880 := hb (x 20 12)
        clear * - r29874 e29875 e29876 b29877 b29878 b29879 b29880 d29869
        omega
      have d29881 : (x 19 13).toNat = 0 := by
        have r29882 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
        have e29883 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
        have e29884 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
        have b29885 := hb (x 17 3)
        have b29886 := hb (x 18 2)
        have b29887 := hb (x 19 13)
        have b29888 := hb (x 20 12)
        clear * - r29882 e29883 e29884 b29885 b29886 b29887 b29888 d29873 d29869
        omega
      have d29889 : (x 18 1 && x 18 14).toNat = 1 := by
        have r29890 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := hcov13 19
        have b29891 := hb (x 17 2)
        have b29892 := hb (x 19 13)
        have b29893 := hb (x 18 1 && x 18 14)
        clear * - r29890 b29891 b29892 b29893 d29881 d29733
        omega
      have d29894 : (x 18 14).toNat = 1 := by
        have r29895 := hand2 (x 18 1) (x 18 14)
        have b29896 := hb (x 18 14)
        have b29897 := hb (x 18 1 && x 18 14)
        clear * - r29895 b29896 b29897 d29889
        omega
      have d29898 : (x 17 1).toNat = 0 := by
        have r29899 : (x 18 14).toNat + (x 17 1).toNat = 1 := hd14 18
        have b29900 := hb (x 17 1)
        have b29901 := hb (x 18 14)
        clear * - r29899 b29900 b29901 d29894
        omega
      have d29902 : (x 17 1 && x 17 11).toNat = 0 := by
        have r29903 := hand1 (x 17 1) (x 17 11)
        have b29904 := hb (x 17 1)
        have b29905 := hb (x 17 1 && x 17 11)
        clear * - r29903 b29904 b29905 d29898
        omega
      have d29906 : (x 18 2).toNat = 0 := by
        have r29907 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
        have e29908 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
        have e29909 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
        have b29910 := hb (x 17 3)
        have b29911 := hb (x 18 2)
        have b29912 := hb (x 19 13)
        have b29913 := hb (x 20 12)
        clear * - r29907 e29908 e29909 b29910 b29911 b29912 b29913 d29873 d29881 d29869
        omega
      have d29914 : (x 18 10).toNat = 0 := by
        have r29915 : (x 18 10).toNat ≤ (x 18 2).toNat := himp _ _ (hp10 18)
        have b29916 := hb (x 18 2)
        have b29917 := hb (x 18 10)
        clear * - r29915 b29916 b29917 d29906
        omega
      have r29918 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := hcov10 18
      have b29919 := hb (x 13 5)
      have b29920 := hb (x 18 10)
      have b29921 := hb (x 17 1 && x 17 11)
      have b29922 := hb (x 16 2 && x 16 12)
      have b29923 := hb (x 15 3 && x 15 13)
      have b29924 := hb (x 14 4 && x 14 14)
      linarith only [r29918, b29919, b29920, b29921, b29922, b29923, b29924, d29914, d29902, d29788, d29804, d29686, d29698]
  · have f29925 : (x 1 1).toNat = 1 := by rw [h28540]; rfl
    have d29926 : (x 2 14).toNat = 0 := by
      have r29927 : (x 2 14).toNat + (x 1 1).toNat = 1 := hd14 2
      have b29928 := hb (x 1 1)
      have b29929 := hb (x 2 14)
      clear * - r29927 b29928 b29929 f29925
      omega
    have d29930 : (x 2 1 && x 2 14).toNat = 0 := by
      have r29931 := hand2 (x 2 1) (x 2 14)
      have b29932 := hb (x 2 14)
      have b29933 := hb (x 2 1 && x 2 14)
      clear * - r29931 b29932 b29933 d29926
      omega
    have d29934 : (x 2 2).toNat = 0 := by
      have r29935 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
      have b29936 := hb (x 2 2)
      have b29937 := hb (x 2 14)
      clear * - r29935 b29936 b29937 d29926
      omega
    have d29938 : (x 4 13).toNat = 1 := by
      have r29939 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
      have b29940 := hb (x 2 2)
      have b29941 := hb (x 4 13)
      have b29942 := hb (x 3 1 && x 3 14)
      clear * - r29939 b29940 b29941 b29942 g34 d29934
      omega
    have d29943 : (x 4 1).toNat = 1 := by
      have r29944 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
      have b29945 := hb (x 4 1)
      have b29946 := hb (x 4 13)
      clear * - r29944 b29945 b29946 d29938
      omega
    have d29947 : (x 5 14).toNat = 0 := by
      have r29948 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
      have b29949 := hb (x 4 1)
      have b29950 := hb (x 5 14)
      clear * - r29948 b29949 b29950 d29943
      omega
    have d29951 : (x 5 1 && x 5 14).toNat = 0 := by
      have r29952 := hand2 (x 5 1) (x 5 14)
      have b29953 := hb (x 5 14)
      have b29954 := hb (x 5 1 && x 5 14)
      clear * - r29952 b29953 b29954 d29947
      omega
    have d29955 : (x 5 2).toNat = 0 := by
      have r29956 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
      have b29957 := hb (x 5 2)
      have b29958 := hb (x 5 14)
      clear * - r29956 b29957 b29958 d29947
      omega
    have d29959 : (x 3 13).toNat = 1 := by
      have r29960 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := hcov13 3
      have b29961 := hb (x 1 2)
      have b29962 := hb (x 3 13)
      have b29963 := hb (x 2 1 && x 2 14)
      clear * - r29960 b29961 b29962 b29963 d29930 g8
      omega
    have d29964 : (x 3 1).toNat = 1 := by
      have r29965 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
      have b29966 := hb (x 3 1)
      have b29967 := hb (x 3 13)
      clear * - r29965 b29966 b29967 d29959
      omega
    have d29968 : (x 4 14).toNat = 0 := by
      have r29969 : (x 4 14).toNat + (x 3 1).toNat = 1 := hd14 4
      have b29970 := hb (x 3 1)
      have b29971 := hb (x 4 14)
      clear * - r29969 b29970 b29971 d29964
      omega
    have d29972 : (x 4 1 && x 4 14).toNat = 0 := by
      have r29973 := hand2 (x 4 1) (x 4 14)
      have b29974 := hb (x 4 14)
      have b29975 := hb (x 4 1 && x 4 14)
      clear * - r29973 b29974 b29975 d29968
      omega
    have d29976 : (x 5 13).toNat = 1 := by
      have r29977 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := hcov13 5
      have b29978 := hb (x 3 2)
      have b29979 := hb (x 5 13)
      have b29980 := hb (x 4 1 && x 4 14)
      clear * - r29977 b29978 b29979 b29980 d29972 g14
      omega
    have d29981 : (x 5 1).toNat = 1 := by
      have r29982 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
      have b29983 := hb (x 5 1)
      have b29984 := hb (x 5 13)
      clear * - r29982 b29983 b29984 d29976
      omega
    have d29985 : (x 6 14).toNat = 0 := by
      have r29986 : (x 6 14).toNat + (x 5 1).toNat = 1 := hd14 6
      have b29987 := hb (x 5 1)
      have b29988 := hb (x 6 14)
      clear * - r29986 b29987 b29988 d29981
      omega
    have d29989 : (x 6 1 && x 6 14).toNat = 0 := by
      have r29990 := hand2 (x 6 1) (x 6 14)
      have b29991 := hb (x 6 14)
      have b29992 := hb (x 6 1 && x 6 14)
      clear * - r29990 b29991 b29992 d29985
      omega
    have d29993 : (x 7 13).toNat = 1 := by
      have r29994 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
      have b29995 := hb (x 5 2)
      have b29996 := hb (x 7 13)
      have b29997 := hb (x 6 1 && x 6 14)
      clear * - r29994 b29995 b29996 b29997 d29989 d29955
      omega
    have d29998 : (x 7 1).toNat = 1 := by
      have r29999 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
      have b30000 := hb (x 7 1)
      have b30001 := hb (x 7 13)
      clear * - r29999 b30000 b30001 d29993
      omega
    have d30002 : (x 8 14).toNat = 0 := by
      have r30003 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
      have b30004 := hb (x 7 1)
      have b30005 := hb (x 8 14)
      clear * - r30003 b30004 b30005 d29998
      omega
    have d30006 : (x 8 1 && x 8 14).toNat = 0 := by
      have r30007 := hand2 (x 8 1) (x 8 14)
      have b30008 := hb (x 8 14)
      have b30009 := hb (x 8 1 && x 8 14)
      clear * - r30007 b30008 b30009 d30002
      omega
    have d30010 : (x 8 2).toNat = 0 := by
      have r30011 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
      have b30012 := hb (x 8 2)
      have b30013 := hb (x 8 14)
      clear * - r30011 b30012 b30013 d30002
      omega
    have d30014 : (x 6 2).toNat = 0 := by
      have r30015 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
      have b30016 := hb (x 6 2)
      have b30017 := hb (x 6 14)
      clear * - r30015 b30016 b30017 d29985
      omega
    have d30018 : (x 4 2).toNat = 0 := by
      have r30019 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
      have b30020 := hb (x 4 2)
      have b30021 := hb (x 4 14)
      clear * - r30019 b30020 b30021 d29968
      omega
    have d30022 : (x 6 13).toNat = 1 := by
      have r30023 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := hcov13 6
      have b30024 := hb (x 4 2)
      have b30025 := hb (x 6 13)
      have b30026 := hb (x 5 1 && x 5 14)
      clear * - r30023 b30024 b30025 b30026 d29951 d30018
      omega
    have d30027 : (x 6 1).toNat = 1 := by
      have r30028 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
      have b30029 := hb (x 6 1)
      have b30030 := hb (x 6 13)
      clear * - r30028 b30029 b30030 d30022
      omega
    have d30031 : (x 7 14).toNat = 0 := by
      have r30032 : (x 7 14).toNat + (x 6 1).toNat = 1 := hd14 7
      have b30033 := hb (x 6 1)
      have b30034 := hb (x 7 14)
      clear * - r30032 b30033 b30034 d30027
      omega
    have d30035 : (x 7 1 && x 7 14).toNat = 0 := by
      have r30036 := hand2 (x 7 1) (x 7 14)
      have b30037 := hb (x 7 14)
      have b30038 := hb (x 7 1 && x 7 14)
      clear * - r30036 b30037 b30038 d30031
      omega
    have d30039 : (x 8 13).toNat = 1 := by
      have r30040 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := hcov13 8
      have b30041 := hb (x 6 2)
      have b30042 := hb (x 8 13)
      have b30043 := hb (x 7 1 && x 7 14)
      clear * - r30040 b30041 b30042 b30043 d30035 d30014
      omega
    have d30044 : (x 8 1).toNat = 1 := by
      have r30045 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
      have b30046 := hb (x 8 1)
      have b30047 := hb (x 8 13)
      clear * - r30045 b30046 b30047 d30039
      omega
    have d30048 : (x 9 14).toNat = 0 := by
      have r30049 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
      have b30050 := hb (x 8 1)
      have b30051 := hb (x 9 14)
      clear * - r30049 b30050 b30051 d30044
      omega
    have d30052 : (x 9 1 && x 9 14).toNat = 0 := by
      have r30053 := hand2 (x 9 1) (x 9 14)
      have b30054 := hb (x 9 14)
      have b30055 := hb (x 9 1 && x 9 14)
      clear * - r30053 b30054 b30055 d30048
      omega
    have d30056 : (x 10 13).toNat = 1 := by
      have r30057 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := hcov13 10
      have b30058 := hb (x 8 2)
      have b30059 := hb (x 10 13)
      have b30060 := hb (x 9 1 && x 9 14)
      clear * - r30057 b30058 b30059 b30060 d30052 d30010
      omega
    have d30061 : (x 10 1).toNat = 1 := by
      have r30062 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
      have b30063 := hb (x 10 1)
      have b30064 := hb (x 10 13)
      clear * - r30062 b30063 b30064 d30056
      omega
    have d30065 : (x 11 14).toNat = 0 := by
      have r30066 : (x 11 14).toNat + (x 10 1).toNat = 1 := hd14 11
      have b30067 := hb (x 10 1)
      have b30068 := hb (x 11 14)
      clear * - r30066 b30067 b30068 d30061
      omega
    have d30069 : (x 11 1 && x 11 14).toNat = 0 := by
      have r30070 := hand2 (x 11 1) (x 11 14)
      have b30071 := hb (x 11 14)
      have b30072 := hb (x 11 1 && x 11 14)
      clear * - r30070 b30071 b30072 d30065
      omega
    have d30073 : (x 11 2).toNat = 0 := by
      have r30074 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
      have b30075 := hb (x 11 2)
      have b30076 := hb (x 11 14)
      clear * - r30074 b30075 b30076 d30065
      omega
    have d30077 : (x 9 2).toNat = 0 := by
      have r30078 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
      have b30079 := hb (x 9 2)
      have b30080 := hb (x 9 14)
      clear * - r30078 b30079 b30080 d30048
      omega
    have d30081 : (x 7 2).toNat = 0 := by
      have r30082 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
      have b30083 := hb (x 7 2)
      have b30084 := hb (x 7 14)
      clear * - r30082 b30083 b30084 d30031
      omega
    have d30085 : (x 9 13).toNat = 1 := by
      have r30086 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := hcov13 9
      have b30087 := hb (x 7 2)
      have b30088 := hb (x 9 13)
      have b30089 := hb (x 8 1 && x 8 14)
      clear * - r30086 b30087 b30088 b30089 d30006 d30081
      omega
    have d30090 : (x 9 1).toNat = 1 := by
      have r30091 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
      have b30092 := hb (x 9 1)
      have b30093 := hb (x 9 13)
      clear * - r30091 b30092 b30093 d30085
      omega
    have d30094 : (x 10 14).toNat = 0 := by
      have r30095 : (x 10 14).toNat + (x 9 1).toNat = 1 := hd14 10
      have b30096 := hb (x 9 1)
      have b30097 := hb (x 10 14)
      clear * - r30095 b30096 b30097 d30090
      omega
    have d30098 : (x 10 1 && x 10 14).toNat = 0 := by
      have r30099 := hand2 (x 10 1) (x 10 14)
      have b30100 := hb (x 10 14)
      have b30101 := hb (x 10 1 && x 10 14)
      clear * - r30099 b30100 b30101 d30094
      omega
    have d30102 : (x 11 13).toNat = 1 := by
      have r30103 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := hcov13 11
      have b30104 := hb (x 9 2)
      have b30105 := hb (x 11 13)
      have b30106 := hb (x 10 1 && x 10 14)
      clear * - r30103 b30104 b30105 b30106 d30098 d30077
      omega
    have d30107 : (x 11 1).toNat = 1 := by
      have r30108 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
      have b30109 := hb (x 11 1)
      have b30110 := hb (x 11 13)
      clear * - r30108 b30109 b30110 d30102
      omega
    have d30111 : (x 12 14).toNat = 0 := by
      have r30112 : (x 12 14).toNat + (x 11 1).toNat = 1 := hd14 12
      have b30113 := hb (x 11 1)
      have b30114 := hb (x 12 14)
      clear * - r30112 b30113 b30114 d30107
      omega
    have d30115 : (x 12 1 && x 12 14).toNat = 0 := by
      have r30116 := hand2 (x 12 1) (x 12 14)
      have b30117 := hb (x 12 14)
      have b30118 := hb (x 12 1 && x 12 14)
      clear * - r30116 b30117 b30118 d30111
      omega
    have d30119 : (x 13 13).toNat = 1 := by
      have r30120 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := hcov13 13
      have b30121 := hb (x 11 2)
      have b30122 := hb (x 13 13)
      have b30123 := hb (x 12 1 && x 12 14)
      clear * - r30120 b30121 b30122 b30123 d30115 d30073
      omega
    have d30124 : (x 13 1).toNat = 1 := by
      have r30125 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
      have b30126 := hb (x 13 1)
      have b30127 := hb (x 13 13)
      clear * - r30125 b30126 b30127 d30119
      omega
    have d30128 : (x 14 14).toNat = 0 := by
      have r30129 : (x 14 14).toNat + (x 13 1).toNat = 1 := hd14 14
      have b30130 := hb (x 13 1)
      have b30131 := hb (x 14 14)
      clear * - r30129 b30130 b30131 d30124
      omega
    have d30132 : (x 14 1 && x 14 14).toNat = 0 := by
      have r30133 := hand2 (x 14 1) (x 14 14)
      have b30134 := hb (x 14 14)
      have b30135 := hb (x 14 1 && x 14 14)
      clear * - r30133 b30134 b30135 d30128
      omega
    have d30136 : (x 14 3 && x 14 14).toNat = 0 := by
      have r30137 := hand2 (x 14 3) (x 14 14)
      have b30138 := hb (x 14 14)
      have b30139 := hb (x 14 3 && x 14 14)
      clear * - r30137 b30138 b30139 d30128
      omega
    have d30140 : (x 14 2).toNat = 0 := by
      have r30141 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
      have b30142 := hb (x 14 2)
      have b30143 := hb (x 14 14)
      clear * - r30141 b30142 b30143 d30128
      omega
    have d30144 : (x 12 2).toNat = 0 := by
      have r30145 : (x 12 2).toNat ≤ (x 12 14).toNat := himp _ _ (hp2 12)
      have b30146 := hb (x 12 2)
      have b30147 := hb (x 12 14)
      clear * - r30145 b30146 b30147 d30111
      omega
    have d30148 : (x 10 2).toNat = 0 := by
      have r30149 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
      have b30150 := hb (x 10 2)
      have b30151 := hb (x 10 14)
      clear * - r30149 b30150 b30151 d30094
      omega
    have d30152 : (x 12 13).toNat = 1 := by
      have r30153 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := hcov13 12
      have b30154 := hb (x 10 2)
      have b30155 := hb (x 12 13)
      have b30156 := hb (x 11 1 && x 11 14)
      clear * - r30153 b30154 b30155 b30156 d30069 d30148
      omega
    have d30157 : (x 12 1).toNat = 1 := by
      have r30158 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
      have b30159 := hb (x 12 1)
      have b30160 := hb (x 12 13)
      clear * - r30158 b30159 b30160 d30152
      omega
    have d30161 : (x 13 14).toNat = 0 := by
      have r30162 : (x 13 14).toNat + (x 12 1).toNat = 1 := hd14 13
      have b30163 := hb (x 12 1)
      have b30164 := hb (x 13 14)
      clear * - r30162 b30163 b30164 d30157
      omega
    have d30165 : (x 13 1 && x 13 14).toNat = 0 := by
      have r30166 := hand2 (x 13 1) (x 13 14)
      have b30167 := hb (x 13 14)
      have b30168 := hb (x 13 1 && x 13 14)
      clear * - r30166 b30167 b30168 d30161
      omega
    have d30169 : (x 14 13).toNat = 1 := by
      have r30170 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
      have b30171 := hb (x 12 2)
      have b30172 := hb (x 14 13)
      have b30173 := hb (x 13 1 && x 13 14)
      clear * - r30170 b30171 b30172 b30173 d30165 d30144
      omega
    have d30174 : (x 14 1).toNat = 1 := by
      have r30175 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
      have b30176 := hb (x 14 1)
      have b30177 := hb (x 14 13)
      clear * - r30175 b30176 b30177 d30169
      omega
    have d30178 : (x 15 14).toNat = 0 := by
      have r30179 : (x 15 14).toNat + (x 14 1).toNat = 1 := hd14 15
      have b30180 := hb (x 14 1)
      have b30181 := hb (x 15 14)
      clear * - r30179 b30180 b30181 d30174
      omega
    have d30182 : (x 15 1 && x 15 14).toNat = 0 := by
      have r30183 := hand2 (x 15 1) (x 15 14)
      have b30184 := hb (x 15 14)
      have b30185 := hb (x 15 1 && x 15 14)
      clear * - r30183 b30184 b30185 d30178
      omega
    have d30186 : (x 16 13).toNat = 1 := by
      have r30187 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := hcov13 16
      have b30188 := hb (x 14 2)
      have b30189 := hb (x 16 13)
      have b30190 := hb (x 15 1 && x 15 14)
      clear * - r30187 b30188 b30189 b30190 d30182 d30140
      omega
    have d30191 : (x 16 1).toNat = 1 := by
      have r30192 : (x 16 13).toNat ≤ (x 16 1).toNat := himp _ _ (hp13 16)
      have b30193 := hb (x 16 1)
      have b30194 := hb (x 16 13)
      clear * - r30192 b30193 b30194 d30186
      omega
    have d30195 : (x 17 14).toNat = 0 := by
      have r30196 : (x 17 14).toNat + (x 16 1).toNat = 1 := hd14 17
      have b30197 := hb (x 16 1)
      have b30198 := hb (x 17 14)
      clear * - r30196 b30197 b30198 d30191
      omega
    have d30199 : (x 17 2).toNat = 0 := by
      have r30200 : (x 17 2).toNat ≤ (x 17 14).toNat := himp _ _ (hp2 17)
      have b30201 := hb (x 17 2)
      have b30202 := hb (x 17 14)
      clear * - r30200 b30201 b30202 d30195
      omega
    have d30203 : (x 15 2).toNat = 0 := by
      have r30204 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
      have b30205 := hb (x 15 2)
      have b30206 := hb (x 15 14)
      clear * - r30204 b30205 b30206 d30178
      omega
    have d30207 : (x 15 2 && x 15 13).toNat = 0 := by
      have r30208 := hand1 (x 15 2) (x 15 13)
      have b30209 := hb (x 15 2)
      have b30210 := hb (x 15 2 && x 15 13)
      clear * - r30208 b30209 b30210 d30203
      omega
    have d30211 : (x 13 2).toNat = 0 := by
      have r30212 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
      have b30213 := hb (x 13 2)
      have b30214 := hb (x 13 14)
      clear * - r30212 b30213 b30214 d30161
      omega
    have d30215 : (x 15 13).toNat = 1 := by
      have r30216 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := hcov13 15
      have b30217 := hb (x 13 2)
      have b30218 := hb (x 15 13)
      have b30219 := hb (x 14 1 && x 14 14)
      clear * - r30216 b30217 b30218 b30219 d30132 d30211
      omega
    have d30220 : (x 15 1).toNat = 1 := by
      have r30221 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
      have b30222 := hb (x 15 1)
      have b30223 := hb (x 15 13)
      clear * - r30221 b30222 b30223 d30215
      omega
    have d30224 : (x 16 14).toNat = 0 := by
      have r30225 : (x 16 14).toNat + (x 15 1).toNat = 1 := hd14 16
      have b30226 := hb (x 15 1)
      have b30227 := hb (x 16 14)
      clear * - r30225 b30226 b30227 d30220
      omega
    have d30228 : (x 16 1 && x 16 14).toNat = 0 := by
      have r30229 := hand2 (x 16 1) (x 16 14)
      have b30230 := hb (x 16 14)
      have b30231 := hb (x 16 1 && x 16 14)
      clear * - r30229 b30230 b30231 d30224
      omega
    have d30232 : (x 17 13).toNat = 1 := by
      have r30233 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := hcov13 17
      have b30234 := hb (x 15 2)
      have b30235 := hb (x 17 13)
      have b30236 := hb (x 16 1 && x 16 14)
      clear * - r30233 b30234 b30235 b30236 d30228 d30203
      omega
    have d30237 : (x 17 1).toNat = 1 := by
      have r30238 : (x 17 13).toNat ≤ (x 17 1).toNat := himp _ _ (hp13 17)
      have b30239 := hb (x 17 1)
      have b30240 := hb (x 17 13)
      clear * - r30238 b30239 b30240 d30232
      omega
    have d30241 : (x 18 14).toNat = 0 := by
      have r30242 : (x 18 14).toNat + (x 17 1).toNat = 1 := hd14 18
      have b30243 := hb (x 17 1)
      have b30244 := hb (x 18 14)
      clear * - r30242 b30243 b30244 d30237
      omega
    have d30245 : (x 18 1 && x 18 14).toNat = 0 := by
      have r30246 := hand2 (x 18 1) (x 18 14)
      have b30247 := hb (x 18 14)
      have b30248 := hb (x 18 1 && x 18 14)
      clear * - r30246 b30247 b30248 d30241
      omega
    have d30249 : (x 19 13).toNat = 1 := by
      have r30250 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := hcov13 19
      have b30251 := hb (x 17 2)
      have b30252 := hb (x 19 13)
      have b30253 := hb (x 18 1 && x 18 14)
      clear * - r30250 b30251 b30252 b30253 d30245 d30199
      omega
    have d30254 : (x 18 2).toNat = 0 := by
      have r30255 : (x 18 2).toNat ≤ (x 18 14).toNat := himp _ _ (hp2 18)
      have b30256 := hb (x 18 2)
      have b30257 := hb (x 18 14)
      clear * - r30255 b30256 b30257 d30241
      omega
    have d30258 : (x 20 12).toNat = 0 := by
      have r30259 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
      have e30260 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
      have e30261 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
      have b30262 := hb (x 17 3)
      have b30263 := hb (x 18 2)
      have b30264 := hb (x 19 13)
      have b30265 := hb (x 20 12)
      clear * - r30259 e30260 e30261 b30262 b30263 b30264 b30265 d30249 d30254
      omega
    have d30266 : (x 17 3).toNat = 0 := by
      have r30267 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
      have e30268 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
      have e30269 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
      have b30270 := hb (x 17 3)
      have b30271 := hb (x 18 2)
      have b30272 := hb (x 19 13)
      have b30273 := hb (x 20 12)
      clear * - r30267 e30268 e30269 b30270 b30271 b30272 b30273 d30258 d30249 d30254
      omega
    have d30274 : (x 17 11).toNat = 0 := by
      have r30275 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
      have b30276 := hb (x 17 3)
      have b30277 := hb (x 17 11)
      clear * - r30275 b30276 b30277 d30266
      omega
    have d30278 : (x 16 12).toNat = 0 := by
      have r30279 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
      have e30280 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
      have e30281 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
      have b30282 := hb (x 13 3)
      have b30283 := hb (x 14 2)
      have b30284 := hb (x 15 13)
      have b30285 := hb (x 16 12)
      clear * - r30279 e30280 e30281 b30282 b30283 b30284 b30285 d30215 d30140
      omega
    have d30286 : (x 16 1 && x 16 12).toNat = 0 := by
      have r30287 := hand2 (x 16 1) (x 16 12)
      have b30288 := hb (x 16 12)
      have b30289 := hb (x 16 1 && x 16 12)
      clear * - r30287 b30288 b30289 d30278
      omega
    have d30290 : (x 13 12).toNat = 0 := by
      have r30291 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
      have e30292 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
      have e30293 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
      have b30294 := hb (x 10 3)
      have b30295 := hb (x 11 2)
      have b30296 := hb (x 12 13)
      have b30297 := hb (x 13 12)
      clear * - r30291 e30292 e30293 b30294 b30295 b30296 b30297 d30152 d30073
      omega
    have d30298 : (x 13 4).toNat = 0 := by
      have r30299 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
      have b30300 := hb (x 13 4)
      have b30301 := hb (x 13 12)
      clear * - r30299 b30300 b30301 d30290
      omega
    have r30302 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := hcov11 17
    have b30303 := hb (x 13 4)
    have b30304 := hb (x 17 11)
    have b30305 := hb (x 16 1 && x 16 12)
    have b30306 := hb (x 15 2 && x 15 13)
    have b30307 := hb (x 14 3 && x 14 14)
    linarith only [r30302, b30303, b30304, b30305, b30306, b30307, d30274, d30286, d30207, d30136, d30298]

theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0000101 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-2) 5).toNat = 0)
    (g1 : (x (-2) 11).toNat = 0)
    (g2 : (x (-2) 13).toNat = 0)
    (g3 : (x 0 3).toNat = 0)
    (g4 : (x 0 6).toNat = 0)
    (g5 : (x 0 7).toNat = 0)
    (g6 : (x 0 9).toNat = 1)
    (g7 : (x 0 11).toNat = 0)
    (g8 : (x 1 2).toNat = 0)
    (g9 : (x 1 4).toNat = 0)
    (g10 : (x 1 6).toNat = 0)
    (g11 : (x 1 10).toNat = 0)
    (g12 : (x 2 1).toNat = 1)
    (g13 : (x 2 4).toNat = 0)
    (g14 : (x 3 2).toNat = 0)
    (g15 : (x 3 4).toNat = 0)
    (g16 : (x 1 2 && x 1 6).toNat = 0)
    (g17 : (x 0 3 && x 0 7).toNat = 0)
    (g18 : (x (-1) 4 && x (-1) 8).toNat = 0)
    (g19 : (x (-2) 5 && x (-2) 9).toNat = 0)
    (g20 : (x 0 1 && x 0 7).toNat = 0)
    (g21 : (x (-1) 2 && x (-1) 8).toNat = 0)
    (g22 : (x (-2) 3 && x (-2) 9).toNat = 0)
    (g23 : (x 3 3 && x 3 12).toNat = 0)
    (g24 : (x 2 4 && x 2 13).toNat = 0)
    (g25 : (x 1 5 && x 1 14).toNat = 0)
    (g26 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g27 : (x 0 1 && x 0 11).toNat = 0)
    (g28 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g29 : (x 2 1 && x 2 12).toNat = 0)
    (g30 : (x 1 2 && x 1 13).toNat = 0)
    (g31 : (x 0 3 && x 0 14).toNat = 0)
    (g32 : (x 3 2 && x 3 13).toNat = 0)
    (g33 : (x 3 3 && x 3 14).toNat = 0)
    (g34 : (x 3 1 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0000101_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34
