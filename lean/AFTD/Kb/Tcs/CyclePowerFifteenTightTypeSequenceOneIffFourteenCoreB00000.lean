import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b00000

Topic: combinatorics   Node: f3da87ac7326

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core: under the layer-free tight-cover constraints for k = 15 and 34 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b00000_aux (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x (-3) 11).toNat = 0)
    (g2 : (x (-3) 13).toNat = 0)
    (g3 : (x (-1) 5).toNat = 0)
    (g4 : (x (-1) 13).toNat = 0)
    (g5 : (x 0 2).toNat = 0)
    (g6 : (x 0 3).toNat = 0)
    (g7 : (x 0 4).toNat = 0)
    (g8 : (x 0 5).toNat = 0)
    (g9 : (x 0 7).toNat = 0)
    (g10 : (x 0 10).toNat = 0)
    (g11 : (x 0 11).toNat = 0)
    (g12 : (x 0 13).toNat = 0)
    (g13 : (x 0 14).toNat = 1)
    (g14 : (x 1 3).toNat = 0)
    (g15 : (x 1 14).toNat = 1)
    (g16 : (x 0 2 && x 0 5).toNat = 0)
    (g17 : (x (-3) 5 && x (-3) 8).toNat = 0)
    (g18 : (x 0 3 && x 0 12).toNat = 0)
    (g19 : (x (-1) 4 && x (-1) 13).toNat = 0)
    (g20 : (x 0 4 && x 0 13).toNat = 0)
    (g21 : (x (-1) 5 && x (-1) 14).toNat = 0)
    (g22 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g23 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g24 : (x 0 2 && x 0 12).toNat = 0)
    (g25 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g26 : (x 0 4 && x 0 14).toNat = 0)
    (g27 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g28 : (x (-3) 3 && x (-3) 14).toNat = 0)
    (g29 : (x 0 1 && x 0 12).toNat = 0)
    (g30 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g31 : (x 0 3 && x 0 14).toNat = 0)
    (g32 : (x (-3) 1 && x (-3) 14).toNat = 0)
    (g33 : (x 0 1 && x 0 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d324 : (x 1 3 && x 1 14).toNat = 0 := by
    have r325 := hand1 (x 1 3) (x 1 14)
    have b326 := hb (x 1 3)
    have b327 := hb (x 1 3 && x 1 14)
    clear * - r325 b326 b327 g14
    omega
  have d328 : (x 1 3 && x 1 13).toNat = 0 := by
    have r329 := hand1 (x 1 3) (x 1 13)
    have b330 := hb (x 1 3)
    have b331 := hb (x 1 3 && x 1 13)
    clear * - r329 b330 b331 g14
    omega
  have d332 : (x 1 3 && x 1 12).toNat = 0 := by
    have r333 := hand1 (x 1 3) (x 1 12)
    have b334 := hb (x 1 3)
    have b335 := hb (x 1 3 && x 1 12)
    clear * - r333 b334 b335 g14
    omega
  have d336 : (x 1 11).toNat = 0 := by
    have r337 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
    have b338 := hb (x 1 3)
    have b339 := hb (x 1 11)
    clear * - r337 b338 b339 g14
    omega
  have d340 : (x 1 1 && x 1 11).toNat = 0 := by
    have r341 := hand2 (x 1 1) (x 1 11)
    have b342 := hb (x 1 11)
    have b343 := hb (x 1 1 && x 1 11)
    clear * - r341 b342 b343 d336
    omega
  have d344 : (x 1 2 && x 1 11).toNat = 0 := by
    have r345 := hand2 (x 1 2) (x 1 11)
    have b346 := hb (x 1 11)
    have b347 := hb (x 1 2 && x 1 11)
    clear * - r345 b346 b347 d336
    omega
  cases h348 : x 0 6
  · have f349 : (x 0 6).toNat = 0 := by rw [h348]; rfl
    cases h350 : x 1 1
    · have f351 : (x 1 1).toNat = 0 := by rw [h350]; rfl
      have d352 : (x 1 13).toNat = 0 := by
        have r353 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
        have b354 := hb (x 1 1)
        have b355 := hb (x 1 13)
        clear * - r353 b354 b355 f351
        omega
      have d356 : (x (-1) 2).toNat = 1 := by
        have r357 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := hcov13 1
        have b358 := hb (x (-1) 2)
        have b359 := hb (x 1 13)
        have b360 := hb (x 0 1 && x 0 14)
        clear * - r357 b358 b359 b360 d352 g33
        omega
      have d361 : (x (-1) 14).toNat = 1 := by
        have r362 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
        have b363 := hb (x (-1) 2)
        have b364 := hb (x (-1) 14)
        clear * - r362 b363 b364 d356
        omega
      have d365 : (x (-2) 1).toNat = 0 := by
        have r366 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := hd14 (-1)
        have b367 := hb (x (-2) 1)
        have b368 := hb (x (-1) 14)
        clear * - r366 b367 b368 d361
        omega
      have d369 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
        have r370 := hand1 (x (-2) 1) (x (-2) 14)
        have b371 := hb (x (-2) 1)
        have b372 := hb (x (-2) 1 && x (-2) 14)
        clear * - r370 b371 b372 d365
        omega
      have d373 : (x (-3) 2).toNat = 1 := by
        have r374 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := hcov13 (-1)
        have b375 := hb (x (-3) 2)
        have b376 := hb (x (-1) 13)
        have b377 := hb (x (-2) 1 && x (-2) 14)
        clear * - r374 b375 b376 b377 g4 d369
        omega
      have d378 : (x (-3) 14).toNat = 1 := by
        have r379 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
        have b380 := hb (x (-3) 2)
        have b381 := hb (x (-3) 14)
        clear * - r379 b380 b381 d373
        omega
      have d382 : (x (-4) 1).toNat = 0 := by
        have r383 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := hd14 (-3)
        have b384 := hb (x (-4) 1)
        have b385 := hb (x (-3) 14)
        clear * - r383 b384 b385 d378
        omega
      have d386 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
        have r387 := hand1 (x (-4) 1) (x (-4) 14)
        have b388 := hb (x (-4) 1)
        have b389 := hb (x (-4) 1 && x (-4) 14)
        clear * - r387 b388 b389 d382
        omega
      have d390 : (x (-4) 13).toNat = 0 := by
        have r391 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
        have b392 := hb (x (-4) 1)
        have b393 := hb (x (-4) 13)
        clear * - r391 b392 b393 d382
        omega
      have d394 : (x (-5) 2).toNat = 1 := by
        have r395 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := hcov13 (-3)
        have b396 := hb (x (-5) 2)
        have b397 := hb (x (-3) 13)
        have b398 := hb (x (-4) 1 && x (-4) 14)
        clear * - r395 b396 b397 b398 g2 d386
        omega
      have d399 : (x 1 12).toNat = 0 := by
        have r400 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
        have e401 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e402 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b403 := hb (x (-2) 3)
        have b404 := hb (x (-1) 2)
        have b405 := hb (x 0 13)
        have b406 := hb (x 1 12)
        clear * - r400 e401 e402 b403 b404 b405 b406 g12 d356
        omega
      have d407 : (x (-2) 3).toNat = 0 := by
        have r408 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
        have e409 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e410 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b411 := hb (x (-2) 3)
        have b412 := hb (x (-1) 2)
        have b413 := hb (x 0 13)
        have b414 := hb (x 1 12)
        clear * - r408 e409 e410 b411 b412 b413 b414 d399 g12 d356
        omega
      have d415 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
        have r416 := hand1 (x (-2) 3) (x (-2) 14)
        have b417 := hb (x (-2) 3)
        have b418 := hb (x (-2) 3 && x (-2) 14)
        clear * - r416 b417 b418 d407
        omega
      have d419 : (x (-3) 12).toNat = 0 := by
        have r420 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := hd12 (-3)
        have e421 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
        have e422 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
        have b423 := hb (x (-6) 3)
        have b424 := hb (x (-5) 2)
        have b425 := hb (x (-4) 13)
        have b426 := hb (x (-3) 12)
        clear * - r420 e421 e422 b423 b424 b425 b426 d390 d394
        omega
      have d427 : (x (-3) 4).toNat = 0 := by
        have r428 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
        have b429 := hb (x (-3) 4)
        have b430 := hb (x (-3) 12)
        clear * - r428 b429 b430 d419
        omega
      have r431 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := hcov11 1
      have b432 := hb (x (-3) 4)
      have b433 := hb (x 1 11)
      have b434 := hb (x 0 1 && x 0 12)
      have b435 := hb (x (-1) 2 && x (-1) 13)
      have b436 := hb (x (-2) 3 && x (-2) 14)
      linarith only [r431, b432, b433, b434, b435, b436, d336, g29, g30, d415, d427]
    · have f437 : (x 1 1).toNat = 1 := by rw [h350]; rfl
      have d438 : (x 2 14).toNat = 0 := by
        have r439 : (x 2 14).toNat + (x 1 1).toNat = 1 := hd14 2
        have b440 := hb (x 1 1)
        have b441 := hb (x 2 14)
        clear * - r439 b440 b441 f437
        omega
      have d442 : (x 2 1 && x 2 14).toNat = 0 := by
        have r443 := hand2 (x 2 1) (x 2 14)
        have b444 := hb (x 2 14)
        have b445 := hb (x 2 1 && x 2 14)
        clear * - r443 b444 b445 d438
        omega
      have d446 : (x 2 6).toNat = 0 := by
        have r447 : (x 2 6).toNat ≤ (x 2 14).toNat := himp _ _ (hp6 2)
        have b448 := hb (x 2 6)
        have b449 := hb (x 2 14)
        clear * - r447 b448 b449 d438
        omega
      have d450 : (x 2 2).toNat = 0 := by
        have r451 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
        have b452 := hb (x 2 2)
        have b453 := hb (x 2 14)
        clear * - r451 b452 b453 d438
        omega
      have d454 : (x 2 2 && x 2 13).toNat = 0 := by
        have r455 := hand1 (x 2 2) (x 2 13)
        have b456 := hb (x 2 2)
        have b457 := hb (x 2 2 && x 2 13)
        clear * - r455 b456 b457 d450
        omega
      have d458 : (x 2 2 && x 2 12).toNat = 0 := by
        have r459 := hand1 (x 2 2) (x 2 12)
        have b460 := hb (x 2 2)
        have b461 := hb (x 2 2 && x 2 12)
        clear * - r459 b460 b461 d450
        omega
      have d462 : (x 2 2 && x 2 11).toNat = 0 := by
        have r463 := hand1 (x 2 2) (x 2 11)
        have b464 := hb (x 2 2)
        have b465 := hb (x 2 2 && x 2 11)
        clear * - r463 b464 b465 d450
        omega
      have d466 : (x 2 10).toNat = 0 := by
        have r467 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
        have b468 := hb (x 2 2)
        have b469 := hb (x 2 10)
        clear * - r467 b468 b469 d450
        omega
      have d470 : (x 2 1 && x 2 10).toNat = 0 := by
        have r471 := hand2 (x 2 1) (x 2 10)
        have b472 := hb (x 2 10)
        have b473 := hb (x 2 1 && x 2 10)
        clear * - r471 b472 b473 d466
        omega
      have d474 : (x (-2) 4 && x (-2) 14).toNat = 1 := by
        have r475 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := hcov10 2
        have b476 := hb (x (-3) 5)
        have b477 := hb (x 2 10)
        have b478 := hb (x 1 1 && x 1 11)
        have b479 := hb (x 0 2 && x 0 12)
        have b480 := hb (x (-1) 3 && x (-1) 13)
        have b481 := hb (x (-2) 4 && x (-2) 14)
        clear * - r475 b476 b477 b478 b479 b480 b481 d466 d340 g24 g25 g0
        omega
      have d482 : (x (-2) 4).toNat = 1 := by
        have r483 := hand1 (x (-2) 4) (x (-2) 14)
        have b484 := hb (x (-2) 4)
        have b485 := hb (x (-2) 4 && x (-2) 14)
        clear * - r483 b484 b485 d474
        omega
      have d486 : (x (-2) 12).toNat = 1 := by
        have r487 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
        have b488 := hb (x (-2) 4)
        have b489 := hb (x (-2) 12)
        clear * - r487 b488 b489 d482
        omega
      have d490 : (x (-4) 2).toNat = 0 := by
        have r491 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := hd12 (-2)
        have e492 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e493 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have b494 := hb (x (-5) 3)
        have b495 := hb (x (-4) 2)
        have b496 := hb (x (-3) 13)
        have b497 := hb (x (-2) 12)
        clear * - r491 e492 e493 b494 b495 b496 b497 d486 g2
        omega
      have d498 : (x (-4) 10).toNat = 0 := by
        have r499 : (x (-4) 10).toNat ≤ (x (-4) 2).toNat := himp _ _ (hp10 (-4))
        have b500 := hb (x (-4) 2)
        have b501 := hb (x (-4) 10)
        clear * - r499 b500 b501 d490
        omega
      have d502 : (x (-2) 13).toNat = 1 := by
        have r503 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := hcov13 (-2)
        have b504 := hb (x (-4) 2)
        have b505 := hb (x (-2) 13)
        have b506 := hb (x (-3) 1 && x (-3) 14)
        clear * - r503 b504 b505 b506 g32 d490
        omega
      have d507 : (x (-2) 1).toNat = 1 := by
        have r508 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
        have b509 := hb (x (-2) 1)
        have b510 := hb (x (-2) 13)
        clear * - r508 b509 b510 d502
        omega
      have d511 : (x (-1) 14).toNat = 0 := by
        have r512 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := hd14 (-1)
        have b513 := hb (x (-2) 1)
        have b514 := hb (x (-1) 14)
        clear * - r512 b513 b514 d507
        omega
      have d515 : (x (-1) 6).toNat = 0 := by
        have r516 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
        have b517 := hb (x (-1) 6)
        have b518 := hb (x (-1) 14)
        clear * - r516 b517 b518 d511
        omega
      have d519 : (x (-1) 3 && x (-1) 6).toNat = 0 := by
        have r520 := hand2 (x (-1) 3) (x (-1) 6)
        have b521 := hb (x (-1) 6)
        have b522 := hb (x (-1) 3 && x (-1) 6)
        clear * - r520 b521 b522 d515
        omega
      have d523 : (x (-1) 2).toNat = 0 := by
        have r524 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
        have b525 := hb (x (-1) 2)
        have b526 := hb (x (-1) 14)
        clear * - r524 b525 b526 d511
        omega
      have d527 : (x 1 13).toNat = 1 := by
        have r528 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := hcov13 1
        have b529 := hb (x (-1) 2)
        have b530 := hb (x 1 13)
        have b531 := hb (x 0 1 && x 0 14)
        clear * - r528 b529 b530 b531 g33 d523
        omega
      have d532 : (x 2 12).toNat = 0 := by
        have r533 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := hd12 2
        have e534 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
        have e535 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
        have b536 := hb (x (-1) 3)
        have b537 := hb (x 0 2)
        have b538 := hb (x 1 13)
        have b539 := hb (x 2 12)
        clear * - r533 e534 e535 b536 b537 b538 b539 d527 g5
        omega
      have d540 : (x 2 1 && x 2 12).toNat = 0 := by
        have r541 := hand2 (x 2 1) (x 2 12)
        have b542 := hb (x 2 12)
        have b543 := hb (x 2 1 && x 2 12)
        clear * - r541 b542 b543 d532
        omega
      have d544 : (x 2 4).toNat = 0 := by
        have r545 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
        have b546 := hb (x 2 4)
        have b547 := hb (x 2 12)
        clear * - r545 b546 b547 d532
        omega
      have d548 : (x (-1) 3).toNat = 0 := by
        have r549 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := hd12 2
        have e550 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
        have e551 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
        have b552 := hb (x (-1) 3)
        have b553 := hb (x 0 2)
        have b554 := hb (x 1 13)
        have b555 := hb (x 2 12)
        clear * - r549 e550 e551 b552 b553 b554 b555 d532 d527 g5
        omega
      have d556 : (x (-1) 11).toNat = 0 := by
        have r557 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
        have b558 := hb (x (-1) 3)
        have b559 := hb (x (-1) 11)
        clear * - r557 b558 b559 d548
        omega
      have d560 : (x (-1) 12).toNat = 0 := by
        have r561 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
        have e562 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e563 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b564 := hb (x (-4) 3)
        have b565 := hb (x (-3) 2)
        have b566 := hb (x (-2) 13)
        have b567 := hb (x (-1) 12)
        clear * - r561 e562 e563 b564 b565 b566 b567 d502
        omega
      have d568 : (x (-1) 4).toNat = 0 := by
        have r569 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
        have b570 := hb (x (-1) 4)
        have b571 := hb (x (-1) 12)
        clear * - r569 b570 b571 d560
        omega
      have d572 : (x (-3) 2).toNat = 0 := by
        have r573 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
        have e574 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e575 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b576 := hb (x (-4) 3)
        have b577 := hb (x (-3) 2)
        have b578 := hb (x (-2) 13)
        have b579 := hb (x (-1) 12)
        clear * - r573 e574 e575 b576 b577 b578 b579 d560 d502
        omega
      have d580 : (x (-3) 10).toNat = 0 := by
        have r581 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
        have b582 := hb (x (-3) 2)
        have b583 := hb (x (-3) 10)
        clear * - r581 b582 b583 d572
        omega
      have d584 : (x (-4) 3).toNat = 0 := by
        have r585 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
        have e586 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e587 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b588 := hb (x (-4) 3)
        have b589 := hb (x (-3) 2)
        have b590 := hb (x (-2) 13)
        have b591 := hb (x (-1) 12)
        clear * - r585 e586 e587 b588 b589 b590 b591 d560 d502 d572
        omega
      have d592 : (x (-4) 11).toNat = 0 := by
        have r593 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
        have b594 := hb (x (-4) 3)
        have b595 := hb (x (-4) 11)
        clear * - r593 b594 b595 d584
        omega
      have d596 : (x (-4) 1 && x (-4) 11).toNat = 0 := by
        have r597 := hand2 (x (-4) 1) (x (-4) 11)
        have b598 := hb (x (-4) 11)
        have b599 := hb (x (-4) 1 && x (-4) 11)
        clear * - r597 b598 b599 d592
        omega
      have d600 : (x (-5) 3).toNat = 0 := by
        have r601 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := hd12 (-2)
        have e602 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e603 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have b604 := hb (x (-5) 3)
        have b605 := hb (x (-4) 2)
        have b606 := hb (x (-3) 13)
        have b607 := hb (x (-2) 12)
        clear * - r601 e602 e603 b604 b605 b606 b607 d486 g2 d490
        omega
      have d608 : (x (-5) 11).toNat = 0 := by
        have r609 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
        have b610 := hb (x (-5) 3)
        have b611 := hb (x (-5) 11)
        clear * - r609 b610 b611 d600
        omega
      have d612 : (x (-5) 1 && x (-5) 11).toNat = 0 := by
        have r613 := hand2 (x (-5) 1) (x (-5) 11)
        have b614 := hb (x (-5) 11)
        have b615 := hb (x (-5) 1 && x (-5) 11)
        clear * - r613 b614 b615 d608
        omega
      have d616 : (x 2 8).toNat = 0 := by
        have r617 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := hd8 2
        have e618 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e619 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e620 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e621 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e622 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e623 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b624 := hb (x (-5) 7)
        have b625 := hb (x (-4) 6)
        have b626 := hb (x (-3) 5)
        have b627 := hb (x (-2) 4)
        have b628 := hb (x (-1) 11)
        have b629 := hb (x 0 10)
        have b630 := hb (x 1 9)
        have b631 := hb (x 2 8)
        clear * - r617 e618 e619 e620 e621 e622 e623 b624 b625 b626 b627 b628 b629 b630 b631 g10 d556 d482 g0
        omega
      have d632 : (x 2 8 && x 2 13).toNat = 0 := by
        have r633 := hand1 (x 2 8) (x 2 13)
        have b634 := hb (x 2 8)
        have b635 := hb (x 2 8 && x 2 13)
        clear * - r633 b634 b635 d616
        omega
      have d636 : (x 1 9).toNat = 0 := by
        have r637 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := hd8 2
        have e638 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e639 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e640 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e641 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e642 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e643 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b644 := hb (x (-5) 7)
        have b645 := hb (x (-4) 6)
        have b646 := hb (x (-3) 5)
        have b647 := hb (x (-2) 4)
        have b648 := hb (x (-1) 11)
        have b649 := hb (x 0 10)
        have b650 := hb (x 1 9)
        have b651 := hb (x 2 8)
        clear * - r637 e638 e639 e640 e641 e642 e643 b644 b645 b646 b647 b648 b649 b650 b651 d616 g10 d556 d482 g0
        omega
      have d652 : (x 1 9 && x 1 14).toNat = 0 := by
        have r653 := hand1 (x 1 9) (x 1 14)
        have b654 := hb (x 1 9)
        have b655 := hb (x 1 9 && x 1 14)
        clear * - r653 b654 b655 d636
        omega
      have d656 : (x (-4) 6).toNat = 0 := by
        have r657 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := hd8 2
        have e658 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e659 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e660 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e661 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e662 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e663 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b664 := hb (x (-5) 7)
        have b665 := hb (x (-4) 6)
        have b666 := hb (x (-3) 5)
        have b667 := hb (x (-2) 4)
        have b668 := hb (x (-1) 11)
        have b669 := hb (x 0 10)
        have b670 := hb (x 1 9)
        have b671 := hb (x 2 8)
        clear * - r657 e658 e659 e660 e661 e662 e663 b664 b665 b666 b667 b668 b669 b670 b671 d616 d636 g10 d556 d482 g0
        omega
      have d672 : (x (-4) 6 && x (-4) 9).toNat = 0 := by
        have r673 := hand1 (x (-4) 6) (x (-4) 9)
        have b674 := hb (x (-4) 6)
        have b675 := hb (x (-4) 6 && x (-4) 9)
        clear * - r673 b674 b675 d656
        omega
      have d676 : (x (-5) 7).toNat = 0 := by
        have r677 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := hd8 2
        have e678 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e679 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e680 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e681 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e682 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e683 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b684 := hb (x (-5) 7)
        have b685 := hb (x (-4) 6)
        have b686 := hb (x (-3) 5)
        have b687 := hb (x (-2) 4)
        have b688 := hb (x (-1) 11)
        have b689 := hb (x 0 10)
        have b690 := hb (x 1 9)
        have b691 := hb (x 2 8)
        clear * - r677 e678 e679 e680 e681 e682 e683 b684 b685 b686 b687 b688 b689 b690 b691 d616 d636 g10 d556 d482 g0 d656
        omega
      have d692 : (x (-5) 7 && x (-5) 10).toNat = 0 := by
        have r693 := hand1 (x (-5) 7) (x (-5) 10)
        have b694 := hb (x (-5) 7)
        have b695 := hb (x (-5) 7 && x (-5) 10)
        clear * - r693 b694 b695 d676
        omega
      cases h696 : x 1 2
      · have f697 : (x 1 2).toNat = 0 := by rw [h696]; rfl
        have d698 : (x 1 2 && x 1 13).toNat = 0 := by
          have r699 := hand1 (x 1 2) (x 1 13)
          have b700 := hb (x 1 2)
          have b701 := hb (x 1 2 && x 1 13)
          clear * - r699 b700 b701 f697
          omega
        have d702 : (x 3 13).toNat = 1 := by
          have r703 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := hcov13 3
          have b704 := hb (x 1 2)
          have b705 := hb (x 3 13)
          have b706 := hb (x 2 1 && x 2 14)
          clear * - r703 b704 b705 b706 d442 f697
          omega
        have d707 : (x 3 1).toNat = 1 := by
          have r708 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
          have b709 := hb (x 3 1)
          have b710 := hb (x 3 13)
          clear * - r708 b709 b710 d702
          omega
        have d711 : (x 4 14).toNat = 0 := by
          have r712 : (x 4 14).toNat + (x 3 1).toNat = 1 := hd14 4
          have b713 := hb (x 3 1)
          have b714 := hb (x 4 14)
          clear * - r712 b713 b714 d707
          omega
        have d715 : (x 4 1 && x 4 14).toNat = 0 := by
          have r716 := hand2 (x 4 1) (x 4 14)
          have b717 := hb (x 4 14)
          have b718 := hb (x 4 1 && x 4 14)
          clear * - r716 b717 b718 d711
          omega
        have d719 : (x 4 4 && x 4 14).toNat = 0 := by
          have r720 := hand2 (x 4 4) (x 4 14)
          have b721 := hb (x 4 14)
          have b722 := hb (x 4 4 && x 4 14)
          clear * - r720 b721 b722 d711
          omega
        have d723 : (x 4 5 && x 4 14).toNat = 0 := by
          have r724 := hand2 (x 4 5) (x 4 14)
          have b725 := hb (x 4 14)
          have b726 := hb (x 4 5 && x 4 14)
          clear * - r724 b725 b726 d711
          omega
        have d727 : (x 4 6).toNat = 0 := by
          have r728 : (x 4 6).toNat ≤ (x 4 14).toNat := himp _ _ (hp6 4)
          have b729 := hb (x 4 6)
          have b730 := hb (x 4 14)
          clear * - r728 b729 b730 d711
          omega
        have d731 : (x 4 6 && x 4 11).toNat = 0 := by
          have r732 := hand1 (x 4 6) (x 4 11)
          have b733 := hb (x 4 6)
          have b734 := hb (x 4 6 && x 4 11)
          clear * - r732 b733 b734 d727
          omega
        have d735 : (x 4 2).toNat = 0 := by
          have r736 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
          have b737 := hb (x 4 2)
          have b738 := hb (x 4 14)
          clear * - r736 b737 b738 d711
          omega
        have d739 : (x 4 10).toNat = 0 := by
          have r740 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
          have b741 := hb (x 4 2)
          have b742 := hb (x 4 10)
          clear * - r740 b741 b742 d735
          omega
        have d743 : (x 4 12).toNat = 0 := by
          have r744 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
          have e745 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e746 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b747 := hb (x 1 3)
          have b748 := hb (x 2 2)
          have b749 := hb (x 3 13)
          have b750 := hb (x 4 12)
          clear * - r744 e745 e746 b747 b748 b749 b750 d702 d450 g14
          omega
        have d751 : (x 4 4).toNat = 0 := by
          have r752 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
          have b753 := hb (x 4 4)
          have b754 := hb (x 4 12)
          clear * - r752 b753 b754 d743
          omega
        have d755 : (x 3 11).toNat = 1 := by
          have r756 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := hcov11 3
          have b757 := hb (x (-1) 4)
          have b758 := hb (x 3 11)
          have b759 := hb (x 2 1 && x 2 12)
          have b760 := hb (x 1 2 && x 1 13)
          have b761 := hb (x 0 3 && x 0 14)
          clear * - r756 b757 b758 b759 b760 b761 d540 d698 g31 d568
          omega
        have d762 : (x 3 3).toNat = 1 := by
          have r763 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
          have b764 := hb (x 3 3)
          have b765 := hb (x 3 11)
          clear * - r763 b764 b765 d755
          omega
        have d766 : (x 6 12).toNat = 0 := by
          have r767 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
          have e768 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e769 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b770 := hb (x 3 3)
          have b771 := hb (x 4 2)
          have b772 := hb (x 5 13)
          have b773 := hb (x 6 12)
          clear * - r767 e768 e769 b770 b771 b772 b773 d735 d762
          omega
        have d774 : (x 6 2 && x 6 12).toNat = 0 := by
          have r775 := hand2 (x 6 2) (x 6 12)
          have b776 := hb (x 6 12)
          have b777 := hb (x 6 2 && x 6 12)
          clear * - r775 b776 b777 d766
          omega
        have d778 : (x 6 3 && x 6 12).toNat = 0 := by
          have r779 := hand2 (x 6 3) (x 6 12)
          have b780 := hb (x 6 12)
          have b781 := hb (x 6 3 && x 6 12)
          clear * - r779 b780 b781 d766
          omega
        have d782 : (x 6 4).toNat = 0 := by
          have r783 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
          have b784 := hb (x 6 4)
          have b785 := hb (x 6 12)
          clear * - r783 b784 b785 d766
          omega
        have d786 : (x 6 4 && x 6 9).toNat = 0 := by
          have r787 := hand1 (x 6 4) (x 6 9)
          have b788 := hb (x 6 4)
          have b789 := hb (x 6 4 && x 6 9)
          clear * - r787 b788 b789 d782
          omega
        have d790 : (x 5 13).toNat = 0 := by
          have r791 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
          have e792 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e793 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b794 := hb (x 3 3)
          have b795 := hb (x 4 2)
          have b796 := hb (x 5 13)
          have b797 := hb (x 6 12)
          clear * - r791 e792 e793 b794 b795 b796 b797 d766 d735 d762
          omega
        have d798 : (x 5 3 && x 5 13).toNat = 0 := by
          have r799 := hand2 (x 5 3) (x 5 13)
          have b800 := hb (x 5 13)
          have b801 := hb (x 5 3 && x 5 13)
          clear * - r799 b800 b801 d790
          omega
        have d802 : (x 5 4 && x 5 13).toNat = 0 := by
          have r803 := hand2 (x 5 4) (x 5 13)
          have b804 := hb (x 5 13)
          have b805 := hb (x 5 4 && x 5 13)
          clear * - r803 b804 b805 d790
          omega
        have d806 : (x 5 5).toNat = 0 := by
          have r807 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
          have b808 := hb (x 5 5)
          have b809 := hb (x 5 13)
          clear * - r807 b808 b809 d790
          omega
        have d810 : (x 5 5 && x 5 10).toNat = 0 := by
          have r811 := hand1 (x 5 5) (x 5 10)
          have b812 := hb (x 5 5)
          have b813 := hb (x 5 5 && x 5 10)
          clear * - r811 b812 b813 d806
          omega
        have d814 : (x 3 2).toNat = 1 := by
          have r815 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := hcov13 5
          have b816 := hb (x 3 2)
          have b817 := hb (x 5 13)
          have b818 := hb (x 4 1 && x 4 14)
          clear * - r815 b816 b817 b818 d790 d715
          omega
        have d819 : (x 3 14).toNat = 1 := by
          have r820 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
          have b821 := hb (x 3 2)
          have b822 := hb (x 3 14)
          clear * - r820 b821 b822 d814
          omega
        have d823 : (x 2 1).toNat = 0 := by
          have r824 : (x 3 14).toNat + (x 2 1).toNat = 1 := hd14 3
          have b825 := hb (x 2 1)
          have b826 := hb (x 3 14)
          clear * - r824 b825 b826 d819
          omega
        have d827 : (x 2 13).toNat = 0 := by
          have r828 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
          have b829 := hb (x 2 1)
          have b830 := hb (x 2 13)
          clear * - r828 b829 b830 d823
          omega
        have d831 : (x 3 12).toNat = 1 := by
          have r832 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := hd12 3
          have e833 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
          have e834 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
          have b835 := hb (x 0 3)
          have b836 := hb (x 1 2)
          have b837 := hb (x 2 13)
          have b838 := hb (x 3 12)
          clear * - r832 e833 e834 b835 b836 b837 b838 d827 f697 g6
          omega
        have d839 : (x 5 12).toNat = 0 := by
          have r840 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
          have e841 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e842 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b843 := hb (x 2 3)
          have b844 := hb (x 3 2)
          have b845 := hb (x 4 13)
          have b846 := hb (x 5 12)
          clear * - r840 e841 e842 b843 b844 b845 b846 d814
          omega
        have d847 : (x 5 4).toNat = 0 := by
          have r848 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
          have b849 := hb (x 5 4)
          have b850 := hb (x 5 12)
          clear * - r848 b849 b850 d839
          omega
        have d851 : (x 4 13).toNat = 0 := by
          have r852 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
          have e853 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e854 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b855 := hb (x 2 3)
          have b856 := hb (x 3 2)
          have b857 := hb (x 4 13)
          have b858 := hb (x 5 12)
          clear * - r852 e853 e854 b855 b856 b857 b858 d839 d814
          omega
        have d859 : (x 4 5).toNat = 0 := by
          have r860 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
          have b861 := hb (x 4 5)
          have b862 := hb (x 4 13)
          clear * - r860 b861 b862 d851
          omega
        have d863 : (x 6 8).toNat = 0 := by
          have r864 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
          have e865 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
          have e866 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
          have e867 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
          have e868 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
          have e869 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
          have e870 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
          have b871 := hb (x (-1) 7)
          have b872 := hb (x 0 6)
          have b873 := hb (x 1 5)
          have b874 := hb (x 2 4)
          have b875 := hb (x 3 11)
          have b876 := hb (x 4 10)
          have b877 := hb (x 5 9)
          have b878 := hb (x 6 8)
          clear * - r864 e865 e866 e867 e868 e869 e870 b871 b872 b873 b874 b875 b876 b877 b878 d739 d755 d544 f349
          omega
        have d879 : (x 5 9).toNat = 0 := by
          have r880 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
          have e881 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
          have e882 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
          have e883 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
          have e884 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
          have e885 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
          have e886 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
          have b887 := hb (x (-1) 7)
          have b888 := hb (x 0 6)
          have b889 := hb (x 1 5)
          have b890 := hb (x 2 4)
          have b891 := hb (x 3 11)
          have b892 := hb (x 4 10)
          have b893 := hb (x 5 9)
          have b894 := hb (x 6 8)
          clear * - r880 e881 e882 e883 e884 e885 e886 b887 b888 b889 b890 b891 b892 b893 b894 d863 d739 d755 d544 f349
          omega
        have d895 : (x 13 1).toNat = 0 := by
          have r896 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := hcount 14
          have b897 := hb (x 0 14)
          have b898 := hb (x 1 13)
          have b899 := hb (x 2 12)
          have b900 := hb (x 3 11)
          have b901 := hb (x 4 10)
          have b902 := hb (x 5 9)
          have b903 := hb (x 6 8)
          have b904 := hb (x 7 7)
          have b905 := hb (x 8 6)
          have b906 := hb (x 9 5)
          have b907 := hb (x 10 4)
          have b908 := hb (x 11 3)
          have b909 := hb (x 12 2)
          have b910 := hb (x 13 1)
          clear * - r896 b897 b898 b899 b900 b901 b902 b903 b904 b905 b906 b907 b908 b909 b910 d863 d879 d739 d755 d532 d527 g13
          omega
        have d911 : (x 13 1 && x 13 14).toNat = 0 := by
          have r912 := hand1 (x 13 1) (x 13 14)
          have b913 := hb (x 13 1)
          have b914 := hb (x 13 1 && x 13 14)
          clear * - r912 b913 b914 d895
          omega
        have d915 : (x 13 1 && x 13 11).toNat = 0 := by
          have r916 := hand1 (x 13 1) (x 13 11)
          have b917 := hb (x 13 1)
          have b918 := hb (x 13 1 && x 13 11)
          clear * - r916 b917 b918 d895
          omega
        have d919 : (x 13 13).toNat = 0 := by
          have r920 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
          have b921 := hb (x 13 1)
          have b922 := hb (x 13 13)
          clear * - r920 b921 b922 d895
          omega
        have d923 : (x 13 5).toNat = 0 := by
          have r924 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
          have b925 := hb (x 13 5)
          have b926 := hb (x 13 13)
          clear * - r924 b925 b926 d919
          omega
        have d927 : (x 13 9).toNat = 0 := by
          have r928 : (x 13 9).toNat ≤ (x 13 1).toNat := himp _ _ (hp9 13)
          have b929 := hb (x 13 1)
          have b930 := hb (x 13 9)
          clear * - r928 b929 b930 d895
          omega
        have d931 : (x 13 2 && x 13 9).toNat = 0 := by
          have r932 := hand2 (x 13 2) (x 13 9)
          have b933 := hb (x 13 9)
          have b934 := hb (x 13 2 && x 13 9)
          clear * - r932 b933 b934 d927
          omega
        have d935 : (x 12 2).toNat = 0 := by
          have r936 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := hcount 14
          have b937 := hb (x 0 14)
          have b938 := hb (x 1 13)
          have b939 := hb (x 2 12)
          have b940 := hb (x 3 11)
          have b941 := hb (x 4 10)
          have b942 := hb (x 5 9)
          have b943 := hb (x 6 8)
          have b944 := hb (x 7 7)
          have b945 := hb (x 8 6)
          have b946 := hb (x 9 5)
          have b947 := hb (x 10 4)
          have b948 := hb (x 11 3)
          have b949 := hb (x 12 2)
          have b950 := hb (x 13 1)
          clear * - r936 b937 b938 b939 b940 b941 b942 b943 b944 b945 b946 b947 b948 b949 b950 d895 d863 d879 d739 d755 d532 d527 g13
          omega
        have d951 : (x 12 2 && x 12 12).toNat = 0 := by
          have r952 := hand1 (x 12 2) (x 12 12)
          have b953 := hb (x 12 2)
          have b954 := hb (x 12 2 && x 12 12)
          clear * - r952 b953 b954 d935
          omega
        have d955 : (x 12 10).toNat = 0 := by
          have r956 : (x 12 10).toNat ≤ (x 12 2).toNat := himp _ _ (hp10 12)
          have b957 := hb (x 12 2)
          have b958 := hb (x 12 10)
          clear * - r956 b957 b958 d935
          omega
        have d959 : (x 12 3 && x 12 10).toNat = 0 := by
          have r960 := hand2 (x 12 3) (x 12 10)
          have b961 := hb (x 12 10)
          have b962 := hb (x 12 3 && x 12 10)
          clear * - r960 b961 b962 d955
          omega
        have d963 : (x 14 13).toNat = 1 := by
          have r964 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
          have b965 := hb (x 12 2)
          have b966 := hb (x 14 13)
          have b967 := hb (x 13 1 && x 13 14)
          clear * - r964 b965 b966 b967 d911 d935
          omega
        have d968 : (x 14 1).toNat = 1 := by
          have r969 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
          have b970 := hb (x 14 1)
          have b971 := hb (x 14 13)
          clear * - r969 b970 b971 d963
          omega
        have d972 : (x 15 14).toNat = 0 := by
          have r973 : (x 15 14).toNat + (x 14 1).toNat = 1 := hd14 15
          have b974 := hb (x 14 1)
          have b975 := hb (x 15 14)
          clear * - r973 b974 b975 d968
          omega
        have d976 : (x 15 1 && x 15 14).toNat = 0 := by
          have r977 := hand2 (x 15 1) (x 15 14)
          have b978 := hb (x 15 14)
          have b979 := hb (x 15 1 && x 15 14)
          clear * - r977 b978 b979 d972
          omega
        have d980 : (x 15 4 && x 15 14).toNat = 0 := by
          have r981 := hand2 (x 15 4) (x 15 14)
          have b982 := hb (x 15 14)
          have b983 := hb (x 15 4 && x 15 14)
          clear * - r981 b982 b983 d972
          omega
        have d984 : (x 15 5 && x 15 14).toNat = 0 := by
          have r985 := hand2 (x 15 5) (x 15 14)
          have b986 := hb (x 15 14)
          have b987 := hb (x 15 5 && x 15 14)
          clear * - r985 b986 b987 d972
          omega
        have d988 : (x 15 6).toNat = 0 := by
          have r989 : (x 15 6).toNat ≤ (x 15 14).toNat := himp _ _ (hp6 15)
          have b990 := hb (x 15 6)
          have b991 := hb (x 15 14)
          clear * - r989 b990 b991 d972
          omega
        have d992 : (x 15 2 && x 15 6).toNat = 0 := by
          have r993 := hand2 (x 15 2) (x 15 6)
          have b994 := hb (x 15 6)
          have b995 := hb (x 15 2 && x 15 6)
          clear * - r993 b994 b995 d988
          omega
        have d996 : (x 15 2).toNat = 0 := by
          have r997 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
          have b998 := hb (x 15 2)
          have b999 := hb (x 15 14)
          clear * - r997 b998 b999 d972
          omega
        have d1000 : (x 15 10).toNat = 0 := by
          have r1001 : (x 15 10).toNat ≤ (x 15 2).toNat := himp _ _ (hp10 15)
          have b1002 := hb (x 15 2)
          have b1003 := hb (x 15 10)
          clear * - r1001 b1002 b1003 d996
          omega
        have d1004 : (x 13 2).toNat = 0 := by
          have r1005 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := hcount 15
          have b1006 := hb (x 1 14)
          have b1007 := hb (x 2 13)
          have b1008 := hb (x 3 12)
          have b1009 := hb (x 4 11)
          have b1010 := hb (x 5 10)
          have b1011 := hb (x 6 9)
          have b1012 := hb (x 7 8)
          have b1013 := hb (x 8 7)
          have b1014 := hb (x 9 6)
          have b1015 := hb (x 10 5)
          have b1016 := hb (x 11 4)
          have b1017 := hb (x 12 3)
          have b1018 := hb (x 13 2)
          have b1019 := hb (x 14 1)
          clear * - r1005 b1006 b1007 b1008 b1009 b1010 b1011 b1012 b1013 b1014 b1015 b1016 b1017 b1018 b1019 d968 d831 d827 g15
          omega
        have d1020 : (x 13 2 && x 13 12).toNat = 0 := by
          have r1021 := hand1 (x 13 2) (x 13 12)
          have b1022 := hb (x 13 2)
          have b1023 := hb (x 13 2 && x 13 12)
          clear * - r1021 b1022 b1023 d1004
          omega
        have d1024 : (x 12 3).toNat = 0 := by
          have r1025 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := hcount 15
          have b1026 := hb (x 1 14)
          have b1027 := hb (x 2 13)
          have b1028 := hb (x 3 12)
          have b1029 := hb (x 4 11)
          have b1030 := hb (x 5 10)
          have b1031 := hb (x 6 9)
          have b1032 := hb (x 7 8)
          have b1033 := hb (x 8 7)
          have b1034 := hb (x 9 6)
          have b1035 := hb (x 10 5)
          have b1036 := hb (x 11 4)
          have b1037 := hb (x 12 3)
          have b1038 := hb (x 13 2)
          have b1039 := hb (x 14 1)
          clear * - r1025 b1026 b1027 b1028 b1029 b1030 b1031 b1032 b1033 b1034 b1035 b1036 b1037 b1038 b1039 d968 d1004 d831 d827 g15
          omega
        have d1040 : (x 12 3 && x 12 13).toNat = 0 := by
          have r1041 := hand1 (x 12 3) (x 12 13)
          have b1042 := hb (x 12 3)
          have b1043 := hb (x 12 3 && x 12 13)
          clear * - r1041 b1042 b1043 d1024
          omega
        have d1044 : (x 11 4).toNat = 0 := by
          have r1045 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := hcount 15
          have b1046 := hb (x 1 14)
          have b1047 := hb (x 2 13)
          have b1048 := hb (x 3 12)
          have b1049 := hb (x 4 11)
          have b1050 := hb (x 5 10)
          have b1051 := hb (x 6 9)
          have b1052 := hb (x 7 8)
          have b1053 := hb (x 8 7)
          have b1054 := hb (x 9 6)
          have b1055 := hb (x 10 5)
          have b1056 := hb (x 11 4)
          have b1057 := hb (x 12 3)
          have b1058 := hb (x 13 2)
          have b1059 := hb (x 14 1)
          clear * - r1045 b1046 b1047 b1048 b1049 b1050 b1051 b1052 b1053 b1054 b1055 b1056 b1057 b1058 b1059 d968 d1004 d1024 d831 d827 g15
          omega
        have d1060 : (x 11 4 && x 11 14).toNat = 0 := by
          have r1061 := hand1 (x 11 4) (x 11 14)
          have b1062 := hb (x 11 4)
          have b1063 := hb (x 11 4 && x 11 14)
          clear * - r1061 b1062 b1063 d1044
          omega
        have d1064 : (x 11 4 && x 11 11).toNat = 0 := by
          have r1065 := hand1 (x 11 4) (x 11 11)
          have b1066 := hb (x 11 4)
          have b1067 := hb (x 11 4 && x 11 11)
          clear * - r1065 b1066 b1067 d1044
          omega
        have d1068 : (x 10 5).toNat = 0 := by
          have r1069 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := hcount 15
          have b1070 := hb (x 1 14)
          have b1071 := hb (x 2 13)
          have b1072 := hb (x 3 12)
          have b1073 := hb (x 4 11)
          have b1074 := hb (x 5 10)
          have b1075 := hb (x 6 9)
          have b1076 := hb (x 7 8)
          have b1077 := hb (x 8 7)
          have b1078 := hb (x 9 6)
          have b1079 := hb (x 10 5)
          have b1080 := hb (x 11 4)
          have b1081 := hb (x 12 3)
          have b1082 := hb (x 13 2)
          have b1083 := hb (x 14 1)
          clear * - r1069 b1070 b1071 b1072 b1073 b1074 b1075 b1076 b1077 b1078 b1079 b1080 b1081 b1082 b1083 d968 d1004 d1024 d1044 d831 d827 g15
          omega
        have d1084 : (x 10 5 && x 10 12).toNat = 0 := by
          have r1085 := hand1 (x 10 5) (x 10 12)
          have b1086 := hb (x 10 5)
          have b1087 := hb (x 10 5 && x 10 12)
          clear * - r1085 b1086 b1087 d1068
          omega
        have d1088 : (x 14 1 && x 14 11).toNat = 1 := by
          have r1089 : 1 ≤ (x 15 10).toNat + (x 14 1 && x 14 11).toNat + (x 13 2 && x 13 12).toNat + (x 12 3 && x 12 13).toNat + (x 11 4 && x 11 14).toNat + (x 10 5).toNat := hcov10 15
          have b1090 := hb (x 10 5)
          have b1091 := hb (x 15 10)
          have b1092 := hb (x 14 1 && x 14 11)
          have b1093 := hb (x 13 2 && x 13 12)
          have b1094 := hb (x 12 3 && x 12 13)
          have b1095 := hb (x 11 4 && x 11 14)
          clear * - r1089 b1090 b1091 b1092 b1093 b1094 b1095 d1000 d1020 d1040 d1060 d1068
          omega
        have d1096 : (x 14 11).toNat = 1 := by
          have r1097 := hand2 (x 14 1) (x 14 11)
          have b1098 := hb (x 14 11)
          have b1099 := hb (x 14 1 && x 14 11)
          clear * - r1097 b1098 b1099 d1088
          omega
        have d1100 : (x 14 3).toNat = 1 := by
          have r1101 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
          have b1102 := hb (x 14 3)
          have b1103 := hb (x 14 11)
          clear * - r1101 b1102 b1103 d1096
          omega
        have d1104 : (x 17 12).toNat = 0 := by
          have r1105 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
          have e1106 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
          have e1107 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
          have b1108 := hb (x 14 3)
          have b1109 := hb (x 15 2)
          have b1110 := hb (x 16 13)
          have b1111 := hb (x 17 12)
          clear * - r1105 e1106 e1107 b1108 b1109 b1110 b1111 d996 d1100
          omega
        have d1112 : (x 17 2 && x 17 12).toNat = 0 := by
          have r1113 := hand2 (x 17 2) (x 17 12)
          have b1114 := hb (x 17 12)
          have b1115 := hb (x 17 2 && x 17 12)
          clear * - r1113 b1114 b1115 d1104
          omega
        have d1116 : (x 17 3 && x 17 12).toNat = 0 := by
          have r1117 := hand2 (x 17 3) (x 17 12)
          have b1118 := hb (x 17 12)
          have b1119 := hb (x 17 3 && x 17 12)
          clear * - r1117 b1118 b1119 d1104
          omega
        have d1120 : (x 17 4).toNat = 0 := by
          have r1121 : (x 17 4).toNat ≤ (x 17 12).toNat := himp _ _ (hp4 17)
          have b1122 := hb (x 17 4)
          have b1123 := hb (x 17 12)
          clear * - r1121 b1122 b1123 d1104
          omega
        have d1124 : (x 17 4 && x 17 14).toNat = 0 := by
          have r1125 := hand1 (x 17 4) (x 17 14)
          have b1126 := hb (x 17 4)
          have b1127 := hb (x 17 4 && x 17 14)
          clear * - r1125 b1126 b1127 d1120
          omega
        have d1128 : (x 17 4 && x 17 13).toNat = 0 := by
          have r1129 := hand1 (x 17 4) (x 17 13)
          have b1130 := hb (x 17 4)
          have b1131 := hb (x 17 4 && x 17 13)
          clear * - r1129 b1130 b1131 d1120
          omega
        have d1132 : (x 16 13).toNat = 0 := by
          have r1133 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
          have e1134 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
          have e1135 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
          have b1136 := hb (x 14 3)
          have b1137 := hb (x 15 2)
          have b1138 := hb (x 16 13)
          have b1139 := hb (x 17 12)
          clear * - r1133 e1134 e1135 b1136 b1137 b1138 b1139 d1104 d996 d1100
          omega
        have d1140 : (x 16 3 && x 16 13).toNat = 0 := by
          have r1141 := hand2 (x 16 3) (x 16 13)
          have b1142 := hb (x 16 13)
          have b1143 := hb (x 16 3 && x 16 13)
          clear * - r1141 b1142 b1143 d1132
          omega
        have d1144 : (x 16 4 && x 16 13).toNat = 0 := by
          have r1145 := hand2 (x 16 4) (x 16 13)
          have b1146 := hb (x 16 13)
          have b1147 := hb (x 16 4 && x 16 13)
          clear * - r1145 b1146 b1147 d1132
          omega
        have d1148 : (x 16 5).toNat = 0 := by
          have r1149 : (x 16 5).toNat ≤ (x 16 13).toNat := himp _ _ (hp5 16)
          have b1150 := hb (x 16 5)
          have b1151 := hb (x 16 13)
          clear * - r1149 b1150 b1151 d1132
          omega
        have d1152 : (x 16 5 && x 16 14).toNat = 0 := by
          have r1153 := hand1 (x 16 5) (x 16 14)
          have b1154 := hb (x 16 5)
          have b1155 := hb (x 16 5 && x 16 14)
          clear * - r1153 b1154 b1155 d1148
          omega
        have d1156 : (x 14 2).toNat = 1 := by
          have r1157 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := hcov13 16
          have b1158 := hb (x 14 2)
          have b1159 := hb (x 16 13)
          have b1160 := hb (x 15 1 && x 15 14)
          clear * - r1157 b1158 b1159 b1160 d1132 d976
          omega
        have d1161 : (x 16 12).toNat = 0 := by
          have r1162 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
          have e1163 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
          have e1164 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
          have b1165 := hb (x 13 3)
          have b1166 := hb (x 14 2)
          have b1167 := hb (x 15 13)
          have b1168 := hb (x 16 12)
          clear * - r1162 e1163 e1164 b1165 b1166 b1167 b1168 d1156
          omega
        have d1169 : (x 16 2 && x 16 12).toNat = 0 := by
          have r1170 := hand2 (x 16 2) (x 16 12)
          have b1171 := hb (x 16 12)
          have b1172 := hb (x 16 2 && x 16 12)
          clear * - r1170 b1171 b1172 d1161
          omega
        have d1173 : (x 16 4).toNat = 0 := by
          have r1174 : (x 16 4).toNat ≤ (x 16 12).toNat := himp _ _ (hp4 16)
          have b1175 := hb (x 16 4)
          have b1176 := hb (x 16 12)
          clear * - r1174 b1175 b1176 d1161
          omega
        have d1177 : (x 15 13).toNat = 0 := by
          have r1178 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
          have e1179 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
          have e1180 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
          have b1181 := hb (x 13 3)
          have b1182 := hb (x 14 2)
          have b1183 := hb (x 15 13)
          have b1184 := hb (x 16 12)
          clear * - r1178 e1179 e1180 b1181 b1182 b1183 b1184 d1161 d1156
          omega
        have d1185 : (x 15 3 && x 15 13).toNat = 0 := by
          have r1186 := hand2 (x 15 3) (x 15 13)
          have b1187 := hb (x 15 13)
          have b1188 := hb (x 15 3 && x 15 13)
          clear * - r1186 b1187 b1188 d1177
          omega
        have d1189 : (x 15 5).toNat = 0 := by
          have r1190 : (x 15 5).toNat ≤ (x 15 13).toNat := himp _ _ (hp5 15)
          have b1191 := hb (x 15 5)
          have b1192 := hb (x 15 13)
          clear * - r1190 b1191 b1192 d1177
          omega
        have d1193 : (x 13 3).toNat = 0 := by
          have r1194 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
          have e1195 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
          have e1196 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
          have b1197 := hb (x 13 3)
          have b1198 := hb (x 14 2)
          have b1199 := hb (x 15 13)
          have b1200 := hb (x 16 12)
          clear * - r1194 e1195 e1196 b1197 b1198 b1199 b1200 d1161 d1177 d1156
          omega
        have d1201 : (x 13 11).toNat = 0 := by
          have r1202 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
          have b1203 := hb (x 13 3)
          have b1204 := hb (x 13 11)
          clear * - r1202 b1203 b1204 d1193
          omega
        have d1205 : (x 17 8).toNat = 0 := by
          have r1206 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := hd8 17
          have e1207 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
          have e1208 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
          have e1209 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
          have e1210 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
          have e1211 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
          have e1212 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
          have b1213 := hb (x 10 7)
          have b1214 := hb (x 11 6)
          have b1215 := hb (x 12 5)
          have b1216 := hb (x 13 4)
          have b1217 := hb (x 14 11)
          have b1218 := hb (x 15 10)
          have b1219 := hb (x 16 9)
          have b1220 := hb (x 17 8)
          clear * - r1206 e1207 e1208 e1209 e1210 e1211 e1212 b1213 b1214 b1215 b1216 b1217 b1218 b1219 b1220 d1000 d1096
          omega
        have d1221 : (x 16 9).toNat = 0 := by
          have r1222 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := hd8 17
          have e1223 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
          have e1224 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
          have e1225 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
          have e1226 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
          have e1227 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
          have e1228 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
          have b1229 := hb (x 10 7)
          have b1230 := hb (x 11 6)
          have b1231 := hb (x 12 5)
          have b1232 := hb (x 13 4)
          have b1233 := hb (x 14 11)
          have b1234 := hb (x 15 10)
          have b1235 := hb (x 16 9)
          have b1236 := hb (x 17 8)
          clear * - r1222 e1223 e1224 e1225 e1226 e1227 e1228 b1229 b1230 b1231 b1232 b1233 b1234 b1235 b1236 d1205 d1000 d1096
          omega
        have d1237 : (x 13 4).toNat = 0 := by
          have r1238 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := hd8 17
          have e1239 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
          have e1240 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
          have e1241 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
          have e1242 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
          have e1243 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
          have e1244 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
          have b1245 := hb (x 10 7)
          have b1246 := hb (x 11 6)
          have b1247 := hb (x 12 5)
          have b1248 := hb (x 13 4)
          have b1249 := hb (x 14 11)
          have b1250 := hb (x 15 10)
          have b1251 := hb (x 16 9)
          have b1252 := hb (x 17 8)
          clear * - r1238 e1239 e1240 e1241 e1242 e1243 e1244 b1245 b1246 b1247 b1248 b1249 b1250 b1251 b1252 d1205 d1221 d1000 d1096
          omega
        have d1253 : (x 13 4 && x 13 8).toNat = 0 := by
          have r1254 := hand1 (x 13 4) (x 13 8)
          have b1255 := hb (x 13 4)
          have b1256 := hb (x 13 4 && x 13 8)
          clear * - r1254 b1255 b1256 d1237
          omega
        have d1257 : (x 12 5).toNat = 0 := by
          have r1258 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := hd8 17
          have e1259 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
          have e1260 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
          have e1261 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
          have e1262 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
          have e1263 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
          have e1264 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
          have b1265 := hb (x 10 7)
          have b1266 := hb (x 11 6)
          have b1267 := hb (x 12 5)
          have b1268 := hb (x 13 4)
          have b1269 := hb (x 14 11)
          have b1270 := hb (x 15 10)
          have b1271 := hb (x 16 9)
          have b1272 := hb (x 17 8)
          clear * - r1258 e1259 e1260 e1261 e1262 e1263 e1264 b1265 b1266 b1267 b1268 b1269 b1270 b1271 b1272 d1205 d1221 d1000 d1096 d1237
          omega
        have d1273 : (x 12 5 && x 12 9).toNat = 0 := by
          have r1274 := hand1 (x 12 5) (x 12 9)
          have b1275 := hb (x 12 5)
          have b1276 := hb (x 12 5 && x 12 9)
          clear * - r1274 b1275 b1276 d1257
          omega
        have d1277 : (x 11 6).toNat = 0 := by
          have r1278 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := hd8 17
          have e1279 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
          have e1280 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
          have e1281 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
          have e1282 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
          have e1283 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
          have e1284 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
          have b1285 := hb (x 10 7)
          have b1286 := hb (x 11 6)
          have b1287 := hb (x 12 5)
          have b1288 := hb (x 13 4)
          have b1289 := hb (x 14 11)
          have b1290 := hb (x 15 10)
          have b1291 := hb (x 16 9)
          have b1292 := hb (x 17 8)
          clear * - r1278 e1279 e1280 e1281 e1282 e1283 e1284 b1285 b1286 b1287 b1288 b1289 b1290 b1291 b1292 d1205 d1221 d1000 d1096 d1237 d1257
          omega
        have d1293 : (x 11 6 && x 11 10).toNat = 0 := by
          have r1294 := hand1 (x 11 6) (x 11 10)
          have b1295 := hb (x 11 6)
          have b1296 := hb (x 11 6 && x 11 10)
          clear * - r1294 b1295 b1296 d1277
          omega
        have d1297 : (x 10 7).toNat = 0 := by
          have r1298 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := hd8 17
          have e1299 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
          have e1300 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
          have e1301 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
          have e1302 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
          have e1303 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
          have e1304 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
          have b1305 := hb (x 10 7)
          have b1306 := hb (x 11 6)
          have b1307 := hb (x 12 5)
          have b1308 := hb (x 13 4)
          have b1309 := hb (x 14 11)
          have b1310 := hb (x 15 10)
          have b1311 := hb (x 16 9)
          have b1312 := hb (x 17 8)
          clear * - r1298 e1299 e1300 e1301 e1302 e1303 e1304 b1305 b1306 b1307 b1308 b1309 b1310 b1311 b1312 d1205 d1221 d1000 d1096 d1237 d1257 d1277
          omega
        have d1313 : (x 10 7 && x 10 11).toNat = 0 := by
          have r1314 := hand1 (x 10 7) (x 10 11)
          have b1315 := hb (x 10 7)
          have b1316 := hb (x 10 7 && x 10 11)
          clear * - r1314 b1315 b1316 d1297
          omega
        have d1317 : (x 9 6).toNat = 0 := by
          have r1318 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := hcount 15
          have b1319 := hb (x 1 14)
          have b1320 := hb (x 2 13)
          have b1321 := hb (x 3 12)
          have b1322 := hb (x 4 11)
          have b1323 := hb (x 5 10)
          have b1324 := hb (x 6 9)
          have b1325 := hb (x 7 8)
          have b1326 := hb (x 8 7)
          have b1327 := hb (x 9 6)
          have b1328 := hb (x 10 5)
          have b1329 := hb (x 11 4)
          have b1330 := hb (x 12 3)
          have b1331 := hb (x 13 2)
          have b1332 := hb (x 14 1)
          clear * - r1318 b1319 b1320 b1321 b1322 b1323 b1324 b1325 b1326 b1327 b1328 b1329 b1330 b1331 b1332 d968 d1004 d1024 d1044 d1068 d831 d827 g15
          omega
        have d1333 : (x 9 6 && x 9 13).toNat = 0 := by
          have r1334 := hand1 (x 9 6) (x 9 13)
          have b1335 := hb (x 9 6)
          have b1336 := hb (x 9 6 && x 9 13)
          clear * - r1334 b1335 b1336 d1317
          omega
        have d1337 : (x 9 1 && x 9 6).toNat = 0 := by
          have r1338 := hand2 (x 9 1) (x 9 6)
          have b1339 := hb (x 9 6)
          have b1340 := hb (x 9 1 && x 9 6)
          clear * - r1338 b1339 b1340 d1317
          omega
        have d1341 : (x 8 7).toNat = 0 := by
          have r1342 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := hcount 15
          have b1343 := hb (x 1 14)
          have b1344 := hb (x 2 13)
          have b1345 := hb (x 3 12)
          have b1346 := hb (x 4 11)
          have b1347 := hb (x 5 10)
          have b1348 := hb (x 6 9)
          have b1349 := hb (x 7 8)
          have b1350 := hb (x 8 7)
          have b1351 := hb (x 9 6)
          have b1352 := hb (x 10 5)
          have b1353 := hb (x 11 4)
          have b1354 := hb (x 12 3)
          have b1355 := hb (x 13 2)
          have b1356 := hb (x 14 1)
          clear * - r1342 b1343 b1344 b1345 b1346 b1347 b1348 b1349 b1350 b1351 b1352 b1353 b1354 b1355 b1356 d968 d1004 d1024 d1044 d1068 d1317 d831 d827 g15
          omega
        have d1357 : (x 8 7 && x 8 14).toNat = 0 := by
          have r1358 := hand1 (x 8 7) (x 8 14)
          have b1359 := hb (x 8 7)
          have b1360 := hb (x 8 7 && x 8 14)
          clear * - r1358 b1359 b1360 d1341
          omega
        have d1361 : (x 8 2 && x 8 7).toNat = 0 := by
          have r1362 := hand2 (x 8 2) (x 8 7)
          have b1363 := hb (x 8 7)
          have b1364 := hb (x 8 2 && x 8 7)
          clear * - r1362 b1363 b1364 d1341
          omega
        have d1365 : (x 7 8).toNat = 0 := by
          have r1366 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := hcount 15
          have b1367 := hb (x 1 14)
          have b1368 := hb (x 2 13)
          have b1369 := hb (x 3 12)
          have b1370 := hb (x 4 11)
          have b1371 := hb (x 5 10)
          have b1372 := hb (x 6 9)
          have b1373 := hb (x 7 8)
          have b1374 := hb (x 8 7)
          have b1375 := hb (x 9 6)
          have b1376 := hb (x 10 5)
          have b1377 := hb (x 11 4)
          have b1378 := hb (x 12 3)
          have b1379 := hb (x 13 2)
          have b1380 := hb (x 14 1)
          clear * - r1366 b1367 b1368 b1369 b1370 b1371 b1372 b1373 b1374 b1375 b1376 b1377 b1378 b1379 b1380 d968 d1004 d1024 d1044 d1068 d1317 d1341 d831 d827 g15
          omega
        have d1381 : (x 7 3 && x 7 8).toNat = 0 := by
          have r1382 := hand2 (x 7 3) (x 7 8)
          have b1383 := hb (x 7 8)
          have b1384 := hb (x 7 3 && x 7 8)
          clear * - r1382 b1383 b1384 d1365
          omega
        have d1385 : (x 3 7 && x 3 12).toNat = 1 := by
          have r1386 : 1 ≤ (x 10 5).toNat + (x 9 1 && x 9 6).toNat + (x 8 2 && x 8 7).toNat + (x 7 3 && x 7 8).toNat + (x 6 4 && x 6 9).toNat + (x 5 5 && x 5 10).toNat + (x 4 6 && x 4 11).toNat + (x 3 7 && x 3 12).toNat + (x 2 8 && x 2 13).toNat + (x 1 9 && x 1 14).toNat + (x 0 10).toNat := hcov5 10
          have b1387 := hb (x 0 10)
          have b1388 := hb (x 10 5)
          have b1389 := hb (x 9 1 && x 9 6)
          have b1390 := hb (x 8 2 && x 8 7)
          have b1391 := hb (x 7 3 && x 7 8)
          have b1392 := hb (x 6 4 && x 6 9)
          have b1393 := hb (x 5 5 && x 5 10)
          have b1394 := hb (x 4 6 && x 4 11)
          have b1395 := hb (x 3 7 && x 3 12)
          have b1396 := hb (x 2 8 && x 2 13)
          have b1397 := hb (x 1 9 && x 1 14)
          clear * - r1386 b1387 b1388 b1389 b1390 b1391 b1392 b1393 b1394 b1395 b1396 b1397 d1068 d1337 d1361 d1381 d786 d810 d731 d632 d652 g10
          omega
        have d1398 : (x 3 7).toNat = 1 := by
          have r1399 := hand1 (x 3 7) (x 3 12)
          have b1400 := hb (x 3 7)
          have b1401 := hb (x 3 7 && x 3 12)
          clear * - r1399 b1400 b1401 d1385
          omega
        have d1402 : (x 10 8).toNat = 0 := by
          have r1403 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := hd8 10
          have e1404 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
          have e1405 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
          have e1406 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
          have e1407 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
          have e1408 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
          have e1409 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
          have b1410 := hb (x 3 7)
          have b1411 := hb (x 4 6)
          have b1412 := hb (x 5 5)
          have b1413 := hb (x 6 4)
          have b1414 := hb (x 7 11)
          have b1415 := hb (x 8 10)
          have b1416 := hb (x 9 9)
          have b1417 := hb (x 10 8)
          clear * - r1403 e1404 e1405 e1406 e1407 e1408 e1409 b1410 b1411 b1412 b1413 b1414 b1415 b1416 b1417 d782 d806 d727 d1398
          omega
        have d1418 : (x 9 9).toNat = 0 := by
          have r1419 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := hd8 10
          have e1420 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
          have e1421 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
          have e1422 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
          have e1423 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
          have e1424 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
          have e1425 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
          have b1426 := hb (x 3 7)
          have b1427 := hb (x 4 6)
          have b1428 := hb (x 5 5)
          have b1429 := hb (x 6 4)
          have b1430 := hb (x 7 11)
          have b1431 := hb (x 8 10)
          have b1432 := hb (x 9 9)
          have b1433 := hb (x 10 8)
          clear * - r1419 e1420 e1421 e1422 e1423 e1424 e1425 b1426 b1427 b1428 b1429 b1430 b1431 b1432 b1433 d1402 d782 d806 d727 d1398
          omega
        have d1434 : (x 8 10).toNat = 0 := by
          have r1435 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := hd8 10
          have e1436 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
          have e1437 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
          have e1438 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
          have e1439 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
          have e1440 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
          have e1441 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
          have b1442 := hb (x 3 7)
          have b1443 := hb (x 4 6)
          have b1444 := hb (x 5 5)
          have b1445 := hb (x 6 4)
          have b1446 := hb (x 7 11)
          have b1447 := hb (x 8 10)
          have b1448 := hb (x 9 9)
          have b1449 := hb (x 10 8)
          clear * - r1435 e1436 e1437 e1438 e1439 e1440 e1441 b1442 b1443 b1444 b1445 b1446 b1447 b1448 b1449 d1402 d1418 d782 d806 d727 d1398
          omega
        have d1450 : (x 8 1 && x 8 10).toNat = 0 := by
          have r1451 := hand2 (x 8 1) (x 8 10)
          have b1452 := hb (x 8 10)
          have b1453 := hb (x 8 1 && x 8 10)
          clear * - r1451 b1452 b1453 d1434
          omega
        have d1454 : (x 7 11).toNat = 0 := by
          have r1455 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := hd8 10
          have e1456 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
          have e1457 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
          have e1458 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
          have e1459 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
          have e1460 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
          have e1461 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
          have b1462 := hb (x 3 7)
          have b1463 := hb (x 4 6)
          have b1464 := hb (x 5 5)
          have b1465 := hb (x 6 4)
          have b1466 := hb (x 7 11)
          have b1467 := hb (x 8 10)
          have b1468 := hb (x 9 9)
          have b1469 := hb (x 10 8)
          clear * - r1455 e1456 e1457 e1458 e1459 e1460 e1461 b1462 b1463 b1464 b1465 b1466 b1467 b1468 b1469 d1402 d1418 d1434 d782 d806 d727 d1398
          omega
        have d1470 : (x 7 1 && x 7 11).toNat = 0 := by
          have r1471 := hand2 (x 7 1) (x 7 11)
          have b1472 := hb (x 7 11)
          have b1473 := hb (x 7 1 && x 7 11)
          clear * - r1471 b1472 b1473 d1454
          omega
        have d1474 : (x 3 5).toNat = 1 := by
          have r1475 : 1 ≤ (x 8 10).toNat + (x 7 1 && x 7 11).toNat + (x 6 2 && x 6 12).toNat + (x 5 3 && x 5 13).toNat + (x 4 4 && x 4 14).toNat + (x 3 5).toNat := hcov10 8
          have b1476 := hb (x 3 5)
          have b1477 := hb (x 8 10)
          have b1478 := hb (x 7 1 && x 7 11)
          have b1479 := hb (x 6 2 && x 6 12)
          have b1480 := hb (x 5 3 && x 5 13)
          have b1481 := hb (x 4 4 && x 4 14)
          clear * - r1475 b1476 b1477 b1478 b1479 b1480 b1481 d1434 d1470 d774 d798 d719
          omega
        have d1482 : (x 8 8).toNat = 0 := by
          have r1483 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
          have e1484 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e1485 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e1486 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e1487 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e1488 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e1489 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have b1490 := hb (x 1 7)
          have b1491 := hb (x 2 6)
          have b1492 := hb (x 3 5)
          have b1493 := hb (x 4 4)
          have b1494 := hb (x 5 11)
          have b1495 := hb (x 6 10)
          have b1496 := hb (x 7 9)
          have b1497 := hb (x 8 8)
          clear * - r1483 e1484 e1485 e1486 e1487 e1488 e1489 b1490 b1491 b1492 b1493 b1494 b1495 b1496 b1497 d751 d1474 d446
          omega
        have d1498 : (x 7 9).toNat = 0 := by
          have r1499 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
          have e1500 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e1501 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e1502 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e1503 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e1504 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e1505 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have b1506 := hb (x 1 7)
          have b1507 := hb (x 2 6)
          have b1508 := hb (x 3 5)
          have b1509 := hb (x 4 4)
          have b1510 := hb (x 5 11)
          have b1511 := hb (x 6 10)
          have b1512 := hb (x 7 9)
          have b1513 := hb (x 8 8)
          clear * - r1499 e1500 e1501 e1502 e1503 e1504 e1505 b1506 b1507 b1508 b1509 b1510 b1511 b1512 b1513 d1482 d751 d1474 d446
          omega
        have d1514 : (x 6 10).toNat = 0 := by
          have r1515 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
          have e1516 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e1517 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e1518 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e1519 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e1520 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e1521 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have b1522 := hb (x 1 7)
          have b1523 := hb (x 2 6)
          have b1524 := hb (x 3 5)
          have b1525 := hb (x 4 4)
          have b1526 := hb (x 5 11)
          have b1527 := hb (x 6 10)
          have b1528 := hb (x 7 9)
          have b1529 := hb (x 8 8)
          clear * - r1515 e1516 e1517 e1518 e1519 e1520 e1521 b1522 b1523 b1524 b1525 b1526 b1527 b1528 b1529 d1482 d1498 d751 d1474 d446
          omega
        have d1530 : (x 5 11).toNat = 0 := by
          have r1531 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
          have e1532 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e1533 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e1534 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e1535 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e1536 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e1537 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have b1538 := hb (x 1 7)
          have b1539 := hb (x 2 6)
          have b1540 := hb (x 3 5)
          have b1541 := hb (x 4 4)
          have b1542 := hb (x 5 11)
          have b1543 := hb (x 6 10)
          have b1544 := hb (x 7 9)
          have b1545 := hb (x 8 8)
          clear * - r1531 e1532 e1533 e1534 e1535 e1536 e1537 b1538 b1539 b1540 b1541 b1542 b1543 b1544 b1545 d1482 d1498 d1514 d751 d1474 d446
          omega
        have d1546 : (x 7 2 && x 7 11).toNat = 0 := by
          have r1547 := hand2 (x 7 2) (x 7 11)
          have b1548 := hb (x 7 11)
          have b1549 := hb (x 7 2 && x 7 11)
          clear * - r1547 b1548 b1549 d1454
          omega
        have d1550 : (x 3 6).toNat = 1 := by
          have r1551 : 1 ≤ (x 9 9).toNat + (x 8 1 && x 8 10).toNat + (x 7 2 && x 7 11).toNat + (x 6 3 && x 6 12).toNat + (x 5 4 && x 5 13).toNat + (x 4 5 && x 4 14).toNat + (x 3 6).toNat := hcov9 9
          have b1552 := hb (x 3 6)
          have b1553 := hb (x 9 9)
          have b1554 := hb (x 8 1 && x 8 10)
          have b1555 := hb (x 7 2 && x 7 11)
          have b1556 := hb (x 6 3 && x 6 12)
          have b1557 := hb (x 5 4 && x 5 13)
          have b1558 := hb (x 4 5 && x 4 14)
          clear * - r1551 b1552 b1553 b1554 b1555 b1556 b1557 b1558 d1418 d1450 d1546 d778 d802 d723
          omega
        have d1559 : (x 9 8).toNat = 0 := by
          have r1560 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := hd8 9
          have e1561 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
          have e1562 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
          have e1563 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
          have e1564 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
          have e1565 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
          have e1566 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
          have b1567 := hb (x 2 7)
          have b1568 := hb (x 3 6)
          have b1569 := hb (x 4 5)
          have b1570 := hb (x 5 4)
          have b1571 := hb (x 6 11)
          have b1572 := hb (x 7 10)
          have b1573 := hb (x 8 9)
          have b1574 := hb (x 9 8)
          clear * - r1560 e1561 e1562 e1563 e1564 e1565 e1566 b1567 b1568 b1569 b1570 b1571 b1572 b1573 b1574 d847 d859 d1550
          omega
        have d1575 : (x 9 8 && x 9 12).toNat = 0 := by
          have r1576 := hand1 (x 9 8) (x 9 12)
          have b1577 := hb (x 9 8)
          have b1578 := hb (x 9 8 && x 9 12)
          clear * - r1576 b1577 b1578 d1559
          omega
        have d1579 : (x 8 9).toNat = 0 := by
          have r1580 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := hd8 9
          have e1581 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
          have e1582 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
          have e1583 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
          have e1584 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
          have e1585 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
          have e1586 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
          have b1587 := hb (x 2 7)
          have b1588 := hb (x 3 6)
          have b1589 := hb (x 4 5)
          have b1590 := hb (x 5 4)
          have b1591 := hb (x 6 11)
          have b1592 := hb (x 7 10)
          have b1593 := hb (x 8 9)
          have b1594 := hb (x 9 8)
          clear * - r1580 e1581 e1582 e1583 e1584 e1585 e1586 b1587 b1588 b1589 b1590 b1591 b1592 b1593 b1594 d1559 d847 d859 d1550
          omega
        have d1595 : (x 8 9 && x 8 13).toNat = 0 := by
          have r1596 := hand1 (x 8 9) (x 8 13)
          have b1597 := hb (x 8 9)
          have b1598 := hb (x 8 9 && x 8 13)
          clear * - r1596 b1597 b1598 d1579
          omega
        have d1599 : (x 7 10).toNat = 0 := by
          have r1600 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := hd8 9
          have e1601 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
          have e1602 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
          have e1603 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
          have e1604 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
          have e1605 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
          have e1606 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
          have b1607 := hb (x 2 7)
          have b1608 := hb (x 3 6)
          have b1609 := hb (x 4 5)
          have b1610 := hb (x 5 4)
          have b1611 := hb (x 6 11)
          have b1612 := hb (x 7 10)
          have b1613 := hb (x 8 9)
          have b1614 := hb (x 9 8)
          clear * - r1600 e1601 e1602 e1603 e1604 e1605 e1606 b1607 b1608 b1609 b1610 b1611 b1612 b1613 b1614 d1559 d1579 d847 d859 d1550
          omega
        have d1615 : (x 6 11).toNat = 0 := by
          have r1616 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := hd8 9
          have e1617 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
          have e1618 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
          have e1619 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
          have e1620 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
          have e1621 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
          have e1622 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
          have b1623 := hb (x 2 7)
          have b1624 := hb (x 3 6)
          have b1625 := hb (x 4 5)
          have b1626 := hb (x 5 4)
          have b1627 := hb (x 6 11)
          have b1628 := hb (x 7 10)
          have b1629 := hb (x 8 9)
          have b1630 := hb (x 9 8)
          clear * - r1616 e1617 e1618 e1619 e1620 e1621 e1622 b1623 b1624 b1625 b1626 b1627 b1628 b1629 b1630 d1559 d1579 d1599 d847 d859 d1550
          omega
        have d1631 : (x 14 3 && x 14 7).toNat = 1 := by
          have r1632 : 1 ≤ (x 17 4).toNat + (x 16 1 && x 16 5).toNat + (x 15 2 && x 15 6).toNat + (x 14 3 && x 14 7).toNat + (x 13 4 && x 13 8).toNat + (x 12 5 && x 12 9).toNat + (x 11 6 && x 11 10).toNat + (x 10 7 && x 10 11).toNat + (x 9 8 && x 9 12).toNat + (x 8 9 && x 8 13).toNat + (x 7 10 && x 7 14).toNat + (x 6 11).toNat := hcov4 17
          have e1633 : (x 16 1 && x 16 5).toNat = (x 16 5).toNat := handr _ _ (fun h => hp13 16 (hp5 16 (h)))
          have e1634 : (x 7 10 && x 7 14).toNat = (x 7 10).toNat := handl _ _ (fun h => hp2 7 (hp10 7 (h)))
          have b1635 := hb (x 6 11)
          have b1636 := hb (x 7 10)
          have b1637 := hb (x 16 5)
          have b1638 := hb (x 17 4)
          have b1639 := hb (x 15 2 && x 15 6)
          have b1640 := hb (x 14 3 && x 14 7)
          have b1641 := hb (x 13 4 && x 13 8)
          have b1642 := hb (x 12 5 && x 12 9)
          have b1643 := hb (x 11 6 && x 11 10)
          have b1644 := hb (x 10 7 && x 10 11)
          have b1645 := hb (x 9 8 && x 9 12)
          have b1646 := hb (x 8 9 && x 8 13)
          clear * - r1632 e1633 e1634 b1635 b1636 b1637 b1638 b1639 b1640 b1641 b1642 b1643 b1644 b1645 b1646 d1120 d1148 d992 d1253 d1273 d1293 d1313 d1575 d1595 d1599 d1615
          omega
        have d1647 : (x 14 7).toNat = 1 := by
          have r1648 := hand2 (x 14 3) (x 14 7)
          have b1649 := hb (x 14 7)
          have b1650 := hb (x 14 3 && x 14 7)
          clear * - r1648 b1649 b1650 d1631
          omega
        have d1651 : (x 21 8).toNat = 0 := by
          have r1652 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := hd8 21
          have e1653 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
          have e1654 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
          have e1655 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
          have e1656 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
          have e1657 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
          have e1658 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
          have b1659 := hb (x 14 7)
          have b1660 := hb (x 15 6)
          have b1661 := hb (x 16 5)
          have b1662 := hb (x 17 4)
          have b1663 := hb (x 18 11)
          have b1664 := hb (x 19 10)
          have b1665 := hb (x 20 9)
          have b1666 := hb (x 21 8)
          clear * - r1652 e1653 e1654 e1655 e1656 e1657 e1658 b1659 b1660 b1661 b1662 b1663 b1664 b1665 b1666 d1120 d1148 d988 d1647
          omega
        have d1667 : (x 20 9).toNat = 0 := by
          have r1668 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := hd8 21
          have e1669 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
          have e1670 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
          have e1671 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
          have e1672 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
          have e1673 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
          have e1674 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
          have b1675 := hb (x 14 7)
          have b1676 := hb (x 15 6)
          have b1677 := hb (x 16 5)
          have b1678 := hb (x 17 4)
          have b1679 := hb (x 18 11)
          have b1680 := hb (x 19 10)
          have b1681 := hb (x 20 9)
          have b1682 := hb (x 21 8)
          clear * - r1668 e1669 e1670 e1671 e1672 e1673 e1674 b1675 b1676 b1677 b1678 b1679 b1680 b1681 b1682 d1651 d1120 d1148 d988 d1647
          omega
        have d1683 : (x 19 10).toNat = 0 := by
          have r1684 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := hd8 21
          have e1685 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
          have e1686 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
          have e1687 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
          have e1688 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
          have e1689 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
          have e1690 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
          have b1691 := hb (x 14 7)
          have b1692 := hb (x 15 6)
          have b1693 := hb (x 16 5)
          have b1694 := hb (x 17 4)
          have b1695 := hb (x 18 11)
          have b1696 := hb (x 19 10)
          have b1697 := hb (x 20 9)
          have b1698 := hb (x 21 8)
          clear * - r1684 e1685 e1686 e1687 e1688 e1689 e1690 b1691 b1692 b1693 b1694 b1695 b1696 b1697 b1698 d1651 d1667 d1120 d1148 d988 d1647
          omega
        have d1699 : (x 19 1 && x 19 10).toNat = 0 := by
          have r1700 := hand2 (x 19 1) (x 19 10)
          have b1701 := hb (x 19 10)
          have b1702 := hb (x 19 1 && x 19 10)
          clear * - r1700 b1701 b1702 d1683
          omega
        have d1703 : (x 18 11).toNat = 0 := by
          have r1704 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := hd8 21
          have e1705 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
          have e1706 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
          have e1707 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
          have e1708 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
          have e1709 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
          have e1710 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
          have b1711 := hb (x 14 7)
          have b1712 := hb (x 15 6)
          have b1713 := hb (x 16 5)
          have b1714 := hb (x 17 4)
          have b1715 := hb (x 18 11)
          have b1716 := hb (x 19 10)
          have b1717 := hb (x 20 9)
          have b1718 := hb (x 21 8)
          clear * - r1704 e1705 e1706 e1707 e1708 e1709 e1710 b1711 b1712 b1713 b1714 b1715 b1716 b1717 b1718 d1651 d1667 d1683 d1120 d1148 d988 d1647
          omega
        have d1719 : (x 18 1 && x 18 11).toNat = 0 := by
          have r1720 := hand2 (x 18 1) (x 18 11)
          have b1721 := hb (x 18 11)
          have b1722 := hb (x 18 1 && x 18 11)
          clear * - r1720 b1721 b1722 d1703
          omega
        have d1723 : (x 14 5).toNat = 1 := by
          have r1724 : 1 ≤ (x 19 10).toNat + (x 18 1 && x 18 11).toNat + (x 17 2 && x 17 12).toNat + (x 16 3 && x 16 13).toNat + (x 15 4 && x 15 14).toNat + (x 14 5).toNat := hcov10 19
          have b1725 := hb (x 14 5)
          have b1726 := hb (x 19 10)
          have b1727 := hb (x 18 1 && x 18 11)
          have b1728 := hb (x 17 2 && x 17 12)
          have b1729 := hb (x 16 3 && x 16 13)
          have b1730 := hb (x 15 4 && x 15 14)
          clear * - r1724 b1725 b1726 b1727 b1728 b1729 b1730 d1683 d1719 d1112 d1140 d980
          omega
        have d1731 : (x 19 8).toNat = 0 := by
          have r1732 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := hd8 19
          have e1733 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
          have e1734 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
          have e1735 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
          have e1736 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
          have e1737 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
          have e1738 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
          have b1739 := hb (x 12 7)
          have b1740 := hb (x 13 6)
          have b1741 := hb (x 14 5)
          have b1742 := hb (x 15 4)
          have b1743 := hb (x 16 11)
          have b1744 := hb (x 17 10)
          have b1745 := hb (x 18 9)
          have b1746 := hb (x 19 8)
          clear * - r1732 e1733 e1734 e1735 e1736 e1737 e1738 b1739 b1740 b1741 b1742 b1743 b1744 b1745 b1746 d1723
          omega
        have d1747 : (x 18 9).toNat = 0 := by
          have r1748 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := hd8 19
          have e1749 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
          have e1750 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
          have e1751 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
          have e1752 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
          have e1753 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
          have e1754 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
          have b1755 := hb (x 12 7)
          have b1756 := hb (x 13 6)
          have b1757 := hb (x 14 5)
          have b1758 := hb (x 15 4)
          have b1759 := hb (x 16 11)
          have b1760 := hb (x 17 10)
          have b1761 := hb (x 18 9)
          have b1762 := hb (x 19 8)
          clear * - r1748 e1749 e1750 e1751 e1752 e1753 e1754 b1755 b1756 b1757 b1758 b1759 b1760 b1761 b1762 d1731 d1723
          omega
        have d1763 : (x 17 10).toNat = 0 := by
          have r1764 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := hd8 19
          have e1765 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
          have e1766 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
          have e1767 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
          have e1768 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
          have e1769 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
          have e1770 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
          have b1771 := hb (x 12 7)
          have b1772 := hb (x 13 6)
          have b1773 := hb (x 14 5)
          have b1774 := hb (x 15 4)
          have b1775 := hb (x 16 11)
          have b1776 := hb (x 17 10)
          have b1777 := hb (x 18 9)
          have b1778 := hb (x 19 8)
          clear * - r1764 e1765 e1766 e1767 e1768 e1769 e1770 b1771 b1772 b1773 b1774 b1775 b1776 b1777 b1778 d1731 d1747 d1723
          omega
        have d1779 : (x 16 11).toNat = 0 := by
          have r1780 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := hd8 19
          have e1781 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
          have e1782 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
          have e1783 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
          have e1784 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
          have e1785 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
          have e1786 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
          have b1787 := hb (x 12 7)
          have b1788 := hb (x 13 6)
          have b1789 := hb (x 14 5)
          have b1790 := hb (x 15 4)
          have b1791 := hb (x 16 11)
          have b1792 := hb (x 17 10)
          have b1793 := hb (x 18 9)
          have b1794 := hb (x 19 8)
          clear * - r1780 e1781 e1782 e1783 e1784 e1785 e1786 b1787 b1788 b1789 b1790 b1791 b1792 b1793 b1794 d1731 d1747 d1763 d1723
          omega
        have d1795 : (x 15 4).toNat = 0 := by
          have r1796 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := hd8 19
          have e1797 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
          have e1798 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
          have e1799 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
          have e1800 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
          have e1801 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
          have e1802 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
          have b1803 := hb (x 12 7)
          have b1804 := hb (x 13 6)
          have b1805 := hb (x 14 5)
          have b1806 := hb (x 15 4)
          have b1807 := hb (x 16 11)
          have b1808 := hb (x 17 10)
          have b1809 := hb (x 18 9)
          have b1810 := hb (x 19 8)
          clear * - r1796 e1797 e1798 e1799 e1800 e1801 e1802 b1803 b1804 b1805 b1806 b1807 b1808 b1809 b1810 d1731 d1747 d1763 d1779 d1723
          omega
        have d1811 : (x 18 2 && x 18 11).toNat = 0 := by
          have r1812 := hand2 (x 18 2) (x 18 11)
          have b1813 := hb (x 18 11)
          have b1814 := hb (x 18 2 && x 18 11)
          clear * - r1812 b1813 b1814 d1703
          omega
        have d1815 : (x 14 6).toNat = 1 := by
          have r1816 : 1 ≤ (x 20 9).toNat + (x 19 1 && x 19 10).toNat + (x 18 2 && x 18 11).toNat + (x 17 3 && x 17 12).toNat + (x 16 4 && x 16 13).toNat + (x 15 5 && x 15 14).toNat + (x 14 6).toNat := hcov9 20
          have b1817 := hb (x 14 6)
          have b1818 := hb (x 20 9)
          have b1819 := hb (x 19 1 && x 19 10)
          have b1820 := hb (x 18 2 && x 18 11)
          have b1821 := hb (x 17 3 && x 17 12)
          have b1822 := hb (x 16 4 && x 16 13)
          have b1823 := hb (x 15 5 && x 15 14)
          clear * - r1816 b1817 b1818 b1819 b1820 b1821 b1822 b1823 d1667 d1699 d1811 d1116 d1144 d984
          omega
        have d1824 : (x 20 8).toNat = 0 := by
          have r1825 : (x 20 8).toNat + (x 19 1 && x 19 9).toNat + (x 18 2 && x 18 10).toNat + (x 17 3 && x 17 11).toNat + (x 16 4 && x 16 12).toNat + (x 15 5 && x 15 13).toNat + (x 14 6 && x 14 14).toNat + (x 13 7).toNat = 1 := hd8 20
          have e1826 : (x 19 1 && x 19 9).toNat = (x 19 9).toNat := handr _ _ (fun h => hp9 19 (h))
          have e1827 : (x 18 2 && x 18 10).toNat = (x 18 10).toNat := handr _ _ (fun h => hp10 18 (h))
          have e1828 : (x 17 3 && x 17 11).toNat = (x 17 11).toNat := handr _ _ (fun h => hp11 17 (h))
          have e1829 : (x 16 4 && x 16 12).toNat = (x 16 4).toNat := handl _ _ (fun h => hp4 16 (h))
          have e1830 : (x 15 5 && x 15 13).toNat = (x 15 5).toNat := handl _ _ (fun h => hp5 15 (h))
          have e1831 : (x 14 6 && x 14 14).toNat = (x 14 6).toNat := handl _ _ (fun h => hp6 14 (h))
          have b1832 := hb (x 13 7)
          have b1833 := hb (x 14 6)
          have b1834 := hb (x 15 5)
          have b1835 := hb (x 16 4)
          have b1836 := hb (x 17 11)
          have b1837 := hb (x 18 10)
          have b1838 := hb (x 19 9)
          have b1839 := hb (x 20 8)
          clear * - r1825 e1826 e1827 e1828 e1829 e1830 e1831 b1832 b1833 b1834 b1835 b1836 b1837 b1838 b1839 d1173 d1189 d1815
          omega
        have d1840 : (x 19 9).toNat = 0 := by
          have r1841 : (x 20 8).toNat + (x 19 1 && x 19 9).toNat + (x 18 2 && x 18 10).toNat + (x 17 3 && x 17 11).toNat + (x 16 4 && x 16 12).toNat + (x 15 5 && x 15 13).toNat + (x 14 6 && x 14 14).toNat + (x 13 7).toNat = 1 := hd8 20
          have e1842 : (x 19 1 && x 19 9).toNat = (x 19 9).toNat := handr _ _ (fun h => hp9 19 (h))
          have e1843 : (x 18 2 && x 18 10).toNat = (x 18 10).toNat := handr _ _ (fun h => hp10 18 (h))
          have e1844 : (x 17 3 && x 17 11).toNat = (x 17 11).toNat := handr _ _ (fun h => hp11 17 (h))
          have e1845 : (x 16 4 && x 16 12).toNat = (x 16 4).toNat := handl _ _ (fun h => hp4 16 (h))
          have e1846 : (x 15 5 && x 15 13).toNat = (x 15 5).toNat := handl _ _ (fun h => hp5 15 (h))
          have e1847 : (x 14 6 && x 14 14).toNat = (x 14 6).toNat := handl _ _ (fun h => hp6 14 (h))
          have b1848 := hb (x 13 7)
          have b1849 := hb (x 14 6)
          have b1850 := hb (x 15 5)
          have b1851 := hb (x 16 4)
          have b1852 := hb (x 17 11)
          have b1853 := hb (x 18 10)
          have b1854 := hb (x 19 9)
          have b1855 := hb (x 20 8)
          clear * - r1841 e1842 e1843 e1844 e1845 e1846 e1847 b1848 b1849 b1850 b1851 b1852 b1853 b1854 b1855 d1824 d1173 d1189 d1815
          omega
        have d1856 : (x 18 10).toNat = 0 := by
          have r1857 : (x 20 8).toNat + (x 19 1 && x 19 9).toNat + (x 18 2 && x 18 10).toNat + (x 17 3 && x 17 11).toNat + (x 16 4 && x 16 12).toNat + (x 15 5 && x 15 13).toNat + (x 14 6 && x 14 14).toNat + (x 13 7).toNat = 1 := hd8 20
          have e1858 : (x 19 1 && x 19 9).toNat = (x 19 9).toNat := handr _ _ (fun h => hp9 19 (h))
          have e1859 : (x 18 2 && x 18 10).toNat = (x 18 10).toNat := handr _ _ (fun h => hp10 18 (h))
          have e1860 : (x 17 3 && x 17 11).toNat = (x 17 11).toNat := handr _ _ (fun h => hp11 17 (h))
          have e1861 : (x 16 4 && x 16 12).toNat = (x 16 4).toNat := handl _ _ (fun h => hp4 16 (h))
          have e1862 : (x 15 5 && x 15 13).toNat = (x 15 5).toNat := handl _ _ (fun h => hp5 15 (h))
          have e1863 : (x 14 6 && x 14 14).toNat = (x 14 6).toNat := handl _ _ (fun h => hp6 14 (h))
          have b1864 := hb (x 13 7)
          have b1865 := hb (x 14 6)
          have b1866 := hb (x 15 5)
          have b1867 := hb (x 16 4)
          have b1868 := hb (x 17 11)
          have b1869 := hb (x 18 10)
          have b1870 := hb (x 19 9)
          have b1871 := hb (x 20 8)
          clear * - r1857 e1858 e1859 e1860 e1861 e1862 e1863 b1864 b1865 b1866 b1867 b1868 b1869 b1870 b1871 d1824 d1840 d1173 d1189 d1815
          omega
        have d1872 : (x 17 11).toNat = 0 := by
          have r1873 : (x 20 8).toNat + (x 19 1 && x 19 9).toNat + (x 18 2 && x 18 10).toNat + (x 17 3 && x 17 11).toNat + (x 16 4 && x 16 12).toNat + (x 15 5 && x 15 13).toNat + (x 14 6 && x 14 14).toNat + (x 13 7).toNat = 1 := hd8 20
          have e1874 : (x 19 1 && x 19 9).toNat = (x 19 9).toNat := handr _ _ (fun h => hp9 19 (h))
          have e1875 : (x 18 2 && x 18 10).toNat = (x 18 10).toNat := handr _ _ (fun h => hp10 18 (h))
          have e1876 : (x 17 3 && x 17 11).toNat = (x 17 11).toNat := handr _ _ (fun h => hp11 17 (h))
          have e1877 : (x 16 4 && x 16 12).toNat = (x 16 4).toNat := handl _ _ (fun h => hp4 16 (h))
          have e1878 : (x 15 5 && x 15 13).toNat = (x 15 5).toNat := handl _ _ (fun h => hp5 15 (h))
          have e1879 : (x 14 6 && x 14 14).toNat = (x 14 6).toNat := handl _ _ (fun h => hp6 14 (h))
          have b1880 := hb (x 13 7)
          have b1881 := hb (x 14 6)
          have b1882 := hb (x 15 5)
          have b1883 := hb (x 16 4)
          have b1884 := hb (x 17 11)
          have b1885 := hb (x 18 10)
          have b1886 := hb (x 19 9)
          have b1887 := hb (x 20 8)
          clear * - r1873 e1874 e1875 e1876 e1877 e1878 e1879 b1880 b1881 b1882 b1883 b1884 b1885 b1886 b1887 d1824 d1840 d1856 d1173 d1189 d1815
          omega
        have d1888 : (x 17 1 && x 17 11).toNat = 0 := by
          have r1889 := hand2 (x 17 1) (x 17 11)
          have b1890 := hb (x 17 11)
          have b1891 := hb (x 17 1 && x 17 11)
          clear * - r1889 b1890 b1891 d1872
          omega
        have d1892 : (x 14 4 && x 14 14).toNat = 1 := by
          have r1893 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := hcov10 18
          have b1894 := hb (x 13 5)
          have b1895 := hb (x 18 10)
          have b1896 := hb (x 17 1 && x 17 11)
          have b1897 := hb (x 16 2 && x 16 12)
          have b1898 := hb (x 15 3 && x 15 13)
          have b1899 := hb (x 14 4 && x 14 14)
          clear * - r1893 b1894 b1895 b1896 b1897 b1898 b1899 d1856 d1888 d1169 d1185 d923
          omega
        have d1900 : (x 14 4).toNat = 1 := by
          have r1901 := hand1 (x 14 4) (x 14 14)
          have b1902 := hb (x 14 4)
          have b1903 := hb (x 14 4 && x 14 14)
          clear * - r1901 b1902 b1903 d1892
          omega
        have d1904 : (x 14 12).toNat = 1 := by
          have r1905 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
          have b1906 := hb (x 14 4)
          have b1907 := hb (x 14 12)
          clear * - r1905 b1906 b1907 d1900
          omega
        have d1908 : (x 16 1).toNat = 1 := by
          have r1909 : (x 16 1).toNat + (x 15 2).toNat + (x 14 3).toNat + (x 13 4).toNat + (x 12 5).toNat + (x 11 6).toNat + (x 10 7).toNat + (x 9 8).toNat + (x 8 9).toNat + (x 7 10).toNat + (x 6 11).toNat + (x 5 12).toNat + (x 4 13).toNat + (x 3 14).toNat = 3 := hcount 17
          have b1910 := hb (x 3 14)
          have b1911 := hb (x 4 13)
          have b1912 := hb (x 5 12)
          have b1913 := hb (x 6 11)
          have b1914 := hb (x 7 10)
          have b1915 := hb (x 8 9)
          have b1916 := hb (x 9 8)
          have b1917 := hb (x 10 7)
          have b1918 := hb (x 11 6)
          have b1919 := hb (x 12 5)
          have b1920 := hb (x 13 4)
          have b1921 := hb (x 14 3)
          have b1922 := hb (x 15 2)
          have b1923 := hb (x 16 1)
          clear * - r1909 b1910 b1911 b1912 b1913 b1914 b1915 b1916 b1917 b1918 b1919 b1920 b1921 b1922 b1923 d996 d1100 d1237 d1257 d1277 d1297 d1559 d1579 d1599 d1615 d839 d851 d819
          omega
        have d1924 : (x 17 14).toNat = 0 := by
          have r1925 : (x 17 14).toNat + (x 16 1).toNat = 1 := hd14 17
          have b1926 := hb (x 16 1)
          have b1927 := hb (x 17 14)
          clear * - r1925 b1926 b1927 d1908
          omega
        have d1928 : (x 17 1 && x 17 14).toNat = 0 := by
          have r1929 := hand2 (x 17 1) (x 17 14)
          have b1930 := hb (x 17 14)
          have b1931 := hb (x 17 1 && x 17 14)
          clear * - r1929 b1930 b1931 d1924
          omega
        have d1932 : (x 17 3 && x 17 14).toNat = 0 := by
          have r1933 := hand2 (x 17 3) (x 17 14)
          have b1934 := hb (x 17 14)
          have b1935 := hb (x 17 3 && x 17 14)
          clear * - r1933 b1934 b1935 d1924
          omega
        have d1936 : (x 17 5 && x 17 14).toNat = 0 := by
          have r1937 := hand2 (x 17 5) (x 17 14)
          have b1938 := hb (x 17 14)
          have b1939 := hb (x 17 5 && x 17 14)
          clear * - r1937 b1938 b1939 d1924
          omega
        have d1940 : (x 17 6).toNat = 0 := by
          have r1941 : (x 17 6).toNat ≤ (x 17 14).toNat := himp _ _ (hp6 17)
          have b1942 := hb (x 17 6)
          have b1943 := hb (x 17 14)
          clear * - r1941 b1942 b1943 d1924
          omega
        have d1944 : (x 17 2).toNat = 0 := by
          have r1945 : (x 17 2).toNat ≤ (x 17 14).toNat := himp _ _ (hp2 17)
          have b1946 := hb (x 17 2)
          have b1947 := hb (x 17 14)
          clear * - r1945 b1946 b1947 d1924
          omega
        have d1948 : (x 17 2 && x 17 13).toNat = 0 := by
          have r1949 := hand1 (x 17 2) (x 17 13)
          have b1950 := hb (x 17 2)
          have b1951 := hb (x 17 2 && x 17 13)
          clear * - r1949 b1950 b1951 d1944
          omega
        have d1952 : (x 11 3).toNat = 0 := by
          have r1953 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
          have e1954 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
          have e1955 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
          have b1956 := hb (x 11 3)
          have b1957 := hb (x 12 2)
          have b1958 := hb (x 13 13)
          have b1959 := hb (x 14 12)
          clear * - r1953 e1954 e1955 b1956 b1957 b1958 b1959 d1904 d919 d935
          omega
        have d1960 : (x 11 3 && x 11 13).toNat = 0 := by
          have r1961 := hand1 (x 11 3) (x 11 13)
          have b1962 := hb (x 11 3)
          have b1963 := hb (x 11 3 && x 11 13)
          clear * - r1961 b1962 b1963 d1952
          omega
        have d1964 : (x 11 11).toNat = 0 := by
          have r1965 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
          have b1966 := hb (x 11 3)
          have b1967 := hb (x 11 11)
          clear * - r1965 b1966 b1967 d1952
          omega
        have d1968 : (x 10 4).toNat = 0 := by
          have r1969 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := hcount 14
          have b1970 := hb (x 0 14)
          have b1971 := hb (x 1 13)
          have b1972 := hb (x 2 12)
          have b1973 := hb (x 3 11)
          have b1974 := hb (x 4 10)
          have b1975 := hb (x 5 9)
          have b1976 := hb (x 6 8)
          have b1977 := hb (x 7 7)
          have b1978 := hb (x 8 6)
          have b1979 := hb (x 9 5)
          have b1980 := hb (x 10 4)
          have b1981 := hb (x 11 3)
          have b1982 := hb (x 12 2)
          have b1983 := hb (x 13 1)
          clear * - r1969 b1970 b1971 b1972 b1973 b1974 b1975 b1976 b1977 b1978 b1979 b1980 b1981 b1982 b1983 d895 d935 d1952 d863 d879 d739 d755 d532 d527 g13
          omega
        have d1984 : (x 10 4 && x 10 14).toNat = 0 := by
          have r1985 := hand1 (x 10 4) (x 10 14)
          have b1986 := hb (x 10 4)
          have b1987 := hb (x 10 4 && x 10 14)
          clear * - r1985 b1986 b1987 d1968
          omega
        have d1988 : (x 9 5).toNat = 0 := by
          have r1989 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := hcount 14
          have b1990 := hb (x 0 14)
          have b1991 := hb (x 1 13)
          have b1992 := hb (x 2 12)
          have b1993 := hb (x 3 11)
          have b1994 := hb (x 4 10)
          have b1995 := hb (x 5 9)
          have b1996 := hb (x 6 8)
          have b1997 := hb (x 7 7)
          have b1998 := hb (x 8 6)
          have b1999 := hb (x 9 5)
          have b2000 := hb (x 10 4)
          have b2001 := hb (x 11 3)
          have b2002 := hb (x 12 2)
          have b2003 := hb (x 13 1)
          clear * - r1989 b1990 b1991 b1992 b1993 b1994 b1995 b1996 b1997 b1998 b1999 b2000 b2001 b2002 b2003 d895 d935 d1952 d1968 d863 d879 d739 d755 d532 d527 g13
          omega
        have d2004 : (x 14 10).toNat = 1 := by
          have r2005 : 1 ≤ (x 14 10).toNat + (x 13 1 && x 13 11).toNat + (x 12 2 && x 12 12).toNat + (x 11 3 && x 11 13).toNat + (x 10 4 && x 10 14).toNat + (x 9 5).toNat := hcov10 14
          have b2006 := hb (x 9 5)
          have b2007 := hb (x 14 10)
          have b2008 := hb (x 13 1 && x 13 11)
          have b2009 := hb (x 12 2 && x 12 12)
          have b2010 := hb (x 11 3 && x 11 13)
          have b2011 := hb (x 10 4 && x 10 14)
          clear * - r2005 b2006 b2007 b2008 b2009 b2010 b2011 d915 d951 d1960 d1984 d1988
          omega
        have d2012 : (x 16 8).toNat = 0 := by
          have r2013 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := hd8 16
          have e2014 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
          have e2015 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
          have e2016 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
          have e2017 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
          have e2018 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
          have e2019 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
          have b2020 := hb (x 9 7)
          have b2021 := hb (x 10 6)
          have b2022 := hb (x 11 5)
          have b2023 := hb (x 12 4)
          have b2024 := hb (x 13 11)
          have b2025 := hb (x 14 10)
          have b2026 := hb (x 15 9)
          have b2027 := hb (x 16 8)
          clear * - r2013 e2014 e2015 e2016 e2017 e2018 e2019 b2020 b2021 b2022 b2023 b2024 b2025 b2026 b2027 d2004 d1201
          omega
        have d2028 : (x 15 9).toNat = 0 := by
          have r2029 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := hd8 16
          have e2030 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
          have e2031 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
          have e2032 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
          have e2033 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
          have e2034 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
          have e2035 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
          have b2036 := hb (x 9 7)
          have b2037 := hb (x 10 6)
          have b2038 := hb (x 11 5)
          have b2039 := hb (x 12 4)
          have b2040 := hb (x 13 11)
          have b2041 := hb (x 14 10)
          have b2042 := hb (x 15 9)
          have b2043 := hb (x 16 8)
          clear * - r2029 e2030 e2031 e2032 e2033 e2034 e2035 b2036 b2037 b2038 b2039 b2040 b2041 b2042 b2043 d2012 d2004 d1201
          omega
        have d2044 : (x 12 4).toNat = 0 := by
          have r2045 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := hd8 16
          have e2046 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
          have e2047 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
          have e2048 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
          have e2049 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
          have e2050 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
          have e2051 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
          have b2052 := hb (x 9 7)
          have b2053 := hb (x 10 6)
          have b2054 := hb (x 11 5)
          have b2055 := hb (x 12 4)
          have b2056 := hb (x 13 11)
          have b2057 := hb (x 14 10)
          have b2058 := hb (x 15 9)
          have b2059 := hb (x 16 8)
          clear * - r2045 e2046 e2047 e2048 e2049 e2050 e2051 b2052 b2053 b2054 b2055 b2056 b2057 b2058 b2059 d2012 d2028 d2004 d1201
          omega
        have d2060 : (x 11 5).toNat = 0 := by
          have r2061 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := hd8 16
          have e2062 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
          have e2063 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
          have e2064 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
          have e2065 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
          have e2066 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
          have e2067 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
          have b2068 := hb (x 9 7)
          have b2069 := hb (x 10 6)
          have b2070 := hb (x 11 5)
          have b2071 := hb (x 12 4)
          have b2072 := hb (x 13 11)
          have b2073 := hb (x 14 10)
          have b2074 := hb (x 15 9)
          have b2075 := hb (x 16 8)
          clear * - r2061 e2062 e2063 e2064 e2065 e2066 e2067 b2068 b2069 b2070 b2071 b2072 b2073 b2074 b2075 d2012 d2028 d2004 d1201 d2044
          omega
        have d2076 : (x 10 6).toNat = 0 := by
          have r2077 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := hd8 16
          have e2078 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
          have e2079 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
          have e2080 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
          have e2081 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
          have e2082 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
          have e2083 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
          have b2084 := hb (x 9 7)
          have b2085 := hb (x 10 6)
          have b2086 := hb (x 11 5)
          have b2087 := hb (x 12 4)
          have b2088 := hb (x 13 11)
          have b2089 := hb (x 14 10)
          have b2090 := hb (x 15 9)
          have b2091 := hb (x 16 8)
          clear * - r2077 e2078 e2079 e2080 e2081 e2082 e2083 b2084 b2085 b2086 b2087 b2088 b2089 b2090 b2091 d2012 d2028 d2004 d1201 d2044 d2060
          omega
        have d2092 : (x 9 7).toNat = 0 := by
          have r2093 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := hd8 16
          have e2094 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
          have e2095 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
          have e2096 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
          have e2097 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
          have e2098 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
          have e2099 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
          have b2100 := hb (x 9 7)
          have b2101 := hb (x 10 6)
          have b2102 := hb (x 11 5)
          have b2103 := hb (x 12 4)
          have b2104 := hb (x 13 11)
          have b2105 := hb (x 14 10)
          have b2106 := hb (x 15 9)
          have b2107 := hb (x 16 8)
          clear * - r2093 e2094 e2095 e2096 e2097 e2098 e2099 b2100 b2101 b2102 b2103 b2104 b2105 b2106 b2107 d2012 d2028 d2004 d1201 d2044 d2060 d2076
          omega
        have d2108 : (x 15 1).toNat = 1 := by
          have r2109 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := hcount 16
          have b2110 := hb (x 2 14)
          have b2111 := hb (x 3 13)
          have b2112 := hb (x 4 12)
          have b2113 := hb (x 5 11)
          have b2114 := hb (x 6 10)
          have b2115 := hb (x 7 9)
          have b2116 := hb (x 8 8)
          have b2117 := hb (x 9 7)
          have b2118 := hb (x 10 6)
          have b2119 := hb (x 11 5)
          have b2120 := hb (x 12 4)
          have b2121 := hb (x 13 3)
          have b2122 := hb (x 14 2)
          have b2123 := hb (x 15 1)
          clear * - r2109 b2110 b2111 b2112 b2113 b2114 b2115 b2116 b2117 b2118 b2119 b2120 b2121 b2122 b2123 d1156 d1193 d2044 d2060 d2076 d2092 d1482 d1498 d1514 d1530 d743 d702 d438
          omega
        have d2124 : (x 16 14).toNat = 0 := by
          have r2125 : (x 16 14).toNat + (x 15 1).toNat = 1 := hd14 16
          have b2126 := hb (x 15 1)
          have b2127 := hb (x 16 14)
          clear * - r2125 b2126 b2127 d2108
          omega
        have d2128 : (x 16 1 && x 16 14).toNat = 0 := by
          have r2129 := hand2 (x 16 1) (x 16 14)
          have b2130 := hb (x 16 14)
          have b2131 := hb (x 16 1 && x 16 14)
          clear * - r2129 b2130 b2131 d2124
          omega
        have d2132 : (x 17 13).toNat = 1 := by
          have r2133 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := hcov13 17
          have b2134 := hb (x 15 2)
          have b2135 := hb (x 17 13)
          have b2136 := hb (x 16 1 && x 16 14)
          clear * - r2133 b2134 b2135 b2136 d2128 d996
          omega
        have d2137 : (x 17 1).toNat = 1 := by
          have r2138 : (x 17 13).toNat ≤ (x 17 1).toNat := himp _ _ (hp13 17)
          have b2139 := hb (x 17 1)
          have b2140 := hb (x 17 13)
          clear * - r2138 b2139 b2140 d2132
          omega
        have d2141 : (x 18 14).toNat = 0 := by
          have r2142 : (x 18 14).toNat + (x 17 1).toNat = 1 := hd14 18
          have b2143 := hb (x 17 1)
          have b2144 := hb (x 18 14)
          clear * - r2142 b2143 b2144 d2137
          omega
        have d2145 : (x 18 1 && x 18 14).toNat = 0 := by
          have r2146 := hand2 (x 18 1) (x 18 14)
          have b2147 := hb (x 18 14)
          have b2148 := hb (x 18 1 && x 18 14)
          clear * - r2146 b2147 b2148 d2141
          omega
        have d2149 : (x 19 13).toNat = 1 := by
          have r2150 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := hcov13 19
          have b2151 := hb (x 17 2)
          have b2152 := hb (x 19 13)
          have b2153 := hb (x 18 1 && x 18 14)
          clear * - r2150 b2151 b2152 b2153 d2145 d1944
          omega
        have d2154 : (x 20 12).toNat = 0 := by
          have r2155 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
          have e2156 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
          have e2157 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
          have b2158 := hb (x 17 3)
          have b2159 := hb (x 18 2)
          have b2160 := hb (x 19 13)
          have b2161 := hb (x 20 12)
          clear * - r2155 e2156 e2157 b2158 b2159 b2160 b2161 d2149
          omega
        have d2162 : (x 18 2).toNat = 0 := by
          have r2163 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
          have e2164 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
          have e2165 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
          have b2166 := hb (x 17 3)
          have b2167 := hb (x 18 2)
          have b2168 := hb (x 19 13)
          have b2169 := hb (x 20 12)
          clear * - r2163 e2164 e2165 b2166 b2167 b2168 b2169 d2154 d2149
          omega
        have d2170 : (x 18 2 && x 18 13).toNat = 0 := by
          have r2171 := hand1 (x 18 2) (x 18 13)
          have b2172 := hb (x 18 2)
          have b2173 := hb (x 18 2 && x 18 13)
          clear * - r2171 b2172 b2173 d2162
          omega
        have d2174 : (x 18 12).toNat = 0 := by
          have r2175 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
          have e2176 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
          have e2177 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
          have b2178 := hb (x 15 3)
          have b2179 := hb (x 16 2)
          have b2180 := hb (x 17 13)
          have b2181 := hb (x 18 12)
          clear * - r2175 e2176 e2177 b2178 b2179 b2180 b2181 d2132
          omega
        have d2182 : (x 18 1 && x 18 12).toNat = 0 := by
          have r2183 := hand2 (x 18 1) (x 18 12)
          have b2184 := hb (x 18 12)
          have b2185 := hb (x 18 1 && x 18 12)
          clear * - r2183 b2184 b2185 d2174
          omega
        have d2186 : (x 18 3 && x 18 12).toNat = 0 := by
          have r2187 := hand2 (x 18 3) (x 18 12)
          have b2188 := hb (x 18 12)
          have b2189 := hb (x 18 3 && x 18 12)
          clear * - r2187 b2188 b2189 d2174
          omega
        have d2190 : (x 18 4).toNat = 0 := by
          have r2191 : (x 18 4).toNat ≤ (x 18 12).toNat := himp _ _ (hp4 18)
          have b2192 := hb (x 18 4)
          have b2193 := hb (x 18 12)
          clear * - r2191 b2192 b2193 d2174
          omega
        have d2194 : (x 18 4 && x 18 13).toNat = 0 := by
          have r2195 := hand1 (x 18 4) (x 18 13)
          have b2196 := hb (x 18 4)
          have b2197 := hb (x 18 4 && x 18 13)
          clear * - r2195 b2196 b2197 d2190
          omega
        have d2198 : (x 16 2).toNat = 0 := by
          have r2199 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
          have e2200 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
          have e2201 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
          have b2202 := hb (x 15 3)
          have b2203 := hb (x 16 2)
          have b2204 := hb (x 17 13)
          have b2205 := hb (x 18 12)
          clear * - r2199 e2200 e2201 b2202 b2203 b2204 b2205 d2174 d2132
          omega
        have d2206 : (x 18 13).toNat = 1 := by
          have r2207 : 1 ≤ (x 18 13).toNat + (x 17 1 && x 17 14).toNat + (x 16 2).toNat := hcov13 18
          have b2208 := hb (x 16 2)
          have b2209 := hb (x 18 13)
          have b2210 := hb (x 17 1 && x 17 14)
          clear * - r2207 b2208 b2209 b2210 d1928 d2198
          omega
        have d2211 : (x 19 12).toNat = 0 := by
          have r2212 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
          have e2213 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
          have e2214 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
          have b2215 := hb (x 16 3)
          have b2216 := hb (x 17 2)
          have b2217 := hb (x 18 13)
          have b2218 := hb (x 19 12)
          clear * - r2212 e2213 e2214 b2215 b2216 b2217 b2218 d2206 d1944
          omega
        have d2219 : (x 19 1 && x 19 12).toNat = 0 := by
          have r2220 := hand2 (x 19 1) (x 19 12)
          have b2221 := hb (x 19 12)
          have b2222 := hb (x 19 1 && x 19 12)
          clear * - r2220 b2221 b2222 d2211
          omega
        have d2223 : (x 20 11).toNat = 1 := by
          have r2224 : 1 ≤ (x 20 11).toNat + (x 19 1 && x 19 12).toNat + (x 18 2 && x 18 13).toNat + (x 17 3 && x 17 14).toNat + (x 16 4).toNat := hcov11 20
          have b2225 := hb (x 16 4)
          have b2226 := hb (x 20 11)
          have b2227 := hb (x 19 1 && x 19 12)
          have b2228 := hb (x 18 2 && x 18 13)
          have b2229 := hb (x 17 3 && x 17 14)
          clear * - r2224 b2225 b2226 b2227 b2228 b2229 d2219 d2170 d1932 d1173
          omega
        have d2230 : (x 23 8).toNat = 0 := by
          have r2231 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := hd8 23
          have e2232 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
          have e2233 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
          have e2234 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
          have e2235 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
          have e2236 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
          have e2237 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
          have b2238 := hb (x 16 7)
          have b2239 := hb (x 17 6)
          have b2240 := hb (x 18 5)
          have b2241 := hb (x 19 4)
          have b2242 := hb (x 20 11)
          have b2243 := hb (x 21 10)
          have b2244 := hb (x 22 9)
          have b2245 := hb (x 23 8)
          clear * - r2231 e2232 e2233 e2234 e2235 e2236 e2237 b2238 b2239 b2240 b2241 b2242 b2243 b2244 b2245 d2223 d1940
          omega
        have d2246 : (x 22 9).toNat = 0 := by
          have r2247 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := hd8 23
          have e2248 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
          have e2249 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
          have e2250 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
          have e2251 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
          have e2252 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
          have e2253 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
          have b2254 := hb (x 16 7)
          have b2255 := hb (x 17 6)
          have b2256 := hb (x 18 5)
          have b2257 := hb (x 19 4)
          have b2258 := hb (x 20 11)
          have b2259 := hb (x 21 10)
          have b2260 := hb (x 22 9)
          have b2261 := hb (x 23 8)
          clear * - r2247 e2248 e2249 e2250 e2251 e2252 e2253 b2254 b2255 b2256 b2257 b2258 b2259 b2260 b2261 d2230 d2223 d1940
          omega
        have d2262 : (x 21 10).toNat = 0 := by
          have r2263 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := hd8 23
          have e2264 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
          have e2265 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
          have e2266 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
          have e2267 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
          have e2268 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
          have e2269 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
          have b2270 := hb (x 16 7)
          have b2271 := hb (x 17 6)
          have b2272 := hb (x 18 5)
          have b2273 := hb (x 19 4)
          have b2274 := hb (x 20 11)
          have b2275 := hb (x 21 10)
          have b2276 := hb (x 22 9)
          have b2277 := hb (x 23 8)
          clear * - r2263 e2264 e2265 e2266 e2267 e2268 e2269 b2270 b2271 b2272 b2273 b2274 b2275 b2276 b2277 d2230 d2246 d2223 d1940
          omega
        have d2278 : (x 21 1 && x 21 10).toNat = 0 := by
          have r2279 := hand2 (x 21 1) (x 21 10)
          have b2280 := hb (x 21 10)
          have b2281 := hb (x 21 1 && x 21 10)
          clear * - r2279 b2280 b2281 d2262
          omega
        have d2282 : (x 19 2 && x 19 12).toNat = 0 := by
          have r2283 := hand2 (x 19 2) (x 19 12)
          have b2284 := hb (x 19 12)
          have b2285 := hb (x 19 2 && x 19 12)
          clear * - r2283 b2284 b2285 d2211
          omega
        have d2286 : (x 19 3 && x 19 12).toNat = 0 := by
          have r2287 := hand2 (x 19 3) (x 19 12)
          have b2288 := hb (x 19 12)
          have b2289 := hb (x 19 3 && x 19 12)
          clear * - r2287 b2288 b2289 d2211
          omega
        have d2290 : (x 16 3).toNat = 0 := by
          have r2291 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
          have e2292 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
          have e2293 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
          have b2294 := hb (x 16 3)
          have b2295 := hb (x 17 2)
          have b2296 := hb (x 18 13)
          have b2297 := hb (x 19 12)
          clear * - r2291 e2292 e2293 b2294 b2295 b2296 b2297 d2211 d2206 d1944
          omega
        have d2298 : (x 16 3 && x 16 14).toNat = 0 := by
          have r2299 := hand1 (x 16 3) (x 16 14)
          have b2300 := hb (x 16 3)
          have b2301 := hb (x 16 3 && x 16 14)
          clear * - r2299 b2300 b2301 d2290
          omega
        have d2302 : (x 19 11).toNat = 1 := by
          have r2303 : 1 ≤ (x 19 11).toNat + (x 18 1 && x 18 12).toNat + (x 17 2 && x 17 13).toNat + (x 16 3 && x 16 14).toNat + (x 15 4).toNat := hcov11 19
          have b2304 := hb (x 15 4)
          have b2305 := hb (x 19 11)
          have b2306 := hb (x 18 1 && x 18 12)
          have b2307 := hb (x 17 2 && x 17 13)
          have b2308 := hb (x 16 3 && x 16 14)
          clear * - r2303 b2304 b2305 b2306 b2307 b2308 d2182 d1948 d2298 d1795
          omega
        have d2309 : (x 19 3).toNat = 1 := by
          have r2310 : (x 19 11).toNat ≤ (x 19 3).toNat := himp _ _ (hp11 19)
          have b2311 := hb (x 19 3)
          have b2312 := hb (x 19 11)
          clear * - r2310 b2311 b2312 d2302
          omega
        have d2313 : (x 22 8).toNat = 0 := by
          have r2314 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := hd8 22
          have e2315 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
          have e2316 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
          have e2317 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
          have e2318 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
          have e2319 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
          have e2320 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
          have b2321 := hb (x 15 7)
          have b2322 := hb (x 16 6)
          have b2323 := hb (x 17 5)
          have b2324 := hb (x 18 4)
          have b2325 := hb (x 19 11)
          have b2326 := hb (x 20 10)
          have b2327 := hb (x 21 9)
          have b2328 := hb (x 22 8)
          clear * - r2314 e2315 e2316 e2317 e2318 e2319 e2320 b2321 b2322 b2323 b2324 b2325 b2326 b2327 b2328 d2302 d2190
          omega
        have d2329 : (x 21 9).toNat = 0 := by
          have r2330 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := hd8 22
          have e2331 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
          have e2332 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
          have e2333 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
          have e2334 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
          have e2335 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
          have e2336 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
          have b2337 := hb (x 15 7)
          have b2338 := hb (x 16 6)
          have b2339 := hb (x 17 5)
          have b2340 := hb (x 18 4)
          have b2341 := hb (x 19 11)
          have b2342 := hb (x 20 10)
          have b2343 := hb (x 21 9)
          have b2344 := hb (x 22 8)
          clear * - r2330 e2331 e2332 e2333 e2334 e2335 e2336 b2337 b2338 b2339 b2340 b2341 b2342 b2343 b2344 d2313 d2302 d2190
          omega
        have d2345 : (x 20 10).toNat = 0 := by
          have r2346 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := hd8 22
          have e2347 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
          have e2348 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
          have e2349 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
          have e2350 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
          have e2351 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
          have e2352 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
          have b2353 := hb (x 15 7)
          have b2354 := hb (x 16 6)
          have b2355 := hb (x 17 5)
          have b2356 := hb (x 18 4)
          have b2357 := hb (x 19 11)
          have b2358 := hb (x 20 10)
          have b2359 := hb (x 21 9)
          have b2360 := hb (x 22 8)
          clear * - r2346 e2347 e2348 e2349 e2350 e2351 e2352 b2353 b2354 b2355 b2356 b2357 b2358 b2359 b2360 d2313 d2329 d2302 d2190
          omega
        have d2361 : (x 20 1 && x 20 10).toNat = 0 := by
          have r2362 := hand2 (x 20 1) (x 20 10)
          have b2363 := hb (x 20 10)
          have b2364 := hb (x 20 1 && x 20 10)
          clear * - r2362 b2363 b2364 d2345
          omega
        have d2365 : (x 19 2 && x 19 11).toNat = 1 := by
          have r2366 : 1 ≤ (x 21 9).toNat + (x 20 1 && x 20 10).toNat + (x 19 2 && x 19 11).toNat + (x 18 3 && x 18 12).toNat + (x 17 4 && x 17 13).toNat + (x 16 5 && x 16 14).toNat + (x 15 6).toNat := hcov9 21
          have b2367 := hb (x 15 6)
          have b2368 := hb (x 21 9)
          have b2369 := hb (x 20 1 && x 20 10)
          have b2370 := hb (x 19 2 && x 19 11)
          have b2371 := hb (x 18 3 && x 18 12)
          have b2372 := hb (x 17 4 && x 17 13)
          have b2373 := hb (x 16 5 && x 16 14)
          clear * - r2366 b2367 b2368 b2369 b2370 b2371 b2372 b2373 d2329 d2361 d2186 d1128 d1152 d988
          omega
        have d2374 : (x 19 2).toNat = 1 := by
          have r2375 := hand1 (x 19 2) (x 19 11)
          have b2376 := hb (x 19 2)
          have b2377 := hb (x 19 2 && x 19 11)
          clear * - r2375 b2376 b2377 d2365
          omega
        have d2378 : (x 17 5).toNat = 0 := by
          have r2379 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := hd8 22
          have e2380 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
          have e2381 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
          have e2382 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
          have e2383 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
          have e2384 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
          have e2385 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
          have b2386 := hb (x 15 7)
          have b2387 := hb (x 16 6)
          have b2388 := hb (x 17 5)
          have b2389 := hb (x 18 4)
          have b2390 := hb (x 19 11)
          have b2391 := hb (x 20 10)
          have b2392 := hb (x 21 9)
          have b2393 := hb (x 22 8)
          clear * - r2379 e2380 e2381 e2382 e2383 e2384 e2385 b2386 b2387 b2388 b2389 b2390 b2391 b2392 b2393 d2313 d2329 d2345 d2302 d2190
          omega
        have d2394 : (x 16 6).toNat = 0 := by
          have r2395 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := hd8 22
          have e2396 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
          have e2397 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
          have e2398 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
          have e2399 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
          have e2400 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
          have e2401 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
          have b2402 := hb (x 15 7)
          have b2403 := hb (x 16 6)
          have b2404 := hb (x 17 5)
          have b2405 := hb (x 18 4)
          have b2406 := hb (x 19 11)
          have b2407 := hb (x 20 10)
          have b2408 := hb (x 21 9)
          have b2409 := hb (x 22 8)
          clear * - r2395 e2396 e2397 e2398 e2399 e2400 e2401 b2402 b2403 b2404 b2405 b2406 b2407 b2408 b2409 d2313 d2329 d2345 d2302 d2190 d2378
          omega
        have d2410 : (x 20 2 && x 20 11).toNat = 1 := by
          have r2411 : 1 ≤ (x 22 9).toNat + (x 21 1 && x 21 10).toNat + (x 20 2 && x 20 11).toNat + (x 19 3 && x 19 12).toNat + (x 18 4 && x 18 13).toNat + (x 17 5 && x 17 14).toNat + (x 16 6).toNat := hcov9 22
          have b2412 := hb (x 16 6)
          have b2413 := hb (x 22 9)
          have b2414 := hb (x 21 1 && x 21 10)
          have b2415 := hb (x 20 2 && x 20 11)
          have b2416 := hb (x 19 3 && x 19 12)
          have b2417 := hb (x 18 4 && x 18 13)
          have b2418 := hb (x 17 5 && x 17 14)
          clear * - r2411 b2412 b2413 b2414 b2415 b2416 b2417 b2418 d2246 d2278 d2286 d2194 d1936 d2394
          omega
        have d2419 : (x 20 2).toNat = 1 := by
          have r2420 := hand1 (x 20 2) (x 20 11)
          have b2421 := hb (x 20 2)
          have b2422 := hb (x 20 2 && x 20 11)
          clear * - r2420 b2421 b2422 d2410
          omega
        have d2423 : (x 15 7).toNat = 0 := by
          have r2424 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := hd8 22
          have e2425 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
          have e2426 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
          have e2427 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
          have e2428 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
          have e2429 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
          have e2430 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
          have b2431 := hb (x 15 7)
          have b2432 := hb (x 16 6)
          have b2433 := hb (x 17 5)
          have b2434 := hb (x 18 4)
          have b2435 := hb (x 19 11)
          have b2436 := hb (x 20 10)
          have b2437 := hb (x 21 9)
          have b2438 := hb (x 22 8)
          clear * - r2424 e2425 e2426 e2427 e2428 e2429 e2430 b2431 b2432 b2433 b2434 b2435 b2436 b2437 b2438 d2313 d2329 d2345 d2302 d2190 d2378 d2394
          omega
        have d2439 : (x 14 1 && x 14 8).toNat = 1 := by
          have r2440 : 1 ≤ (x 15 7).toNat + (x 14 1 && x 14 8).toNat + (x 13 2 && x 13 9).toNat + (x 12 3 && x 12 10).toNat + (x 11 4 && x 11 11).toNat + (x 10 5 && x 10 12).toNat + (x 9 6 && x 9 13).toNat + (x 8 7 && x 8 14).toNat + (x 7 8).toNat := hcov7 15
          have b2441 := hb (x 7 8)
          have b2442 := hb (x 15 7)
          have b2443 := hb (x 14 1 && x 14 8)
          have b2444 := hb (x 13 2 && x 13 9)
          have b2445 := hb (x 12 3 && x 12 10)
          have b2446 := hb (x 11 4 && x 11 11)
          have b2447 := hb (x 10 5 && x 10 12)
          have b2448 := hb (x 9 6 && x 9 13)
          have b2449 := hb (x 8 7 && x 8 14)
          clear * - r2440 b2441 b2442 b2443 b2444 b2445 b2446 b2447 b2448 b2449 d2423 d931 d959 d1064 d1084 d1333 d1357 d1365
          omega
        have d2450 : (x 14 8).toNat = 1 := by
          have r2451 := hand2 (x 14 1) (x 14 8)
          have b2452 := hb (x 14 8)
          have b2453 := hb (x 14 1 && x 14 8)
          clear * - r2451 b2452 b2453 d2439
          omega
        have d2454 : (x 21 1).toNat = 0 := by
          have r2455 : (x 21 1).toNat + (x 20 2).toNat + (x 19 3).toNat + (x 18 4).toNat + (x 17 5).toNat + (x 16 6).toNat + (x 15 7).toNat + (x 14 8).toNat + (x 13 9).toNat + (x 12 10).toNat + (x 11 11).toNat + (x 10 12).toNat + (x 9 13).toNat + (x 8 14).toNat = 3 := hcount 22
          have b2456 := hb (x 8 14)
          have b2457 := hb (x 9 13)
          have b2458 := hb (x 10 12)
          have b2459 := hb (x 11 11)
          have b2460 := hb (x 12 10)
          have b2461 := hb (x 13 9)
          have b2462 := hb (x 14 8)
          have b2463 := hb (x 15 7)
          have b2464 := hb (x 16 6)
          have b2465 := hb (x 17 5)
          have b2466 := hb (x 18 4)
          have b2467 := hb (x 19 3)
          have b2468 := hb (x 20 2)
          have b2469 := hb (x 21 1)
          clear * - r2455 b2456 b2457 b2458 b2459 b2460 b2461 b2462 b2463 b2464 b2465 b2466 b2467 b2468 b2469 d2419 d2309 d2190 d2378 d2394 d2423 d2450 d927 d955 d1964
          omega
        have d2470 : (x 10 12).toNat = 0 := by
          have r2471 : (x 21 1).toNat + (x 20 2).toNat + (x 19 3).toNat + (x 18 4).toNat + (x 17 5).toNat + (x 16 6).toNat + (x 15 7).toNat + (x 14 8).toNat + (x 13 9).toNat + (x 12 10).toNat + (x 11 11).toNat + (x 10 12).toNat + (x 9 13).toNat + (x 8 14).toNat = 3 := hcount 22
          have b2472 := hb (x 8 14)
          have b2473 := hb (x 9 13)
          have b2474 := hb (x 10 12)
          have b2475 := hb (x 11 11)
          have b2476 := hb (x 12 10)
          have b2477 := hb (x 13 9)
          have b2478 := hb (x 14 8)
          have b2479 := hb (x 15 7)
          have b2480 := hb (x 16 6)
          have b2481 := hb (x 17 5)
          have b2482 := hb (x 18 4)
          have b2483 := hb (x 19 3)
          have b2484 := hb (x 20 2)
          have b2485 := hb (x 21 1)
          clear * - r2471 b2472 b2473 b2474 b2475 b2476 b2477 b2478 b2479 b2480 b2481 b2482 b2483 b2484 b2485 d2454 d2419 d2309 d2190 d2378 d2394 d2423 d2450 d927 d955 d1964
          omega
        have d2486 : (x 9 13).toNat = 0 := by
          have r2487 : (x 21 1).toNat + (x 20 2).toNat + (x 19 3).toNat + (x 18 4).toNat + (x 17 5).toNat + (x 16 6).toNat + (x 15 7).toNat + (x 14 8).toNat + (x 13 9).toNat + (x 12 10).toNat + (x 11 11).toNat + (x 10 12).toNat + (x 9 13).toNat + (x 8 14).toNat = 3 := hcount 22
          have b2488 := hb (x 8 14)
          have b2489 := hb (x 9 13)
          have b2490 := hb (x 10 12)
          have b2491 := hb (x 11 11)
          have b2492 := hb (x 12 10)
          have b2493 := hb (x 13 9)
          have b2494 := hb (x 14 8)
          have b2495 := hb (x 15 7)
          have b2496 := hb (x 16 6)
          have b2497 := hb (x 17 5)
          have b2498 := hb (x 18 4)
          have b2499 := hb (x 19 3)
          have b2500 := hb (x 20 2)
          have b2501 := hb (x 21 1)
          clear * - r2487 b2488 b2489 b2490 b2491 b2492 b2493 b2494 b2495 b2496 b2497 b2498 b2499 b2500 b2501 d2454 d2419 d2309 d2190 d2378 d2394 d2423 d2450 d927 d955 d1964 d2470
          omega
        have d2502 : (x 8 14).toNat = 0 := by
          have r2503 : (x 21 1).toNat + (x 20 2).toNat + (x 19 3).toNat + (x 18 4).toNat + (x 17 5).toNat + (x 16 6).toNat + (x 15 7).toNat + (x 14 8).toNat + (x 13 9).toNat + (x 12 10).toNat + (x 11 11).toNat + (x 10 12).toNat + (x 9 13).toNat + (x 8 14).toNat = 3 := hcount 22
          have b2504 := hb (x 8 14)
          have b2505 := hb (x 9 13)
          have b2506 := hb (x 10 12)
          have b2507 := hb (x 11 11)
          have b2508 := hb (x 12 10)
          have b2509 := hb (x 13 9)
          have b2510 := hb (x 14 8)
          have b2511 := hb (x 15 7)
          have b2512 := hb (x 16 6)
          have b2513 := hb (x 17 5)
          have b2514 := hb (x 18 4)
          have b2515 := hb (x 19 3)
          have b2516 := hb (x 20 2)
          have b2517 := hb (x 21 1)
          clear * - r2503 b2504 b2505 b2506 b2507 b2508 b2509 b2510 b2511 b2512 b2513 b2514 b2515 b2516 b2517 d2454 d2419 d2309 d2190 d2378 d2394 d2423 d2450 d927 d955 d1964 d2470 d2486
          omega
        have d2518 : (x 8 1 && x 8 14).toNat = 0 := by
          have r2519 := hand2 (x 8 1) (x 8 14)
          have b2520 := hb (x 8 14)
          have b2521 := hb (x 8 1 && x 8 14)
          clear * - r2519 b2520 b2521 d2502
          omega
        have d2522 : (x 7 2).toNat = 1 := by
          have r2523 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := hcov13 9
          have b2524 := hb (x 7 2)
          have b2525 := hb (x 9 13)
          have b2526 := hb (x 8 1 && x 8 14)
          clear * - r2523 b2524 b2525 b2526 d2486 d2518
          omega
        have d2527 : (x 7 14).toNat = 1 := by
          have r2528 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
          have b2529 := hb (x 7 2)
          have b2530 := hb (x 7 14)
          clear * - r2528 b2529 b2530 d2522
          omega
        have d2531 : (x 20 1).toNat = 0 := by
          have r2532 : (x 20 1).toNat + (x 19 2).toNat + (x 18 3).toNat + (x 17 4).toNat + (x 16 5).toNat + (x 15 6).toNat + (x 14 7).toNat + (x 13 8).toNat + (x 12 9).toNat + (x 11 10).toNat + (x 10 11).toNat + (x 9 12).toNat + (x 8 13).toNat + (x 7 14).toNat = 3 := hcount 21
          have b2533 := hb (x 7 14)
          have b2534 := hb (x 8 13)
          have b2535 := hb (x 9 12)
          have b2536 := hb (x 10 11)
          have b2537 := hb (x 11 10)
          have b2538 := hb (x 12 9)
          have b2539 := hb (x 13 8)
          have b2540 := hb (x 14 7)
          have b2541 := hb (x 15 6)
          have b2542 := hb (x 16 5)
          have b2543 := hb (x 17 4)
          have b2544 := hb (x 18 3)
          have b2545 := hb (x 19 2)
          have b2546 := hb (x 20 1)
          clear * - r2532 b2533 b2534 b2535 b2536 b2537 b2538 b2539 b2540 b2541 b2542 b2543 b2544 b2545 b2546 d2374 d1120 d1148 d988 d1647 d2527
          omega
        have d2547 : (x 20 1 && x 20 11).toNat = 0 := by
          have r2548 := hand1 (x 20 1) (x 20 11)
          have b2549 := hb (x 20 1)
          have b2550 := hb (x 20 1 && x 20 11)
          clear * - r2548 b2549 b2550 d2531
          omega
        have d2551 : (x 18 3 && x 18 13).toNat = 1 := by
          have r2552 : 1 ≤ (x 21 10).toNat + (x 20 1 && x 20 11).toNat + (x 19 2 && x 19 12).toNat + (x 18 3 && x 18 13).toNat + (x 17 4 && x 17 14).toNat + (x 16 5).toNat := hcov10 21
          have b2553 := hb (x 16 5)
          have b2554 := hb (x 21 10)
          have b2555 := hb (x 20 1 && x 20 11)
          have b2556 := hb (x 19 2 && x 19 12)
          have b2557 := hb (x 18 3 && x 18 13)
          have b2558 := hb (x 17 4 && x 17 14)
          clear * - r2552 b2553 b2554 b2555 b2556 b2557 b2558 d2262 d2547 d2282 d1124 d1148
          omega
        have d2559 : (x 18 3).toNat = 1 := by
          have r2560 := hand1 (x 18 3) (x 18 13)
          have b2561 := hb (x 18 3)
          have b2562 := hb (x 18 3 && x 18 13)
          clear * - r2560 b2561 b2562 d2551
          omega
        have r2563 : (x 20 1).toNat + (x 19 2).toNat + (x 18 3).toNat + (x 17 4).toNat + (x 16 5).toNat + (x 15 6).toNat + (x 14 7).toNat + (x 13 8).toNat + (x 12 9).toNat + (x 11 10).toNat + (x 10 11).toNat + (x 9 12).toNat + (x 8 13).toNat + (x 7 14).toNat = 3 := hcount 21
        have b2564 := hb (x 7 14)
        have b2565 := hb (x 8 13)
        have b2566 := hb (x 9 12)
        have b2567 := hb (x 10 11)
        have b2568 := hb (x 11 10)
        have b2569 := hb (x 12 9)
        have b2570 := hb (x 13 8)
        have b2571 := hb (x 14 7)
        have b2572 := hb (x 15 6)
        have b2573 := hb (x 16 5)
        have b2574 := hb (x 17 4)
        have b2575 := hb (x 18 3)
        have b2576 := hb (x 19 2)
        have b2577 := hb (x 20 1)
        linarith only [r2563, b2564, b2565, b2566, b2567, b2568, b2569, b2570, b2571, b2572, b2573, b2574, b2575, b2576, b2577, d2531, d2374, d2559, d1120, d1148, d988, d1647, d2527]
      · have f2578 : (x 1 2).toNat = 1 := by rw [h696]; rfl
        have d2579 : (x 3 12).toNat = 0 := by
          have r2580 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := hd12 3
          have e2581 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
          have e2582 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
          have b2583 := hb (x 0 3)
          have b2584 := hb (x 1 2)
          have b2585 := hb (x 2 13)
          have b2586 := hb (x 3 12)
          clear * - r2580 e2581 e2582 b2583 b2584 b2585 b2586 f2578 g6
          omega
        have d2587 : (x 3 1 && x 3 12).toNat = 0 := by
          have r2588 := hand2 (x 3 1) (x 3 12)
          have b2589 := hb (x 3 12)
          have b2590 := hb (x 3 1 && x 3 12)
          clear * - r2588 b2589 b2590 d2579
          omega
        have d2591 : (x 3 2 && x 3 12).toNat = 0 := by
          have r2592 := hand2 (x 3 2) (x 3 12)
          have b2593 := hb (x 3 12)
          have b2594 := hb (x 3 2 && x 3 12)
          clear * - r2592 b2593 b2594 d2579
          omega
        have d2595 : (x 3 7 && x 3 12).toNat = 0 := by
          have r2596 := hand2 (x 3 7) (x 3 12)
          have b2597 := hb (x 3 12)
          have b2598 := hb (x 3 7 && x 3 12)
          clear * - r2596 b2597 b2598 d2579
          omega
        have d2599 : (x 3 4).toNat = 0 := by
          have r2600 : (x 3 4).toNat ≤ (x 3 12).toNat := himp _ _ (hp4 3)
          have b2601 := hb (x 3 4)
          have b2602 := hb (x 3 12)
          clear * - r2600 b2601 b2602 d2579
          omega
        have d2603 : (x 2 13).toNat = 0 := by
          have r2604 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := hd12 3
          have e2605 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
          have e2606 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
          have b2607 := hb (x 0 3)
          have b2608 := hb (x 1 2)
          have b2609 := hb (x 2 13)
          have b2610 := hb (x 3 12)
          clear * - r2604 e2605 e2606 b2607 b2608 b2609 b2610 d2579 f2578 g6
          omega
        have d2611 : (x 2 3 && x 2 13).toNat = 0 := by
          have r2612 := hand2 (x 2 3) (x 2 13)
          have b2613 := hb (x 2 13)
          have b2614 := hb (x 2 3 && x 2 13)
          clear * - r2612 b2613 b2614 d2603
          omega
        have d2615 : (x 2 5).toNat = 0 := by
          have r2616 : (x 2 5).toNat ≤ (x 2 13).toNat := himp _ _ (hp5 2)
          have b2617 := hb (x 2 5)
          have b2618 := hb (x 2 13)
          clear * - r2616 b2617 b2618 d2603
          omega
        have d2619 : (x 4 11).toNat = 1 := by
          have r2620 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := hcov11 4
          have b2621 := hb (x 0 4)
          have b2622 := hb (x 4 11)
          have b2623 := hb (x 3 1 && x 3 12)
          have b2624 := hb (x 2 2 && x 2 13)
          have b2625 := hb (x 1 3 && x 1 14)
          clear * - r2620 b2621 b2622 b2623 b2624 b2625 d2587 d454 d324 g7
          omega
        have d2626 : (x 4 3).toNat = 1 := by
          have r2627 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
          have b2628 := hb (x 4 3)
          have b2629 := hb (x 4 11)
          clear * - r2627 b2628 b2629 d2619
          omega
        have d2630 : (x 7 12).toNat = 0 := by
          have r2631 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
          have e2632 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
          have e2633 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
          have b2634 := hb (x 4 3)
          have b2635 := hb (x 5 2)
          have b2636 := hb (x 6 13)
          have b2637 := hb (x 7 12)
          clear * - r2631 e2632 e2633 b2634 b2635 b2636 b2637 d2626
          omega
        have d2638 : (x 6 13).toNat = 0 := by
          have r2639 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
          have e2640 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
          have e2641 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
          have b2642 := hb (x 4 3)
          have b2643 := hb (x 5 2)
          have b2644 := hb (x 6 13)
          have b2645 := hb (x 7 12)
          clear * - r2639 e2640 e2641 b2642 b2643 b2644 b2645 d2630 d2626
          omega
        have d2646 : (x 5 2).toNat = 0 := by
          have r2647 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
          have e2648 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
          have e2649 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
          have b2650 := hb (x 4 3)
          have b2651 := hb (x 5 2)
          have b2652 := hb (x 6 13)
          have b2653 := hb (x 7 12)
          clear * - r2647 e2648 e2649 b2650 b2651 b2652 b2653 d2630 d2638 d2626
          omega
        have d2654 : (x 5 10).toNat = 0 := by
          have r2655 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
          have b2656 := hb (x 5 2)
          have b2657 := hb (x 5 10)
          clear * - r2655 b2656 b2657 d2646
          omega
        have d2658 : (x 5 5 && x 5 10).toNat = 0 := by
          have r2659 := hand2 (x 5 5) (x 5 10)
          have b2660 := hb (x 5 10)
          have b2661 := hb (x 5 5 && x 5 10)
          clear * - r2659 b2660 b2661 d2654
          omega
        have d2662 : (x 7 8).toNat = 0 := by
          have r2663 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
          have e2664 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e2665 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e2666 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e2667 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e2668 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e2669 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have b2670 := hb (x 0 7)
          have b2671 := hb (x 1 6)
          have b2672 := hb (x 2 5)
          have b2673 := hb (x 3 4)
          have b2674 := hb (x 4 11)
          have b2675 := hb (x 5 10)
          have b2676 := hb (x 6 9)
          have b2677 := hb (x 7 8)
          clear * - r2663 e2664 e2665 e2666 e2667 e2668 e2669 b2670 b2671 b2672 b2673 b2674 b2675 b2676 b2677 d2654 d2619 d2599 d2615 g9
          omega
        have d2678 : (x 7 8 && x 7 14).toNat = 0 := by
          have r2679 := hand1 (x 7 8) (x 7 14)
          have b2680 := hb (x 7 8)
          have b2681 := hb (x 7 8 && x 7 14)
          clear * - r2679 b2680 b2681 d2662
          omega
        have d2682 : (x 7 3 && x 7 8).toNat = 0 := by
          have r2683 := hand2 (x 7 3) (x 7 8)
          have b2684 := hb (x 7 8)
          have b2685 := hb (x 7 3 && x 7 8)
          clear * - r2683 b2684 b2685 d2662
          omega
        have d2686 : (x 6 9).toNat = 0 := by
          have r2687 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
          have e2688 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e2689 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e2690 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e2691 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e2692 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e2693 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have b2694 := hb (x 0 7)
          have b2695 := hb (x 1 6)
          have b2696 := hb (x 2 5)
          have b2697 := hb (x 3 4)
          have b2698 := hb (x 4 11)
          have b2699 := hb (x 5 10)
          have b2700 := hb (x 6 9)
          have b2701 := hb (x 7 8)
          clear * - r2687 e2688 e2689 e2690 e2691 e2692 e2693 b2694 b2695 b2696 b2697 b2698 b2699 b2700 b2701 d2662 d2654 d2619 d2599 d2615 g9
          omega
        have d2702 : (x 6 4 && x 6 9).toNat = 0 := by
          have r2703 := hand2 (x 6 4) (x 6 9)
          have b2704 := hb (x 6 9)
          have b2705 := hb (x 6 4 && x 6 9)
          clear * - r2703 b2704 b2705 d2686
          omega
        cases h2706 : x 1 4
        · have f2707 : (x 1 4).toNat = 0 := by rw [h2706]; rfl
          have d2708 : (x 1 4 && x 1 14).toNat = 0 := by
            have r2709 := hand1 (x 1 4) (x 1 14)
            have b2710 := hb (x 1 4)
            have b2711 := hb (x 1 4 && x 1 14)
            clear * - r2709 b2710 b2711 f2707
            omega
          have d2712 : (x 1 1 && x 1 4).toNat = 0 := by
            have r2713 := hand2 (x 1 1) (x 1 4)
            have b2714 := hb (x 1 4)
            have b2715 := hb (x 1 1 && x 1 4)
            clear * - r2713 b2714 b2715 f2707
            omega
          have d2716 : (x 4 1 && x 4 11).toNat = 1 := by
            have r2717 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := hcov10 5
            have b2718 := hb (x 0 5)
            have b2719 := hb (x 5 10)
            have b2720 := hb (x 4 1 && x 4 11)
            have b2721 := hb (x 3 2 && x 3 12)
            have b2722 := hb (x 2 3 && x 2 13)
            have b2723 := hb (x 1 4 && x 1 14)
            clear * - r2717 b2718 b2719 b2720 b2721 b2722 b2723 d2654 d2591 d2611 d2708 g8
            omega
          have d2724 : (x 4 1).toNat = 1 := by
            have r2725 := hand1 (x 4 1) (x 4 11)
            have b2726 := hb (x 4 1)
            have b2727 := hb (x 4 1 && x 4 11)
            clear * - r2725 b2726 b2727 d2716
            omega
          have d2728 : (x 5 14).toNat = 0 := by
            have r2729 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
            have b2730 := hb (x 4 1)
            have b2731 := hb (x 5 14)
            clear * - r2729 b2730 b2731 d2724
            omega
          have d2732 : (x 5 1 && x 5 14).toNat = 0 := by
            have r2733 := hand2 (x 5 1) (x 5 14)
            have b2734 := hb (x 5 14)
            have b2735 := hb (x 5 1 && x 5 14)
            clear * - r2733 b2734 b2735 d2728
            omega
          have d2736 : (x 4 2).toNat = 1 := by
            have r2737 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := hcov13 6
            have b2738 := hb (x 4 2)
            have b2739 := hb (x 6 13)
            have b2740 := hb (x 5 1 && x 5 14)
            clear * - r2737 b2738 b2739 b2740 d2638 d2732
            omega
          have d2741 : (x 4 14).toNat = 1 := by
            have r2742 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
            have b2743 := hb (x 4 2)
            have b2744 := hb (x 4 14)
            clear * - r2742 b2743 b2744 d2736
            omega
          have d2745 : (x 3 1).toNat = 0 := by
            have r2746 : (x 4 14).toNat + (x 3 1).toNat = 1 := hd14 4
            have b2747 := hb (x 3 1)
            have b2748 := hb (x 4 14)
            clear * - r2746 b2747 b2748 d2741
            omega
          have d2749 : (x 3 1 && x 3 14).toNat = 0 := by
            have r2750 := hand1 (x 3 1) (x 3 14)
            have b2751 := hb (x 3 1)
            have b2752 := hb (x 3 1 && x 3 14)
            clear * - r2750 b2751 b2752 d2745
            omega
          have d2753 : (x 4 13).toNat = 1 := by
            have r2754 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
            have b2755 := hb (x 2 2)
            have b2756 := hb (x 4 13)
            have b2757 := hb (x 3 1 && x 3 14)
            clear * - r2754 b2755 b2756 b2757 d2749 d450
            omega
          have d2758 : (x 5 12).toNat = 0 := by
            have r2759 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
            have e2760 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e2761 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b2762 := hb (x 2 3)
            have b2763 := hb (x 3 2)
            have b2764 := hb (x 4 13)
            have b2765 := hb (x 5 12)
            clear * - r2759 e2760 e2761 b2762 b2763 b2764 b2765 d2753
            omega
          have d2766 : (x 3 2).toNat = 0 := by
            have r2767 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
            have e2768 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e2769 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b2770 := hb (x 2 3)
            have b2771 := hb (x 3 2)
            have b2772 := hb (x 4 13)
            have b2773 := hb (x 5 12)
            clear * - r2767 e2768 e2769 b2770 b2771 b2772 b2773 d2758 d2753
            omega
          have d2774 : (x 3 10).toNat = 0 := by
            have r2775 : (x 3 10).toNat ≤ (x 3 2).toNat := himp _ _ (hp10 3)
            have b2776 := hb (x 3 2)
            have b2777 := hb (x 3 10)
            clear * - r2775 b2776 b2777 d2766
            omega
          have d2778 : (x 3 1 && x 3 10).toNat = 0 := by
            have r2779 := hand2 (x 3 1) (x 3 10)
            have b2780 := hb (x 3 10)
            have b2781 := hb (x 3 1 && x 3 10)
            clear * - r2779 b2780 b2781 d2774
            omega
          have d2782 : (x 2 3).toNat = 0 := by
            have r2783 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
            have e2784 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e2785 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b2786 := hb (x 2 3)
            have b2787 := hb (x 3 2)
            have b2788 := hb (x 4 13)
            have b2789 := hb (x 5 12)
            clear * - r2783 e2784 e2785 b2786 b2787 b2788 b2789 d2758 d2753 d2766
            omega
          have d2790 : (x 2 11).toNat = 0 := by
            have r2791 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
            have b2792 := hb (x 2 3)
            have b2793 := hb (x 2 11)
            clear * - r2791 b2792 b2793 d2782
            omega
          have d2794 : (x 3 1 && x 3 11).toNat = 0 := by
            have r2795 := hand1 (x 3 1) (x 3 11)
            have b2796 := hb (x 3 1)
            have b2797 := hb (x 3 1 && x 3 11)
            clear * - r2795 b2796 b2797 d2745
            omega
          have d2798 : (x 3 9).toNat = 0 := by
            have r2799 : (x 3 9).toNat ≤ (x 3 1).toNat := himp _ _ (hp9 3)
            have b2800 := hb (x 3 1)
            have b2801 := hb (x 3 9)
            clear * - r2799 b2800 b2801 d2745
            omega
          have d2802 : (x 6 12).toNat = 0 := by
            have r2803 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
            have e2804 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
            have e2805 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
            have b2806 := hb (x 3 3)
            have b2807 := hb (x 4 2)
            have b2808 := hb (x 5 13)
            have b2809 := hb (x 6 12)
            clear * - r2803 e2804 e2805 b2806 b2807 b2808 b2809 d2736
            omega
          have d2810 : (x 6 6 && x 6 12).toNat = 0 := by
            have r2811 := hand2 (x 6 6) (x 6 12)
            have b2812 := hb (x 6 12)
            have b2813 := hb (x 6 6 && x 6 12)
            clear * - r2811 b2812 b2813 d2802
            omega
          have d2814 : (x 6 4).toNat = 0 := by
            have r2815 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
            have b2816 := hb (x 6 4)
            have b2817 := hb (x 6 12)
            clear * - r2815 b2816 b2817 d2802
            omega
          have d2818 : (x 5 13).toNat = 0 := by
            have r2819 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
            have e2820 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
            have e2821 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
            have b2822 := hb (x 3 3)
            have b2823 := hb (x 4 2)
            have b2824 := hb (x 5 13)
            have b2825 := hb (x 6 12)
            clear * - r2819 e2820 e2821 b2822 b2823 b2824 b2825 d2802 d2736
            omega
          have d2826 : (x 5 7 && x 5 13).toNat = 0 := by
            have r2827 := hand2 (x 5 7) (x 5 13)
            have b2828 := hb (x 5 13)
            have b2829 := hb (x 5 7 && x 5 13)
            clear * - r2827 b2828 b2829 d2818
            omega
          have d2830 : (x 5 5).toNat = 0 := by
            have r2831 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
            have b2832 := hb (x 5 5)
            have b2833 := hb (x 5 13)
            clear * - r2831 b2832 b2833 d2818
            omega
          have d2834 : (x 3 3).toNat = 0 := by
            have r2835 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
            have e2836 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
            have e2837 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
            have b2838 := hb (x 3 3)
            have b2839 := hb (x 4 2)
            have b2840 := hb (x 5 13)
            have b2841 := hb (x 6 12)
            clear * - r2835 e2836 e2837 b2838 b2839 b2840 b2841 d2802 d2818 d2736
            omega
          have d2842 : (x 3 11).toNat = 0 := by
            have r2843 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
            have b2844 := hb (x 3 3)
            have b2845 := hb (x 3 11)
            clear * - r2843 b2844 b2845 d2834
            omega
          have d2846 : (x 4 10).toNat = 1 := by
            have r2847 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := hcov10 4
            have b2848 := hb (x (-1) 5)
            have b2849 := hb (x 4 10)
            have b2850 := hb (x 3 1 && x 3 11)
            have b2851 := hb (x 2 2 && x 2 12)
            have b2852 := hb (x 1 3 && x 1 13)
            have b2853 := hb (x 0 4 && x 0 14)
            clear * - r2847 b2848 b2849 b2850 b2851 b2852 b2853 d2794 d458 d328 g26 g3
            omega
          have d2854 : (x 6 8).toNat = 0 := by
            have r2855 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
            have e2856 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
            have e2857 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
            have e2858 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
            have e2859 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
            have e2860 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
            have e2861 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
            have b2862 := hb (x (-1) 7)
            have b2863 := hb (x 0 6)
            have b2864 := hb (x 1 5)
            have b2865 := hb (x 2 4)
            have b2866 := hb (x 3 11)
            have b2867 := hb (x 4 10)
            have b2868 := hb (x 5 9)
            have b2869 := hb (x 6 8)
            clear * - r2855 e2856 e2857 e2858 e2859 e2860 e2861 b2862 b2863 b2864 b2865 b2866 b2867 b2868 b2869 d2846 d2842 d544 f349
            omega
          have d2870 : (x 5 9).toNat = 0 := by
            have r2871 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
            have e2872 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
            have e2873 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
            have e2874 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
            have e2875 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
            have e2876 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
            have e2877 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
            have b2878 := hb (x (-1) 7)
            have b2879 := hb (x 0 6)
            have b2880 := hb (x 1 5)
            have b2881 := hb (x 2 4)
            have b2882 := hb (x 3 11)
            have b2883 := hb (x 4 10)
            have b2884 := hb (x 5 9)
            have b2885 := hb (x 6 8)
            clear * - r2871 e2872 e2873 e2874 e2875 e2876 e2877 b2878 b2879 b2880 b2881 b2882 b2883 b2884 b2885 d2854 d2846 d2842 d544 f349
            omega
          have d2886 : (x 13 1).toNat = 0 := by
            have r2887 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := hcount 14
            have b2888 := hb (x 0 14)
            have b2889 := hb (x 1 13)
            have b2890 := hb (x 2 12)
            have b2891 := hb (x 3 11)
            have b2892 := hb (x 4 10)
            have b2893 := hb (x 5 9)
            have b2894 := hb (x 6 8)
            have b2895 := hb (x 7 7)
            have b2896 := hb (x 8 6)
            have b2897 := hb (x 9 5)
            have b2898 := hb (x 10 4)
            have b2899 := hb (x 11 3)
            have b2900 := hb (x 12 2)
            have b2901 := hb (x 13 1)
            clear * - r2887 b2888 b2889 b2890 b2891 b2892 b2893 b2894 b2895 b2896 b2897 b2898 b2899 b2900 b2901 d2854 d2870 d2846 d2842 d532 d527 g13
            omega
          have d2902 : (x 13 1 && x 13 14).toNat = 0 := by
            have r2903 := hand1 (x 13 1) (x 13 14)
            have b2904 := hb (x 13 1)
            have b2905 := hb (x 13 1 && x 13 14)
            clear * - r2903 b2904 b2905 d2886
            omega
          have d2906 : (x 13 13).toNat = 0 := by
            have r2907 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
            have b2908 := hb (x 13 1)
            have b2909 := hb (x 13 13)
            clear * - r2907 b2908 b2909 d2886
            omega
          have d2910 : (x 13 5).toNat = 0 := by
            have r2911 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
            have b2912 := hb (x 13 5)
            have b2913 := hb (x 13 13)
            clear * - r2911 b2912 b2913 d2906
            omega
          have d2914 : (x 12 2).toNat = 0 := by
            have r2915 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := hcount 14
            have b2916 := hb (x 0 14)
            have b2917 := hb (x 1 13)
            have b2918 := hb (x 2 12)
            have b2919 := hb (x 3 11)
            have b2920 := hb (x 4 10)
            have b2921 := hb (x 5 9)
            have b2922 := hb (x 6 8)
            have b2923 := hb (x 7 7)
            have b2924 := hb (x 8 6)
            have b2925 := hb (x 9 5)
            have b2926 := hb (x 10 4)
            have b2927 := hb (x 11 3)
            have b2928 := hb (x 12 2)
            have b2929 := hb (x 13 1)
            clear * - r2915 b2916 b2917 b2918 b2919 b2920 b2921 b2922 b2923 b2924 b2925 b2926 b2927 b2928 b2929 d2886 d2854 d2870 d2846 d2842 d532 d527 g13
            omega
          have d2930 : (x 14 13).toNat = 1 := by
            have r2931 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
            have b2932 := hb (x 12 2)
            have b2933 := hb (x 14 13)
            have b2934 := hb (x 13 1 && x 13 14)
            clear * - r2931 b2932 b2933 b2934 d2902 d2914
            omega
          have d2935 : (x 14 1).toNat = 1 := by
            have r2936 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
            have b2937 := hb (x 14 1)
            have b2938 := hb (x 14 13)
            clear * - r2936 b2937 b2938 d2930
            omega
          have d2939 : (x 15 14).toNat = 0 := by
            have r2940 : (x 15 14).toNat + (x 14 1).toNat = 1 := hd14 15
            have b2941 := hb (x 14 1)
            have b2942 := hb (x 15 14)
            clear * - r2940 b2941 b2942 d2935
            omega
          have d2943 : (x 15 1 && x 15 14).toNat = 0 := by
            have r2944 := hand2 (x 15 1) (x 15 14)
            have b2945 := hb (x 15 14)
            have b2946 := hb (x 15 1 && x 15 14)
            clear * - r2944 b2945 b2946 d2939
            omega
          have d2947 : (x 15 5 && x 15 14).toNat = 0 := by
            have r2948 := hand2 (x 15 5) (x 15 14)
            have b2949 := hb (x 15 14)
            have b2950 := hb (x 15 5 && x 15 14)
            clear * - r2948 b2949 b2950 d2939
            omega
          have d2951 : (x 15 6).toNat = 0 := by
            have r2952 : (x 15 6).toNat ≤ (x 15 14).toNat := himp _ _ (hp6 15)
            have b2953 := hb (x 15 6)
            have b2954 := hb (x 15 14)
            clear * - r2952 b2953 b2954 d2939
            omega
          have d2955 : (x 15 2).toNat = 0 := by
            have r2956 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
            have b2957 := hb (x 15 2)
            have b2958 := hb (x 15 14)
            clear * - r2956 b2957 b2958 d2939
            omega
          have d2959 : (x 15 10).toNat = 0 := by
            have r2960 : (x 15 10).toNat ≤ (x 15 2).toNat := himp _ _ (hp10 15)
            have b2961 := hb (x 15 2)
            have b2962 := hb (x 15 10)
            clear * - r2960 b2961 b2962 d2955
            omega
          have d2963 : (x 13 2).toNat = 0 := by
            have r2964 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := hcount 15
            have b2965 := hb (x 1 14)
            have b2966 := hb (x 2 13)
            have b2967 := hb (x 3 12)
            have b2968 := hb (x 4 11)
            have b2969 := hb (x 5 10)
            have b2970 := hb (x 6 9)
            have b2971 := hb (x 7 8)
            have b2972 := hb (x 8 7)
            have b2973 := hb (x 9 6)
            have b2974 := hb (x 10 5)
            have b2975 := hb (x 11 4)
            have b2976 := hb (x 12 3)
            have b2977 := hb (x 13 2)
            have b2978 := hb (x 14 1)
            clear * - r2964 b2965 b2966 b2967 b2968 b2969 b2970 b2971 b2972 b2973 b2974 b2975 b2976 b2977 b2978 d2935 d2662 d2686 d2654 d2619 d2579 d2603 g15
            omega
          have d2979 : (x 13 2 && x 13 12).toNat = 0 := by
            have r2980 := hand1 (x 13 2) (x 13 12)
            have b2981 := hb (x 13 2)
            have b2982 := hb (x 13 2 && x 13 12)
            clear * - r2980 b2981 b2982 d2963
            omega
          have d2983 : (x 13 2 && x 13 8).toNat = 0 := by
            have r2984 := hand1 (x 13 2) (x 13 8)
            have b2985 := hb (x 13 2)
            have b2986 := hb (x 13 2 && x 13 8)
            clear * - r2984 b2985 b2986 d2963
            omega
          have d2987 : (x 12 3).toNat = 0 := by
            have r2988 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := hcount 15
            have b2989 := hb (x 1 14)
            have b2990 := hb (x 2 13)
            have b2991 := hb (x 3 12)
            have b2992 := hb (x 4 11)
            have b2993 := hb (x 5 10)
            have b2994 := hb (x 6 9)
            have b2995 := hb (x 7 8)
            have b2996 := hb (x 8 7)
            have b2997 := hb (x 9 6)
            have b2998 := hb (x 10 5)
            have b2999 := hb (x 11 4)
            have b3000 := hb (x 12 3)
            have b3001 := hb (x 13 2)
            have b3002 := hb (x 14 1)
            clear * - r2988 b2989 b2990 b2991 b2992 b2993 b2994 b2995 b2996 b2997 b2998 b2999 b3000 b3001 b3002 d2935 d2963 d2662 d2686 d2654 d2619 d2579 d2603 g15
            omega
          have d3003 : (x 12 3 && x 12 13).toNat = 0 := by
            have r3004 := hand1 (x 12 3) (x 12 13)
            have b3005 := hb (x 12 3)
            have b3006 := hb (x 12 3 && x 12 13)
            clear * - r3004 b3005 b3006 d2987
            omega
          have d3007 : (x 12 3 && x 12 9).toNat = 0 := by
            have r3008 := hand1 (x 12 3) (x 12 9)
            have b3009 := hb (x 12 3)
            have b3010 := hb (x 12 3 && x 12 9)
            clear * - r3008 b3009 b3010 d2987
            omega
          have d3011 : (x 11 4).toNat = 0 := by
            have r3012 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := hcount 15
            have b3013 := hb (x 1 14)
            have b3014 := hb (x 2 13)
            have b3015 := hb (x 3 12)
            have b3016 := hb (x 4 11)
            have b3017 := hb (x 5 10)
            have b3018 := hb (x 6 9)
            have b3019 := hb (x 7 8)
            have b3020 := hb (x 8 7)
            have b3021 := hb (x 9 6)
            have b3022 := hb (x 10 5)
            have b3023 := hb (x 11 4)
            have b3024 := hb (x 12 3)
            have b3025 := hb (x 13 2)
            have b3026 := hb (x 14 1)
            clear * - r3012 b3013 b3014 b3015 b3016 b3017 b3018 b3019 b3020 b3021 b3022 b3023 b3024 b3025 b3026 d2935 d2963 d2987 d2662 d2686 d2654 d2619 d2579 d2603 g15
            omega
          have d3027 : (x 11 4 && x 11 14).toNat = 0 := by
            have r3028 := hand1 (x 11 4) (x 11 14)
            have b3029 := hb (x 11 4)
            have b3030 := hb (x 11 4 && x 11 14)
            clear * - r3028 b3029 b3030 d3011
            omega
          have d3031 : (x 11 4 && x 11 10).toNat = 0 := by
            have r3032 := hand1 (x 11 4) (x 11 10)
            have b3033 := hb (x 11 4)
            have b3034 := hb (x 11 4 && x 11 10)
            clear * - r3032 b3033 b3034 d3011
            omega
          have d3035 : (x 10 5).toNat = 0 := by
            have r3036 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := hcount 15
            have b3037 := hb (x 1 14)
            have b3038 := hb (x 2 13)
            have b3039 := hb (x 3 12)
            have b3040 := hb (x 4 11)
            have b3041 := hb (x 5 10)
            have b3042 := hb (x 6 9)
            have b3043 := hb (x 7 8)
            have b3044 := hb (x 8 7)
            have b3045 := hb (x 9 6)
            have b3046 := hb (x 10 5)
            have b3047 := hb (x 11 4)
            have b3048 := hb (x 12 3)
            have b3049 := hb (x 13 2)
            have b3050 := hb (x 14 1)
            clear * - r3036 b3037 b3038 b3039 b3040 b3041 b3042 b3043 b3044 b3045 b3046 b3047 b3048 b3049 b3050 d2935 d2963 d2987 d3011 d2662 d2686 d2654 d2619 d2579 d2603 g15
            omega
          have d3051 : (x 10 5 && x 10 11).toNat = 0 := by
            have r3052 := hand1 (x 10 5) (x 10 11)
            have b3053 := hb (x 10 5)
            have b3054 := hb (x 10 5 && x 10 11)
            clear * - r3052 b3053 b3054 d3035
            omega
          have d3055 : (x 14 1 && x 14 11).toNat = 1 := by
            have r3056 : 1 ≤ (x 15 10).toNat + (x 14 1 && x 14 11).toNat + (x 13 2 && x 13 12).toNat + (x 12 3 && x 12 13).toNat + (x 11 4 && x 11 14).toNat + (x 10 5).toNat := hcov10 15
            have b3057 := hb (x 10 5)
            have b3058 := hb (x 15 10)
            have b3059 := hb (x 14 1 && x 14 11)
            have b3060 := hb (x 13 2 && x 13 12)
            have b3061 := hb (x 12 3 && x 12 13)
            have b3062 := hb (x 11 4 && x 11 14)
            clear * - r3056 b3057 b3058 b3059 b3060 b3061 b3062 d2959 d2979 d3003 d3027 d3035
            omega
          have d3063 : (x 14 11).toNat = 1 := by
            have r3064 := hand2 (x 14 1) (x 14 11)
            have b3065 := hb (x 14 11)
            have b3066 := hb (x 14 1 && x 14 11)
            clear * - r3064 b3065 b3066 d3055
            omega
          have d3067 : (x 14 3).toNat = 1 := by
            have r3068 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
            have b3069 := hb (x 14 3)
            have b3070 := hb (x 14 11)
            clear * - r3068 b3069 b3070 d3063
            omega
          have d3071 : (x 17 12).toNat = 0 := by
            have r3072 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
            have e3073 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
            have e3074 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
            have b3075 := hb (x 14 3)
            have b3076 := hb (x 15 2)
            have b3077 := hb (x 16 13)
            have b3078 := hb (x 17 12)
            clear * - r3072 e3073 e3074 b3075 b3076 b3077 b3078 d2955 d3067
            omega
          have d3079 : (x 17 3 && x 17 12).toNat = 0 := by
            have r3080 := hand2 (x 17 3) (x 17 12)
            have b3081 := hb (x 17 12)
            have b3082 := hb (x 17 3 && x 17 12)
            clear * - r3080 b3081 b3082 d3071
            omega
          have d3083 : (x 17 4).toNat = 0 := by
            have r3084 : (x 17 4).toNat ≤ (x 17 12).toNat := himp _ _ (hp4 17)
            have b3085 := hb (x 17 4)
            have b3086 := hb (x 17 12)
            clear * - r3084 b3085 b3086 d3071
            omega
          have d3087 : (x 16 13).toNat = 0 := by
            have r3088 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
            have e3089 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
            have e3090 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
            have b3091 := hb (x 14 3)
            have b3092 := hb (x 15 2)
            have b3093 := hb (x 16 13)
            have b3094 := hb (x 17 12)
            clear * - r3088 e3089 e3090 b3091 b3092 b3093 b3094 d3071 d2955 d3067
            omega
          have d3095 : (x 16 4 && x 16 13).toNat = 0 := by
            have r3096 := hand2 (x 16 4) (x 16 13)
            have b3097 := hb (x 16 13)
            have b3098 := hb (x 16 4 && x 16 13)
            clear * - r3096 b3097 b3098 d3087
            omega
          have d3099 : (x 16 5).toNat = 0 := by
            have r3100 : (x 16 5).toNat ≤ (x 16 13).toNat := himp _ _ (hp5 16)
            have b3101 := hb (x 16 5)
            have b3102 := hb (x 16 13)
            clear * - r3100 b3101 b3102 d3087
            omega
          have d3103 : (x 14 2).toNat = 1 := by
            have r3104 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := hcov13 16
            have b3105 := hb (x 14 2)
            have b3106 := hb (x 16 13)
            have b3107 := hb (x 15 1 && x 15 14)
            clear * - r3104 b3105 b3106 b3107 d3087 d2943
            omega
          have d3108 : (x 16 12).toNat = 0 := by
            have r3109 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
            have e3110 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
            have e3111 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
            have b3112 := hb (x 13 3)
            have b3113 := hb (x 14 2)
            have b3114 := hb (x 15 13)
            have b3115 := hb (x 16 12)
            clear * - r3109 e3110 e3111 b3112 b3113 b3114 b3115 d3103
            omega
          have d3116 : (x 16 2 && x 16 12).toNat = 0 := by
            have r3117 := hand2 (x 16 2) (x 16 12)
            have b3118 := hb (x 16 12)
            have b3119 := hb (x 16 2 && x 16 12)
            clear * - r3117 b3118 b3119 d3108
            omega
          have d3120 : (x 16 4).toNat = 0 := by
            have r3121 : (x 16 4).toNat ≤ (x 16 12).toNat := himp _ _ (hp4 16)
            have b3122 := hb (x 16 4)
            have b3123 := hb (x 16 12)
            clear * - r3121 b3122 b3123 d3108
            omega
          have d3124 : (x 15 13).toNat = 0 := by
            have r3125 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
            have e3126 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
            have e3127 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
            have b3128 := hb (x 13 3)
            have b3129 := hb (x 14 2)
            have b3130 := hb (x 15 13)
            have b3131 := hb (x 16 12)
            clear * - r3125 e3126 e3127 b3128 b3129 b3130 b3131 d3108 d3103
            omega
          have d3132 : (x 15 3 && x 15 13).toNat = 0 := by
            have r3133 := hand2 (x 15 3) (x 15 13)
            have b3134 := hb (x 15 13)
            have b3135 := hb (x 15 3 && x 15 13)
            clear * - r3133 b3134 b3135 d3124
            omega
          have d3136 : (x 15 5).toNat = 0 := by
            have r3137 : (x 15 5).toNat ≤ (x 15 13).toNat := himp _ _ (hp5 15)
            have b3138 := hb (x 15 5)
            have b3139 := hb (x 15 13)
            clear * - r3137 b3138 b3139 d3124
            omega
          have d3140 : (x 9 6).toNat = 0 := by
            have r3141 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := hcount 15
            have b3142 := hb (x 1 14)
            have b3143 := hb (x 2 13)
            have b3144 := hb (x 3 12)
            have b3145 := hb (x 4 11)
            have b3146 := hb (x 5 10)
            have b3147 := hb (x 6 9)
            have b3148 := hb (x 7 8)
            have b3149 := hb (x 8 7)
            have b3150 := hb (x 9 6)
            have b3151 := hb (x 10 5)
            have b3152 := hb (x 11 4)
            have b3153 := hb (x 12 3)
            have b3154 := hb (x 13 2)
            have b3155 := hb (x 14 1)
            clear * - r3141 b3142 b3143 b3144 b3145 b3146 b3147 b3148 b3149 b3150 b3151 b3152 b3153 b3154 b3155 d2935 d2963 d2987 d3011 d3035 d2662 d2686 d2654 d2619 d2579 d2603 g15
            omega
          have d3156 : (x 9 6 && x 9 12).toNat = 0 := by
            have r3157 := hand1 (x 9 6) (x 9 12)
            have b3158 := hb (x 9 6)
            have b3159 := hb (x 9 6 && x 9 12)
            clear * - r3157 b3158 b3159 d3140
            omega
          have d3160 : (x 9 1 && x 9 6).toNat = 0 := by
            have r3161 := hand2 (x 9 1) (x 9 6)
            have b3162 := hb (x 9 6)
            have b3163 := hb (x 9 1 && x 9 6)
            clear * - r3161 b3162 b3163 d3140
            omega
          have d3164 : (x 8 7).toNat = 0 := by
            have r3165 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := hcount 15
            have b3166 := hb (x 1 14)
            have b3167 := hb (x 2 13)
            have b3168 := hb (x 3 12)
            have b3169 := hb (x 4 11)
            have b3170 := hb (x 5 10)
            have b3171 := hb (x 6 9)
            have b3172 := hb (x 7 8)
            have b3173 := hb (x 8 7)
            have b3174 := hb (x 9 6)
            have b3175 := hb (x 10 5)
            have b3176 := hb (x 11 4)
            have b3177 := hb (x 12 3)
            have b3178 := hb (x 13 2)
            have b3179 := hb (x 14 1)
            clear * - r3165 b3166 b3167 b3168 b3169 b3170 b3171 b3172 b3173 b3174 b3175 b3176 b3177 b3178 b3179 d2935 d2963 d2987 d3011 d3035 d3140 d2662 d2686 d2654 d2619 d2579 d2603 g15
            omega
          have d3180 : (x 8 7 && x 8 13).toNat = 0 := by
            have r3181 := hand1 (x 8 7) (x 8 13)
            have b3182 := hb (x 8 7)
            have b3183 := hb (x 8 7 && x 8 13)
            clear * - r3181 b3182 b3183 d3164
            omega
          have d3184 : (x 14 1 && x 14 7).toNat = 1 := by
            have r3185 : 1 ≤ (x 15 6).toNat + (x 14 1 && x 14 7).toNat + (x 13 2 && x 13 8).toNat + (x 12 3 && x 12 9).toNat + (x 11 4 && x 11 10).toNat + (x 10 5 && x 10 11).toNat + (x 9 6 && x 9 12).toNat + (x 8 7 && x 8 13).toNat + (x 7 8 && x 7 14).toNat + (x 6 9).toNat := hcov6 15
            have b3186 := hb (x 6 9)
            have b3187 := hb (x 15 6)
            have b3188 := hb (x 14 1 && x 14 7)
            have b3189 := hb (x 13 2 && x 13 8)
            have b3190 := hb (x 12 3 && x 12 9)
            have b3191 := hb (x 11 4 && x 11 10)
            have b3192 := hb (x 10 5 && x 10 11)
            have b3193 := hb (x 9 6 && x 9 12)
            have b3194 := hb (x 8 7 && x 8 13)
            have b3195 := hb (x 7 8 && x 7 14)
            clear * - r3185 b3186 b3187 b3188 b3189 b3190 b3191 b3192 b3193 b3194 b3195 d2951 d2983 d3007 d3031 d3051 d3156 d3180 d2678 d2686
            omega
          have d3196 : (x 14 7).toNat = 1 := by
            have r3197 := hand2 (x 14 1) (x 14 7)
            have b3198 := hb (x 14 7)
            have b3199 := hb (x 14 1 && x 14 7)
            clear * - r3197 b3198 b3199 d3184
            omega
          have d3200 : (x 21 8).toNat = 0 := by
            have r3201 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := hd8 21
            have e3202 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
            have e3203 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
            have e3204 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
            have e3205 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
            have e3206 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
            have e3207 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
            have b3208 := hb (x 14 7)
            have b3209 := hb (x 15 6)
            have b3210 := hb (x 16 5)
            have b3211 := hb (x 17 4)
            have b3212 := hb (x 18 11)
            have b3213 := hb (x 19 10)
            have b3214 := hb (x 20 9)
            have b3215 := hb (x 21 8)
            clear * - r3201 e3202 e3203 e3204 e3205 e3206 e3207 b3208 b3209 b3210 b3211 b3212 b3213 b3214 b3215 d3083 d3099 d2951 d3196
            omega
          have d3216 : (x 20 9).toNat = 0 := by
            have r3217 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := hd8 21
            have e3218 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
            have e3219 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
            have e3220 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
            have e3221 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
            have e3222 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
            have e3223 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
            have b3224 := hb (x 14 7)
            have b3225 := hb (x 15 6)
            have b3226 := hb (x 16 5)
            have b3227 := hb (x 17 4)
            have b3228 := hb (x 18 11)
            have b3229 := hb (x 19 10)
            have b3230 := hb (x 20 9)
            have b3231 := hb (x 21 8)
            clear * - r3217 e3218 e3219 e3220 e3221 e3222 e3223 b3224 b3225 b3226 b3227 b3228 b3229 b3230 b3231 d3200 d3083 d3099 d2951 d3196
            omega
          have d3232 : (x 19 10).toNat = 0 := by
            have r3233 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := hd8 21
            have e3234 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
            have e3235 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
            have e3236 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
            have e3237 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
            have e3238 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
            have e3239 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
            have b3240 := hb (x 14 7)
            have b3241 := hb (x 15 6)
            have b3242 := hb (x 16 5)
            have b3243 := hb (x 17 4)
            have b3244 := hb (x 18 11)
            have b3245 := hb (x 19 10)
            have b3246 := hb (x 20 9)
            have b3247 := hb (x 21 8)
            clear * - r3233 e3234 e3235 e3236 e3237 e3238 e3239 b3240 b3241 b3242 b3243 b3244 b3245 b3246 b3247 d3200 d3216 d3083 d3099 d2951 d3196
            omega
          have d3248 : (x 19 1 && x 19 10).toNat = 0 := by
            have r3249 := hand2 (x 19 1) (x 19 10)
            have b3250 := hb (x 19 10)
            have b3251 := hb (x 19 1 && x 19 10)
            clear * - r3249 b3250 b3251 d3232
            omega
          have d3252 : (x 18 11).toNat = 0 := by
            have r3253 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := hd8 21
            have e3254 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
            have e3255 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
            have e3256 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
            have e3257 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
            have e3258 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
            have e3259 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
            have b3260 := hb (x 14 7)
            have b3261 := hb (x 15 6)
            have b3262 := hb (x 16 5)
            have b3263 := hb (x 17 4)
            have b3264 := hb (x 18 11)
            have b3265 := hb (x 19 10)
            have b3266 := hb (x 20 9)
            have b3267 := hb (x 21 8)
            clear * - r3253 e3254 e3255 e3256 e3257 e3258 e3259 b3260 b3261 b3262 b3263 b3264 b3265 b3266 b3267 d3200 d3216 d3232 d3083 d3099 d2951 d3196
            omega
          have d3268 : (x 18 2 && x 18 11).toNat = 0 := by
            have r3269 := hand2 (x 18 2) (x 18 11)
            have b3270 := hb (x 18 11)
            have b3271 := hb (x 18 2 && x 18 11)
            clear * - r3269 b3270 b3271 d3252
            omega
          have d3272 : (x 14 6).toNat = 1 := by
            have r3273 : 1 ≤ (x 20 9).toNat + (x 19 1 && x 19 10).toNat + (x 18 2 && x 18 11).toNat + (x 17 3 && x 17 12).toNat + (x 16 4 && x 16 13).toNat + (x 15 5 && x 15 14).toNat + (x 14 6).toNat := hcov9 20
            have b3274 := hb (x 14 6)
            have b3275 := hb (x 20 9)
            have b3276 := hb (x 19 1 && x 19 10)
            have b3277 := hb (x 18 2 && x 18 11)
            have b3278 := hb (x 17 3 && x 17 12)
            have b3279 := hb (x 16 4 && x 16 13)
            have b3280 := hb (x 15 5 && x 15 14)
            clear * - r3273 b3274 b3275 b3276 b3277 b3278 b3279 b3280 d3216 d3248 d3268 d3079 d3095 d2947
            omega
          have d3281 : (x 20 8).toNat = 0 := by
            have r3282 : (x 20 8).toNat + (x 19 1 && x 19 9).toNat + (x 18 2 && x 18 10).toNat + (x 17 3 && x 17 11).toNat + (x 16 4 && x 16 12).toNat + (x 15 5 && x 15 13).toNat + (x 14 6 && x 14 14).toNat + (x 13 7).toNat = 1 := hd8 20
            have e3283 : (x 19 1 && x 19 9).toNat = (x 19 9).toNat := handr _ _ (fun h => hp9 19 (h))
            have e3284 : (x 18 2 && x 18 10).toNat = (x 18 10).toNat := handr _ _ (fun h => hp10 18 (h))
            have e3285 : (x 17 3 && x 17 11).toNat = (x 17 11).toNat := handr _ _ (fun h => hp11 17 (h))
            have e3286 : (x 16 4 && x 16 12).toNat = (x 16 4).toNat := handl _ _ (fun h => hp4 16 (h))
            have e3287 : (x 15 5 && x 15 13).toNat = (x 15 5).toNat := handl _ _ (fun h => hp5 15 (h))
            have e3288 : (x 14 6 && x 14 14).toNat = (x 14 6).toNat := handl _ _ (fun h => hp6 14 (h))
            have b3289 := hb (x 13 7)
            have b3290 := hb (x 14 6)
            have b3291 := hb (x 15 5)
            have b3292 := hb (x 16 4)
            have b3293 := hb (x 17 11)
            have b3294 := hb (x 18 10)
            have b3295 := hb (x 19 9)
            have b3296 := hb (x 20 8)
            clear * - r3282 e3283 e3284 e3285 e3286 e3287 e3288 b3289 b3290 b3291 b3292 b3293 b3294 b3295 b3296 d3120 d3136 d3272
            omega
          have d3297 : (x 19 9).toNat = 0 := by
            have r3298 : (x 20 8).toNat + (x 19 1 && x 19 9).toNat + (x 18 2 && x 18 10).toNat + (x 17 3 && x 17 11).toNat + (x 16 4 && x 16 12).toNat + (x 15 5 && x 15 13).toNat + (x 14 6 && x 14 14).toNat + (x 13 7).toNat = 1 := hd8 20
            have e3299 : (x 19 1 && x 19 9).toNat = (x 19 9).toNat := handr _ _ (fun h => hp9 19 (h))
            have e3300 : (x 18 2 && x 18 10).toNat = (x 18 10).toNat := handr _ _ (fun h => hp10 18 (h))
            have e3301 : (x 17 3 && x 17 11).toNat = (x 17 11).toNat := handr _ _ (fun h => hp11 17 (h))
            have e3302 : (x 16 4 && x 16 12).toNat = (x 16 4).toNat := handl _ _ (fun h => hp4 16 (h))
            have e3303 : (x 15 5 && x 15 13).toNat = (x 15 5).toNat := handl _ _ (fun h => hp5 15 (h))
            have e3304 : (x 14 6 && x 14 14).toNat = (x 14 6).toNat := handl _ _ (fun h => hp6 14 (h))
            have b3305 := hb (x 13 7)
            have b3306 := hb (x 14 6)
            have b3307 := hb (x 15 5)
            have b3308 := hb (x 16 4)
            have b3309 := hb (x 17 11)
            have b3310 := hb (x 18 10)
            have b3311 := hb (x 19 9)
            have b3312 := hb (x 20 8)
            clear * - r3298 e3299 e3300 e3301 e3302 e3303 e3304 b3305 b3306 b3307 b3308 b3309 b3310 b3311 b3312 d3281 d3120 d3136 d3272
            omega
          have d3313 : (x 18 10).toNat = 0 := by
            have r3314 : (x 20 8).toNat + (x 19 1 && x 19 9).toNat + (x 18 2 && x 18 10).toNat + (x 17 3 && x 17 11).toNat + (x 16 4 && x 16 12).toNat + (x 15 5 && x 15 13).toNat + (x 14 6 && x 14 14).toNat + (x 13 7).toNat = 1 := hd8 20
            have e3315 : (x 19 1 && x 19 9).toNat = (x 19 9).toNat := handr _ _ (fun h => hp9 19 (h))
            have e3316 : (x 18 2 && x 18 10).toNat = (x 18 10).toNat := handr _ _ (fun h => hp10 18 (h))
            have e3317 : (x 17 3 && x 17 11).toNat = (x 17 11).toNat := handr _ _ (fun h => hp11 17 (h))
            have e3318 : (x 16 4 && x 16 12).toNat = (x 16 4).toNat := handl _ _ (fun h => hp4 16 (h))
            have e3319 : (x 15 5 && x 15 13).toNat = (x 15 5).toNat := handl _ _ (fun h => hp5 15 (h))
            have e3320 : (x 14 6 && x 14 14).toNat = (x 14 6).toNat := handl _ _ (fun h => hp6 14 (h))
            have b3321 := hb (x 13 7)
            have b3322 := hb (x 14 6)
            have b3323 := hb (x 15 5)
            have b3324 := hb (x 16 4)
            have b3325 := hb (x 17 11)
            have b3326 := hb (x 18 10)
            have b3327 := hb (x 19 9)
            have b3328 := hb (x 20 8)
            clear * - r3314 e3315 e3316 e3317 e3318 e3319 e3320 b3321 b3322 b3323 b3324 b3325 b3326 b3327 b3328 d3281 d3297 d3120 d3136 d3272
            omega
          have d3329 : (x 17 11).toNat = 0 := by
            have r3330 : (x 20 8).toNat + (x 19 1 && x 19 9).toNat + (x 18 2 && x 18 10).toNat + (x 17 3 && x 17 11).toNat + (x 16 4 && x 16 12).toNat + (x 15 5 && x 15 13).toNat + (x 14 6 && x 14 14).toNat + (x 13 7).toNat = 1 := hd8 20
            have e3331 : (x 19 1 && x 19 9).toNat = (x 19 9).toNat := handr _ _ (fun h => hp9 19 (h))
            have e3332 : (x 18 2 && x 18 10).toNat = (x 18 10).toNat := handr _ _ (fun h => hp10 18 (h))
            have e3333 : (x 17 3 && x 17 11).toNat = (x 17 11).toNat := handr _ _ (fun h => hp11 17 (h))
            have e3334 : (x 16 4 && x 16 12).toNat = (x 16 4).toNat := handl _ _ (fun h => hp4 16 (h))
            have e3335 : (x 15 5 && x 15 13).toNat = (x 15 5).toNat := handl _ _ (fun h => hp5 15 (h))
            have e3336 : (x 14 6 && x 14 14).toNat = (x 14 6).toNat := handl _ _ (fun h => hp6 14 (h))
            have b3337 := hb (x 13 7)
            have b3338 := hb (x 14 6)
            have b3339 := hb (x 15 5)
            have b3340 := hb (x 16 4)
            have b3341 := hb (x 17 11)
            have b3342 := hb (x 18 10)
            have b3343 := hb (x 19 9)
            have b3344 := hb (x 20 8)
            clear * - r3330 e3331 e3332 e3333 e3334 e3335 e3336 b3337 b3338 b3339 b3340 b3341 b3342 b3343 b3344 d3281 d3297 d3313 d3120 d3136 d3272
            omega
          have d3345 : (x 17 1 && x 17 11).toNat = 0 := by
            have r3346 := hand2 (x 17 1) (x 17 11)
            have b3347 := hb (x 17 11)
            have b3348 := hb (x 17 1 && x 17 11)
            clear * - r3346 b3347 b3348 d3329
            omega
          have d3349 : (x 14 4 && x 14 14).toNat = 1 := by
            have r3350 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := hcov10 18
            have b3351 := hb (x 13 5)
            have b3352 := hb (x 18 10)
            have b3353 := hb (x 17 1 && x 17 11)
            have b3354 := hb (x 16 2 && x 16 12)
            have b3355 := hb (x 15 3 && x 15 13)
            have b3356 := hb (x 14 4 && x 14 14)
            clear * - r3350 b3351 b3352 b3353 b3354 b3355 b3356 d3313 d3345 d3116 d3132 d2910
            omega
          have d3357 : (x 14 4).toNat = 1 := by
            have r3358 := hand1 (x 14 4) (x 14 14)
            have b3359 := hb (x 14 4)
            have b3360 := hb (x 14 4 && x 14 14)
            clear * - r3358 b3359 b3360 d3349
            omega
          have d3361 : (x 18 8).toNat = 0 := by
            have r3362 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := hd8 18
            have e3363 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
            have e3364 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
            have e3365 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
            have e3366 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
            have e3367 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
            have e3368 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
            have b3369 := hb (x 11 7)
            have b3370 := hb (x 12 6)
            have b3371 := hb (x 13 5)
            have b3372 := hb (x 14 4)
            have b3373 := hb (x 15 11)
            have b3374 := hb (x 16 10)
            have b3375 := hb (x 17 9)
            have b3376 := hb (x 18 8)
            clear * - r3362 e3363 e3364 e3365 e3366 e3367 e3368 b3369 b3370 b3371 b3372 b3373 b3374 b3375 b3376 d3357 d2910
            omega
          have d3377 : (x 17 9).toNat = 0 := by
            have r3378 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := hd8 18
            have e3379 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
            have e3380 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
            have e3381 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
            have e3382 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
            have e3383 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
            have e3384 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
            have b3385 := hb (x 11 7)
            have b3386 := hb (x 12 6)
            have b3387 := hb (x 13 5)
            have b3388 := hb (x 14 4)
            have b3389 := hb (x 15 11)
            have b3390 := hb (x 16 10)
            have b3391 := hb (x 17 9)
            have b3392 := hb (x 18 8)
            clear * - r3378 e3379 e3380 e3381 e3382 e3383 e3384 b3385 b3386 b3387 b3388 b3389 b3390 b3391 b3392 d3361 d3357 d2910
            omega
          have d3393 : (x 16 10).toNat = 0 := by
            have r3394 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := hd8 18
            have e3395 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
            have e3396 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
            have e3397 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
            have e3398 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
            have e3399 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
            have e3400 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
            have b3401 := hb (x 11 7)
            have b3402 := hb (x 12 6)
            have b3403 := hb (x 13 5)
            have b3404 := hb (x 14 4)
            have b3405 := hb (x 15 11)
            have b3406 := hb (x 16 10)
            have b3407 := hb (x 17 9)
            have b3408 := hb (x 18 8)
            clear * - r3394 e3395 e3396 e3397 e3398 e3399 e3400 b3401 b3402 b3403 b3404 b3405 b3406 b3407 b3408 d3361 d3377 d3357 d2910
            omega
          have d3409 : (x 15 11).toNat = 0 := by
            have r3410 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := hd8 18
            have e3411 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
            have e3412 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
            have e3413 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
            have e3414 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
            have e3415 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
            have e3416 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
            have b3417 := hb (x 11 7)
            have b3418 := hb (x 12 6)
            have b3419 := hb (x 13 5)
            have b3420 := hb (x 14 4)
            have b3421 := hb (x 15 11)
            have b3422 := hb (x 16 10)
            have b3423 := hb (x 17 9)
            have b3424 := hb (x 18 8)
            clear * - r3410 e3411 e3412 e3413 e3414 e3415 e3416 b3417 b3418 b3419 b3420 b3421 b3422 b3423 b3424 d3361 d3377 d3393 d3357 d2910
            omega
          have d3425 : (x 12 6).toNat = 0 := by
            have r3426 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := hd8 18
            have e3427 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
            have e3428 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
            have e3429 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
            have e3430 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
            have e3431 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
            have e3432 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
            have b3433 := hb (x 11 7)
            have b3434 := hb (x 12 6)
            have b3435 := hb (x 13 5)
            have b3436 := hb (x 14 4)
            have b3437 := hb (x 15 11)
            have b3438 := hb (x 16 10)
            have b3439 := hb (x 17 9)
            have b3440 := hb (x 18 8)
            clear * - r3426 e3427 e3428 e3429 e3430 e3431 e3432 b3433 b3434 b3435 b3436 b3437 b3438 b3439 b3440 d3361 d3377 d3393 d3409 d3357 d2910
            omega
          have d3441 : (x 11 7).toNat = 0 := by
            have r3442 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := hd8 18
            have e3443 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
            have e3444 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
            have e3445 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
            have e3446 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
            have e3447 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
            have e3448 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
            have b3449 := hb (x 11 7)
            have b3450 := hb (x 12 6)
            have b3451 := hb (x 13 5)
            have b3452 := hb (x 14 4)
            have b3453 := hb (x 15 11)
            have b3454 := hb (x 16 10)
            have b3455 := hb (x 17 9)
            have b3456 := hb (x 18 8)
            clear * - r3442 e3443 e3444 e3445 e3446 e3447 e3448 b3449 b3450 b3451 b3452 b3453 b3454 b3455 b3456 d3361 d3377 d3393 d3409 d3357 d2910 d3425
            omega
          have d3457 : (x 11 1 && x 11 7).toNat = 0 := by
            have r3458 := hand2 (x 11 1) (x 11 7)
            have b3459 := hb (x 11 7)
            have b3460 := hb (x 11 1 && x 11 7)
            clear * - r3458 b3459 b3460 d3441
            omega
          have d3461 : (x 8 2 && x 8 7).toNat = 0 := by
            have r3462 := hand2 (x 8 2) (x 8 7)
            have b3463 := hb (x 8 7)
            have b3464 := hb (x 8 2 && x 8 7)
            clear * - r3462 b3463 b3464 d3164
            omega
          have d3465 : (x 4 6 && x 4 11).toNat = 1 := by
            have r3466 : 1 ≤ (x 10 5).toNat + (x 9 1 && x 9 6).toNat + (x 8 2 && x 8 7).toNat + (x 7 3 && x 7 8).toNat + (x 6 4 && x 6 9).toNat + (x 5 5 && x 5 10).toNat + (x 4 6 && x 4 11).toNat + (x 3 7 && x 3 12).toNat + (x 2 8 && x 2 13).toNat + (x 1 9 && x 1 14).toNat + (x 0 10).toNat := hcov5 10
            have b3467 := hb (x 0 10)
            have b3468 := hb (x 10 5)
            have b3469 := hb (x 9 1 && x 9 6)
            have b3470 := hb (x 8 2 && x 8 7)
            have b3471 := hb (x 7 3 && x 7 8)
            have b3472 := hb (x 6 4 && x 6 9)
            have b3473 := hb (x 5 5 && x 5 10)
            have b3474 := hb (x 4 6 && x 4 11)
            have b3475 := hb (x 3 7 && x 3 12)
            have b3476 := hb (x 2 8 && x 2 13)
            have b3477 := hb (x 1 9 && x 1 14)
            clear * - r3466 b3467 b3468 b3469 b3470 b3471 b3472 b3473 b3474 b3475 b3476 b3477 d3035 d3160 d3461 d2682 d2702 d2658 d2595 d632 d652 g10
            omega
          have d3478 : (x 4 6).toNat = 1 := by
            have r3479 := hand1 (x 4 6) (x 4 11)
            have b3480 := hb (x 4 6)
            have b3481 := hb (x 4 6 && x 4 11)
            clear * - r3479 b3480 b3481 d3465
            omega
          have d3482 : (x 10 8).toNat = 0 := by
            have r3483 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := hd8 10
            have e3484 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
            have e3485 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
            have e3486 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
            have e3487 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
            have e3488 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
            have e3489 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
            have b3490 := hb (x 3 7)
            have b3491 := hb (x 4 6)
            have b3492 := hb (x 5 5)
            have b3493 := hb (x 6 4)
            have b3494 := hb (x 7 11)
            have b3495 := hb (x 8 10)
            have b3496 := hb (x 9 9)
            have b3497 := hb (x 10 8)
            clear * - r3483 e3484 e3485 e3486 e3487 e3488 e3489 b3490 b3491 b3492 b3493 b3494 b3495 b3496 b3497 d2814 d2830 d3478
            omega
          have d3498 : (x 10 2 && x 10 8).toNat = 0 := by
            have r3499 := hand2 (x 10 2) (x 10 8)
            have b3500 := hb (x 10 8)
            have b3501 := hb (x 10 2 && x 10 8)
            clear * - r3499 b3500 b3501 d3482
            omega
          have d3502 : (x 9 9).toNat = 0 := by
            have r3503 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := hd8 10
            have e3504 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
            have e3505 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
            have e3506 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
            have e3507 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
            have e3508 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
            have e3509 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
            have b3510 := hb (x 3 7)
            have b3511 := hb (x 4 6)
            have b3512 := hb (x 5 5)
            have b3513 := hb (x 6 4)
            have b3514 := hb (x 7 11)
            have b3515 := hb (x 8 10)
            have b3516 := hb (x 9 9)
            have b3517 := hb (x 10 8)
            clear * - r3503 e3504 e3505 e3506 e3507 e3508 e3509 b3510 b3511 b3512 b3513 b3514 b3515 b3516 b3517 d3482 d2814 d2830 d3478
            omega
          have d3518 : (x 9 3 && x 9 9).toNat = 0 := by
            have r3519 := hand2 (x 9 3) (x 9 9)
            have b3520 := hb (x 9 9)
            have b3521 := hb (x 9 3 && x 9 9)
            clear * - r3519 b3520 b3521 d3502
            omega
          have d3522 : (x 8 10).toNat = 0 := by
            have r3523 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := hd8 10
            have e3524 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
            have e3525 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
            have e3526 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
            have e3527 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
            have e3528 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
            have e3529 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
            have b3530 := hb (x 3 7)
            have b3531 := hb (x 4 6)
            have b3532 := hb (x 5 5)
            have b3533 := hb (x 6 4)
            have b3534 := hb (x 7 11)
            have b3535 := hb (x 8 10)
            have b3536 := hb (x 9 9)
            have b3537 := hb (x 10 8)
            clear * - r3523 e3524 e3525 e3526 e3527 e3528 e3529 b3530 b3531 b3532 b3533 b3534 b3535 b3536 b3537 d3482 d3502 d2814 d2830 d3478
            omega
          have d3538 : (x 8 4 && x 8 10).toNat = 0 := by
            have r3539 := hand2 (x 8 4) (x 8 10)
            have b3540 := hb (x 8 10)
            have b3541 := hb (x 8 4 && x 8 10)
            clear * - r3539 b3540 b3541 d3522
            omega
          have d3542 : (x 7 11).toNat = 0 := by
            have r3543 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := hd8 10
            have e3544 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
            have e3545 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
            have e3546 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
            have e3547 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
            have e3548 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
            have e3549 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
            have b3550 := hb (x 3 7)
            have b3551 := hb (x 4 6)
            have b3552 := hb (x 5 5)
            have b3553 := hb (x 6 4)
            have b3554 := hb (x 7 11)
            have b3555 := hb (x 8 10)
            have b3556 := hb (x 9 9)
            have b3557 := hb (x 10 8)
            clear * - r3543 e3544 e3545 e3546 e3547 e3548 e3549 b3550 b3551 b3552 b3553 b3554 b3555 b3556 b3557 d3482 d3502 d3522 d2814 d2830 d3478
            omega
          have d3558 : (x 7 5 && x 7 11).toNat = 0 := by
            have r3559 := hand2 (x 7 5) (x 7 11)
            have b3560 := hb (x 7 11)
            have b3561 := hb (x 7 5 && x 7 11)
            clear * - r3559 b3560 b3561 d3542
            omega
          have d3562 : (x 4 8 && x 4 14).toNat = 1 := by
            have r3563 : 1 ≤ (x 12 6).toNat + (x 11 1 && x 11 7).toNat + (x 10 2 && x 10 8).toNat + (x 9 3 && x 9 9).toNat + (x 8 4 && x 8 10).toNat + (x 7 5 && x 7 11).toNat + (x 6 6 && x 6 12).toNat + (x 5 7 && x 5 13).toNat + (x 4 8 && x 4 14).toNat + (x 3 9).toNat := hcov6 12
            have b3564 := hb (x 3 9)
            have b3565 := hb (x 12 6)
            have b3566 := hb (x 11 1 && x 11 7)
            have b3567 := hb (x 10 2 && x 10 8)
            have b3568 := hb (x 9 3 && x 9 9)
            have b3569 := hb (x 8 4 && x 8 10)
            have b3570 := hb (x 7 5 && x 7 11)
            have b3571 := hb (x 6 6 && x 6 12)
            have b3572 := hb (x 5 7 && x 5 13)
            have b3573 := hb (x 4 8 && x 4 14)
            clear * - r3563 b3564 b3565 b3566 b3567 b3568 b3569 b3570 b3571 b3572 b3573 d3425 d3457 d3498 d3518 d3538 d3558 d2810 d2826 d2798
            omega
          have d3574 : (x 4 8).toNat = 1 := by
            have r3575 := hand1 (x 4 8) (x 4 14)
            have b3576 := hb (x 4 8)
            have b3577 := hb (x 4 8 && x 4 14)
            clear * - r3575 b3576 b3577 d3562
            omega
          have d3578 : (x (-2) 6).toNat = 0 := by
            have r3579 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := hd8 4
            have e3580 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
            have e3581 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
            have e3582 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
            have e3583 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
            have e3584 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
            have e3585 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
            have b3586 := hb (x (-3) 7)
            have b3587 := hb (x (-2) 6)
            have b3588 := hb (x (-1) 5)
            have b3589 := hb (x 0 4)
            have b3590 := hb (x 1 11)
            have b3591 := hb (x 2 10)
            have b3592 := hb (x 3 9)
            have b3593 := hb (x 4 8)
            clear * - r3579 e3580 e3581 e3582 e3583 e3584 e3585 b3586 b3587 b3588 b3589 b3590 b3591 b3592 b3593 d3574 d2798 d466 d336 g7 g3
            omega
          have d3594 : (x 4 9).toNat = 1 := by
            have r3595 : 1 ≤ (x 4 9).toNat + (x 3 1 && x 3 10).toNat + (x 2 2 && x 2 11).toNat + (x 1 3 && x 1 12).toNat + (x 0 4 && x 0 13).toNat + (x (-1) 5 && x (-1) 14).toNat + (x (-2) 6).toNat := hcov9 4
            have b3596 := hb (x (-2) 6)
            have b3597 := hb (x 4 9)
            have b3598 := hb (x 3 1 && x 3 10)
            have b3599 := hb (x 2 2 && x 2 11)
            have b3600 := hb (x 1 3 && x 1 12)
            have b3601 := hb (x 0 4 && x 0 13)
            have b3602 := hb (x (-1) 5 && x (-1) 14)
            clear * - r3595 b3596 b3597 b3598 b3599 b3600 b3601 b3602 d2778 d462 d332 g20 g21 d3578
            omega
          have d3603 : (x 5 8).toNat = 0 := by
            have r3604 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := hd8 5
            have e3605 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
            have e3606 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
            have e3607 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
            have e3608 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
            have e3609 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
            have e3610 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
            have b3611 := hb (x (-2) 7)
            have b3612 := hb (x (-1) 6)
            have b3613 := hb (x 0 5)
            have b3614 := hb (x 1 4)
            have b3615 := hb (x 2 11)
            have b3616 := hb (x 3 10)
            have b3617 := hb (x 4 9)
            have b3618 := hb (x 5 8)
            clear * - r3604 e3605 e3606 e3607 e3608 e3609 e3610 b3611 b3612 b3613 b3614 b3615 b3616 b3617 b3618 d3594 d2774 d2790 f2707 g8 d515
            omega
          have d3619 : (x (-2) 7).toNat = 0 := by
            have r3620 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := hd8 5
            have e3621 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
            have e3622 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
            have e3623 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
            have e3624 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
            have e3625 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
            have e3626 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
            have b3627 := hb (x (-2) 7)
            have b3628 := hb (x (-1) 6)
            have b3629 := hb (x 0 5)
            have b3630 := hb (x 1 4)
            have b3631 := hb (x 2 11)
            have b3632 := hb (x 3 10)
            have b3633 := hb (x 4 9)
            have b3634 := hb (x 5 8)
            clear * - r3620 e3621 e3622 e3623 e3624 e3625 e3626 b3627 b3628 b3629 b3630 b3631 b3632 b3633 b3634 d3603 d3594 d2774 d2790 f2707 g8 d515
            omega
          have d3635 : (x (-2) 4 && x (-2) 7).toNat = 0 := by
            have r3636 := hand2 (x (-2) 4) (x (-2) 7)
            have b3637 := hb (x (-2) 7)
            have b3638 := hb (x (-2) 4 && x (-2) 7)
            clear * - r3636 b3637 b3638 d3619
            omega
          have d3639 : (x (-3) 7).toNat = 0 := by
            have r3640 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := hd8 4
            have e3641 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
            have e3642 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
            have e3643 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
            have e3644 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
            have e3645 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
            have e3646 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
            have b3647 := hb (x (-3) 7)
            have b3648 := hb (x (-2) 6)
            have b3649 := hb (x (-1) 5)
            have b3650 := hb (x 0 4)
            have b3651 := hb (x 1 11)
            have b3652 := hb (x 2 10)
            have b3653 := hb (x 3 9)
            have b3654 := hb (x 4 8)
            clear * - r3640 e3641 e3642 e3643 e3644 e3645 e3646 b3647 b3648 b3649 b3650 b3651 b3652 b3653 b3654 d3574 d2798 d466 d336 g7 g3 d3578
            omega
          have r3655 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := hcount 2
          have r3656 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := hcount 3
          have r3657 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := hcount 4
          have r3658 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := hd8 (-8)
          have e3659 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
          have e3660 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
          have e3661 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
          have e3662 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
          have e3663 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
          have e3664 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
          have r3665 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := hd8 (-4)
          have e3666 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
          have e3667 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
          have e3668 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
          have e3669 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
          have e3670 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
          have e3671 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
          have r3672 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := hd12 (-8)
          have e3673 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
          have e3674 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
          have r3675 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := hd12 (-6)
          have e3676 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
          have e3677 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
          have r3678 : 1 ≤ (x 2 3).toNat + (x 1 1 && x 1 4).toNat + (x 0 2 && x 0 5).toNat + (x (-1) 3 && x (-1) 6).toNat + (x (-2) 4 && x (-2) 7).toNat + (x (-3) 5 && x (-3) 8).toNat + (x (-4) 6 && x (-4) 9).toNat + (x (-5) 7 && x (-5) 10).toNat + (x (-6) 8 && x (-6) 11).toNat + (x (-7) 9 && x (-7) 12).toNat + (x (-8) 10 && x (-8) 13).toNat + (x (-9) 11 && x (-9) 14).toNat + (x (-10) 12).toNat := hcov3 2
          have r3679 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := hcov9 3
          have r3680 : 1 ≤ (x (-8) 10).toNat + (x (-9) 1 && x (-9) 11).toNat + (x (-10) 2 && x (-10) 12).toNat + (x (-11) 3 && x (-11) 13).toNat + (x (-12) 4 && x (-12) 14).toNat + (x (-13) 5).toNat := hcov10 (-8)
          have r3681 : 1 ≤ (x (-4) 10).toNat + (x (-5) 1 && x (-5) 11).toNat + (x (-6) 2 && x (-6) 12).toNat + (x (-7) 3 && x (-7) 13).toNat + (x (-8) 4 && x (-8) 14).toNat + (x (-9) 5).toNat := hcov10 (-4)
          have r3682 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := hcov11 (-8)
          have r3683 : 1 ≤ (x (-10) 13).toNat + (x (-11) 1 && x (-11) 14).toNat + (x (-12) 2).toNat := hcov13 (-10)
          have r3684 : (x (-12) 2).toNat ≤ (x (-12) 14).toNat := himp _ _ (hp2 (-12))
          have r3685 : (x (-9) 11).toNat ≤ (x (-9) 3).toNat := himp _ _ (hp11 (-9))
          have r3686 : (x (-8) 10).toNat ≤ (x (-8) 2).toNat := himp _ _ (hp10 (-8))
          have r3687 := hand1 (x (-6) 8) (x (-6) 11)
          have r3688 := hand1 (x (-7) 9) (x (-7) 12)
          have r3689 := hand1 (x (-8) 10) (x (-8) 13)
          have r3690 := hand1 (x (-9) 11) (x (-9) 14)
          have r3691 := hand1 (x (-2) 5) (x (-2) 14)
          have r3692 := hand2 (x (-9) 1) (x (-9) 11)
          have r3693 := hand1 (x (-10) 2) (x (-10) 12)
          have r3694 := hand1 (x (-11) 3) (x (-11) 13)
          have r3695 := hand2 (x (-12) 4) (x (-12) 14)
          have r3696 := hand2 (x (-6) 2) (x (-6) 12)
          have r3697 := hand2 (x (-7) 3) (x (-7) 13)
          have r3698 := hand1 (x (-8) 4) (x (-8) 14)
          have r3699 := hand2 (x (-9) 1) (x (-9) 12)
          have r3700 := hand1 (x (-10) 2) (x (-10) 13)
          have r3701 := hand1 (x (-11) 3) (x (-11) 14)
          have r3702 := hand2 (x (-11) 1) (x (-11) 14)
          have b3703 := hb (x (-15) 7)
          have b3704 := hb (x (-14) 6)
          have b3705 := hb (x (-13) 5)
          have b3706 := hb (x (-12) 2)
          have b3707 := hb (x (-12) 4)
          have b3708 := hb (x (-12) 14)
          have b3709 := hb (x (-11) 3)
          have b3710 := hb (x (-11) 7)
          have b3711 := hb (x (-11) 11)
          have b3712 := hb (x (-11) 13)
          have b3713 := hb (x (-11) 14)
          have b3714 := hb (x (-10) 2)
          have b3715 := hb (x (-10) 6)
          have b3716 := hb (x (-10) 10)
          have b3717 := hb (x (-10) 12)
          have b3718 := hb (x (-10) 13)
          have b3719 := hb (x (-10) 14)
          have b3720 := hb (x (-9) 3)
          have b3721 := hb (x (-9) 5)
          have b3722 := hb (x (-9) 9)
          have b3723 := hb (x (-9) 11)
          have b3724 := hb (x (-9) 12)
          have b3725 := hb (x (-9) 13)
          have b3726 := hb (x (-8) 2)
          have b3727 := hb (x (-8) 4)
          have b3728 := hb (x (-8) 8)
          have b3729 := hb (x (-8) 10)
          have b3730 := hb (x (-8) 11)
          have b3731 := hb (x (-8) 12)
          have b3732 := hb (x (-7) 9)
          have b3733 := hb (x (-7) 10)
          have b3734 := hb (x (-7) 11)
          have b3735 := hb (x (-7) 13)
          have b3736 := hb (x (-6) 8)
          have b3737 := hb (x (-6) 9)
          have b3738 := hb (x (-6) 10)
          have b3739 := hb (x (-6) 12)
          have b3740 := hb (x (-5) 7)
          have b3741 := hb (x (-5) 8)
          have b3742 := hb (x (-5) 9)
          have b3743 := hb (x (-4) 6)
          have b3744 := hb (x (-4) 7)
          have b3745 := hb (x (-4) 8)
          have b3746 := hb (x (-4) 10)
          have b3747 := hb (x (-3) 5)
          have b3748 := hb (x (-3) 6)
          have b3749 := hb (x (-3) 7)
          have b3750 := hb (x (-2) 4)
          have b3751 := hb (x (-2) 5)
          have b3752 := hb (x (-2) 6)
          have b3753 := hb (x (-1) 3)
          have b3754 := hb (x (-1) 4)
          have b3755 := hb (x (-1) 5)
          have b3756 := hb (x 0 2)
          have b3757 := hb (x 0 3)
          have b3758 := hb (x 0 4)
          have b3759 := hb (x 1 1)
          have b3760 := hb (x 1 2)
          have b3761 := hb (x 1 3)
          have b3762 := hb (x 2 1)
          have b3763 := hb (x 2 2)
          have b3764 := hb (x 2 3)
          have b3765 := hb (x 3 1)
          have b3766 := hb (x 3 9)
          have b3767 := hb (x 1 1 && x 1 4)
          have b3768 := hb (x 0 2 && x 0 5)
          have b3769 := hb (x (-1) 3 && x (-1) 6)
          have b3770 := hb (x (-2) 4 && x (-2) 7)
          have b3771 := hb (x (-3) 5 && x (-3) 8)
          have b3772 := hb (x (-4) 6 && x (-4) 9)
          have b3773 := hb (x (-5) 7 && x (-5) 10)
          have b3774 := hb (x (-6) 8 && x (-6) 11)
          have b3775 := hb (x (-7) 9 && x (-7) 12)
          have b3776 := hb (x (-8) 10 && x (-8) 13)
          have b3777 := hb (x (-9) 11 && x (-9) 14)
          have b3778 := hb (x 2 1 && x 2 10)
          have b3779 := hb (x 1 2 && x 1 11)
          have b3780 := hb (x 0 3 && x 0 12)
          have b3781 := hb (x (-1) 4 && x (-1) 13)
          have b3782 := hb (x (-2) 5 && x (-2) 14)
          have b3783 := hb (x (-9) 1 && x (-9) 11)
          have b3784 := hb (x (-10) 2 && x (-10) 12)
          have b3785 := hb (x (-11) 3 && x (-11) 13)
          have b3786 := hb (x (-12) 4 && x (-12) 14)
          have b3787 := hb (x (-5) 1 && x (-5) 11)
          have b3788 := hb (x (-6) 2 && x (-6) 12)
          have b3789 := hb (x (-7) 3 && x (-7) 13)
          have b3790 := hb (x (-8) 4 && x (-8) 14)
          have b3791 := hb (x (-9) 1 && x (-9) 12)
          have b3792 := hb (x (-10) 2 && x (-10) 13)
          have b3793 := hb (x (-11) 3 && x (-11) 14)
          have b3794 := hb (x (-11) 1 && x (-11) 14)
          linarith only [r3655, r3656, r3657, r3658, e3659, e3660, e3661, e3662, e3663, e3664, r3665, e3666, e3667, e3668, e3669, e3670, e3671, r3672, e3673, e3674, r3675, e3676, e3677, r3678, r3679, r3680, r3681, r3682, r3683, r3684, r3685, r3686, r3687, r3688, r3689, r3690, r3691, r3692, r3693, r3694, r3695, r3696, r3697, r3698, r3699, r3700, r3701, r3702, b3703, b3704, b3705, b3706, b3707, b3708, b3709, b3710, b3711, b3712, b3713, b3714, b3715, b3716, b3717, b3718, b3719, b3720, b3721, b3722, b3723, b3724, b3725, b3726, b3727, b3728, b3729, b3730, b3731, b3732, b3733, b3734, b3735, b3736, b3737, b3738, b3739, b3740, b3741, b3742, b3743, b3744, b3745, b3746, b3747, b3748, b3749, b3750, b3751, b3752, b3753, b3754, b3755, b3756, b3757, b3758, b3759, b3760, b3761, b3762, b3763, b3764, b3765, b3766, b3767, b3768, b3769, b3770, b3771, b3772, b3773, b3774, b3775, b3776, b3777, b3778, b3779, b3780, b3781, b3782, b3783, b3784, b3785, b3786, b3787, b3788, b3789, b3790, b3791, b3792, b3793, b3794, d676, d656, d498, g0, d3639, d482, d3578, d548, d568, g3, g5, g6, g7, f437, f2578, g14, d450, d2782, d2745, d2798, d2712, g16, d519, d3635, g17, d672, d692, d470, d344, g18, g19, d612]
        · have f3795 : (x 1 4).toNat = 1 := by rw [h2706]; rfl
          have d3796 : (x 1 12).toNat = 1 := by
            have r3797 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
            have b3798 := hb (x 1 4)
            have b3799 := hb (x 1 12)
            clear * - r3797 b3798 b3799 f3795
            omega
          have d3800 : (x (-2) 3).toNat = 0 := by
            have r3801 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
            have e3802 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
            have e3803 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
            have b3804 := hb (x (-2) 3)
            have b3805 := hb (x (-1) 2)
            have b3806 := hb (x 0 13)
            have b3807 := hb (x 1 12)
            clear * - r3801 e3802 e3803 b3804 b3805 b3806 b3807 d3796 g12 d523
            omega
          have d3808 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
            have r3809 := hand1 (x (-2) 3) (x (-2) 14)
            have b3810 := hb (x (-2) 3)
            have b3811 := hb (x (-2) 3 && x (-2) 14)
            clear * - r3809 b3810 b3811 d3800
            omega
          have d3812 : (x (-3) 4).toNat = 1 := by
            have r3813 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := hcov11 1
            have b3814 := hb (x (-3) 4)
            have b3815 := hb (x 1 11)
            have b3816 := hb (x 0 1 && x 0 12)
            have b3817 := hb (x (-1) 2 && x (-1) 13)
            have b3818 := hb (x (-2) 3 && x (-2) 14)
            clear * - r3813 b3814 b3815 b3816 b3817 b3818 d336 g29 g30 d3808
            omega
          have d3819 : (x (-3) 12).toNat = 1 := by
            have r3820 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
            have b3821 := hb (x (-3) 4)
            have b3822 := hb (x (-3) 12)
            clear * - r3820 b3821 b3822 d3812
            omega
          have d3823 : (x (-4) 13).toNat = 0 := by
            have r3824 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := hd12 (-3)
            have e3825 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
            have e3826 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
            have b3827 := hb (x (-6) 3)
            have b3828 := hb (x (-5) 2)
            have b3829 := hb (x (-4) 13)
            have b3830 := hb (x (-3) 12)
            clear * - r3824 e3825 e3826 b3827 b3828 b3829 b3830 d3819
            omega
          have d3831 : (x (-5) 2).toNat = 0 := by
            have r3832 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := hd12 (-3)
            have e3833 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
            have e3834 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
            have b3835 := hb (x (-6) 3)
            have b3836 := hb (x (-5) 2)
            have b3837 := hb (x (-4) 13)
            have b3838 := hb (x (-3) 12)
            clear * - r3832 e3833 e3834 b3835 b3836 b3837 b3838 d3819 d3823
            omega
          have d3839 : (x (-5) 2 && x (-5) 13).toNat = 0 := by
            have r3840 := hand1 (x (-5) 2) (x (-5) 13)
            have b3841 := hb (x (-5) 2)
            have b3842 := hb (x (-5) 2 && x (-5) 13)
            clear * - r3840 b3841 b3842 d3831
            omega
          have d3843 : (x (-5) 2 && x (-5) 12).toNat = 0 := by
            have r3844 := hand1 (x (-5) 2) (x (-5) 12)
            have b3845 := hb (x (-5) 2)
            have b3846 := hb (x (-5) 2 && x (-5) 12)
            clear * - r3844 b3845 b3846 d3831
            omega
          have d3847 : (x (-4) 1 && x (-4) 14).toNat = 1 := by
            have r3848 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := hcov13 (-3)
            have b3849 := hb (x (-5) 2)
            have b3850 := hb (x (-3) 13)
            have b3851 := hb (x (-4) 1 && x (-4) 14)
            clear * - r3848 b3849 b3850 b3851 g2 d3831
            omega
          have d3852 : (x (-4) 14).toNat = 1 := by
            have r3853 := hand2 (x (-4) 1) (x (-4) 14)
            have b3854 := hb (x (-4) 14)
            have b3855 := hb (x (-4) 1 && x (-4) 14)
            clear * - r3853 b3854 b3855 d3847
            omega
          have d3856 : (x (-5) 1).toNat = 0 := by
            have r3857 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := hd14 (-4)
            have b3858 := hb (x (-5) 1)
            have b3859 := hb (x (-4) 14)
            clear * - r3857 b3858 b3859 d3852
            omega
          have d3860 : (x (-5) 1 && x (-5) 14).toNat = 0 := by
            have r3861 := hand1 (x (-5) 1) (x (-5) 14)
            have b3862 := hb (x (-5) 1)
            have b3863 := hb (x (-5) 1 && x (-5) 14)
            clear * - r3861 b3862 b3863 d3856
            omega
          have d3864 : (x (-6) 2).toNat = 1 := by
            have r3865 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := hcov13 (-4)
            have b3866 := hb (x (-6) 2)
            have b3867 := hb (x (-4) 13)
            have b3868 := hb (x (-5) 1 && x (-5) 14)
            clear * - r3865 b3866 b3867 b3868 d3823 d3860
            omega
          have d3869 : (x (-6) 14).toNat = 1 := by
            have r3870 : (x (-6) 2).toNat ≤ (x (-6) 14).toNat := himp _ _ (hp2 (-6))
            have b3871 := hb (x (-6) 2)
            have b3872 := hb (x (-6) 14)
            clear * - r3870 b3871 b3872 d3864
            omega
          have d3873 : (x (-7) 1).toNat = 0 := by
            have r3874 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := hd14 (-6)
            have b3875 := hb (x (-7) 1)
            have b3876 := hb (x (-6) 14)
            clear * - r3874 b3875 b3876 d3869
            omega
          have d3877 : (x (-7) 13).toNat = 0 := by
            have r3878 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
            have b3879 := hb (x (-7) 1)
            have b3880 := hb (x (-7) 13)
            clear * - r3878 b3879 b3880 d3873
            omega
          have d3881 : (x (-4) 12).toNat = 0 := by
            have r3882 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := hd12 (-4)
            have e3883 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
            have e3884 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
            have b3885 := hb (x (-7) 3)
            have b3886 := hb (x (-6) 2)
            have b3887 := hb (x (-5) 13)
            have b3888 := hb (x (-4) 12)
            clear * - r3882 e3883 e3884 b3885 b3886 b3887 b3888 d3864
            omega
          have d3889 : (x (-4) 1 && x (-4) 12).toNat = 0 := by
            have r3890 := hand2 (x (-4) 1) (x (-4) 12)
            have b3891 := hb (x (-4) 12)
            have b3892 := hb (x (-4) 1 && x (-4) 12)
            clear * - r3890 b3891 b3892 d3881
            omega
          have d3893 : (x (-6) 3).toNat = 0 := by
            have r3894 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := hd12 (-3)
            have e3895 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
            have e3896 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
            have b3897 := hb (x (-6) 3)
            have b3898 := hb (x (-5) 2)
            have b3899 := hb (x (-4) 13)
            have b3900 := hb (x (-3) 12)
            clear * - r3894 e3895 e3896 b3897 b3898 b3899 b3900 d3819 d3823 d3831
            omega
          have d3901 : (x (-6) 3 && x (-6) 14).toNat = 0 := by
            have r3902 := hand1 (x (-6) 3) (x (-6) 14)
            have b3903 := hb (x (-6) 3)
            have b3904 := hb (x (-6) 3 && x (-6) 14)
            clear * - r3902 b3903 b3904 d3893
            omega
          have d3905 : (x (-6) 3 && x (-6) 13).toNat = 0 := by
            have r3906 := hand1 (x (-6) 3) (x (-6) 13)
            have b3907 := hb (x (-6) 3)
            have b3908 := hb (x (-6) 3 && x (-6) 13)
            clear * - r3906 b3907 b3908 d3893
            omega
          have d3909 : (x (-7) 4).toNat = 1 := by
            have r3910 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := hcov11 (-3)
            have b3911 := hb (x (-7) 4)
            have b3912 := hb (x (-3) 11)
            have b3913 := hb (x (-4) 1 && x (-4) 12)
            have b3914 := hb (x (-5) 2 && x (-5) 13)
            have b3915 := hb (x (-6) 3 && x (-6) 14)
            clear * - r3910 b3911 b3912 b3913 b3914 b3915 g1 d3889 d3839 d3901
            omega
          have d3916 : (x (-7) 12).toNat = 1 := by
            have r3917 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
            have b3918 := hb (x (-7) 4)
            have b3919 := hb (x (-7) 12)
            clear * - r3917 b3918 b3919 d3909
            omega
          have d3920 : (x (-8) 13).toNat = 0 := by
            have r3921 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := hd12 (-7)
            have e3922 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
            have e3923 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
            have b3924 := hb (x (-10) 3)
            have b3925 := hb (x (-9) 2)
            have b3926 := hb (x (-8) 13)
            have b3927 := hb (x (-7) 12)
            clear * - r3921 e3922 e3923 b3924 b3925 b3926 b3927 d3916
            omega
          have d3928 : (x (-8) 5).toNat = 0 := by
            have r3929 : (x (-8) 5).toNat ≤ (x (-8) 13).toNat := himp _ _ (hp5 (-8))
            have b3930 := hb (x (-8) 5)
            have b3931 := hb (x (-8) 13)
            clear * - r3929 b3930 b3931 d3920
            omega
          have d3932 : (x (-9) 2).toNat = 0 := by
            have r3933 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := hd12 (-7)
            have e3934 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
            have e3935 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
            have b3936 := hb (x (-10) 3)
            have b3937 := hb (x (-9) 2)
            have b3938 := hb (x (-8) 13)
            have b3939 := hb (x (-7) 12)
            clear * - r3933 e3934 e3935 b3936 b3937 b3938 b3939 d3916 d3920
            omega
          have d3940 : (x (-8) 1 && x (-8) 14).toNat = 1 := by
            have r3941 : 1 ≤ (x (-7) 13).toNat + (x (-8) 1 && x (-8) 14).toNat + (x (-9) 2).toNat := hcov13 (-7)
            have b3942 := hb (x (-9) 2)
            have b3943 := hb (x (-7) 13)
            have b3944 := hb (x (-8) 1 && x (-8) 14)
            clear * - r3941 b3942 b3943 b3944 d3877 d3932
            omega
          have d3945 : (x (-8) 1).toNat = 1 := by
            have r3946 := hand1 (x (-8) 1) (x (-8) 14)
            have b3947 := hb (x (-8) 1)
            have b3948 := hb (x (-8) 1 && x (-8) 14)
            clear * - r3946 b3947 b3948 d3940
            omega
          have d3949 : (x (-7) 14).toNat = 0 := by
            have r3950 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := hd14 (-7)
            have b3951 := hb (x (-8) 1)
            have b3952 := hb (x (-7) 14)
            clear * - r3950 b3951 b3952 d3945
            omega
          have d3953 : (x (-7) 4 && x (-7) 14).toNat = 0 := by
            have r3954 := hand2 (x (-7) 4) (x (-7) 14)
            have b3955 := hb (x (-7) 14)
            have b3956 := hb (x (-7) 4 && x (-7) 14)
            clear * - r3954 b3955 b3956 d3949
            omega
          have r3957 : 1 ≤ (x (-3) 10).toNat + (x (-4) 1 && x (-4) 11).toNat + (x (-5) 2 && x (-5) 12).toNat + (x (-6) 3 && x (-6) 13).toNat + (x (-7) 4 && x (-7) 14).toNat + (x (-8) 5).toNat := hcov10 (-3)
          have b3958 := hb (x (-8) 5)
          have b3959 := hb (x (-3) 10)
          have b3960 := hb (x (-4) 1 && x (-4) 11)
          have b3961 := hb (x (-5) 2 && x (-5) 12)
          have b3962 := hb (x (-6) 3 && x (-6) 13)
          have b3963 := hb (x (-7) 4 && x (-7) 14)
          linarith only [r3957, b3958, b3959, b3960, b3961, b3962, b3963, d580, d596, d3843, d3905, d3953, d3928]
  · have f3964 : (x 0 6).toNat = 1 := by rw [h348]; rfl
    have d3965 : (x 6 8).toNat = 0 := by
      have r3966 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
      have e3967 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e3968 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e3969 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e3970 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e3971 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e3972 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b3973 := hb (x (-1) 7)
      have b3974 := hb (x 0 6)
      have b3975 := hb (x 1 5)
      have b3976 := hb (x 2 4)
      have b3977 := hb (x 3 11)
      have b3978 := hb (x 4 10)
      have b3979 := hb (x 5 9)
      have b3980 := hb (x 6 8)
      clear * - r3966 e3967 e3968 e3969 e3970 e3971 e3972 b3973 b3974 b3975 b3976 b3977 b3978 b3979 b3980 f3964
      omega
    have d3981 : (x 5 9).toNat = 0 := by
      have r3982 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
      have e3983 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e3984 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e3985 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e3986 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e3987 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e3988 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b3989 := hb (x (-1) 7)
      have b3990 := hb (x 0 6)
      have b3991 := hb (x 1 5)
      have b3992 := hb (x 2 4)
      have b3993 := hb (x 3 11)
      have b3994 := hb (x 4 10)
      have b3995 := hb (x 5 9)
      have b3996 := hb (x 6 8)
      clear * - r3982 e3983 e3984 e3985 e3986 e3987 e3988 b3989 b3990 b3991 b3992 b3993 b3994 b3995 b3996 d3965 f3964
      omega
    have d3997 : (x 4 10).toNat = 0 := by
      have r3998 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
      have e3999 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e4000 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e4001 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e4002 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e4003 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e4004 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b4005 := hb (x (-1) 7)
      have b4006 := hb (x 0 6)
      have b4007 := hb (x 1 5)
      have b4008 := hb (x 2 4)
      have b4009 := hb (x 3 11)
      have b4010 := hb (x 4 10)
      have b4011 := hb (x 5 9)
      have b4012 := hb (x 6 8)
      clear * - r3998 e3999 e4000 e4001 e4002 e4003 e4004 b4005 b4006 b4007 b4008 b4009 b4010 b4011 b4012 d3965 d3981 f3964
      omega
    have d4013 : (x 3 11).toNat = 0 := by
      have r4014 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
      have e4015 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e4016 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e4017 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e4018 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e4019 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e4020 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b4021 := hb (x (-1) 7)
      have b4022 := hb (x 0 6)
      have b4023 := hb (x 1 5)
      have b4024 := hb (x 2 4)
      have b4025 := hb (x 3 11)
      have b4026 := hb (x 4 10)
      have b4027 := hb (x 5 9)
      have b4028 := hb (x 6 8)
      clear * - r4014 e4015 e4016 e4017 e4018 e4019 e4020 b4021 b4022 b4023 b4024 b4025 b4026 b4027 b4028 d3965 d3981 d3997 f3964
      omega
    have d4029 : (x 3 1 && x 3 11).toNat = 0 := by
      have r4030 := hand2 (x 3 1) (x 3 11)
      have b4031 := hb (x 3 11)
      have b4032 := hb (x 3 1 && x 3 11)
      clear * - r4030 b4031 b4032 d4013
      omega
    have d4033 : (x 2 2 && x 2 12).toNat = 1 := by
      have r4034 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := hcov10 4
      have b4035 := hb (x (-1) 5)
      have b4036 := hb (x 4 10)
      have b4037 := hb (x 3 1 && x 3 11)
      have b4038 := hb (x 2 2 && x 2 12)
      have b4039 := hb (x 1 3 && x 1 13)
      have b4040 := hb (x 0 4 && x 0 14)
      clear * - r4034 b4035 b4036 b4037 b4038 b4039 b4040 d3997 d4029 d328 g26 g3
      omega
    have d4041 : (x 2 12).toNat = 1 := by
      have r4042 := hand2 (x 2 2) (x 2 12)
      have b4043 := hb (x 2 12)
      have b4044 := hb (x 2 2 && x 2 12)
      clear * - r4042 b4043 b4044 d4033
      omega
    have d4045 : (x 1 13).toNat = 0 := by
      have r4046 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := hd12 2
      have e4047 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e4048 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b4049 := hb (x (-1) 3)
      have b4050 := hb (x 0 2)
      have b4051 := hb (x 1 13)
      have b4052 := hb (x 2 12)
      clear * - r4046 e4047 e4048 b4049 b4050 b4051 b4052 d4041 g5
      omega
    have d4053 : (x (-1) 2).toNat = 1 := by
      have r4054 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := hcov13 1
      have b4055 := hb (x (-1) 2)
      have b4056 := hb (x 1 13)
      have b4057 := hb (x 0 1 && x 0 14)
      clear * - r4054 b4055 b4056 b4057 d4045 g33
      omega
    have d4058 : (x (-1) 14).toNat = 1 := by
      have r4059 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
      have b4060 := hb (x (-1) 2)
      have b4061 := hb (x (-1) 14)
      clear * - r4059 b4060 b4061 d4053
      omega
    have d4062 : (x (-2) 1).toNat = 0 := by
      have r4063 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := hd14 (-1)
      have b4064 := hb (x (-2) 1)
      have b4065 := hb (x (-1) 14)
      clear * - r4063 b4064 b4065 d4058
      omega
    have d4066 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
      have r4067 := hand1 (x (-2) 1) (x (-2) 14)
      have b4068 := hb (x (-2) 1)
      have b4069 := hb (x (-2) 1 && x (-2) 14)
      clear * - r4067 b4068 b4069 d4062
      omega
    have d4070 : (x (-3) 2).toNat = 1 := by
      have r4071 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := hcov13 (-1)
      have b4072 := hb (x (-3) 2)
      have b4073 := hb (x (-1) 13)
      have b4074 := hb (x (-2) 1 && x (-2) 14)
      clear * - r4071 b4072 b4073 b4074 g4 d4066
      omega
    have d4075 : (x (-3) 14).toNat = 1 := by
      have r4076 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
      have b4077 := hb (x (-3) 2)
      have b4078 := hb (x (-3) 14)
      clear * - r4076 b4077 b4078 d4070
      omega
    have d4079 : (x (-4) 1).toNat = 0 := by
      have r4080 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := hd14 (-3)
      have b4081 := hb (x (-4) 1)
      have b4082 := hb (x (-3) 14)
      clear * - r4080 b4081 b4082 d4075
      omega
    have d4083 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
      have r4084 := hand1 (x (-4) 1) (x (-4) 14)
      have b4085 := hb (x (-4) 1)
      have b4086 := hb (x (-4) 1 && x (-4) 14)
      clear * - r4084 b4085 b4086 d4079
      omega
    have d4087 : (x (-5) 2).toNat = 1 := by
      have r4088 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := hcov13 (-3)
      have b4089 := hb (x (-5) 2)
      have b4090 := hb (x (-3) 13)
      have b4091 := hb (x (-4) 1 && x (-4) 14)
      clear * - r4088 b4089 b4090 b4091 g2 d4083
      omega
    have d4092 : (x (-5) 14).toNat = 1 := by
      have r4093 : (x (-5) 2).toNat ≤ (x (-5) 14).toNat := himp _ _ (hp2 (-5))
      have b4094 := hb (x (-5) 2)
      have b4095 := hb (x (-5) 14)
      clear * - r4093 b4094 b4095 d4087
      omega
    have d4096 : (x (-6) 1).toNat = 0 := by
      have r4097 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := hd14 (-5)
      have b4098 := hb (x (-6) 1)
      have b4099 := hb (x (-5) 14)
      clear * - r4097 b4098 b4099 d4092
      omega
    have d4100 : (x (-6) 1 && x (-6) 14).toNat = 0 := by
      have r4101 := hand1 (x (-6) 1) (x (-6) 14)
      have b4102 := hb (x (-6) 1)
      have b4103 := hb (x (-6) 1 && x (-6) 14)
      clear * - r4101 b4102 b4103 d4096
      omega
    have d4104 : (x (-3) 12).toNat = 0 := by
      have r4105 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := hd12 (-3)
      have e4106 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e4107 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b4108 := hb (x (-6) 3)
      have b4109 := hb (x (-5) 2)
      have b4110 := hb (x (-4) 13)
      have b4111 := hb (x (-3) 12)
      clear * - r4105 e4106 e4107 b4108 b4109 b4110 b4111 d4087
      omega
    have d4112 : (x (-4) 13).toNat = 0 := by
      have r4113 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := hd12 (-3)
      have e4114 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e4115 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b4116 := hb (x (-6) 3)
      have b4117 := hb (x (-5) 2)
      have b4118 := hb (x (-4) 13)
      have b4119 := hb (x (-3) 12)
      clear * - r4113 e4114 e4115 b4116 b4117 b4118 b4119 d4104 d4087
      omega
    have d4120 : (x (-6) 3).toNat = 0 := by
      have r4121 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := hd12 (-3)
      have e4122 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e4123 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b4124 := hb (x (-6) 3)
      have b4125 := hb (x (-5) 2)
      have b4126 := hb (x (-4) 13)
      have b4127 := hb (x (-3) 12)
      clear * - r4121 e4122 e4123 b4124 b4125 b4126 b4127 d4104 d4112 d4087
      omega
    have d4128 : (x (-6) 3 && x (-6) 14).toNat = 0 := by
      have r4129 := hand1 (x (-6) 3) (x (-6) 14)
      have b4130 := hb (x (-6) 3)
      have b4131 := hb (x (-6) 3 && x (-6) 14)
      clear * - r4129 b4130 b4131 d4120
      omega
    have d4132 : (x (-4) 1 && x (-4) 12).toNat = 0 := by
      have r4133 := hand1 (x (-4) 1) (x (-4) 12)
      have b4134 := hb (x (-4) 1)
      have b4135 := hb (x (-4) 1 && x (-4) 12)
      clear * - r4133 b4134 b4135 d4079
      omega
    have d4136 : (x (-1) 12).toNat = 0 := by
      have r4137 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
      have e4138 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e4139 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b4140 := hb (x (-4) 3)
      have b4141 := hb (x (-3) 2)
      have b4142 := hb (x (-2) 13)
      have b4143 := hb (x (-1) 12)
      clear * - r4137 e4138 e4139 b4140 b4141 b4142 b4143 d4070
      omega
    have d4144 : (x (-2) 13).toNat = 0 := by
      have r4145 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
      have e4146 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e4147 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b4148 := hb (x (-4) 3)
      have b4149 := hb (x (-3) 2)
      have b4150 := hb (x (-2) 13)
      have b4151 := hb (x (-1) 12)
      clear * - r4145 e4146 e4147 b4148 b4149 b4150 b4151 d4136 d4070
      omega
    have d4152 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
      have r4153 := hand2 (x (-2) 2) (x (-2) 13)
      have b4154 := hb (x (-2) 13)
      have b4155 := hb (x (-2) 2 && x (-2) 13)
      clear * - r4153 b4154 b4155 d4144
      omega
    have d4156 : (x (-4) 4).toNat = 1 := by
      have r4157 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := hcov11 0
      have b4158 := hb (x (-4) 4)
      have b4159 := hb (x 0 11)
      have b4160 := hb (x (-1) 1 && x (-1) 12)
      have b4161 := hb (x (-2) 2 && x (-2) 13)
      have b4162 := hb (x (-3) 3 && x (-3) 14)
      clear * - r4157 b4158 b4159 b4160 b4161 b4162 g11 g27 d4152 g28
      omega
    have d4163 : (x (-4) 12).toNat = 1 := by
      have r4164 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
      have b4165 := hb (x (-4) 4)
      have b4166 := hb (x (-4) 12)
      clear * - r4164 b4165 b4166 d4156
      omega
    have d4167 : (x (-5) 13).toNat = 0 := by
      have r4168 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := hd12 (-4)
      have e4169 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e4170 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have b4171 := hb (x (-7) 3)
      have b4172 := hb (x (-6) 2)
      have b4173 := hb (x (-5) 13)
      have b4174 := hb (x (-4) 12)
      clear * - r4168 e4169 e4170 b4171 b4172 b4173 b4174 d4163
      omega
    have d4175 : (x (-5) 2 && x (-5) 13).toNat = 0 := by
      have r4176 := hand2 (x (-5) 2) (x (-5) 13)
      have b4177 := hb (x (-5) 13)
      have b4178 := hb (x (-5) 2 && x (-5) 13)
      clear * - r4176 b4177 b4178 d4167
      omega
    have d4179 : (x (-7) 4).toNat = 1 := by
      have r4180 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := hcov11 (-3)
      have b4181 := hb (x (-7) 4)
      have b4182 := hb (x (-3) 11)
      have b4183 := hb (x (-4) 1 && x (-4) 12)
      have b4184 := hb (x (-5) 2 && x (-5) 13)
      have b4185 := hb (x (-6) 3 && x (-6) 14)
      clear * - r4180 b4181 b4182 b4183 b4184 b4185 g1 d4132 d4175 d4128
      omega
    have d4186 : (x (-7) 12).toNat = 1 := by
      have r4187 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
      have b4188 := hb (x (-7) 4)
      have b4189 := hb (x (-7) 12)
      clear * - r4187 b4188 b4189 d4179
      omega
    have d4190 : (x (-8) 13).toNat = 0 := by
      have r4191 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := hd12 (-7)
      have e4192 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
      have e4193 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
      have b4194 := hb (x (-10) 3)
      have b4195 := hb (x (-9) 2)
      have b4196 := hb (x (-8) 13)
      have b4197 := hb (x (-7) 12)
      clear * - r4191 e4192 e4193 b4194 b4195 b4196 b4197 d4186
      omega
    have d4198 : (x (-9) 2).toNat = 0 := by
      have r4199 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := hd12 (-7)
      have e4200 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
      have e4201 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
      have b4202 := hb (x (-10) 3)
      have b4203 := hb (x (-9) 2)
      have b4204 := hb (x (-8) 13)
      have b4205 := hb (x (-7) 12)
      clear * - r4199 e4200 e4201 b4202 b4203 b4204 b4205 d4186 d4190
      omega
    have d4206 : (x (-5) 5).toNat = 0 := by
      have r4207 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
      have b4208 := hb (x (-5) 5)
      have b4209 := hb (x (-5) 13)
      clear * - r4207 b4208 b4209 d4167
      omega
    have d4210 : (x (-7) 2).toNat = 1 := by
      have r4211 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := hcov13 (-5)
      have b4212 := hb (x (-7) 2)
      have b4213 := hb (x (-5) 13)
      have b4214 := hb (x (-6) 1 && x (-6) 14)
      clear * - r4211 b4212 b4213 b4214 d4167 d4100
      omega
    have d4215 : (x (-7) 14).toNat = 1 := by
      have r4216 : (x (-7) 2).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp2 (-7))
      have b4217 := hb (x (-7) 2)
      have b4218 := hb (x (-7) 14)
      clear * - r4216 b4217 b4218 d4210
      omega
    have d4219 : (x (-8) 1).toNat = 0 := by
      have r4220 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := hd14 (-7)
      have b4221 := hb (x (-8) 1)
      have b4222 := hb (x (-7) 14)
      clear * - r4220 b4221 b4222 d4215
      omega
    have d4223 : (x (-8) 1 && x (-8) 14).toNat = 0 := by
      have r4224 := hand1 (x (-8) 1) (x (-8) 14)
      have b4225 := hb (x (-8) 1)
      have b4226 := hb (x (-8) 1 && x (-8) 14)
      clear * - r4224 b4225 b4226 d4219
      omega
    have d4227 : (x (-7) 13).toNat = 1 := by
      have r4228 : 1 ≤ (x (-7) 13).toNat + (x (-8) 1 && x (-8) 14).toNat + (x (-9) 2).toNat := hcov13 (-7)
      have b4229 := hb (x (-9) 2)
      have b4230 := hb (x (-7) 13)
      have b4231 := hb (x (-8) 1 && x (-8) 14)
      clear * - r4228 b4229 b4230 b4231 d4223 d4198
      omega
    have d4232 : (x (-7) 1).toNat = 1 := by
      have r4233 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
      have b4234 := hb (x (-7) 1)
      have b4235 := hb (x (-7) 13)
      clear * - r4233 b4234 b4235 d4227
      omega
    have d4236 : (x (-6) 14).toNat = 0 := by
      have r4237 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := hd14 (-6)
      have b4238 := hb (x (-7) 1)
      have b4239 := hb (x (-6) 14)
      clear * - r4237 b4238 b4239 d4232
      omega
    have d4240 : (x (-6) 2).toNat = 0 := by
      have r4241 : (x (-6) 2).toNat ≤ (x (-6) 14).toNat := himp _ _ (hp2 (-6))
      have b4242 := hb (x (-6) 2)
      have b4243 := hb (x (-6) 14)
      clear * - r4241 b4242 b4243 d4236
      omega
    have d4244 : (x (-5) 1 && x (-5) 14).toNat = 1 := by
      have r4245 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := hcov13 (-4)
      have b4246 := hb (x (-6) 2)
      have b4247 := hb (x (-4) 13)
      have b4248 := hb (x (-5) 1 && x (-5) 14)
      clear * - r4245 b4246 b4247 b4248 d4112 d4240
      omega
    have d4249 : (x (-5) 1).toNat = 1 := by
      have r4250 := hand1 (x (-5) 1) (x (-5) 14)
      have b4251 := hb (x (-5) 1)
      have b4252 := hb (x (-5) 1 && x (-5) 14)
      clear * - r4250 b4251 b4252 d4244
      omega
    have d4253 : (x (-4) 14).toNat = 0 := by
      have r4254 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := hd14 (-4)
      have b4255 := hb (x (-5) 1)
      have b4256 := hb (x (-4) 14)
      clear * - r4254 b4255 b4256 d4249
      omega
    have d4257 : (x (-4) 4 && x (-4) 14).toNat = 0 := by
      have r4258 := hand2 (x (-4) 4) (x (-4) 14)
      have b4259 := hb (x (-4) 14)
      have b4260 := hb (x (-4) 4 && x (-4) 14)
      clear * - r4258 b4259 b4260 d4253
      omega
    have d4261 : (x (-2) 2 && x (-2) 12).toNat = 1 := by
      have r4262 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := hcov10 0
      have b4263 := hb (x (-5) 5)
      have b4264 := hb (x 0 10)
      have b4265 := hb (x (-1) 1 && x (-1) 11)
      have b4266 := hb (x (-2) 2 && x (-2) 12)
      have b4267 := hb (x (-3) 3 && x (-3) 13)
      have b4268 := hb (x (-4) 4 && x (-4) 14)
      clear * - r4262 b4263 b4264 b4265 b4266 b4267 b4268 g10 g22 g23 d4257 d4206
      omega
    have d4269 : (x (-2) 12).toNat = 1 := by
      have r4270 := hand2 (x (-2) 2) (x (-2) 12)
      have b4271 := hb (x (-2) 12)
      have b4272 := hb (x (-2) 2 && x (-2) 12)
      clear * - r4270 b4271 b4272 d4261
      omega
    have d4273 : (x (-4) 2).toNat = 0 := by
      have r4274 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := hd12 (-2)
      have e4275 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e4276 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have b4277 := hb (x (-5) 3)
      have b4278 := hb (x (-4) 2)
      have b4279 := hb (x (-3) 13)
      have b4280 := hb (x (-2) 12)
      clear * - r4274 e4275 e4276 b4277 b4278 b4279 b4280 d4269 g2
      omega
    have r4281 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := hcov13 (-2)
    have b4282 := hb (x (-4) 2)
    have b4283 := hb (x (-2) 13)
    have b4284 := hb (x (-3) 1 && x (-3) 14)
    linarith only [r4281, b4282, b4283, b4284, d4144, g32, d4273]

theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b00000 (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x (-3) 11).toNat = 0)
    (g2 : (x (-3) 13).toNat = 0)
    (g3 : (x (-1) 5).toNat = 0)
    (g4 : (x (-1) 13).toNat = 0)
    (g5 : (x 0 2).toNat = 0)
    (g6 : (x 0 3).toNat = 0)
    (g7 : (x 0 4).toNat = 0)
    (g8 : (x 0 5).toNat = 0)
    (g9 : (x 0 7).toNat = 0)
    (g10 : (x 0 10).toNat = 0)
    (g11 : (x 0 11).toNat = 0)
    (g12 : (x 0 13).toNat = 0)
    (g13 : (x 0 14).toNat = 1)
    (g14 : (x 1 3).toNat = 0)
    (g15 : (x 1 14).toNat = 1)
    (g16 : (x 0 2 && x 0 5).toNat = 0)
    (g17 : (x (-3) 5 && x (-3) 8).toNat = 0)
    (g18 : (x 0 3 && x 0 12).toNat = 0)
    (g19 : (x (-1) 4 && x (-1) 13).toNat = 0)
    (g20 : (x 0 4 && x 0 13).toNat = 0)
    (g21 : (x (-1) 5 && x (-1) 14).toNat = 0)
    (g22 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g23 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g24 : (x 0 2 && x 0 12).toNat = 0)
    (g25 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g26 : (x 0 4 && x 0 14).toNat = 0)
    (g27 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g28 : (x (-3) 3 && x (-3) 14).toNat = 0)
    (g29 : (x 0 1 && x 0 12).toNat = 0)
    (g30 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g31 : (x 0 3 && x 0 14).toNat = 0)
    (g32 : (x (-3) 1 && x (-3) 14).toNat = 0)
    (g33 : (x 0 1 && x 0 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b00000_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33
