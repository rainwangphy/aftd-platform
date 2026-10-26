import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a0000

Topic: combinatorics   Node: c02a0fcbb075

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP; the same generator on the same window refutes x(0,2) != x(0,3) (a case-split tree of 109 + 3 nodes).

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_two_iff_three_core: under the layer-free tight-cover constraints for k = 15 and 13 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a0000_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 13).toNat = 0)
    (g1 : (x (-1) 13).toNat = 0)
    (g2 : (x 0 1).toNat = 0)
    (g3 : (x 0 13).toNat = 0)
    (g4 : (x 1 13).toNat = 0)
    (g5 : (x 0 1 && x 0 12).toNat = 0)
    (g6 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g7 : (x 0 2 && x 0 13).toNat = 0)
    (g8 : (x (-1) 3 && x (-1) 14).toNat = 0)
    (g9 : (x 2 1 && x 2 12).toNat = 0)
    (g10 : (x 1 2 && x 1 13).toNat = 0)
    (g11 : (x 0 3 && x 0 14).toNat = 0)
    (g12 : (x (-3) 1 && x (-3) 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d2367 : (x 0 1 && x 0 14).toNat = 0 := by
    have r2368 := hand1 (x 0 1) (x 0 14)
    have b2369 := hb (x 0 1)
    have b2370 := hb (x 0 1 && x 0 14)
    clear * - r2368 b2369 b2370 g2
    omega
  have d2371 : (x (-1) 2).toNat = 1 := by
    have r2372 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2373 := hb (x (-1) 2)
    have b2374 := hb (x 1 13)
    have b2375 := hb (x 0 1 && x 0 14)
    clear * - r2372 b2373 b2374 b2375 g4 d2367
    omega
  have d2376 : (x (-1) 14).toNat = 1 := by
    have r2377 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
    have b2378 := hb (x (-1) 2)
    have b2379 := hb (x (-1) 14)
    clear * - r2377 b2378 b2379 d2371
    omega
  have d2380 : (x (-2) 1).toNat = 0 := by
    have r2381 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2382 := hb (x (-2) 1)
    have b2383 := hb (x (-1) 14)
    clear * - r2381 b2382 b2383 d2376
    omega
  have d2384 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
    have r2385 := hand1 (x (-2) 1) (x (-2) 14)
    have b2386 := hb (x (-2) 1)
    have b2387 := hb (x (-2) 1 && x (-2) 14)
    clear * - r2385 b2386 b2387 d2380
    omega
  have d2388 : (x (-2) 13).toNat = 0 := by
    have r2389 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
    have b2390 := hb (x (-2) 1)
    have b2391 := hb (x (-2) 13)
    clear * - r2389 b2390 b2391 d2380
    omega
  have d2392 : (x (-3) 2).toNat = 1 := by
    have r2393 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2394 := hb (x (-3) 2)
    have b2395 := hb (x (-1) 13)
    have b2396 := hb (x (-2) 1 && x (-2) 14)
    clear * - r2393 b2394 b2395 b2396 g1 d2384
    omega
  have d2397 : (x (-3) 14).toNat = 1 := by
    have r2398 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
    have b2399 := hb (x (-3) 2)
    have b2400 := hb (x (-3) 14)
    clear * - r2398 b2399 b2400 d2392
    omega
  have d2401 : (x (-4) 1).toNat = 0 := by
    have r2402 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2403 := hb (x (-4) 1)
    have b2404 := hb (x (-3) 14)
    clear * - r2402 b2403 b2404 d2397
    omega
  have d2405 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
    have r2406 := hand1 (x (-4) 1) (x (-4) 14)
    have b2407 := hb (x (-4) 1)
    have b2408 := hb (x (-4) 1 && x (-4) 14)
    clear * - r2406 b2407 b2408 d2401
    omega
  have d2409 : (x (-4) 13).toNat = 0 := by
    have r2410 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
    have b2411 := hb (x (-4) 1)
    have b2412 := hb (x (-4) 13)
    clear * - r2410 b2411 b2412 d2401
    omega
  have d2413 : (x (-4) 2).toNat = 1 := by
    have r2414 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2415 := hb (x (-4) 2)
    have b2416 := hb (x (-2) 13)
    have b2417 := hb (x (-3) 1 && x (-3) 14)
    clear * - r2414 b2415 b2416 b2417 d2388 g12
    omega
  have d2418 : (x (-5) 2).toNat = 1 := by
    have r2419 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2420 := hb (x (-5) 2)
    have b2421 := hb (x (-3) 13)
    have b2422 := hb (x (-4) 1 && x (-4) 14)
    clear * - r2419 b2420 b2421 b2422 g0 d2405
    omega
  have d2423 : (x 1 12).toNat = 0 := by
    have r2424 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2425 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e2426 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b2427 := hb (x (-2) 3)
    have b2428 := hb (x (-1) 2)
    have b2429 := hb (x 0 13)
    have b2430 := hb (x 1 12)
    clear * - r2424 e2425 e2426 b2427 b2428 b2429 b2430 g3 d2371
    omega
  have d2431 : (x 1 1 && x 1 12).toNat = 0 := by
    have r2432 := hand2 (x 1 1) (x 1 12)
    have b2433 := hb (x 1 12)
    have b2434 := hb (x 1 1 && x 1 12)
    clear * - r2432 b2433 b2434 d2423
    omega
  have d2435 : (x (-2) 3).toNat = 0 := by
    have r2436 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2437 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e2438 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b2439 := hb (x (-2) 3)
    have b2440 := hb (x (-1) 2)
    have b2441 := hb (x 0 13)
    have b2442 := hb (x 1 12)
    clear * - r2436 e2437 e2438 b2439 b2440 b2441 b2442 d2423 g3 d2371
    omega
  have d2443 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
    have r2444 := hand1 (x (-2) 3) (x (-2) 14)
    have b2445 := hb (x (-2) 3)
    have b2446 := hb (x (-2) 3 && x (-2) 14)
    clear * - r2444 b2445 b2446 d2435
    omega
  have d2447 : (x (-1) 12).toNat = 0 := by
    have r2448 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2449 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e2450 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b2451 := hb (x (-4) 3)
    have b2452 := hb (x (-3) 2)
    have b2453 := hb (x (-2) 13)
    have b2454 := hb (x (-1) 12)
    clear * - r2448 e2449 e2450 b2451 b2452 b2453 b2454 d2388 d2392
    omega
  have d2455 : (x (-1) 4).toNat = 0 := by
    have r2456 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
    have b2457 := hb (x (-1) 4)
    have b2458 := hb (x (-1) 12)
    clear * - r2456 b2457 b2458 d2447
    omega
  have d2459 : (x (-2) 12).toNat = 0 := by
    have r2460 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2461 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
    have e2462 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
    have b2463 := hb (x (-5) 3)
    have b2464 := hb (x (-4) 2)
    have b2465 := hb (x (-3) 13)
    have b2466 := hb (x (-2) 12)
    clear * - r2460 e2461 e2462 b2463 b2464 b2465 b2466 g0 d2413
    omega
  have d2467 : (x (-2) 4).toNat = 0 := by
    have r2468 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
    have b2469 := hb (x (-2) 4)
    have b2470 := hb (x (-2) 12)
    clear * - r2468 b2469 b2470 d2459
    omega
  have d2471 : (x (-3) 12).toNat = 0 := by
    have r2472 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2473 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
    have e2474 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
    have b2475 := hb (x (-6) 3)
    have b2476 := hb (x (-5) 2)
    have b2477 := hb (x (-4) 13)
    have b2478 := hb (x (-3) 12)
    clear * - r2472 e2473 e2474 b2475 b2476 b2477 b2478 d2409 d2418
    omega
  have d2479 : (x (-3) 4).toNat = 0 := by
    have r2480 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
    have b2481 := hb (x (-3) 4)
    have b2482 := hb (x (-3) 12)
    clear * - r2480 b2481 b2482 d2471
    omega
  have d2483 : (x 3 11).toNat = 1 := by
    have r2484 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2485 := hb (x (-1) 4)
    have b2486 := hb (x 3 11)
    have b2487 := hb (x 2 1 && x 2 12)
    have b2488 := hb (x 1 2 && x 1 13)
    have b2489 := hb (x 0 3 && x 0 14)
    clear * - r2484 b2485 b2486 b2487 b2488 b2489 g9 g10 g11 d2455
    omega
  have d2490 : (x 3 3).toNat = 1 := by
    have r2491 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
    have b2492 := hb (x 3 3)
    have b2493 := hb (x 3 11)
    clear * - r2491 b2492 b2493 d2483
    omega
  have d2494 : (x 6 12).toNat = 0 := by
    have r2495 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2496 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e2497 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b2498 := hb (x 3 3)
    have b2499 := hb (x 4 2)
    have b2500 := hb (x 5 13)
    have b2501 := hb (x 6 12)
    clear * - r2495 e2496 e2497 b2498 b2499 b2500 b2501 d2490
    omega
  have d2502 : (x 5 13).toNat = 0 := by
    have r2503 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2504 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e2505 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b2506 := hb (x 3 3)
    have b2507 := hb (x 4 2)
    have b2508 := hb (x 5 13)
    have b2509 := hb (x 6 12)
    clear * - r2503 e2504 e2505 b2506 b2507 b2508 b2509 d2494 d2490
    omega
  have d2510 : (x 2 11).toNat = 1 := by
    have r2511 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := by have q := hcov11 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2512 := hb (x (-2) 4)
    have b2513 := hb (x 2 11)
    have b2514 := hb (x 1 1 && x 1 12)
    have b2515 := hb (x 0 2 && x 0 13)
    have b2516 := hb (x (-1) 3 && x (-1) 14)
    clear * - r2511 b2512 b2513 b2514 b2515 b2516 d2431 g7 g8 d2467
    omega
  have d2517 : (x 2 3).toNat = 1 := by
    have r2518 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
    have b2519 := hb (x 2 3)
    have b2520 := hb (x 2 11)
    clear * - r2518 b2519 b2520 d2510
    omega
  have d2521 : (x 5 12).toNat = 0 := by
    have r2522 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2523 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e2524 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b2525 := hb (x 2 3)
    have b2526 := hb (x 3 2)
    have b2527 := hb (x 4 13)
    have b2528 := hb (x 5 12)
    clear * - r2522 e2523 e2524 b2525 b2526 b2527 b2528 d2517
    omega
  have d2529 : (x 4 13).toNat = 0 := by
    have r2530 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2531 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e2532 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b2533 := hb (x 2 3)
    have b2534 := hb (x 3 2)
    have b2535 := hb (x 4 13)
    have b2536 := hb (x 5 12)
    clear * - r2530 e2531 e2532 b2533 b2534 b2535 b2536 d2521 d2517
    omega
  have d2537 : (x 3 2).toNat = 0 := by
    have r2538 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2539 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e2540 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b2541 := hb (x 2 3)
    have b2542 := hb (x 3 2)
    have b2543 := hb (x 4 13)
    have b2544 := hb (x 5 12)
    clear * - r2538 e2539 e2540 b2541 b2542 b2543 b2544 d2521 d2529 d2517
    omega
  have d2545 : (x 4 1 && x 4 14).toNat = 1 := by
    have r2546 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2547 := hb (x 3 2)
    have b2548 := hb (x 5 13)
    have b2549 := hb (x 4 1 && x 4 14)
    clear * - r2546 b2547 b2548 b2549 d2502 d2537
    omega
  have d2550 : (x 4 14).toNat = 1 := by
    have r2551 := hand2 (x 4 1) (x 4 14)
    have b2552 := hb (x 4 14)
    have b2553 := hb (x 4 1 && x 4 14)
    clear * - r2551 b2552 b2553 d2545
    omega
  have d2554 : (x 3 1).toNat = 0 := by
    have r2555 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2556 := hb (x 3 1)
    have b2557 := hb (x 4 14)
    clear * - r2555 b2556 b2557 d2550
    omega
  have d2558 : (x 3 1 && x 3 14).toNat = 0 := by
    have r2559 := hand1 (x 3 1) (x 3 14)
    have b2560 := hb (x 3 1)
    have b2561 := hb (x 3 1 && x 3 14)
    clear * - r2559 b2560 b2561 d2554
    omega
  have d2562 : (x 2 2).toNat = 1 := by
    have r2563 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2564 := hb (x 2 2)
    have b2565 := hb (x 4 13)
    have b2566 := hb (x 3 1 && x 3 14)
    clear * - r2563 b2564 b2565 b2566 d2529 d2558
    omega
  have d2567 : (x 4 12).toNat = 0 := by
    have r2568 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2569 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e2570 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b2571 := hb (x 1 3)
    have b2572 := hb (x 2 2)
    have b2573 := hb (x 3 13)
    have b2574 := hb (x 4 12)
    clear * - r2568 e2569 e2570 b2571 b2572 b2573 b2574 d2562
    omega
  have d2575 : (x 3 13).toNat = 0 := by
    have r2576 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2577 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e2578 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b2579 := hb (x 1 3)
    have b2580 := hb (x 2 2)
    have b2581 := hb (x 3 13)
    have b2582 := hb (x 4 12)
    clear * - r2576 e2577 e2578 b2579 b2580 b2581 b2582 d2567 d2562
    omega
  have d2583 : (x 1 3).toNat = 0 := by
    have r2584 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2585 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e2586 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b2587 := hb (x 1 3)
    have b2588 := hb (x 2 2)
    have b2589 := hb (x 3 13)
    have b2590 := hb (x 4 12)
    clear * - r2584 e2585 e2586 b2587 b2588 b2589 b2590 d2567 d2575 d2562
    omega
  have d2591 : (x 1 11).toNat = 0 := by
    have r2592 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
    have b2593 := hb (x 1 3)
    have b2594 := hb (x 1 11)
    clear * - r2592 b2593 b2594 d2583
    omega
  have r2595 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have b2596 := hb (x (-3) 4)
  have b2597 := hb (x 1 11)
  have b2598 := hb (x 0 1 && x 0 12)
  have b2599 := hb (x (-1) 2 && x (-1) 13)
  have b2600 := hb (x (-2) 3 && x (-2) 14)
  linarith only [r2595, b2596, b2597, b2598, b2599, b2600, d2591, g5, g6, d2443, d2479]

theorem cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a0000 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 13).toNat = 0)
    (g1 : (x (-1) 13).toNat = 0)
    (g2 : (x 0 1).toNat = 0)
    (g3 : (x 0 13).toNat = 0)
    (g4 : (x 1 13).toNat = 0)
    (g5 : (x 0 1 && x 0 12).toNat = 0)
    (g6 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g7 : (x 0 2 && x 0 13).toNat = 0)
    (g8 : (x (-1) 3 && x (-1) 14).toNat = 0)
    (g9 : (x 2 1 && x 2 12).toNat = 0)
    (g10 : (x 1 2 && x 1 13).toNat = 0)
    (g11 : (x 0 3 && x 0 14).toNat = 0)
    (g12 : (x (-3) 1 && x (-3) 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a0000_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12
