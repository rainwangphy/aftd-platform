import AFTD.Prelude

/-!
# cycle_power_fifteen_tight_type_sequence_shape_rules_core_v101_110

Topic: combinatorics   Node: 759ad8b66f8d

Provenance: helper lemma. Research thread RT-1, open case k = 15 (m = 4) of OP-205 (arXiv:2610.15635, Theorems 1.3-1.4: eq(C_n^k) for k+1 = 2^m, n even, (k+1) not dividing n). Experiment 9757: on the integer window [-24, 24] the layer-free tight-class model leaves 13 class types at the centre, none with an island; on [-32, 32] the six types {0,15}, {0,1,14,15}, {0..3,12..15}, {0..7,12..15}, {0..3,8..15}, {0..15}.

Window refutation for k = 15: in the layer-free tight-class model on the integer line (x p j: the class starting at p contains p + j; inner count 3 per vertex, distances 14, 12, 8 covered exactly once, the other distances covered, classes closed under the tight-class parent map), with x p 1 = x p 14 and x p 2 = x p 3 everywhere, the class at 0 cannot have bit 10 = 1 and bit 11 = 0.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_shape_rules_core_v101_110_aux (x : ℤ → Fin 16 → Bool)
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
    (h114 : ∀ p, x p 1 = x p 14)
    (h23 : ∀ p, x p 2 = x p 3)
    (g0 : (x 0 10).toNat = 1) (g1 : (x 0 11).toNat = 0) : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d9354 : (x 0 1 && x 0 11).toNat = 0 := by
    have r9355 := hand2 (x 0 1) (x 0 11)
    have b9356 := hb (x 0 11)
    have b9357 := hb (x 0 1 && x 0 11)
    clear * - r9355 b9356 b9357 g1
    omega
  have d9358 : (x 0 2 && x 0 11).toNat = 0 := by
    have r9359 := hand2 (x 0 2) (x 0 11)
    have b9360 := hb (x 0 11)
    have b9361 := hb (x 0 2 && x 0 11)
    clear * - r9359 b9360 b9361 g1
    omega
  have d9362 : (x 0 4 && x 0 11).toNat = 0 := by
    have r9363 := hand2 (x 0 4) (x 0 11)
    have b9364 := hb (x 0 11)
    have b9365 := hb (x 0 4 && x 0 11)
    clear * - r9363 b9364 b9365 g1
    omega
  have d9366 : (x 0 6 && x 0 11).toNat = 0 := by
    have r9367 := hand2 (x 0 6) (x 0 11)
    have b9368 := hb (x 0 11)
    have b9369 := hb (x 0 6 && x 0 11)
    clear * - r9367 b9368 b9369 g1
    omega
  have d9370 : (x 0 2).toNat = 1 := by
    have r9371 : (x 0 10).toNat ≤ (x 0 2).toNat := himp _ _ (hp10 0)
    have b9372 := hb (x 0 2)
    have b9373 := hb (x 0 10)
    clear * - r9371 b9372 b9373 g0
    omega
  have d9374 : (x 0 3).toNat = 1 := by
    have r9375 : (x 0 2).toNat = (x 0 3).toNat := congrArg Bool.toNat (h23 0)
    have b9376 := hb (x 0 2)
    have b9377 := hb (x 0 3)
    clear * - r9375 b9376 b9377 d9370
    omega
  have d9378 : (x 0 14).toNat = 1 := by
    have r9379 : (x 0 2).toNat ≤ (x 0 14).toNat := himp _ _ (hp2 0)
    have b9380 := hb (x 0 2)
    have b9381 := hb (x 0 14)
    clear * - r9379 b9380 b9381 d9370
    omega
  have d9382 : (x 0 1).toNat = 1 := by
    have r9383 : (x 0 1).toNat = (x 0 14).toNat := congrArg Bool.toNat (h114 0)
    have b9384 := hb (x 0 1)
    have b9385 := hb (x 0 14)
    clear * - r9383 b9384 b9385 d9378
    omega
  have d9386 : (x 1 14).toNat = 0 := by
    have r9387 : (x 1 14).toNat + (x 0 1).toNat = 1 := by have q := hd14 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9388 := hb (x 0 1)
    have b9389 := hb (x 1 14)
    clear * - r9387 b9388 b9389 d9382
    omega
  have d9390 : (x 1 3 && x 1 14).toNat = 0 := by
    have r9391 := hand2 (x 1 3) (x 1 14)
    have b9392 := hb (x 1 14)
    have b9393 := hb (x 1 3 && x 1 14)
    clear * - r9391 b9392 b9393 d9386
    omega
  have d9394 : (x 1 1).toNat = 0 := by
    have r9395 : (x 1 1).toNat = (x 1 14).toNat := congrArg Bool.toNat (h114 1)
    have b9396 := hb (x 1 1)
    have b9397 := hb (x 1 14)
    clear * - r9395 b9396 b9397 d9386
    omega
  have d9398 : (x 1 1 && x 1 11).toNat = 0 := by
    have r9399 := hand1 (x 1 1) (x 1 11)
    have b9400 := hb (x 1 1)
    have b9401 := hb (x 1 1 && x 1 11)
    clear * - r9399 b9400 b9401 d9394
    omega
  have d9402 : (x 1 1 && x 1 10).toNat = 0 := by
    have r9403 := hand1 (x 1 1) (x 1 10)
    have b9404 := hb (x 1 1)
    have b9405 := hb (x 1 1 && x 1 10)
    clear * - r9403 b9404 b9405 d9394
    omega
  have d9406 : (x 1 1 && x 1 8).toNat = 0 := by
    have r9407 := hand1 (x 1 1) (x 1 8)
    have b9408 := hb (x 1 1)
    have b9409 := hb (x 1 1 && x 1 8)
    clear * - r9407 b9408 b9409 d9394
    omega
  have d9410 : (x 1 1 && x 1 7).toNat = 0 := by
    have r9411 := hand1 (x 1 1) (x 1 7)
    have b9412 := hb (x 1 1)
    have b9413 := hb (x 1 1 && x 1 7)
    clear * - r9411 b9412 b9413 d9394
    omega
  have d9414 : (x 1 13).toNat = 0 := by
    have r9415 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
    have b9416 := hb (x 1 1)
    have b9417 := hb (x 1 13)
    clear * - r9415 b9416 b9417 d9394
    omega
  have d9418 : (x 1 3 && x 1 13).toNat = 0 := by
    have r9419 := hand2 (x 1 3) (x 1 13)
    have b9420 := hb (x 1 13)
    have b9421 := hb (x 1 3 && x 1 13)
    clear * - r9419 b9420 b9421 d9414
    omega
  have d9422 : (x 1 5).toNat = 0 := by
    have r9423 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
    have b9424 := hb (x 1 5)
    have b9425 := hb (x 1 13)
    clear * - r9423 b9424 b9425 d9414
    omega
  have d9426 : (x 1 5 && x 1 11).toNat = 0 := by
    have r9427 := hand1 (x 1 5) (x 1 11)
    have b9428 := hb (x 1 5)
    have b9429 := hb (x 1 5 && x 1 11)
    clear * - r9427 b9428 b9429 d9422
    omega
  have d9430 : (x 1 5 && x 1 10).toNat = 0 := by
    have r9431 := hand1 (x 1 5) (x 1 10)
    have b9432 := hb (x 1 5)
    have b9433 := hb (x 1 5 && x 1 10)
    clear * - r9431 b9432 b9433 d9422
    omega
  have d9434 : (x 1 5 && x 1 9).toNat = 0 := by
    have r9435 := hand1 (x 1 5) (x 1 9)
    have b9436 := hb (x 1 5)
    have b9437 := hb (x 1 5 && x 1 9)
    clear * - r9435 b9436 b9437 d9422
    omega
  have d9438 : (x 1 9).toNat = 0 := by
    have r9439 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
    have b9440 := hb (x 1 1)
    have b9441 := hb (x 1 9)
    clear * - r9439 b9440 b9441 d9394
    omega
  have d9442 : (x 2 14).toNat = 1 := by
    have r9443 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9444 := hb (x 1 1)
    have b9445 := hb (x 2 14)
    clear * - r9443 b9444 b9445 d9394
    omega
  have d9446 : (x 2 1).toNat = 1 := by
    have r9447 : (x 2 1).toNat = (x 2 14).toNat := congrArg Bool.toNat (h114 2)
    have b9448 := hb (x 2 1)
    have b9449 := hb (x 2 14)
    clear * - r9447 b9448 b9449 d9442
    omega
  have d9450 : (x 3 14).toNat = 0 := by
    have r9451 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9452 := hb (x 2 1)
    have b9453 := hb (x 3 14)
    clear * - r9451 b9452 b9453 d9446
    omega
  have d9454 : (x 3 3 && x 3 14).toNat = 0 := by
    have r9455 := hand2 (x 3 3) (x 3 14)
    have b9456 := hb (x 3 14)
    have b9457 := hb (x 3 3 && x 3 14)
    clear * - r9455 b9456 b9457 d9450
    omega
  have d9458 : (x 3 1).toNat = 0 := by
    have r9459 : (x 3 1).toNat = (x 3 14).toNat := congrArg Bool.toNat (h114 3)
    have b9460 := hb (x 3 1)
    have b9461 := hb (x 3 14)
    clear * - r9459 b9460 b9461 d9450
    omega
  have d9462 : (x 3 1 && x 3 12).toNat = 0 := by
    have r9463 := hand1 (x 3 1) (x 3 12)
    have b9464 := hb (x 3 1)
    have b9465 := hb (x 3 1 && x 3 12)
    clear * - r9463 b9464 b9465 d9458
    omega
  have d9466 : (x 3 1 && x 3 11).toNat = 0 := by
    have r9467 := hand1 (x 3 1) (x 3 11)
    have b9468 := hb (x 3 1)
    have b9469 := hb (x 3 1 && x 3 11)
    clear * - r9467 b9468 b9469 d9458
    omega
  have d9470 : (x 3 1 && x 3 8).toNat = 0 := by
    have r9471 := hand1 (x 3 1) (x 3 8)
    have b9472 := hb (x 3 1)
    have b9473 := hb (x 3 1 && x 3 8)
    clear * - r9471 b9472 b9473 d9458
    omega
  have d9474 : (x 3 13).toNat = 0 := by
    have r9475 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
    have b9476 := hb (x 3 1)
    have b9477 := hb (x 3 13)
    clear * - r9475 b9476 b9477 d9458
    omega
  have d9478 : (x 3 3 && x 3 13).toNat = 0 := by
    have r9479 := hand2 (x 3 3) (x 3 13)
    have b9480 := hb (x 3 13)
    have b9481 := hb (x 3 3 && x 3 13)
    clear * - r9479 b9480 b9481 d9474
    omega
  have d9482 : (x 3 5).toNat = 0 := by
    have r9483 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
    have b9484 := hb (x 3 5)
    have b9485 := hb (x 3 13)
    clear * - r9483 b9484 b9485 d9474
    omega
  have d9486 : (x 3 5 && x 3 9).toNat = 0 := by
    have r9487 := hand1 (x 3 5) (x 3 9)
    have b9488 := hb (x 3 5)
    have b9489 := hb (x 3 5 && x 3 9)
    clear * - r9487 b9488 b9489 d9482
    omega
  have d9490 : (x 3 9).toNat = 0 := by
    have r9491 : (x 3 9).toNat ≤ (x 3 1).toNat := himp _ _ (hp9 3)
    have b9492 := hb (x 3 1)
    have b9493 := hb (x 3 9)
    clear * - r9491 b9492 b9493 d9458
    omega
  have d9494 : (x 3 3 && x 3 9).toNat = 0 := by
    have r9495 := hand2 (x 3 3) (x 3 9)
    have b9496 := hb (x 3 9)
    have b9497 := hb (x 3 3 && x 3 9)
    clear * - r9495 b9496 b9497 d9490
    omega
  have d9498 : (x 4 14).toNat = 1 := by
    have r9499 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9500 := hb (x 3 1)
    have b9501 := hb (x 4 14)
    clear * - r9499 b9500 b9501 d9458
    omega
  have d9502 : (x 4 1).toNat = 1 := by
    have r9503 : (x 4 1).toNat = (x 4 14).toNat := congrArg Bool.toNat (h114 4)
    have b9504 := hb (x 4 1)
    have b9505 := hb (x 4 14)
    clear * - r9503 b9504 b9505 d9498
    omega
  have d9506 : (x 5 14).toNat = 0 := by
    have r9507 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9508 := hb (x 4 1)
    have b9509 := hb (x 5 14)
    clear * - r9507 b9508 b9509 d9502
    omega
  have d9510 : (x 5 3 && x 5 14).toNat = 0 := by
    have r9511 := hand2 (x 5 3) (x 5 14)
    have b9512 := hb (x 5 14)
    have b9513 := hb (x 5 3 && x 5 14)
    clear * - r9511 b9512 b9513 d9506
    omega
  have d9514 : (x 5 1).toNat = 0 := by
    have r9515 : (x 5 1).toNat = (x 5 14).toNat := congrArg Bool.toNat (h114 5)
    have b9516 := hb (x 5 1)
    have b9517 := hb (x 5 14)
    clear * - r9515 b9516 b9517 d9506
    omega
  have d9518 : (x 5 1 && x 5 12).toNat = 0 := by
    have r9519 := hand1 (x 5 1) (x 5 12)
    have b9520 := hb (x 5 1)
    have b9521 := hb (x 5 1 && x 5 12)
    clear * - r9519 b9520 b9521 d9514
    omega
  have d9522 : (x 5 1 && x 5 11).toNat = 0 := by
    have r9523 := hand1 (x 5 1) (x 5 11)
    have b9524 := hb (x 5 1)
    have b9525 := hb (x 5 1 && x 5 11)
    clear * - r9523 b9524 b9525 d9514
    omega
  have d9526 : (x 5 1 && x 5 7).toNat = 0 := by
    have r9527 := hand1 (x 5 1) (x 5 7)
    have b9528 := hb (x 5 1)
    have b9529 := hb (x 5 1 && x 5 7)
    clear * - r9527 b9528 b9529 d9514
    omega
  have d9530 : (x 5 1 && x 5 6).toNat = 0 := by
    have r9531 := hand1 (x 5 1) (x 5 6)
    have b9532 := hb (x 5 1)
    have b9533 := hb (x 5 1 && x 5 6)
    clear * - r9531 b9532 b9533 d9514
    omega
  have d9534 : (x 5 13).toNat = 0 := by
    have r9535 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
    have b9536 := hb (x 5 1)
    have b9537 := hb (x 5 13)
    clear * - r9535 b9536 b9537 d9514
    omega
  have d9538 : (x 5 5).toNat = 0 := by
    have r9539 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
    have b9540 := hb (x 5 5)
    have b9541 := hb (x 5 13)
    clear * - r9539 b9540 b9541 d9534
    omega
  have d9542 : (x 5 9).toNat = 0 := by
    have r9543 : (x 5 9).toNat ≤ (x 5 1).toNat := himp _ _ (hp9 5)
    have b9544 := hb (x 5 1)
    have b9545 := hb (x 5 9)
    clear * - r9543 b9544 b9545 d9514
    omega
  have d9546 : (x 6 14).toNat = 1 := by
    have r9547 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9548 := hb (x 5 1)
    have b9549 := hb (x 6 14)
    clear * - r9547 b9548 b9549 d9514
    omega
  have d9550 : (x 6 1).toNat = 1 := by
    have r9551 : (x 6 1).toNat = (x 6 14).toNat := congrArg Bool.toNat (h114 6)
    have b9552 := hb (x 6 1)
    have b9553 := hb (x 6 14)
    clear * - r9551 b9552 b9553 d9546
    omega
  have d9554 : (x 7 14).toNat = 0 := by
    have r9555 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9556 := hb (x 6 1)
    have b9557 := hb (x 7 14)
    clear * - r9555 b9556 b9557 d9550
    omega
  have d9558 : (x 7 1).toNat = 0 := by
    have r9559 : (x 7 1).toNat = (x 7 14).toNat := congrArg Bool.toNat (h114 7)
    have b9560 := hb (x 7 1)
    have b9561 := hb (x 7 14)
    clear * - r9559 b9560 b9561 d9554
    omega
  have d9562 : (x 7 1 && x 7 12).toNat = 0 := by
    have r9563 := hand1 (x 7 1) (x 7 12)
    have b9564 := hb (x 7 1)
    have b9565 := hb (x 7 1 && x 7 12)
    clear * - r9563 b9564 b9565 d9558
    omega
  have d9566 : (x 7 13).toNat = 0 := by
    have r9567 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
    have b9568 := hb (x 7 1)
    have b9569 := hb (x 7 13)
    clear * - r9567 b9568 b9569 d9558
    omega
  have d9570 : (x 7 3 && x 7 13).toNat = 0 := by
    have r9571 := hand2 (x 7 3) (x 7 13)
    have b9572 := hb (x 7 13)
    have b9573 := hb (x 7 3 && x 7 13)
    clear * - r9571 b9572 b9573 d9566
    omega
  have d9574 : (x 7 4 && x 7 13).toNat = 0 := by
    have r9575 := hand2 (x 7 4) (x 7 13)
    have b9576 := hb (x 7 13)
    have b9577 := hb (x 7 4 && x 7 13)
    clear * - r9575 b9576 b9577 d9566
    omega
  have d9578 : (x 7 5).toNat = 0 := by
    have r9579 : (x 7 5).toNat ≤ (x 7 13).toNat := himp _ _ (hp5 7)
    have b9580 := hb (x 7 5)
    have b9581 := hb (x 7 13)
    clear * - r9579 b9580 b9581 d9566
    omega
  have d9582 : (x 7 9).toNat = 0 := by
    have r9583 : (x 7 9).toNat ≤ (x 7 1).toNat := himp _ _ (hp9 7)
    have b9584 := hb (x 7 1)
    have b9585 := hb (x 7 9)
    clear * - r9583 b9584 b9585 d9558
    omega
  have d9586 : (x 8 14).toNat = 1 := by
    have r9587 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9588 := hb (x 7 1)
    have b9589 := hb (x 8 14)
    clear * - r9587 b9588 b9589 d9558
    omega
  have d9590 : (x 8 1).toNat = 1 := by
    have r9591 : (x 8 1).toNat = (x 8 14).toNat := congrArg Bool.toNat (h114 8)
    have b9592 := hb (x 8 1)
    have b9593 := hb (x 8 14)
    clear * - r9591 b9592 b9593 d9586
    omega
  have d9594 : (x 9 14).toNat = 0 := by
    have r9595 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9596 := hb (x 8 1)
    have b9597 := hb (x 9 14)
    clear * - r9595 b9596 b9597 d9590
    omega
  have d9598 : (x 9 3 && x 9 14).toNat = 0 := by
    have r9599 := hand2 (x 9 3) (x 9 14)
    have b9600 := hb (x 9 14)
    have b9601 := hb (x 9 3 && x 9 14)
    clear * - r9599 b9600 b9601 d9594
    omega
  have d9602 : (x 9 1).toNat = 0 := by
    have r9603 : (x 9 1).toNat = (x 9 14).toNat := congrArg Bool.toNat (h114 9)
    have b9604 := hb (x 9 1)
    have b9605 := hb (x 9 14)
    clear * - r9603 b9604 b9605 d9594
    omega
  have d9606 : (x 9 1 && x 9 11).toNat = 0 := by
    have r9607 := hand1 (x 9 1) (x 9 11)
    have b9608 := hb (x 9 1)
    have b9609 := hb (x 9 1 && x 9 11)
    clear * - r9607 b9608 b9609 d9602
    omega
  have d9610 : (x 10 14).toNat = 1 := by
    have r9611 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9612 := hb (x 9 1)
    have b9613 := hb (x 10 14)
    clear * - r9611 b9612 b9613 d9602
    omega
  have d9614 : (x 10 1).toNat = 1 := by
    have r9615 : (x 10 1).toNat = (x 10 14).toNat := congrArg Bool.toNat (h114 10)
    have b9616 := hb (x 10 1)
    have b9617 := hb (x 10 14)
    clear * - r9615 b9616 b9617 d9610
    omega
  have d9618 : (x 9 6).toNat = 0 := by
    have r9619 : (x 9 6).toNat ≤ (x 9 14).toNat := himp _ _ (hp6 9)
    have b9620 := hb (x 9 6)
    have b9621 := hb (x 9 14)
    clear * - r9619 b9620 b9621 d9594
    omega
  have d9622 : (x 9 2 && x 9 6).toNat = 0 := by
    have r9623 := hand2 (x 9 2) (x 9 6)
    have b9624 := hb (x 9 6)
    have b9625 := hb (x 9 2 && x 9 6)
    clear * - r9623 b9624 b9625 d9618
    omega
  have d9626 : (x 9 2).toNat = 0 := by
    have r9627 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
    have b9628 := hb (x 9 2)
    have b9629 := hb (x 9 14)
    clear * - r9627 b9628 b9629 d9594
    omega
  have d9630 : (x 9 2 && x 9 11).toNat = 0 := by
    have r9631 := hand1 (x 9 2) (x 9 11)
    have b9632 := hb (x 9 2)
    have b9633 := hb (x 9 2 && x 9 11)
    clear * - r9631 b9632 b9633 d9626
    omega
  have d9634 : (x 9 3).toNat = 0 := by
    have r9635 : (x 9 2).toNat = (x 9 3).toNat := congrArg Bool.toNat (h23 9)
    have b9636 := hb (x 9 2)
    have b9637 := hb (x 9 3)
    clear * - r9635 b9636 b9637 d9626
    omega
  have d9638 : (x 9 11).toNat = 0 := by
    have r9639 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
    have b9640 := hb (x 9 3)
    have b9641 := hb (x 9 11)
    clear * - r9639 b9640 b9641 d9634
    omega
  have d9642 : (x 7 2).toNat = 0 := by
    have r9643 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
    have b9644 := hb (x 7 2)
    have b9645 := hb (x 7 14)
    clear * - r9643 b9644 b9645 d9554
    omega
  have d9646 : (x 7 3).toNat = 0 := by
    have r9647 : (x 7 2).toNat = (x 7 3).toNat := congrArg Bool.toNat (h23 7)
    have b9648 := hb (x 7 2)
    have b9649 := hb (x 7 3)
    clear * - r9647 b9648 b9649 d9642
    omega
  have d9650 : (x 7 10).toNat = 0 := by
    have r9651 : (x 7 10).toNat ≤ (x 7 2).toNat := himp _ _ (hp10 7)
    have b9652 := hb (x 7 2)
    have b9653 := hb (x 7 10)
    clear * - r9651 b9652 b9653 d9642
    omega
  have d9654 : (x 5 6).toNat = 0 := by
    have r9655 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
    have b9656 := hb (x 5 6)
    have b9657 := hb (x 5 14)
    clear * - r9655 b9656 b9657 d9506
    omega
  have d9658 : (x 5 6 && x 5 10).toNat = 0 := by
    have r9659 := hand1 (x 5 6) (x 5 10)
    have b9660 := hb (x 5 6)
    have b9661 := hb (x 5 6 && x 5 10)
    clear * - r9659 b9660 b9661 d9654
    omega
  have d9662 : (x 5 2).toNat = 0 := by
    have r9663 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
    have b9664 := hb (x 5 2)
    have b9665 := hb (x 5 14)
    clear * - r9663 b9664 b9665 d9506
    omega
  have d9666 : (x 5 3).toNat = 0 := by
    have r9667 : (x 5 2).toNat = (x 5 3).toNat := congrArg Bool.toNat (h23 5)
    have b9668 := hb (x 5 2)
    have b9669 := hb (x 5 3)
    clear * - r9667 b9668 b9669 d9662
    omega
  have d9670 : (x 5 3 && x 5 7).toNat = 0 := by
    have r9671 := hand1 (x 5 3) (x 5 7)
    have b9672 := hb (x 5 3)
    have b9673 := hb (x 5 3 && x 5 7)
    clear * - r9671 b9672 b9673 d9666
    omega
  have d9674 : (x 5 11).toNat = 0 := by
    have r9675 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
    have b9676 := hb (x 5 3)
    have b9677 := hb (x 5 11)
    clear * - r9675 b9676 b9677 d9666
    omega
  have d9678 : (x 3 6).toNat = 0 := by
    have r9679 : (x 3 6).toNat ≤ (x 3 14).toNat := himp _ _ (hp6 3)
    have b9680 := hb (x 3 6)
    have b9681 := hb (x 3 14)
    clear * - r9679 b9680 b9681 d9450
    omega
  have d9682 : (x 3 2).toNat = 0 := by
    have r9683 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
    have b9684 := hb (x 3 2)
    have b9685 := hb (x 3 14)
    clear * - r9683 b9684 b9685 d9450
    omega
  have d9686 : (x 3 3).toNat = 0 := by
    have r9687 : (x 3 2).toNat = (x 3 3).toNat := congrArg Bool.toNat (h23 3)
    have b9688 := hb (x 3 2)
    have b9689 := hb (x 3 3)
    clear * - r9687 b9688 b9689 d9682
    omega
  have d9690 : (x 3 3 && x 3 8).toNat = 0 := by
    have r9691 := hand1 (x 3 3) (x 3 8)
    have b9692 := hb (x 3 3)
    have b9693 := hb (x 3 3 && x 3 8)
    clear * - r9691 b9692 b9693 d9686
    omega
  have d9694 : (x 3 3 && x 3 7).toNat = 0 := by
    have r9695 := hand1 (x 3 3) (x 3 7)
    have b9696 := hb (x 3 3)
    have b9697 := hb (x 3 3 && x 3 7)
    clear * - r9695 b9696 b9697 d9686
    omega
  have d9698 : (x 3 11).toNat = 0 := by
    have r9699 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
    have b9700 := hb (x 3 3)
    have b9701 := hb (x 3 11)
    clear * - r9699 b9700 b9701 d9686
    omega
  have d9702 : (x 1 2).toNat = 0 := by
    have r9703 : (x 1 2).toNat ≤ (x 1 14).toNat := himp _ _ (hp2 1)
    have b9704 := hb (x 1 2)
    have b9705 := hb (x 1 14)
    clear * - r9703 b9704 b9705 d9386
    omega
  have d9706 : (x 1 3).toNat = 0 := by
    have r9707 : (x 1 2).toNat = (x 1 3).toNat := congrArg Bool.toNat (h23 1)
    have b9708 := hb (x 1 2)
    have b9709 := hb (x 1 3)
    clear * - r9707 b9708 b9709 d9702
    omega
  have d9710 : (x 1 3 && x 1 10).toNat = 0 := by
    have r9711 := hand1 (x 1 3) (x 1 10)
    have b9712 := hb (x 1 3)
    have b9713 := hb (x 1 3 && x 1 10)
    clear * - r9711 b9712 b9713 d9706
    omega
  have d9714 : (x 1 11).toNat = 0 := by
    have r9715 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
    have b9716 := hb (x 1 3)
    have b9717 := hb (x 1 11)
    clear * - r9715 b9716 b9717 d9706
    omega
  have d9718 : (x 1 7 && x 1 11).toNat = 0 := by
    have r9719 := hand2 (x 1 7) (x 1 11)
    have b9720 := hb (x 1 11)
    have b9721 := hb (x 1 7 && x 1 11)
    clear * - r9719 b9720 b9721 d9714
    omega
  have d9722 : (x 1 10).toNat = 0 := by
    have r9723 : (x 1 10).toNat ≤ (x 1 2).toNat := himp _ _ (hp10 1)
    have b9724 := hb (x 1 2)
    have b9725 := hb (x 1 10)
    clear * - r9723 b9724 b9725 d9702
    omega
  have d9726 : (x (-1) 1).toNat = 0 := by
    have r9727 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9728 := hb (x (-1) 1)
    have b9729 := hb (x 0 14)
    clear * - r9727 b9728 b9729 d9378
    omega
  have d9730 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
    have r9731 := hand1 (x (-1) 1) (x (-1) 12)
    have b9732 := hb (x (-1) 1)
    have b9733 := hb (x (-1) 1 && x (-1) 12)
    clear * - r9731 b9732 b9733 d9726
    omega
  have d9734 : (x (-1) 14).toNat = 0 := by
    have r9735 : (x (-1) 1).toNat = (x (-1) 14).toNat := congrArg Bool.toNat (h114 (-1))
    have b9736 := hb (x (-1) 1)
    have b9737 := hb (x (-1) 14)
    clear * - r9735 b9736 b9737 d9726
    omega
  have d9738 : (x (-1) 2).toNat = 0 := by
    have r9739 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
    have b9740 := hb (x (-1) 2)
    have b9741 := hb (x (-1) 14)
    clear * - r9739 b9740 b9741 d9734
    omega
  have d9742 : (x (-1) 2 && x (-1) 12).toNat = 0 := by
    have r9743 := hand1 (x (-1) 2) (x (-1) 12)
    have b9744 := hb (x (-1) 2)
    have b9745 := hb (x (-1) 2 && x (-1) 12)
    clear * - r9743 b9744 b9745 d9738
    omega
  have d9746 : (x (-1) 3).toNat = 0 := by
    have r9747 : (x (-1) 2).toNat = (x (-1) 3).toNat := congrArg Bool.toNat (h23 (-1))
    have b9748 := hb (x (-1) 2)
    have b9749 := hb (x (-1) 3)
    clear * - r9747 b9748 b9749 d9738
    omega
  have d9750 : (x (-1) 3 && x (-1) 13).toNat = 0 := by
    have r9751 := hand1 (x (-1) 3) (x (-1) 13)
    have b9752 := hb (x (-1) 3)
    have b9753 := hb (x (-1) 3 && x (-1) 13)
    clear * - r9751 b9752 b9753 d9746
    omega
  have d9754 : (x (-1) 3 && x (-1) 12).toNat = 0 := by
    have r9755 := hand1 (x (-1) 3) (x (-1) 12)
    have b9756 := hb (x (-1) 3)
    have b9757 := hb (x (-1) 3 && x (-1) 12)
    clear * - r9755 b9756 b9757 d9746
    omega
  have d9758 : (x (-1) 3 && x (-1) 10).toNat = 0 := by
    have r9759 := hand1 (x (-1) 3) (x (-1) 10)
    have b9760 := hb (x (-1) 3)
    have b9761 := hb (x (-1) 3 && x (-1) 10)
    clear * - r9759 b9760 b9761 d9746
    omega
  have d9762 : (x (-1) 3 && x (-1) 9).toNat = 0 := by
    have r9763 := hand1 (x (-1) 3) (x (-1) 9)
    have b9764 := hb (x (-1) 3)
    have b9765 := hb (x (-1) 3 && x (-1) 9)
    clear * - r9763 b9764 b9765 d9746
    omega
  have d9766 : (x (-1) 3 && x (-1) 7).toNat = 0 := by
    have r9767 := hand1 (x (-1) 3) (x (-1) 7)
    have b9768 := hb (x (-1) 3)
    have b9769 := hb (x (-1) 3 && x (-1) 7)
    clear * - r9767 b9768 b9769 d9746
    omega
  have d9770 : (x (-1) 11).toNat = 0 := by
    have r9771 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
    have b9772 := hb (x (-1) 3)
    have b9773 := hb (x (-1) 11)
    clear * - r9771 b9772 b9773 d9746
    omega
  have d9774 : (x (-1) 7 && x (-1) 11).toNat = 0 := by
    have r9775 := hand2 (x (-1) 7) (x (-1) 11)
    have b9776 := hb (x (-1) 11)
    have b9777 := hb (x (-1) 7 && x (-1) 11)
    clear * - r9775 b9776 b9777 d9770
    omega
  have d9778 : (x (-1) 10).toNat = 0 := by
    have r9779 : (x (-1) 10).toNat ≤ (x (-1) 2).toNat := himp _ _ (hp10 (-1))
    have b9780 := hb (x (-1) 2)
    have b9781 := hb (x (-1) 10)
    clear * - r9779 b9780 b9781 d9738
    omega
  have d9782 : (x (-1) 13).toNat = 0 := by
    have r9783 : (x (-1) 13).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp13 (-1))
    have b9784 := hb (x (-1) 1)
    have b9785 := hb (x (-1) 13)
    clear * - r9783 b9784 b9785 d9726
    omega
  have d9786 : (x (-1) 7 && x (-1) 13).toNat = 0 := by
    have r9787 := hand2 (x (-1) 7) (x (-1) 13)
    have b9788 := hb (x (-1) 13)
    have b9789 := hb (x (-1) 7 && x (-1) 13)
    clear * - r9787 b9788 b9789 d9782
    omega
  have d9790 : (x (-1) 9 && x (-1) 13).toNat = 0 := by
    have r9791 := hand2 (x (-1) 9) (x (-1) 13)
    have b9792 := hb (x (-1) 13)
    have b9793 := hb (x (-1) 9 && x (-1) 13)
    clear * - r9791 b9792 b9793 d9782
    omega
  have d9794 : (x (-1) 5).toNat = 0 := by
    have r9795 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
    have b9796 := hb (x (-1) 5)
    have b9797 := hb (x (-1) 13)
    clear * - r9795 b9796 b9797 d9782
    omega
  have d9798 : (x (-1) 5 && x (-1) 12).toNat = 0 := by
    have r9799 := hand1 (x (-1) 5) (x (-1) 12)
    have b9800 := hb (x (-1) 5)
    have b9801 := hb (x (-1) 5 && x (-1) 12)
    clear * - r9799 b9800 b9801 d9794
    omega
  have d9802 : (x (-1) 9).toNat = 0 := by
    have r9803 : (x (-1) 9).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp9 (-1))
    have b9804 := hb (x (-1) 1)
    have b9805 := hb (x (-1) 9)
    clear * - r9803 b9804 b9805 d9726
    omega
  have d9806 : (x (-2) 1).toNat = 1 := by
    have r9807 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9808 := hb (x (-2) 1)
    have b9809 := hb (x (-1) 14)
    clear * - r9807 b9808 b9809 d9734
    omega
  have d9810 : (x (-2) 14).toNat = 1 := by
    have r9811 : (x (-2) 1).toNat = (x (-2) 14).toNat := congrArg Bool.toNat (h114 (-2))
    have b9812 := hb (x (-2) 1)
    have b9813 := hb (x (-2) 14)
    clear * - r9811 b9812 b9813 d9806
    omega
  have d9814 : (x (-3) 1).toNat = 0 := by
    have r9815 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9816 := hb (x (-3) 1)
    have b9817 := hb (x (-2) 14)
    clear * - r9815 b9816 b9817 d9810
    omega
  have d9818 : (x (-3) 14).toNat = 0 := by
    have r9819 : (x (-3) 1).toNat = (x (-3) 14).toNat := congrArg Bool.toNat (h114 (-3))
    have b9820 := hb (x (-3) 1)
    have b9821 := hb (x (-3) 14)
    clear * - r9819 b9820 b9821 d9814
    omega
  have d9822 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
    have r9823 := hand2 (x (-3) 3) (x (-3) 14)
    have b9824 := hb (x (-3) 14)
    have b9825 := hb (x (-3) 3 && x (-3) 14)
    clear * - r9823 b9824 b9825 d9818
    omega
  have d9826 : (x (-3) 4 && x (-3) 14).toNat = 0 := by
    have r9827 := hand2 (x (-3) 4) (x (-3) 14)
    have b9828 := hb (x (-3) 14)
    have b9829 := hb (x (-3) 4 && x (-3) 14)
    clear * - r9827 b9828 b9829 d9818
    omega
  have d9830 : (x (-3) 5 && x (-3) 14).toNat = 0 := by
    have r9831 := hand2 (x (-3) 5) (x (-3) 14)
    have b9832 := hb (x (-3) 14)
    have b9833 := hb (x (-3) 5 && x (-3) 14)
    clear * - r9831 b9832 b9833 d9818
    omega
  have d9834 : (x (-3) 7 && x (-3) 14).toNat = 0 := by
    have r9835 := hand2 (x (-3) 7) (x (-3) 14)
    have b9836 := hb (x (-3) 14)
    have b9837 := hb (x (-3) 7 && x (-3) 14)
    clear * - r9835 b9836 b9837 d9818
    omega
  have d9838 : (x (-3) 9 && x (-3) 14).toNat = 0 := by
    have r9839 := hand2 (x (-3) 9) (x (-3) 14)
    have b9840 := hb (x (-3) 14)
    have b9841 := hb (x (-3) 9 && x (-3) 14)
    clear * - r9839 b9840 b9841 d9818
    omega
  have d9842 : (x (-3) 6).toNat = 0 := by
    have r9843 : (x (-3) 6).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp6 (-3))
    have b9844 := hb (x (-3) 6)
    have b9845 := hb (x (-3) 14)
    clear * - r9843 b9844 b9845 d9818
    omega
  have d9846 : (x (-3) 2).toNat = 0 := by
    have r9847 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
    have b9848 := hb (x (-3) 2)
    have b9849 := hb (x (-3) 14)
    clear * - r9847 b9848 b9849 d9818
    omega
  have d9850 : (x (-3) 3).toNat = 0 := by
    have r9851 : (x (-3) 2).toNat = (x (-3) 3).toNat := congrArg Bool.toNat (h23 (-3))
    have b9852 := hb (x (-3) 2)
    have b9853 := hb (x (-3) 3)
    clear * - r9851 b9852 b9853 d9846
    omega
  have d9854 : (x (-3) 11).toNat = 0 := by
    have r9855 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
    have b9856 := hb (x (-3) 3)
    have b9857 := hb (x (-3) 11)
    clear * - r9855 b9856 b9857 d9850
    omega
  have d9858 : (x (-3) 5 && x (-3) 11).toNat = 0 := by
    have r9859 := hand2 (x (-3) 5) (x (-3) 11)
    have b9860 := hb (x (-3) 11)
    have b9861 := hb (x (-3) 5 && x (-3) 11)
    clear * - r9859 b9860 b9861 d9854
    omega
  have d9862 : (x (-3) 13).toNat = 0 := by
    have r9863 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
    have b9864 := hb (x (-3) 1)
    have b9865 := hb (x (-3) 13)
    clear * - r9863 b9864 b9865 d9814
    omega
  have d9866 : (x (-3) 9 && x (-3) 13).toNat = 0 := by
    have r9867 := hand2 (x (-3) 9) (x (-3) 13)
    have b9868 := hb (x (-3) 13)
    have b9869 := hb (x (-3) 9 && x (-3) 13)
    clear * - r9867 b9868 b9869 d9862
    omega
  have d9870 : (x (-3) 5).toNat = 0 := by
    have r9871 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
    have b9872 := hb (x (-3) 5)
    have b9873 := hb (x (-3) 13)
    clear * - r9871 b9872 b9873 d9862
    omega
  have d9874 : (x (-3) 5 && x (-3) 12).toNat = 0 := by
    have r9875 := hand1 (x (-3) 5) (x (-3) 12)
    have b9876 := hb (x (-3) 5)
    have b9877 := hb (x (-3) 5 && x (-3) 12)
    clear * - r9875 b9876 b9877 d9870
    omega
  have d9878 : (x (-3) 5 && x (-3) 9).toNat = 0 := by
    have r9879 := hand1 (x (-3) 5) (x (-3) 9)
    have b9880 := hb (x (-3) 5)
    have b9881 := hb (x (-3) 5 && x (-3) 9)
    clear * - r9879 b9880 b9881 d9870
    omega
  have d9882 : (x (-3) 9).toNat = 0 := by
    have r9883 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
    have b9884 := hb (x (-3) 1)
    have b9885 := hb (x (-3) 9)
    clear * - r9883 b9884 b9885 d9814
    omega
  have d9886 : (x (-4) 1).toNat = 1 := by
    have r9887 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9888 := hb (x (-4) 1)
    have b9889 := hb (x (-3) 14)
    clear * - r9887 b9888 b9889 d9818
    omega
  have d9890 : (x (-4) 14).toNat = 1 := by
    have r9891 : (x (-4) 1).toNat = (x (-4) 14).toNat := congrArg Bool.toNat (h114 (-4))
    have b9892 := hb (x (-4) 1)
    have b9893 := hb (x (-4) 14)
    clear * - r9891 b9892 b9893 d9886
    omega
  have d9894 : (x (-5) 1).toNat = 0 := by
    have r9895 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9896 := hb (x (-5) 1)
    have b9897 := hb (x (-4) 14)
    clear * - r9895 b9896 b9897 d9890
    omega
  have d9898 : (x (-5) 1 && x (-5) 14).toNat = 0 := by
    have r9899 := hand1 (x (-5) 1) (x (-5) 14)
    have b9900 := hb (x (-5) 1)
    have b9901 := hb (x (-5) 1 && x (-5) 14)
    clear * - r9899 b9900 b9901 d9894
    omega
  have d9902 : (x (-5) 1 && x (-5) 11).toNat = 0 := by
    have r9903 := hand1 (x (-5) 1) (x (-5) 11)
    have b9904 := hb (x (-5) 1)
    have b9905 := hb (x (-5) 1 && x (-5) 11)
    clear * - r9903 b9904 b9905 d9894
    omega
  have d9906 : (x (-5) 14).toNat = 0 := by
    have r9907 : (x (-5) 1).toNat = (x (-5) 14).toNat := congrArg Bool.toNat (h114 (-5))
    have b9908 := hb (x (-5) 1)
    have b9909 := hb (x (-5) 14)
    clear * - r9907 b9908 b9909 d9894
    omega
  have d9910 : (x (-5) 7 && x (-5) 14).toNat = 0 := by
    have r9911 := hand2 (x (-5) 7) (x (-5) 14)
    have b9912 := hb (x (-5) 14)
    have b9913 := hb (x (-5) 7 && x (-5) 14)
    clear * - r9911 b9912 b9913 d9906
    omega
  have d9914 : (x (-5) 6).toNat = 0 := by
    have r9915 : (x (-5) 6).toNat ≤ (x (-5) 14).toNat := himp _ _ (hp6 (-5))
    have b9916 := hb (x (-5) 6)
    have b9917 := hb (x (-5) 14)
    clear * - r9915 b9916 b9917 d9906
    omega
  have d9918 : (x (-5) 2).toNat = 0 := by
    have r9919 : (x (-5) 2).toNat ≤ (x (-5) 14).toNat := himp _ _ (hp2 (-5))
    have b9920 := hb (x (-5) 2)
    have b9921 := hb (x (-5) 14)
    clear * - r9919 b9920 b9921 d9906
    omega
  have d9922 : (x (-5) 3).toNat = 0 := by
    have r9923 : (x (-5) 2).toNat = (x (-5) 3).toNat := congrArg Bool.toNat (h23 (-5))
    have b9924 := hb (x (-5) 2)
    have b9925 := hb (x (-5) 3)
    clear * - r9923 b9924 b9925 d9918
    omega
  have d9926 : (x (-5) 11).toNat = 0 := by
    have r9927 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
    have b9928 := hb (x (-5) 3)
    have b9929 := hb (x (-5) 11)
    clear * - r9927 b9928 b9929 d9922
    omega
  have d9930 : (x (-5) 7 && x (-5) 11).toNat = 0 := by
    have r9931 := hand2 (x (-5) 7) (x (-5) 11)
    have b9932 := hb (x (-5) 11)
    have b9933 := hb (x (-5) 7 && x (-5) 11)
    clear * - r9931 b9932 b9933 d9926
    omega
  have d9934 : (x (-5) 13).toNat = 0 := by
    have r9935 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
    have b9936 := hb (x (-5) 1)
    have b9937 := hb (x (-5) 13)
    clear * - r9935 b9936 b9937 d9894
    omega
  have d9938 : (x (-5) 7 && x (-5) 13).toNat = 0 := by
    have r9939 := hand2 (x (-5) 7) (x (-5) 13)
    have b9940 := hb (x (-5) 13)
    have b9941 := hb (x (-5) 7 && x (-5) 13)
    clear * - r9939 b9940 b9941 d9934
    omega
  have d9942 : (x (-5) 5).toNat = 0 := by
    have r9943 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
    have b9944 := hb (x (-5) 5)
    have b9945 := hb (x (-5) 13)
    clear * - r9943 b9944 b9945 d9934
    omega
  have d9946 : (x (-5) 9).toNat = 0 := by
    have r9947 : (x (-5) 9).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp9 (-5))
    have b9948 := hb (x (-5) 1)
    have b9949 := hb (x (-5) 9)
    clear * - r9947 b9948 b9949 d9894
    omega
  have d9950 : (x (-6) 1).toNat = 1 := by
    have r9951 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9952 := hb (x (-6) 1)
    have b9953 := hb (x (-5) 14)
    clear * - r9951 b9952 b9953 d9906
    omega
  have d9954 : (x (-6) 14).toNat = 1 := by
    have r9955 : (x (-6) 1).toNat = (x (-6) 14).toNat := congrArg Bool.toNat (h114 (-6))
    have b9956 := hb (x (-6) 1)
    have b9957 := hb (x (-6) 14)
    clear * - r9955 b9956 b9957 d9950
    omega
  have d9958 : (x (-7) 1).toNat = 0 := by
    have r9959 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9960 := hb (x (-7) 1)
    have b9961 := hb (x (-6) 14)
    clear * - r9959 b9960 b9961 d9954
    omega
  have d9962 : (x (-7) 1 && x (-7) 11).toNat = 0 := by
    have r9963 := hand1 (x (-7) 1) (x (-7) 11)
    have b9964 := hb (x (-7) 1)
    have b9965 := hb (x (-7) 1 && x (-7) 11)
    clear * - r9963 b9964 b9965 d9958
    omega
  have d9966 : (x (-7) 14).toNat = 0 := by
    have r9967 : (x (-7) 1).toNat = (x (-7) 14).toNat := congrArg Bool.toNat (h114 (-7))
    have b9968 := hb (x (-7) 1)
    have b9969 := hb (x (-7) 14)
    clear * - r9967 b9968 b9969 d9958
    omega
  have d9970 : (x (-7) 2).toNat = 0 := by
    have r9971 : (x (-7) 2).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp2 (-7))
    have b9972 := hb (x (-7) 2)
    have b9973 := hb (x (-7) 14)
    clear * - r9971 b9972 b9973 d9966
    omega
  have d9974 : (x (-7) 3).toNat = 0 := by
    have r9975 : (x (-7) 2).toNat = (x (-7) 3).toNat := congrArg Bool.toNat (h23 (-7))
    have b9976 := hb (x (-7) 2)
    have b9977 := hb (x (-7) 3)
    clear * - r9975 b9976 b9977 d9970
    omega
  have d9978 : (x (-7) 3 && x (-7) 13).toNat = 0 := by
    have r9979 := hand1 (x (-7) 3) (x (-7) 13)
    have b9980 := hb (x (-7) 3)
    have b9981 := hb (x (-7) 3 && x (-7) 13)
    clear * - r9979 b9980 b9981 d9974
    omega
  have d9982 : (x (-7) 11).toNat = 0 := by
    have r9983 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
    have b9984 := hb (x (-7) 3)
    have b9985 := hb (x (-7) 11)
    clear * - r9983 b9984 b9985 d9974
    omega
  have d9986 : (x (-7) 13).toNat = 0 := by
    have r9987 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
    have b9988 := hb (x (-7) 1)
    have b9989 := hb (x (-7) 13)
    clear * - r9987 b9988 b9989 d9958
    omega
  have d9990 : (x (-7) 9 && x (-7) 13).toNat = 0 := by
    have r9991 := hand2 (x (-7) 9) (x (-7) 13)
    have b9992 := hb (x (-7) 13)
    have b9993 := hb (x (-7) 9 && x (-7) 13)
    clear * - r9991 b9992 b9993 d9986
    omega
  have d9994 : (x (-7) 9).toNat = 0 := by
    have r9995 : (x (-7) 9).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp9 (-7))
    have b9996 := hb (x (-7) 1)
    have b9997 := hb (x (-7) 9)
    clear * - r9995 b9996 b9997 d9958
    omega
  have d9998 : (x (-8) 1).toNat = 1 := by
    have r9999 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b10000 := hb (x (-8) 1)
    have b10001 := hb (x (-7) 14)
    clear * - r9999 b10000 b10001 d9966
    omega
  have d10002 : (x (-8) 14).toNat = 1 := by
    have r10003 : (x (-8) 1).toNat = (x (-8) 14).toNat := congrArg Bool.toNat (h114 (-8))
    have b10004 := hb (x (-8) 1)
    have b10005 := hb (x (-8) 14)
    clear * - r10003 b10004 b10005 d9998
    omega
  have d10006 : (x (-9) 1).toNat = 0 := by
    have r10007 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b10008 := hb (x (-9) 1)
    have b10009 := hb (x (-8) 14)
    clear * - r10007 b10008 b10009 d10002
    omega
  have d10010 : (x (-9) 14).toNat = 0 := by
    have r10011 : (x (-9) 1).toNat = (x (-9) 14).toNat := congrArg Bool.toNat (h114 (-9))
    have b10012 := hb (x (-9) 1)
    have b10013 := hb (x (-9) 14)
    clear * - r10011 b10012 b10013 d10006
    omega
  have d10014 : (x (-9) 2).toNat = 0 := by
    have r10015 : (x (-9) 2).toNat ≤ (x (-9) 14).toNat := himp _ _ (hp2 (-9))
    have b10016 := hb (x (-9) 2)
    have b10017 := hb (x (-9) 14)
    clear * - r10015 b10016 b10017 d10010
    omega
  have d10018 : (x (-9) 3).toNat = 0 := by
    have r10019 : (x (-9) 2).toNat = (x (-9) 3).toNat := congrArg Bool.toNat (h23 (-9))
    have b10020 := hb (x (-9) 2)
    have b10021 := hb (x (-9) 3)
    clear * - r10019 b10020 b10021 d10014
    omega
  have d10022 : (x (-9) 3 && x (-9) 13).toNat = 0 := by
    have r10023 := hand1 (x (-9) 3) (x (-9) 13)
    have b10024 := hb (x (-9) 3)
    have b10025 := hb (x (-9) 3 && x (-9) 13)
    clear * - r10023 b10024 b10025 d10018
    omega
  have d10026 : (x (-9) 11).toNat = 0 := by
    have r10027 : (x (-9) 11).toNat ≤ (x (-9) 3).toNat := himp _ _ (hp11 (-9))
    have b10028 := hb (x (-9) 3)
    have b10029 := hb (x (-9) 11)
    clear * - r10027 b10028 b10029 d10018
    omega
  have d10030 : (x (-9) 13).toNat = 0 := by
    have r10031 : (x (-9) 13).toNat ≤ (x (-9) 1).toNat := himp _ _ (hp13 (-9))
    have b10032 := hb (x (-9) 1)
    have b10033 := hb (x (-9) 13)
    clear * - r10031 b10032 b10033 d10006
    omega
  have d10034 : (x (-9) 5).toNat = 0 := by
    have r10035 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
    have b10036 := hb (x (-9) 5)
    have b10037 := hb (x (-9) 13)
    clear * - r10035 b10036 b10037 d10030
    omega
  have d10038 : (x (-10) 1).toNat = 1 := by
    have r10039 : (x (-9) 14).toNat + (x (-10) 1).toNat = 1 := by have q := hd14 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b10040 := hb (x (-10) 1)
    have b10041 := hb (x (-9) 14)
    clear * - r10039 b10040 b10041 d10010
    omega
  have d10042 : (x (-10) 14).toNat = 1 := by
    have r10043 : (x (-10) 1).toNat = (x (-10) 14).toNat := congrArg Bool.toNat (h114 (-10))
    have b10044 := hb (x (-10) 1)
    have b10045 := hb (x (-10) 14)
    clear * - r10043 b10044 b10045 d10038
    omega
  have d10046 : (x 3 12).toNat = 0 := by
    have r10047 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10048 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e10049 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b10050 := hb (x 0 3)
    have b10051 := hb (x 1 2)
    have b10052 := hb (x 2 13)
    have b10053 := hb (x 3 12)
    clear * - r10047 e10048 e10049 b10050 b10051 b10052 b10053 d9702 d9374
    omega
  have d10054 : (x 3 8 && x 3 12).toNat = 0 := by
    have r10055 := hand2 (x 3 8) (x 3 12)
    have b10056 := hb (x 3 12)
    have b10057 := hb (x 3 8 && x 3 12)
    clear * - r10055 b10056 b10057 d10046
    omega
  have d10058 : (x 2 13).toNat = 0 := by
    have r10059 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10060 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e10061 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b10062 := hb (x 0 3)
    have b10063 := hb (x 1 2)
    have b10064 := hb (x 2 13)
    have b10065 := hb (x 3 12)
    clear * - r10059 e10060 e10061 b10062 b10063 b10064 b10065 d10046 d9702 d9374
    omega
  have d10066 : (x 2 2 && x 2 13).toNat = 0 := by
    have r10067 := hand2 (x 2 2) (x 2 13)
    have b10068 := hb (x 2 13)
    have b10069 := hb (x 2 2 && x 2 13)
    clear * - r10067 b10068 b10069 d10058
    omega
  have d10070 : (x 2 9 && x 2 13).toNat = 0 := by
    have r10071 := hand2 (x 2 9) (x 2 13)
    have b10072 := hb (x 2 13)
    have b10073 := hb (x 2 9 && x 2 13)
    clear * - r10071 b10072 b10073 d10058
    omega
  have d10074 : (x 2 12).toNat = 0 := by
    have r10075 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10076 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e10077 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b10078 := hb (x (-1) 3)
    have b10079 := hb (x 0 2)
    have b10080 := hb (x 1 13)
    have b10081 := hb (x 2 12)
    clear * - r10075 e10076 e10077 b10078 b10079 b10080 b10081 d9414 d9370 d9746
    omega
  have d10082 : (x 2 2 && x 2 12).toNat = 0 := by
    have r10083 := hand2 (x 2 2) (x 2 12)
    have b10084 := hb (x 2 12)
    have b10085 := hb (x 2 2 && x 2 12)
    clear * - r10083 b10084 b10085 d10074
    omega
  have d10086 : (x 2 4).toNat = 0 := by
    have r10087 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
    have b10088 := hb (x 2 4)
    have b10089 := hb (x 2 12)
    clear * - r10087 b10088 b10089 d10074
    omega
  have d10090 : (x 2 4 && x 2 14).toNat = 0 := by
    have r10091 := hand1 (x 2 4) (x 2 14)
    have b10092 := hb (x 2 4)
    have b10093 := hb (x 2 4 && x 2 14)
    clear * - r10091 b10092 b10093 d10086
    omega
  have d10094 : (x 2 4 && x 2 10).toNat = 0 := by
    have r10095 := hand1 (x 2 4) (x 2 10)
    have b10096 := hb (x 2 4)
    have b10097 := hb (x 2 4 && x 2 10)
    clear * - r10095 b10096 b10097 d10086
    omega
  have d10098 : (x 2 4 && x 2 9).toNat = 0 := by
    have r10099 := hand1 (x 2 4) (x 2 9)
    have b10100 := hb (x 2 4)
    have b10101 := hb (x 2 4 && x 2 9)
    clear * - r10099 b10100 b10101 d10086
    omega
  have d10102 : (x 2 4 && x 2 8).toNat = 0 := by
    have r10103 := hand1 (x 2 4) (x 2 8)
    have b10104 := hb (x 2 4)
    have b10105 := hb (x 2 4 && x 2 8)
    clear * - r10103 b10104 b10105 d10086
    omega
  have d10106 : (x 2 8).toNat = 0 := by
    have r10107 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10108 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
    have e10109 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
    have e10110 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
    have e10111 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
    have e10112 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
    have e10113 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
    have b10114 := hb (x (-5) 7)
    have b10115 := hb (x (-4) 6)
    have b10116 := hb (x (-3) 5)
    have b10117 := hb (x (-2) 4)
    have b10118 := hb (x (-1) 11)
    have b10119 := hb (x 0 10)
    have b10120 := hb (x 1 9)
    have b10121 := hb (x 2 8)
    clear * - r10107 e10108 e10109 e10110 e10111 e10112 e10113 b10114 b10115 b10116 b10117 b10118 b10119 b10120 b10121 d9438 g0 d9770 d9870
    omega
  have d10122 : (x (-2) 4).toNat = 0 := by
    have r10123 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10124 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
    have e10125 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
    have e10126 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
    have e10127 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
    have e10128 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
    have e10129 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
    have b10130 := hb (x (-5) 7)
    have b10131 := hb (x (-4) 6)
    have b10132 := hb (x (-3) 5)
    have b10133 := hb (x (-2) 4)
    have b10134 := hb (x (-1) 11)
    have b10135 := hb (x 0 10)
    have b10136 := hb (x 1 9)
    have b10137 := hb (x 2 8)
    clear * - r10123 e10124 e10125 e10126 e10127 e10128 e10129 b10130 b10131 b10132 b10133 b10134 b10135 b10136 b10137 d10106 d9438 g0 d9770 d9870
    omega
  have d10138 : (x (-2) 4 && x (-2) 14).toNat = 0 := by
    have r10139 := hand1 (x (-2) 4) (x (-2) 14)
    have b10140 := hb (x (-2) 4)
    have b10141 := hb (x (-2) 4 && x (-2) 14)
    clear * - r10139 b10140 b10141 d10122
    omega
  have d10142 : (x (-2) 4 && x (-2) 13).toNat = 0 := by
    have r10143 := hand1 (x (-2) 4) (x (-2) 13)
    have b10144 := hb (x (-2) 4)
    have b10145 := hb (x (-2) 4 && x (-2) 13)
    clear * - r10143 b10144 b10145 d10122
    omega
  have d10146 : (x (-2) 4 && x (-2) 11).toNat = 0 := by
    have r10147 := hand1 (x (-2) 4) (x (-2) 11)
    have b10148 := hb (x (-2) 4)
    have b10149 := hb (x (-2) 4 && x (-2) 11)
    clear * - r10147 b10148 b10149 d10122
    omega
  have d10150 : (x (-2) 4 && x (-2) 10).toNat = 0 := by
    have r10151 := hand1 (x (-2) 4) (x (-2) 10)
    have b10152 := hb (x (-2) 4)
    have b10153 := hb (x (-2) 4 && x (-2) 10)
    clear * - r10151 b10152 b10153 d10122
    omega
  have d10154 : (x (-2) 4 && x (-2) 8).toNat = 0 := by
    have r10155 := hand1 (x (-2) 4) (x (-2) 8)
    have b10156 := hb (x (-2) 4)
    have b10157 := hb (x (-2) 4 && x (-2) 8)
    clear * - r10155 b10156 b10157 d10122
    omega
  have d10158 : (x (-4) 6).toNat = 0 := by
    have r10159 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10160 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
    have e10161 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
    have e10162 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
    have e10163 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
    have e10164 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
    have e10165 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
    have b10166 := hb (x (-5) 7)
    have b10167 := hb (x (-4) 6)
    have b10168 := hb (x (-3) 5)
    have b10169 := hb (x (-2) 4)
    have b10170 := hb (x (-1) 11)
    have b10171 := hb (x 0 10)
    have b10172 := hb (x 1 9)
    have b10173 := hb (x 2 8)
    clear * - r10159 e10160 e10161 e10162 e10163 e10164 e10165 b10166 b10167 b10168 b10169 b10170 b10171 b10172 b10173 d10106 d9438 g0 d9770 d10122 d9870
    omega
  have d10174 : (x (-4) 6 && x (-4) 13).toNat = 0 := by
    have r10175 := hand1 (x (-4) 6) (x (-4) 13)
    have b10176 := hb (x (-4) 6)
    have b10177 := hb (x (-4) 6 && x (-4) 13)
    clear * - r10175 b10176 b10177 d10158
    omega
  have d10178 : (x (-4) 6 && x (-4) 12).toNat = 0 := by
    have r10179 := hand1 (x (-4) 6) (x (-4) 12)
    have b10180 := hb (x (-4) 6)
    have b10181 := hb (x (-4) 6 && x (-4) 12)
    clear * - r10179 b10180 b10181 d10158
    omega
  have d10182 : (x (-4) 6 && x (-4) 10).toNat = 0 := by
    have r10183 := hand1 (x (-4) 6) (x (-4) 10)
    have b10184 := hb (x (-4) 6)
    have b10185 := hb (x (-4) 6 && x (-4) 10)
    clear * - r10183 b10184 b10185 d10158
    omega
  have d10186 : (x 2 9).toNat = 1 := by
    have r10187 : 1 ≤ (x 2 9).toNat + (x 1 1 && x 1 10).toNat + (x 0 2 && x 0 11).toNat + (x (-1) 3 && x (-1) 12).toNat + (x (-2) 4 && x (-2) 13).toNat + (x (-3) 5 && x (-3) 14).toNat + (x (-4) 6).toNat := by have q := hcov9 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b10188 := hb (x (-4) 6)
    have b10189 := hb (x 2 9)
    have b10190 := hb (x 1 1 && x 1 10)
    have b10191 := hb (x 0 2 && x 0 11)
    have b10192 := hb (x (-1) 3 && x (-1) 12)
    have b10193 := hb (x (-2) 4 && x (-2) 13)
    have b10194 := hb (x (-3) 5 && x (-3) 14)
    clear * - r10187 b10188 b10189 b10190 b10191 b10192 b10193 b10194 d9402 d9358 d9754 d10142 d9830 d10158
    omega
  have d10195 : (x 3 8).toNat = 0 := by
    have r10196 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10197 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
    have e10198 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
    have e10199 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
    have e10200 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
    have e10201 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
    have e10202 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
    have b10203 := hb (x (-4) 7)
    have b10204 := hb (x (-3) 6)
    have b10205 := hb (x (-2) 5)
    have b10206 := hb (x (-1) 4)
    have b10207 := hb (x 0 11)
    have b10208 := hb (x 1 10)
    have b10209 := hb (x 2 9)
    have b10210 := hb (x 3 8)
    clear * - r10196 e10197 e10198 e10199 e10200 e10201 e10202 b10203 b10204 b10205 b10206 b10207 b10208 b10209 b10210 d10186 d9722 g1 d9842
    omega
  cases h10211 : x 0 4
  · have f10212 : (x 0 4).toNat = 0 := by rw [h10211]; rfl
    have d10213 : (x 0 4 && x 0 14).toNat = 0 := by
      have r10214 := hand1 (x 0 4) (x 0 14)
      have b10215 := hb (x 0 4)
      have b10216 := hb (x 0 4 && x 0 14)
      clear * - r10214 b10215 b10216 f10212
      omega
    have d10217 : (x 4 11).toNat = 1 := by
      have r10218 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b10219 := hb (x 0 4)
      have b10220 := hb (x 4 11)
      have b10221 := hb (x 3 1 && x 3 12)
      have b10222 := hb (x 2 2 && x 2 13)
      have b10223 := hb (x 1 3 && x 1 14)
      clear * - r10218 b10219 b10220 b10221 b10222 b10223 d9462 d10066 d9390 f10212
      omega
    have d10224 : (x 4 3).toNat = 1 := by
      have r10225 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
      have b10226 := hb (x 4 3)
      have b10227 := hb (x 4 11)
      clear * - r10225 b10226 b10227 d10217
      omega
    have d10228 : (x 4 2).toNat = 1 := by
      have r10229 : (x 4 2).toNat = (x 4 3).toNat := congrArg Bool.toNat (h23 4)
      have b10230 := hb (x 4 2)
      have b10231 := hb (x 4 3)
      clear * - r10229 b10230 b10231 d10224
      omega
    have d10232 : (x 6 12).toNat = 0 := by
      have r10233 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10234 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e10235 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b10236 := hb (x 3 3)
      have b10237 := hb (x 4 2)
      have b10238 := hb (x 5 13)
      have b10239 := hb (x 6 12)
      clear * - r10233 e10234 e10235 b10236 b10237 b10238 b10239 d9534 d10228 d9686
      omega
    have d10240 : (x 6 4).toNat = 0 := by
      have r10241 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
      have b10242 := hb (x 6 4)
      have b10243 := hb (x 6 12)
      clear * - r10241 b10242 b10243 d10232
      omega
    have d10244 : (x 6 4 && x 6 14).toNat = 0 := by
      have r10245 := hand1 (x 6 4) (x 6 14)
      have b10246 := hb (x 6 4)
      have b10247 := hb (x 6 4 && x 6 14)
      clear * - r10245 b10246 b10247 d10240
      omega
    have d10248 : (x 7 12).toNat = 0 := by
      have r10249 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10250 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
      have e10251 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
      have b10252 := hb (x 4 3)
      have b10253 := hb (x 5 2)
      have b10254 := hb (x 6 13)
      have b10255 := hb (x 7 12)
      clear * - r10249 e10250 e10251 b10252 b10253 b10254 b10255 d9662 d10224
      omega
    have d10256 : (x 7 4).toNat = 0 := by
      have r10257 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
      have b10258 := hb (x 7 4)
      have b10259 := hb (x 7 12)
      clear * - r10257 b10258 b10259 d10248
      omega
    have d10260 : (x 7 4 && x 7 8).toNat = 0 := by
      have r10261 := hand1 (x 7 4) (x 7 8)
      have b10262 := hb (x 7 4)
      have b10263 := hb (x 7 4 && x 7 8)
      clear * - r10261 b10262 b10263 d10256
      omega
    have d10264 : (x 6 13).toNat = 0 := by
      have r10265 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10266 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
      have e10267 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
      have b10268 := hb (x 4 3)
      have b10269 := hb (x 5 2)
      have b10270 := hb (x 6 13)
      have b10271 := hb (x 7 12)
      clear * - r10265 e10266 e10267 b10268 b10269 b10270 b10271 d10248 d9662 d10224
      omega
    have d10272 : (x 6 2 && x 6 13).toNat = 0 := by
      have r10273 := hand2 (x 6 2) (x 6 13)
      have b10274 := hb (x 6 13)
      have b10275 := hb (x 6 2 && x 6 13)
      clear * - r10273 b10274 b10275 d10264
      omega
    have d10276 : (x 6 5).toNat = 0 := by
      have r10277 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
      have b10278 := hb (x 6 5)
      have b10279 := hb (x 6 13)
      clear * - r10277 b10278 b10279 d10264
      omega
    have d10280 : (x 6 5 && x 6 9).toNat = 0 := by
      have r10281 := hand1 (x 6 5) (x 6 9)
      have b10282 := hb (x 6 5)
      have b10283 := hb (x 6 5 && x 6 9)
      clear * - r10281 b10282 b10283 d10276
      omega
    have d10284 : (x 4 10).toNat = 1 := by
      have r10285 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b10286 := hb (x (-1) 5)
      have b10287 := hb (x 4 10)
      have b10288 := hb (x 3 1 && x 3 11)
      have b10289 := hb (x 2 2 && x 2 12)
      have b10290 := hb (x 1 3 && x 1 13)
      have b10291 := hb (x 0 4 && x 0 14)
      clear * - r10285 b10286 b10287 b10288 b10289 b10290 b10291 d9466 d10082 d9418 d10213 d9794
      omega
    have d10292 : (x 6 8).toNat = 0 := by
      have r10293 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10294 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e10295 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e10296 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e10297 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e10298 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e10299 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b10300 := hb (x (-1) 7)
      have b10301 := hb (x 0 6)
      have b10302 := hb (x 1 5)
      have b10303 := hb (x 2 4)
      have b10304 := hb (x 3 11)
      have b10305 := hb (x 4 10)
      have b10306 := hb (x 5 9)
      have b10307 := hb (x 6 8)
      clear * - r10293 e10294 e10295 e10296 e10297 e10298 e10299 b10300 b10301 b10302 b10303 b10304 b10305 b10306 b10307 d9542 d10284 d9698 d10086 d9422
      omega
    have d10308 : (x 0 6).toNat = 0 := by
      have r10309 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10310 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e10311 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e10312 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e10313 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e10314 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e10315 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b10316 := hb (x (-1) 7)
      have b10317 := hb (x 0 6)
      have b10318 := hb (x 1 5)
      have b10319 := hb (x 2 4)
      have b10320 := hb (x 3 11)
      have b10321 := hb (x 4 10)
      have b10322 := hb (x 5 9)
      have b10323 := hb (x 6 8)
      clear * - r10309 e10310 e10311 e10312 e10313 e10314 e10315 b10316 b10317 b10318 b10319 b10320 b10321 b10322 b10323 d10292 d9542 d10284 d9698 d10086 d9422
      omega
    have d10324 : (x 0 6 && x 0 12).toNat = 0 := by
      have r10325 := hand1 (x 0 6) (x 0 12)
      have b10326 := hb (x 0 6)
      have b10327 := hb (x 0 6 && x 0 12)
      clear * - r10325 b10326 b10327 d10308
      omega
    have d10328 : (x 0 6 && x 0 10).toNat = 0 := by
      have r10329 := hand1 (x 0 6) (x 0 10)
      have b10330 := hb (x 0 6)
      have b10331 := hb (x 0 6 && x 0 10)
      clear * - r10329 b10330 b10331 d10308
      omega
    have d10332 : (x 0 2 && x 0 6).toNat = 0 := by
      have r10333 := hand2 (x 0 2) (x 0 6)
      have b10334 := hb (x 0 6)
      have b10335 := hb (x 0 2 && x 0 6)
      clear * - r10333 b10334 b10335 d10308
      omega
    have d10336 : (x (-1) 7).toNat = 0 := by
      have r10337 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10338 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e10339 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e10340 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e10341 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e10342 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e10343 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b10344 := hb (x (-1) 7)
      have b10345 := hb (x 0 6)
      have b10346 := hb (x 1 5)
      have b10347 := hb (x 2 4)
      have b10348 := hb (x 3 11)
      have b10349 := hb (x 4 10)
      have b10350 := hb (x 5 9)
      have b10351 := hb (x 6 8)
      clear * - r10337 e10338 e10339 e10340 e10341 e10342 e10343 b10344 b10345 b10346 b10347 b10348 b10349 b10350 b10351 d10292 d9542 d10284 d9698 d10086 d9422 d10308
      omega
    have d10352 : (x (-1) 7 && x (-1) 12).toNat = 0 := by
      have r10353 := hand1 (x (-1) 7) (x (-1) 12)
      have b10354 := hb (x (-1) 7)
      have b10355 := hb (x (-1) 7 && x (-1) 12)
      clear * - r10353 b10354 b10355 d10336
      omega
    have r10356 : (x 5 1).toNat + (x 4 2).toNat + (x 3 3).toNat + (x 2 4).toNat + (x 1 5).toNat + (x 0 6).toNat + (x (-1) 7).toNat + (x (-2) 8).toNat + (x (-3) 9).toNat + (x (-4) 10).toNat + (x (-5) 11).toNat + (x (-6) 12).toNat + (x (-7) 13).toNat + (x (-8) 14).toNat = 3 := by have q := hcount 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r10357 : (x 9 1).toNat + (x 8 2).toNat + (x 7 3).toNat + (x 6 4).toNat + (x 5 5).toNat + (x 4 6).toNat + (x 3 7).toNat + (x 2 8).toNat + (x 1 9).toNat + (x 0 10).toNat + (x (-1) 11).toNat + (x (-2) 12).toNat + (x (-3) 13).toNat + (x (-4) 14).toNat = 3 := by have q := hcount 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r10358 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r10359 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r10360 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10361 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
    have e10362 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
    have e10363 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
    have e10364 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
    have e10365 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
    have e10366 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
    have r10367 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10368 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e10369 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e10370 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e10371 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e10372 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e10373 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have r10374 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10375 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e10376 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e10377 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e10378 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e10379 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e10380 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have r10381 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10382 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
    have e10383 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
    have e10384 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
    have e10385 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
    have e10386 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
    have e10387 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
    have r10388 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10389 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e10390 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have r10391 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10392 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e10393 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have r10394 : 1 ≤ (x 2 4).toNat + (x 1 1 && x 1 5).toNat + (x 0 2 && x 0 6).toNat + (x (-1) 3 && x (-1) 7).toNat + (x (-2) 4 && x (-2) 8).toNat + (x (-3) 5 && x (-3) 9).toNat + (x (-4) 6 && x (-4) 10).toNat + (x (-5) 7 && x (-5) 11).toNat + (x (-6) 8 && x (-6) 12).toNat + (x (-7) 9 && x (-7) 13).toNat + (x (-8) 10 && x (-8) 14).toNat + (x (-9) 11).toNat := by have q := hcov4 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10395 : (x 1 1 && x 1 5).toNat = (x 1 5).toNat := handr _ _ (fun h => hp13 1 (hp5 1 (h)))
    have e10396 : (x (-8) 10 && x (-8) 14).toNat = (x (-8) 10).toNat := handl _ _ (fun h => hp2 (-8) (hp10 (-8) (h)))
    have r10397 : 1 ≤ (x 6 4).toNat + (x 5 1 && x 5 5).toNat + (x 4 2 && x 4 6).toNat + (x 3 3 && x 3 7).toNat + (x 2 4 && x 2 8).toNat + (x 1 5 && x 1 9).toNat + (x 0 6 && x 0 10).toNat + (x (-1) 7 && x (-1) 11).toNat + (x (-2) 8 && x (-2) 12).toNat + (x (-3) 9 && x (-3) 13).toNat + (x (-4) 10 && x (-4) 14).toNat + (x (-5) 11).toNat := by have q := hcov4 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10398 : (x 5 1 && x 5 5).toNat = (x 5 5).toNat := handr _ _ (fun h => hp13 5 (hp5 5 (h)))
    have e10399 : (x (-4) 10 && x (-4) 14).toNat = (x (-4) 10).toNat := handl _ _ (fun h => hp2 (-4) (hp10 (-4) (h)))
    have r10400 : 1 ≤ (x 11 4).toNat + (x 10 1 && x 10 5).toNat + (x 9 2 && x 9 6).toNat + (x 8 3 && x 8 7).toNat + (x 7 4 && x 7 8).toNat + (x 6 5 && x 6 9).toNat + (x 5 6 && x 5 10).toNat + (x 4 7 && x 4 11).toNat + (x 3 8 && x 3 12).toNat + (x 2 9 && x 2 13).toNat + (x 1 10 && x 1 14).toNat + (x 0 11).toNat := by have q := hcov4 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10401 : (x 10 1 && x 10 5).toNat = (x 10 5).toNat := handr _ _ (fun h => hp13 10 (hp5 10 (h)))
    have e10402 : (x 1 10 && x 1 14).toNat = (x 1 10).toNat := handl _ _ (fun h => hp2 1 (hp10 1 (h)))
    have r10403 : 1 ≤ (x 6 5).toNat + (x 5 1 && x 5 6).toNat + (x 4 2 && x 4 7).toNat + (x 3 3 && x 3 8).toNat + (x 2 4 && x 2 9).toNat + (x 1 5 && x 1 10).toNat + (x 0 6 && x 0 11).toNat + (x (-1) 7 && x (-1) 12).toNat + (x (-2) 8 && x (-2) 13).toNat + (x (-3) 9 && x (-3) 14).toNat + (x (-4) 10).toNat := by have q := hcov5 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r10404 : 1 ≤ (x 2 6).toNat + (x 1 1 && x 1 7).toNat + (x 0 2 && x 0 8).toNat + (x (-1) 3 && x (-1) 9).toNat + (x (-2) 4 && x (-2) 10).toNat + (x (-3) 5 && x (-3) 11).toNat + (x (-4) 6 && x (-4) 12).toNat + (x (-5) 7 && x (-5) 13).toNat + (x (-6) 8 && x (-6) 14).toNat + (x (-7) 9).toNat := by have q := hcov6 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r10405 : 1 ≤ (x 6 6).toNat + (x 5 1 && x 5 7).toNat + (x 4 2 && x 4 8).toNat + (x 3 3 && x 3 9).toNat + (x 2 4 && x 2 10).toNat + (x 1 5 && x 1 11).toNat + (x 0 6 && x 0 12).toNat + (x (-1) 7 && x (-1) 13).toNat + (x (-2) 8 && x (-2) 14).toNat + (x (-3) 9).toNat := by have q := hcov6 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r10406 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r10407 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r10408 : 1 ≤ (x 10 10).toNat + (x 9 1 && x 9 11).toNat + (x 8 2 && x 8 12).toNat + (x 7 3 && x 7 13).toNat + (x 6 4 && x 6 14).toNat + (x 5 5).toNat := by have q := hcov10 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r10409 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r10410 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r10411 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r10412 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
    have r10413 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
    have r10414 : (x 10 10).toNat ≤ (x 10 2).toNat := himp _ _ (hp10 10)
    have r10415 := hand2 (x (-6) 8) (x (-6) 12)
    have r10416 := hand2 (x 4 2) (x 4 6)
    have r10417 := hand2 (x (-2) 8) (x (-2) 12)
    have r10418 := hand2 (x 8 3) (x 8 7)
    have r10419 := hand1 (x 4 7) (x 4 11)
    have r10420 := hand2 (x 4 2) (x 4 7)
    have r10421 := hand2 (x (-2) 8) (x (-2) 13)
    have r10422 := hand2 (x 0 2) (x 0 8)
    have r10423 := hand1 (x (-6) 8) (x (-6) 14)
    have r10424 := hand2 (x 4 2) (x 4 8)
    have r10425 := hand1 (x (-2) 8) (x (-2) 14)
    have r10426 := hand2 (x 0 2) (x 0 12)
    have r10427 := hand2 (x 4 2) (x 4 12)
    have r10428 := hand1 (x 8 2) (x 8 12)
    have r10429 := hand1 (x (-2) 2) (x (-2) 13)
    have r10430 := hand1 (x 11 1) (x 11 12)
    have r10431 := hand1 (x 10 2) (x 10 13)
    have b10432 := hb (x (-13) 7)
    have b10433 := hb (x (-12) 6)
    have b10434 := hb (x (-11) 5)
    have b10435 := hb (x (-10) 4)
    have b10436 := hb (x (-9) 11)
    have b10437 := hb (x (-8) 10)
    have b10438 := hb (x (-8) 14)
    have b10439 := hb (x (-7) 7)
    have b10440 := hb (x (-7) 9)
    have b10441 := hb (x (-7) 13)
    have b10442 := hb (x (-6) 6)
    have b10443 := hb (x (-6) 8)
    have b10444 := hb (x (-6) 12)
    have b10445 := hb (x (-5) 5)
    have b10446 := hb (x (-5) 11)
    have b10447 := hb (x (-4) 4)
    have b10448 := hb (x (-4) 10)
    have b10449 := hb (x (-4) 14)
    have b10450 := hb (x (-3) 3)
    have b10451 := hb (x (-3) 5)
    have b10452 := hb (x (-3) 9)
    have b10453 := hb (x (-3) 11)
    have b10454 := hb (x (-3) 13)
    have b10455 := hb (x (-3) 14)
    have b10456 := hb (x (-2) 2)
    have b10457 := hb (x (-2) 8)
    have b10458 := hb (x (-2) 10)
    have b10459 := hb (x (-2) 12)
    have b10460 := hb (x (-2) 13)
    have b10461 := hb (x (-2) 14)
    have b10462 := hb (x (-1) 7)
    have b10463 := hb (x (-1) 9)
    have b10464 := hb (x (-1) 11)
    have b10465 := hb (x (-1) 12)
    have b10466 := hb (x (-1) 13)
    have b10467 := hb (x 0 6)
    have b10468 := hb (x 0 8)
    have b10469 := hb (x 0 10)
    have b10470 := hb (x 0 11)
    have b10471 := hb (x 0 12)
    have b10472 := hb (x 1 3)
    have b10473 := hb (x 1 5)
    have b10474 := hb (x 1 7)
    have b10475 := hb (x 1 9)
    have b10476 := hb (x 1 10)
    have b10477 := hb (x 1 11)
    have b10478 := hb (x 2 2)
    have b10479 := hb (x 2 4)
    have b10480 := hb (x 2 6)
    have b10481 := hb (x 2 8)
    have b10482 := hb (x 2 9)
    have b10483 := hb (x 2 10)
    have b10484 := hb (x 3 3)
    have b10485 := hb (x 3 5)
    have b10486 := hb (x 3 7)
    have b10487 := hb (x 3 8)
    have b10488 := hb (x 3 9)
    have b10489 := hb (x 3 13)
    have b10490 := hb (x 4 2)
    have b10491 := hb (x 4 4)
    have b10492 := hb (x 4 6)
    have b10493 := hb (x 4 7)
    have b10494 := hb (x 4 8)
    have b10495 := hb (x 4 12)
    have b10496 := hb (x 5 1)
    have b10497 := hb (x 5 5)
    have b10498 := hb (x 5 6)
    have b10499 := hb (x 5 7)
    have b10500 := hb (x 5 11)
    have b10501 := hb (x 6 4)
    have b10502 := hb (x 6 5)
    have b10503 := hb (x 6 6)
    have b10504 := hb (x 6 10)
    have b10505 := hb (x 7 3)
    have b10506 := hb (x 7 4)
    have b10507 := hb (x 7 5)
    have b10508 := hb (x 7 9)
    have b10509 := hb (x 8 2)
    have b10510 := hb (x 8 3)
    have b10511 := hb (x 8 4)
    have b10512 := hb (x 8 7)
    have b10513 := hb (x 8 8)
    have b10514 := hb (x 8 11)
    have b10515 := hb (x 9 1)
    have b10516 := hb (x 9 2)
    have b10517 := hb (x 9 3)
    have b10518 := hb (x 9 6)
    have b10519 := hb (x 10 1)
    have b10520 := hb (x 10 2)
    have b10521 := hb (x 10 5)
    have b10522 := hb (x 10 10)
    have b10523 := hb (x 11 1)
    have b10524 := hb (x 11 4)
    have b10525 := hb (x 12 11)
    have b10526 := hb (x 13 10)
    have b10527 := hb (x 14 9)
    have b10528 := hb (x 15 8)
    have b10529 := hb (x 0 2 && x 0 6)
    have b10530 := hb (x (-1) 3 && x (-1) 7)
    have b10531 := hb (x (-2) 4 && x (-2) 8)
    have b10532 := hb (x (-3) 5 && x (-3) 9)
    have b10533 := hb (x (-4) 6 && x (-4) 10)
    have b10534 := hb (x (-5) 7 && x (-5) 11)
    have b10535 := hb (x (-6) 8 && x (-6) 12)
    have b10536 := hb (x (-7) 9 && x (-7) 13)
    have b10537 := hb (x 4 2 && x 4 6)
    have b10538 := hb (x 3 3 && x 3 7)
    have b10539 := hb (x 2 4 && x 2 8)
    have b10540 := hb (x 1 5 && x 1 9)
    have b10541 := hb (x 0 6 && x 0 10)
    have b10542 := hb (x (-1) 7 && x (-1) 11)
    have b10543 := hb (x (-2) 8 && x (-2) 12)
    have b10544 := hb (x (-3) 9 && x (-3) 13)
    have b10545 := hb (x 9 2 && x 9 6)
    have b10546 := hb (x 8 3 && x 8 7)
    have b10547 := hb (x 7 4 && x 7 8)
    have b10548 := hb (x 6 5 && x 6 9)
    have b10549 := hb (x 5 6 && x 5 10)
    have b10550 := hb (x 4 7 && x 4 11)
    have b10551 := hb (x 3 8 && x 3 12)
    have b10552 := hb (x 2 9 && x 2 13)
    have b10553 := hb (x 5 1 && x 5 6)
    have b10554 := hb (x 4 2 && x 4 7)
    have b10555 := hb (x 3 3 && x 3 8)
    have b10556 := hb (x 2 4 && x 2 9)
    have b10557 := hb (x 1 5 && x 1 10)
    have b10558 := hb (x 0 6 && x 0 11)
    have b10559 := hb (x (-1) 7 && x (-1) 12)
    have b10560 := hb (x (-2) 8 && x (-2) 13)
    have b10561 := hb (x (-3) 9 && x (-3) 14)
    have b10562 := hb (x 1 1 && x 1 7)
    have b10563 := hb (x 0 2 && x 0 8)
    have b10564 := hb (x (-1) 3 && x (-1) 9)
    have b10565 := hb (x (-2) 4 && x (-2) 10)
    have b10566 := hb (x (-3) 5 && x (-3) 11)
    have b10567 := hb (x (-4) 6 && x (-4) 12)
    have b10568 := hb (x (-5) 7 && x (-5) 13)
    have b10569 := hb (x (-6) 8 && x (-6) 14)
    have b10570 := hb (x 5 1 && x 5 7)
    have b10571 := hb (x 4 2 && x 4 8)
    have b10572 := hb (x 3 3 && x 3 9)
    have b10573 := hb (x 2 4 && x 2 10)
    have b10574 := hb (x 1 5 && x 1 11)
    have b10575 := hb (x 0 6 && x 0 12)
    have b10576 := hb (x (-1) 7 && x (-1) 13)
    have b10577 := hb (x (-2) 8 && x (-2) 14)
    have b10578 := hb (x 1 1 && x 1 11)
    have b10579 := hb (x 0 2 && x 0 12)
    have b10580 := hb (x (-1) 3 && x (-1) 13)
    have b10581 := hb (x (-2) 4 && x (-2) 14)
    have b10582 := hb (x 5 1 && x 5 11)
    have b10583 := hb (x 4 2 && x 4 12)
    have b10584 := hb (x 3 3 && x 3 13)
    have b10585 := hb (x 2 4 && x 2 14)
    have b10586 := hb (x 9 1 && x 9 11)
    have b10587 := hb (x 8 2 && x 8 12)
    have b10588 := hb (x 7 3 && x 7 13)
    have b10589 := hb (x 6 4 && x 6 14)
    have b10590 := hb (x (-1) 1 && x (-1) 12)
    have b10591 := hb (x (-2) 2 && x (-2) 13)
    have b10592 := hb (x (-3) 3 && x (-3) 14)
    have b10593 := hb (x 7 1 && x 7 12)
    have b10594 := hb (x 6 2 && x 6 13)
    have b10595 := hb (x 5 3 && x 5 14)
    have b10596 := hb (x 11 1 && x 11 12)
    have b10597 := hb (x 10 2 && x 10 13)
    have b10598 := hb (x 9 3 && x 9 14)
    linarith only [r10356, r10357, r10358, r10359, r10360, e10361, e10362, e10363, e10364, e10365, e10366, r10367, e10368, e10369, e10370, e10371, e10372, e10373, r10374, e10375, e10376, e10377, e10378, e10379, e10380, r10381, e10382, e10383, e10384, e10385, e10386, e10387, r10388, e10389, e10390, r10391, e10392, e10393, r10394, e10395, e10396, r10397, e10398, e10399, r10400, e10401, e10402, r10403, r10404, r10405, r10406, r10407, r10408, r10409, r10410, r10411, r10412, r10413, r10414, r10415, r10416, r10417, r10418, r10419, r10420, r10421, r10422, r10423, r10424, r10425, r10426, r10427, r10428, r10429, r10430, r10431, b10432, b10433, b10434, b10435, b10436, b10437, b10438, b10439, b10440, b10441, b10442, b10443, b10444, b10445, b10446, b10447, b10448, b10449, b10450, b10451, b10452, b10453, b10454, b10455, b10456, b10457, b10458, b10459, b10460, b10461, b10462, b10463, b10464, b10465, b10466, b10467, b10468, b10469, b10470, b10471, b10472, b10473, b10474, b10475, b10476, b10477, b10478, b10479, b10480, b10481, b10482, b10483, b10484, b10485, b10486, b10487, b10488, b10489, b10490, b10491, b10492, b10493, b10494, b10495, b10496, b10497, b10498, b10499, b10500, b10501, b10502, b10503, b10504, b10505, b10506, b10507, b10508, b10509, b10510, b10511, b10512, b10513, b10514, b10515, b10516, b10517, b10518, b10519, b10520, b10521, b10522, b10523, b10524, b10525, b10526, b10527, b10528, b10529, b10530, b10531, b10532, b10533, b10534, b10535, b10536, b10537, b10538, b10539, b10540, b10541, b10542, b10543, b10544, b10545, b10546, b10547, b10548, b10549, b10550, b10551, b10552, b10553, b10554, b10555, b10556, b10557, b10558, b10559, b10560, b10561, b10562, b10563, b10564, b10565, b10566, b10567, b10568, b10569, b10570, b10571, b10572, b10573, b10574, b10575, b10576, b10577, b10578, b10579, b10580, b10581, b10582, b10583, b10584, b10585, b10586, b10587, b10588, b10589, b10590, b10591, b10592, b10593, b10594, b10595, b10596, b10597, b10598, d10026, d10002, d9994, d9986, d9942, d9926, d9890, d9850, d9870, d9882, d9854, d9862, d9818, d9810, d10336, d9802, d9770, d9782, d10308, g0, g1, d9706, d9422, d9438, d9722, d9714, d10086, d10106, d10186, d9686, d9482, d10195, d9490, d9474, d10228, d9514, d9538, d9654, d9674, d10240, d10276, d9646, d10256, d9578, d9582, d9602, d9626, d9634, d9618, d9614, d10332, d9766, d10154, d9878, d10182, d9930, d9990, d9694, d10102, d9434, d10328, d9774, d9866, d9622, d10260, d10280, d9658, d10054, d10070, d9530, d9690, d10098, d9430, d9366, d10352, d9838, d9410, d9762, d10150, d9858, d10178, d9938, d9526, d9494, d10094, d9426, d10324, d9786, d9398, d9750, d10138, d9522, d9478, d10090, d9606, d9570, d10244, d9730, d9822, d9562, d10272, d9510, d9598]
  · have f10599 : (x 0 4).toNat = 1 := by rw [h10211]; rfl
    have d10600 : (x 0 12).toNat = 1 := by
      have r10601 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
      have b10602 := hb (x 0 4)
      have b10603 := hb (x 0 12)
      clear * - r10601 b10602 b10603 f10599
      omega
    have d10604 : (x (-2) 2).toNat = 0 := by
      have r10605 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10606 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e10607 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have b10608 := hb (x (-3) 3)
      have b10609 := hb (x (-2) 2)
      have b10610 := hb (x (-1) 13)
      have b10611 := hb (x 0 12)
      clear * - r10605 e10606 e10607 b10608 b10609 b10610 b10611 d10600 d9782 d9850
      omega
    have d10612 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
      have r10613 := hand1 (x (-2) 2) (x (-2) 13)
      have b10614 := hb (x (-2) 2)
      have b10615 := hb (x (-2) 2 && x (-2) 13)
      clear * - r10613 b10614 b10615 d10604
      omega
    have d10616 : (x (-2) 3).toNat = 0 := by
      have r10617 : (x (-2) 2).toNat = (x (-2) 3).toNat := congrArg Bool.toNat (h23 (-2))
      have b10618 := hb (x (-2) 2)
      have b10619 := hb (x (-2) 3)
      clear * - r10617 b10618 b10619 d10604
      omega
    have d10620 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
      have r10621 := hand1 (x (-2) 3) (x (-2) 13)
      have b10622 := hb (x (-2) 3)
      have b10623 := hb (x (-2) 3 && x (-2) 13)
      clear * - r10621 b10622 b10623 d10616
      omega
    have d10624 : (x (-2) 11).toNat = 0 := by
      have r10625 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
      have b10626 := hb (x (-2) 3)
      have b10627 := hb (x (-2) 11)
      clear * - r10625 b10626 b10627 d10616
      omega
    have d10628 : (x (-2) 10).toNat = 0 := by
      have r10629 : (x (-2) 10).toNat ≤ (x (-2) 2).toNat := himp _ _ (hp10 (-2))
      have b10630 := hb (x (-2) 2)
      have b10631 := hb (x (-2) 10)
      clear * - r10629 b10630 b10631 d10604
      omega
    have d10632 : (x (-4) 4).toNat = 1 := by
      have r10633 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b10634 := hb (x (-4) 4)
      have b10635 := hb (x 0 11)
      have b10636 := hb (x (-1) 1 && x (-1) 12)
      have b10637 := hb (x (-2) 2 && x (-2) 13)
      have b10638 := hb (x (-3) 3 && x (-3) 14)
      clear * - r10633 b10634 b10635 b10636 b10637 b10638 g1 d9730 d10612 d9822
      omega
    have d10639 : (x (-4) 12).toNat = 1 := by
      have r10640 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
      have b10641 := hb (x (-4) 4)
      have b10642 := hb (x (-4) 12)
      clear * - r10640 b10641 b10642 d10632
      omega
    have d10643 : (x (-6) 2).toNat = 0 := by
      have r10644 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10645 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e10646 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have b10647 := hb (x (-7) 3)
      have b10648 := hb (x (-6) 2)
      have b10649 := hb (x (-5) 13)
      have b10650 := hb (x (-4) 12)
      clear * - r10644 e10645 e10646 b10647 b10648 b10649 b10650 d10639 d9934 d9974
      omega
    have d10651 : (x (-6) 2 && x (-6) 12).toNat = 0 := by
      have r10652 := hand1 (x (-6) 2) (x (-6) 12)
      have b10653 := hb (x (-6) 2)
      have b10654 := hb (x (-6) 2 && x (-6) 12)
      clear * - r10652 b10653 b10654 d10643
      omega
    have d10655 : (x (-6) 3).toNat = 0 := by
      have r10656 : (x (-6) 2).toNat = (x (-6) 3).toNat := congrArg Bool.toNat (h23 (-6))
      have b10657 := hb (x (-6) 2)
      have b10658 := hb (x (-6) 3)
      clear * - r10656 b10657 b10658 d10643
      omega
    have d10659 : (x (-6) 10).toNat = 0 := by
      have r10660 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
      have b10661 := hb (x (-6) 2)
      have b10662 := hb (x (-6) 10)
      clear * - r10660 b10661 b10662 d10643
      omega
    have d10663 : (x (-4) 13).toNat = 1 := by
      have r10664 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b10665 := hb (x (-6) 2)
      have b10666 := hb (x (-4) 13)
      have b10667 := hb (x (-5) 1 && x (-5) 14)
      clear * - r10664 b10665 b10666 b10667 d9898 d10643
      omega
    have d10668 : (x (-3) 12).toNat = 0 := by
      have r10669 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10670 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e10671 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b10672 := hb (x (-6) 3)
      have b10673 := hb (x (-5) 2)
      have b10674 := hb (x (-4) 13)
      have b10675 := hb (x (-3) 12)
      clear * - r10669 e10670 e10671 b10672 b10673 b10674 b10675 d10663 d9918 d10655
      omega
    have d10676 : (x (-3) 4).toNat = 0 := by
      have r10677 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
      have b10678 := hb (x (-3) 4)
      have b10679 := hb (x (-3) 12)
      clear * - r10677 b10678 b10679 d10668
      omega
    have d10680 : (x (-4) 5).toNat = 1 := by
      have r10681 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b10682 := hb (x (-4) 5)
      have b10683 := hb (x 1 10)
      have b10684 := hb (x 0 1 && x 0 11)
      have b10685 := hb (x (-1) 2 && x (-1) 12)
      have b10686 := hb (x (-2) 3 && x (-2) 13)
      have b10687 := hb (x (-3) 4 && x (-3) 14)
      clear * - r10681 b10682 b10683 b10684 b10685 b10686 b10687 d9722 d9354 d9742 d10620 d9826
      omega
    have d10688 : (x 4 8).toNat = 0 := by
      have r10689 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10690 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
      have e10691 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
      have e10692 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
      have e10693 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
      have e10694 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
      have e10695 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
      have b10696 := hb (x (-3) 7)
      have b10697 := hb (x (-2) 6)
      have b10698 := hb (x (-1) 5)
      have b10699 := hb (x 0 4)
      have b10700 := hb (x 1 11)
      have b10701 := hb (x 2 10)
      have b10702 := hb (x 3 9)
      have b10703 := hb (x 4 8)
      clear * - r10689 e10690 e10691 e10692 e10693 e10694 e10695 b10696 b10697 b10698 b10699 b10700 b10701 b10702 b10703 d9490 d9714 f10599 d9794
      omega
    have d10704 : (x 4 4 && x 4 8).toNat = 0 := by
      have r10705 := hand2 (x 4 4) (x 4 8)
      have b10706 := hb (x 4 8)
      have b10707 := hb (x 4 4 && x 4 8)
      clear * - r10705 b10706 b10707 d10688
      omega
    have d10708 : (x 2 10).toNat = 0 := by
      have r10709 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10710 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
      have e10711 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
      have e10712 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
      have e10713 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
      have e10714 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
      have e10715 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
      have b10716 := hb (x (-3) 7)
      have b10717 := hb (x (-2) 6)
      have b10718 := hb (x (-1) 5)
      have b10719 := hb (x 0 4)
      have b10720 := hb (x 1 11)
      have b10721 := hb (x 2 10)
      have b10722 := hb (x 3 9)
      have b10723 := hb (x 4 8)
      clear * - r10709 e10710 e10711 e10712 e10713 e10714 e10715 b10716 b10717 b10718 b10719 b10720 b10721 b10722 b10723 d10688 d9490 d9714 f10599 d9794
      omega
    have d10724 : (x 2 6 && x 2 10).toNat = 0 := by
      have r10725 := hand2 (x 2 6) (x 2 10)
      have b10726 := hb (x 2 10)
      have b10727 := hb (x 2 6 && x 2 10)
      clear * - r10725 b10726 b10727 d10708
      omega
    have d10728 : (x (-2) 6).toNat = 0 := by
      have r10729 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10730 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
      have e10731 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
      have e10732 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
      have e10733 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
      have e10734 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
      have e10735 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
      have b10736 := hb (x (-3) 7)
      have b10737 := hb (x (-2) 6)
      have b10738 := hb (x (-1) 5)
      have b10739 := hb (x 0 4)
      have b10740 := hb (x 1 11)
      have b10741 := hb (x 2 10)
      have b10742 := hb (x 3 9)
      have b10743 := hb (x 4 8)
      clear * - r10729 e10730 e10731 e10732 e10733 e10734 e10735 b10736 b10737 b10738 b10739 b10740 b10741 b10742 b10743 d10688 d9490 d10708 d9714 f10599 d9794
      omega
    have d10744 : (x (-2) 6 && x (-2) 13).toNat = 0 := by
      have r10745 := hand1 (x (-2) 6) (x (-2) 13)
      have b10746 := hb (x (-2) 6)
      have b10747 := hb (x (-2) 6 && x (-2) 13)
      clear * - r10745 b10746 b10747 d10728
      omega
    have d10748 : (x (-3) 7).toNat = 0 := by
      have r10749 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10750 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
      have e10751 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
      have e10752 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
      have e10753 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
      have e10754 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
      have e10755 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
      have b10756 := hb (x (-3) 7)
      have b10757 := hb (x (-2) 6)
      have b10758 := hb (x (-1) 5)
      have b10759 := hb (x 0 4)
      have b10760 := hb (x 1 11)
      have b10761 := hb (x 2 10)
      have b10762 := hb (x 3 9)
      have b10763 := hb (x 4 8)
      clear * - r10749 e10750 e10751 e10752 e10753 e10754 e10755 b10756 b10757 b10758 b10759 b10760 b10761 b10762 b10763 d10688 d9490 d10708 d9714 f10599 d9794 d10728
      omega
    have d10764 : (x 1 8).toNat = 0 := by
      have r10765 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10766 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e10767 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e10768 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e10769 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e10770 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e10771 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b10772 := hb (x (-6) 7)
      have b10773 := hb (x (-5) 6)
      have b10774 := hb (x (-4) 5)
      have b10775 := hb (x (-3) 4)
      have b10776 := hb (x (-2) 11)
      have b10777 := hb (x (-1) 10)
      have b10778 := hb (x 0 9)
      have b10779 := hb (x 1 8)
      clear * - r10765 e10766 e10767 e10768 e10769 e10770 e10771 b10772 b10773 b10774 b10775 b10776 b10777 b10778 b10779 d9778 d10624 d10676 d10680 d9914
      omega
    have d10780 : (x 0 9).toNat = 0 := by
      have r10781 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10782 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e10783 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e10784 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e10785 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e10786 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e10787 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b10788 := hb (x (-6) 7)
      have b10789 := hb (x (-5) 6)
      have b10790 := hb (x (-4) 5)
      have b10791 := hb (x (-3) 4)
      have b10792 := hb (x (-2) 11)
      have b10793 := hb (x (-1) 10)
      have b10794 := hb (x 0 9)
      have b10795 := hb (x 1 8)
      clear * - r10781 e10782 e10783 e10784 e10785 e10786 e10787 b10788 b10789 b10790 b10791 b10792 b10793 b10794 b10795 d10764 d9778 d10624 d10676 d10680 d9914
      omega
    have d10796 : (x 0 2 && x 0 9).toNat = 0 := by
      have r10797 := hand2 (x 0 2) (x 0 9)
      have b10798 := hb (x 0 9)
      have b10799 := hb (x 0 2 && x 0 9)
      clear * - r10797 b10798 b10799 d10780
      omega
    have d10800 : (x 0 8).toNat = 0 := by
      have r10801 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10802 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
      have e10803 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
      have e10804 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
      have e10805 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
      have e10806 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
      have e10807 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
      have b10808 := hb (x (-7) 7)
      have b10809 := hb (x (-6) 6)
      have b10810 := hb (x (-5) 5)
      have b10811 := hb (x (-4) 4)
      have b10812 := hb (x (-3) 11)
      have b10813 := hb (x (-2) 10)
      have b10814 := hb (x (-1) 9)
      have b10815 := hb (x 0 8)
      clear * - r10801 e10802 e10803 e10804 e10805 e10806 e10807 b10808 b10809 b10810 b10811 b10812 b10813 b10814 b10815 d9802 d10628 d9854 d10632 d9942
      omega
    have d10816 : (x 0 8 && x 0 12).toNat = 0 := by
      have r10817 := hand1 (x 0 8) (x 0 12)
      have b10818 := hb (x 0 8)
      have b10819 := hb (x 0 8 && x 0 12)
      clear * - r10817 b10818 b10819 d10800
      omega
    have r10820 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r10821 : (x 5 1).toNat + (x 4 2).toNat + (x 3 3).toNat + (x 2 4).toNat + (x 1 5).toNat + (x 0 6).toNat + (x (-1) 7).toNat + (x (-2) 8).toNat + (x (-3) 9).toNat + (x (-4) 10).toNat + (x (-5) 11).toNat + (x (-6) 12).toNat + (x (-7) 13).toNat + (x (-8) 14).toNat = 3 := by have q := hcount 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r10822 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r10823 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10824 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
    have e10825 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
    have e10826 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
    have e10827 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
    have e10828 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
    have e10829 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
    have r10830 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10831 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
    have e10832 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
    have e10833 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
    have e10834 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
    have e10835 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
    have e10836 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
    have r10837 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10838 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
    have e10839 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
    have e10840 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
    have e10841 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
    have e10842 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
    have e10843 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
    have r10844 : 1 ≤ (x 2 4).toNat + (x 1 1 && x 1 5).toNat + (x 0 2 && x 0 6).toNat + (x (-1) 3 && x (-1) 7).toNat + (x (-2) 4 && x (-2) 8).toNat + (x (-3) 5 && x (-3) 9).toNat + (x (-4) 6 && x (-4) 10).toNat + (x (-5) 7 && x (-5) 11).toNat + (x (-6) 8 && x (-6) 12).toNat + (x (-7) 9 && x (-7) 13).toNat + (x (-8) 10 && x (-8) 14).toNat + (x (-9) 11).toNat := by have q := hcov4 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10845 : (x 1 1 && x 1 5).toNat = (x 1 5).toNat := handr _ _ (fun h => hp13 1 (hp5 1 (h)))
    have e10846 : (x (-8) 10 && x (-8) 14).toNat = (x (-8) 10).toNat := handl _ _ (fun h => hp2 (-8) (hp10 (-8) (h)))
    have r10847 : 1 ≤ (x 8 4).toNat + (x 7 1 && x 7 5).toNat + (x 6 2 && x 6 6).toNat + (x 5 3 && x 5 7).toNat + (x 4 4 && x 4 8).toNat + (x 3 5 && x 3 9).toNat + (x 2 6 && x 2 10).toNat + (x 1 7 && x 1 11).toNat + (x 0 8 && x 0 12).toNat + (x (-1) 9 && x (-1) 13).toNat + (x (-2) 10 && x (-2) 14).toNat + (x (-3) 11).toNat := by have q := hcov4 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10848 : (x 7 1 && x 7 5).toNat = (x 7 5).toNat := handr _ _ (fun h => hp13 7 (hp5 7 (h)))
    have e10849 : (x (-2) 10 && x (-2) 14).toNat = (x (-2) 10).toNat := handl _ _ (fun h => hp2 (-2) (hp10 (-2) (h)))
    have r10850 : 1 ≤ (x 2 7).toNat + (x 1 1 && x 1 8).toNat + (x 0 2 && x 0 9).toNat + (x (-1) 3 && x (-1) 10).toNat + (x (-2) 4 && x (-2) 11).toNat + (x (-3) 5 && x (-3) 12).toNat + (x (-4) 6 && x (-4) 13).toNat + (x (-5) 7 && x (-5) 14).toNat + (x (-6) 8).toNat := by have q := hcov7 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r10851 : 1 ≤ (x 4 7).toNat + (x 3 1 && x 3 8).toNat + (x 2 2 && x 2 9).toNat + (x 1 3 && x 1 10).toNat + (x 0 4 && x 0 11).toNat + (x (-1) 5 && x (-1) 12).toNat + (x (-2) 6 && x (-2) 13).toNat + (x (-3) 7 && x (-3) 14).toNat + (x (-4) 8).toNat := by have q := hcov7 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r10852 : 1 ≤ (x 11 9).toNat + (x 10 1 && x 10 10).toNat + (x 9 2 && x 9 11).toNat + (x 8 3 && x 8 12).toNat + (x 7 4 && x 7 13).toNat + (x 6 5 && x 6 14).toNat + (x 5 6).toNat := by have q := hcov9 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r10853 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r10854 : 1 ≤ (x (-4) 10).toNat + (x (-5) 1 && x (-5) 11).toNat + (x (-6) 2 && x (-6) 12).toNat + (x (-7) 3 && x (-7) 13).toNat + (x (-8) 4 && x (-8) 14).toNat + (x (-9) 5).toNat := by have q := hcov10 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r10855 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := by have q := hcov11 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r10856 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
    have r10857 := hand2 (x 0 2) (x 0 6)
    have r10858 := hand2 (x (-6) 8) (x (-6) 12)
    have r10859 := hand2 (x 6 2) (x 6 6)
    have r10860 := hand1 (x 2 2) (x 2 9)
    have r10861 := hand2 (x 10 1) (x 10 10)
    have r10862 := hand1 (x 8 3) (x 8 12)
    have r10863 := hand1 (x 6 5) (x 6 14)
    have r10864 := hand2 (x (-8) 2) (x (-8) 12)
    have r10865 := hand1 (x (-10) 4) (x (-10) 14)
    have r10866 := hand1 (x (-8) 4) (x (-8) 14)
    have r10867 := hand1 (x 4 2) (x 4 13)
    have b10868 := hb (x (-13) 7)
    have b10869 := hb (x (-12) 6)
    have b10870 := hb (x (-11) 5)
    have b10871 := hb (x (-10) 4)
    have b10872 := hb (x (-10) 14)
    have b10873 := hb (x (-9) 5)
    have b10874 := hb (x (-9) 11)
    have b10875 := hb (x (-9) 13)
    have b10876 := hb (x (-8) 4)
    have b10877 := hb (x (-8) 10)
    have b10878 := hb (x (-8) 12)
    have b10879 := hb (x (-8) 14)
    have b10880 := hb (x (-7) 9)
    have b10881 := hb (x (-7) 11)
    have b10882 := hb (x (-7) 13)
    have b10883 := hb (x (-6) 8)
    have b10884 := hb (x (-6) 10)
    have b10885 := hb (x (-6) 12)
    have b10886 := hb (x (-5) 9)
    have b10887 := hb (x (-5) 11)
    have b10888 := hb (x (-4) 8)
    have b10889 := hb (x (-4) 10)
    have b10890 := hb (x (-3) 7)
    have b10891 := hb (x (-3) 9)
    have b10892 := hb (x (-3) 11)
    have b10893 := hb (x (-3) 14)
    have b10894 := hb (x (-2) 6)
    have b10895 := hb (x (-2) 8)
    have b10896 := hb (x (-2) 10)
    have b10897 := hb (x (-2) 13)
    have b10898 := hb (x (-1) 5)
    have b10899 := hb (x (-1) 7)
    have b10900 := hb (x (-1) 12)
    have b10901 := hb (x 0 4)
    have b10902 := hb (x 0 6)
    have b10903 := hb (x 0 11)
    have b10904 := hb (x 1 3)
    have b10905 := hb (x 1 5)
    have b10906 := hb (x 1 10)
    have b10907 := hb (x 2 2)
    have b10908 := hb (x 2 4)
    have b10909 := hb (x 2 7)
    have b10910 := hb (x 2 9)
    have b10911 := hb (x 3 1)
    have b10912 := hb (x 3 3)
    have b10913 := hb (x 3 6)
    have b10914 := hb (x 3 8)
    have b10915 := hb (x 4 2)
    have b10916 := hb (x 4 5)
    have b10917 := hb (x 4 7)
    have b10918 := hb (x 5 1)
    have b10919 := hb (x 5 4)
    have b10920 := hb (x 5 6)
    have b10921 := hb (x 5 7)
    have b10922 := hb (x 6 5)
    have b10923 := hb (x 6 6)
    have b10924 := hb (x 6 11)
    have b10925 := hb (x 7 4)
    have b10926 := hb (x 7 5)
    have b10927 := hb (x 7 10)
    have b10928 := hb (x 8 3)
    have b10929 := hb (x 8 4)
    have b10930 := hb (x 8 9)
    have b10931 := hb (x 9 2)
    have b10932 := hb (x 9 8)
    have b10933 := hb (x 9 11)
    have b10934 := hb (x 10 1)
    have b10935 := hb (x 10 10)
    have b10936 := hb (x 11 9)
    have b10937 := hb (x 12 8)
    have b10938 := hb (x 0 2 && x 0 6)
    have b10939 := hb (x (-1) 3 && x (-1) 7)
    have b10940 := hb (x (-2) 4 && x (-2) 8)
    have b10941 := hb (x (-3) 5 && x (-3) 9)
    have b10942 := hb (x (-4) 6 && x (-4) 10)
    have b10943 := hb (x (-5) 7 && x (-5) 11)
    have b10944 := hb (x (-6) 8 && x (-6) 12)
    have b10945 := hb (x (-7) 9 && x (-7) 13)
    have b10946 := hb (x 6 2 && x 6 6)
    have b10947 := hb (x 5 3 && x 5 7)
    have b10948 := hb (x 4 4 && x 4 8)
    have b10949 := hb (x 3 5 && x 3 9)
    have b10950 := hb (x 2 6 && x 2 10)
    have b10951 := hb (x 1 7 && x 1 11)
    have b10952 := hb (x 0 8 && x 0 12)
    have b10953 := hb (x (-1) 9 && x (-1) 13)
    have b10954 := hb (x 1 1 && x 1 8)
    have b10955 := hb (x 0 2 && x 0 9)
    have b10956 := hb (x (-1) 3 && x (-1) 10)
    have b10957 := hb (x (-2) 4 && x (-2) 11)
    have b10958 := hb (x (-3) 5 && x (-3) 12)
    have b10959 := hb (x (-4) 6 && x (-4) 13)
    have b10960 := hb (x (-5) 7 && x (-5) 14)
    have b10961 := hb (x 3 1 && x 3 8)
    have b10962 := hb (x 2 2 && x 2 9)
    have b10963 := hb (x 1 3 && x 1 10)
    have b10964 := hb (x 0 4 && x 0 11)
    have b10965 := hb (x (-1) 5 && x (-1) 12)
    have b10966 := hb (x (-2) 6 && x (-2) 13)
    have b10967 := hb (x (-3) 7 && x (-3) 14)
    have b10968 := hb (x 10 1 && x 10 10)
    have b10969 := hb (x 9 2 && x 9 11)
    have b10970 := hb (x 8 3 && x 8 12)
    have b10971 := hb (x 7 4 && x 7 13)
    have b10972 := hb (x 6 5 && x 6 14)
    have b10973 := hb (x (-7) 1 && x (-7) 11)
    have b10974 := hb (x (-8) 2 && x (-8) 12)
    have b10975 := hb (x (-9) 3 && x (-9) 13)
    have b10976 := hb (x (-10) 4 && x (-10) 14)
    have b10977 := hb (x (-5) 1 && x (-5) 11)
    have b10978 := hb (x (-6) 2 && x (-6) 12)
    have b10979 := hb (x (-7) 3 && x (-7) 13)
    have b10980 := hb (x (-8) 4 && x (-8) 14)
    have b10981 := hb (x 5 1 && x 5 12)
    have b10982 := hb (x 4 2 && x 4 13)
    have b10983 := hb (x 3 3 && x 3 14)
    linarith only [r10820, r10821, r10822, r10823, e10824, e10825, e10826, e10827, e10828, e10829, r10830, e10831, e10832, e10833, e10834, e10835, e10836, r10837, e10838, e10839, e10840, e10841, e10842, e10843, r10844, e10845, e10846, r10847, e10848, e10849, r10850, r10851, r10852, r10853, r10854, r10855, r10856, r10857, r10858, r10859, r10860, r10861, r10862, r10863, r10864, r10865, r10866, r10867, b10868, b10869, b10870, b10871, b10872, b10873, b10874, b10875, b10876, b10877, b10878, b10879, b10880, b10881, b10882, b10883, b10884, b10885, b10886, b10887, b10888, b10889, b10890, b10891, b10892, b10893, b10894, b10895, b10896, b10897, b10898, b10899, b10900, b10901, b10902, b10903, b10904, b10905, b10906, b10907, b10908, b10909, b10910, b10911, b10912, b10913, b10914, b10915, b10916, b10917, b10918, b10919, b10920, b10921, b10922, b10923, b10924, b10925, b10926, b10927, b10928, b10929, b10930, b10931, b10932, b10933, b10934, b10935, b10936, b10937, b10938, b10939, b10940, b10941, b10942, b10943, b10944, b10945, b10946, b10947, b10948, b10949, b10950, b10951, b10952, b10953, b10954, b10955, b10956, b10957, b10958, b10959, b10960, b10961, b10962, b10963, b10964, b10965, b10966, b10967, b10968, b10969, b10970, b10971, b10972, b10973, b10974, b10975, b10976, b10977, b10978, b10979, b10980, b10981, b10982, b10983, d10042, d10034, d10026, d10030, d10002, d9994, d9982, d9986, d10659, d9946, d9926, d10748, d9882, d9854, d9818, d10728, d10628, d9794, f10599, g1, d9706, d9422, d9722, d10086, d10186, d9458, d9686, d9678, d10195, d9514, d9654, d9578, d9650, d9626, d9638, d9614, d9766, d10154, d9878, d10182, d9930, d9990, d9670, d10704, d9486, d10724, d9718, d10816, d9790, d9406, d10796, d9758, d10146, d9874, d10174, d9910, d9470, d9710, d9362, d9798, d10744, d9834, d9630, d9574, d9962, d10022, d9902, d10651, d9978, d9518, d9454]

theorem cycle_power_fifteen_tight_type_sequence_shape_rules_core_v101_110 (x : ℤ → Fin 16 → Bool)
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
    (h114 : ∀ p, x p 1 = x p 14)
    (h23 : ∀ p, x p 2 = x p 3)
    (g0 : (x 0 10).toNat = 1) (g1 : (x 0 11).toNat = 0) : False := cycle_power_fifteen_tight_type_sequence_shape_rules_core_v101_110_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 h114 h23 g0 g1
