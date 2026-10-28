import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b01

Topic: combinatorics   Node: cc2cee5a5b74

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core: under the layer-free tight-cover constraints for k = 15 and 12 fixed bits of the class-type sequence near position 0, the constraints are contradictory. Its module also proves the sibling branches cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b00001, cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b0001, cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b001.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b00001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-5) 6).toNat = 0)
    (g1 : (x (-4) 5).toNat = 0)
    (g2 : (x (-3) 4).toNat = 0)
    (g3 : (x (-2) 11).toNat = 0)
    (g4 : (x (-1) 10).toNat = 0)
    (g5 : (x 0 2).toNat = 0)
    (g6 : (x 0 5).toNat = 0)
    (g7 : (x 0 6).toNat = 1)
    (g8 : (x 0 8).toNat = 0)
    (g9 : (x 0 9).toNat = 1)
    (g10 : (x 0 10).toNat = 0)
    (g11 : (x 1 2).toNat = 0)
    (g12 : (x 1 6).toNat = 0)
    (g13 : (x 1 8).toNat = 0)
    (g14 : (x 1 10).toNat = 0)
    (g15 : (x 1 14).toNat = 0)
    (g16 : (x 2 13).toNat = 1)
    (g17 : (x 3 2).toNat = 0)
    (g18 : (x 3 4).toNat = 0)
    (g19 : (x 3 6).toNat = 0)
    (g20 : (x 3 12).toNat = 0)
    (g21 : (x 0 6 && x 0 10).toNat = 0)
    (g22 : (x 3 6 && x 3 10).toNat = 0)
    (g23 : (x 1 8 && x 1 12).toNat = 0)
    (g24 : (x 0 8 && x 0 14).toNat = 0)
    (g25 : (x 3 5 && x 3 12).toNat = 0)
    (g26 : (x 1 7 && x 1 14).toNat = 0)
    (g27 : (x 0 1 && x 0 10).toNat = 0)
    (g28 : (x (-3) 4 && x (-3) 13).toNat = 0)
    (g29 : (x (-4) 5 && x (-4) 14).toNat = 0)
    (g30 : (x 3 2 && x 3 11).toNat = 0)
    (g31 : (x 0 5 && x 0 14).toNat = 0)
    (g32 : (x 0 1 && x 0 11).toNat = 0)
    (g33 : (x (-3) 4 && x (-3) 14).toNat = 0)
    (g34 : (x 0 4 && x 0 14).toNat = 0)
    (g35 : (x 3 2 && x 3 12).toNat = 0)
    (g36 : (x 1 4 && x 1 14).toNat = 0)
    (g37 : (x 3 4 && x 3 14).toNat = 0)
    (g38 : (x 3 3 && x 3 14).toNat = 0)
    (g39 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d3418 : (x 0 14).toNat = 1 := by
    have r3419 : (x 0 6).toNat ≤ (x 0 14).toNat := himp _ _ (hp6 0)
    have b3420 := hb (x 0 6)
    have b3421 := hb (x 0 14)
    clear * - r3419 b3420 b3421 g7
    omega
  have d3422 : (x (-1) 1).toNat = 0 := by
    have r3423 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b3424 := hb (x (-1) 1)
    have b3425 := hb (x 0 14)
    clear * - r3423 b3424 b3425 d3418
    omega
  have d3426 : (x (-1) 1 && x (-1) 14).toNat = 0 := by
    have r3427 := hand1 (x (-1) 1) (x (-1) 14)
    have b3428 := hb (x (-1) 1)
    have b3429 := hb (x (-1) 1 && x (-1) 14)
    clear * - r3427 b3428 b3429 d3422
    omega
  have d3430 : (x (-1) 13).toNat = 0 := by
    have r3431 : (x (-1) 13).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp13 (-1))
    have b3432 := hb (x (-1) 1)
    have b3433 := hb (x (-1) 13)
    clear * - r3431 b3432 b3433 d3422
    omega
  have d3434 : (x (-1) 2 && x (-1) 13).toNat = 0 := by
    have r3435 := hand2 (x (-1) 2) (x (-1) 13)
    have b3436 := hb (x (-1) 13)
    have b3437 := hb (x (-1) 2 && x (-1) 13)
    clear * - r3435 b3436 b3437 d3430
    omega
  have d3438 : (x (-1) 5).toNat = 0 := by
    have r3439 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
    have b3440 := hb (x (-1) 5)
    have b3441 := hb (x (-1) 13)
    clear * - r3439 b3440 b3441 d3430
    omega
  have d3442 : (x (-1) 9).toNat = 0 := by
    have r3443 : (x (-1) 9).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp9 (-1))
    have b3444 := hb (x (-1) 1)
    have b3445 := hb (x (-1) 9)
    clear * - r3443 b3444 b3445 d3422
    omega
  have d3446 : (x 6 8).toNat = 0 := by
    have r3447 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e3448 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e3449 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e3450 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e3451 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e3452 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e3453 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b3454 := hb (x (-1) 7)
    have b3455 := hb (x 0 6)
    have b3456 := hb (x 1 5)
    have b3457 := hb (x 2 4)
    have b3458 := hb (x 3 11)
    have b3459 := hb (x 4 10)
    have b3460 := hb (x 5 9)
    have b3461 := hb (x 6 8)
    clear * - r3447 e3448 e3449 e3450 e3451 e3452 e3453 b3454 b3455 b3456 b3457 b3458 b3459 b3460 b3461 g7
    omega
  have d3462 : (x 6 2 && x 6 8).toNat = 0 := by
    have r3463 := hand2 (x 6 2) (x 6 8)
    have b3464 := hb (x 6 8)
    have b3465 := hb (x 6 2 && x 6 8)
    clear * - r3463 b3464 b3465 d3446
    omega
  have d3466 : (x 6 4 && x 6 8).toNat = 0 := by
    have r3467 := hand2 (x 6 4) (x 6 8)
    have b3468 := hb (x 6 8)
    have b3469 := hb (x 6 4 && x 6 8)
    clear * - r3467 b3468 b3469 d3446
    omega
  have d3470 : (x 5 9).toNat = 0 := by
    have r3471 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e3472 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e3473 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e3474 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e3475 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e3476 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e3477 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b3478 := hb (x (-1) 7)
    have b3479 := hb (x 0 6)
    have b3480 := hb (x 1 5)
    have b3481 := hb (x 2 4)
    have b3482 := hb (x 3 11)
    have b3483 := hb (x 4 10)
    have b3484 := hb (x 5 9)
    have b3485 := hb (x 6 8)
    clear * - r3471 e3472 e3473 e3474 e3475 e3476 e3477 b3478 b3479 b3480 b3481 b3482 b3483 b3484 b3485 d3446 g7
    omega
  have d3486 : (x 5 3 && x 5 9).toNat = 0 := by
    have r3487 := hand2 (x 5 3) (x 5 9)
    have b3488 := hb (x 5 9)
    have b3489 := hb (x 5 3 && x 5 9)
    clear * - r3487 b3488 b3489 d3470
    omega
  have d3490 : (x 5 5 && x 5 9).toNat = 0 := by
    have r3491 := hand2 (x 5 5) (x 5 9)
    have b3492 := hb (x 5 9)
    have b3493 := hb (x 5 5 && x 5 9)
    clear * - r3491 b3492 b3493 d3470
    omega
  have d3494 : (x 4 10).toNat = 0 := by
    have r3495 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e3496 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e3497 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e3498 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e3499 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e3500 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e3501 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b3502 := hb (x (-1) 7)
    have b3503 := hb (x 0 6)
    have b3504 := hb (x 1 5)
    have b3505 := hb (x 2 4)
    have b3506 := hb (x 3 11)
    have b3507 := hb (x 4 10)
    have b3508 := hb (x 5 9)
    have b3509 := hb (x 6 8)
    clear * - r3495 e3496 e3497 e3498 e3499 e3500 e3501 b3502 b3503 b3504 b3505 b3506 b3507 b3508 b3509 d3446 d3470 g7
    omega
  have d3510 : (x 4 1 && x 4 10).toNat = 0 := by
    have r3511 := hand2 (x 4 1) (x 4 10)
    have b3512 := hb (x 4 10)
    have b3513 := hb (x 4 1 && x 4 10)
    clear * - r3511 b3512 b3513 d3494
    omega
  have d3514 : (x 4 4 && x 4 10).toNat = 0 := by
    have r3515 := hand2 (x 4 4) (x 4 10)
    have b3516 := hb (x 4 10)
    have b3517 := hb (x 4 4 && x 4 10)
    clear * - r3515 b3516 b3517 d3494
    omega
  have d3518 : (x 4 6 && x 4 10).toNat = 0 := by
    have r3519 := hand2 (x 4 6) (x 4 10)
    have b3520 := hb (x 4 10)
    have b3521 := hb (x 4 6 && x 4 10)
    clear * - r3519 b3520 b3521 d3494
    omega
  have d3522 : (x 3 11).toNat = 0 := by
    have r3523 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e3524 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e3525 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e3526 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e3527 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e3528 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e3529 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b3530 := hb (x (-1) 7)
    have b3531 := hb (x 0 6)
    have b3532 := hb (x 1 5)
    have b3533 := hb (x 2 4)
    have b3534 := hb (x 3 11)
    have b3535 := hb (x 4 10)
    have b3536 := hb (x 5 9)
    have b3537 := hb (x 6 8)
    clear * - r3523 e3524 e3525 e3526 e3527 e3528 e3529 b3530 b3531 b3532 b3533 b3534 b3535 b3536 b3537 d3446 d3470 d3494 g7
    omega
  have d3538 : (x 3 1 && x 3 11).toNat = 0 := by
    have r3539 := hand2 (x 3 1) (x 3 11)
    have b3540 := hb (x 3 11)
    have b3541 := hb (x 3 1 && x 3 11)
    clear * - r3539 b3540 b3541 d3522
    omega
  have d3542 : (x 3 5 && x 3 11).toNat = 0 := by
    have r3543 := hand2 (x 3 5) (x 3 11)
    have b3544 := hb (x 3 11)
    have b3545 := hb (x 3 5 && x 3 11)
    clear * - r3543 b3544 b3545 d3522
    omega
  have d3546 : (x 3 7 && x 3 11).toNat = 0 := by
    have r3547 := hand2 (x 3 7) (x 3 11)
    have b3548 := hb (x 3 11)
    have b3549 := hb (x 3 7 && x 3 11)
    clear * - r3547 b3548 b3549 d3522
    omega
  have d3550 : (x 2 4).toNat = 0 := by
    have r3551 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e3552 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e3553 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e3554 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e3555 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e3556 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e3557 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b3558 := hb (x (-1) 7)
    have b3559 := hb (x 0 6)
    have b3560 := hb (x 1 5)
    have b3561 := hb (x 2 4)
    have b3562 := hb (x 3 11)
    have b3563 := hb (x 4 10)
    have b3564 := hb (x 5 9)
    have b3565 := hb (x 6 8)
    clear * - r3551 e3552 e3553 e3554 e3555 e3556 e3557 b3558 b3559 b3560 b3561 b3562 b3563 b3564 b3565 d3446 d3470 d3494 d3522 g7
    omega
  have d3566 : (x 2 4 && x 2 14).toNat = 0 := by
    have r3567 := hand1 (x 2 4) (x 2 14)
    have b3568 := hb (x 2 4)
    have b3569 := hb (x 2 4 && x 2 14)
    clear * - r3567 b3568 b3569 d3550
    omega
  have d3570 : (x 2 4 && x 2 8).toNat = 0 := by
    have r3571 := hand1 (x 2 4) (x 2 8)
    have b3572 := hb (x 2 4)
    have b3573 := hb (x 2 4 && x 2 8)
    clear * - r3571 b3572 b3573 d3550
    omega
  have d3574 : (x 1 5).toNat = 0 := by
    have r3575 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e3576 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e3577 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e3578 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e3579 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e3580 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e3581 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b3582 := hb (x (-1) 7)
    have b3583 := hb (x 0 6)
    have b3584 := hb (x 1 5)
    have b3585 := hb (x 2 4)
    have b3586 := hb (x 3 11)
    have b3587 := hb (x 4 10)
    have b3588 := hb (x 5 9)
    have b3589 := hb (x 6 8)
    clear * - r3575 e3576 e3577 e3578 e3579 e3580 e3581 b3582 b3583 b3584 b3585 b3586 b3587 b3588 b3589 d3446 d3470 d3494 d3522 d3550 g7
    omega
  have d3590 : (x 1 5 && x 1 9).toNat = 0 := by
    have r3591 := hand1 (x 1 5) (x 1 9)
    have b3592 := hb (x 1 5)
    have b3593 := hb (x 1 5 && x 1 9)
    clear * - r3591 b3592 b3593 d3574
    omega
  have d3594 : (x (-1) 7).toNat = 0 := by
    have r3595 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e3596 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e3597 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e3598 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e3599 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e3600 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e3601 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b3602 := hb (x (-1) 7)
    have b3603 := hb (x 0 6)
    have b3604 := hb (x 1 5)
    have b3605 := hb (x 2 4)
    have b3606 := hb (x 3 11)
    have b3607 := hb (x 4 10)
    have b3608 := hb (x 5 9)
    have b3609 := hb (x 6 8)
    clear * - r3595 e3596 e3597 e3598 e3599 e3600 e3601 b3602 b3603 b3604 b3605 b3606 b3607 b3608 b3609 d3446 d3470 d3494 d3522 d3550 d3574 g7
    omega
  have d3610 : (x (-1) 7 && x (-1) 11).toNat = 0 := by
    have r3611 := hand1 (x (-1) 7) (x (-1) 11)
    have b3612 := hb (x (-1) 7)
    have b3613 := hb (x (-1) 7 && x (-1) 11)
    clear * - r3611 b3612 b3613 d3594
    omega
  cases h3614 : x 0 7
  · have f3615 : (x 0 7).toNat = 0 := by rw [h3614]; rfl
    cases h3616 : x 0 13
    · have f3617 : (x 0 13).toNat = 0 := by rw [h3616]; rfl
      have d3618 : (x (-2) 2).toNat = 1 := by
        have r3619 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b3620 := hb (x (-2) 2)
        have b3621 := hb (x 0 13)
        have b3622 := hb (x (-1) 1 && x (-1) 14)
        clear * - r3619 b3620 b3621 b3622 f3617 d3426
        omega
      have d3623 : (x (-2) 14).toNat = 1 := by
        have r3624 : (x (-2) 2).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp2 (-2))
        have b3625 := hb (x (-2) 2)
        have b3626 := hb (x (-2) 14)
        clear * - r3624 b3625 b3626 d3618
        omega
      have d3627 : (x (-3) 1).toNat = 0 := by
        have r3628 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b3629 := hb (x (-3) 1)
        have b3630 := hb (x (-2) 14)
        clear * - r3628 b3629 b3630 d3623
        omega
      have d3631 : (x (-3) 1 && x (-3) 12).toNat = 0 := by
        have r3632 := hand1 (x (-3) 1) (x (-3) 12)
        have b3633 := hb (x (-3) 1)
        have b3634 := hb (x (-3) 1 && x (-3) 12)
        clear * - r3632 b3633 b3634 d3627
        omega
      have d3635 : (x (-3) 13).toNat = 0 := by
        have r3636 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
        have b3637 := hb (x (-3) 1)
        have b3638 := hb (x (-3) 13)
        clear * - r3636 b3637 b3638 d3627
        omega
      have d3639 : (x (-3) 9 && x (-3) 13).toNat = 0 := by
        have r3640 := hand2 (x (-3) 9) (x (-3) 13)
        have b3641 := hb (x (-3) 13)
        have b3642 := hb (x (-3) 9 && x (-3) 13)
        clear * - r3640 b3641 b3642 d3635
        omega
      have d3643 : (x (-3) 9).toNat = 0 := by
        have r3644 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
        have b3645 := hb (x (-3) 1)
        have b3646 := hb (x (-3) 9)
        clear * - r3644 b3645 b3646 d3627
        omega
      have d3647 : (x 0 12).toNat = 0 := by
        have r3648 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e3649 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
        have e3650 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
        have b3651 := hb (x (-3) 3)
        have b3652 := hb (x (-2) 2)
        have b3653 := hb (x (-1) 13)
        have b3654 := hb (x 0 12)
        clear * - r3648 e3649 e3650 b3651 b3652 b3653 b3654 d3430 d3618
        omega
      have d3655 : (x 0 1 && x 0 12).toNat = 0 := by
        have r3656 := hand2 (x 0 1) (x 0 12)
        have b3657 := hb (x 0 12)
        have b3658 := hb (x 0 1 && x 0 12)
        clear * - r3656 b3657 b3658 d3647
        omega
      cases h3659 : x 1 1
      · have f3660 : (x 1 1).toNat = 0 := by rw [h3659]; rfl
        have d3661 : (x 1 13).toNat = 0 := by
          have r3662 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
          have b3663 := hb (x 1 1)
          have b3664 := hb (x 1 13)
          clear * - r3662 b3663 b3664 f3660
          omega
        have d3665 : (x 1 3 && x 1 13).toNat = 0 := by
          have r3666 := hand2 (x 1 3) (x 1 13)
          have b3667 := hb (x 1 13)
          have b3668 := hb (x 1 3 && x 1 13)
          clear * - r3666 b3667 b3668 d3661
          omega
        have d3669 : (x 1 4 && x 1 13).toNat = 0 := by
          have r3670 := hand2 (x 1 4) (x 1 13)
          have b3671 := hb (x 1 13)
          have b3672 := hb (x 1 4 && x 1 13)
          clear * - r3670 b3671 b3672 d3661
          omega
        have d3673 : (x 1 7 && x 1 13).toNat = 0 := by
          have r3674 := hand2 (x 1 7) (x 1 13)
          have b3675 := hb (x 1 13)
          have b3676 := hb (x 1 7 && x 1 13)
          clear * - r3674 b3675 b3676 d3661
          omega
        have d3677 : (x 1 9 && x 1 13).toNat = 0 := by
          have r3678 := hand2 (x 1 9) (x 1 13)
          have b3679 := hb (x 1 13)
          have b3680 := hb (x 1 9 && x 1 13)
          clear * - r3678 b3679 b3680 d3661
          omega
        have d3681 : (x 1 9).toNat = 0 := by
          have r3682 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
          have b3683 := hb (x 1 1)
          have b3684 := hb (x 1 9)
          clear * - r3682 b3683 b3684 f3660
          omega
        have d3685 : (x 2 2 && x 2 12).toNat = 1 := by
          have r3686 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b3687 := hb (x (-1) 5)
          have b3688 := hb (x 4 10)
          have b3689 := hb (x 3 1 && x 3 11)
          have b3690 := hb (x 2 2 && x 2 12)
          have b3691 := hb (x 1 3 && x 1 13)
          have b3692 := hb (x 0 4 && x 0 14)
          clear * - r3686 b3687 b3688 b3689 b3690 b3691 b3692 d3494 d3538 d3665 g34 d3438
          omega
        have d3693 : (x 2 12).toNat = 1 := by
          have r3694 := hand2 (x 2 2) (x 2 12)
          have b3695 := hb (x 2 12)
          have b3696 := hb (x 2 2 && x 2 12)
          clear * - r3694 b3695 b3696 d3685
          omega
        have d3697 : (x (-1) 3).toNat = 0 := by
          have r3698 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e3699 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
          have e3700 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
          have b3701 := hb (x (-1) 3)
          have b3702 := hb (x 0 2)
          have b3703 := hb (x 1 13)
          have b3704 := hb (x 2 12)
          clear * - r3698 e3699 e3700 b3701 b3702 b3703 b3704 d3693 d3661 g5
          omega
        have d3705 : (x (-1) 11).toNat = 0 := by
          have r3706 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
          have b3707 := hb (x (-1) 3)
          have b3708 := hb (x (-1) 11)
          clear * - r3706 b3707 b3708 d3697
          omega
        have d3709 : (x (-1) 2 && x (-1) 11).toNat = 0 := by
          have r3710 := hand2 (x (-1) 2) (x (-1) 11)
          have b3711 := hb (x (-1) 11)
          have b3712 := hb (x (-1) 2 && x (-1) 11)
          clear * - r3710 b3711 b3712 d3705
          omega
        have d3713 : (x 2 2).toNat = 1 := by
          have r3714 := hand1 (x 2 2) (x 2 12)
          have b3715 := hb (x 2 2)
          have b3716 := hb (x 2 2 && x 2 12)
          clear * - r3714 b3715 b3716 d3685
          omega
        have d3717 : (x 4 12).toNat = 0 := by
          have r3718 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e3719 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e3720 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b3721 := hb (x 1 3)
          have b3722 := hb (x 2 2)
          have b3723 := hb (x 3 13)
          have b3724 := hb (x 4 12)
          clear * - r3718 e3719 e3720 b3721 b3722 b3723 b3724 d3713
          omega
        have d3725 : (x 4 2 && x 4 12).toNat = 0 := by
          have r3726 := hand2 (x 4 2) (x 4 12)
          have b3727 := hb (x 4 12)
          have b3728 := hb (x 4 2 && x 4 12)
          clear * - r3726 b3727 b3728 d3717
          omega
        have d3729 : (x 4 4).toNat = 0 := by
          have r3730 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
          have b3731 := hb (x 4 4)
          have b3732 := hb (x 4 12)
          clear * - r3730 b3731 b3732 d3717
          omega
        have d3733 : (x 3 13).toNat = 0 := by
          have r3734 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e3735 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e3736 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b3737 := hb (x 1 3)
          have b3738 := hb (x 2 2)
          have b3739 := hb (x 3 13)
          have b3740 := hb (x 4 12)
          clear * - r3734 e3735 e3736 b3737 b3738 b3739 b3740 d3717 d3713
          omega
        have d3741 : (x 3 3 && x 3 13).toNat = 0 := by
          have r3742 := hand2 (x 3 3) (x 3 13)
          have b3743 := hb (x 3 13)
          have b3744 := hb (x 3 3 && x 3 13)
          clear * - r3742 b3743 b3744 d3733
          omega
        have d3745 : (x 3 5).toNat = 0 := by
          have r3746 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
          have b3747 := hb (x 3 5)
          have b3748 := hb (x 3 13)
          clear * - r3746 b3747 b3748 d3733
          omega
        have d3749 : (x 1 3).toNat = 0 := by
          have r3750 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e3751 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e3752 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b3753 := hb (x 1 3)
          have b3754 := hb (x 2 2)
          have b3755 := hb (x 3 13)
          have b3756 := hb (x 4 12)
          clear * - r3750 e3751 e3752 b3753 b3754 b3755 b3756 d3717 d3733 d3713
          omega
        have d3757 : (x 1 11).toNat = 0 := by
          have r3758 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
          have b3759 := hb (x 1 3)
          have b3760 := hb (x 1 11)
          clear * - r3758 b3759 b3760 d3749
          omega
        have d3761 : (x (-2) 3 && x (-2) 14).toNat = 1 := by
          have r3762 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b3763 := hb (x (-3) 4)
          have b3764 := hb (x 1 11)
          have b3765 := hb (x 0 1 && x 0 12)
          have b3766 := hb (x (-1) 2 && x (-1) 13)
          have b3767 := hb (x (-2) 3 && x (-2) 14)
          clear * - r3762 b3763 b3764 b3765 b3766 b3767 d3757 d3655 d3434 g2
          omega
        have d3768 : (x (-2) 3).toNat = 1 := by
          have r3769 := hand1 (x (-2) 3) (x (-2) 14)
          have b3770 := hb (x (-2) 3)
          have b3771 := hb (x (-2) 3 && x (-2) 14)
          clear * - r3769 b3770 b3771 d3761
          omega
        have d3772 : (x 1 12).toNat = 0 := by
          have r3773 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e3774 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
          have e3775 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
          have b3776 := hb (x (-2) 3)
          have b3777 := hb (x (-1) 2)
          have b3778 := hb (x 0 13)
          have b3779 := hb (x 1 12)
          clear * - r3773 e3774 e3775 b3776 b3777 b3778 b3779 f3617 d3768
          omega
        have d3780 : (x (-1) 2).toNat = 0 := by
          have r3781 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e3782 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
          have e3783 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
          have b3784 := hb (x (-2) 3)
          have b3785 := hb (x (-1) 2)
          have b3786 := hb (x 0 13)
          have b3787 := hb (x 1 12)
          clear * - r3781 e3782 e3783 b3784 b3785 b3786 b3787 d3772 f3617 d3768
          omega
        have d3788 : (x (-1) 2 && x (-1) 12).toNat = 0 := by
          have r3789 := hand1 (x (-1) 2) (x (-1) 12)
          have b3790 := hb (x (-1) 2)
          have b3791 := hb (x (-1) 2 && x (-1) 12)
          clear * - r3789 b3790 b3791 d3780
          omega
        have d3792 : (x (-2) 3 && x (-2) 13).toNat = 1 := by
          have r3793 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b3794 := hb (x (-4) 5)
          have b3795 := hb (x 1 10)
          have b3796 := hb (x 0 1 && x 0 11)
          have b3797 := hb (x (-1) 2 && x (-1) 12)
          have b3798 := hb (x (-2) 3 && x (-2) 13)
          have b3799 := hb (x (-3) 4 && x (-3) 14)
          clear * - r3793 b3794 b3795 b3796 b3797 b3798 b3799 g14 g32 d3788 g33 g1
          omega
        have d3800 : (x (-2) 13).toNat = 1 := by
          have r3801 := hand2 (x (-2) 3) (x (-2) 13)
          have b3802 := hb (x (-2) 13)
          have b3803 := hb (x (-2) 3 && x (-2) 13)
          clear * - r3801 b3802 b3803 d3792
          omega
        have d3804 : (x (-2) 1).toNat = 1 := by
          have r3805 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
          have b3806 := hb (x (-2) 1)
          have b3807 := hb (x (-2) 13)
          clear * - r3805 b3806 b3807 d3800
          omega
        have d3808 : (x (-1) 14).toNat = 0 := by
          have r3809 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b3810 := hb (x (-2) 1)
          have b3811 := hb (x (-1) 14)
          clear * - r3809 b3810 b3811 d3804
          omega
        have d3812 : (x (-1) 6).toNat = 0 := by
          have r3813 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
          have b3814 := hb (x (-1) 6)
          have b3815 := hb (x (-1) 14)
          clear * - r3813 b3814 b3815 d3808
          omega
        have d3816 : (x 2 3 && x 2 12).toNat = 1 := by
          have r3817 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b3818 := hb (x (-1) 6)
          have b3819 := hb (x 5 9)
          have b3820 := hb (x 4 1 && x 4 10)
          have b3821 := hb (x 3 2 && x 3 11)
          have b3822 := hb (x 2 3 && x 2 12)
          have b3823 := hb (x 1 4 && x 1 13)
          have b3824 := hb (x 0 5 && x 0 14)
          clear * - r3817 b3818 b3819 b3820 b3821 b3822 b3823 b3824 d3470 d3510 g30 d3669 g31 d3812
          omega
        have d3825 : (x 2 3).toNat = 1 := by
          have r3826 := hand1 (x 2 3) (x 2 12)
          have b3827 := hb (x 2 3)
          have b3828 := hb (x 2 3 && x 2 12)
          clear * - r3826 b3827 b3828 d3816
          omega
        have d3829 : (x 5 12).toNat = 0 := by
          have r3830 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e3831 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e3832 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b3833 := hb (x 2 3)
          have b3834 := hb (x 3 2)
          have b3835 := hb (x 4 13)
          have b3836 := hb (x 5 12)
          clear * - r3830 e3831 e3832 b3833 b3834 b3835 b3836 g17 d3825
          omega
        have d3837 : (x 5 1 && x 5 12).toNat = 0 := by
          have r3838 := hand2 (x 5 1) (x 5 12)
          have b3839 := hb (x 5 12)
          have b3840 := hb (x 5 1 && x 5 12)
          clear * - r3838 b3839 b3840 d3829
          omega
        have d3841 : (x 5 4).toNat = 0 := by
          have r3842 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
          have b3843 := hb (x 5 4)
          have b3844 := hb (x 5 12)
          clear * - r3842 b3843 b3844 d3829
          omega
        have d3845 : (x 4 13).toNat = 0 := by
          have r3846 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e3847 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e3848 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b3849 := hb (x 2 3)
          have b3850 := hb (x 3 2)
          have b3851 := hb (x 4 13)
          have b3852 := hb (x 5 12)
          clear * - r3846 e3847 e3848 b3849 b3850 b3851 b3852 d3829 g17 d3825
          omega
        have d3853 : (x 4 2 && x 4 13).toNat = 0 := by
          have r3854 := hand2 (x 4 2) (x 4 13)
          have b3855 := hb (x 4 13)
          have b3856 := hb (x 4 2 && x 4 13)
          clear * - r3854 b3855 b3856 d3845
          omega
        have d3857 : (x 6 11).toNat = 1 := by
          have r3858 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := by have q := hcov11 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b3859 := hb (x 2 4)
          have b3860 := hb (x 6 11)
          have b3861 := hb (x 5 1 && x 5 12)
          have b3862 := hb (x 4 2 && x 4 13)
          have b3863 := hb (x 3 3 && x 3 14)
          clear * - r3858 b3859 b3860 b3861 b3862 b3863 d3837 d3853 g38 d3550
          omega
        have d3864 : (x 6 3).toNat = 1 := by
          have r3865 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
          have b3866 := hb (x 6 3)
          have b3867 := hb (x 6 11)
          clear * - r3865 b3866 b3867 d3857
          omega
        have d3868 : (x 9 12).toNat = 0 := by
          have r3869 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e3870 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
          have e3871 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
          have b3872 := hb (x 6 3)
          have b3873 := hb (x 7 2)
          have b3874 := hb (x 8 13)
          have b3875 := hb (x 9 12)
          clear * - r3869 e3870 e3871 b3872 b3873 b3874 b3875 d3864
          omega
        have d3876 : (x 8 13).toNat = 0 := by
          have r3877 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e3878 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
          have e3879 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
          have b3880 := hb (x 6 3)
          have b3881 := hb (x 7 2)
          have b3882 := hb (x 8 13)
          have b3883 := hb (x 9 12)
          clear * - r3877 e3878 e3879 b3880 b3881 b3882 b3883 d3868 d3864
          omega
        have d3884 : (x 7 2).toNat = 0 := by
          have r3885 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e3886 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
          have e3887 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
          have b3888 := hb (x 6 3)
          have b3889 := hb (x 7 2)
          have b3890 := hb (x 8 13)
          have b3891 := hb (x 9 12)
          clear * - r3885 e3886 e3887 b3888 b3889 b3890 b3891 d3868 d3876 d3864
          omega
        have d3892 : (x 7 10).toNat = 0 := by
          have r3893 : (x 7 10).toNat ≤ (x 7 2).toNat := himp _ _ (hp10 7)
          have b3894 := hb (x 7 2)
          have b3895 := hb (x 7 10)
          clear * - r3893 b3894 b3895 d3884
          omega
        have d3896 : (x 4 5).toNat = 0 := by
          have r3897 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
          have b3898 := hb (x 4 5)
          have b3899 := hb (x 4 13)
          clear * - r3897 b3898 b3899 d3845
          omega
        have d3900 : (x (-2) 3 && x (-2) 12).toNat = 1 := by
          have r3901 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b3902 := hb (x (-5) 6)
          have b3903 := hb (x 1 9)
          have b3904 := hb (x 0 1 && x 0 10)
          have b3905 := hb (x (-1) 2 && x (-1) 11)
          have b3906 := hb (x (-2) 3 && x (-2) 12)
          have b3907 := hb (x (-3) 4 && x (-3) 13)
          have b3908 := hb (x (-4) 5 && x (-4) 14)
          clear * - r3901 b3902 b3903 b3904 b3905 b3906 b3907 b3908 d3681 g27 d3709 g28 g29 g0
          omega
        have d3909 : (x (-2) 12).toNat = 1 := by
          have r3910 := hand2 (x (-2) 3) (x (-2) 12)
          have b3911 := hb (x (-2) 12)
          have b3912 := hb (x (-2) 3 && x (-2) 12)
          clear * - r3910 b3911 b3912 d3900
          omega
        have d3913 : (x (-4) 2).toNat = 0 := by
          have r3914 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e3915 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
          have e3916 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
          have b3917 := hb (x (-5) 3)
          have b3918 := hb (x (-4) 2)
          have b3919 := hb (x (-3) 13)
          have b3920 := hb (x (-2) 12)
          clear * - r3914 e3915 e3916 b3917 b3918 b3919 b3920 d3909 d3635
          omega
        have d3921 : (x (-4) 2 && x (-4) 13).toNat = 0 := by
          have r3922 := hand1 (x (-4) 2) (x (-4) 13)
          have b3923 := hb (x (-4) 2)
          have b3924 := hb (x (-4) 2 && x (-4) 13)
          clear * - r3922 b3923 b3924 d3913
          omega
        have d3925 : (x (-4) 10).toNat = 0 := by
          have r3926 : (x (-4) 10).toNat ≤ (x (-4) 2).toNat := himp _ _ (hp10 (-4))
          have b3927 := hb (x (-4) 2)
          have b3928 := hb (x (-4) 10)
          clear * - r3926 b3927 b3928 d3913
          omega
        have d3929 : (x (-5) 3).toNat = 0 := by
          have r3930 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e3931 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
          have e3932 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
          have b3933 := hb (x (-5) 3)
          have b3934 := hb (x (-4) 2)
          have b3935 := hb (x (-3) 13)
          have b3936 := hb (x (-2) 12)
          clear * - r3930 e3931 e3932 b3933 b3934 b3935 b3936 d3909 d3635 d3913
          omega
        have d3937 : (x (-5) 3 && x (-5) 14).toNat = 0 := by
          have r3938 := hand1 (x (-5) 3) (x (-5) 14)
          have b3939 := hb (x (-5) 3)
          have b3940 := hb (x (-5) 3 && x (-5) 14)
          clear * - r3938 b3939 b3940 d3929
          omega
        have d3941 : (x (-6) 4).toNat = 1 := by
          have r3942 : 1 ≤ (x (-2) 11).toNat + (x (-3) 1 && x (-3) 12).toNat + (x (-4) 2 && x (-4) 13).toNat + (x (-5) 3 && x (-5) 14).toNat + (x (-6) 4).toNat := by have q := hcov11 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b3943 := hb (x (-6) 4)
          have b3944 := hb (x (-2) 11)
          have b3945 := hb (x (-3) 1 && x (-3) 12)
          have b3946 := hb (x (-4) 2 && x (-4) 13)
          have b3947 := hb (x (-5) 3 && x (-5) 14)
          clear * - r3942 b3943 b3944 b3945 b3946 b3947 g3 d3631 d3921 d3937
          omega
        have d3948 : (x (-6) 12).toNat = 1 := by
          have r3949 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
          have b3950 := hb (x (-6) 4)
          have b3951 := hb (x (-6) 12)
          clear * - r3949 b3950 b3951 d3941
          omega
        have d3952 : (x (-7) 13).toNat = 0 := by
          have r3953 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e3954 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
          have e3955 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
          have b3956 := hb (x (-9) 3)
          have b3957 := hb (x (-8) 2)
          have b3958 := hb (x (-7) 13)
          have b3959 := hb (x (-6) 12)
          clear * - r3953 e3954 e3955 b3956 b3957 b3958 b3959 d3948
          omega
        have d3960 : (x (-7) 5).toNat = 0 := by
          have r3961 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
          have b3962 := hb (x (-7) 5)
          have b3963 := hb (x (-7) 13)
          clear * - r3961 b3962 b3963 d3952
          omega
        have d3964 : (x (-5) 11).toNat = 0 := by
          have r3965 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
          have b3966 := hb (x (-5) 3)
          have b3967 := hb (x (-5) 11)
          clear * - r3965 b3966 b3967 d3929
          omega
        have d3968 : (x 9 8).toNat = 0 := by
          have r3969 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e3970 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
          have e3971 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
          have e3972 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
          have e3973 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
          have e3974 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
          have e3975 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
          have b3976 := hb (x 2 7)
          have b3977 := hb (x 3 6)
          have b3978 := hb (x 4 5)
          have b3979 := hb (x 5 4)
          have b3980 := hb (x 6 11)
          have b3981 := hb (x 7 10)
          have b3982 := hb (x 8 9)
          have b3983 := hb (x 9 8)
          clear * - r3969 e3970 e3971 e3972 e3973 e3974 e3975 b3976 b3977 b3978 b3979 b3980 b3981 b3982 b3983 d3892 d3857 d3841 d3896 g19
          omega
        have d3984 : (x 8 9).toNat = 0 := by
          have r3985 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e3986 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
          have e3987 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
          have e3988 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
          have e3989 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
          have e3990 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
          have e3991 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
          have b3992 := hb (x 2 7)
          have b3993 := hb (x 3 6)
          have b3994 := hb (x 4 5)
          have b3995 := hb (x 5 4)
          have b3996 := hb (x 6 11)
          have b3997 := hb (x 7 10)
          have b3998 := hb (x 8 9)
          have b3999 := hb (x 9 8)
          clear * - r3985 e3986 e3987 e3988 e3989 e3990 e3991 b3992 b3993 b3994 b3995 b3996 b3997 b3998 b3999 d3968 d3892 d3857 d3841 d3896 g19
          omega
        have d4000 : (x 2 7).toNat = 0 := by
          have r4001 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4002 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
          have e4003 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
          have e4004 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
          have e4005 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
          have e4006 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
          have e4007 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
          have b4008 := hb (x 2 7)
          have b4009 := hb (x 3 6)
          have b4010 := hb (x 4 5)
          have b4011 := hb (x 5 4)
          have b4012 := hb (x 6 11)
          have b4013 := hb (x 7 10)
          have b4014 := hb (x 8 9)
          have b4015 := hb (x 9 8)
          clear * - r4001 e4002 e4003 e4004 e4005 e4006 e4007 b4008 b4009 b4010 b4011 b4012 b4013 b4014 b4015 d3968 d3984 d3892 d3857 d3841 d3896 g19
          omega
        have d4016 : (x (-2) 8).toNat = 0 := by
          have r4017 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4018 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
          have e4019 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
          have e4020 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
          have e4021 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
          have e4022 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
          have e4023 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
          have b4024 := hb (x (-9) 7)
          have b4025 := hb (x (-8) 6)
          have b4026 := hb (x (-7) 5)
          have b4027 := hb (x (-6) 4)
          have b4028 := hb (x (-5) 11)
          have b4029 := hb (x (-4) 10)
          have b4030 := hb (x (-3) 9)
          have b4031 := hb (x (-2) 8)
          clear * - r4017 e4018 e4019 e4020 e4021 e4022 e4023 b4024 b4025 b4026 b4027 b4028 b4029 b4030 b4031 d3643 d3925 d3964 d3941 d3960
          omega
        have d4032 : (x (-2) 8 && x (-2) 12).toNat = 0 := by
          have r4033 := hand1 (x (-2) 8) (x (-2) 12)
          have b4034 := hb (x (-2) 8)
          have b4035 := hb (x (-2) 8 && x (-2) 12)
          clear * - r4033 b4034 b4035 d4016
          omega
        have r4036 : (x 8 1).toNat + (x 7 2).toNat + (x 6 3).toNat + (x 5 4).toNat + (x 4 5).toNat + (x 3 6).toNat + (x 2 7).toNat + (x 1 8).toNat + (x 0 9).toNat + (x (-1) 10).toNat + (x (-2) 11).toNat + (x (-3) 12).toNat + (x (-4) 13).toNat + (x (-5) 14).toNat = 3 := by have q := hcount 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r4037 : (x 9 1).toNat + (x 8 2).toNat + (x 7 3).toNat + (x 6 4).toNat + (x 5 5).toNat + (x 4 6).toNat + (x 3 7).toNat + (x 2 8).toNat + (x 1 9).toNat + (x 0 10).toNat + (x (-1) 11).toNat + (x (-2) 12).toNat + (x (-3) 13).toNat + (x (-4) 14).toNat = 3 := by have q := hcount 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r4038 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e4039 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e4040 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e4041 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e4042 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e4043 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e4044 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have r4045 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e4046 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
        have e4047 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
        have e4048 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
        have e4049 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
        have e4050 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
        have e4051 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
        have r4052 : 1 ≤ (x 6 4).toNat + (x 5 1 && x 5 5).toNat + (x 4 2 && x 4 6).toNat + (x 3 3 && x 3 7).toNat + (x 2 4 && x 2 8).toNat + (x 1 5 && x 1 9).toNat + (x 0 6 && x 0 10).toNat + (x (-1) 7 && x (-1) 11).toNat + (x (-2) 8 && x (-2) 12).toNat + (x (-3) 9 && x (-3) 13).toNat + (x (-4) 10 && x (-4) 14).toNat + (x (-5) 11).toNat := by have q := hcov4 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e4053 : (x 5 1 && x 5 5).toNat = (x 5 5).toNat := handr _ _ (fun h => hp13 5 (hp5 5 (h)))
        have e4054 : (x (-4) 10 && x (-4) 14).toNat = (x (-4) 10).toNat := handl _ _ (fun h => hp2 (-4) (hp10 (-4) (h)))
        have r4055 : 1 ≤ (x 10 4).toNat + (x 9 1 && x 9 5).toNat + (x 8 2 && x 8 6).toNat + (x 7 3 && x 7 7).toNat + (x 6 4 && x 6 8).toNat + (x 5 5 && x 5 9).toNat + (x 4 6 && x 4 10).toNat + (x 3 7 && x 3 11).toNat + (x 2 8 && x 2 12).toNat + (x 1 9 && x 1 13).toNat + (x 0 10 && x 0 14).toNat + (x (-1) 11).toNat := by have q := hcov4 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e4056 : (x 9 1 && x 9 5).toNat = (x 9 5).toNat := handr _ _ (fun h => hp13 9 (hp5 9 (h)))
        have e4057 : (x 0 10 && x 0 14).toNat = (x 0 10).toNat := handl _ _ (fun h => hp2 0 (hp10 0 (h)))
        have r4058 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r4059 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r4060 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r4061 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r4062 : (x (-5) 2).toNat ≤ (x (-5) 14).toNat := himp _ _ (hp2 (-5))
        have r4063 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
        have r4064 := hand2 (x 4 2) (x 4 6)
        have r4065 := hand2 (x 3 3) (x 3 7)
        have r4066 := hand1 (x 8 2) (x 8 6)
        have r4067 := hand1 (x 7 3) (x 7 7)
        have r4068 := hand1 (x 2 8) (x 2 12)
        have r4069 := hand2 (x 7 1) (x 7 7)
        have r4070 := hand1 (x 2 6) (x 2 12)
        have r4071 := hand2 (x 5 1) (x 5 11)
        have r4072 := hand2 (x (-4) 1) (x (-4) 14)
        have r4073 := hand1 (x 8 1) (x 8 14)
        linarith only [r4036, r4037, r4038, e4039, e4040, e4041, e4042, e4043, e4044, r4045, e4046, e4047, e4048, e4049, e4050, e4051, r4052, e4053, e4054, r4055, e4056, e4057, r4058, r4059, r4060, r4061, r4062, r4063, r4064, r4065, r4066, r4067, r4068, r4069, r4070, r4071, r4072, r4073, d3964, d3925, d3635, g3, d3909, d3442, g4, d3705, g9, g10, d3574, g13, d3681, d4000, d3745, g19, d3729, d3896, d3841, d3864, d3884, d3570, d3590, g21, d3610, d4032, d3639, d3466, d3490, d3518, d3546, d3677, d3462, d3486, d3514, d3542, d3673, g24, d3725, d3741, d3566]
      · have f4154 : (x 1 1).toNat = 1 := by rw [h3659]; rfl
        have d4155 : (x 2 14).toNat = 0 := by
          have r4156 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4157 := hb (x 1 1)
          have b4158 := hb (x 2 14)
          clear * - r4156 b4157 b4158 f4154
          omega
        have d4159 : (x 2 1 && x 2 14).toNat = 0 := by
          have r4160 := hand2 (x 2 1) (x 2 14)
          have b4161 := hb (x 2 14)
          have b4162 := hb (x 2 1 && x 2 14)
          clear * - r4160 b4161 b4162 d4155
          omega
        have d4163 : (x 2 2).toNat = 0 := by
          have r4164 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
          have b4165 := hb (x 2 2)
          have b4166 := hb (x 2 14)
          clear * - r4164 b4165 b4166 d4155
          omega
        have d4167 : (x 4 13).toNat = 1 := by
          have r4168 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4169 := hb (x 2 2)
          have b4170 := hb (x 4 13)
          have b4171 := hb (x 3 1 && x 3 14)
          clear * - r4168 b4169 b4170 b4171 g39 d4163
          omega
        have d4172 : (x 4 1).toNat = 1 := by
          have r4173 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
          have b4174 := hb (x 4 1)
          have b4175 := hb (x 4 13)
          clear * - r4173 b4174 b4175 d4167
          omega
        have d4176 : (x 5 14).toNat = 0 := by
          have r4177 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4178 := hb (x 4 1)
          have b4179 := hb (x 5 14)
          clear * - r4177 b4178 b4179 d4172
          omega
        have d4180 : (x 5 1 && x 5 14).toNat = 0 := by
          have r4181 := hand2 (x 5 1) (x 5 14)
          have b4182 := hb (x 5 14)
          have b4183 := hb (x 5 1 && x 5 14)
          clear * - r4181 b4182 b4183 d4176
          omega
        have d4184 : (x 5 2).toNat = 0 := by
          have r4185 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
          have b4186 := hb (x 5 2)
          have b4187 := hb (x 5 14)
          clear * - r4185 b4186 b4187 d4176
          omega
        have d4188 : (x 3 13).toNat = 1 := by
          have r4189 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4190 := hb (x 1 2)
          have b4191 := hb (x 3 13)
          have b4192 := hb (x 2 1 && x 2 14)
          clear * - r4189 b4190 b4191 b4192 d4159 g11
          omega
        have d4193 : (x 3 1).toNat = 1 := by
          have r4194 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
          have b4195 := hb (x 3 1)
          have b4196 := hb (x 3 13)
          clear * - r4194 b4195 b4196 d4188
          omega
        have d4197 : (x 4 14).toNat = 0 := by
          have r4198 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4199 := hb (x 3 1)
          have b4200 := hb (x 4 14)
          clear * - r4198 b4199 b4200 d4193
          omega
        have d4201 : (x 4 1 && x 4 14).toNat = 0 := by
          have r4202 := hand2 (x 4 1) (x 4 14)
          have b4203 := hb (x 4 14)
          have b4204 := hb (x 4 1 && x 4 14)
          clear * - r4202 b4203 b4204 d4197
          omega
        have d4205 : (x 5 13).toNat = 1 := by
          have r4206 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4207 := hb (x 3 2)
          have b4208 := hb (x 5 13)
          have b4209 := hb (x 4 1 && x 4 14)
          clear * - r4206 b4207 b4208 b4209 d4201 g17
          omega
        have d4210 : (x 5 1).toNat = 1 := by
          have r4211 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
          have b4212 := hb (x 5 1)
          have b4213 := hb (x 5 13)
          clear * - r4211 b4212 b4213 d4205
          omega
        have d4214 : (x 6 14).toNat = 0 := by
          have r4215 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4216 := hb (x 5 1)
          have b4217 := hb (x 6 14)
          clear * - r4215 b4216 b4217 d4210
          omega
        have d4218 : (x 6 1 && x 6 14).toNat = 0 := by
          have r4219 := hand2 (x 6 1) (x 6 14)
          have b4220 := hb (x 6 14)
          have b4221 := hb (x 6 1 && x 6 14)
          clear * - r4219 b4220 b4221 d4214
          omega
        have d4222 : (x 7 13).toNat = 1 := by
          have r4223 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4224 := hb (x 5 2)
          have b4225 := hb (x 7 13)
          have b4226 := hb (x 6 1 && x 6 14)
          clear * - r4223 b4224 b4225 b4226 d4218 d4184
          omega
        have d4227 : (x 7 1).toNat = 1 := by
          have r4228 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
          have b4229 := hb (x 7 1)
          have b4230 := hb (x 7 13)
          clear * - r4228 b4229 b4230 d4222
          omega
        have d4231 : (x 8 14).toNat = 0 := by
          have r4232 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4233 := hb (x 7 1)
          have b4234 := hb (x 8 14)
          clear * - r4232 b4233 b4234 d4227
          omega
        have d4235 : (x 8 1 && x 8 14).toNat = 0 := by
          have r4236 := hand2 (x 8 1) (x 8 14)
          have b4237 := hb (x 8 14)
          have b4238 := hb (x 8 1 && x 8 14)
          clear * - r4236 b4237 b4238 d4231
          omega
        have d4239 : (x 8 2).toNat = 0 := by
          have r4240 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
          have b4241 := hb (x 8 2)
          have b4242 := hb (x 8 14)
          clear * - r4240 b4241 b4242 d4231
          omega
        have d4243 : (x 6 2).toNat = 0 := by
          have r4244 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
          have b4245 := hb (x 6 2)
          have b4246 := hb (x 6 14)
          clear * - r4244 b4245 b4246 d4214
          omega
        have d4247 : (x 4 2).toNat = 0 := by
          have r4248 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
          have b4249 := hb (x 4 2)
          have b4250 := hb (x 4 14)
          clear * - r4248 b4249 b4250 d4197
          omega
        have d4251 : (x 6 13).toNat = 1 := by
          have r4252 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4253 := hb (x 4 2)
          have b4254 := hb (x 6 13)
          have b4255 := hb (x 5 1 && x 5 14)
          clear * - r4252 b4253 b4254 b4255 d4180 d4247
          omega
        have d4256 : (x 6 1).toNat = 1 := by
          have r4257 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
          have b4258 := hb (x 6 1)
          have b4259 := hb (x 6 13)
          clear * - r4257 b4258 b4259 d4251
          omega
        have d4260 : (x 7 14).toNat = 0 := by
          have r4261 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4262 := hb (x 6 1)
          have b4263 := hb (x 7 14)
          clear * - r4261 b4262 b4263 d4256
          omega
        have d4264 : (x 7 1 && x 7 14).toNat = 0 := by
          have r4265 := hand2 (x 7 1) (x 7 14)
          have b4266 := hb (x 7 14)
          have b4267 := hb (x 7 1 && x 7 14)
          clear * - r4265 b4266 b4267 d4260
          omega
        have d4268 : (x 8 13).toNat = 1 := by
          have r4269 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4270 := hb (x 6 2)
          have b4271 := hb (x 8 13)
          have b4272 := hb (x 7 1 && x 7 14)
          clear * - r4269 b4270 b4271 b4272 d4264 d4243
          omega
        have d4273 : (x 8 1).toNat = 1 := by
          have r4274 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
          have b4275 := hb (x 8 1)
          have b4276 := hb (x 8 13)
          clear * - r4274 b4275 b4276 d4268
          omega
        have d4277 : (x 9 14).toNat = 0 := by
          have r4278 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4279 := hb (x 8 1)
          have b4280 := hb (x 9 14)
          clear * - r4278 b4279 b4280 d4273
          omega
        have d4281 : (x 9 1 && x 9 14).toNat = 0 := by
          have r4282 := hand2 (x 9 1) (x 9 14)
          have b4283 := hb (x 9 14)
          have b4284 := hb (x 9 1 && x 9 14)
          clear * - r4282 b4283 b4284 d4277
          omega
        have d4285 : (x 10 13).toNat = 1 := by
          have r4286 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4287 := hb (x 8 2)
          have b4288 := hb (x 10 13)
          have b4289 := hb (x 9 1 && x 9 14)
          clear * - r4286 b4287 b4288 b4289 d4281 d4239
          omega
        have d4290 : (x 10 1).toNat = 1 := by
          have r4291 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
          have b4292 := hb (x 10 1)
          have b4293 := hb (x 10 13)
          clear * - r4291 b4292 b4293 d4285
          omega
        have d4294 : (x 11 14).toNat = 0 := by
          have r4295 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4296 := hb (x 10 1)
          have b4297 := hb (x 11 14)
          clear * - r4295 b4296 b4297 d4290
          omega
        have d4298 : (x 11 1 && x 11 14).toNat = 0 := by
          have r4299 := hand2 (x 11 1) (x 11 14)
          have b4300 := hb (x 11 14)
          have b4301 := hb (x 11 1 && x 11 14)
          clear * - r4299 b4300 b4301 d4294
          omega
        have d4302 : (x 11 2).toNat = 0 := by
          have r4303 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
          have b4304 := hb (x 11 2)
          have b4305 := hb (x 11 14)
          clear * - r4303 b4304 b4305 d4294
          omega
        have d4306 : (x 9 2).toNat = 0 := by
          have r4307 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
          have b4308 := hb (x 9 2)
          have b4309 := hb (x 9 14)
          clear * - r4307 b4308 b4309 d4277
          omega
        have d4310 : (x 7 2).toNat = 0 := by
          have r4311 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
          have b4312 := hb (x 7 2)
          have b4313 := hb (x 7 14)
          clear * - r4311 b4312 b4313 d4260
          omega
        have d4314 : (x 9 13).toNat = 1 := by
          have r4315 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4316 := hb (x 7 2)
          have b4317 := hb (x 9 13)
          have b4318 := hb (x 8 1 && x 8 14)
          clear * - r4315 b4316 b4317 b4318 d4235 d4310
          omega
        have d4319 : (x 9 1).toNat = 1 := by
          have r4320 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
          have b4321 := hb (x 9 1)
          have b4322 := hb (x 9 13)
          clear * - r4320 b4321 b4322 d4314
          omega
        have d4323 : (x 10 14).toNat = 0 := by
          have r4324 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4325 := hb (x 9 1)
          have b4326 := hb (x 10 14)
          clear * - r4324 b4325 b4326 d4319
          omega
        have d4327 : (x 10 1 && x 10 14).toNat = 0 := by
          have r4328 := hand2 (x 10 1) (x 10 14)
          have b4329 := hb (x 10 14)
          have b4330 := hb (x 10 1 && x 10 14)
          clear * - r4328 b4329 b4330 d4323
          omega
        have d4331 : (x 11 13).toNat = 1 := by
          have r4332 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4333 := hb (x 9 2)
          have b4334 := hb (x 11 13)
          have b4335 := hb (x 10 1 && x 10 14)
          clear * - r4332 b4333 b4334 b4335 d4327 d4306
          omega
        have d4336 : (x 11 1).toNat = 1 := by
          have r4337 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
          have b4338 := hb (x 11 1)
          have b4339 := hb (x 11 13)
          clear * - r4337 b4338 b4339 d4331
          omega
        have d4340 : (x 12 14).toNat = 0 := by
          have r4341 : (x 12 14).toNat + (x 11 1).toNat = 1 := by have q := hd14 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4342 := hb (x 11 1)
          have b4343 := hb (x 12 14)
          clear * - r4341 b4342 b4343 d4336
          omega
        have d4344 : (x 12 1 && x 12 14).toNat = 0 := by
          have r4345 := hand2 (x 12 1) (x 12 14)
          have b4346 := hb (x 12 14)
          have b4347 := hb (x 12 1 && x 12 14)
          clear * - r4345 b4346 b4347 d4340
          omega
        have d4348 : (x 13 13).toNat = 1 := by
          have r4349 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4350 := hb (x 11 2)
          have b4351 := hb (x 13 13)
          have b4352 := hb (x 12 1 && x 12 14)
          clear * - r4349 b4350 b4351 b4352 d4344 d4302
          omega
        have d4353 : (x 13 1).toNat = 1 := by
          have r4354 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
          have b4355 := hb (x 13 1)
          have b4356 := hb (x 13 13)
          clear * - r4354 b4355 b4356 d4348
          omega
        have d4357 : (x 14 14).toNat = 0 := by
          have r4358 : (x 14 14).toNat + (x 13 1).toNat = 1 := by have q := hd14 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4359 := hb (x 13 1)
          have b4360 := hb (x 14 14)
          clear * - r4358 b4359 b4360 d4353
          omega
        have d4361 : (x 14 1 && x 14 14).toNat = 0 := by
          have r4362 := hand2 (x 14 1) (x 14 14)
          have b4363 := hb (x 14 14)
          have b4364 := hb (x 14 1 && x 14 14)
          clear * - r4362 b4363 b4364 d4357
          omega
        have d4365 : (x 14 3 && x 14 14).toNat = 0 := by
          have r4366 := hand2 (x 14 3) (x 14 14)
          have b4367 := hb (x 14 14)
          have b4368 := hb (x 14 3 && x 14 14)
          clear * - r4366 b4367 b4368 d4357
          omega
        have d4369 : (x 14 2).toNat = 0 := by
          have r4370 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
          have b4371 := hb (x 14 2)
          have b4372 := hb (x 14 14)
          clear * - r4370 b4371 b4372 d4357
          omega
        have d4373 : (x 12 2).toNat = 0 := by
          have r4374 : (x 12 2).toNat ≤ (x 12 14).toNat := himp _ _ (hp2 12)
          have b4375 := hb (x 12 2)
          have b4376 := hb (x 12 14)
          clear * - r4374 b4375 b4376 d4340
          omega
        have d4377 : (x 10 2).toNat = 0 := by
          have r4378 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
          have b4379 := hb (x 10 2)
          have b4380 := hb (x 10 14)
          clear * - r4378 b4379 b4380 d4323
          omega
        have d4381 : (x 12 13).toNat = 1 := by
          have r4382 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4383 := hb (x 10 2)
          have b4384 := hb (x 12 13)
          have b4385 := hb (x 11 1 && x 11 14)
          clear * - r4382 b4383 b4384 b4385 d4298 d4377
          omega
        have d4386 : (x 12 1).toNat = 1 := by
          have r4387 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
          have b4388 := hb (x 12 1)
          have b4389 := hb (x 12 13)
          clear * - r4387 b4388 b4389 d4381
          omega
        have d4390 : (x 13 14).toNat = 0 := by
          have r4391 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4392 := hb (x 12 1)
          have b4393 := hb (x 13 14)
          clear * - r4391 b4392 b4393 d4386
          omega
        have d4394 : (x 13 1 && x 13 14).toNat = 0 := by
          have r4395 := hand2 (x 13 1) (x 13 14)
          have b4396 := hb (x 13 14)
          have b4397 := hb (x 13 1 && x 13 14)
          clear * - r4395 b4396 b4397 d4390
          omega
        have d4398 : (x 14 13).toNat = 1 := by
          have r4399 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4400 := hb (x 12 2)
          have b4401 := hb (x 14 13)
          have b4402 := hb (x 13 1 && x 13 14)
          clear * - r4399 b4400 b4401 b4402 d4394 d4373
          omega
        have d4403 : (x 14 1).toNat = 1 := by
          have r4404 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
          have b4405 := hb (x 14 1)
          have b4406 := hb (x 14 13)
          clear * - r4404 b4405 b4406 d4398
          omega
        have d4407 : (x 15 14).toNat = 0 := by
          have r4408 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4409 := hb (x 14 1)
          have b4410 := hb (x 15 14)
          clear * - r4408 b4409 b4410 d4403
          omega
        have d4411 : (x 15 1 && x 15 14).toNat = 0 := by
          have r4412 := hand2 (x 15 1) (x 15 14)
          have b4413 := hb (x 15 14)
          have b4414 := hb (x 15 1 && x 15 14)
          clear * - r4412 b4413 b4414 d4407
          omega
        have d4415 : (x 16 13).toNat = 1 := by
          have r4416 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4417 := hb (x 14 2)
          have b4418 := hb (x 16 13)
          have b4419 := hb (x 15 1 && x 15 14)
          clear * - r4416 b4417 b4418 b4419 d4411 d4369
          omega
        have d4420 : (x 16 1).toNat = 1 := by
          have r4421 : (x 16 13).toNat ≤ (x 16 1).toNat := himp _ _ (hp13 16)
          have b4422 := hb (x 16 1)
          have b4423 := hb (x 16 13)
          clear * - r4421 b4422 b4423 d4415
          omega
        have d4424 : (x 17 14).toNat = 0 := by
          have r4425 : (x 17 14).toNat + (x 16 1).toNat = 1 := by have q := hd14 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4426 := hb (x 16 1)
          have b4427 := hb (x 17 14)
          clear * - r4425 b4426 b4427 d4420
          omega
        have d4428 : (x 17 2).toNat = 0 := by
          have r4429 : (x 17 2).toNat ≤ (x 17 14).toNat := himp _ _ (hp2 17)
          have b4430 := hb (x 17 2)
          have b4431 := hb (x 17 14)
          clear * - r4429 b4430 b4431 d4424
          omega
        have d4432 : (x 15 2).toNat = 0 := by
          have r4433 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
          have b4434 := hb (x 15 2)
          have b4435 := hb (x 15 14)
          clear * - r4433 b4434 b4435 d4407
          omega
        have d4436 : (x 15 2 && x 15 13).toNat = 0 := by
          have r4437 := hand1 (x 15 2) (x 15 13)
          have b4438 := hb (x 15 2)
          have b4439 := hb (x 15 2 && x 15 13)
          clear * - r4437 b4438 b4439 d4432
          omega
        have d4440 : (x 13 2).toNat = 0 := by
          have r4441 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
          have b4442 := hb (x 13 2)
          have b4443 := hb (x 13 14)
          clear * - r4441 b4442 b4443 d4390
          omega
        have d4444 : (x 15 13).toNat = 1 := by
          have r4445 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4446 := hb (x 13 2)
          have b4447 := hb (x 15 13)
          have b4448 := hb (x 14 1 && x 14 14)
          clear * - r4445 b4446 b4447 b4448 d4361 d4440
          omega
        have d4449 : (x 15 1).toNat = 1 := by
          have r4450 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
          have b4451 := hb (x 15 1)
          have b4452 := hb (x 15 13)
          clear * - r4450 b4451 b4452 d4444
          omega
        have d4453 : (x 16 14).toNat = 0 := by
          have r4454 : (x 16 14).toNat + (x 15 1).toNat = 1 := by have q := hd14 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4455 := hb (x 15 1)
          have b4456 := hb (x 16 14)
          clear * - r4454 b4455 b4456 d4449
          omega
        have d4457 : (x 16 1 && x 16 14).toNat = 0 := by
          have r4458 := hand2 (x 16 1) (x 16 14)
          have b4459 := hb (x 16 14)
          have b4460 := hb (x 16 1 && x 16 14)
          clear * - r4458 b4459 b4460 d4453
          omega
        have d4461 : (x 17 13).toNat = 1 := by
          have r4462 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := by have q := hcov13 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4463 := hb (x 15 2)
          have b4464 := hb (x 17 13)
          have b4465 := hb (x 16 1 && x 16 14)
          clear * - r4462 b4463 b4464 b4465 d4457 d4432
          omega
        have d4466 : (x 17 1).toNat = 1 := by
          have r4467 : (x 17 13).toNat ≤ (x 17 1).toNat := himp _ _ (hp13 17)
          have b4468 := hb (x 17 1)
          have b4469 := hb (x 17 13)
          clear * - r4467 b4468 b4469 d4461
          omega
        have d4470 : (x 18 14).toNat = 0 := by
          have r4471 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4472 := hb (x 17 1)
          have b4473 := hb (x 18 14)
          clear * - r4471 b4472 b4473 d4466
          omega
        have d4474 : (x 18 1 && x 18 14).toNat = 0 := by
          have r4475 := hand2 (x 18 1) (x 18 14)
          have b4476 := hb (x 18 14)
          have b4477 := hb (x 18 1 && x 18 14)
          clear * - r4475 b4476 b4477 d4470
          omega
        have d4478 : (x 19 13).toNat = 1 := by
          have r4479 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4480 := hb (x 17 2)
          have b4481 := hb (x 19 13)
          have b4482 := hb (x 18 1 && x 18 14)
          clear * - r4479 b4480 b4481 b4482 d4474 d4428
          omega
        have d4483 : (x 18 2).toNat = 0 := by
          have r4484 : (x 18 2).toNat ≤ (x 18 14).toNat := himp _ _ (hp2 18)
          have b4485 := hb (x 18 2)
          have b4486 := hb (x 18 14)
          clear * - r4484 b4485 b4486 d4470
          omega
        have d4487 : (x 20 12).toNat = 0 := by
          have r4488 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4489 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
          have e4490 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
          have b4491 := hb (x 17 3)
          have b4492 := hb (x 18 2)
          have b4493 := hb (x 19 13)
          have b4494 := hb (x 20 12)
          clear * - r4488 e4489 e4490 b4491 b4492 b4493 b4494 d4478 d4483
          omega
        have d4495 : (x 17 3).toNat = 0 := by
          have r4496 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4497 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
          have e4498 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
          have b4499 := hb (x 17 3)
          have b4500 := hb (x 18 2)
          have b4501 := hb (x 19 13)
          have b4502 := hb (x 20 12)
          clear * - r4496 e4497 e4498 b4499 b4500 b4501 b4502 d4487 d4478 d4483
          omega
        have d4503 : (x 17 11).toNat = 0 := by
          have r4504 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
          have b4505 := hb (x 17 3)
          have b4506 := hb (x 17 11)
          clear * - r4504 b4505 b4506 d4495
          omega
        have d4507 : (x 16 12).toNat = 0 := by
          have r4508 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4509 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
          have e4510 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
          have b4511 := hb (x 13 3)
          have b4512 := hb (x 14 2)
          have b4513 := hb (x 15 13)
          have b4514 := hb (x 16 12)
          clear * - r4508 e4509 e4510 b4511 b4512 b4513 b4514 d4444 d4369
          omega
        have d4515 : (x 16 1 && x 16 12).toNat = 0 := by
          have r4516 := hand2 (x 16 1) (x 16 12)
          have b4517 := hb (x 16 12)
          have b4518 := hb (x 16 1 && x 16 12)
          clear * - r4516 b4517 b4518 d4507
          omega
        have d4519 : (x 13 12).toNat = 0 := by
          have r4520 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4521 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
          have e4522 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
          have b4523 := hb (x 10 3)
          have b4524 := hb (x 11 2)
          have b4525 := hb (x 12 13)
          have b4526 := hb (x 13 12)
          clear * - r4520 e4521 e4522 b4523 b4524 b4525 b4526 d4381 d4302
          omega
        have d4527 : (x 13 4).toNat = 0 := by
          have r4528 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
          have b4529 := hb (x 13 4)
          have b4530 := hb (x 13 12)
          clear * - r4528 b4529 b4530 d4519
          omega
        have r4531 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b4532 := hb (x 13 4)
        have b4533 := hb (x 17 11)
        have b4534 := hb (x 16 1 && x 16 12)
        have b4535 := hb (x 15 2 && x 15 13)
        have b4536 := hb (x 14 3 && x 14 14)
        linarith only [r4531, b4532, b4533, b4534, b4535, b4536, d4503, d4515, d4436, d4365, d4527]
    · have f4537 : (x 0 13).toNat = 1 := by rw [h3616]; rfl
      have d4538 : (x 1 12).toNat = 0 := by
        have r4539 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e4540 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e4541 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b4542 := hb (x (-2) 3)
        have b4543 := hb (x (-1) 2)
        have b4544 := hb (x 0 13)
        have b4545 := hb (x 1 12)
        clear * - r4539 e4540 e4541 b4542 b4543 b4544 b4545 f4537
        omega
      have d4546 : (x (-1) 2).toNat = 0 := by
        have r4547 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e4548 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e4549 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b4550 := hb (x (-2) 3)
        have b4551 := hb (x (-1) 2)
        have b4552 := hb (x 0 13)
        have b4553 := hb (x 1 12)
        clear * - r4547 e4548 e4549 b4550 b4551 b4552 b4553 d4538 f4537
        omega
      have d4554 : (x (-1) 2 && x (-1) 12).toNat = 0 := by
        have r4555 := hand1 (x (-1) 2) (x (-1) 12)
        have b4556 := hb (x (-1) 2)
        have b4557 := hb (x (-1) 2 && x (-1) 12)
        clear * - r4555 b4556 b4557 d4546
        omega
      have d4558 : (x (-2) 3).toNat = 0 := by
        have r4559 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e4560 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e4561 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b4562 := hb (x (-2) 3)
        have b4563 := hb (x (-1) 2)
        have b4564 := hb (x 0 13)
        have b4565 := hb (x 1 12)
        clear * - r4559 e4560 e4561 b4562 b4563 b4564 b4565 d4538 f4537 d4546
        omega
      have d4566 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
        have r4567 := hand1 (x (-2) 3) (x (-2) 13)
        have b4568 := hb (x (-2) 3)
        have b4569 := hb (x (-2) 3 && x (-2) 13)
        clear * - r4567 b4568 b4569 d4558
        omega
      have r4570 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4571 := hb (x (-4) 5)
      have b4572 := hb (x 1 10)
      have b4573 := hb (x 0 1 && x 0 11)
      have b4574 := hb (x (-1) 2 && x (-1) 12)
      have b4575 := hb (x (-2) 3 && x (-2) 13)
      have b4576 := hb (x (-3) 4 && x (-3) 14)
      linarith only [r4570, b4571, b4572, b4573, b4574, b4575, b4576, g14, g32, d4554, d4566, g33, g1]
  · have f4577 : (x 0 7).toNat = 1 := by rw [h3614]; rfl
    have d4578 : (x 7 8).toNat = 0 := by
      have r4579 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e4580 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e4581 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e4582 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e4583 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e4584 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e4585 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b4586 := hb (x 0 7)
      have b4587 := hb (x 1 6)
      have b4588 := hb (x 2 5)
      have b4589 := hb (x 3 4)
      have b4590 := hb (x 4 11)
      have b4591 := hb (x 5 10)
      have b4592 := hb (x 6 9)
      have b4593 := hb (x 7 8)
      clear * - r4579 e4580 e4581 e4582 e4583 e4584 e4585 b4586 b4587 b4588 b4589 b4590 b4591 b4592 b4593 g18 g12 f4577
      omega
    have d4594 : (x 7 1 && x 7 8).toNat = 0 := by
      have r4595 := hand2 (x 7 1) (x 7 8)
      have b4596 := hb (x 7 8)
      have b4597 := hb (x 7 1 && x 7 8)
      clear * - r4595 b4596 b4597 d4578
      omega
    have d4598 : (x 7 8 && x 7 14).toNat = 0 := by
      have r4599 := hand1 (x 7 8) (x 7 14)
      have b4600 := hb (x 7 8)
      have b4601 := hb (x 7 8 && x 7 14)
      clear * - r4599 b4600 b4601 d4578
      omega
    have d4602 : (x 7 8 && x 7 13).toNat = 0 := by
      have r4603 := hand1 (x 7 8) (x 7 13)
      have b4604 := hb (x 7 8)
      have b4605 := hb (x 7 8 && x 7 13)
      clear * - r4603 b4604 b4605 d4578
      omega
    have d4606 : (x 6 9).toNat = 0 := by
      have r4607 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e4608 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e4609 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e4610 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e4611 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e4612 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e4613 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b4614 := hb (x 0 7)
      have b4615 := hb (x 1 6)
      have b4616 := hb (x 2 5)
      have b4617 := hb (x 3 4)
      have b4618 := hb (x 4 11)
      have b4619 := hb (x 5 10)
      have b4620 := hb (x 6 9)
      have b4621 := hb (x 7 8)
      clear * - r4607 e4608 e4609 e4610 e4611 e4612 e4613 b4614 b4615 b4616 b4617 b4618 b4619 b4620 b4621 d4578 g18 g12 f4577
      omega
    have d4622 : (x 6 2 && x 6 9).toNat = 0 := by
      have r4623 := hand2 (x 6 2) (x 6 9)
      have b4624 := hb (x 6 9)
      have b4625 := hb (x 6 2 && x 6 9)
      clear * - r4623 b4624 b4625 d4606
      omega
    have d4626 : (x 6 9 && x 6 14).toNat = 0 := by
      have r4627 := hand1 (x 6 9) (x 6 14)
      have b4628 := hb (x 6 9)
      have b4629 := hb (x 6 9 && x 6 14)
      clear * - r4627 b4628 b4629 d4606
      omega
    have d4630 : (x 5 10).toNat = 0 := by
      have r4631 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e4632 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e4633 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e4634 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e4635 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e4636 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e4637 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b4638 := hb (x 0 7)
      have b4639 := hb (x 1 6)
      have b4640 := hb (x 2 5)
      have b4641 := hb (x 3 4)
      have b4642 := hb (x 4 11)
      have b4643 := hb (x 5 10)
      have b4644 := hb (x 6 9)
      have b4645 := hb (x 7 8)
      clear * - r4631 e4632 e4633 e4634 e4635 e4636 e4637 b4638 b4639 b4640 b4641 b4642 b4643 b4644 b4645 d4578 d4606 g18 g12 f4577
      omega
    have d4646 : (x 5 3 && x 5 10).toNat = 0 := by
      have r4647 := hand2 (x 5 3) (x 5 10)
      have b4648 := hb (x 5 10)
      have b4649 := hb (x 5 3 && x 5 10)
      clear * - r4647 b4648 b4649 d4630
      omega
    have d4650 : (x 4 11).toNat = 0 := by
      have r4651 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e4652 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e4653 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e4654 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e4655 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e4656 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e4657 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b4658 := hb (x 0 7)
      have b4659 := hb (x 1 6)
      have b4660 := hb (x 2 5)
      have b4661 := hb (x 3 4)
      have b4662 := hb (x 4 11)
      have b4663 := hb (x 5 10)
      have b4664 := hb (x 6 9)
      have b4665 := hb (x 7 8)
      clear * - r4651 e4652 e4653 e4654 e4655 e4656 e4657 b4658 b4659 b4660 b4661 b4662 b4663 b4664 b4665 d4578 d4606 d4630 g18 g12 f4577
      omega
    have d4666 : (x 4 1 && x 4 11).toNat = 0 := by
      have r4667 := hand2 (x 4 1) (x 4 11)
      have b4668 := hb (x 4 11)
      have b4669 := hb (x 4 1 && x 4 11)
      clear * - r4667 b4668 b4669 d4650
      omega
    have d4670 : (x 2 3 && x 2 13).toNat = 1 := by
      have r4671 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4672 := hb (x 0 5)
      have b4673 := hb (x 5 10)
      have b4674 := hb (x 4 1 && x 4 11)
      have b4675 := hb (x 3 2 && x 3 12)
      have b4676 := hb (x 2 3 && x 2 13)
      have b4677 := hb (x 1 4 && x 1 14)
      clear * - r4671 b4672 b4673 b4674 b4675 b4676 b4677 d4630 d4666 g35 g36 g6
      omega
    have d4678 : (x 2 3).toNat = 1 := by
      have r4679 := hand1 (x 2 3) (x 2 13)
      have b4680 := hb (x 2 3)
      have b4681 := hb (x 2 3 && x 2 13)
      clear * - r4679 b4680 b4681 d4670
      omega
    have d4682 : (x 5 12).toNat = 0 := by
      have r4683 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e4684 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e4685 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b4686 := hb (x 2 3)
      have b4687 := hb (x 3 2)
      have b4688 := hb (x 4 13)
      have b4689 := hb (x 5 12)
      clear * - r4683 e4684 e4685 b4686 b4687 b4688 b4689 g17 d4678
      omega
    have d4690 : (x 5 1 && x 5 12).toNat = 0 := by
      have r4691 := hand2 (x 5 1) (x 5 12)
      have b4692 := hb (x 5 12)
      have b4693 := hb (x 5 1 && x 5 12)
      clear * - r4691 b4692 b4693 d4682
      omega
    have d4694 : (x 5 2 && x 5 12).toNat = 0 := by
      have r4695 := hand2 (x 5 2) (x 5 12)
      have b4696 := hb (x 5 12)
      have b4697 := hb (x 5 2 && x 5 12)
      clear * - r4695 b4696 b4697 d4682
      omega
    have d4698 : (x 5 4).toNat = 0 := by
      have r4699 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
      have b4700 := hb (x 5 4)
      have b4701 := hb (x 5 12)
      clear * - r4699 b4700 b4701 d4682
      omega
    have d4702 : (x 5 4 && x 5 8).toNat = 0 := by
      have r4703 := hand1 (x 5 4) (x 5 8)
      have b4704 := hb (x 5 4)
      have b4705 := hb (x 5 4 && x 5 8)
      clear * - r4703 b4704 b4705 d4698
      omega
    have d4706 : (x 4 13).toNat = 0 := by
      have r4707 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e4708 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e4709 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b4710 := hb (x 2 3)
      have b4711 := hb (x 3 2)
      have b4712 := hb (x 4 13)
      have b4713 := hb (x 5 12)
      clear * - r4707 e4708 e4709 b4710 b4711 b4712 b4713 d4682 g17 d4678
      omega
    have d4714 : (x 4 2 && x 4 13).toNat = 0 := by
      have r4715 := hand2 (x 4 2) (x 4 13)
      have b4716 := hb (x 4 13)
      have b4717 := hb (x 4 2 && x 4 13)
      clear * - r4715 b4716 b4717 d4706
      omega
    have d4718 : (x 6 11).toNat = 1 := by
      have r4719 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := by have q := hcov11 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4720 := hb (x 2 4)
      have b4721 := hb (x 6 11)
      have b4722 := hb (x 5 1 && x 5 12)
      have b4723 := hb (x 4 2 && x 4 13)
      have b4724 := hb (x 3 3 && x 3 14)
      clear * - r4719 b4720 b4721 b4722 b4723 b4724 d4690 d4714 g38 d3550
      omega
    have d4725 : (x 6 3).toNat = 1 := by
      have r4726 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
      have b4727 := hb (x 6 3)
      have b4728 := hb (x 6 11)
      clear * - r4726 b4727 b4728 d4718
      omega
    have d4729 : (x 9 12).toNat = 0 := by
      have r4730 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e4731 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
      have e4732 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
      have b4733 := hb (x 6 3)
      have b4734 := hb (x 7 2)
      have b4735 := hb (x 8 13)
      have b4736 := hb (x 9 12)
      clear * - r4730 e4731 e4732 b4733 b4734 b4735 b4736 d4725
      omega
    have d4737 : (x 9 2 && x 9 12).toNat = 0 := by
      have r4738 := hand2 (x 9 2) (x 9 12)
      have b4739 := hb (x 9 12)
      have b4740 := hb (x 9 2 && x 9 12)
      clear * - r4738 b4739 b4740 d4729
      omega
    have d4741 : (x 9 3 && x 9 12).toNat = 0 := by
      have r4742 := hand2 (x 9 3) (x 9 12)
      have b4743 := hb (x 9 12)
      have b4744 := hb (x 9 3 && x 9 12)
      clear * - r4742 b4743 b4744 d4729
      omega
    have d4745 : (x 9 5 && x 9 12).toNat = 0 := by
      have r4746 := hand2 (x 9 5) (x 9 12)
      have b4747 := hb (x 9 12)
      have b4748 := hb (x 9 5 && x 9 12)
      clear * - r4746 b4747 b4748 d4729
      omega
    have d4749 : (x 9 6 && x 9 12).toNat = 0 := by
      have r4750 := hand2 (x 9 6) (x 9 12)
      have b4751 := hb (x 9 12)
      have b4752 := hb (x 9 6 && x 9 12)
      clear * - r4750 b4751 b4752 d4729
      omega
    have d4753 : (x 9 4).toNat = 0 := by
      have r4754 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
      have b4755 := hb (x 9 4)
      have b4756 := hb (x 9 12)
      clear * - r4754 b4755 b4756 d4729
      omega
    have d4757 : (x 9 4 && x 9 13).toNat = 0 := by
      have r4758 := hand1 (x 9 4) (x 9 13)
      have b4759 := hb (x 9 4)
      have b4760 := hb (x 9 4 && x 9 13)
      clear * - r4758 b4759 b4760 d4753
      omega
    have d4761 : (x 8 13).toNat = 0 := by
      have r4762 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e4763 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
      have e4764 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
      have b4765 := hb (x 6 3)
      have b4766 := hb (x 7 2)
      have b4767 := hb (x 8 13)
      have b4768 := hb (x 9 12)
      clear * - r4762 e4763 e4764 b4765 b4766 b4767 b4768 d4729 d4725
      omega
    have d4769 : (x 8 3 && x 8 13).toNat = 0 := by
      have r4770 := hand2 (x 8 3) (x 8 13)
      have b4771 := hb (x 8 13)
      have b4772 := hb (x 8 3 && x 8 13)
      clear * - r4770 b4771 b4772 d4761
      omega
    have d4773 : (x 8 4 && x 8 13).toNat = 0 := by
      have r4774 := hand2 (x 8 4) (x 8 13)
      have b4775 := hb (x 8 13)
      have b4776 := hb (x 8 4 && x 8 13)
      clear * - r4774 b4775 b4776 d4761
      omega
    have d4777 : (x 8 6 && x 8 13).toNat = 0 := by
      have r4778 := hand2 (x 8 6) (x 8 13)
      have b4779 := hb (x 8 13)
      have b4780 := hb (x 8 6 && x 8 13)
      clear * - r4778 b4779 b4780 d4761
      omega
    have d4781 : (x 8 7 && x 8 13).toNat = 0 := by
      have r4782 := hand2 (x 8 7) (x 8 13)
      have b4783 := hb (x 8 13)
      have b4784 := hb (x 8 7 && x 8 13)
      clear * - r4782 b4783 b4784 d4761
      omega
    have d4785 : (x 8 5).toNat = 0 := by
      have r4786 : (x 8 5).toNat ≤ (x 8 13).toNat := himp _ _ (hp5 8)
      have b4787 := hb (x 8 5)
      have b4788 := hb (x 8 13)
      clear * - r4786 b4787 b4788 d4761
      omega
    have d4789 : (x 8 5 && x 8 14).toNat = 0 := by
      have r4790 := hand1 (x 8 5) (x 8 14)
      have b4791 := hb (x 8 5)
      have b4792 := hb (x 8 5 && x 8 14)
      clear * - r4790 b4791 b4792 d4785
      omega
    have d4793 : (x 7 2).toNat = 0 := by
      have r4794 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e4795 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
      have e4796 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
      have b4797 := hb (x 6 3)
      have b4798 := hb (x 7 2)
      have b4799 := hb (x 8 13)
      have b4800 := hb (x 9 12)
      clear * - r4794 e4795 e4796 b4797 b4798 b4799 b4800 d4729 d4761 d4725
      omega
    have d4801 : (x 7 2 && x 7 6).toNat = 0 := by
      have r4802 := hand1 (x 7 2) (x 7 6)
      have b4803 := hb (x 7 2)
      have b4804 := hb (x 7 2 && x 7 6)
      clear * - r4802 b4803 b4804 d4793
      omega
    have d4805 : (x 7 10).toNat = 0 := by
      have r4806 : (x 7 10).toNat ≤ (x 7 2).toNat := himp _ _ (hp10 7)
      have b4807 := hb (x 7 2)
      have b4808 := hb (x 7 10)
      clear * - r4806 b4807 b4808 d4793
      omega
    have d4809 : (x 9 8).toNat = 0 := by
      have r4810 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e4811 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
      have e4812 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
      have e4813 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
      have e4814 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
      have e4815 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
      have e4816 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
      have b4817 := hb (x 2 7)
      have b4818 := hb (x 3 6)
      have b4819 := hb (x 4 5)
      have b4820 := hb (x 5 4)
      have b4821 := hb (x 6 11)
      have b4822 := hb (x 7 10)
      have b4823 := hb (x 8 9)
      have b4824 := hb (x 9 8)
      clear * - r4810 e4811 e4812 e4813 e4814 e4815 e4816 b4817 b4818 b4819 b4820 b4821 b4822 b4823 b4824 d4805 d4718 d4698 g19
      omega
    have d4825 : (x 8 9).toNat = 0 := by
      have r4826 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e4827 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
      have e4828 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
      have e4829 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
      have e4830 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
      have e4831 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
      have e4832 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
      have b4833 := hb (x 2 7)
      have b4834 := hb (x 3 6)
      have b4835 := hb (x 4 5)
      have b4836 := hb (x 5 4)
      have b4837 := hb (x 6 11)
      have b4838 := hb (x 7 10)
      have b4839 := hb (x 8 9)
      have b4840 := hb (x 9 8)
      clear * - r4826 e4827 e4828 e4829 e4830 e4831 e4832 b4833 b4834 b4835 b4836 b4837 b4838 b4839 b4840 d4809 d4805 d4718 d4698 g19
      omega
    have d4841 : (x 4 5).toNat = 0 := by
      have r4842 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e4843 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
      have e4844 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
      have e4845 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
      have e4846 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
      have e4847 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
      have e4848 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
      have b4849 := hb (x 2 7)
      have b4850 := hb (x 3 6)
      have b4851 := hb (x 4 5)
      have b4852 := hb (x 5 4)
      have b4853 := hb (x 6 11)
      have b4854 := hb (x 7 10)
      have b4855 := hb (x 8 9)
      have b4856 := hb (x 9 8)
      clear * - r4842 e4843 e4844 e4845 e4846 e4847 e4848 b4849 b4850 b4851 b4852 b4853 b4854 b4855 b4856 d4809 d4825 d4805 d4718 d4698 g19
      omega
    have d4857 : (x 4 5 && x 4 9).toNat = 0 := by
      have r4858 := hand1 (x 4 5) (x 4 9)
      have b4859 := hb (x 4 5)
      have b4860 := hb (x 4 5 && x 4 9)
      clear * - r4858 b4859 b4860 d4841
      omega
    have d4861 : (x 2 7).toNat = 0 := by
      have r4862 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e4863 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
      have e4864 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
      have e4865 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
      have e4866 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
      have e4867 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
      have e4868 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
      have b4869 := hb (x 2 7)
      have b4870 := hb (x 3 6)
      have b4871 := hb (x 4 5)
      have b4872 := hb (x 5 4)
      have b4873 := hb (x 6 11)
      have b4874 := hb (x 7 10)
      have b4875 := hb (x 8 9)
      have b4876 := hb (x 9 8)
      clear * - r4862 e4863 e4864 e4865 e4866 e4867 e4868 b4869 b4870 b4871 b4872 b4873 b4874 b4875 b4876 d4809 d4825 d4805 d4718 d4698 d4841 g19
      omega
    have d4877 : (x 2 7 && x 2 11).toNat = 0 := by
      have r4878 := hand1 (x 2 7) (x 2 11)
      have b4879 := hb (x 2 7)
      have b4880 := hb (x 2 7 && x 2 11)
      clear * - r4878 b4879 b4880 d4861
      omega
    have d4881 : (x 4 3 && x 4 13).toNat = 0 := by
      have r4882 := hand2 (x 4 3) (x 4 13)
      have b4883 := hb (x 4 13)
      have b4884 := hb (x 4 3 && x 4 13)
      clear * - r4882 b4883 b4884 d4706
      omega
    have d4885 : (x 2 2).toNat = 1 := by
      have r4886 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4887 := hb (x 2 2)
      have b4888 := hb (x 4 13)
      have b4889 := hb (x 3 1 && x 3 14)
      clear * - r4886 b4887 b4888 b4889 d4706 g39
      omega
    have d4890 : (x 2 14).toNat = 1 := by
      have r4891 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
      have b4892 := hb (x 2 2)
      have b4893 := hb (x 2 14)
      clear * - r4891 b4892 b4893 d4885
      omega
    have d4894 : (x 1 1).toNat = 0 := by
      have r4895 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4896 := hb (x 1 1)
      have b4897 := hb (x 2 14)
      clear * - r4895 b4896 b4897 d4890
      omega
    have d4898 : (x 1 13).toNat = 0 := by
      have r4899 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
      have b4900 := hb (x 1 1)
      have b4901 := hb (x 1 13)
      clear * - r4899 b4900 b4901 d4894
      omega
    have d4902 : (x 1 3 && x 1 13).toNat = 0 := by
      have r4903 := hand2 (x 1 3) (x 1 13)
      have b4904 := hb (x 1 13)
      have b4905 := hb (x 1 3 && x 1 13)
      clear * - r4903 b4904 b4905 d4898
      omega
    have d4906 : (x 2 2 && x 2 12).toNat = 1 := by
      have r4907 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4908 := hb (x (-1) 5)
      have b4909 := hb (x 4 10)
      have b4910 := hb (x 3 1 && x 3 11)
      have b4911 := hb (x 2 2 && x 2 12)
      have b4912 := hb (x 1 3 && x 1 13)
      have b4913 := hb (x 0 4 && x 0 14)
      clear * - r4907 b4908 b4909 b4910 b4911 b4912 b4913 d3494 d3538 d4902 g34 d3438
      omega
    have d4914 : (x 2 12).toNat = 1 := by
      have r4915 := hand2 (x 2 2) (x 2 12)
      have b4916 := hb (x 2 12)
      have b4917 := hb (x 2 2 && x 2 12)
      clear * - r4915 b4916 b4917 d4906
      omega
    have d4918 : (x 1 7 && x 1 13).toNat = 0 := by
      have r4919 := hand2 (x 1 7) (x 1 13)
      have b4920 := hb (x 1 13)
      have b4921 := hb (x 1 7 && x 1 13)
      clear * - r4919 b4920 b4921 d4898
      omega
    have d4922 : (x (-1) 3).toNat = 0 := by
      have r4923 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e4924 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e4925 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b4926 := hb (x (-1) 3)
      have b4927 := hb (x 0 2)
      have b4928 := hb (x 1 13)
      have b4929 := hb (x 2 12)
      clear * - r4923 e4924 e4925 b4926 b4927 b4928 b4929 d4914 d4898 g5
      omega
    have d4930 : (x (-1) 11).toNat = 0 := by
      have r4931 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
      have b4932 := hb (x (-1) 3)
      have b4933 := hb (x (-1) 11)
      clear * - r4931 b4932 b4933 d4922
      omega
    have d4934 : (x (-1) 2 && x (-1) 11).toNat = 0 := by
      have r4935 := hand2 (x (-1) 2) (x (-1) 11)
      have b4936 := hb (x (-1) 11)
      have b4937 := hb (x (-1) 2 && x (-1) 11)
      clear * - r4935 b4936 b4937 d4930
      omega
    have d4938 : (x 1 9).toNat = 0 := by
      have r4939 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
      have b4940 := hb (x 1 1)
      have b4941 := hb (x 1 9)
      clear * - r4939 b4940 b4941 d4894
      omega
    have d4942 : (x (-2) 3 && x (-2) 12).toNat = 1 := by
      have r4943 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b4944 := hb (x (-5) 6)
      have b4945 := hb (x 1 9)
      have b4946 := hb (x 0 1 && x 0 10)
      have b4947 := hb (x (-1) 2 && x (-1) 11)
      have b4948 := hb (x (-2) 3 && x (-2) 12)
      have b4949 := hb (x (-3) 4 && x (-3) 13)
      have b4950 := hb (x (-4) 5 && x (-4) 14)
      clear * - r4943 b4944 b4945 b4946 b4947 b4948 b4949 b4950 d4938 g27 d4934 g28 g29 g0
      omega
    have d4951 : (x (-2) 3).toNat = 1 := by
      have r4952 := hand1 (x (-2) 3) (x (-2) 12)
      have b4953 := hb (x (-2) 3)
      have b4954 := hb (x (-2) 3 && x (-2) 12)
      clear * - r4952 b4953 b4954 d4942
      omega
    have d4955 : (x 1 12).toNat = 0 := by
      have r4956 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e4957 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e4958 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b4959 := hb (x (-2) 3)
      have b4960 := hb (x (-1) 2)
      have b4961 := hb (x 0 13)
      have b4962 := hb (x 1 12)
      clear * - r4956 e4957 e4958 b4959 b4960 b4961 b4962 d4951
      omega
    have d4963 : (x 0 13).toNat = 0 := by
      have r4964 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e4965 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e4966 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b4967 := hb (x (-2) 3)
      have b4968 := hb (x (-1) 2)
      have b4969 := hb (x 0 13)
      have b4970 := hb (x 1 12)
      clear * - r4964 e4965 e4966 b4967 b4968 b4969 b4970 d4955 d4951
      omega
    have d4971 : (x 0 9 && x 0 13).toNat = 0 := by
      have r4972 := hand2 (x 0 9) (x 0 13)
      have b4973 := hb (x 0 13)
      have b4974 := hb (x 0 9 && x 0 13)
      clear * - r4972 b4973 b4974 d4963
      omega
    have d4975 : (x 4 12).toNat = 0 := by
      have r4976 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e4977 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e4978 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b4979 := hb (x 1 3)
      have b4980 := hb (x 2 2)
      have b4981 := hb (x 3 13)
      have b4982 := hb (x 4 12)
      clear * - r4976 e4977 e4978 b4979 b4980 b4981 b4982 d4885
      omega
    have d4983 : (x 4 2 && x 4 12).toNat = 0 := by
      have r4984 := hand2 (x 4 2) (x 4 12)
      have b4985 := hb (x 4 12)
      have b4986 := hb (x 4 2 && x 4 12)
      clear * - r4984 b4985 b4986 d4975
      omega
    have d4987 : (x 4 4).toNat = 0 := by
      have r4988 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
      have b4989 := hb (x 4 4)
      have b4990 := hb (x 4 12)
      clear * - r4988 b4989 b4990 d4975
      omega
    have d4991 : (x 4 4 && x 4 11).toNat = 0 := by
      have r4992 := hand1 (x 4 4) (x 4 11)
      have b4993 := hb (x 4 4)
      have b4994 := hb (x 4 4 && x 4 11)
      clear * - r4992 b4993 b4994 d4987
      omega
    have d4995 : (x 3 13).toNat = 0 := by
      have r4996 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e4997 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e4998 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b4999 := hb (x 1 3)
      have b5000 := hb (x 2 2)
      have b5001 := hb (x 3 13)
      have b5002 := hb (x 4 12)
      clear * - r4996 e4997 e4998 b4999 b5000 b5001 b5002 d4975 d4885
      omega
    have d5003 : (x 3 3 && x 3 13).toNat = 0 := by
      have r5004 := hand2 (x 3 3) (x 3 13)
      have b5005 := hb (x 3 13)
      have b5006 := hb (x 3 3 && x 3 13)
      clear * - r5004 b5005 b5006 d4995
      omega
    have d5007 : (x 3 5).toNat = 0 := by
      have r5008 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
      have b5009 := hb (x 3 5)
      have b5010 := hb (x 3 13)
      clear * - r5008 b5009 b5010 d4995
      omega
    have d5011 : (x 2 5).toNat = 0 := by
      have r5012 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5013 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e5014 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e5015 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e5016 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e5017 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e5018 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b5019 := hb (x 0 7)
      have b5020 := hb (x 1 6)
      have b5021 := hb (x 2 5)
      have b5022 := hb (x 3 4)
      have b5023 := hb (x 4 11)
      have b5024 := hb (x 5 10)
      have b5025 := hb (x 6 9)
      have b5026 := hb (x 7 8)
      clear * - r5012 e5013 e5014 e5015 e5016 e5017 e5018 b5019 b5020 b5021 b5022 b5023 b5024 b5025 b5026 d4578 d4606 d4630 d4650 g18 g12 f4577
      omega
    have d5027 : (x 6 1 && x 6 11).toNat = 1 := by
      have r5028 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5029 := hb (x 2 5)
      have b5030 := hb (x 7 10)
      have b5031 := hb (x 6 1 && x 6 11)
      have b5032 := hb (x 5 2 && x 5 12)
      have b5033 := hb (x 4 3 && x 4 13)
      have b5034 := hb (x 3 4 && x 3 14)
      clear * - r5028 b5029 b5030 b5031 b5032 b5033 b5034 d4805 d4694 d4881 g37 d5011
      omega
    have d5035 : (x 6 1).toNat = 1 := by
      have r5036 := hand1 (x 6 1) (x 6 11)
      have b5037 := hb (x 6 1)
      have b5038 := hb (x 6 1 && x 6 11)
      clear * - r5036 b5037 b5038 d5027
      omega
    have d5039 : (x 7 14).toNat = 0 := by
      have r5040 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5041 := hb (x 6 1)
      have b5042 := hb (x 7 14)
      clear * - r5040 b5041 b5042 d5035
      omega
    have d5043 : (x 7 1 && x 7 14).toNat = 0 := by
      have r5044 := hand2 (x 7 1) (x 7 14)
      have b5045 := hb (x 7 14)
      have b5046 := hb (x 7 1 && x 7 14)
      clear * - r5044 b5045 b5046 d5039
      omega
    have d5047 : (x 6 2).toNat = 1 := by
      have r5048 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5049 := hb (x 6 2)
      have b5050 := hb (x 8 13)
      have b5051 := hb (x 7 1 && x 7 14)
      clear * - r5048 b5049 b5050 b5051 d4761 d5043
      omega
    have d5052 : (x 6 14).toNat = 1 := by
      have r5053 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
      have b5054 := hb (x 6 2)
      have b5055 := hb (x 6 14)
      clear * - r5053 b5054 b5055 d5047
      omega
    have d5056 : (x 5 1).toNat = 0 := by
      have r5057 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5058 := hb (x 5 1)
      have b5059 := hb (x 6 14)
      clear * - r5057 b5058 b5059 d5052
      omega
    have d5060 : (x 5 1 && x 5 11).toNat = 0 := by
      have r5061 := hand1 (x 5 1) (x 5 11)
      have b5062 := hb (x 5 1)
      have b5063 := hb (x 5 1 && x 5 11)
      clear * - r5061 b5062 b5063 d5056
      omega
    have d5064 : (x 6 10).toNat = 1 := by
      have r5065 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5066 := hb (x 1 5)
      have b5067 := hb (x 6 10)
      have b5068 := hb (x 5 1 && x 5 11)
      have b5069 := hb (x 4 2 && x 4 12)
      have b5070 := hb (x 3 3 && x 3 13)
      have b5071 := hb (x 2 4 && x 2 14)
      clear * - r5065 b5066 b5067 b5068 b5069 b5070 b5071 d5060 d4983 d5003 d3566 d3574
      omega
    have d5072 : (x 8 8).toNat = 0 := by
      have r5073 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5074 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e5075 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e5076 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e5077 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e5078 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e5079 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have b5080 := hb (x 1 7)
      have b5081 := hb (x 2 6)
      have b5082 := hb (x 3 5)
      have b5083 := hb (x 4 4)
      have b5084 := hb (x 5 11)
      have b5085 := hb (x 6 10)
      have b5086 := hb (x 7 9)
      have b5087 := hb (x 8 8)
      clear * - r5073 e5074 e5075 e5076 e5077 e5078 e5079 b5080 b5081 b5082 b5083 b5084 b5085 b5086 b5087 d5064 d4987 d5007
      omega
    have d5088 : (x 7 9).toNat = 0 := by
      have r5089 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5090 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e5091 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e5092 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e5093 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e5094 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e5095 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have b5096 := hb (x 1 7)
      have b5097 := hb (x 2 6)
      have b5098 := hb (x 3 5)
      have b5099 := hb (x 4 4)
      have b5100 := hb (x 5 11)
      have b5101 := hb (x 6 10)
      have b5102 := hb (x 7 9)
      have b5103 := hb (x 8 8)
      clear * - r5089 e5090 e5091 e5092 e5093 e5094 e5095 b5096 b5097 b5098 b5099 b5100 b5101 b5102 b5103 d5072 d5064 d4987 d5007
      omega
    have d5104 : (x 5 11).toNat = 0 := by
      have r5105 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5106 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e5107 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e5108 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e5109 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e5110 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e5111 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have b5112 := hb (x 1 7)
      have b5113 := hb (x 2 6)
      have b5114 := hb (x 3 5)
      have b5115 := hb (x 4 4)
      have b5116 := hb (x 5 11)
      have b5117 := hb (x 6 10)
      have b5118 := hb (x 7 9)
      have b5119 := hb (x 8 8)
      clear * - r5105 e5106 e5107 e5108 e5109 e5110 e5111 b5112 b5113 b5114 b5115 b5116 b5117 b5118 b5119 d5072 d5088 d5064 d4987 d5007
      omega
    have d5120 : (x 2 6).toNat = 0 := by
      have r5121 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5122 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e5123 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e5124 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e5125 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e5126 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e5127 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have b5128 := hb (x 1 7)
      have b5129 := hb (x 2 6)
      have b5130 := hb (x 3 5)
      have b5131 := hb (x 4 4)
      have b5132 := hb (x 5 11)
      have b5133 := hb (x 6 10)
      have b5134 := hb (x 7 9)
      have b5135 := hb (x 8 8)
      clear * - r5121 e5122 e5123 e5124 e5125 e5126 e5127 b5128 b5129 b5130 b5131 b5132 b5133 b5134 b5135 d5072 d5088 d5064 d5104 d4987 d5007
      omega
    have d5136 : (x 2 6 && x 2 13).toNat = 0 := by
      have r5137 := hand1 (x 2 6) (x 2 13)
      have b5138 := hb (x 2 6)
      have b5139 := hb (x 2 6 && x 2 13)
      clear * - r5137 b5138 b5139 d5120
      omega
    have d5140 : (x 2 6 && x 2 12).toNat = 0 := by
      have r5141 := hand1 (x 2 6) (x 2 12)
      have b5142 := hb (x 2 6)
      have b5143 := hb (x 2 6 && x 2 12)
      clear * - r5141 b5142 b5143 d5120
      omega
    have d5144 : (x 5 13).toNat = 0 := by
      have r5145 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
      have b5146 := hb (x 5 1)
      have b5147 := hb (x 5 13)
      clear * - r5145 b5146 b5147 d5056
      omega
    have d5148 : (x 5 5).toNat = 0 := by
      have r5149 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
      have b5150 := hb (x 5 5)
      have b5151 := hb (x 5 13)
      clear * - r5149 b5150 b5151 d5144
      omega
    have d5152 : (x 4 1 && x 4 14).toNat = 1 := by
      have r5153 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5154 := hb (x 3 2)
      have b5155 := hb (x 5 13)
      have b5156 := hb (x 4 1 && x 4 14)
      clear * - r5153 b5154 b5155 b5156 d5144 g17
      omega
    have d5157 : (x 4 14).toNat = 1 := by
      have r5158 := hand2 (x 4 1) (x 4 14)
      have b5159 := hb (x 4 14)
      have b5160 := hb (x 4 1 && x 4 14)
      clear * - r5158 b5159 b5160 d5152
      omega
    have d5161 : (x 4 1).toNat = 1 := by
      have r5162 := hand1 (x 4 1) (x 4 14)
      have b5163 := hb (x 4 1)
      have b5164 := hb (x 4 1 && x 4 14)
      clear * - r5162 b5163 b5164 d5152
      omega
    have d5165 : (x 5 14).toNat = 0 := by
      have r5166 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5167 := hb (x 4 1)
      have b5168 := hb (x 5 14)
      clear * - r5166 b5167 b5168 d5161
      omega
    have d5169 : (x 5 6).toNat = 0 := by
      have r5170 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
      have b5171 := hb (x 5 6)
      have b5172 := hb (x 5 14)
      clear * - r5170 b5171 b5172 d5165
      omega
    have d5173 : (x 5 2).toNat = 0 := by
      have r5174 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
      have b5175 := hb (x 5 2)
      have b5176 := hb (x 5 14)
      clear * - r5174 b5175 b5176 d5165
      omega
    have d5177 : (x 8 12).toNat = 0 := by
      have r5178 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5179 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e5180 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have b5181 := hb (x 5 3)
      have b5182 := hb (x 6 2)
      have b5183 := hb (x 7 13)
      have b5184 := hb (x 8 12)
      clear * - r5178 e5179 e5180 b5181 b5182 b5183 b5184 d5047
      omega
    have d5185 : (x 8 2 && x 8 12).toNat = 0 := by
      have r5186 := hand2 (x 8 2) (x 8 12)
      have b5187 := hb (x 8 12)
      have b5188 := hb (x 8 2 && x 8 12)
      clear * - r5186 b5187 b5188 d5177
      omega
    have d5189 : (x 8 7 && x 8 12).toNat = 0 := by
      have r5190 := hand2 (x 8 7) (x 8 12)
      have b5191 := hb (x 8 12)
      have b5192 := hb (x 8 7 && x 8 12)
      clear * - r5190 b5191 b5192 d5177
      omega
    have d5193 : (x 8 4).toNat = 0 := by
      have r5194 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
      have b5195 := hb (x 8 4)
      have b5196 := hb (x 8 12)
      clear * - r5194 b5195 b5196 d5177
      omega
    have d5197 : (x 8 4 && x 8 14).toNat = 0 := by
      have r5198 := hand1 (x 8 4) (x 8 14)
      have b5199 := hb (x 8 4)
      have b5200 := hb (x 8 4 && x 8 14)
      clear * - r5198 b5199 b5200 d5193
      omega
    have d5201 : (x 7 13).toNat = 0 := by
      have r5202 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5203 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e5204 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have b5205 := hb (x 5 3)
      have b5206 := hb (x 6 2)
      have b5207 := hb (x 7 13)
      have b5208 := hb (x 8 12)
      clear * - r5202 e5203 e5204 b5205 b5206 b5207 b5208 d5177 d5047
      omega
    have d5209 : (x 7 3 && x 7 13).toNat = 0 := by
      have r5210 := hand2 (x 7 3) (x 7 13)
      have b5211 := hb (x 7 13)
      have b5212 := hb (x 7 3 && x 7 13)
      clear * - r5210 b5211 b5212 d5201
      omega
    have d5213 : (x 7 5).toNat = 0 := by
      have r5214 : (x 7 5).toNat ≤ (x 7 13).toNat := himp _ _ (hp5 7)
      have b5215 := hb (x 7 5)
      have b5216 := hb (x 7 13)
      clear * - r5214 b5215 b5216 d5201
      omega
    have d5217 : (x 7 5 && x 7 14).toNat = 0 := by
      have r5218 := hand1 (x 7 5) (x 7 14)
      have b5219 := hb (x 7 5)
      have b5220 := hb (x 7 5 && x 7 14)
      clear * - r5218 b5219 b5220 d5213
      omega
    have d5221 : (x 7 4 && x 7 14).toNat = 0 := by
      have r5222 := hand2 (x 7 4) (x 7 14)
      have b5223 := hb (x 7 14)
      have b5224 := hb (x 7 4 && x 7 14)
      clear * - r5222 b5223 b5224 d5039
      omega
    have d5225 : (x 7 7 && x 7 14).toNat = 0 := by
      have r5226 := hand2 (x 7 7) (x 7 14)
      have b5227 := hb (x 7 14)
      have b5228 := hb (x 7 7 && x 7 14)
      clear * - r5226 b5227 b5228 d5039
      omega
    have d5229 : (x 7 6).toNat = 0 := by
      have r5230 : (x 7 6).toNat ≤ (x 7 14).toNat := himp _ _ (hp6 7)
      have b5231 := hb (x 7 6)
      have b5232 := hb (x 7 14)
      clear * - r5230 b5231 b5232 d5039
      omega
    have d5233 : (x 8 7).toNat = 1 := by
      have r5234 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := by have q := hcov7 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5235 := hb (x 0 8)
      have b5236 := hb (x 8 7)
      have b5237 := hb (x 7 1 && x 7 8)
      have b5238 := hb (x 6 2 && x 6 9)
      have b5239 := hb (x 5 3 && x 5 10)
      have b5240 := hb (x 4 4 && x 4 11)
      have b5241 := hb (x 3 5 && x 3 12)
      have b5242 := hb (x 2 6 && x 2 13)
      have b5243 := hb (x 1 7 && x 1 14)
      clear * - r5234 b5235 b5236 b5237 b5238 b5239 b5240 b5241 b5242 b5243 d4594 d4622 d4646 d4991 g25 d5136 g26 g8
      omega
    have d5244 : (x 15 8).toNat = 0 := by
      have r5245 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5246 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e5247 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e5248 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e5249 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e5250 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e5251 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have b5252 := hb (x 8 7)
      have b5253 := hb (x 9 6)
      have b5254 := hb (x 10 5)
      have b5255 := hb (x 11 4)
      have b5256 := hb (x 12 11)
      have b5257 := hb (x 13 10)
      have b5258 := hb (x 14 9)
      have b5259 := hb (x 15 8)
      clear * - r5245 e5246 e5247 e5248 e5249 e5250 e5251 b5252 b5253 b5254 b5255 b5256 b5257 b5258 b5259 d5233
      omega
    have d5260 : (x 15 1 && x 15 8).toNat = 0 := by
      have r5261 := hand2 (x 15 1) (x 15 8)
      have b5262 := hb (x 15 8)
      have b5263 := hb (x 15 1 && x 15 8)
      clear * - r5261 b5262 b5263 d5244
      omega
    have d5264 : (x 15 4 && x 15 8).toNat = 0 := by
      have r5265 := hand2 (x 15 4) (x 15 8)
      have b5266 := hb (x 15 8)
      have b5267 := hb (x 15 4 && x 15 8)
      clear * - r5265 b5266 b5267 d5244
      omega
    have d5268 : (x 14 9).toNat = 0 := by
      have r5269 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5270 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e5271 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e5272 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e5273 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e5274 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e5275 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have b5276 := hb (x 8 7)
      have b5277 := hb (x 9 6)
      have b5278 := hb (x 10 5)
      have b5279 := hb (x 11 4)
      have b5280 := hb (x 12 11)
      have b5281 := hb (x 13 10)
      have b5282 := hb (x 14 9)
      have b5283 := hb (x 15 8)
      clear * - r5269 e5270 e5271 e5272 e5273 e5274 e5275 b5276 b5277 b5278 b5279 b5280 b5281 b5282 b5283 d5244 d5233
      omega
    have d5284 : (x 14 2 && x 14 9).toNat = 0 := by
      have r5285 := hand2 (x 14 2) (x 14 9)
      have b5286 := hb (x 14 9)
      have b5287 := hb (x 14 2 && x 14 9)
      clear * - r5285 b5286 b5287 d5268
      omega
    have d5288 : (x 14 5 && x 14 9).toNat = 0 := by
      have r5289 := hand2 (x 14 5) (x 14 9)
      have b5290 := hb (x 14 9)
      have b5291 := hb (x 14 5 && x 14 9)
      clear * - r5289 b5290 b5291 d5268
      omega
    have d5292 : (x 13 10).toNat = 0 := by
      have r5293 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5294 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e5295 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e5296 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e5297 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e5298 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e5299 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have b5300 := hb (x 8 7)
      have b5301 := hb (x 9 6)
      have b5302 := hb (x 10 5)
      have b5303 := hb (x 11 4)
      have b5304 := hb (x 12 11)
      have b5305 := hb (x 13 10)
      have b5306 := hb (x 14 9)
      have b5307 := hb (x 15 8)
      clear * - r5293 e5294 e5295 e5296 e5297 e5298 e5299 b5300 b5301 b5302 b5303 b5304 b5305 b5306 b5307 d5244 d5268 d5233
      omega
    have d5308 : (x 13 3 && x 13 10).toNat = 0 := by
      have r5309 := hand2 (x 13 3) (x 13 10)
      have b5310 := hb (x 13 10)
      have b5311 := hb (x 13 3 && x 13 10)
      clear * - r5309 b5310 b5311 d5292
      omega
    have d5312 : (x 13 6 && x 13 10).toNat = 0 := by
      have r5313 := hand2 (x 13 6) (x 13 10)
      have b5314 := hb (x 13 10)
      have b5315 := hb (x 13 6 && x 13 10)
      clear * - r5313 b5314 b5315 d5292
      omega
    have d5316 : (x 12 11).toNat = 0 := by
      have r5317 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5318 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e5319 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e5320 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e5321 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e5322 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e5323 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have b5324 := hb (x 8 7)
      have b5325 := hb (x 9 6)
      have b5326 := hb (x 10 5)
      have b5327 := hb (x 11 4)
      have b5328 := hb (x 12 11)
      have b5329 := hb (x 13 10)
      have b5330 := hb (x 14 9)
      have b5331 := hb (x 15 8)
      clear * - r5317 e5318 e5319 e5320 e5321 e5322 e5323 b5324 b5325 b5326 b5327 b5328 b5329 b5330 b5331 d5244 d5268 d5292 d5233
      omega
    have d5332 : (x 12 4 && x 12 11).toNat = 0 := by
      have r5333 := hand2 (x 12 4) (x 12 11)
      have b5334 := hb (x 12 11)
      have b5335 := hb (x 12 4 && x 12 11)
      clear * - r5333 b5334 b5335 d5316
      omega
    have d5336 : (x 12 7 && x 12 11).toNat = 0 := by
      have r5337 := hand2 (x 12 7) (x 12 11)
      have b5338 := hb (x 12 11)
      have b5339 := hb (x 12 7 && x 12 11)
      clear * - r5337 b5338 b5339 d5316
      omega
    have d5340 : (x 11 4).toNat = 0 := by
      have r5341 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5342 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e5343 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e5344 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e5345 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e5346 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e5347 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have b5348 := hb (x 8 7)
      have b5349 := hb (x 9 6)
      have b5350 := hb (x 10 5)
      have b5351 := hb (x 11 4)
      have b5352 := hb (x 12 11)
      have b5353 := hb (x 13 10)
      have b5354 := hb (x 14 9)
      have b5355 := hb (x 15 8)
      clear * - r5341 e5342 e5343 e5344 e5345 e5346 e5347 b5348 b5349 b5350 b5351 b5352 b5353 b5354 b5355 d5244 d5268 d5292 d5316 d5233
      omega
    have d5356 : (x 11 4 && x 11 14).toNat = 0 := by
      have r5357 := hand1 (x 11 4) (x 11 14)
      have b5358 := hb (x 11 4)
      have b5359 := hb (x 11 4 && x 11 14)
      clear * - r5357 b5358 b5359 d5340
      omega
    have d5360 : (x 11 4 && x 11 10).toNat = 0 := by
      have r5361 := hand1 (x 11 4) (x 11 10)
      have b5362 := hb (x 11 4)
      have b5363 := hb (x 11 4 && x 11 10)
      clear * - r5361 b5362 b5363 d5340
      omega
    have d5364 : (x 11 4 && x 11 9).toNat = 0 := by
      have r5365 := hand1 (x 11 4) (x 11 9)
      have b5366 := hb (x 11 4)
      have b5367 := hb (x 11 4 && x 11 9)
      clear * - r5365 b5366 b5367 d5340
      omega
    have d5368 : (x 10 5).toNat = 0 := by
      have r5369 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5370 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e5371 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e5372 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e5373 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e5374 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e5375 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have b5376 := hb (x 8 7)
      have b5377 := hb (x 9 6)
      have b5378 := hb (x 10 5)
      have b5379 := hb (x 11 4)
      have b5380 := hb (x 12 11)
      have b5381 := hb (x 13 10)
      have b5382 := hb (x 14 9)
      have b5383 := hb (x 15 8)
      clear * - r5369 e5370 e5371 e5372 e5373 e5374 e5375 b5376 b5377 b5378 b5379 b5380 b5381 b5382 b5383 d5244 d5268 d5292 d5316 d5340 d5233
      omega
    have d5384 : (x 10 5 && x 10 11).toNat = 0 := by
      have r5385 := hand1 (x 10 5) (x 10 11)
      have b5386 := hb (x 10 5)
      have b5387 := hb (x 10 5 && x 10 11)
      clear * - r5385 b5386 b5387 d5368
      omega
    have d5388 : (x 10 5 && x 10 10).toNat = 0 := by
      have r5389 := hand1 (x 10 5) (x 10 10)
      have b5390 := hb (x 10 5)
      have b5391 := hb (x 10 5 && x 10 10)
      clear * - r5389 b5390 b5391 d5368
      omega
    have d5392 : (x 9 6).toNat = 0 := by
      have r5393 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5394 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e5395 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e5396 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e5397 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e5398 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e5399 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have b5400 := hb (x 8 7)
      have b5401 := hb (x 9 6)
      have b5402 := hb (x 10 5)
      have b5403 := hb (x 11 4)
      have b5404 := hb (x 12 11)
      have b5405 := hb (x 13 10)
      have b5406 := hb (x 14 9)
      have b5407 := hb (x 15 8)
      clear * - r5393 e5394 e5395 e5396 e5397 e5398 e5399 b5400 b5401 b5402 b5403 b5404 b5405 b5406 b5407 d5244 d5268 d5292 d5316 d5340 d5368 d5233
      omega
    have d5408 : (x 9 6 && x 9 11).toNat = 0 := by
      have r5409 := hand1 (x 9 6) (x 9 11)
      have b5410 := hb (x 9 6)
      have b5411 := hb (x 9 6 && x 9 11)
      clear * - r5409 b5410 b5411 d5392
      omega
    have d5412 : (x 6 3 && x 6 7).toNat = 1 := by
      have r5413 : 1 ≤ (x 9 4).toNat + (x 8 1 && x 8 5).toNat + (x 7 2 && x 7 6).toNat + (x 6 3 && x 6 7).toNat + (x 5 4 && x 5 8).toNat + (x 4 5 && x 4 9).toNat + (x 3 6 && x 3 10).toNat + (x 2 7 && x 2 11).toNat + (x 1 8 && x 1 12).toNat + (x 0 9 && x 0 13).toNat + (x (-1) 10 && x (-1) 14).toNat + (x (-2) 11).toNat := by have q := hcov4 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5414 : (x 8 1 && x 8 5).toNat = (x 8 5).toNat := handr _ _ (fun h => hp13 8 (hp5 8 (h)))
      have e5415 : (x (-1) 10 && x (-1) 14).toNat = (x (-1) 10).toNat := handl _ _ (fun h => hp2 (-1) (hp10 (-1) (h)))
      have b5416 := hb (x (-2) 11)
      have b5417 := hb (x (-1) 10)
      have b5418 := hb (x 8 5)
      have b5419 := hb (x 9 4)
      have b5420 := hb (x 7 2 && x 7 6)
      have b5421 := hb (x 6 3 && x 6 7)
      have b5422 := hb (x 5 4 && x 5 8)
      have b5423 := hb (x 4 5 && x 4 9)
      have b5424 := hb (x 3 6 && x 3 10)
      have b5425 := hb (x 2 7 && x 2 11)
      have b5426 := hb (x 1 8 && x 1 12)
      have b5427 := hb (x 0 9 && x 0 13)
      clear * - r5413 e5414 e5415 b5416 b5417 b5418 b5419 b5420 b5421 b5422 b5423 b5424 b5425 b5426 b5427 d4753 d4785 d4801 d4702 d4857 g22 d4877 g23 d4971 g4 g3
      omega
    have d5428 : (x 6 7).toNat = 1 := by
      have r5429 := hand2 (x 6 3) (x 6 7)
      have b5430 := hb (x 6 7)
      have b5431 := hb (x 6 3 && x 6 7)
      clear * - r5429 b5430 b5431 d5412
      omega
    have d5432 : (x 13 8).toNat = 0 := by
      have r5433 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5434 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
      have e5435 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
      have e5436 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
      have e5437 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
      have e5438 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
      have e5439 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
      have b5440 := hb (x 6 7)
      have b5441 := hb (x 7 6)
      have b5442 := hb (x 8 5)
      have b5443 := hb (x 9 4)
      have b5444 := hb (x 10 11)
      have b5445 := hb (x 11 10)
      have b5446 := hb (x 12 9)
      have b5447 := hb (x 13 8)
      clear * - r5433 e5434 e5435 e5436 e5437 e5438 e5439 b5440 b5441 b5442 b5443 b5444 b5445 b5446 b5447 d4753 d4785 d5229 d5428
      omega
    have d5448 : (x 13 1 && x 13 8).toNat = 0 := by
      have r5449 := hand2 (x 13 1) (x 13 8)
      have b5450 := hb (x 13 8)
      have b5451 := hb (x 13 1 && x 13 8)
      clear * - r5449 b5450 b5451 d5432
      omega
    have d5452 : (x 13 2 && x 13 8).toNat = 0 := by
      have r5453 := hand2 (x 13 2) (x 13 8)
      have b5454 := hb (x 13 8)
      have b5455 := hb (x 13 2 && x 13 8)
      clear * - r5453 b5454 b5455 d5432
      omega
    have d5456 : (x 12 9).toNat = 0 := by
      have r5457 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5458 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
      have e5459 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
      have e5460 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
      have e5461 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
      have e5462 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
      have e5463 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
      have b5464 := hb (x 6 7)
      have b5465 := hb (x 7 6)
      have b5466 := hb (x 8 5)
      have b5467 := hb (x 9 4)
      have b5468 := hb (x 10 11)
      have b5469 := hb (x 11 10)
      have b5470 := hb (x 12 9)
      have b5471 := hb (x 13 8)
      clear * - r5457 e5458 e5459 e5460 e5461 e5462 e5463 b5464 b5465 b5466 b5467 b5468 b5469 b5470 b5471 d5432 d4753 d4785 d5229 d5428
      omega
    have d5472 : (x 12 2 && x 12 9).toNat = 0 := by
      have r5473 := hand2 (x 12 2) (x 12 9)
      have b5474 := hb (x 12 9)
      have b5475 := hb (x 12 2 && x 12 9)
      clear * - r5473 b5474 b5475 d5456
      omega
    have d5476 : (x 12 3 && x 12 9).toNat = 0 := by
      have r5477 := hand2 (x 12 3) (x 12 9)
      have b5478 := hb (x 12 9)
      have b5479 := hb (x 12 3 && x 12 9)
      clear * - r5477 b5478 b5479 d5456
      omega
    have d5480 : (x 11 10).toNat = 0 := by
      have r5481 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5482 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
      have e5483 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
      have e5484 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
      have e5485 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
      have e5486 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
      have e5487 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
      have b5488 := hb (x 6 7)
      have b5489 := hb (x 7 6)
      have b5490 := hb (x 8 5)
      have b5491 := hb (x 9 4)
      have b5492 := hb (x 10 11)
      have b5493 := hb (x 11 10)
      have b5494 := hb (x 12 9)
      have b5495 := hb (x 13 8)
      clear * - r5481 e5482 e5483 e5484 e5485 e5486 e5487 b5488 b5489 b5490 b5491 b5492 b5493 b5494 b5495 d5432 d5456 d4753 d4785 d5229 d5428
      omega
    have d5496 : (x 11 1 && x 11 10).toNat = 0 := by
      have r5497 := hand2 (x 11 1) (x 11 10)
      have b5498 := hb (x 11 10)
      have b5499 := hb (x 11 1 && x 11 10)
      clear * - r5497 b5498 b5499 d5480
      omega
    have d5500 : (x 11 3 && x 11 10).toNat = 0 := by
      have r5501 := hand2 (x 11 3) (x 11 10)
      have b5502 := hb (x 11 10)
      have b5503 := hb (x 11 3 && x 11 10)
      clear * - r5501 b5502 b5503 d5480
      omega
    have d5504 : (x 10 11).toNat = 0 := by
      have r5505 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5506 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
      have e5507 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
      have e5508 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
      have e5509 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
      have e5510 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
      have e5511 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
      have b5512 := hb (x 6 7)
      have b5513 := hb (x 7 6)
      have b5514 := hb (x 8 5)
      have b5515 := hb (x 9 4)
      have b5516 := hb (x 10 11)
      have b5517 := hb (x 11 10)
      have b5518 := hb (x 12 9)
      have b5519 := hb (x 13 8)
      clear * - r5505 e5506 e5507 e5508 e5509 e5510 e5511 b5512 b5513 b5514 b5515 b5516 b5517 b5518 b5519 d5432 d5456 d5480 d4753 d4785 d5229 d5428
      omega
    have d5520 : (x 10 1 && x 10 11).toNat = 0 := by
      have r5521 := hand2 (x 10 1) (x 10 11)
      have b5522 := hb (x 10 11)
      have b5523 := hb (x 10 1 && x 10 11)
      clear * - r5521 b5522 b5523 d5504
      omega
    have d5524 : (x 6 5).toNat = 1 := by
      have r5525 : 1 ≤ (x 11 10).toNat + (x 10 1 && x 10 11).toNat + (x 9 2 && x 9 12).toNat + (x 8 3 && x 8 13).toNat + (x 7 4 && x 7 14).toNat + (x 6 5).toNat := by have q := hcov10 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5526 := hb (x 6 5)
      have b5527 := hb (x 11 10)
      have b5528 := hb (x 10 1 && x 10 11)
      have b5529 := hb (x 9 2 && x 9 12)
      have b5530 := hb (x 8 3 && x 8 13)
      have b5531 := hb (x 7 4 && x 7 14)
      clear * - r5525 b5526 b5527 b5528 b5529 b5530 b5531 d5480 d5520 d4737 d4769 d5221
      omega
    have d5532 : (x 6 13).toNat = 1 := by
      have r5533 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
      have b5534 := hb (x 6 5)
      have b5535 := hb (x 6 13)
      clear * - r5533 b5534 b5535 d5524
      omega
    have d5536 : (x 7 12).toNat = 0 := by
      have r5537 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5538 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
      have e5539 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
      have b5540 := hb (x 4 3)
      have b5541 := hb (x 5 2)
      have b5542 := hb (x 6 13)
      have b5543 := hb (x 7 12)
      clear * - r5537 e5538 e5539 b5540 b5541 b5542 b5543 d5532 d5173
      omega
    have d5544 : (x 7 4).toNat = 0 := by
      have r5545 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
      have b5546 := hb (x 7 4)
      have b5547 := hb (x 7 12)
      clear * - r5545 b5546 b5547 d5536
      omega
    have d5548 : (x 11 8).toNat = 0 := by
      have r5549 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5550 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
      have e5551 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
      have e5552 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
      have e5553 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
      have e5554 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
      have e5555 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
      have b5556 := hb (x 4 7)
      have b5557 := hb (x 5 6)
      have b5558 := hb (x 6 5)
      have b5559 := hb (x 7 4)
      have b5560 := hb (x 8 11)
      have b5561 := hb (x 9 10)
      have b5562 := hb (x 10 9)
      have b5563 := hb (x 11 8)
      clear * - r5549 e5550 e5551 e5552 e5553 e5554 e5555 b5556 b5557 b5558 b5559 b5560 b5561 b5562 b5563 d5544 d5524 d5169
      omega
    have d5564 : (x 11 8 && x 11 12).toNat = 0 := by
      have r5565 := hand1 (x 11 8) (x 11 12)
      have b5566 := hb (x 11 8)
      have b5567 := hb (x 11 8 && x 11 12)
      clear * - r5565 b5566 b5567 d5548
      omega
    have d5568 : (x 10 9).toNat = 0 := by
      have r5569 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5570 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
      have e5571 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
      have e5572 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
      have e5573 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
      have e5574 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
      have e5575 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
      have b5576 := hb (x 4 7)
      have b5577 := hb (x 5 6)
      have b5578 := hb (x 6 5)
      have b5579 := hb (x 7 4)
      have b5580 := hb (x 8 11)
      have b5581 := hb (x 9 10)
      have b5582 := hb (x 10 9)
      have b5583 := hb (x 11 8)
      clear * - r5569 e5570 e5571 e5572 e5573 e5574 e5575 b5576 b5577 b5578 b5579 b5580 b5581 b5582 b5583 d5548 d5544 d5524 d5169
      omega
    have d5584 : (x 10 9 && x 10 13).toNat = 0 := by
      have r5585 := hand1 (x 10 9) (x 10 13)
      have b5586 := hb (x 10 9)
      have b5587 := hb (x 10 9 && x 10 13)
      clear * - r5585 b5586 b5587 d5568
      omega
    have d5588 : (x 9 10).toNat = 0 := by
      have r5589 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5590 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
      have e5591 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
      have e5592 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
      have e5593 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
      have e5594 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
      have e5595 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
      have b5596 := hb (x 4 7)
      have b5597 := hb (x 5 6)
      have b5598 := hb (x 6 5)
      have b5599 := hb (x 7 4)
      have b5600 := hb (x 8 11)
      have b5601 := hb (x 9 10)
      have b5602 := hb (x 10 9)
      have b5603 := hb (x 11 8)
      clear * - r5589 e5590 e5591 e5592 e5593 e5594 e5595 b5596 b5597 b5598 b5599 b5600 b5601 b5602 b5603 d5548 d5568 d5544 d5524 d5169
      omega
    have d5604 : (x 8 11).toNat = 0 := by
      have r5605 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5606 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
      have e5607 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
      have e5608 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
      have e5609 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
      have e5610 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
      have e5611 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
      have b5612 := hb (x 4 7)
      have b5613 := hb (x 5 6)
      have b5614 := hb (x 6 5)
      have b5615 := hb (x 7 4)
      have b5616 := hb (x 8 11)
      have b5617 := hb (x 9 10)
      have b5618 := hb (x 10 9)
      have b5619 := hb (x 11 8)
      clear * - r5605 e5606 e5607 e5608 e5609 e5610 e5611 b5612 b5613 b5614 b5615 b5616 b5617 b5618 b5619 d5548 d5568 d5588 d5544 d5524 d5169
      omega
    have d5620 : (x 10 2 && x 10 11).toNat = 0 := by
      have r5621 := hand2 (x 10 2) (x 10 11)
      have b5622 := hb (x 10 11)
      have b5623 := hb (x 10 2 && x 10 11)
      clear * - r5621 b5622 b5623 d5504
      omega
    have d5624 : (x 6 6).toNat = 1 := by
      have r5625 : 1 ≤ (x 12 9).toNat + (x 11 1 && x 11 10).toNat + (x 10 2 && x 10 11).toNat + (x 9 3 && x 9 12).toNat + (x 8 4 && x 8 13).toNat + (x 7 5 && x 7 14).toNat + (x 6 6).toNat := by have q := hcov9 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5626 := hb (x 6 6)
      have b5627 := hb (x 12 9)
      have b5628 := hb (x 11 1 && x 11 10)
      have b5629 := hb (x 10 2 && x 10 11)
      have b5630 := hb (x 9 3 && x 9 12)
      have b5631 := hb (x 8 4 && x 8 13)
      have b5632 := hb (x 7 5 && x 7 14)
      clear * - r5625 b5626 b5627 b5628 b5629 b5630 b5631 b5632 d5456 d5496 d5620 d4741 d4773 d5217
      omega
    have d5633 : (x 12 8).toNat = 0 := by
      have r5634 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5635 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
      have e5636 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
      have e5637 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
      have e5638 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
      have e5639 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
      have e5640 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
      have b5641 := hb (x 5 7)
      have b5642 := hb (x 6 6)
      have b5643 := hb (x 7 5)
      have b5644 := hb (x 8 4)
      have b5645 := hb (x 9 11)
      have b5646 := hb (x 10 10)
      have b5647 := hb (x 11 9)
      have b5648 := hb (x 12 8)
      clear * - r5634 e5635 e5636 e5637 e5638 e5639 e5640 b5641 b5642 b5643 b5644 b5645 b5646 b5647 b5648 d5193 d5213 d5624
      omega
    have d5649 : (x 12 3 && x 12 8).toNat = 0 := by
      have r5650 := hand2 (x 12 3) (x 12 8)
      have b5651 := hb (x 12 8)
      have b5652 := hb (x 12 3 && x 12 8)
      clear * - r5650 b5651 b5652 d5633
      omega
    have d5653 : (x 11 9).toNat = 0 := by
      have r5654 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5655 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
      have e5656 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
      have e5657 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
      have e5658 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
      have e5659 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
      have e5660 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
      have b5661 := hb (x 5 7)
      have b5662 := hb (x 6 6)
      have b5663 := hb (x 7 5)
      have b5664 := hb (x 8 4)
      have b5665 := hb (x 9 11)
      have b5666 := hb (x 10 10)
      have b5667 := hb (x 11 9)
      have b5668 := hb (x 12 8)
      clear * - r5654 e5655 e5656 e5657 e5658 e5659 e5660 b5661 b5662 b5663 b5664 b5665 b5666 b5667 b5668 d5633 d5193 d5213 d5624
      omega
    have d5669 : (x 10 10).toNat = 0 := by
      have r5670 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5671 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
      have e5672 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
      have e5673 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
      have e5674 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
      have e5675 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
      have e5676 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
      have b5677 := hb (x 5 7)
      have b5678 := hb (x 6 6)
      have b5679 := hb (x 7 5)
      have b5680 := hb (x 8 4)
      have b5681 := hb (x 9 11)
      have b5682 := hb (x 10 10)
      have b5683 := hb (x 11 9)
      have b5684 := hb (x 12 8)
      clear * - r5670 e5671 e5672 e5673 e5674 e5675 e5676 b5677 b5678 b5679 b5680 b5681 b5682 b5683 b5684 d5633 d5653 d5193 d5213 d5624
      omega
    have d5685 : (x 9 11).toNat = 0 := by
      have r5686 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5687 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
      have e5688 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
      have e5689 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
      have e5690 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
      have e5691 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
      have e5692 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
      have b5693 := hb (x 5 7)
      have b5694 := hb (x 6 6)
      have b5695 := hb (x 7 5)
      have b5696 := hb (x 8 4)
      have b5697 := hb (x 9 11)
      have b5698 := hb (x 10 10)
      have b5699 := hb (x 11 9)
      have b5700 := hb (x 12 8)
      clear * - r5686 e5687 e5688 e5689 e5690 e5691 e5692 b5693 b5694 b5695 b5696 b5697 b5698 b5699 b5700 d5633 d5653 d5669 d5193 d5213 d5624
      omega
    have d5701 : (x 9 1 && x 9 11).toNat = 0 := by
      have r5702 := hand2 (x 9 1) (x 9 11)
      have b5703 := hb (x 9 11)
      have b5704 := hb (x 9 1 && x 9 11)
      clear * - r5702 b5703 b5704 d5685
      omega
    have d5705 : (x 6 4 && x 6 14).toNat = 1 := by
      have r5706 : 1 ≤ (x 10 10).toNat + (x 9 1 && x 9 11).toNat + (x 8 2 && x 8 12).toNat + (x 7 3 && x 7 13).toNat + (x 6 4 && x 6 14).toNat + (x 5 5).toNat := by have q := hcov10 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5707 := hb (x 5 5)
      have b5708 := hb (x 10 10)
      have b5709 := hb (x 9 1 && x 9 11)
      have b5710 := hb (x 8 2 && x 8 12)
      have b5711 := hb (x 7 3 && x 7 13)
      have b5712 := hb (x 6 4 && x 6 14)
      clear * - r5706 b5707 b5708 b5709 b5710 b5711 b5712 d5669 d5701 d5185 d5209 d5148
      omega
    have d5713 : (x 6 4).toNat = 1 := by
      have r5714 := hand1 (x 6 4) (x 6 14)
      have b5715 := hb (x 6 4)
      have b5716 := hb (x 6 4 && x 6 14)
      clear * - r5714 b5715 b5716 d5705
      omega
    have d5717 : (x 6 12).toNat = 1 := by
      have r5718 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
      have b5719 := hb (x 6 4)
      have b5720 := hb (x 6 12)
      clear * - r5718 b5719 b5720 d5713
      omega
    have d5721 : (x 10 8).toNat = 0 := by
      have r5722 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5723 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
      have e5724 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
      have e5725 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
      have e5726 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
      have e5727 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
      have e5728 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
      have b5729 := hb (x 3 7)
      have b5730 := hb (x 4 6)
      have b5731 := hb (x 5 5)
      have b5732 := hb (x 6 4)
      have b5733 := hb (x 7 11)
      have b5734 := hb (x 8 10)
      have b5735 := hb (x 9 9)
      have b5736 := hb (x 10 8)
      clear * - r5722 e5723 e5724 e5725 e5726 e5727 e5728 b5729 b5730 b5731 b5732 b5733 b5734 b5735 b5736 d5713 d5148
      omega
    have d5737 : (x 9 9).toNat = 0 := by
      have r5738 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5739 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
      have e5740 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
      have e5741 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
      have e5742 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
      have e5743 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
      have e5744 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
      have b5745 := hb (x 3 7)
      have b5746 := hb (x 4 6)
      have b5747 := hb (x 5 5)
      have b5748 := hb (x 6 4)
      have b5749 := hb (x 7 11)
      have b5750 := hb (x 8 10)
      have b5751 := hb (x 9 9)
      have b5752 := hb (x 10 8)
      clear * - r5738 e5739 e5740 e5741 e5742 e5743 e5744 b5745 b5746 b5747 b5748 b5749 b5750 b5751 b5752 d5721 d5713 d5148
      omega
    have d5753 : (x 8 10).toNat = 0 := by
      have r5754 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5755 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
      have e5756 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
      have e5757 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
      have e5758 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
      have e5759 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
      have e5760 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
      have b5761 := hb (x 3 7)
      have b5762 := hb (x 4 6)
      have b5763 := hb (x 5 5)
      have b5764 := hb (x 6 4)
      have b5765 := hb (x 7 11)
      have b5766 := hb (x 8 10)
      have b5767 := hb (x 9 9)
      have b5768 := hb (x 10 8)
      clear * - r5754 e5755 e5756 e5757 e5758 e5759 e5760 b5761 b5762 b5763 b5764 b5765 b5766 b5767 b5768 d5721 d5737 d5713 d5148
      omega
    have d5769 : (x 7 11).toNat = 0 := by
      have r5770 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5771 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
      have e5772 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
      have e5773 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
      have e5774 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
      have e5775 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
      have e5776 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
      have b5777 := hb (x 3 7)
      have b5778 := hb (x 4 6)
      have b5779 := hb (x 5 5)
      have b5780 := hb (x 6 4)
      have b5781 := hb (x 7 11)
      have b5782 := hb (x 8 10)
      have b5783 := hb (x 9 9)
      have b5784 := hb (x 10 8)
      clear * - r5770 e5771 e5772 e5773 e5774 e5775 e5776 b5777 b5778 b5779 b5780 b5781 b5782 b5783 b5784 d5721 d5737 d5753 d5713 d5148
      omega
    have d5785 : (x 10 4 && x 10 11).toNat = 0 := by
      have r5786 := hand2 (x 10 4) (x 10 11)
      have b5787 := hb (x 10 11)
      have b5788 := hb (x 10 4 && x 10 11)
      clear * - r5786 b5787 b5788 d5504
      omega
    have d5789 : (x 14 7).toNat = 1 := by
      have r5790 : 1 ≤ (x 14 7).toNat + (x 13 1 && x 13 8).toNat + (x 12 2 && x 12 9).toNat + (x 11 3 && x 11 10).toNat + (x 10 4 && x 10 11).toNat + (x 9 5 && x 9 12).toNat + (x 8 6 && x 8 13).toNat + (x 7 7 && x 7 14).toNat + (x 6 8).toNat := by have q := hcov7 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5791 := hb (x 6 8)
      have b5792 := hb (x 14 7)
      have b5793 := hb (x 13 1 && x 13 8)
      have b5794 := hb (x 12 2 && x 12 9)
      have b5795 := hb (x 11 3 && x 11 10)
      have b5796 := hb (x 10 4 && x 10 11)
      have b5797 := hb (x 9 5 && x 9 12)
      have b5798 := hb (x 8 6 && x 8 13)
      have b5799 := hb (x 7 7 && x 7 14)
      clear * - r5790 b5791 b5792 b5793 b5794 b5795 b5796 b5797 b5798 b5799 d5448 d5472 d5500 d5785 d4745 d4777 d5225 d3446
      omega
    have d5800 : (x 21 8).toNat = 0 := by
      have r5801 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5802 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
      have e5803 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
      have e5804 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
      have e5805 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
      have e5806 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
      have e5807 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
      have b5808 := hb (x 14 7)
      have b5809 := hb (x 15 6)
      have b5810 := hb (x 16 5)
      have b5811 := hb (x 17 4)
      have b5812 := hb (x 18 11)
      have b5813 := hb (x 19 10)
      have b5814 := hb (x 20 9)
      have b5815 := hb (x 21 8)
      clear * - r5801 e5802 e5803 e5804 e5805 e5806 e5807 b5808 b5809 b5810 b5811 b5812 b5813 b5814 b5815 d5789
      omega
    have d5816 : (x 20 9).toNat = 0 := by
      have r5817 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5818 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
      have e5819 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
      have e5820 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
      have e5821 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
      have e5822 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
      have e5823 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
      have b5824 := hb (x 14 7)
      have b5825 := hb (x 15 6)
      have b5826 := hb (x 16 5)
      have b5827 := hb (x 17 4)
      have b5828 := hb (x 18 11)
      have b5829 := hb (x 19 10)
      have b5830 := hb (x 20 9)
      have b5831 := hb (x 21 8)
      clear * - r5817 e5818 e5819 e5820 e5821 e5822 e5823 b5824 b5825 b5826 b5827 b5828 b5829 b5830 b5831 d5800 d5789
      omega
    have d5832 : (x 19 10).toNat = 0 := by
      have r5833 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5834 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
      have e5835 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
      have e5836 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
      have e5837 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
      have e5838 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
      have e5839 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
      have b5840 := hb (x 14 7)
      have b5841 := hb (x 15 6)
      have b5842 := hb (x 16 5)
      have b5843 := hb (x 17 4)
      have b5844 := hb (x 18 11)
      have b5845 := hb (x 19 10)
      have b5846 := hb (x 20 9)
      have b5847 := hb (x 21 8)
      clear * - r5833 e5834 e5835 e5836 e5837 e5838 e5839 b5840 b5841 b5842 b5843 b5844 b5845 b5846 b5847 d5800 d5816 d5789
      omega
    have d5848 : (x 18 11).toNat = 0 := by
      have r5849 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5850 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
      have e5851 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
      have e5852 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
      have e5853 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
      have e5854 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
      have e5855 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
      have b5856 := hb (x 14 7)
      have b5857 := hb (x 15 6)
      have b5858 := hb (x 16 5)
      have b5859 := hb (x 17 4)
      have b5860 := hb (x 18 11)
      have b5861 := hb (x 19 10)
      have b5862 := hb (x 20 9)
      have b5863 := hb (x 21 8)
      clear * - r5849 e5850 e5851 e5852 e5853 e5854 e5855 b5856 b5857 b5858 b5859 b5860 b5861 b5862 b5863 d5800 d5816 d5832 d5789
      omega
    have d5864 : (x 17 4).toNat = 0 := by
      have r5865 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5866 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
      have e5867 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
      have e5868 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
      have e5869 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
      have e5870 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
      have e5871 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
      have b5872 := hb (x 14 7)
      have b5873 := hb (x 15 6)
      have b5874 := hb (x 16 5)
      have b5875 := hb (x 17 4)
      have b5876 := hb (x 18 11)
      have b5877 := hb (x 19 10)
      have b5878 := hb (x 20 9)
      have b5879 := hb (x 21 8)
      clear * - r5865 e5866 e5867 e5868 e5869 e5870 e5871 b5872 b5873 b5874 b5875 b5876 b5877 b5878 b5879 d5800 d5816 d5832 d5848 d5789
      omega
    have d5880 : (x 17 4 && x 17 14).toNat = 0 := by
      have r5881 := hand1 (x 17 4) (x 17 14)
      have b5882 := hb (x 17 4)
      have b5883 := hb (x 17 4 && x 17 14)
      clear * - r5881 b5882 b5883 d5864
      omega
    have d5884 : (x 16 5).toNat = 0 := by
      have r5885 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5886 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
      have e5887 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
      have e5888 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
      have e5889 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
      have e5890 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
      have e5891 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
      have b5892 := hb (x 14 7)
      have b5893 := hb (x 15 6)
      have b5894 := hb (x 16 5)
      have b5895 := hb (x 17 4)
      have b5896 := hb (x 18 11)
      have b5897 := hb (x 19 10)
      have b5898 := hb (x 20 9)
      have b5899 := hb (x 21 8)
      clear * - r5885 e5886 e5887 e5888 e5889 e5890 e5891 b5892 b5893 b5894 b5895 b5896 b5897 b5898 b5899 d5800 d5816 d5832 d5848 d5864 d5789
      omega
    have d5900 : (x 15 6).toNat = 0 := by
      have r5901 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5902 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
      have e5903 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
      have e5904 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
      have e5905 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
      have e5906 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
      have e5907 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
      have b5908 := hb (x 14 7)
      have b5909 := hb (x 15 6)
      have b5910 := hb (x 16 5)
      have b5911 := hb (x 17 4)
      have b5912 := hb (x 18 11)
      have b5913 := hb (x 19 10)
      have b5914 := hb (x 20 9)
      have b5915 := hb (x 21 8)
      clear * - r5901 e5902 e5903 e5904 e5905 e5906 e5907 b5908 b5909 b5910 b5911 b5912 b5913 b5914 b5915 d5800 d5816 d5832 d5848 d5864 d5884 d5789
      omega
    have d5916 : (x 14 1 && x 14 7).toNat = 1 := by
      have r5917 : 1 ≤ (x 15 6).toNat + (x 14 1 && x 14 7).toNat + (x 13 2 && x 13 8).toNat + (x 12 3 && x 12 9).toNat + (x 11 4 && x 11 10).toNat + (x 10 5 && x 10 11).toNat + (x 9 6 && x 9 12).toNat + (x 8 7 && x 8 13).toNat + (x 7 8 && x 7 14).toNat + (x 6 9).toNat := by have q := hcov6 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5918 := hb (x 6 9)
      have b5919 := hb (x 15 6)
      have b5920 := hb (x 14 1 && x 14 7)
      have b5921 := hb (x 13 2 && x 13 8)
      have b5922 := hb (x 12 3 && x 12 9)
      have b5923 := hb (x 11 4 && x 11 10)
      have b5924 := hb (x 10 5 && x 10 11)
      have b5925 := hb (x 9 6 && x 9 12)
      have b5926 := hb (x 8 7 && x 8 13)
      have b5927 := hb (x 7 8 && x 7 14)
      clear * - r5917 b5918 b5919 b5920 b5921 b5922 b5923 b5924 b5925 b5926 b5927 d5900 d5452 d5476 d5360 d5384 d4749 d4781 d4598 d4606
      omega
    have d5928 : (x 14 1).toNat = 1 := by
      have r5929 := hand1 (x 14 1) (x 14 7)
      have b5930 := hb (x 14 1)
      have b5931 := hb (x 14 1 && x 14 7)
      clear * - r5929 b5930 b5931 d5916
      omega
    have d5932 : (x 15 14).toNat = 0 := by
      have r5933 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5934 := hb (x 14 1)
      have b5935 := hb (x 15 14)
      clear * - r5933 b5934 b5935 d5928
      omega
    have d5936 : (x 15 3 && x 15 14).toNat = 0 := by
      have r5937 := hand2 (x 15 3) (x 15 14)
      have b5938 := hb (x 15 14)
      have b5939 := hb (x 15 3 && x 15 14)
      clear * - r5937 b5938 b5939 d5932
      omega
    have d5940 : (x 15 2).toNat = 0 := by
      have r5941 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
      have b5942 := hb (x 15 2)
      have b5943 := hb (x 15 14)
      clear * - r5941 b5942 b5943 d5932
      omega
    have d5944 : (x 15 10).toNat = 0 := by
      have r5945 : (x 15 10).toNat ≤ (x 15 2).toNat := himp _ _ (hp10 15)
      have b5946 := hb (x 15 2)
      have b5947 := hb (x 15 10)
      clear * - r5945 b5946 b5947 d5940
      omega
    have d5948 : (x 13 2).toNat = 0 := by
      have r5949 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5950 := hb (x 1 14)
      have b5951 := hb (x 2 13)
      have b5952 := hb (x 3 12)
      have b5953 := hb (x 4 11)
      have b5954 := hb (x 5 10)
      have b5955 := hb (x 6 9)
      have b5956 := hb (x 7 8)
      have b5957 := hb (x 8 7)
      have b5958 := hb (x 9 6)
      have b5959 := hb (x 10 5)
      have b5960 := hb (x 11 4)
      have b5961 := hb (x 12 3)
      have b5962 := hb (x 13 2)
      have b5963 := hb (x 14 1)
      clear * - r5949 b5950 b5951 b5952 b5953 b5954 b5955 b5956 b5957 b5958 b5959 b5960 b5961 b5962 b5963 d5928 d5340 d5368 d5392 d5233 d4578 d4606 d4630 d4650 g20 g16 g15
      omega
    have d5964 : (x 13 2 && x 13 12).toNat = 0 := by
      have r5965 := hand1 (x 13 2) (x 13 12)
      have b5966 := hb (x 13 2)
      have b5967 := hb (x 13 2 && x 13 12)
      clear * - r5965 b5966 b5967 d5948
      omega
    have d5968 : (x 13 2 && x 13 7).toNat = 0 := by
      have r5969 := hand1 (x 13 2) (x 13 7)
      have b5970 := hb (x 13 2)
      have b5971 := hb (x 13 2 && x 13 7)
      clear * - r5969 b5970 b5971 d5948
      omega
    have d5972 : (x 12 3).toNat = 0 := by
      have r5973 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5974 := hb (x 1 14)
      have b5975 := hb (x 2 13)
      have b5976 := hb (x 3 12)
      have b5977 := hb (x 4 11)
      have b5978 := hb (x 5 10)
      have b5979 := hb (x 6 9)
      have b5980 := hb (x 7 8)
      have b5981 := hb (x 8 7)
      have b5982 := hb (x 9 6)
      have b5983 := hb (x 10 5)
      have b5984 := hb (x 11 4)
      have b5985 := hb (x 12 3)
      have b5986 := hb (x 13 2)
      have b5987 := hb (x 14 1)
      clear * - r5973 b5974 b5975 b5976 b5977 b5978 b5979 b5980 b5981 b5982 b5983 b5984 b5985 b5986 b5987 d5928 d5948 d5340 d5368 d5392 d5233 d4578 d4606 d4630 d4650 g20 g16 g15
      omega
    have d5988 : (x 12 3 && x 12 13).toNat = 0 := by
      have r5989 := hand1 (x 12 3) (x 12 13)
      have b5990 := hb (x 12 3)
      have b5991 := hb (x 12 3 && x 12 13)
      clear * - r5989 b5990 b5991 d5972
      omega
    have d5992 : (x 14 1 && x 14 11).toNat = 1 := by
      have r5993 : 1 ≤ (x 15 10).toNat + (x 14 1 && x 14 11).toNat + (x 13 2 && x 13 12).toNat + (x 12 3 && x 12 13).toNat + (x 11 4 && x 11 14).toNat + (x 10 5).toNat := by have q := hcov10 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5994 := hb (x 10 5)
      have b5995 := hb (x 15 10)
      have b5996 := hb (x 14 1 && x 14 11)
      have b5997 := hb (x 13 2 && x 13 12)
      have b5998 := hb (x 12 3 && x 12 13)
      have b5999 := hb (x 11 4 && x 11 14)
      clear * - r5993 b5994 b5995 b5996 b5997 b5998 b5999 d5944 d5964 d5988 d5356 d5368
      omega
    have d6000 : (x 14 11).toNat = 1 := by
      have r6001 := hand2 (x 14 1) (x 14 11)
      have b6002 := hb (x 14 11)
      have b6003 := hb (x 14 1 && x 14 11)
      clear * - r6001 b6002 b6003 d5992
      omega
    have d6004 : (x 14 3).toNat = 1 := by
      have r6005 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
      have b6006 := hb (x 14 3)
      have b6007 := hb (x 14 11)
      clear * - r6005 b6006 b6007 d6000
      omega
    have d6008 : (x 17 12).toNat = 0 := by
      have r6009 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6010 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
      have e6011 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
      have b6012 := hb (x 14 3)
      have b6013 := hb (x 15 2)
      have b6014 := hb (x 16 13)
      have b6015 := hb (x 17 12)
      clear * - r6009 e6010 e6011 b6012 b6013 b6014 b6015 d5940 d6004
      omega
    have d6016 : (x 17 1 && x 17 12).toNat = 0 := by
      have r6017 := hand2 (x 17 1) (x 17 12)
      have b6018 := hb (x 17 12)
      have b6019 := hb (x 17 1 && x 17 12)
      clear * - r6017 b6018 b6019 d6008
      omega
    have d6020 : (x 16 13).toNat = 0 := by
      have r6021 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6022 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
      have e6023 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
      have b6024 := hb (x 14 3)
      have b6025 := hb (x 15 2)
      have b6026 := hb (x 16 13)
      have b6027 := hb (x 17 12)
      clear * - r6021 e6022 e6023 b6024 b6025 b6026 b6027 d6008 d5940 d6004
      omega
    have d6028 : (x 16 2 && x 16 13).toNat = 0 := by
      have r6029 := hand2 (x 16 2) (x 16 13)
      have b6030 := hb (x 16 13)
      have b6031 := hb (x 16 2 && x 16 13)
      clear * - r6029 b6030 b6031 d6020
      omega
    have d6032 : (x 14 4).toNat = 1 := by
      have r6033 : 1 ≤ (x 18 11).toNat + (x 17 1 && x 17 12).toNat + (x 16 2 && x 16 13).toNat + (x 15 3 && x 15 14).toNat + (x 14 4).toNat := by have q := hcov11 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6034 := hb (x 14 4)
      have b6035 := hb (x 18 11)
      have b6036 := hb (x 17 1 && x 17 12)
      have b6037 := hb (x 16 2 && x 16 13)
      have b6038 := hb (x 15 3 && x 15 14)
      clear * - r6033 b6034 b6035 b6036 b6037 b6038 d5848 d6016 d6028 d5936
      omega
    have d6039 : (x 14 12).toNat = 1 := by
      have r6040 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
      have b6041 := hb (x 14 4)
      have b6042 := hb (x 14 12)
      clear * - r6040 b6041 b6042 d6032
      omega
    have d6043 : (x 13 13).toNat = 0 := by
      have r6044 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6045 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
      have e6046 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
      have b6047 := hb (x 11 3)
      have b6048 := hb (x 12 2)
      have b6049 := hb (x 13 13)
      have b6050 := hb (x 14 12)
      clear * - r6044 e6045 e6046 b6047 b6048 b6049 b6050 d6039
      omega
    have d6051 : (x 13 5).toNat = 0 := by
      have r6052 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
      have b6053 := hb (x 13 5)
      have b6054 := hb (x 13 13)
      clear * - r6052 b6053 b6054 d6043
      omega
    have d6055 : (x 12 2).toNat = 0 := by
      have r6056 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6057 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
      have e6058 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
      have b6059 := hb (x 11 3)
      have b6060 := hb (x 12 2)
      have b6061 := hb (x 13 13)
      have b6062 := hb (x 14 12)
      clear * - r6056 e6057 e6058 b6059 b6060 b6061 b6062 d6039 d6043
      omega
    have d6063 : (x 12 2 && x 12 12).toNat = 0 := by
      have r6064 := hand1 (x 12 2) (x 12 12)
      have b6065 := hb (x 12 2)
      have b6066 := hb (x 12 2 && x 12 12)
      clear * - r6064 b6065 b6066 d6055
      omega
    have d6067 : (x 12 10).toNat = 0 := by
      have r6068 : (x 12 10).toNat ≤ (x 12 2).toNat := himp _ _ (hp10 12)
      have b6069 := hb (x 12 2)
      have b6070 := hb (x 12 10)
      clear * - r6068 b6069 b6070 d6055
      omega
    have d6071 : (x 12 1 && x 12 10).toNat = 0 := by
      have r6072 := hand2 (x 12 1) (x 12 10)
      have b6073 := hb (x 12 10)
      have b6074 := hb (x 12 1 && x 12 10)
      clear * - r6072 b6073 b6074 d6067
      omega
    have d6075 : (x 11 3).toNat = 0 := by
      have r6076 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6077 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
      have e6078 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
      have b6079 := hb (x 11 3)
      have b6080 := hb (x 12 2)
      have b6081 := hb (x 13 13)
      have b6082 := hb (x 14 12)
      clear * - r6076 e6077 e6078 b6079 b6080 b6081 b6082 d6039 d6043 d6055
      omega
    have d6083 : (x 11 3 && x 11 13).toNat = 0 := by
      have r6084 := hand1 (x 11 3) (x 11 13)
      have b6085 := hb (x 11 3)
      have b6086 := hb (x 11 3 && x 11 13)
      clear * - r6084 b6085 b6086 d6075
      omega
    have d6087 : (x 11 11).toNat = 0 := by
      have r6088 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
      have b6089 := hb (x 11 3)
      have b6090 := hb (x 11 11)
      clear * - r6088 b6089 b6090 d6075
      omega
    have d6091 : (x 11 1 && x 11 11).toNat = 0 := by
      have r6092 := hand2 (x 11 1) (x 11 11)
      have b6093 := hb (x 11 11)
      have b6094 := hb (x 11 1 && x 11 11)
      clear * - r6092 b6093 b6094 d6087
      omega
    have d6095 : (x 11 2 && x 11 11).toNat = 0 := by
      have r6096 := hand2 (x 11 2) (x 11 11)
      have b6097 := hb (x 11 11)
      have b6098 := hb (x 11 2 && x 11 11)
      clear * - r6096 b6097 b6098 d6087
      omega
    have d6099 : (x 18 8).toNat = 0 := by
      have r6100 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6101 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
      have e6102 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
      have e6103 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
      have e6104 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
      have e6105 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
      have e6106 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
      have b6107 := hb (x 11 7)
      have b6108 := hb (x 12 6)
      have b6109 := hb (x 13 5)
      have b6110 := hb (x 14 4)
      have b6111 := hb (x 15 11)
      have b6112 := hb (x 16 10)
      have b6113 := hb (x 17 9)
      have b6114 := hb (x 18 8)
      clear * - r6100 e6101 e6102 e6103 e6104 e6105 e6106 b6107 b6108 b6109 b6110 b6111 b6112 b6113 b6114 d6032 d6051
      omega
    have d6115 : (x 17 9).toNat = 0 := by
      have r6116 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6117 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
      have e6118 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
      have e6119 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
      have e6120 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
      have e6121 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
      have e6122 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
      have b6123 := hb (x 11 7)
      have b6124 := hb (x 12 6)
      have b6125 := hb (x 13 5)
      have b6126 := hb (x 14 4)
      have b6127 := hb (x 15 11)
      have b6128 := hb (x 16 10)
      have b6129 := hb (x 17 9)
      have b6130 := hb (x 18 8)
      clear * - r6116 e6117 e6118 e6119 e6120 e6121 e6122 b6123 b6124 b6125 b6126 b6127 b6128 b6129 b6130 d6099 d6032 d6051
      omega
    have d6131 : (x 16 10).toNat = 0 := by
      have r6132 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6133 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
      have e6134 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
      have e6135 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
      have e6136 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
      have e6137 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
      have e6138 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
      have b6139 := hb (x 11 7)
      have b6140 := hb (x 12 6)
      have b6141 := hb (x 13 5)
      have b6142 := hb (x 14 4)
      have b6143 := hb (x 15 11)
      have b6144 := hb (x 16 10)
      have b6145 := hb (x 17 9)
      have b6146 := hb (x 18 8)
      clear * - r6132 e6133 e6134 e6135 e6136 e6137 e6138 b6139 b6140 b6141 b6142 b6143 b6144 b6145 b6146 d6099 d6115 d6032 d6051
      omega
    have d6147 : (x 15 11).toNat = 0 := by
      have r6148 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6149 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
      have e6150 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
      have e6151 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
      have e6152 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
      have e6153 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
      have e6154 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
      have b6155 := hb (x 11 7)
      have b6156 := hb (x 12 6)
      have b6157 := hb (x 13 5)
      have b6158 := hb (x 14 4)
      have b6159 := hb (x 15 11)
      have b6160 := hb (x 16 10)
      have b6161 := hb (x 17 9)
      have b6162 := hb (x 18 8)
      clear * - r6148 e6149 e6150 e6151 e6152 e6153 e6154 b6155 b6156 b6157 b6158 b6159 b6160 b6161 b6162 d6099 d6115 d6131 d6032 d6051
      omega
    have d6163 : (x 12 6).toNat = 0 := by
      have r6164 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6165 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
      have e6166 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
      have e6167 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
      have e6168 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
      have e6169 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
      have e6170 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
      have b6171 := hb (x 11 7)
      have b6172 := hb (x 12 6)
      have b6173 := hb (x 13 5)
      have b6174 := hb (x 14 4)
      have b6175 := hb (x 15 11)
      have b6176 := hb (x 16 10)
      have b6177 := hb (x 17 9)
      have b6178 := hb (x 18 8)
      clear * - r6164 e6165 e6166 e6167 e6168 e6169 e6170 b6171 b6172 b6173 b6174 b6175 b6176 b6177 b6178 d6099 d6115 d6131 d6147 d6032 d6051
      omega
    have d6179 : (x 11 7).toNat = 0 := by
      have r6180 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6181 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
      have e6182 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
      have e6183 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
      have e6184 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
      have e6185 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
      have e6186 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
      have b6187 := hb (x 11 7)
      have b6188 := hb (x 12 6)
      have b6189 := hb (x 13 5)
      have b6190 := hb (x 14 4)
      have b6191 := hb (x 15 11)
      have b6192 := hb (x 16 10)
      have b6193 := hb (x 17 9)
      have b6194 := hb (x 18 8)
      clear * - r6180 e6181 e6182 e6183 e6184 e6185 e6186 b6187 b6188 b6189 b6190 b6191 b6192 b6193 b6194 d6099 d6115 d6131 d6147 d6032 d6051 d6163
      omega
    have d6195 : (x 17 1).toNat = 0 := by
      have r6196 : (x 17 1).toNat + (x 16 2).toNat + (x 15 3).toNat + (x 14 4).toNat + (x 13 5).toNat + (x 12 6).toNat + (x 11 7).toNat + (x 10 8).toNat + (x 9 9).toNat + (x 8 10).toNat + (x 7 11).toNat + (x 6 12).toNat + (x 5 13).toNat + (x 4 14).toNat = 3 := by have q := hcount 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6197 := hb (x 4 14)
      have b6198 := hb (x 5 13)
      have b6199 := hb (x 6 12)
      have b6200 := hb (x 7 11)
      have b6201 := hb (x 8 10)
      have b6202 := hb (x 9 9)
      have b6203 := hb (x 10 8)
      have b6204 := hb (x 11 7)
      have b6205 := hb (x 12 6)
      have b6206 := hb (x 13 5)
      have b6207 := hb (x 14 4)
      have b6208 := hb (x 15 3)
      have b6209 := hb (x 16 2)
      have b6210 := hb (x 17 1)
      clear * - r6196 b6197 b6198 b6199 b6200 b6201 b6202 b6203 b6204 b6205 b6206 b6207 b6208 b6209 b6210 d6032 d6051 d6163 d6179 d5721 d5737 d5753 d5769 d5717 d5144 d5157
      omega
    have d6211 : (x 17 13).toNat = 0 := by
      have r6212 : (x 17 13).toNat ≤ (x 17 1).toNat := himp _ _ (hp13 17)
      have b6213 := hb (x 17 1)
      have b6214 := hb (x 17 13)
      clear * - r6212 b6213 b6214 d6195
      omega
    have d6215 : (x 16 1 && x 16 14).toNat = 1 := by
      have r6216 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := by have q := hcov13 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6217 := hb (x 15 2)
      have b6218 := hb (x 17 13)
      have b6219 := hb (x 16 1 && x 16 14)
      clear * - r6216 b6217 b6218 b6219 d6211 d5940
      omega
    have d6220 : (x 16 14).toNat = 1 := by
      have r6221 := hand2 (x 16 1) (x 16 14)
      have b6222 := hb (x 16 14)
      have b6223 := hb (x 16 1 && x 16 14)
      clear * - r6221 b6222 b6223 d6215
      omega
    have d6224 : (x 15 1).toNat = 0 := by
      have r6225 : (x 16 14).toNat + (x 15 1).toNat = 1 := by have q := hd14 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6226 := hb (x 15 1)
      have b6227 := hb (x 16 14)
      clear * - r6225 b6226 b6227 d6220
      omega
    have d6228 : (x 15 13).toNat = 0 := by
      have r6229 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
      have b6230 := hb (x 15 1)
      have b6231 := hb (x 15 13)
      clear * - r6229 b6230 b6231 d6224
      omega
    have d6232 : (x 15 5).toNat = 0 := by
      have r6233 : (x 15 5).toNat ≤ (x 15 13).toNat := himp _ _ (hp5 15)
      have b6234 := hb (x 15 5)
      have b6235 := hb (x 15 13)
      clear * - r6233 b6234 b6235 d6228
      omega
    have d6236 : (x 14 1 && x 14 6).toNat = 1 := by
      have r6237 : 1 ≤ (x 15 5).toNat + (x 14 1 && x 14 6).toNat + (x 13 2 && x 13 7).toNat + (x 12 3 && x 12 8).toNat + (x 11 4 && x 11 9).toNat + (x 10 5 && x 10 10).toNat + (x 9 6 && x 9 11).toNat + (x 8 7 && x 8 12).toNat + (x 7 8 && x 7 13).toNat + (x 6 9 && x 6 14).toNat + (x 5 10).toNat := by have q := hcov5 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6238 := hb (x 5 10)
      have b6239 := hb (x 15 5)
      have b6240 := hb (x 14 1 && x 14 6)
      have b6241 := hb (x 13 2 && x 13 7)
      have b6242 := hb (x 12 3 && x 12 8)
      have b6243 := hb (x 11 4 && x 11 9)
      have b6244 := hb (x 10 5 && x 10 10)
      have b6245 := hb (x 9 6 && x 9 11)
      have b6246 := hb (x 8 7 && x 8 12)
      have b6247 := hb (x 7 8 && x 7 13)
      have b6248 := hb (x 6 9 && x 6 14)
      clear * - r6237 b6238 b6239 b6240 b6241 b6242 b6243 b6244 b6245 b6246 b6247 b6248 d6232 d5968 d5649 d5364 d5388 d5408 d5189 d4602 d4626 d4630
      omega
    have d6249 : (x 14 6).toNat = 1 := by
      have r6250 := hand2 (x 14 1) (x 14 6)
      have b6251 := hb (x 14 6)
      have b6252 := hb (x 14 1 && x 14 6)
      clear * - r6250 b6251 b6252 d6236
      omega
    have d6253 : (x 14 14).toNat = 1 := by
      have r6254 : (x 14 6).toNat ≤ (x 14 14).toNat := himp _ _ (hp6 14)
      have b6255 := hb (x 14 6)
      have b6256 := hb (x 14 14)
      clear * - r6254 b6255 b6256 d6249
      omega
    have d6257 : (x 13 1).toNat = 0 := by
      have r6258 : (x 14 14).toNat + (x 13 1).toNat = 1 := by have q := hd14 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6259 := hb (x 13 1)
      have b6260 := hb (x 14 14)
      clear * - r6258 b6259 b6260 d6253
      omega
    have d6261 : (x 13 1 && x 13 11).toNat = 0 := by
      have r6262 := hand1 (x 13 1) (x 13 11)
      have b6263 := hb (x 13 1)
      have b6264 := hb (x 13 1 && x 13 11)
      clear * - r6262 b6263 b6264 d6257
      omega
    have d6265 : (x 13 9).toNat = 0 := by
      have r6266 : (x 13 9).toNat ≤ (x 13 1).toNat := himp _ _ (hp9 13)
      have b6267 := hb (x 13 1)
      have b6268 := hb (x 13 9)
      clear * - r6266 b6267 b6268 d6257
      omega
    have d6269 : (x 10 3 && x 10 12).toNat = 1 := by
      have r6270 : 1 ≤ (x 13 9).toNat + (x 12 1 && x 12 10).toNat + (x 11 2 && x 11 11).toNat + (x 10 3 && x 10 12).toNat + (x 9 4 && x 9 13).toNat + (x 8 5 && x 8 14).toNat + (x 7 6).toNat := by have q := hcov9 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6271 := hb (x 7 6)
      have b6272 := hb (x 13 9)
      have b6273 := hb (x 12 1 && x 12 10)
      have b6274 := hb (x 11 2 && x 11 11)
      have b6275 := hb (x 10 3 && x 10 12)
      have b6276 := hb (x 9 4 && x 9 13)
      have b6277 := hb (x 8 5 && x 8 14)
      clear * - r6270 b6271 b6272 b6273 b6274 b6275 b6276 b6277 d6265 d6071 d6095 d4757 d4789 d5229
      omega
    have d6278 : (x 10 12).toNat = 1 := by
      have r6279 := hand2 (x 10 3) (x 10 12)
      have b6280 := hb (x 10 12)
      have b6281 := hb (x 10 3 && x 10 12)
      clear * - r6279 b6280 b6281 d6269
      omega
    have d6282 : (x 9 13).toNat = 0 := by
      have r6283 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6284 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e6285 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b6286 := hb (x 7 3)
      have b6287 := hb (x 8 2)
      have b6288 := hb (x 9 13)
      have b6289 := hb (x 10 12)
      clear * - r6283 e6284 e6285 b6286 b6287 b6288 b6289 d6278
      omega
    have d6290 : (x 9 3 && x 9 13).toNat = 0 := by
      have r6291 := hand2 (x 9 3) (x 9 13)
      have b6292 := hb (x 9 13)
      have b6293 := hb (x 9 3 && x 9 13)
      clear * - r6291 b6292 b6293 d6282
      omega
    have d6294 : (x 10 2 && x 10 12).toNat = 1 := by
      have r6295 : 1 ≤ (x 12 10).toNat + (x 11 1 && x 11 11).toNat + (x 10 2 && x 10 12).toNat + (x 9 3 && x 9 13).toNat + (x 8 4 && x 8 14).toNat + (x 7 5).toNat := by have q := hcov10 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6296 := hb (x 7 5)
      have b6297 := hb (x 12 10)
      have b6298 := hb (x 11 1 && x 11 11)
      have b6299 := hb (x 10 2 && x 10 12)
      have b6300 := hb (x 9 3 && x 9 13)
      have b6301 := hb (x 8 4 && x 8 14)
      clear * - r6295 b6296 b6297 b6298 b6299 b6300 b6301 d6067 d6091 d6290 d5197 d5213
      omega
    have d6302 : (x 10 2).toNat = 1 := by
      have r6303 := hand1 (x 10 2) (x 10 12)
      have b6304 := hb (x 10 2)
      have b6305 := hb (x 10 2 && x 10 12)
      clear * - r6303 b6304 b6305 d6294
      omega
    have d6306 : (x 12 12).toNat = 0 := by
      have r6307 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6308 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
      have e6309 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
      have b6310 := hb (x 9 3)
      have b6311 := hb (x 10 2)
      have b6312 := hb (x 11 13)
      have b6313 := hb (x 12 12)
      clear * - r6307 e6308 e6309 b6310 b6311 b6312 b6313 d6302
      omega
    have d6314 : (x 12 4).toNat = 0 := by
      have r6315 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
      have b6316 := hb (x 12 4)
      have b6317 := hb (x 12 12)
      clear * - r6315 b6316 b6317 d6306
      omega
    have d6318 : (x 11 13).toNat = 0 := by
      have r6319 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6320 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
      have e6321 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
      have b6322 := hb (x 9 3)
      have b6323 := hb (x 10 2)
      have b6324 := hb (x 11 13)
      have b6325 := hb (x 12 12)
      clear * - r6319 e6320 e6321 b6322 b6323 b6324 b6325 d6306 d6302
      omega
    have d6326 : (x 11 5).toNat = 0 := by
      have r6327 : (x 11 5).toNat ≤ (x 11 13).toNat := himp _ _ (hp5 11)
      have b6328 := hb (x 11 5)
      have b6329 := hb (x 11 13)
      clear * - r6327 b6328 b6329 d6318
      omega
    have d6330 : (x 11 5 && x 11 12).toNat = 0 := by
      have r6331 := hand1 (x 11 5) (x 11 12)
      have b6332 := hb (x 11 5)
      have b6333 := hb (x 11 5 && x 11 12)
      clear * - r6331 b6332 b6333 d6326
      omega
    have d6334 : (x 9 5).toNat = 0 := by
      have r6335 : (x 9 5).toNat ≤ (x 9 13).toNat := himp _ _ (hp5 9)
      have b6336 := hb (x 9 5)
      have b6337 := hb (x 9 13)
      clear * - r6335 b6336 b6337 d6282
      omega
    have d6338 : (x 8 1 && x 8 14).toNat = 1 := by
      have r6339 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6340 := hb (x 7 2)
      have b6341 := hb (x 9 13)
      have b6342 := hb (x 8 1 && x 8 14)
      clear * - r6339 b6340 b6341 b6342 d6282 d4793
      omega
    have d6343 : (x 8 14).toNat = 1 := by
      have r6344 := hand2 (x 8 1) (x 8 14)
      have b6345 := hb (x 8 14)
      have b6346 := hb (x 8 1 && x 8 14)
      clear * - r6344 b6345 b6346 d6338
      omega
    have d6347 : (x 7 1).toNat = 0 := by
      have r6348 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6349 := hb (x 7 1)
      have b6350 := hb (x 8 14)
      clear * - r6348 b6349 b6350 d6343
      omega
    have d6351 : (x 7 1 && x 7 7).toNat = 0 := by
      have r6352 := hand1 (x 7 1) (x 7 7)
      have b6353 := hb (x 7 1)
      have b6354 := hb (x 7 1 && x 7 7)
      clear * - r6352 b6353 b6354 d6347
      omega
    have d6355 : (x 8 6).toNat = 1 := by
      have r6356 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6357 := hb (x (-1) 9)
      have b6358 := hb (x 8 6)
      have b6359 := hb (x 7 1 && x 7 7)
      have b6360 := hb (x 6 2 && x 6 8)
      have b6361 := hb (x 5 3 && x 5 9)
      have b6362 := hb (x 4 4 && x 4 10)
      have b6363 := hb (x 3 5 && x 3 11)
      have b6364 := hb (x 2 6 && x 2 12)
      have b6365 := hb (x 1 7 && x 1 13)
      have b6366 := hb (x 0 8 && x 0 14)
      clear * - r6356 b6357 b6358 b6359 b6360 b6361 b6362 b6363 b6364 b6365 b6366 d6351 d3462 d3486 d3514 d3542 d5140 d4918 g24 d3442
      omega
    have d6367 : (x 8 1).toNat = 1 := by
      have r6368 := hand1 (x 8 1) (x 8 14)
      have b6369 := hb (x 8 1)
      have b6370 := hb (x 8 1 && x 8 14)
      clear * - r6368 b6369 b6370 d6338
      omega
    have d6371 : (x 9 14).toNat = 0 := by
      have r6372 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6373 := hb (x 8 1)
      have b6374 := hb (x 9 14)
      clear * - r6372 b6373 b6374 d6367
      omega
    have d6375 : (x 9 7 && x 9 14).toNat = 0 := by
      have r6376 := hand2 (x 9 7) (x 9 14)
      have b6377 := hb (x 9 14)
      have b6378 := hb (x 9 7 && x 9 14)
      clear * - r6376 b6377 b6378 d6371
      omega
    have d6379 : (x 14 8).toNat = 0 := by
      have r6380 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6381 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
      have e6382 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
      have e6383 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
      have e6384 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
      have e6385 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
      have e6386 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
      have b6387 := hb (x 7 7)
      have b6388 := hb (x 8 6)
      have b6389 := hb (x 9 5)
      have b6390 := hb (x 10 4)
      have b6391 := hb (x 11 11)
      have b6392 := hb (x 12 10)
      have b6393 := hb (x 13 9)
      have b6394 := hb (x 14 8)
      clear * - r6380 e6381 e6382 e6383 e6384 e6385 e6386 b6387 b6388 b6389 b6390 b6391 b6392 b6393 b6394 d6265 d6067 d6087 d6334 d6355
      omega
    have d6395 : (x 10 4).toNat = 0 := by
      have r6396 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6397 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
      have e6398 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
      have e6399 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
      have e6400 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
      have e6401 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
      have e6402 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
      have b6403 := hb (x 7 7)
      have b6404 := hb (x 8 6)
      have b6405 := hb (x 9 5)
      have b6406 := hb (x 10 4)
      have b6407 := hb (x 11 11)
      have b6408 := hb (x 12 10)
      have b6409 := hb (x 13 9)
      have b6410 := hb (x 14 8)
      clear * - r6396 e6397 e6398 e6399 e6400 e6401 e6402 b6403 b6404 b6405 b6406 b6407 b6408 b6409 b6410 d6379 d6265 d6067 d6087 d6334 d6355
      omega
    have d6411 : (x 10 4 && x 10 14).toNat = 0 := by
      have r6412 := hand1 (x 10 4) (x 10 14)
      have b6413 := hb (x 10 4)
      have b6414 := hb (x 10 4 && x 10 14)
      clear * - r6412 b6413 b6414 d6395
      omega
    have d6415 : (x 14 10).toNat = 1 := by
      have r6416 : 1 ≤ (x 14 10).toNat + (x 13 1 && x 13 11).toNat + (x 12 2 && x 12 12).toNat + (x 11 3 && x 11 13).toNat + (x 10 4 && x 10 14).toNat + (x 9 5).toNat := by have q := hcov10 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6417 := hb (x 9 5)
      have b6418 := hb (x 14 10)
      have b6419 := hb (x 13 1 && x 13 11)
      have b6420 := hb (x 12 2 && x 12 12)
      have b6421 := hb (x 11 3 && x 11 13)
      have b6422 := hb (x 10 4 && x 10 14)
      clear * - r6416 b6417 b6418 b6419 b6420 b6421 b6422 d6261 d6063 d6083 d6411 d6334
      omega
    have d6423 : (x 16 8).toNat = 0 := by
      have r6424 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6425 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
      have e6426 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
      have e6427 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
      have e6428 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
      have e6429 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
      have e6430 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
      have b6431 := hb (x 9 7)
      have b6432 := hb (x 10 6)
      have b6433 := hb (x 11 5)
      have b6434 := hb (x 12 4)
      have b6435 := hb (x 13 11)
      have b6436 := hb (x 14 10)
      have b6437 := hb (x 15 9)
      have b6438 := hb (x 16 8)
      clear * - r6424 e6425 e6426 e6427 e6428 e6429 e6430 b6431 b6432 b6433 b6434 b6435 b6436 b6437 b6438 d6415 d6314 d6326
      omega
    have d6439 : (x 15 9).toNat = 0 := by
      have r6440 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6441 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
      have e6442 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
      have e6443 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
      have e6444 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
      have e6445 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
      have e6446 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
      have b6447 := hb (x 9 7)
      have b6448 := hb (x 10 6)
      have b6449 := hb (x 11 5)
      have b6450 := hb (x 12 4)
      have b6451 := hb (x 13 11)
      have b6452 := hb (x 14 10)
      have b6453 := hb (x 15 9)
      have b6454 := hb (x 16 8)
      clear * - r6440 e6441 e6442 e6443 e6444 e6445 e6446 b6447 b6448 b6449 b6450 b6451 b6452 b6453 b6454 d6423 d6415 d6314 d6326
      omega
    have d6455 : (x 13 11).toNat = 0 := by
      have r6456 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6457 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
      have e6458 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
      have e6459 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
      have e6460 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
      have e6461 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
      have e6462 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
      have b6463 := hb (x 9 7)
      have b6464 := hb (x 10 6)
      have b6465 := hb (x 11 5)
      have b6466 := hb (x 12 4)
      have b6467 := hb (x 13 11)
      have b6468 := hb (x 14 10)
      have b6469 := hb (x 15 9)
      have b6470 := hb (x 16 8)
      clear * - r6456 e6457 e6458 e6459 e6460 e6461 e6462 b6463 b6464 b6465 b6466 b6467 b6468 b6469 b6470 d6423 d6439 d6415 d6314 d6326
      omega
    have d6471 : (x 10 6).toNat = 0 := by
      have r6472 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6473 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
      have e6474 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
      have e6475 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
      have e6476 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
      have e6477 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
      have e6478 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
      have b6479 := hb (x 9 7)
      have b6480 := hb (x 10 6)
      have b6481 := hb (x 11 5)
      have b6482 := hb (x 12 4)
      have b6483 := hb (x 13 11)
      have b6484 := hb (x 14 10)
      have b6485 := hb (x 15 9)
      have b6486 := hb (x 16 8)
      clear * - r6472 e6473 e6474 e6475 e6476 e6477 e6478 b6479 b6480 b6481 b6482 b6483 b6484 b6485 b6486 d6423 d6439 d6415 d6455 d6314 d6326
      omega
    have d6487 : (x 10 6 && x 10 13).toNat = 0 := by
      have r6488 := hand1 (x 10 6) (x 10 13)
      have b6489 := hb (x 10 6)
      have b6490 := hb (x 10 6 && x 10 13)
      clear * - r6488 b6489 b6490 d6471
      omega
    have d6491 : (x 16 7).toNat = 1 := by
      have r6492 : 1 ≤ (x 16 7).toNat + (x 15 1 && x 15 8).toNat + (x 14 2 && x 14 9).toNat + (x 13 3 && x 13 10).toNat + (x 12 4 && x 12 11).toNat + (x 11 5 && x 11 12).toNat + (x 10 6 && x 10 13).toNat + (x 9 7 && x 9 14).toNat + (x 8 8).toNat := by have q := hcov7 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6493 := hb (x 8 8)
      have b6494 := hb (x 16 7)
      have b6495 := hb (x 15 1 && x 15 8)
      have b6496 := hb (x 14 2 && x 14 9)
      have b6497 := hb (x 13 3 && x 13 10)
      have b6498 := hb (x 12 4 && x 12 11)
      have b6499 := hb (x 11 5 && x 11 12)
      have b6500 := hb (x 10 6 && x 10 13)
      have b6501 := hb (x 9 7 && x 9 14)
      clear * - r6492 b6493 b6494 b6495 b6496 b6497 b6498 b6499 b6500 b6501 d5260 d5284 d5308 d5332 d6330 d6487 d6375 d5072
      omega
    have d6502 : (x 23 8).toNat = 0 := by
      have r6503 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6504 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
      have e6505 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
      have e6506 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
      have e6507 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
      have e6508 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
      have e6509 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
      have b6510 := hb (x 16 7)
      have b6511 := hb (x 17 6)
      have b6512 := hb (x 18 5)
      have b6513 := hb (x 19 4)
      have b6514 := hb (x 20 11)
      have b6515 := hb (x 21 10)
      have b6516 := hb (x 22 9)
      have b6517 := hb (x 23 8)
      clear * - r6503 e6504 e6505 e6506 e6507 e6508 e6509 b6510 b6511 b6512 b6513 b6514 b6515 b6516 b6517 d6491
      omega
    have d6518 : (x 22 9).toNat = 0 := by
      have r6519 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6520 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
      have e6521 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
      have e6522 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
      have e6523 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
      have e6524 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
      have e6525 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
      have b6526 := hb (x 16 7)
      have b6527 := hb (x 17 6)
      have b6528 := hb (x 18 5)
      have b6529 := hb (x 19 4)
      have b6530 := hb (x 20 11)
      have b6531 := hb (x 21 10)
      have b6532 := hb (x 22 9)
      have b6533 := hb (x 23 8)
      clear * - r6519 e6520 e6521 e6522 e6523 e6524 e6525 b6526 b6527 b6528 b6529 b6530 b6531 b6532 b6533 d6502 d6491
      omega
    have d6534 : (x 21 10).toNat = 0 := by
      have r6535 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6536 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
      have e6537 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
      have e6538 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
      have e6539 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
      have e6540 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
      have e6541 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
      have b6542 := hb (x 16 7)
      have b6543 := hb (x 17 6)
      have b6544 := hb (x 18 5)
      have b6545 := hb (x 19 4)
      have b6546 := hb (x 20 11)
      have b6547 := hb (x 21 10)
      have b6548 := hb (x 22 9)
      have b6549 := hb (x 23 8)
      clear * - r6535 e6536 e6537 e6538 e6539 e6540 e6541 b6542 b6543 b6544 b6545 b6546 b6547 b6548 b6549 d6502 d6518 d6491
      omega
    have d6550 : (x 20 11).toNat = 0 := by
      have r6551 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6552 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
      have e6553 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
      have e6554 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
      have e6555 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
      have e6556 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
      have e6557 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
      have b6558 := hb (x 16 7)
      have b6559 := hb (x 17 6)
      have b6560 := hb (x 18 5)
      have b6561 := hb (x 19 4)
      have b6562 := hb (x 20 11)
      have b6563 := hb (x 21 10)
      have b6564 := hb (x 22 9)
      have b6565 := hb (x 23 8)
      clear * - r6551 e6552 e6553 e6554 e6555 e6556 e6557 b6558 b6559 b6560 b6561 b6562 b6563 b6564 b6565 d6502 d6518 d6534 d6491
      omega
    have d6566 : (x 20 1 && x 20 11).toNat = 0 := by
      have r6567 := hand2 (x 20 1) (x 20 11)
      have b6568 := hb (x 20 11)
      have b6569 := hb (x 20 1 && x 20 11)
      clear * - r6567 b6568 b6569 d6550
      omega
    have d6570 : (x 19 4).toNat = 0 := by
      have r6571 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6572 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
      have e6573 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
      have e6574 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
      have e6575 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
      have e6576 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
      have e6577 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
      have b6578 := hb (x 16 7)
      have b6579 := hb (x 17 6)
      have b6580 := hb (x 18 5)
      have b6581 := hb (x 19 4)
      have b6582 := hb (x 20 11)
      have b6583 := hb (x 21 10)
      have b6584 := hb (x 22 9)
      have b6585 := hb (x 23 8)
      clear * - r6571 e6572 e6573 e6574 e6575 e6576 e6577 b6578 b6579 b6580 b6581 b6582 b6583 b6584 b6585 d6502 d6518 d6534 d6550 d6491
      omega
    have d6586 : (x 18 5).toNat = 0 := by
      have r6587 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6588 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
      have e6589 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
      have e6590 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
      have e6591 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
      have e6592 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
      have e6593 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
      have b6594 := hb (x 16 7)
      have b6595 := hb (x 17 6)
      have b6596 := hb (x 18 5)
      have b6597 := hb (x 19 4)
      have b6598 := hb (x 20 11)
      have b6599 := hb (x 21 10)
      have b6600 := hb (x 22 9)
      have b6601 := hb (x 23 8)
      clear * - r6587 e6588 e6589 e6590 e6591 e6592 e6593 b6594 b6595 b6596 b6597 b6598 b6599 b6600 b6601 d6502 d6518 d6534 d6550 d6570 d6491
      omega
    have d6602 : (x 17 6).toNat = 0 := by
      have r6603 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6604 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
      have e6605 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
      have e6606 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
      have e6607 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
      have e6608 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
      have e6609 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
      have b6610 := hb (x 16 7)
      have b6611 := hb (x 17 6)
      have b6612 := hb (x 18 5)
      have b6613 := hb (x 19 4)
      have b6614 := hb (x 20 11)
      have b6615 := hb (x 21 10)
      have b6616 := hb (x 22 9)
      have b6617 := hb (x 23 8)
      clear * - r6603 e6604 e6605 e6606 e6607 e6608 e6609 b6610 b6611 b6612 b6613 b6614 b6615 b6616 b6617 d6502 d6518 d6534 d6550 d6570 d6586 d6491
      omega
    have d6618 : (x 17 2 && x 17 6).toNat = 0 := by
      have r6619 := hand2 (x 17 2) (x 17 6)
      have b6620 := hb (x 17 6)
      have b6621 := hb (x 17 2 && x 17 6)
      clear * - r6619 b6620 b6621 d6602
      omega
    have d6622 : (x 16 3 && x 16 7).toNat = 1 := by
      have r6623 : 1 ≤ (x 19 4).toNat + (x 18 1 && x 18 5).toNat + (x 17 2 && x 17 6).toNat + (x 16 3 && x 16 7).toNat + (x 15 4 && x 15 8).toNat + (x 14 5 && x 14 9).toNat + (x 13 6 && x 13 10).toNat + (x 12 7 && x 12 11).toNat + (x 11 8 && x 11 12).toNat + (x 10 9 && x 10 13).toNat + (x 9 10 && x 9 14).toNat + (x 8 11).toNat := by have q := hcov4 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6624 : (x 18 1 && x 18 5).toNat = (x 18 5).toNat := handr _ _ (fun h => hp13 18 (hp5 18 (h)))
      have e6625 : (x 9 10 && x 9 14).toNat = (x 9 10).toNat := handl _ _ (fun h => hp2 9 (hp10 9 (h)))
      have b6626 := hb (x 8 11)
      have b6627 := hb (x 9 10)
      have b6628 := hb (x 18 5)
      have b6629 := hb (x 19 4)
      have b6630 := hb (x 17 2 && x 17 6)
      have b6631 := hb (x 16 3 && x 16 7)
      have b6632 := hb (x 15 4 && x 15 8)
      have b6633 := hb (x 14 5 && x 14 9)
      have b6634 := hb (x 13 6 && x 13 10)
      have b6635 := hb (x 12 7 && x 12 11)
      have b6636 := hb (x 11 8 && x 11 12)
      have b6637 := hb (x 10 9 && x 10 13)
      clear * - r6623 e6624 e6625 b6626 b6627 b6628 b6629 b6630 b6631 b6632 b6633 b6634 b6635 b6636 b6637 d6570 d6586 d6618 d5264 d5288 d5312 d5336 d5564 d5584 d5588 d5604
      omega
    have d6638 : (x 16 3).toNat = 1 := by
      have r6639 := hand1 (x 16 3) (x 16 7)
      have b6640 := hb (x 16 3)
      have b6641 := hb (x 16 3 && x 16 7)
      clear * - r6639 b6640 b6641 d6622
      omega
    have d6642 : (x 19 12).toNat = 0 := by
      have r6643 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6644 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
      have e6645 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
      have b6646 := hb (x 16 3)
      have b6647 := hb (x 17 2)
      have b6648 := hb (x 18 13)
      have b6649 := hb (x 19 12)
      clear * - r6643 e6644 e6645 b6646 b6647 b6648 b6649 d6638
      omega
    have d6650 : (x 19 2 && x 19 12).toNat = 0 := by
      have r6651 := hand2 (x 19 2) (x 19 12)
      have b6652 := hb (x 19 12)
      have b6653 := hb (x 19 2 && x 19 12)
      clear * - r6651 b6652 b6653 d6642
      omega
    have d6654 : (x 18 3 && x 18 13).toNat = 1 := by
      have r6655 : 1 ≤ (x 21 10).toNat + (x 20 1 && x 20 11).toNat + (x 19 2 && x 19 12).toNat + (x 18 3 && x 18 13).toNat + (x 17 4 && x 17 14).toNat + (x 16 5).toNat := by have q := hcov10 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6656 := hb (x 16 5)
      have b6657 := hb (x 21 10)
      have b6658 := hb (x 20 1 && x 20 11)
      have b6659 := hb (x 19 2 && x 19 12)
      have b6660 := hb (x 18 3 && x 18 13)
      have b6661 := hb (x 17 4 && x 17 14)
      clear * - r6655 b6656 b6657 b6658 b6659 b6660 b6661 d6534 d6566 d6650 d5880 d5884
      omega
    have d6662 : (x 18 13).toNat = 1 := by
      have r6663 := hand2 (x 18 3) (x 18 13)
      have b6664 := hb (x 18 13)
      have b6665 := hb (x 18 3 && x 18 13)
      clear * - r6663 b6664 b6665 d6654
      omega
    have r6666 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6667 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e6668 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have b6669 := hb (x 16 3)
    have b6670 := hb (x 17 2)
    have b6671 := hb (x 18 13)
    have b6672 := hb (x 19 12)
    linarith only [r6666, e6667, e6668, b6669, b6670, b6671, b6672, d6642, d6662, d6638]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b0001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-4) 5).toNat = 0)
    (g1 : (x 0 5).toNat = 1)
    (g2 : (x 1 10).toNat = 0)
    (g3 : (x 0 1 && x 0 11).toNat = 0)
    (g4 : (x (-3) 4 && x (-3) 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d6674 : (x 0 13).toNat = 1 := by
    have r6675 : (x 0 5).toNat ≤ (x 0 13).toNat := himp _ _ (hp5 0)
    have b6676 := hb (x 0 5)
    have b6677 := hb (x 0 13)
    clear * - r6675 b6676 b6677 g1
    omega
  have d6678 : (x 1 12).toNat = 0 := by
    have r6679 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6680 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e6681 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b6682 := hb (x (-2) 3)
    have b6683 := hb (x (-1) 2)
    have b6684 := hb (x 0 13)
    have b6685 := hb (x 1 12)
    clear * - r6679 e6680 e6681 b6682 b6683 b6684 b6685 d6674
    omega
  have d6686 : (x (-1) 2).toNat = 0 := by
    have r6687 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6688 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e6689 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b6690 := hb (x (-2) 3)
    have b6691 := hb (x (-1) 2)
    have b6692 := hb (x 0 13)
    have b6693 := hb (x 1 12)
    clear * - r6687 e6688 e6689 b6690 b6691 b6692 b6693 d6678 d6674
    omega
  have d6694 : (x (-1) 2 && x (-1) 12).toNat = 0 := by
    have r6695 := hand1 (x (-1) 2) (x (-1) 12)
    have b6696 := hb (x (-1) 2)
    have b6697 := hb (x (-1) 2 && x (-1) 12)
    clear * - r6695 b6696 b6697 d6686
    omega
  have d6698 : (x (-2) 3).toNat = 0 := by
    have r6699 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6700 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e6701 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b6702 := hb (x (-2) 3)
    have b6703 := hb (x (-1) 2)
    have b6704 := hb (x 0 13)
    have b6705 := hb (x 1 12)
    clear * - r6699 e6700 e6701 b6702 b6703 b6704 b6705 d6678 d6674 d6686
    omega
  have d6706 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
    have r6707 := hand1 (x (-2) 3) (x (-2) 13)
    have b6708 := hb (x (-2) 3)
    have b6709 := hb (x (-2) 3 && x (-2) 13)
    clear * - r6707 b6708 b6709 d6698
    omega
  have r6710 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have b6711 := hb (x (-4) 5)
  have b6712 := hb (x 1 10)
  have b6713 := hb (x 0 1 && x 0 11)
  have b6714 := hb (x (-1) 2 && x (-1) 12)
  have b6715 := hb (x (-2) 3 && x (-2) 13)
  have b6716 := hb (x (-3) 4 && x (-3) 14)
  linarith only [r6710, b6711, b6712, b6713, b6714, b6715, b6716, g2, g3, d6694, d6706, g4, g0]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-4) 5).toNat = 0)
    (g1 : (x 0 4).toNat = 1)
    (g2 : (x 1 10).toNat = 0)
    (g3 : (x 0 1 && x 0 11).toNat = 0)
    (g4 : (x (-3) 4 && x (-3) 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d6718 : (x 0 12).toNat = 1 := by
    have r6719 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
    have b6720 := hb (x 0 4)
    have b6721 := hb (x 0 12)
    clear * - r6719 b6720 b6721 g1
    omega
  have d6722 : (x (-1) 13).toNat = 0 := by
    have r6723 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6724 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e6725 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b6726 := hb (x (-3) 3)
    have b6727 := hb (x (-2) 2)
    have b6728 := hb (x (-1) 13)
    have b6729 := hb (x 0 12)
    clear * - r6723 e6724 e6725 b6726 b6727 b6728 b6729 d6718
    omega
  have d6730 : (x (-2) 2).toNat = 0 := by
    have r6731 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6732 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e6733 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b6734 := hb (x (-3) 3)
    have b6735 := hb (x (-2) 2)
    have b6736 := hb (x (-1) 13)
    have b6737 := hb (x 0 12)
    clear * - r6731 e6732 e6733 b6734 b6735 b6736 b6737 d6718 d6722
    omega
  have r6738 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e6739 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
  have e6740 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
  have r6741 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e6742 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
  have e6743 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
  have r6744 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r6745 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r6746 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r6747 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r6748 := hand1 (x (-1) 2) (x (-1) 12)
  have r6749 := hand2 (x (-1) 2) (x (-1) 12)
  have r6750 := hand1 (x (-2) 3) (x (-2) 13)
  have r6751 := hand2 (x (-2) 3) (x (-2) 13)
  have r6752 := hand1 (x (-2) 1) (x (-2) 14)
  have r6753 := hand2 (x (-1) 1) (x (-1) 14)
  linarith only [r6738, e6739, e6740, r6741, e6742, e6743, r6744, r6745, r6746, r6747, r6748, r6749, r6750, r6751, r6752, r6753, g0, d6730, d6722, g2, g3, g4]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b01_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-4) 5).toNat = 0)
    (g1 : (x (-2) 11).toNat = 0)
    (g2 : (x 0 2).toNat = 1)
    (g3 : (x 1 10).toNat = 0)
    (g4 : (x (-3) 4 && x (-3) 9).toNat = 0)
    (g5 : (x (-4) 5 && x (-4) 10).toNat = 0)
    (g6 : (x (-5) 6 && x (-5) 11).toNat = 0)
    (g7 : (x (-6) 7 && x (-6) 12).toNat = 0)
    (g8 : (x 0 1 && x 0 11).toNat = 0)
    (g9 : (x (-3) 4 && x (-3) 14).toNat = 0)
    (g10 : (x 1 2 && x 1 13).toNat = 0)
    (g11 : (x 0 3 && x 0 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d6775 : (x 0 14).toNat = 1 := by
    have r6776 : (x 0 2).toNat ≤ (x 0 14).toNat := himp _ _ (hp2 0)
    have b6777 := hb (x 0 2)
    have b6778 := hb (x 0 14)
    clear * - r6776 b6777 b6778 g2
    omega
  have d6779 : (x (-1) 1).toNat = 0 := by
    have r6780 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6781 := hb (x (-1) 1)
    have b6782 := hb (x 0 14)
    clear * - r6780 b6781 b6782 d6775
    omega
  have d6783 : (x (-1) 1 && x (-1) 14).toNat = 0 := by
    have r6784 := hand1 (x (-1) 1) (x (-1) 14)
    have b6785 := hb (x (-1) 1)
    have b6786 := hb (x (-1) 1 && x (-1) 14)
    clear * - r6784 b6785 b6786 d6779
    omega
  have d6787 : (x (-1) 13).toNat = 0 := by
    have r6788 : (x (-1) 13).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp13 (-1))
    have b6789 := hb (x (-1) 1)
    have b6790 := hb (x (-1) 13)
    clear * - r6788 b6789 b6790 d6779
    omega
  have d6791 : (x (-1) 5).toNat = 0 := by
    have r6792 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
    have b6793 := hb (x (-1) 5)
    have b6794 := hb (x (-1) 13)
    clear * - r6792 b6793 b6794 d6787
    omega
  have d6795 : (x 2 12).toNat = 0 := by
    have r6796 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6797 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e6798 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b6799 := hb (x (-1) 3)
    have b6800 := hb (x 0 2)
    have b6801 := hb (x 1 13)
    have b6802 := hb (x 2 12)
    clear * - r6796 e6797 e6798 b6799 b6800 b6801 b6802 g2
    omega
  have d6803 : (x 2 1 && x 2 12).toNat = 0 := by
    have r6804 := hand2 (x 2 1) (x 2 12)
    have b6805 := hb (x 2 12)
    have b6806 := hb (x 2 1 && x 2 12)
    clear * - r6804 b6805 b6806 d6795
    omega
  have d6807 : (x 2 2 && x 2 12).toNat = 0 := by
    have r6808 := hand2 (x 2 2) (x 2 12)
    have b6809 := hb (x 2 12)
    have b6810 := hb (x 2 2 && x 2 12)
    clear * - r6808 b6809 b6810 d6795
    omega
  have d6811 : (x 2 4).toNat = 0 := by
    have r6812 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
    have b6813 := hb (x 2 4)
    have b6814 := hb (x 2 12)
    clear * - r6812 b6813 b6814 d6795
    omega
  have d6815 : (x 1 13).toNat = 0 := by
    have r6816 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6817 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e6818 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b6819 := hb (x (-1) 3)
    have b6820 := hb (x 0 2)
    have b6821 := hb (x 1 13)
    have b6822 := hb (x 2 12)
    clear * - r6816 e6817 e6818 b6819 b6820 b6821 b6822 d6795 g2
    omega
  have d6823 : (x 1 3 && x 1 13).toNat = 0 := by
    have r6824 := hand2 (x 1 3) (x 1 13)
    have b6825 := hb (x 1 13)
    have b6826 := hb (x 1 3 && x 1 13)
    clear * - r6824 b6825 b6826 d6815
    omega
  have d6827 : (x 1 5).toNat = 0 := by
    have r6828 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
    have b6829 := hb (x 1 5)
    have b6830 := hb (x 1 13)
    clear * - r6828 b6829 b6830 d6815
    omega
  have d6831 : (x (-1) 3).toNat = 0 := by
    have r6832 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6833 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e6834 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b6835 := hb (x (-1) 3)
    have b6836 := hb (x 0 2)
    have b6837 := hb (x 1 13)
    have b6838 := hb (x 2 12)
    clear * - r6832 e6833 e6834 b6835 b6836 b6837 b6838 d6795 d6815 g2
    omega
  have d6839 : (x (-1) 3 && x (-1) 14).toNat = 0 := by
    have r6840 := hand1 (x (-1) 3) (x (-1) 14)
    have b6841 := hb (x (-1) 3)
    have b6842 := hb (x (-1) 3 && x (-1) 14)
    clear * - r6840 b6841 b6842 d6831
    omega
  have d6843 : (x (-1) 3 && x (-1) 7).toNat = 0 := by
    have r6844 := hand1 (x (-1) 3) (x (-1) 7)
    have b6845 := hb (x (-1) 3)
    have b6846 := hb (x (-1) 3 && x (-1) 7)
    clear * - r6844 b6845 b6846 d6831
    omega
  cases h6847 : x 0 4
  · have f6848 : (x 0 4).toNat = 0 := by rw [h6847]; rfl
    have d6849 : (x 0 4 && x 0 14).toNat = 0 := by
      have r6850 := hand1 (x 0 4) (x 0 14)
      have b6851 := hb (x 0 4)
      have b6852 := hb (x 0 4 && x 0 14)
      clear * - r6850 b6851 b6852 f6848
      omega
    cases h6853 : x 0 6
    · have f6854 : (x 0 6).toNat = 0 := by rw [h6853]; rfl
      have d6855 : (x 0 1 && x 0 6).toNat = 0 := by
        have r6856 := hand2 (x 0 1) (x 0 6)
        have b6857 := hb (x 0 6)
        have b6858 := hb (x 0 1 && x 0 6)
        clear * - r6856 b6857 b6858 f6854
        omega
      have d6859 : (x 0 2 && x 0 6).toNat = 0 := by
        have r6860 := hand2 (x 0 2) (x 0 6)
        have b6861 := hb (x 0 6)
        have b6862 := hb (x 0 2 && x 0 6)
        clear * - r6860 b6861 b6862 f6854
        omega
      have r6863 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r6864 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6865 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
      have e6866 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
      have e6867 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
      have e6868 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
      have e6869 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
      have e6870 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
      have r6871 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6872 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
      have e6873 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
      have e6874 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
      have e6875 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
      have e6876 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
      have e6877 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
      have r6878 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6879 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e6880 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e6881 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e6882 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e6883 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e6884 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have r6885 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6886 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
      have e6887 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
      have r6888 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6889 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e6890 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have r6891 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6892 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e6893 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have r6894 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6895 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e6896 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have r6897 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6898 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e6899 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have r6900 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6901 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e6902 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have r6903 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r6904 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r6905 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r6906 : 1 ≤ (x 2 4).toNat + (x 1 1 && x 1 5).toNat + (x 0 2 && x 0 6).toNat + (x (-1) 3 && x (-1) 7).toNat + (x (-2) 4 && x (-2) 8).toNat + (x (-3) 5 && x (-3) 9).toNat + (x (-4) 6 && x (-4) 10).toNat + (x (-5) 7 && x (-5) 11).toNat + (x (-6) 8 && x (-6) 12).toNat + (x (-7) 9 && x (-7) 13).toNat + (x (-8) 10 && x (-8) 14).toNat + (x (-9) 11).toNat := by have q := hcov4 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6907 : (x 1 1 && x 1 5).toNat = (x 1 5).toNat := handr _ _ (fun h => hp13 1 (hp5 1 (h)))
      have e6908 : (x (-8) 10 && x (-8) 14).toNat = (x (-8) 10).toNat := handl _ _ (fun h => hp2 (-8) (hp10 (-8) (h)))
      have r6909 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := by have q := hcov5 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r6910 : 1 ≤ (x (-7) 9).toNat + (x (-8) 1 && x (-8) 10).toNat + (x (-9) 2 && x (-9) 11).toNat + (x (-10) 3 && x (-10) 12).toNat + (x (-11) 4 && x (-11) 13).toNat + (x (-12) 5 && x (-12) 14).toNat + (x (-13) 6).toNat := by have q := hcov9 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r6911 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r6912 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r6913 : 1 ≤ (x (-2) 11).toNat + (x (-3) 1 && x (-3) 12).toNat + (x (-4) 2 && x (-4) 13).toNat + (x (-5) 3 && x (-5) 14).toNat + (x (-6) 4).toNat := by have q := hcov11 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r6914 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := by have q := hcov11 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r6915 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r6916 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r6917 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r6918 : (x (-9) 11).toNat ≤ (x (-9) 3).toNat := himp _ _ (hp11 (-9))
      have r6919 : (x (-8) 10).toNat ≤ (x (-8) 2).toNat := himp _ _ (hp10 (-8))
      have r6920 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
      have r6921 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
      have r6922 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
      have r6923 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
      have r6924 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
      have r6925 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
      have r6926 := hand2 (x (-2) 4) (x (-2) 8)
      have r6927 := hand2 (x (-3) 5) (x (-3) 9)
      have r6928 := hand2 (x (-4) 6) (x (-4) 10)
      have r6929 := hand1 (x (-5) 7) (x (-5) 11)
      have r6930 := hand1 (x (-6) 8) (x (-6) 12)
      have r6931 := hand2 (x (-7) 9) (x (-7) 13)
      have r6932 := hand2 (x (-1) 2) (x (-1) 7)
      have r6933 := hand2 (x (-2) 3) (x (-2) 8)
      have r6934 := hand1 (x (-7) 8) (x (-7) 13)
      have r6935 := hand1 (x (-8) 9) (x (-8) 14)
      have r6936 := hand2 (x (-8) 1) (x (-8) 10)
      have r6937 := hand2 (x (-9) 2) (x (-9) 11)
      have r6938 := hand2 (x (-10) 3) (x (-10) 12)
      have r6939 := hand1 (x (-11) 4) (x (-11) 13)
      have r6940 := hand1 (x (-12) 5) (x (-12) 14)
      have r6941 := hand1 (x (-1) 2) (x (-1) 12)
      have r6942 := hand2 (x (-1) 2) (x (-1) 12)
      have r6943 := hand1 (x (-2) 3) (x (-2) 13)
      have r6944 := hand2 (x (-2) 3) (x (-2) 13)
      have r6945 := hand1 (x 3 1) (x 3 11)
      have r6946 := hand1 (x (-3) 1) (x (-3) 12)
      have r6947 := hand1 (x (-4) 2) (x (-4) 13)
      have r6948 := hand1 (x (-5) 3) (x (-5) 14)
      have r6949 := hand2 (x 1 1) (x 1 12)
      have r6950 := hand2 (x 0 2) (x 0 13)
      have r6951 := hand1 (x (-2) 1) (x (-2) 14)
      have r6952 := hand2 (x (-2) 1) (x (-2) 14)
      have r6953 := hand2 (x 4 1) (x 4 14)
      linarith only [r6863, r6864, e6865, e6866, e6867, e6868, e6869, e6870, r6871, e6872, e6873, e6874, e6875, e6876, e6877, r6878, e6879, e6880, e6881, e6882, e6883, e6884, r6885, e6886, e6887, r6888, e6889, e6890, r6891, e6892, e6893, r6894, e6895, e6896, r6897, e6898, e6899, r6900, e6901, e6902, r6903, r6904, r6905, r6906, e6907, e6908, r6909, r6910, r6911, r6912, r6913, r6914, r6915, r6916, r6917, r6918, r6919, r6920, r6921, r6922, r6923, r6924, r6925, r6926, r6927, r6928, r6929, r6930, r6931, r6932, r6933, r6934, r6935, r6936, r6937, r6938, r6939, r6940, r6941, r6942, r6943, r6944, r6945, r6946, r6947, r6948, r6949, r6950, r6951, r6952, r6953, g0, g1, d6831, d6791, d6787, g2, f6854, d6827, g3, d6811, d6859, d6843, d6855, g4, g5, g6, g7, g8, g9, d6807, d6823, d6849, d6839, d6803, g10, g11]
    · have f7070 : (x 0 6).toNat = 1 := by rw [h6853]; rfl
      have d7071 : (x 6 8).toNat = 0 := by
        have r7072 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e7073 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e7074 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e7075 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e7076 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e7077 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e7078 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b7079 := hb (x (-1) 7)
        have b7080 := hb (x 0 6)
        have b7081 := hb (x 1 5)
        have b7082 := hb (x 2 4)
        have b7083 := hb (x 3 11)
        have b7084 := hb (x 4 10)
        have b7085 := hb (x 5 9)
        have b7086 := hb (x 6 8)
        clear * - r7072 e7073 e7074 e7075 e7076 e7077 e7078 b7079 b7080 b7081 b7082 b7083 b7084 b7085 b7086 d6811 d6827 f7070
        omega
      have d7087 : (x 5 9).toNat = 0 := by
        have r7088 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e7089 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e7090 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e7091 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e7092 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e7093 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e7094 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b7095 := hb (x (-1) 7)
        have b7096 := hb (x 0 6)
        have b7097 := hb (x 1 5)
        have b7098 := hb (x 2 4)
        have b7099 := hb (x 3 11)
        have b7100 := hb (x 4 10)
        have b7101 := hb (x 5 9)
        have b7102 := hb (x 6 8)
        clear * - r7088 e7089 e7090 e7091 e7092 e7093 e7094 b7095 b7096 b7097 b7098 b7099 b7100 b7101 b7102 d7071 d6811 d6827 f7070
        omega
      have d7103 : (x 4 10).toNat = 0 := by
        have r7104 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e7105 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e7106 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e7107 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e7108 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e7109 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e7110 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b7111 := hb (x (-1) 7)
        have b7112 := hb (x 0 6)
        have b7113 := hb (x 1 5)
        have b7114 := hb (x 2 4)
        have b7115 := hb (x 3 11)
        have b7116 := hb (x 4 10)
        have b7117 := hb (x 5 9)
        have b7118 := hb (x 6 8)
        clear * - r7104 e7105 e7106 e7107 e7108 e7109 e7110 b7111 b7112 b7113 b7114 b7115 b7116 b7117 b7118 d7071 d7087 d6811 d6827 f7070
        omega
      have d7119 : (x 3 1 && x 3 11).toNat = 1 := by
        have r7120 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b7121 := hb (x (-1) 5)
        have b7122 := hb (x 4 10)
        have b7123 := hb (x 3 1 && x 3 11)
        have b7124 := hb (x 2 2 && x 2 12)
        have b7125 := hb (x 1 3 && x 1 13)
        have b7126 := hb (x 0 4 && x 0 14)
        clear * - r7120 b7121 b7122 b7123 b7124 b7125 b7126 d7103 d6807 d6823 d6849 d6791
        omega
      have d7127 : (x 3 11).toNat = 1 := by
        have r7128 := hand2 (x 3 1) (x 3 11)
        have b7129 := hb (x 3 11)
        have b7130 := hb (x 3 1 && x 3 11)
        clear * - r7128 b7129 b7130 d7119
        omega
      have r7131 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7132 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e7133 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e7134 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e7135 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e7136 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e7137 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b7138 := hb (x (-1) 7)
      have b7139 := hb (x 0 6)
      have b7140 := hb (x 1 5)
      have b7141 := hb (x 2 4)
      have b7142 := hb (x 3 11)
      have b7143 := hb (x 4 10)
      have b7144 := hb (x 5 9)
      have b7145 := hb (x 6 8)
      linarith only [r7131, e7132, e7133, e7134, e7135, e7136, e7137, b7138, b7139, b7140, b7141, b7142, b7143, b7144, b7145, d7071, d7087, d7103, d7127, d6811, d6827, f7070]
  · have f7146 : (x 0 4).toNat = 1 := by rw [h6847]; rfl
    have d7147 : (x 0 12).toNat = 1 := by
      have r7148 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
      have b7149 := hb (x 0 4)
      have b7150 := hb (x 0 12)
      clear * - r7148 b7149 b7150 f7146
      omega
    have d7151 : (x (-2) 2).toNat = 0 := by
      have r7152 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7153 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e7154 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have b7155 := hb (x (-3) 3)
      have b7156 := hb (x (-2) 2)
      have b7157 := hb (x (-1) 13)
      have b7158 := hb (x 0 12)
      clear * - r7152 e7153 e7154 b7155 b7156 b7157 b7158 d7147 d6787
      omega
    have d7159 : (x 0 13).toNat = 1 := by
      have r7160 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7161 := hb (x (-2) 2)
      have b7162 := hb (x 0 13)
      have b7163 := hb (x (-1) 1 && x (-1) 14)
      clear * - r7160 b7161 b7162 b7163 d6783 d7151
      omega
    have d7164 : (x 1 12).toNat = 0 := by
      have r7165 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7166 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e7167 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b7168 := hb (x (-2) 3)
      have b7169 := hb (x (-1) 2)
      have b7170 := hb (x 0 13)
      have b7171 := hb (x 1 12)
      clear * - r7165 e7166 e7167 b7168 b7169 b7170 b7171 d7159
      omega
    have d7172 : (x (-1) 2).toNat = 0 := by
      have r7173 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7174 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e7175 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b7176 := hb (x (-2) 3)
      have b7177 := hb (x (-1) 2)
      have b7178 := hb (x 0 13)
      have b7179 := hb (x 1 12)
      clear * - r7173 e7174 e7175 b7176 b7177 b7178 b7179 d7164 d7159
      omega
    have d7180 : (x (-1) 2 && x (-1) 12).toNat = 0 := by
      have r7181 := hand1 (x (-1) 2) (x (-1) 12)
      have b7182 := hb (x (-1) 2)
      have b7183 := hb (x (-1) 2 && x (-1) 12)
      clear * - r7181 b7182 b7183 d7172
      omega
    have d7184 : (x (-2) 3).toNat = 0 := by
      have r7185 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7186 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e7187 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b7188 := hb (x (-2) 3)
      have b7189 := hb (x (-1) 2)
      have b7190 := hb (x 0 13)
      have b7191 := hb (x 1 12)
      clear * - r7185 e7186 e7187 b7188 b7189 b7190 b7191 d7164 d7159 d7172
      omega
    have d7192 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
      have r7193 := hand1 (x (-2) 3) (x (-2) 13)
      have b7194 := hb (x (-2) 3)
      have b7195 := hb (x (-2) 3 && x (-2) 13)
      clear * - r7193 b7194 b7195 d7184
      omega
    have r7196 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7197 := hb (x (-4) 5)
    have b7198 := hb (x 1 10)
    have b7199 := hb (x 0 1 && x 0 11)
    have b7200 := hb (x (-1) 2 && x (-1) 12)
    have b7201 := hb (x (-2) 3 && x (-2) 13)
    have b7202 := hb (x (-3) 4 && x (-3) 14)
    linarith only [r7196, b7197, b7198, b7199, b7200, b7201, b7202, g3, g8, d7180, d7192, g9, g0]

theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b01 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-4) 5).toNat = 0)
    (g1 : (x (-2) 11).toNat = 0)
    (g2 : (x 0 2).toNat = 1)
    (g3 : (x 1 10).toNat = 0)
    (g4 : (x (-3) 4 && x (-3) 9).toNat = 0)
    (g5 : (x (-4) 5 && x (-4) 10).toNat = 0)
    (g6 : (x (-5) 6 && x (-5) 11).toNat = 0)
    (g7 : (x (-6) 7 && x (-6) 12).toNat = 0)
    (g8 : (x 0 1 && x 0 11).toNat = 0)
    (g9 : (x (-3) 4 && x (-3) 14).toNat = 0)
    (g10 : (x 1 2 && x 1 13).toNat = 0)
    (g11 : (x 0 3 && x 0 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b01_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11
