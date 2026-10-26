import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b0000100

Topic: combinatorics   Node: 951d2fe6c209

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core: under the layer-free tight-cover constraints for k = 15 and 58 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b0000100_aux (x : ℤ → Fin 16 → Bool)
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
    (g3 : (x (-2) 14).toNat = 1)
    (g4 : (x (-1) 5).toNat = 0)
    (g5 : (x (-1) 9).toNat = 0)
    (g6 : (x (-1) 13).toNat = 0)
    (g7 : (x 0 2).toNat = 0)
    (g8 : (x 0 3).toNat = 0)
    (g9 : (x 0 4).toNat = 0)
    (g10 : (x 0 5).toNat = 0)
    (g11 : (x 0 7).toNat = 0)
    (g12 : (x 0 10).toNat = 0)
    (g13 : (x 0 11).toNat = 0)
    (g14 : (x 0 12).toNat = 0)
    (g15 : (x 0 13).toNat = 0)
    (g16 : (x 0 14).toNat = 1)
    (g17 : (x 1 3).toNat = 1)
    (g18 : (x 1 4).toNat = 0)
    (g19 : (x 1 8).toNat = 0)
    (g20 : (x 2 2).toNat = 0)
    (g21 : (x 2 10).toNat = 0)
    (g22 : (x 3 5).toNat = 0)
    (g23 : (x 3 13).toNat = 0)
    (g24 : (x 4 4).toNat = 0)
    (g25 : (x 2 2 && x 2 3).toNat = 0)
    (g26 : (x 0 4 && x 0 5).toNat = 0)
    (g27 : (x (-1) 5 && x (-1) 6).toNat = 0)
    (g28 : (x 0 13 && x 0 14).toNat = 0)
    (g29 : (x 4 4 && x 4 10).toNat = 0)
    (g30 : (x 3 5 && x 3 11).toNat = 0)
    (g31 : (x 0 8 && x 0 14).toNat = 0)
    (g32 : (x 4 5 && x 4 12).toNat = 0)
    (g33 : (x 3 6 && x 3 13).toNat = 0)
    (g34 : (x 2 2 && x 2 11).toNat = 0)
    (g35 : (x 0 4 && x 0 13).toNat = 0)
    (g36 : (x (-1) 5 && x (-1) 14).toNat = 0)
    (g37 : (x 0 5 && x 0 14).toNat = 0)
    (g38 : (x 4 3 && x 4 12).toNat = 0)
    (g39 : (x 3 4 && x 3 13).toNat = 0)
    (g40 : (x 4 4 && x 4 13).toNat = 0)
    (g41 : (x 3 5 && x 3 14).toNat = 0)
    (g42 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g43 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g44 : (x 0 2 && x 0 12).toNat = 0)
    (g45 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g46 : (x 2 2 && x 2 12).toNat = 0)
    (g47 : (x 0 4 && x 0 14).toNat = 0)
    (g48 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g49 : (x (-3) 3 && x (-3) 14).toNat = 0)
    (g50 : (x 0 1 && x 0 12).toNat = 0)
    (g51 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g52 : (x 0 2 && x 0 13).toNat = 0)
    (g53 : (x 0 3 && x 0 14).toNat = 0)
    (g54 : (x 4 1 && x 4 12).toNat = 0)
    (g55 : (x 3 2 && x 3 13).toNat = 0)
    (g56 : (x (-3) 1 && x (-3) 14).toNat = 0)
    (g57 : (x 0 1 && x 0 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d4446 : (x 1 4 && x 1 14).toNat = 0 := by
    have r4447 := hand1 (x 1 4) (x 1 14)
    have b4448 := hb (x 1 4)
    have b4449 := hb (x 1 4 && x 1 14)
    clear * - r4447 b4448 b4449 g18
    omega
  have d4450 : (x 1 4 && x 1 13).toNat = 0 := by
    have r4451 := hand1 (x 1 4) (x 1 13)
    have b4452 := hb (x 1 4)
    have b4453 := hb (x 1 4 && x 1 13)
    clear * - r4451 b4452 b4453 g18
    omega
  have d4454 : (x 1 3 && x 1 4).toNat = 0 := by
    have r4455 := hand2 (x 1 3) (x 1 4)
    have b4456 := hb (x 1 4)
    have b4457 := hb (x 1 3 && x 1 4)
    clear * - r4455 b4456 b4457 g18
    omega
  cases h4458 : x 0 6
  · have f4459 : (x 0 6).toNat = 0 := by rw [h4458]; rfl
    cases h4460 : x 1 1
    · have f4461 : (x 1 1).toNat = 0 := by rw [h4460]; rfl
      have d4462 : (x 1 1 && x 1 14).toNat = 0 := by
        have r4463 := hand1 (x 1 1) (x 1 14)
        have b4464 := hb (x 1 1)
        have b4465 := hb (x 1 1 && x 1 14)
        clear * - r4463 b4464 b4465 f4461
        omega
      have d4466 : (x 1 1 && x 1 12).toNat = 0 := by
        have r4467 := hand1 (x 1 1) (x 1 12)
        have b4468 := hb (x 1 1)
        have b4469 := hb (x 1 1 && x 1 12)
        clear * - r4467 b4468 b4469 f4461
        omega
      have d4470 : (x 1 13).toNat = 0 := by
        have r4471 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
        have b4472 := hb (x 1 1)
        have b4473 := hb (x 1 13)
        clear * - r4471 b4472 b4473 f4461
        omega
      have d4474 : (x 1 2 && x 1 13).toNat = 0 := by
        have r4475 := hand2 (x 1 2) (x 1 13)
        have b4476 := hb (x 1 13)
        have b4477 := hb (x 1 2 && x 1 13)
        clear * - r4475 b4476 b4477 d4470
        omega
      have d4478 : (x 2 13).toNat = 1 := by
        have r4479 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := hcov13 2
        have b4480 := hb (x 0 2)
        have b4481 := hb (x 2 13)
        have b4482 := hb (x 1 1 && x 1 14)
        clear * - r4479 b4480 b4481 b4482 d4462 g7
        omega
      have d4483 : (x 2 1).toNat = 1 := by
        have r4484 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
        have b4485 := hb (x 2 1)
        have b4486 := hb (x 2 13)
        clear * - r4484 b4485 b4486 d4478
        omega
      have d4487 : (x 3 14).toNat = 0 := by
        have r4488 : (x 3 14).toNat + (x 2 1).toNat = 1 := hd14 3
        have b4489 := hb (x 2 1)
        have b4490 := hb (x 3 14)
        clear * - r4488 b4489 b4490 d4483
        omega
      have d4491 : (x 3 1 && x 3 14).toNat = 0 := by
        have r4492 := hand2 (x 3 1) (x 3 14)
        have b4493 := hb (x 3 14)
        have b4494 := hb (x 3 1 && x 3 14)
        clear * - r4492 b4493 b4494 d4487
        omega
      have d4495 : (x 4 13).toNat = 1 := by
        have r4496 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
        have b4497 := hb (x 2 2)
        have b4498 := hb (x 4 13)
        have b4499 := hb (x 3 1 && x 3 14)
        clear * - r4496 b4497 b4498 b4499 d4491 g20
        omega
      have d4500 : (x 4 1).toNat = 1 := by
        have r4501 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
        have b4502 := hb (x 4 1)
        have b4503 := hb (x 4 13)
        clear * - r4501 b4502 b4503 d4495
        omega
      have d4504 : (x 5 14).toNat = 0 := by
        have r4505 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
        have b4506 := hb (x 4 1)
        have b4507 := hb (x 5 14)
        clear * - r4505 b4506 b4507 d4500
        omega
      have d4508 : (x 5 1 && x 5 14).toNat = 0 := by
        have r4509 := hand2 (x 5 1) (x 5 14)
        have b4510 := hb (x 5 14)
        have b4511 := hb (x 5 1 && x 5 14)
        clear * - r4509 b4510 b4511 d4504
        omega
      have d4512 : (x 5 3 && x 5 14).toNat = 0 := by
        have r4513 := hand2 (x 5 3) (x 5 14)
        have b4514 := hb (x 5 14)
        have b4515 := hb (x 5 3 && x 5 14)
        clear * - r4513 b4514 b4515 d4504
        omega
      have d4516 : (x 5 2).toNat = 0 := by
        have r4517 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
        have b4518 := hb (x 5 2)
        have b4519 := hb (x 5 14)
        clear * - r4517 b4518 b4519 d4504
        omega
      have d4520 : (x 5 2 && x 5 13).toNat = 0 := by
        have r4521 := hand1 (x 5 2) (x 5 13)
        have b4522 := hb (x 5 2)
        have b4523 := hb (x 5 2 && x 5 13)
        clear * - r4521 b4522 b4523 d4516
        omega
      have d4524 : (x 3 2).toNat = 0 := by
        have r4525 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
        have b4526 := hb (x 3 2)
        have b4527 := hb (x 3 14)
        clear * - r4525 b4526 b4527 d4487
        omega
      have d4528 : (x (-1) 2).toNat = 1 := by
        have r4529 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := hcov13 1
        have b4530 := hb (x (-1) 2)
        have b4531 := hb (x 1 13)
        have b4532 := hb (x 0 1 && x 0 14)
        clear * - r4529 b4530 b4531 b4532 d4470 g57
        omega
      have d4533 : (x (-1) 14).toNat = 1 := by
        have r4534 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
        have b4535 := hb (x (-1) 2)
        have b4536 := hb (x (-1) 14)
        clear * - r4534 b4535 b4536 d4528
        omega
      have d4537 : (x (-2) 1).toNat = 0 := by
        have r4538 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := hd14 (-1)
        have b4539 := hb (x (-2) 1)
        have b4540 := hb (x (-1) 14)
        clear * - r4538 b4539 b4540 d4533
        omega
      have d4541 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
        have r4542 := hand1 (x (-2) 1) (x (-2) 14)
        have b4543 := hb (x (-2) 1)
        have b4544 := hb (x (-2) 1 && x (-2) 14)
        clear * - r4542 b4543 b4544 d4537
        omega
      have d4545 : (x (-2) 13).toNat = 0 := by
        have r4546 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
        have b4547 := hb (x (-2) 1)
        have b4548 := hb (x (-2) 13)
        clear * - r4546 b4547 b4548 d4537
        omega
      have d4549 : (x (-3) 2).toNat = 1 := by
        have r4550 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := hcov13 (-1)
        have b4551 := hb (x (-3) 2)
        have b4552 := hb (x (-1) 13)
        have b4553 := hb (x (-2) 1 && x (-2) 14)
        clear * - r4550 b4551 b4552 b4553 g6 d4541
        omega
      have d4554 : (x (-4) 2).toNat = 1 := by
        have r4555 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := hcov13 (-2)
        have b4556 := hb (x (-4) 2)
        have b4557 := hb (x (-2) 13)
        have b4558 := hb (x (-3) 1 && x (-3) 14)
        clear * - r4555 b4556 b4557 b4558 d4545 g56
        omega
      have d4559 : (x 5 12).toNat = 0 := by
        have r4560 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
        have e4561 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e4562 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b4563 := hb (x 2 3)
        have b4564 := hb (x 3 2)
        have b4565 := hb (x 4 13)
        have b4566 := hb (x 5 12)
        clear * - r4560 e4561 e4562 b4563 b4564 b4565 b4566 d4495 d4524
        omega
      have d4567 : (x 5 4).toNat = 0 := by
        have r4568 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
        have b4569 := hb (x 5 4)
        have b4570 := hb (x 5 12)
        clear * - r4568 b4569 b4570 d4559
        omega
      have d4571 : (x 2 3).toNat = 0 := by
        have r4572 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
        have e4573 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e4574 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b4575 := hb (x 2 3)
        have b4576 := hb (x 3 2)
        have b4577 := hb (x 4 13)
        have b4578 := hb (x 5 12)
        clear * - r4572 e4573 e4574 b4575 b4576 b4577 b4578 d4559 d4495 d4524
        omega
      have d4579 : (x 2 3 && x 2 14).toNat = 0 := by
        have r4580 := hand1 (x 2 3) (x 2 14)
        have b4581 := hb (x 2 3)
        have b4582 := hb (x 2 3 && x 2 14)
        clear * - r4580 b4581 b4582 d4571
        omega
      have d4583 : (x 2 11).toNat = 0 := by
        have r4584 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
        have b4585 := hb (x 2 3)
        have b4586 := hb (x 2 11)
        clear * - r4584 b4585 b4586 d4571
        omega
      have d4587 : (x 3 12).toNat = 0 := by
        have r4588 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := hd12 3
        have e4589 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
        have e4590 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
        have b4591 := hb (x 0 3)
        have b4592 := hb (x 1 2)
        have b4593 := hb (x 2 13)
        have b4594 := hb (x 3 12)
        clear * - r4588 e4589 e4590 b4591 b4592 b4593 b4594 d4478 g8
        omega
      have d4595 : (x 3 4).toNat = 0 := by
        have r4596 : (x 3 4).toNat ≤ (x 3 12).toNat := himp _ _ (hp4 3)
        have b4597 := hb (x 3 4)
        have b4598 := hb (x 3 12)
        clear * - r4596 b4597 b4598 d4587
        omega
      have d4599 : (x (-1) 12).toNat = 0 := by
        have r4600 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
        have e4601 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e4602 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b4603 := hb (x (-4) 3)
        have b4604 := hb (x (-3) 2)
        have b4605 := hb (x (-2) 13)
        have b4606 := hb (x (-1) 12)
        clear * - r4600 e4601 e4602 b4603 b4604 b4605 b4606 d4545 d4549
        omega
      have d4607 : (x (-1) 4).toNat = 0 := by
        have r4608 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
        have b4609 := hb (x (-1) 4)
        have b4610 := hb (x (-1) 12)
        clear * - r4608 b4609 b4610 d4599
        omega
      have d4611 : (x (-2) 12).toNat = 0 := by
        have r4612 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := hd12 (-2)
        have e4613 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e4614 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have b4615 := hb (x (-5) 3)
        have b4616 := hb (x (-4) 2)
        have b4617 := hb (x (-3) 13)
        have b4618 := hb (x (-2) 12)
        clear * - r4612 e4613 e4614 b4615 b4616 b4617 b4618 g2 d4554
        omega
      have d4619 : (x (-2) 4).toNat = 0 := by
        have r4620 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
        have b4621 := hb (x (-2) 4)
        have b4622 := hb (x (-2) 12)
        clear * - r4620 b4621 b4622 d4611
        omega
      have d4623 : (x 5 11).toNat = 1 := by
        have r4624 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := hcov11 5
        have b4625 := hb (x 1 4)
        have b4626 := hb (x 5 11)
        have b4627 := hb (x 4 1 && x 4 12)
        have b4628 := hb (x 3 2 && x 3 13)
        have b4629 := hb (x 2 3 && x 2 14)
        clear * - r4624 b4625 b4626 b4627 b4628 b4629 g54 g55 d4579 g18
        omega
      have d4630 : (x 5 3).toNat = 1 := by
        have r4631 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
        have b4632 := hb (x 5 3)
        have b4633 := hb (x 5 11)
        clear * - r4631 b4632 b4633 d4623
        omega
      have d4634 : (x 8 12).toNat = 0 := by
        have r4635 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
        have e4636 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e4637 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have b4638 := hb (x 5 3)
        have b4639 := hb (x 6 2)
        have b4640 := hb (x 7 13)
        have b4641 := hb (x 8 12)
        clear * - r4635 e4636 e4637 b4638 b4639 b4640 b4641 d4630
        omega
      have d4642 : (x 8 1 && x 8 12).toNat = 0 := by
        have r4643 := hand2 (x 8 1) (x 8 12)
        have b4644 := hb (x 8 12)
        have b4645 := hb (x 8 1 && x 8 12)
        clear * - r4643 b4644 b4645 d4634
        omega
      have d4646 : (x 7 13).toNat = 0 := by
        have r4647 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
        have e4648 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e4649 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have b4650 := hb (x 5 3)
        have b4651 := hb (x 6 2)
        have b4652 := hb (x 7 13)
        have b4653 := hb (x 8 12)
        clear * - r4647 e4648 e4649 b4650 b4651 b4652 b4653 d4634 d4630
        omega
      have d4654 : (x 7 2 && x 7 13).toNat = 0 := by
        have r4655 := hand2 (x 7 2) (x 7 13)
        have b4656 := hb (x 7 13)
        have b4657 := hb (x 7 2 && x 7 13)
        clear * - r4655 b4656 b4657 d4646
        omega
      have d4658 : (x 6 1 && x 6 14).toNat = 1 := by
        have r4659 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
        have b4660 := hb (x 5 2)
        have b4661 := hb (x 7 13)
        have b4662 := hb (x 6 1 && x 6 14)
        clear * - r4659 b4660 b4661 b4662 d4646 d4516
        omega
      have d4663 : (x 6 14).toNat = 1 := by
        have r4664 := hand2 (x 6 1) (x 6 14)
        have b4665 := hb (x 6 14)
        have b4666 := hb (x 6 1 && x 6 14)
        clear * - r4664 b4665 b4666 d4658
        omega
      have d4667 : (x 5 1).toNat = 0 := by
        have r4668 : (x 6 14).toNat + (x 5 1).toNat = 1 := hd14 6
        have b4669 := hb (x 5 1)
        have b4670 := hb (x 6 14)
        clear * - r4668 b4669 b4670 d4663
        omega
      have d4671 : (x 5 13).toNat = 0 := by
        have r4672 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
        have b4673 := hb (x 5 1)
        have b4674 := hb (x 5 13)
        clear * - r4672 b4673 b4674 d4667
        omega
      have d4675 : (x 6 1).toNat = 1 := by
        have r4676 := hand1 (x 6 1) (x 6 14)
        have b4677 := hb (x 6 1)
        have b4678 := hb (x 6 1 && x 6 14)
        clear * - r4676 b4677 b4678 d4658
        omega
      have d4679 : (x 7 14).toNat = 0 := by
        have r4680 : (x 7 14).toNat + (x 6 1).toNat = 1 := hd14 7
        have b4681 := hb (x 6 1)
        have b4682 := hb (x 7 14)
        clear * - r4680 b4681 b4682 d4675
        omega
      have d4683 : (x 7 1 && x 7 14).toNat = 0 := by
        have r4684 := hand2 (x 7 1) (x 7 14)
        have b4685 := hb (x 7 14)
        have b4686 := hb (x 7 1 && x 7 14)
        clear * - r4684 b4685 b4686 d4679
        omega
      have d4687 : (x 7 2).toNat = 0 := by
        have r4688 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
        have b4689 := hb (x 7 2)
        have b4690 := hb (x 7 14)
        clear * - r4688 b4689 b4690 d4679
        omega
      have d4691 : (x 6 2).toNat = 0 := by
        have r4692 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
        have e4693 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e4694 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have b4695 := hb (x 5 3)
        have b4696 := hb (x 6 2)
        have b4697 := hb (x 7 13)
        have b4698 := hb (x 8 12)
        clear * - r4692 e4693 e4694 b4695 b4696 b4697 b4698 d4634 d4646 d4630
        omega
      have d4699 : (x 6 2 && x 6 13).toNat = 0 := by
        have r4700 := hand1 (x 6 2) (x 6 13)
        have b4701 := hb (x 6 2)
        have b4702 := hb (x 6 2 && x 6 13)
        clear * - r4700 b4701 b4702 d4691
        omega
      have d4703 : (x 8 13).toNat = 1 := by
        have r4704 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := hcov13 8
        have b4705 := hb (x 6 2)
        have b4706 := hb (x 8 13)
        have b4707 := hb (x 7 1 && x 7 14)
        clear * - r4704 b4705 b4706 b4707 d4683 d4691
        omega
      have d4708 : (x 8 1).toNat = 1 := by
        have r4709 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
        have b4710 := hb (x 8 1)
        have b4711 := hb (x 8 13)
        clear * - r4709 b4710 b4711 d4703
        omega
      have d4712 : (x 9 14).toNat = 0 := by
        have r4713 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
        have b4714 := hb (x 8 1)
        have b4715 := hb (x 9 14)
        clear * - r4713 b4714 b4715 d4708
        omega
      have d4716 : (x 9 1 && x 9 14).toNat = 0 := by
        have r4717 := hand2 (x 9 1) (x 9 14)
        have b4718 := hb (x 9 14)
        have b4719 := hb (x 9 1 && x 9 14)
        clear * - r4717 b4718 b4719 d4712
        omega
      have d4720 : (x 9 2).toNat = 0 := by
        have r4721 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
        have b4722 := hb (x 9 2)
        have b4723 := hb (x 9 14)
        clear * - r4721 b4722 b4723 d4712
        omega
      have d4724 : (x 9 12).toNat = 0 := by
        have r4725 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
        have e4726 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
        have e4727 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
        have b4728 := hb (x 6 3)
        have b4729 := hb (x 7 2)
        have b4730 := hb (x 8 13)
        have b4731 := hb (x 9 12)
        clear * - r4725 e4726 e4727 b4728 b4729 b4730 b4731 d4703 d4687
        omega
      have d4732 : (x 6 3).toNat = 0 := by
        have r4733 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
        have e4734 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
        have e4735 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
        have b4736 := hb (x 6 3)
        have b4737 := hb (x 7 2)
        have b4738 := hb (x 8 13)
        have b4739 := hb (x 9 12)
        clear * - r4733 e4734 e4735 b4736 b4737 b4738 b4739 d4724 d4703 d4687
        omega
      have d4740 : (x 6 3 && x 6 14).toNat = 0 := by
        have r4741 := hand1 (x 6 3) (x 6 14)
        have b4742 := hb (x 6 3)
        have b4743 := hb (x 6 3 && x 6 14)
        clear * - r4741 b4742 b4743 d4732
        omega
      have d4744 : (x 9 11).toNat = 1 := by
        have r4745 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := hcov11 9
        have b4746 := hb (x 5 4)
        have b4747 := hb (x 9 11)
        have b4748 := hb (x 8 1 && x 8 12)
        have b4749 := hb (x 7 2 && x 7 13)
        have b4750 := hb (x 6 3 && x 6 14)
        clear * - r4745 b4746 b4747 b4748 b4749 b4750 d4642 d4654 d4740 d4567
        omega
      have d4751 : (x 9 3).toNat = 1 := by
        have r4752 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
        have b4753 := hb (x 9 3)
        have b4754 := hb (x 9 11)
        clear * - r4752 b4753 b4754 d4744
        omega
      have d4755 : (x 12 12).toNat = 0 := by
        have r4756 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
        have e4757 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
        have e4758 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
        have b4759 := hb (x 9 3)
        have b4760 := hb (x 10 2)
        have b4761 := hb (x 11 13)
        have b4762 := hb (x 12 12)
        clear * - r4756 e4757 e4758 b4759 b4760 b4761 b4762 d4751
        omega
      have d4763 : (x 11 13).toNat = 0 := by
        have r4764 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
        have e4765 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
        have e4766 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
        have b4767 := hb (x 9 3)
        have b4768 := hb (x 10 2)
        have b4769 := hb (x 11 13)
        have b4770 := hb (x 12 12)
        clear * - r4764 e4765 e4766 b4767 b4768 b4769 b4770 d4755 d4751
        omega
      have d4771 : (x 10 1 && x 10 14).toNat = 1 := by
        have r4772 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := hcov13 11
        have b4773 := hb (x 9 2)
        have b4774 := hb (x 11 13)
        have b4775 := hb (x 10 1 && x 10 14)
        clear * - r4772 b4773 b4774 b4775 d4763 d4720
        omega
      have d4776 : (x 10 14).toNat = 1 := by
        have r4777 := hand2 (x 10 1) (x 10 14)
        have b4778 := hb (x 10 14)
        have b4779 := hb (x 10 1 && x 10 14)
        clear * - r4777 b4778 b4779 d4771
        omega
      have d4780 : (x 9 1).toNat = 0 := by
        have r4781 : (x 10 14).toNat + (x 9 1).toNat = 1 := hd14 10
        have b4782 := hb (x 9 1)
        have b4783 := hb (x 10 14)
        clear * - r4781 b4782 b4783 d4776
        omega
      have d4784 : (x 9 13).toNat = 0 := by
        have r4785 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
        have b4786 := hb (x 9 1)
        have b4787 := hb (x 9 13)
        clear * - r4785 b4786 b4787 d4780
        omega
      have d4788 : (x 8 1 && x 8 14).toNat = 1 := by
        have r4789 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := hcov13 9
        have b4790 := hb (x 7 2)
        have b4791 := hb (x 9 13)
        have b4792 := hb (x 8 1 && x 8 14)
        clear * - r4789 b4790 b4791 b4792 d4784 d4687
        omega
      have d4793 : (x 8 14).toNat = 1 := by
        have r4794 := hand2 (x 8 1) (x 8 14)
        have b4795 := hb (x 8 14)
        have b4796 := hb (x 8 1 && x 8 14)
        clear * - r4794 b4795 b4796 d4788
        omega
      have d4797 : (x 7 1).toNat = 0 := by
        have r4798 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
        have b4799 := hb (x 7 1)
        have b4800 := hb (x 8 14)
        clear * - r4798 b4799 b4800 d4793
        omega
      have d4801 : (x 7 1 && x 7 12).toNat = 0 := by
        have r4802 := hand1 (x 7 1) (x 7 12)
        have b4803 := hb (x 7 1)
        have b4804 := hb (x 7 1 && x 7 12)
        clear * - r4802 b4803 b4804 d4797
        omega
      have d4805 : (x 8 11).toNat = 1 := by
        have r4806 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := hcov11 8
        have b4807 := hb (x 4 4)
        have b4808 := hb (x 8 11)
        have b4809 := hb (x 7 1 && x 7 12)
        have b4810 := hb (x 6 2 && x 6 13)
        have b4811 := hb (x 5 3 && x 5 14)
        clear * - r4806 b4807 b4808 b4809 b4810 b4811 d4801 d4699 d4512 g24
        omega
      have d4812 : (x 8 3).toNat = 1 := by
        have r4813 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
        have b4814 := hb (x 8 3)
        have b4815 := hb (x 8 11)
        clear * - r4813 b4814 b4815 d4805
        omega
      have d4816 : (x 11 12).toNat = 0 := by
        have r4817 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
        have e4818 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e4819 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b4820 := hb (x 8 3)
        have b4821 := hb (x 9 2)
        have b4822 := hb (x 10 13)
        have b4823 := hb (x 11 12)
        clear * - r4817 e4818 e4819 b4820 b4821 b4822 b4823 d4720 d4812
        omega
      have d4824 : (x 10 13).toNat = 0 := by
        have r4825 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
        have e4826 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e4827 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b4828 := hb (x 8 3)
        have b4829 := hb (x 9 2)
        have b4830 := hb (x 10 13)
        have b4831 := hb (x 11 12)
        clear * - r4825 e4826 e4827 b4828 b4829 b4830 b4831 d4816 d4720 d4812
        omega
      have d4832 : (x 8 2).toNat = 1 := by
        have r4833 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := hcov13 10
        have b4834 := hb (x 8 2)
        have b4835 := hb (x 10 13)
        have b4836 := hb (x 9 1 && x 9 14)
        clear * - r4833 b4834 b4835 b4836 d4824 d4716
        omega
      have d4837 : (x 10 12).toNat = 0 := by
        have r4838 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
        have e4839 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
        have e4840 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
        have b4841 := hb (x 7 3)
        have b4842 := hb (x 8 2)
        have b4843 := hb (x 9 13)
        have b4844 := hb (x 10 12)
        clear * - r4838 e4839 e4840 b4841 b4842 b4843 b4844 d4784 d4832
        omega
      have d4845 : (x 7 3).toNat = 0 := by
        have r4846 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
        have e4847 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
        have e4848 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
        have b4849 := hb (x 7 3)
        have b4850 := hb (x 8 2)
        have b4851 := hb (x 9 13)
        have b4852 := hb (x 10 12)
        clear * - r4846 e4847 e4848 b4849 b4850 b4851 b4852 d4837 d4784 d4832
        omega
      have d4853 : (x 7 11).toNat = 0 := by
        have r4854 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
        have b4855 := hb (x 7 3)
        have b4856 := hb (x 7 11)
        clear * - r4854 b4855 b4856 d4845
        omega
      have d4857 : (x (-1) 3 && x (-1) 14).toNat = 1 := by
        have r4858 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := hcov11 2
        have b4859 := hb (x (-2) 4)
        have b4860 := hb (x 2 11)
        have b4861 := hb (x 1 1 && x 1 12)
        have b4862 := hb (x 0 2 && x 0 13)
        have b4863 := hb (x (-1) 3 && x (-1) 14)
        clear * - r4858 b4859 b4860 b4861 b4862 b4863 d4583 d4466 g52 d4619
        omega
      have d4864 : (x (-1) 3).toNat = 1 := by
        have r4865 := hand1 (x (-1) 3) (x (-1) 14)
        have b4866 := hb (x (-1) 3)
        have b4867 := hb (x (-1) 3 && x (-1) 14)
        clear * - r4865 b4866 b4867 d4857
        omega
      have d4868 : (x 2 12).toNat = 0 := by
        have r4869 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := hd12 2
        have e4870 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
        have e4871 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
        have b4872 := hb (x (-1) 3)
        have b4873 := hb (x 0 2)
        have b4874 := hb (x 1 13)
        have b4875 := hb (x 2 12)
        clear * - r4869 e4870 e4871 b4872 b4873 b4874 b4875 d4470 g7 d4864
        omega
      have d4876 : (x 2 1 && x 2 12).toNat = 0 := by
        have r4877 := hand2 (x 2 1) (x 2 12)
        have b4878 := hb (x 2 12)
        have b4879 := hb (x 2 1 && x 2 12)
        clear * - r4877 b4878 b4879 d4868
        omega
      have d4880 : (x 3 11).toNat = 1 := by
        have r4881 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := hcov11 3
        have b4882 := hb (x (-1) 4)
        have b4883 := hb (x 3 11)
        have b4884 := hb (x 2 1 && x 2 12)
        have b4885 := hb (x 1 2 && x 1 13)
        have b4886 := hb (x 0 3 && x 0 14)
        clear * - r4881 b4882 b4883 b4884 b4885 b4886 d4876 d4474 g53 d4607
        omega
      have d4887 : (x 3 3).toNat = 1 := by
        have r4888 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
        have b4889 := hb (x 3 3)
        have b4890 := hb (x 3 11)
        clear * - r4888 b4889 b4890 d4880
        omega
      have d4891 : (x 6 12).toNat = 0 := by
        have r4892 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
        have e4893 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
        have e4894 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
        have b4895 := hb (x 3 3)
        have b4896 := hb (x 4 2)
        have b4897 := hb (x 5 13)
        have b4898 := hb (x 6 12)
        clear * - r4892 e4893 e4894 b4895 b4896 b4897 b4898 d4671 d4887
        omega
      have d4899 : (x 6 1 && x 6 12).toNat = 0 := by
        have r4900 := hand2 (x 6 1) (x 6 12)
        have b4901 := hb (x 6 12)
        have b4902 := hb (x 6 1 && x 6 12)
        clear * - r4900 b4901 b4902 d4891
        omega
      have d4903 : (x 4 3 && x 4 14).toNat = 1 := by
        have r4904 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := hcov11 7
        have b4905 := hb (x 3 4)
        have b4906 := hb (x 7 11)
        have b4907 := hb (x 6 1 && x 6 12)
        have b4908 := hb (x 5 2 && x 5 13)
        have b4909 := hb (x 4 3 && x 4 14)
        clear * - r4904 b4905 b4906 b4907 b4908 b4909 d4853 d4899 d4520 d4595
        omega
      have d4910 : (x 4 3).toNat = 1 := by
        have r4911 := hand1 (x 4 3) (x 4 14)
        have b4912 := hb (x 4 3)
        have b4913 := hb (x 4 3 && x 4 14)
        clear * - r4911 b4912 b4913 d4903
        omega
      have d4914 : (x 7 12).toNat = 0 := by
        have r4915 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
        have e4916 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
        have e4917 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
        have b4918 := hb (x 4 3)
        have b4919 := hb (x 5 2)
        have b4920 := hb (x 6 13)
        have b4921 := hb (x 7 12)
        clear * - r4915 e4916 e4917 b4918 b4919 b4920 b4921 d4516 d4910
        omega
      have d4922 : (x 6 13).toNat = 0 := by
        have r4923 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
        have e4924 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
        have e4925 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
        have b4926 := hb (x 4 3)
        have b4927 := hb (x 5 2)
        have b4928 := hb (x 6 13)
        have b4929 := hb (x 7 12)
        clear * - r4923 e4924 e4925 b4926 b4927 b4928 b4929 d4914 d4516 d4910
        omega
      have d4930 : (x 4 2).toNat = 1 := by
        have r4931 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := hcov13 6
        have b4932 := hb (x 4 2)
        have b4933 := hb (x 6 13)
        have b4934 := hb (x 5 1 && x 5 14)
        clear * - r4931 b4932 b4933 b4934 d4922 d4508
        omega
      have r4935 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
      have e4936 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e4937 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b4938 := hb (x 3 3)
      have b4939 := hb (x 4 2)
      have b4940 := hb (x 5 13)
      have b4941 := hb (x 6 12)
      linarith only [r4935, e4936, e4937, b4938, b4939, b4940, b4941, d4891, d4671, d4930, d4887]
    · have f4942 : (x 1 1).toNat = 1 := by rw [h4460]; rfl
      have d4943 : (x 2 14).toNat = 0 := by
        have r4944 : (x 2 14).toNat + (x 1 1).toNat = 1 := hd14 2
        have b4945 := hb (x 1 1)
        have b4946 := hb (x 2 14)
        clear * - r4944 b4945 b4946 f4942
        omega
      have d4947 : (x 2 1 && x 2 14).toNat = 0 := by
        have r4948 := hand2 (x 2 1) (x 2 14)
        have b4949 := hb (x 2 14)
        have b4950 := hb (x 2 1 && x 2 14)
        clear * - r4948 b4949 b4950 d4943
        omega
      have d4951 : (x 2 3 && x 2 14).toNat = 0 := by
        have r4952 := hand2 (x 2 3) (x 2 14)
        have b4953 := hb (x 2 14)
        have b4954 := hb (x 2 3 && x 2 14)
        clear * - r4952 b4953 b4954 d4943
        omega
      have d4955 : (x 2 5 && x 2 14).toNat = 0 := by
        have r4956 := hand2 (x 2 5) (x 2 14)
        have b4957 := hb (x 2 14)
        have b4958 := hb (x 2 5 && x 2 14)
        clear * - r4956 b4957 b4958 d4943
        omega
      have d4959 : (x 2 7 && x 2 14).toNat = 0 := by
        have r4960 := hand2 (x 2 7) (x 2 14)
        have b4961 := hb (x 2 14)
        have b4962 := hb (x 2 7 && x 2 14)
        clear * - r4960 b4961 b4962 d4943
        omega
      have d4963 : (x 2 6).toNat = 0 := by
        have r4964 : (x 2 6).toNat ≤ (x 2 14).toNat := himp _ _ (hp6 2)
        have b4965 := hb (x 2 6)
        have b4966 := hb (x 2 14)
        clear * - r4964 b4965 b4966 d4943
        omega
      have d4967 : (x 2 6 && x 2 12).toNat = 0 := by
        have r4968 := hand1 (x 2 6) (x 2 12)
        have b4969 := hb (x 2 6)
        have b4970 := hb (x 2 6 && x 2 12)
        clear * - r4968 b4969 b4970 d4963
        omega
      have d4971 : (x 1 2).toNat = 1 := by
        have r4972 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := hcov13 3
        have b4973 := hb (x 1 2)
        have b4974 := hb (x 3 13)
        have b4975 := hb (x 2 1 && x 2 14)
        clear * - r4972 b4973 b4974 b4975 g23 d4947
        omega
      have d4976 : (x 3 12).toNat = 0 := by
        have r4977 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := hd12 3
        have e4978 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
        have e4979 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
        have b4980 := hb (x 0 3)
        have b4981 := hb (x 1 2)
        have b4982 := hb (x 2 13)
        have b4983 := hb (x 3 12)
        clear * - r4977 e4978 e4979 b4980 b4981 b4982 b4983 d4971 g8
        omega
      have d4984 : (x 3 2 && x 3 12).toNat = 0 := by
        have r4985 := hand2 (x 3 2) (x 3 12)
        have b4986 := hb (x 3 12)
        have b4987 := hb (x 3 2 && x 3 12)
        clear * - r4985 b4986 b4987 d4976
        omega
      have d4988 : (x 3 4).toNat = 0 := by
        have r4989 : (x 3 4).toNat ≤ (x 3 12).toNat := himp _ _ (hp4 3)
        have b4990 := hb (x 3 4)
        have b4991 := hb (x 3 12)
        clear * - r4989 b4990 b4991 d4976
        omega
      have d4992 : (x 2 13).toNat = 0 := by
        have r4993 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := hd12 3
        have e4994 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
        have e4995 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
        have b4996 := hb (x 0 3)
        have b4997 := hb (x 1 2)
        have b4998 := hb (x 2 13)
        have b4999 := hb (x 3 12)
        clear * - r4993 e4994 e4995 b4996 b4997 b4998 b4999 d4976 d4971 g8
        omega
      have d5000 : (x 2 3 && x 2 13).toNat = 0 := by
        have r5001 := hand2 (x 2 3) (x 2 13)
        have b5002 := hb (x 2 13)
        have b5003 := hb (x 2 3 && x 2 13)
        clear * - r5001 b5002 b5003 d4992
        omega
      have d5004 : (x 2 5).toNat = 0 := by
        have r5005 : (x 2 5).toNat ≤ (x 2 13).toNat := himp _ _ (hp5 2)
        have b5006 := hb (x 2 5)
        have b5007 := hb (x 2 13)
        clear * - r5005 b5006 b5007 d4992
        omega
      have d5008 : (x 5 11).toNat = 1 := by
        have r5009 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := hcov11 5
        have b5010 := hb (x 1 4)
        have b5011 := hb (x 5 11)
        have b5012 := hb (x 4 1 && x 4 12)
        have b5013 := hb (x 3 2 && x 3 13)
        have b5014 := hb (x 2 3 && x 2 14)
        clear * - r5009 b5010 b5011 b5012 b5013 b5014 g54 g55 d4951 g18
        omega
      have d5015 : (x 5 3).toNat = 1 := by
        have r5016 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
        have b5017 := hb (x 5 3)
        have b5018 := hb (x 5 11)
        clear * - r5016 b5017 b5018 d5008
        omega
      have d5019 : (x 8 12).toNat = 0 := by
        have r5020 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
        have e5021 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e5022 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have b5023 := hb (x 5 3)
        have b5024 := hb (x 6 2)
        have b5025 := hb (x 7 13)
        have b5026 := hb (x 8 12)
        clear * - r5020 e5021 e5022 b5023 b5024 b5025 b5026 d5015
        omega
      have d5027 : (x 8 4).toNat = 0 := by
        have r5028 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
        have b5029 := hb (x 8 4)
        have b5030 := hb (x 8 12)
        clear * - r5028 b5029 b5030 d5019
        omega
      have d5031 : (x 8 4 && x 8 14).toNat = 0 := by
        have r5032 := hand1 (x 8 4) (x 8 14)
        have b5033 := hb (x 8 4)
        have b5034 := hb (x 8 4 && x 8 14)
        clear * - r5032 b5033 b5034 d5027
        omega
      have d5035 : (x 8 4 && x 8 9).toNat = 0 := by
        have r5036 := hand1 (x 8 4) (x 8 9)
        have b5037 := hb (x 8 4)
        have b5038 := hb (x 8 4 && x 8 9)
        clear * - r5036 b5037 b5038 d5027
        omega
      have d5039 : (x 7 13).toNat = 0 := by
        have r5040 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
        have e5041 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e5042 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have b5043 := hb (x 5 3)
        have b5044 := hb (x 6 2)
        have b5045 := hb (x 7 13)
        have b5046 := hb (x 8 12)
        clear * - r5040 e5041 e5042 b5043 b5044 b5045 b5046 d5019 d5015
        omega
      have d5047 : (x 7 5).toNat = 0 := by
        have r5048 : (x 7 5).toNat ≤ (x 7 13).toNat := himp _ _ (hp5 7)
        have b5049 := hb (x 7 5)
        have b5050 := hb (x 7 13)
        clear * - r5048 b5049 b5050 d5039
        omega
      have d5051 : (x 7 5 && x 7 10).toNat = 0 := by
        have r5052 := hand1 (x 7 5) (x 7 10)
        have b5053 := hb (x 7 5)
        have b5054 := hb (x 7 5 && x 7 10)
        clear * - r5052 b5053 b5054 d5047
        omega
      have d5055 : (x 6 2).toNat = 0 := by
        have r5056 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
        have e5057 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e5058 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have b5059 := hb (x 5 3)
        have b5060 := hb (x 6 2)
        have b5061 := hb (x 7 13)
        have b5062 := hb (x 8 12)
        clear * - r5056 e5057 e5058 b5059 b5060 b5061 b5062 d5019 d5039 d5015
        omega
      have d5063 : (x 6 2 && x 6 11).toNat = 0 := by
        have r5064 := hand1 (x 6 2) (x 6 11)
        have b5065 := hb (x 6 2)
        have b5066 := hb (x 6 2 && x 6 11)
        clear * - r5064 b5065 b5066 d5055
        omega
      have d5067 : (x 6 2 && x 6 8).toNat = 0 := by
        have r5068 := hand1 (x 6 2) (x 6 8)
        have b5069 := hb (x 6 2)
        have b5070 := hb (x 6 2 && x 6 8)
        clear * - r5068 b5069 b5070 d5055
        omega
      have d5071 : (x 6 10).toNat = 0 := by
        have r5072 : (x 6 10).toNat ≤ (x 6 2).toNat := himp _ _ (hp10 6)
        have b5073 := hb (x 6 2)
        have b5074 := hb (x 6 10)
        clear * - r5072 b5073 b5074 d5055
        omega
      have d5075 : (x 6 1 && x 6 10).toNat = 0 := by
        have r5076 := hand2 (x 6 1) (x 6 10)
        have b5077 := hb (x 6 10)
        have b5078 := hb (x 6 1 && x 6 10)
        clear * - r5076 b5077 b5078 d5071
        omega
      have d5079 : (x 6 3 && x 6 10).toNat = 0 := by
        have r5080 := hand2 (x 6 3) (x 6 10)
        have b5081 := hb (x 6 10)
        have b5082 := hb (x 6 3 && x 6 10)
        clear * - r5080 b5081 b5082 d5071
        omega
      have d5083 : (x 8 8).toNat = 0 := by
        have r5084 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
        have e5085 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e5086 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e5087 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e5088 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e5089 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e5090 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b5091 := hb (x 1 7)
        have b5092 := hb (x 2 6)
        have b5093 := hb (x 3 5)
        have b5094 := hb (x 4 4)
        have b5095 := hb (x 5 11)
        have b5096 := hb (x 6 10)
        have b5097 := hb (x 7 9)
        have b5098 := hb (x 8 8)
        clear * - r5084 e5085 e5086 e5087 e5088 e5089 e5090 b5091 b5092 b5093 b5094 b5095 b5096 b5097 b5098 d5071 d5008 g24 g22 d4963
        omega
      have d5099 : (x 8 1 && x 8 8).toNat = 0 := by
        have r5100 := hand2 (x 8 1) (x 8 8)
        have b5101 := hb (x 8 8)
        have b5102 := hb (x 8 1 && x 8 8)
        clear * - r5100 b5101 b5102 d5083
        omega
      have d5103 : (x 7 9).toNat = 0 := by
        have r5104 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
        have e5105 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e5106 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e5107 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e5108 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e5109 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e5110 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b5111 := hb (x 1 7)
        have b5112 := hb (x 2 6)
        have b5113 := hb (x 3 5)
        have b5114 := hb (x 4 4)
        have b5115 := hb (x 5 11)
        have b5116 := hb (x 6 10)
        have b5117 := hb (x 7 9)
        have b5118 := hb (x 8 8)
        clear * - r5104 e5105 e5106 e5107 e5108 e5109 e5110 b5111 b5112 b5113 b5114 b5115 b5116 b5117 b5118 d5083 d5071 d5008 g24 g22 d4963
        omega
      have d5119 : (x 7 2 && x 7 9).toNat = 0 := by
        have r5120 := hand2 (x 7 2) (x 7 9)
        have b5121 := hb (x 7 9)
        have b5122 := hb (x 7 2 && x 7 9)
        clear * - r5120 b5121 b5122 d5103
        omega
      have d5123 : (x 1 7).toNat = 0 := by
        have r5124 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
        have e5125 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e5126 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e5127 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e5128 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e5129 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e5130 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b5131 := hb (x 1 7)
        have b5132 := hb (x 2 6)
        have b5133 := hb (x 3 5)
        have b5134 := hb (x 4 4)
        have b5135 := hb (x 5 11)
        have b5136 := hb (x 6 10)
        have b5137 := hb (x 7 9)
        have b5138 := hb (x 8 8)
        clear * - r5124 e5125 e5126 e5127 e5128 e5129 e5130 b5131 b5132 b5133 b5134 b5135 b5136 b5137 b5138 d5083 d5103 d5071 d5008 g24 g22 d4963
        omega
      have d5139 : (x 1 7 && x 1 13).toNat = 0 := by
        have r5140 := hand1 (x 1 7) (x 1 13)
        have b5141 := hb (x 1 7)
        have b5142 := hb (x 1 7 && x 1 13)
        clear * - r5140 b5141 b5142 d5123
        omega
      cases h5143 : x (-1) 3
      · have f5144 : (x (-1) 3).toNat = 0 := by rw [h5143]; rfl
        cases h5145 : x (-1) 6
        · have f5146 : (x (-1) 6).toNat = 0 := by rw [h5145]; rfl
          cases h5147 : x 1 11
          · have f5148 : (x 1 11).toNat = 0 := by rw [h5147]; rfl
            have d5149 : (x 1 1 && x 1 11).toNat = 0 := by
              have r5150 := hand2 (x 1 1) (x 1 11)
              have b5151 := hb (x 1 11)
              have b5152 := hb (x 1 1 && x 1 11)
              clear * - r5150 b5151 b5152 f5148
              omega
            have d5153 : (x (-2) 4 && x (-2) 14).toNat = 1 := by
              have r5154 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := hcov10 2
              have b5155 := hb (x (-3) 5)
              have b5156 := hb (x 2 10)
              have b5157 := hb (x 1 1 && x 1 11)
              have b5158 := hb (x 0 2 && x 0 12)
              have b5159 := hb (x (-1) 3 && x (-1) 13)
              have b5160 := hb (x (-2) 4 && x (-2) 14)
              clear * - r5154 b5155 b5156 b5157 b5158 b5159 b5160 g21 d5149 g44 g45 g0
              omega
            have d5161 : (x (-2) 4).toNat = 1 := by
              have r5162 := hand1 (x (-2) 4) (x (-2) 14)
              have b5163 := hb (x (-2) 4)
              have b5164 := hb (x (-2) 4 && x (-2) 14)
              clear * - r5162 b5163 b5164 d5153
              omega
            have d5165 : (x (-2) 12).toNat = 1 := by
              have r5166 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
              have b5167 := hb (x (-2) 4)
              have b5168 := hb (x (-2) 12)
              clear * - r5166 b5167 b5168 d5161
              omega
            have d5169 : (x (-4) 2).toNat = 0 := by
              have r5170 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := hd12 (-2)
              have e5171 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
              have e5172 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
              have b5173 := hb (x (-5) 3)
              have b5174 := hb (x (-4) 2)
              have b5175 := hb (x (-3) 13)
              have b5176 := hb (x (-2) 12)
              clear * - r5170 e5171 e5172 b5173 b5174 b5175 b5176 d5165 g2
              omega
            have d5177 : (x (-2) 13).toNat = 1 := by
              have r5178 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := hcov13 (-2)
              have b5179 := hb (x (-4) 2)
              have b5180 := hb (x (-2) 13)
              have b5181 := hb (x (-3) 1 && x (-3) 14)
              clear * - r5178 b5179 b5180 b5181 g56 d5169
              omega
            have d5182 : (x (-2) 1).toNat = 1 := by
              have r5183 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
              have b5184 := hb (x (-2) 1)
              have b5185 := hb (x (-2) 13)
              clear * - r5183 b5184 b5185 d5177
              omega
            have d5186 : (x (-1) 14).toNat = 0 := by
              have r5187 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := hd14 (-1)
              have b5188 := hb (x (-2) 1)
              have b5189 := hb (x (-1) 14)
              clear * - r5187 b5188 b5189 d5182
              omega
            have d5190 : (x (-1) 2).toNat = 0 := by
              have r5191 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
              have b5192 := hb (x (-1) 2)
              have b5193 := hb (x (-1) 14)
              clear * - r5191 b5192 b5193 d5186
              omega
            have d5194 : (x 1 13).toNat = 1 := by
              have r5195 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := hcov13 1
              have b5196 := hb (x (-1) 2)
              have b5197 := hb (x 1 13)
              have b5198 := hb (x 0 1 && x 0 14)
              clear * - r5195 b5196 b5197 b5198 g57 d5190
              omega
            have d5199 : (x 2 12).toNat = 0 := by
              have r5200 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := hd12 2
              have e5201 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
              have e5202 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
              have b5203 := hb (x (-1) 3)
              have b5204 := hb (x 0 2)
              have b5205 := hb (x 1 13)
              have b5206 := hb (x 2 12)
              clear * - r5200 e5201 e5202 b5203 b5204 b5205 b5206 d5194 g7 f5144
              omega
            have d5207 : (x 2 3 && x 2 12).toNat = 0 := by
              have r5208 := hand2 (x 2 3) (x 2 12)
              have b5209 := hb (x 2 12)
              have b5210 := hb (x 2 3 && x 2 12)
              clear * - r5208 b5209 b5210 d5199
              omega
            have d5211 : (x 2 11 && x 2 12).toNat = 0 := by
              have r5212 := hand2 (x 2 11) (x 2 12)
              have b5213 := hb (x 2 12)
              have b5214 := hb (x 2 11 && x 2 12)
              clear * - r5212 b5213 b5214 d5199
              omega
            have d5215 : (x (-1) 12).toNat = 0 := by
              have r5216 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
              have e5217 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e5218 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b5219 := hb (x (-4) 3)
              have b5220 := hb (x (-3) 2)
              have b5221 := hb (x (-2) 13)
              have b5222 := hb (x (-1) 12)
              clear * - r5216 e5217 e5218 b5219 b5220 b5221 b5222 d5177
              omega
            have d5223 : (x (-3) 2).toNat = 0 := by
              have r5224 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
              have e5225 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e5226 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b5227 := hb (x (-4) 3)
              have b5228 := hb (x (-3) 2)
              have b5229 := hb (x (-2) 13)
              have b5230 := hb (x (-1) 12)
              clear * - r5224 e5225 e5226 b5227 b5228 b5229 b5230 d5215 d5177
              omega
            have d5231 : (x (-3) 10).toNat = 0 := by
              have r5232 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
              have b5233 := hb (x (-3) 2)
              have b5234 := hb (x (-3) 10)
              clear * - r5232 b5233 b5234 d5223
              omega
            have d5235 : (x (-4) 3).toNat = 0 := by
              have r5236 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
              have e5237 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e5238 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b5239 := hb (x (-4) 3)
              have b5240 := hb (x (-3) 2)
              have b5241 := hb (x (-2) 13)
              have b5242 := hb (x (-1) 12)
              clear * - r5236 e5237 e5238 b5239 b5240 b5241 b5242 d5215 d5177 d5223
              omega
            have d5243 : (x (-4) 11).toNat = 0 := by
              have r5244 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
              have b5245 := hb (x (-4) 3)
              have b5246 := hb (x (-4) 11)
              clear * - r5244 b5245 b5246 d5235
              omega
            have d5247 : (x (-4) 1 && x (-4) 11).toNat = 0 := by
              have r5248 := hand2 (x (-4) 1) (x (-4) 11)
              have b5249 := hb (x (-4) 11)
              have b5250 := hb (x (-4) 1 && x (-4) 11)
              clear * - r5248 b5249 b5250 d5243
              omega
            cases h5251 : x 1 12
            · have f5252 : (x 1 12).toNat = 0 := by rw [h5251]; rfl
              have d5253 : (x 1 3 && x 1 12).toNat = 0 := by
                have r5254 := hand2 (x 1 3) (x 1 12)
                have b5255 := hb (x 1 12)
                have b5256 := hb (x 1 3 && x 1 12)
                clear * - r5254 b5255 b5256 f5252
                omega
              have d5257 : (x 1 12 && x 1 13).toNat = 0 := by
                have r5258 := hand1 (x 1 12) (x 1 13)
                have b5259 := hb (x 1 12)
                have b5260 := hb (x 1 12 && x 1 13)
                clear * - r5258 b5259 b5260 f5252
                omega
              have r5261 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := hcount 4
              have r5262 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := hcount 14
              have r5263 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := hd8 5
              have e5264 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
              have e5265 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
              have e5266 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
              have e5267 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
              have e5268 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
              have e5269 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
              have r5270 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
              have e5271 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
              have e5272 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
              have e5273 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
              have e5274 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
              have e5275 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
              have e5276 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
              have r5277 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := hd8 16
              have e5278 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
              have e5279 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
              have e5280 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
              have e5281 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
              have e5282 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
              have e5283 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
              have r5284 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
              have e5285 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
              have e5286 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
              have r5287 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
              have r5288 : 1 ≤ (x 4 1).toNat + (x 3 1 && x 3 2).toNat + (x 2 2 && x 2 3).toNat + (x 1 3 && x 1 4).toNat + (x 0 4 && x 0 5).toNat + (x (-1) 5 && x (-1) 6).toNat + (x (-2) 6 && x (-2) 7).toNat + (x (-3) 7 && x (-3) 8).toNat + (x (-4) 8 && x (-4) 9).toNat + (x (-5) 9 && x (-5) 10).toNat + (x (-6) 10 && x (-6) 11).toNat + (x (-7) 11 && x (-7) 12).toNat + (x (-8) 12 && x (-8) 13).toNat + (x (-9) 13 && x (-9) 14).toNat + (x (-10) 14).toNat := hcov1 4
              have r5289 : 1 ≤ (x 13 1).toNat + (x 12 1 && x 12 2).toNat + (x 11 2 && x 11 3).toNat + (x 10 3 && x 10 4).toNat + (x 9 4 && x 9 5).toNat + (x 8 5 && x 8 6).toNat + (x 7 6 && x 7 7).toNat + (x 6 7 && x 6 8).toNat + (x 5 8 && x 5 9).toNat + (x 4 9 && x 4 10).toNat + (x 3 10 && x 3 11).toNat + (x 2 11 && x 2 12).toNat + (x 1 12 && x 1 13).toNat + (x 0 13 && x 0 14).toNat + (x (-1) 14).toNat := hcov1 13
              have r5290 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := hcov6 8
              have r5291 : 1 ≤ (x 9 7).toNat + (x 8 1 && x 8 8).toNat + (x 7 2 && x 7 9).toNat + (x 6 3 && x 6 10).toNat + (x 5 4 && x 5 11).toNat + (x 4 5 && x 4 12).toNat + (x 3 6 && x 3 13).toNat + (x 2 7 && x 2 14).toNat + (x 1 8).toNat := hcov7 9
              have r5292 : 1 ≤ (x 4 9).toNat + (x 3 1 && x 3 10).toNat + (x 2 2 && x 2 11).toNat + (x 1 3 && x 1 12).toNat + (x 0 4 && x 0 13).toNat + (x (-1) 5 && x (-1) 14).toNat + (x (-2) 6).toNat := hcov9 4
              have r5293 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := hcov9 5
              have r5294 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := hcov9 7
              have r5295 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := hcov10 5
              have r5296 : 1 ≤ (x 14 10).toNat + (x 13 1 && x 13 11).toNat + (x 12 2 && x 12 12).toNat + (x 11 3 && x 11 13).toNat + (x 10 4 && x 10 14).toNat + (x 9 5).toNat := hcov10 14
              have r5297 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
              have r5298 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
              have r5299 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
              have r5300 := hand2 (x 3 1) (x 3 2)
              have r5301 := hand2 (x (-2) 6) (x (-2) 7)
              have r5302 := hand1 (x (-3) 7) (x (-3) 8)
              have r5303 := hand1 (x (-4) 8) (x (-4) 9)
              have r5304 := hand1 (x (-5) 9) (x (-5) 10)
              have r5305 := hand1 (x (-6) 10) (x (-6) 11)
              have r5306 := hand1 (x (-7) 11) (x (-7) 12)
              have r5307 := hand1 (x (-8) 12) (x (-8) 13)
              have r5308 := hand1 (x (-9) 13) (x (-9) 14)
              have r5309 := hand2 (x 12 1) (x 12 2)
              have r5310 := hand2 (x 11 2) (x 11 3)
              have r5311 := hand2 (x 10 3) (x 10 4)
              have r5312 := hand2 (x 9 4) (x 9 5)
              have r5313 := hand2 (x 8 5) (x 8 6)
              have r5314 := hand2 (x 7 6) (x 7 7)
              have r5315 := hand2 (x 6 7) (x 6 8)
              have r5316 := hand1 (x 5 8) (x 5 9)
              have r5317 := hand2 (x 4 9) (x 4 10)
              have r5318 := hand2 (x 3 10) (x 3 11)
              have r5319 := hand2 (x 7 1) (x 7 7)
              have r5320 := hand2 (x 5 3) (x 5 9)
              have r5321 := hand1 (x 5 4) (x 5 11)
              have r5322 := hand2 (x 3 1) (x 3 10)
              have r5323 := hand2 (x 4 1) (x 4 10)
              have r5324 := hand2 (x 3 2) (x 3 11)
              have r5325 := hand1 (x 5 2) (x 5 11)
              have r5326 := hand2 (x 4 1) (x 4 11)
              have r5327 := hand1 (x 13 1) (x 13 11)
              have r5328 := hand1 (x 12 2) (x 12 12)
              have r5329 := hand1 (x 11 3) (x 11 13)
              have r5330 := hand1 (x 10 4) (x 10 14)
              have r5331 := hand1 (x 3 1) (x 3 14)
              have b5332 := hb (x (-10) 14)
              have b5333 := hb (x (-9) 13)
              have b5334 := hb (x (-8) 12)
              have b5335 := hb (x (-7) 11)
              have b5336 := hb (x (-6) 10)
              have b5337 := hb (x (-5) 9)
              have b5338 := hb (x (-4) 8)
              have b5339 := hb (x (-3) 7)
              have b5340 := hb (x (-2) 6)
              have b5341 := hb (x (-2) 7)
              have b5342 := hb (x (-1) 5)
              have b5343 := hb (x (-1) 6)
              have b5344 := hb (x (-1) 9)
              have b5345 := hb (x (-1) 14)
              have b5346 := hb (x 0 4)
              have b5347 := hb (x 0 5)
              have b5348 := hb (x 0 7)
              have b5349 := hb (x 0 14)
              have b5350 := hb (x 1 3)
              have b5351 := hb (x 1 4)
              have b5352 := hb (x 1 6)
              have b5353 := hb (x 1 8)
              have b5354 := hb (x 1 13)
              have b5355 := hb (x 2 2)
              have b5356 := hb (x 2 3)
              have b5357 := hb (x 2 5)
              have b5358 := hb (x 2 11)
              have b5359 := hb (x 2 12)
              have b5360 := hb (x 3 1)
              have b5361 := hb (x 3 2)
              have b5362 := hb (x 3 4)
              have b5363 := hb (x 3 10)
              have b5364 := hb (x 3 11)
              have b5365 := hb (x 4 1)
              have b5366 := hb (x 4 9)
              have b5367 := hb (x 4 10)
              have b5368 := hb (x 4 11)
              have b5369 := hb (x 4 13)
              have b5370 := hb (x 5 2)
              have b5371 := hb (x 5 4)
              have b5372 := hb (x 5 8)
              have b5373 := hb (x 5 9)
              have b5374 := hb (x 5 10)
              have b5375 := hb (x 5 12)
              have b5376 := hb (x 5 14)
              have b5377 := hb (x 6 8)
              have b5378 := hb (x 6 9)
              have b5379 := hb (x 7 7)
              have b5380 := hb (x 7 8)
              have b5381 := hb (x 7 9)
              have b5382 := hb (x 8 6)
              have b5383 := hb (x 9 5)
              have b5384 := hb (x 9 7)
              have b5385 := hb (x 10 4)
              have b5386 := hb (x 10 6)
              have b5387 := hb (x 11 3)
              have b5388 := hb (x 11 5)
              have b5389 := hb (x 12 2)
              have b5390 := hb (x 12 4)
              have b5391 := hb (x 13 1)
              have b5392 := hb (x 13 11)
              have b5393 := hb (x 14 10)
              have b5394 := hb (x 15 9)
              have b5395 := hb (x 16 8)
              have b5396 := hb (x 3 1 && x 3 2)
              have b5397 := hb (x 2 2 && x 2 3)
              have b5398 := hb (x 1 3 && x 1 4)
              have b5399 := hb (x 0 4 && x 0 5)
              have b5400 := hb (x (-1) 5 && x (-1) 6)
              have b5401 := hb (x (-2) 6 && x (-2) 7)
              have b5402 := hb (x (-3) 7 && x (-3) 8)
              have b5403 := hb (x (-4) 8 && x (-4) 9)
              have b5404 := hb (x (-5) 9 && x (-5) 10)
              have b5405 := hb (x (-6) 10 && x (-6) 11)
              have b5406 := hb (x (-7) 11 && x (-7) 12)
              have b5407 := hb (x (-8) 12 && x (-8) 13)
              have b5408 := hb (x (-9) 13 && x (-9) 14)
              have b5409 := hb (x 12 1 && x 12 2)
              have b5410 := hb (x 11 2 && x 11 3)
              have b5411 := hb (x 10 3 && x 10 4)
              have b5412 := hb (x 9 4 && x 9 5)
              have b5413 := hb (x 8 5 && x 8 6)
              have b5414 := hb (x 7 6 && x 7 7)
              have b5415 := hb (x 6 7 && x 6 8)
              have b5416 := hb (x 5 8 && x 5 9)
              have b5417 := hb (x 4 9 && x 4 10)
              have b5418 := hb (x 3 10 && x 3 11)
              have b5419 := hb (x 2 11 && x 2 12)
              have b5420 := hb (x 1 12 && x 1 13)
              have b5421 := hb (x 0 13 && x 0 14)
              have b5422 := hb (x 7 1 && x 7 7)
              have b5423 := hb (x 6 2 && x 6 8)
              have b5424 := hb (x 5 3 && x 5 9)
              have b5425 := hb (x 4 4 && x 4 10)
              have b5426 := hb (x 3 5 && x 3 11)
              have b5427 := hb (x 2 6 && x 2 12)
              have b5428 := hb (x 1 7 && x 1 13)
              have b5429 := hb (x 0 8 && x 0 14)
              have b5430 := hb (x 8 1 && x 8 8)
              have b5431 := hb (x 7 2 && x 7 9)
              have b5432 := hb (x 6 3 && x 6 10)
              have b5433 := hb (x 5 4 && x 5 11)
              have b5434 := hb (x 4 5 && x 4 12)
              have b5435 := hb (x 3 6 && x 3 13)
              have b5436 := hb (x 2 7 && x 2 14)
              have b5437 := hb (x 3 1 && x 3 10)
              have b5438 := hb (x 2 2 && x 2 11)
              have b5439 := hb (x 1 3 && x 1 12)
              have b5440 := hb (x 0 4 && x 0 13)
              have b5441 := hb (x (-1) 5 && x (-1) 14)
              have b5442 := hb (x 4 1 && x 4 10)
              have b5443 := hb (x 3 2 && x 3 11)
              have b5444 := hb (x 2 3 && x 2 12)
              have b5445 := hb (x 1 4 && x 1 13)
              have b5446 := hb (x 0 5 && x 0 14)
              have b5447 := hb (x 6 1 && x 6 10)
              have b5448 := hb (x 5 2 && x 5 11)
              have b5449 := hb (x 4 3 && x 4 12)
              have b5450 := hb (x 3 4 && x 3 13)
              have b5451 := hb (x 2 5 && x 2 14)
              have b5452 := hb (x 4 1 && x 4 11)
              have b5453 := hb (x 3 2 && x 3 12)
              have b5454 := hb (x 2 3 && x 2 13)
              have b5455 := hb (x 1 4 && x 1 14)
              have b5456 := hb (x 13 1 && x 13 11)
              have b5457 := hb (x 12 2 && x 12 12)
              have b5458 := hb (x 11 3 && x 11 13)
              have b5459 := hb (x 10 4 && x 10 14)
              have b5460 := hb (x 3 1 && x 3 14)
              linarith only [r5261, r5262, r5263, e5264, e5265, e5266, e5267, e5268, e5269, r5270, e5271, e5272, e5273, e5274, e5275, e5276, r5277, e5278, e5279, e5280, e5281, e5282, e5283, r5284, e5285, e5286, r5287, r5288, r5289, r5290, r5291, r5292, r5293, r5294, r5295, r5296, r5297, r5298, r5299, r5300, r5301, r5302, r5303, r5304, r5305, r5306, r5307, r5308, r5309, r5310, r5311, r5312, r5313, r5314, r5315, r5316, r5317, r5318, r5319, r5320, r5321, r5322, r5323, r5324, r5325, r5326, r5327, r5328, r5329, r5330, r5331, b5332, b5333, b5334, b5335, b5336, b5337, b5338, b5339, b5340, b5341, b5342, b5343, b5344, b5345, b5346, b5347, b5348, b5349, b5350, b5351, b5352, b5353, b5354, b5355, b5356, b5357, b5358, b5359, b5360, b5361, b5362, b5363, b5364, b5365, b5366, b5367, b5368, b5369, b5370, b5371, b5372, b5373, b5374, b5375, b5376, b5377, b5378, b5379, b5380, b5381, b5382, b5383, b5384, b5385, b5386, b5387, b5388, b5389, b5390, b5391, b5392, b5393, b5394, b5395, b5396, b5397, b5398, b5399, b5400, b5401, b5402, b5403, b5404, b5405, b5406, b5407, b5408, b5409, b5410, b5411, b5412, b5413, b5414, b5415, b5416, b5417, b5418, b5419, b5420, b5421, b5422, b5423, b5424, b5425, b5426, b5427, b5428, b5429, b5430, b5431, b5432, b5433, b5434, b5435, b5436, b5437, b5438, b5439, b5440, b5441, b5442, b5443, b5444, b5445, b5446, b5447, b5448, b5449, b5450, b5451, b5452, b5453, b5454, b5455, b5456, b5457, b5458, b5459, b5460, g4, f5146, g5, d5186, g9, g10, g11, g16, g17, g18, g19, d5194, g20, d5004, d5199, d4988, d5103, g25, d4454, g26, g27, d5211, d5257, g28, d5067, g29, g30, d4967, d5139, g31, d5099, d5119, d5079, g32, g33, d4959, g34, d5253, g35, g36, d5207, d4450, g37, d5075, g38, g39, d4955, d4984, d5000, d4446]
            · have f5461 : (x 1 12).toNat = 1 := by rw [h5251]; rfl
              have d5462 : (x (-2) 3).toNat = 0 := by
                have r5463 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
                have e5464 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
                have e5465 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
                have b5466 := hb (x (-2) 3)
                have b5467 := hb (x (-1) 2)
                have b5468 := hb (x 0 13)
                have b5469 := hb (x 1 12)
                clear * - r5463 e5464 e5465 b5466 b5467 b5468 b5469 f5461 g15 d5190
                omega
              have d5470 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
                have r5471 := hand1 (x (-2) 3) (x (-2) 14)
                have b5472 := hb (x (-2) 3)
                have b5473 := hb (x (-2) 3 && x (-2) 14)
                clear * - r5471 b5472 b5473 d5462
                omega
              have d5474 : (x (-3) 4).toNat = 1 := by
                have r5475 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := hcov11 1
                have b5476 := hb (x (-3) 4)
                have b5477 := hb (x 1 11)
                have b5478 := hb (x 0 1 && x 0 12)
                have b5479 := hb (x (-1) 2 && x (-1) 13)
                have b5480 := hb (x (-2) 3 && x (-2) 14)
                clear * - r5475 b5476 b5477 b5478 b5479 b5480 f5148 g50 g51 d5470
                omega
              have d5481 : (x (-3) 12).toNat = 1 := by
                have r5482 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
                have b5483 := hb (x (-3) 4)
                have b5484 := hb (x (-3) 12)
                clear * - r5482 b5483 b5484 d5474
                omega
              have d5485 : (x (-4) 13).toNat = 0 := by
                have r5486 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := hd12 (-3)
                have e5487 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                have e5488 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                have b5489 := hb (x (-6) 3)
                have b5490 := hb (x (-5) 2)
                have b5491 := hb (x (-4) 13)
                have b5492 := hb (x (-3) 12)
                clear * - r5486 e5487 e5488 b5489 b5490 b5491 b5492 d5481
                omega
              have d5493 : (x (-5) 2).toNat = 0 := by
                have r5494 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := hd12 (-3)
                have e5495 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                have e5496 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                have b5497 := hb (x (-6) 3)
                have b5498 := hb (x (-5) 2)
                have b5499 := hb (x (-4) 13)
                have b5500 := hb (x (-3) 12)
                clear * - r5494 e5495 e5496 b5497 b5498 b5499 b5500 d5481 d5485
                omega
              have d5501 : (x (-5) 2 && x (-5) 13).toNat = 0 := by
                have r5502 := hand1 (x (-5) 2) (x (-5) 13)
                have b5503 := hb (x (-5) 2)
                have b5504 := hb (x (-5) 2 && x (-5) 13)
                clear * - r5502 b5503 b5504 d5493
                omega
              have d5505 : (x (-5) 2 && x (-5) 12).toNat = 0 := by
                have r5506 := hand1 (x (-5) 2) (x (-5) 12)
                have b5507 := hb (x (-5) 2)
                have b5508 := hb (x (-5) 2 && x (-5) 12)
                clear * - r5506 b5507 b5508 d5493
                omega
              have d5509 : (x (-4) 1 && x (-4) 14).toNat = 1 := by
                have r5510 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := hcov13 (-3)
                have b5511 := hb (x (-5) 2)
                have b5512 := hb (x (-3) 13)
                have b5513 := hb (x (-4) 1 && x (-4) 14)
                clear * - r5510 b5511 b5512 b5513 g2 d5493
                omega
              have d5514 : (x (-4) 14).toNat = 1 := by
                have r5515 := hand2 (x (-4) 1) (x (-4) 14)
                have b5516 := hb (x (-4) 14)
                have b5517 := hb (x (-4) 1 && x (-4) 14)
                clear * - r5515 b5516 b5517 d5509
                omega
              have d5518 : (x (-5) 1).toNat = 0 := by
                have r5519 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := hd14 (-4)
                have b5520 := hb (x (-5) 1)
                have b5521 := hb (x (-4) 14)
                clear * - r5519 b5520 b5521 d5514
                omega
              have d5522 : (x (-5) 1 && x (-5) 14).toNat = 0 := by
                have r5523 := hand1 (x (-5) 1) (x (-5) 14)
                have b5524 := hb (x (-5) 1)
                have b5525 := hb (x (-5) 1 && x (-5) 14)
                clear * - r5523 b5524 b5525 d5518
                omega
              have d5526 : (x (-6) 2).toNat = 1 := by
                have r5527 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := hcov13 (-4)
                have b5528 := hb (x (-6) 2)
                have b5529 := hb (x (-4) 13)
                have b5530 := hb (x (-5) 1 && x (-5) 14)
                clear * - r5527 b5528 b5529 b5530 d5485 d5522
                omega
              have d5531 : (x (-6) 14).toNat = 1 := by
                have r5532 : (x (-6) 2).toNat ≤ (x (-6) 14).toNat := himp _ _ (hp2 (-6))
                have b5533 := hb (x (-6) 2)
                have b5534 := hb (x (-6) 14)
                clear * - r5532 b5533 b5534 d5526
                omega
              have d5535 : (x (-7) 1).toNat = 0 := by
                have r5536 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := hd14 (-6)
                have b5537 := hb (x (-7) 1)
                have b5538 := hb (x (-6) 14)
                clear * - r5536 b5537 b5538 d5531
                omega
              have d5539 : (x (-7) 13).toNat = 0 := by
                have r5540 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
                have b5541 := hb (x (-7) 1)
                have b5542 := hb (x (-7) 13)
                clear * - r5540 b5541 b5542 d5535
                omega
              have d5543 : (x (-4) 12).toNat = 0 := by
                have r5544 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := hd12 (-4)
                have e5545 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                have e5546 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                have b5547 := hb (x (-7) 3)
                have b5548 := hb (x (-6) 2)
                have b5549 := hb (x (-5) 13)
                have b5550 := hb (x (-4) 12)
                clear * - r5544 e5545 e5546 b5547 b5548 b5549 b5550 d5526
                omega
              have d5551 : (x (-4) 1 && x (-4) 12).toNat = 0 := by
                have r5552 := hand2 (x (-4) 1) (x (-4) 12)
                have b5553 := hb (x (-4) 12)
                have b5554 := hb (x (-4) 1 && x (-4) 12)
                clear * - r5552 b5553 b5554 d5543
                omega
              have d5555 : (x (-6) 3).toNat = 0 := by
                have r5556 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := hd12 (-3)
                have e5557 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                have e5558 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                have b5559 := hb (x (-6) 3)
                have b5560 := hb (x (-5) 2)
                have b5561 := hb (x (-4) 13)
                have b5562 := hb (x (-3) 12)
                clear * - r5556 e5557 e5558 b5559 b5560 b5561 b5562 d5481 d5485 d5493
                omega
              have d5563 : (x (-6) 3 && x (-6) 14).toNat = 0 := by
                have r5564 := hand1 (x (-6) 3) (x (-6) 14)
                have b5565 := hb (x (-6) 3)
                have b5566 := hb (x (-6) 3 && x (-6) 14)
                clear * - r5564 b5565 b5566 d5555
                omega
              have d5567 : (x (-6) 3 && x (-6) 13).toNat = 0 := by
                have r5568 := hand1 (x (-6) 3) (x (-6) 13)
                have b5569 := hb (x (-6) 3)
                have b5570 := hb (x (-6) 3 && x (-6) 13)
                clear * - r5568 b5569 b5570 d5555
                omega
              have d5571 : (x (-7) 4).toNat = 1 := by
                have r5572 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := hcov11 (-3)
                have b5573 := hb (x (-7) 4)
                have b5574 := hb (x (-3) 11)
                have b5575 := hb (x (-4) 1 && x (-4) 12)
                have b5576 := hb (x (-5) 2 && x (-5) 13)
                have b5577 := hb (x (-6) 3 && x (-6) 14)
                clear * - r5572 b5573 b5574 b5575 b5576 b5577 g1 d5551 d5501 d5563
                omega
              have d5578 : (x (-7) 12).toNat = 1 := by
                have r5579 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
                have b5580 := hb (x (-7) 4)
                have b5581 := hb (x (-7) 12)
                clear * - r5579 b5580 b5581 d5571
                omega
              have d5582 : (x (-8) 13).toNat = 0 := by
                have r5583 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := hd12 (-7)
                have e5584 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
                have e5585 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
                have b5586 := hb (x (-10) 3)
                have b5587 := hb (x (-9) 2)
                have b5588 := hb (x (-8) 13)
                have b5589 := hb (x (-7) 12)
                clear * - r5583 e5584 e5585 b5586 b5587 b5588 b5589 d5578
                omega
              have d5590 : (x (-8) 5).toNat = 0 := by
                have r5591 : (x (-8) 5).toNat ≤ (x (-8) 13).toNat := himp _ _ (hp5 (-8))
                have b5592 := hb (x (-8) 5)
                have b5593 := hb (x (-8) 13)
                clear * - r5591 b5592 b5593 d5582
                omega
              have d5594 : (x (-9) 2).toNat = 0 := by
                have r5595 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := hd12 (-7)
                have e5596 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
                have e5597 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
                have b5598 := hb (x (-10) 3)
                have b5599 := hb (x (-9) 2)
                have b5600 := hb (x (-8) 13)
                have b5601 := hb (x (-7) 12)
                clear * - r5595 e5596 e5597 b5598 b5599 b5600 b5601 d5578 d5582
                omega
              have d5602 : (x (-8) 1 && x (-8) 14).toNat = 1 := by
                have r5603 : 1 ≤ (x (-7) 13).toNat + (x (-8) 1 && x (-8) 14).toNat + (x (-9) 2).toNat := hcov13 (-7)
                have b5604 := hb (x (-9) 2)
                have b5605 := hb (x (-7) 13)
                have b5606 := hb (x (-8) 1 && x (-8) 14)
                clear * - r5603 b5604 b5605 b5606 d5539 d5594
                omega
              have d5607 : (x (-8) 1).toNat = 1 := by
                have r5608 := hand1 (x (-8) 1) (x (-8) 14)
                have b5609 := hb (x (-8) 1)
                have b5610 := hb (x (-8) 1 && x (-8) 14)
                clear * - r5608 b5609 b5610 d5602
                omega
              have d5611 : (x (-7) 14).toNat = 0 := by
                have r5612 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := hd14 (-7)
                have b5613 := hb (x (-8) 1)
                have b5614 := hb (x (-7) 14)
                clear * - r5612 b5613 b5614 d5607
                omega
              have d5615 : (x (-7) 4 && x (-7) 14).toNat = 0 := by
                have r5616 := hand2 (x (-7) 4) (x (-7) 14)
                have b5617 := hb (x (-7) 14)
                have b5618 := hb (x (-7) 4 && x (-7) 14)
                clear * - r5616 b5617 b5618 d5611
                omega
              have r5619 : 1 ≤ (x (-3) 10).toNat + (x (-4) 1 && x (-4) 11).toNat + (x (-5) 2 && x (-5) 12).toNat + (x (-6) 3 && x (-6) 13).toNat + (x (-7) 4 && x (-7) 14).toNat + (x (-8) 5).toNat := hcov10 (-3)
              have b5620 := hb (x (-8) 5)
              have b5621 := hb (x (-3) 10)
              have b5622 := hb (x (-4) 1 && x (-4) 11)
              have b5623 := hb (x (-5) 2 && x (-5) 12)
              have b5624 := hb (x (-6) 3 && x (-6) 13)
              have b5625 := hb (x (-7) 4 && x (-7) 14)
              linarith only [r5619, b5620, b5621, b5622, b5623, b5624, b5625, d5231, d5247, d5505, d5567, d5615, d5590]
          · have f5626 : (x 1 11).toNat = 1 := by rw [h5147]; rfl
            have d5627 : (x 4 8).toNat = 0 := by
              have r5628 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := hd8 4
              have e5629 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
              have e5630 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
              have e5631 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
              have e5632 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
              have e5633 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
              have e5634 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
              have b5635 := hb (x (-3) 7)
              have b5636 := hb (x (-2) 6)
              have b5637 := hb (x (-1) 5)
              have b5638 := hb (x 0 4)
              have b5639 := hb (x 1 11)
              have b5640 := hb (x 2 10)
              have b5641 := hb (x 3 9)
              have b5642 := hb (x 4 8)
              clear * - r5628 e5629 e5630 e5631 e5632 e5633 e5634 b5635 b5636 b5637 b5638 b5639 b5640 b5641 b5642 g21 f5626 g9 g4
              omega
            have d5643 : (x 4 8 && x 4 13).toNat = 0 := by
              have r5644 := hand1 (x 4 8) (x 4 13)
              have b5645 := hb (x 4 8)
              have b5646 := hb (x 4 8 && x 4 13)
              clear * - r5644 b5645 b5646 d5627
              omega
            have d5647 : (x 3 9).toNat = 0 := by
              have r5648 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := hd8 4
              have e5649 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
              have e5650 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
              have e5651 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
              have e5652 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
              have e5653 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
              have e5654 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
              have b5655 := hb (x (-3) 7)
              have b5656 := hb (x (-2) 6)
              have b5657 := hb (x (-1) 5)
              have b5658 := hb (x 0 4)
              have b5659 := hb (x 1 11)
              have b5660 := hb (x 2 10)
              have b5661 := hb (x 3 9)
              have b5662 := hb (x 4 8)
              clear * - r5648 e5649 e5650 e5651 e5652 e5653 e5654 b5655 b5656 b5657 b5658 b5659 b5660 b5661 b5662 d5627 g21 f5626 g9 g4
              omega
            have d5663 : (x 3 9 && x 3 14).toNat = 0 := by
              have r5664 := hand1 (x 3 9) (x 3 14)
              have b5665 := hb (x 3 9)
              have b5666 := hb (x 3 9 && x 3 14)
              clear * - r5664 b5665 b5666 d5647
              omega
            have r5667 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := hcount 12
            have r5668 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := hcount 14
            have r5669 : (x 16 1).toNat + (x 15 2).toNat + (x 14 3).toNat + (x 13 4).toNat + (x 12 5).toNat + (x 11 6).toNat + (x 10 7).toNat + (x 9 8).toNat + (x 8 9).toNat + (x 7 10).toNat + (x 6 11).toNat + (x 5 12).toNat + (x 4 13).toNat + (x 3 14).toNat = 3 := hcount 17
            have r5670 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := hd12 2
            have e5671 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
            have e5672 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
            have r5673 : 1 ≤ (x 12 5).toNat + (x 11 1 && x 11 6).toNat + (x 10 2 && x 10 7).toNat + (x 9 3 && x 9 8).toNat + (x 8 4 && x 8 9).toNat + (x 7 5 && x 7 10).toNat + (x 6 6 && x 6 11).toNat + (x 5 7 && x 5 12).toNat + (x 4 8 && x 4 13).toNat + (x 3 9 && x 3 14).toNat + (x 2 10).toNat := hcov5 12
            have r5674 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := hcov6 8
            have r5675 : 1 ≤ (x 8 9).toNat + (x 7 1 && x 7 10).toNat + (x 6 2 && x 6 11).toNat + (x 5 3 && x 5 12).toNat + (x 4 4 && x 4 13).toNat + (x 3 5 && x 3 14).toNat + (x 2 6).toNat := hcov9 8
            have r5676 : 1 ≤ (x 12 10).toNat + (x 11 1 && x 11 11).toNat + (x 10 2 && x 10 12).toNat + (x 9 3 && x 9 13).toNat + (x 8 4 && x 8 14).toNat + (x 7 5).toNat := hcov10 12
            have r5677 : 1 ≤ (x 14 11).toNat + (x 13 1 && x 13 12).toNat + (x 12 2 && x 12 13).toNat + (x 11 3 && x 11 14).toNat + (x 10 4).toNat := hcov11 14
            have r5678 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
            have r5679 : (x 12 10).toNat ≤ (x 12 2).toNat := himp _ _ (hp10 12)
            have r5680 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
            have r5681 := hand2 (x 11 1) (x 11 6)
            have r5682 := hand2 (x 10 2) (x 10 7)
            have r5683 := hand2 (x 9 3) (x 9 8)
            have r5684 := hand2 (x 6 6) (x 6 11)
            have r5685 := hand1 (x 5 7) (x 5 12)
            have r5686 := hand2 (x 7 1) (x 7 7)
            have r5687 := hand2 (x 5 3) (x 5 9)
            have r5688 := hand2 (x 7 1) (x 7 10)
            have r5689 := hand2 (x 5 3) (x 5 12)
            have r5690 := hand1 (x 11 1) (x 11 11)
            have r5691 := hand1 (x 10 2) (x 10 12)
            have r5692 := hand1 (x 9 3) (x 9 13)
            have r5693 := hand1 (x 13 1) (x 13 12)
            have r5694 := hand1 (x 12 2) (x 12 13)
            have r5695 := hand1 (x 11 3) (x 11 14)
            have r5696 := hand2 (x 3 1) (x 3 14)
            have b5697 := hb (x (-2) 14)
            have b5698 := hb (x (-1) 3)
            have b5699 := hb (x (-1) 9)
            have b5700 := hb (x (-1) 13)
            have b5701 := hb (x 0 2)
            have b5702 := hb (x 0 12)
            have b5703 := hb (x 0 14)
            have b5704 := hb (x 1 11)
            have b5705 := hb (x 1 13)
            have b5706 := hb (x 2 2)
            have b5707 := hb (x 2 6)
            have b5708 := hb (x 2 10)
            have b5709 := hb (x 2 12)
            have b5710 := hb (x 3 9)
            have b5711 := hb (x 3 11)
            have b5712 := hb (x 3 14)
            have b5713 := hb (x 4 8)
            have b5714 := hb (x 4 10)
            have b5715 := hb (x 4 13)
            have b5716 := hb (x 5 7)
            have b5717 := hb (x 5 9)
            have b5718 := hb (x 5 12)
            have b5719 := hb (x 6 6)
            have b5720 := hb (x 6 8)
            have b5721 := hb (x 6 11)
            have b5722 := hb (x 7 5)
            have b5723 := hb (x 7 7)
            have b5724 := hb (x 7 10)
            have b5725 := hb (x 8 4)
            have b5726 := hb (x 8 6)
            have b5727 := hb (x 8 9)
            have b5728 := hb (x 9 3)
            have b5729 := hb (x 9 5)
            have b5730 := hb (x 9 8)
            have b5731 := hb (x 10 2)
            have b5732 := hb (x 10 4)
            have b5733 := hb (x 10 7)
            have b5734 := hb (x 11 1)
            have b5735 := hb (x 11 3)
            have b5736 := hb (x 11 6)
            have b5737 := hb (x 12 2)
            have b5738 := hb (x 12 5)
            have b5739 := hb (x 12 10)
            have b5740 := hb (x 13 1)
            have b5741 := hb (x 13 4)
            have b5742 := hb (x 14 3)
            have b5743 := hb (x 14 11)
            have b5744 := hb (x 15 2)
            have b5745 := hb (x 16 1)
            have b5746 := hb (x 11 1 && x 11 6)
            have b5747 := hb (x 10 2 && x 10 7)
            have b5748 := hb (x 9 3 && x 9 8)
            have b5749 := hb (x 8 4 && x 8 9)
            have b5750 := hb (x 7 5 && x 7 10)
            have b5751 := hb (x 6 6 && x 6 11)
            have b5752 := hb (x 5 7 && x 5 12)
            have b5753 := hb (x 4 8 && x 4 13)
            have b5754 := hb (x 3 9 && x 3 14)
            have b5755 := hb (x 7 1 && x 7 7)
            have b5756 := hb (x 6 2 && x 6 8)
            have b5757 := hb (x 5 3 && x 5 9)
            have b5758 := hb (x 4 4 && x 4 10)
            have b5759 := hb (x 3 5 && x 3 11)
            have b5760 := hb (x 2 6 && x 2 12)
            have b5761 := hb (x 1 7 && x 1 13)
            have b5762 := hb (x 0 8 && x 0 14)
            have b5763 := hb (x 7 1 && x 7 10)
            have b5764 := hb (x 6 2 && x 6 11)
            have b5765 := hb (x 5 3 && x 5 12)
            have b5766 := hb (x 4 4 && x 4 13)
            have b5767 := hb (x 3 5 && x 3 14)
            have b5768 := hb (x 11 1 && x 11 11)
            have b5769 := hb (x 10 2 && x 10 12)
            have b5770 := hb (x 9 3 && x 9 13)
            have b5771 := hb (x 8 4 && x 8 14)
            have b5772 := hb (x 13 1 && x 13 12)
            have b5773 := hb (x 12 2 && x 12 13)
            have b5774 := hb (x 11 3 && x 11 14)
            have b5775 := hb (x 3 1 && x 3 14)
            linarith only [r5667, r5668, r5669, r5670, e5671, e5672, r5673, r5674, r5675, r5676, r5677, r5678, r5679, r5680, r5681, r5682, r5683, r5684, r5685, r5686, r5687, r5688, r5689, r5690, r5691, r5692, r5693, r5694, r5695, r5696, b5697, b5698, b5699, b5700, b5701, b5702, b5703, b5704, b5705, b5706, b5707, b5708, b5709, b5710, b5711, b5712, b5713, b5714, b5715, b5716, b5717, b5718, b5719, b5720, b5721, b5722, b5723, b5724, b5725, b5726, b5727, b5728, b5729, b5730, b5731, b5732, b5733, b5734, b5735, b5736, b5737, b5738, b5739, b5740, b5741, b5742, b5743, b5744, b5745, b5746, b5747, b5748, b5749, b5750, b5751, b5752, b5753, b5754, b5755, b5756, b5757, b5758, b5759, b5760, b5761, b5762, b5763, b5764, b5765, b5766, b5767, b5768, b5769, b5770, b5771, b5772, b5773, b5774, b5775, g3, f5144, g5, g6, g7, g14, g16, f5626, g20, d4963, g21, d5647, d5627, d5047, d5027, d5035, d5051, d5643, d5663, d5067, g29, g30, d4967, d5139, g31, d5063, g40, g41, d5031]
        · have f5776 : (x (-1) 6).toNat = 1 := by rw [h5145]; rfl
          have d5777 : (x (-1) 14).toNat = 1 := by
            have r5778 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
            have b5779 := hb (x (-1) 6)
            have b5780 := hb (x (-1) 14)
            clear * - r5778 b5779 b5780 f5776
            omega
          have d5781 : (x (-2) 1).toNat = 0 := by
            have r5782 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := hd14 (-1)
            have b5783 := hb (x (-2) 1)
            have b5784 := hb (x (-1) 14)
            clear * - r5782 b5783 b5784 d5777
            omega
          have d5785 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
            have r5786 := hand1 (x (-2) 1) (x (-2) 14)
            have b5787 := hb (x (-2) 1)
            have b5788 := hb (x (-2) 1 && x (-2) 14)
            clear * - r5786 b5787 b5788 d5781
            omega
          have d5789 : (x (-2) 13).toNat = 0 := by
            have r5790 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
            have b5791 := hb (x (-2) 1)
            have b5792 := hb (x (-2) 13)
            clear * - r5790 b5791 b5792 d5781
            omega
          have d5793 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
            have r5794 := hand2 (x (-2) 2) (x (-2) 13)
            have b5795 := hb (x (-2) 13)
            have b5796 := hb (x (-2) 2 && x (-2) 13)
            clear * - r5794 b5795 b5796 d5789
            omega
          have d5797 : (x (-3) 2).toNat = 1 := by
            have r5798 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := hcov13 (-1)
            have b5799 := hb (x (-3) 2)
            have b5800 := hb (x (-1) 13)
            have b5801 := hb (x (-2) 1 && x (-2) 14)
            clear * - r5798 b5799 b5800 b5801 g6 d5785
            omega
          have d5802 : (x (-3) 14).toNat = 1 := by
            have r5803 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
            have b5804 := hb (x (-3) 2)
            have b5805 := hb (x (-3) 14)
            clear * - r5803 b5804 b5805 d5797
            omega
          have d5806 : (x (-4) 1).toNat = 0 := by
            have r5807 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := hd14 (-3)
            have b5808 := hb (x (-4) 1)
            have b5809 := hb (x (-3) 14)
            clear * - r5807 b5808 b5809 d5802
            omega
          have d5810 : (x (-4) 13).toNat = 0 := by
            have r5811 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
            have b5812 := hb (x (-4) 1)
            have b5813 := hb (x (-4) 13)
            clear * - r5811 b5812 b5813 d5806
            omega
          have d5814 : (x (-4) 2).toNat = 1 := by
            have r5815 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := hcov13 (-2)
            have b5816 := hb (x (-4) 2)
            have b5817 := hb (x (-2) 13)
            have b5818 := hb (x (-3) 1 && x (-3) 14)
            clear * - r5815 b5816 b5817 b5818 d5789 g56
            omega
          have d5819 : (x (-4) 14).toNat = 1 := by
            have r5820 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
            have b5821 := hb (x (-4) 2)
            have b5822 := hb (x (-4) 14)
            clear * - r5820 b5821 b5822 d5814
            omega
          have d5823 : (x (-5) 1).toNat = 0 := by
            have r5824 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := hd14 (-4)
            have b5825 := hb (x (-5) 1)
            have b5826 := hb (x (-4) 14)
            clear * - r5824 b5825 b5826 d5819
            omega
          have d5827 : (x (-5) 1 && x (-5) 14).toNat = 0 := by
            have r5828 := hand1 (x (-5) 1) (x (-5) 14)
            have b5829 := hb (x (-5) 1)
            have b5830 := hb (x (-5) 1 && x (-5) 14)
            clear * - r5828 b5829 b5830 d5823
            omega
          have d5831 : (x (-5) 13).toNat = 0 := by
            have r5832 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
            have b5833 := hb (x (-5) 1)
            have b5834 := hb (x (-5) 13)
            clear * - r5832 b5833 b5834 d5823
            omega
          have d5835 : (x (-6) 2).toNat = 1 := by
            have r5836 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := hcov13 (-4)
            have b5837 := hb (x (-6) 2)
            have b5838 := hb (x (-4) 13)
            have b5839 := hb (x (-5) 1 && x (-5) 14)
            clear * - r5836 b5837 b5838 b5839 d5810 d5827
            omega
          have d5840 : (x (-4) 12).toNat = 0 := by
            have r5841 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := hd12 (-4)
            have e5842 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
            have e5843 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
            have b5844 := hb (x (-7) 3)
            have b5845 := hb (x (-6) 2)
            have b5846 := hb (x (-5) 13)
            have b5847 := hb (x (-4) 12)
            clear * - r5841 e5842 e5843 b5844 b5845 b5846 b5847 d5831 d5835
            omega
          have d5848 : (x (-4) 4).toNat = 0 := by
            have r5849 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
            have b5850 := hb (x (-4) 4)
            have b5851 := hb (x (-4) 12)
            clear * - r5849 b5850 b5851 d5840
            omega
          have r5852 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := hcov11 0
          have b5853 := hb (x (-4) 4)
          have b5854 := hb (x 0 11)
          have b5855 := hb (x (-1) 1 && x (-1) 12)
          have b5856 := hb (x (-2) 2 && x (-2) 13)
          have b5857 := hb (x (-3) 3 && x (-3) 14)
          linarith only [r5852, b5853, b5854, b5855, b5856, b5857, g13, g48, d5793, g49, d5848]
      · have f5858 : (x (-1) 3).toNat = 1 := by rw [h5143]; rfl
        have d5859 : (x 2 12).toNat = 0 := by
          have r5860 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := hd12 2
          have e5861 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
          have e5862 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
          have b5863 := hb (x (-1) 3)
          have b5864 := hb (x 0 2)
          have b5865 := hb (x 1 13)
          have b5866 := hb (x 2 12)
          clear * - r5860 e5861 e5862 b5863 b5864 b5865 b5866 g7 f5858
          omega
        have d5867 : (x 1 13).toNat = 0 := by
          have r5868 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := hd12 2
          have e5869 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
          have e5870 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
          have b5871 := hb (x (-1) 3)
          have b5872 := hb (x 0 2)
          have b5873 := hb (x 1 13)
          have b5874 := hb (x 2 12)
          clear * - r5868 e5869 e5870 b5871 b5872 b5873 b5874 d5859 g7 f5858
          omega
        have d5875 : (x (-1) 2).toNat = 1 := by
          have r5876 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := hcov13 1
          have b5877 := hb (x (-1) 2)
          have b5878 := hb (x 1 13)
          have b5879 := hb (x 0 1 && x 0 14)
          clear * - r5876 b5877 b5878 b5879 d5867 g57
          omega
        have d5880 : (x (-1) 14).toNat = 1 := by
          have r5881 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
          have b5882 := hb (x (-1) 2)
          have b5883 := hb (x (-1) 14)
          clear * - r5881 b5882 b5883 d5875
          omega
        have d5884 : (x (-2) 1).toNat = 0 := by
          have r5885 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := hd14 (-1)
          have b5886 := hb (x (-2) 1)
          have b5887 := hb (x (-1) 14)
          clear * - r5885 b5886 b5887 d5880
          omega
        have d5888 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
          have r5889 := hand1 (x (-2) 1) (x (-2) 14)
          have b5890 := hb (x (-2) 1)
          have b5891 := hb (x (-2) 1 && x (-2) 14)
          clear * - r5889 b5890 b5891 d5884
          omega
        have d5892 : (x (-3) 2).toNat = 1 := by
          have r5893 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := hcov13 (-1)
          have b5894 := hb (x (-3) 2)
          have b5895 := hb (x (-1) 13)
          have b5896 := hb (x (-2) 1 && x (-2) 14)
          clear * - r5893 b5894 b5895 b5896 g6 d5888
          omega
        have d5897 : (x (-3) 14).toNat = 1 := by
          have r5898 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
          have b5899 := hb (x (-3) 2)
          have b5900 := hb (x (-3) 14)
          clear * - r5898 b5899 b5900 d5892
          omega
        have d5901 : (x (-4) 1).toNat = 0 := by
          have r5902 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := hd14 (-3)
          have b5903 := hb (x (-4) 1)
          have b5904 := hb (x (-3) 14)
          clear * - r5902 b5903 b5904 d5897
          omega
        have d5905 : (x (-4) 13).toNat = 0 := by
          have r5906 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
          have b5907 := hb (x (-4) 1)
          have b5908 := hb (x (-4) 13)
          clear * - r5906 b5907 b5908 d5901
          omega
        have d5909 : (x (-2) 13).toNat = 0 := by
          have r5910 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
          have b5911 := hb (x (-2) 1)
          have b5912 := hb (x (-2) 13)
          clear * - r5910 b5911 b5912 d5884
          omega
        have d5913 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
          have r5914 := hand2 (x (-2) 2) (x (-2) 13)
          have b5915 := hb (x (-2) 13)
          have b5916 := hb (x (-2) 2 && x (-2) 13)
          clear * - r5914 b5915 b5916 d5909
          omega
        have d5917 : (x (-4) 2).toNat = 1 := by
          have r5918 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := hcov13 (-2)
          have b5919 := hb (x (-4) 2)
          have b5920 := hb (x (-2) 13)
          have b5921 := hb (x (-3) 1 && x (-3) 14)
          clear * - r5918 b5919 b5920 b5921 d5909 g56
          omega
        have d5922 : (x (-4) 14).toNat = 1 := by
          have r5923 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
          have b5924 := hb (x (-4) 2)
          have b5925 := hb (x (-4) 14)
          clear * - r5923 b5924 b5925 d5917
          omega
        have d5926 : (x (-5) 1).toNat = 0 := by
          have r5927 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := hd14 (-4)
          have b5928 := hb (x (-5) 1)
          have b5929 := hb (x (-4) 14)
          clear * - r5927 b5928 b5929 d5922
          omega
        have d5930 : (x (-5) 1 && x (-5) 14).toNat = 0 := by
          have r5931 := hand1 (x (-5) 1) (x (-5) 14)
          have b5932 := hb (x (-5) 1)
          have b5933 := hb (x (-5) 1 && x (-5) 14)
          clear * - r5931 b5932 b5933 d5926
          omega
        have d5934 : (x (-6) 2).toNat = 1 := by
          have r5935 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := hcov13 (-4)
          have b5936 := hb (x (-6) 2)
          have b5937 := hb (x (-4) 13)
          have b5938 := hb (x (-5) 1 && x (-5) 14)
          clear * - r5935 b5936 b5937 b5938 d5905 d5930
          omega
        have d5939 : (x (-5) 13).toNat = 0 := by
          have r5940 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
          have b5941 := hb (x (-5) 1)
          have b5942 := hb (x (-5) 13)
          clear * - r5940 b5941 b5942 d5926
          omega
        have d5943 : (x (-4) 12).toNat = 0 := by
          have r5944 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := hd12 (-4)
          have e5945 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
          have e5946 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
          have b5947 := hb (x (-7) 3)
          have b5948 := hb (x (-6) 2)
          have b5949 := hb (x (-5) 13)
          have b5950 := hb (x (-4) 12)
          clear * - r5944 e5945 e5946 b5947 b5948 b5949 b5950 d5939 d5934
          omega
        have d5951 : (x (-4) 4).toNat = 0 := by
          have r5952 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
          have b5953 := hb (x (-4) 4)
          have b5954 := hb (x (-4) 12)
          clear * - r5952 b5953 b5954 d5943
          omega
        have r5955 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := hcov11 0
        have b5956 := hb (x (-4) 4)
        have b5957 := hb (x 0 11)
        have b5958 := hb (x (-1) 1 && x (-1) 12)
        have b5959 := hb (x (-2) 2 && x (-2) 13)
        have b5960 := hb (x (-3) 3 && x (-3) 14)
        linarith only [r5955, b5956, b5957, b5958, b5959, b5960, g13, g48, d5913, g49, d5951]
  · have f5961 : (x 0 6).toNat = 1 := by rw [h4458]; rfl
    have d5962 : (x 6 8).toNat = 0 := by
      have r5963 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
      have e5964 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e5965 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e5966 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e5967 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e5968 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e5969 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b5970 := hb (x (-1) 7)
      have b5971 := hb (x 0 6)
      have b5972 := hb (x 1 5)
      have b5973 := hb (x 2 4)
      have b5974 := hb (x 3 11)
      have b5975 := hb (x 4 10)
      have b5976 := hb (x 5 9)
      have b5977 := hb (x 6 8)
      clear * - r5963 e5964 e5965 e5966 e5967 e5968 e5969 b5970 b5971 b5972 b5973 b5974 b5975 b5976 b5977 f5961
      omega
    have d5978 : (x 5 9).toNat = 0 := by
      have r5979 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
      have e5980 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e5981 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e5982 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e5983 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e5984 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e5985 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b5986 := hb (x (-1) 7)
      have b5987 := hb (x 0 6)
      have b5988 := hb (x 1 5)
      have b5989 := hb (x 2 4)
      have b5990 := hb (x 3 11)
      have b5991 := hb (x 4 10)
      have b5992 := hb (x 5 9)
      have b5993 := hb (x 6 8)
      clear * - r5979 e5980 e5981 e5982 e5983 e5984 e5985 b5986 b5987 b5988 b5989 b5990 b5991 b5992 b5993 d5962 f5961
      omega
    have d5994 : (x 4 10).toNat = 0 := by
      have r5995 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
      have e5996 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e5997 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e5998 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e5999 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e6000 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e6001 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b6002 := hb (x (-1) 7)
      have b6003 := hb (x 0 6)
      have b6004 := hb (x 1 5)
      have b6005 := hb (x 2 4)
      have b6006 := hb (x 3 11)
      have b6007 := hb (x 4 10)
      have b6008 := hb (x 5 9)
      have b6009 := hb (x 6 8)
      clear * - r5995 e5996 e5997 e5998 e5999 e6000 e6001 b6002 b6003 b6004 b6005 b6006 b6007 b6008 b6009 d5962 d5978 f5961
      omega
    have d6010 : (x 4 1 && x 4 10).toNat = 0 := by
      have r6011 := hand2 (x 4 1) (x 4 10)
      have b6012 := hb (x 4 10)
      have b6013 := hb (x 4 1 && x 4 10)
      clear * - r6011 b6012 b6013 d5994
      omega
    have d6014 : (x 3 11).toNat = 0 := by
      have r6015 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
      have e6016 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e6017 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e6018 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e6019 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e6020 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e6021 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b6022 := hb (x (-1) 7)
      have b6023 := hb (x 0 6)
      have b6024 := hb (x 1 5)
      have b6025 := hb (x 2 4)
      have b6026 := hb (x 3 11)
      have b6027 := hb (x 4 10)
      have b6028 := hb (x 5 9)
      have b6029 := hb (x 6 8)
      clear * - r6015 e6016 e6017 e6018 e6019 e6020 e6021 b6022 b6023 b6024 b6025 b6026 b6027 b6028 b6029 d5962 d5978 d5994 f5961
      omega
    have d6030 : (x 3 1 && x 3 11).toNat = 0 := by
      have r6031 := hand2 (x 3 1) (x 3 11)
      have b6032 := hb (x 3 11)
      have b6033 := hb (x 3 1 && x 3 11)
      clear * - r6031 b6032 b6033 d6014
      omega
    have d6034 : (x 1 3 && x 1 13).toNat = 1 := by
      have r6035 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := hcov10 4
      have b6036 := hb (x (-1) 5)
      have b6037 := hb (x 4 10)
      have b6038 := hb (x 3 1 && x 3 11)
      have b6039 := hb (x 2 2 && x 2 12)
      have b6040 := hb (x 1 3 && x 1 13)
      have b6041 := hb (x 0 4 && x 0 14)
      clear * - r6035 b6036 b6037 b6038 b6039 b6040 b6041 d5994 d6030 g46 g47 g4
      omega
    have d6042 : (x 1 13).toNat = 1 := by
      have r6043 := hand2 (x 1 3) (x 1 13)
      have b6044 := hb (x 1 13)
      have b6045 := hb (x 1 3 && x 1 13)
      clear * - r6043 b6044 b6045 d6034
      omega
    have d6046 : (x 2 12).toNat = 0 := by
      have r6047 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := hd12 2
      have e6048 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e6049 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b6050 := hb (x (-1) 3)
      have b6051 := hb (x 0 2)
      have b6052 := hb (x 1 13)
      have b6053 := hb (x 2 12)
      clear * - r6047 e6048 e6049 b6050 b6051 b6052 b6053 d6042 g7
      omega
    have d6054 : (x 2 3 && x 2 12).toNat = 0 := by
      have r6055 := hand2 (x 2 3) (x 2 12)
      have b6056 := hb (x 2 12)
      have b6057 := hb (x 2 3 && x 2 12)
      clear * - r6055 b6056 b6057 d6046
      omega
    have d6058 : (x 3 2 && x 3 11).toNat = 0 := by
      have r6059 := hand2 (x 3 2) (x 3 11)
      have b6060 := hb (x 3 11)
      have b6061 := hb (x 3 2 && x 3 11)
      clear * - r6059 b6060 b6061 d6014
      omega
    have d6062 : (x (-1) 6).toNat = 1 := by
      have r6063 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := hcov9 5
      have b6064 := hb (x (-1) 6)
      have b6065 := hb (x 5 9)
      have b6066 := hb (x 4 1 && x 4 10)
      have b6067 := hb (x 3 2 && x 3 11)
      have b6068 := hb (x 2 3 && x 2 12)
      have b6069 := hb (x 1 4 && x 1 13)
      have b6070 := hb (x 0 5 && x 0 14)
      clear * - r6063 b6064 b6065 b6066 b6067 b6068 b6069 b6070 d5978 d6010 d6058 d6054 d4450 g37
      omega
    have d6071 : (x (-1) 14).toNat = 1 := by
      have r6072 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
      have b6073 := hb (x (-1) 6)
      have b6074 := hb (x (-1) 14)
      clear * - r6072 b6073 b6074 d6062
      omega
    have d6075 : (x (-2) 1).toNat = 0 := by
      have r6076 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := hd14 (-1)
      have b6077 := hb (x (-2) 1)
      have b6078 := hb (x (-1) 14)
      clear * - r6076 b6077 b6078 d6071
      omega
    have d6079 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
      have r6080 := hand1 (x (-2) 1) (x (-2) 14)
      have b6081 := hb (x (-2) 1)
      have b6082 := hb (x (-2) 1 && x (-2) 14)
      clear * - r6080 b6081 b6082 d6075
      omega
    have d6083 : (x (-3) 2).toNat = 1 := by
      have r6084 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := hcov13 (-1)
      have b6085 := hb (x (-3) 2)
      have b6086 := hb (x (-1) 13)
      have b6087 := hb (x (-2) 1 && x (-2) 14)
      clear * - r6084 b6085 b6086 b6087 g6 d6079
      omega
    have d6088 : (x (-3) 14).toNat = 1 := by
      have r6089 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
      have b6090 := hb (x (-3) 2)
      have b6091 := hb (x (-3) 14)
      clear * - r6089 b6090 b6091 d6083
      omega
    have d6092 : (x (-4) 1).toNat = 0 := by
      have r6093 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := hd14 (-3)
      have b6094 := hb (x (-4) 1)
      have b6095 := hb (x (-3) 14)
      clear * - r6093 b6094 b6095 d6088
      omega
    have d6096 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
      have r6097 := hand1 (x (-4) 1) (x (-4) 14)
      have b6098 := hb (x (-4) 1)
      have b6099 := hb (x (-4) 1 && x (-4) 14)
      clear * - r6097 b6098 b6099 d6092
      omega
    have d6100 : (x (-5) 2).toNat = 1 := by
      have r6101 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := hcov13 (-3)
      have b6102 := hb (x (-5) 2)
      have b6103 := hb (x (-3) 13)
      have b6104 := hb (x (-4) 1 && x (-4) 14)
      clear * - r6101 b6102 b6103 b6104 g2 d6096
      omega
    have d6105 : (x (-5) 14).toNat = 1 := by
      have r6106 : (x (-5) 2).toNat ≤ (x (-5) 14).toNat := himp _ _ (hp2 (-5))
      have b6107 := hb (x (-5) 2)
      have b6108 := hb (x (-5) 14)
      clear * - r6106 b6107 b6108 d6100
      omega
    have d6109 : (x (-6) 1).toNat = 0 := by
      have r6110 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := hd14 (-5)
      have b6111 := hb (x (-6) 1)
      have b6112 := hb (x (-5) 14)
      clear * - r6110 b6111 b6112 d6105
      omega
    have d6113 : (x (-6) 1 && x (-6) 14).toNat = 0 := by
      have r6114 := hand1 (x (-6) 1) (x (-6) 14)
      have b6115 := hb (x (-6) 1)
      have b6116 := hb (x (-6) 1 && x (-6) 14)
      clear * - r6114 b6115 b6116 d6109
      omega
    have d6117 : (x (-3) 12).toNat = 0 := by
      have r6118 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := hd12 (-3)
      have e6119 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e6120 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b6121 := hb (x (-6) 3)
      have b6122 := hb (x (-5) 2)
      have b6123 := hb (x (-4) 13)
      have b6124 := hb (x (-3) 12)
      clear * - r6118 e6119 e6120 b6121 b6122 b6123 b6124 d6100
      omega
    have d6125 : (x (-4) 13).toNat = 0 := by
      have r6126 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := hd12 (-3)
      have e6127 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e6128 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b6129 := hb (x (-6) 3)
      have b6130 := hb (x (-5) 2)
      have b6131 := hb (x (-4) 13)
      have b6132 := hb (x (-3) 12)
      clear * - r6126 e6127 e6128 b6129 b6130 b6131 b6132 d6117 d6100
      omega
    have d6133 : (x (-6) 3).toNat = 0 := by
      have r6134 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := hd12 (-3)
      have e6135 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e6136 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b6137 := hb (x (-6) 3)
      have b6138 := hb (x (-5) 2)
      have b6139 := hb (x (-4) 13)
      have b6140 := hb (x (-3) 12)
      clear * - r6134 e6135 e6136 b6137 b6138 b6139 b6140 d6117 d6125 d6100
      omega
    have d6141 : (x (-6) 3 && x (-6) 14).toNat = 0 := by
      have r6142 := hand1 (x (-6) 3) (x (-6) 14)
      have b6143 := hb (x (-6) 3)
      have b6144 := hb (x (-6) 3 && x (-6) 14)
      clear * - r6142 b6143 b6144 d6133
      omega
    have d6145 : (x (-4) 1 && x (-4) 12).toNat = 0 := by
      have r6146 := hand1 (x (-4) 1) (x (-4) 12)
      have b6147 := hb (x (-4) 1)
      have b6148 := hb (x (-4) 1 && x (-4) 12)
      clear * - r6146 b6147 b6148 d6092
      omega
    have d6149 : (x (-1) 12).toNat = 0 := by
      have r6150 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
      have e6151 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e6152 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b6153 := hb (x (-4) 3)
      have b6154 := hb (x (-3) 2)
      have b6155 := hb (x (-2) 13)
      have b6156 := hb (x (-1) 12)
      clear * - r6150 e6151 e6152 b6153 b6154 b6155 b6156 d6083
      omega
    have d6157 : (x (-2) 13).toNat = 0 := by
      have r6158 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
      have e6159 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e6160 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b6161 := hb (x (-4) 3)
      have b6162 := hb (x (-3) 2)
      have b6163 := hb (x (-2) 13)
      have b6164 := hb (x (-1) 12)
      clear * - r6158 e6159 e6160 b6161 b6162 b6163 b6164 d6149 d6083
      omega
    have d6165 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
      have r6166 := hand2 (x (-2) 2) (x (-2) 13)
      have b6167 := hb (x (-2) 13)
      have b6168 := hb (x (-2) 2 && x (-2) 13)
      clear * - r6166 b6167 b6168 d6157
      omega
    have d6169 : (x (-4) 4).toNat = 1 := by
      have r6170 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := hcov11 0
      have b6171 := hb (x (-4) 4)
      have b6172 := hb (x 0 11)
      have b6173 := hb (x (-1) 1 && x (-1) 12)
      have b6174 := hb (x (-2) 2 && x (-2) 13)
      have b6175 := hb (x (-3) 3 && x (-3) 14)
      clear * - r6170 b6171 b6172 b6173 b6174 b6175 g13 g48 d6165 g49
      omega
    have d6176 : (x (-4) 12).toNat = 1 := by
      have r6177 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
      have b6178 := hb (x (-4) 4)
      have b6179 := hb (x (-4) 12)
      clear * - r6177 b6178 b6179 d6169
      omega
    have d6180 : (x (-5) 13).toNat = 0 := by
      have r6181 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := hd12 (-4)
      have e6182 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e6183 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have b6184 := hb (x (-7) 3)
      have b6185 := hb (x (-6) 2)
      have b6186 := hb (x (-5) 13)
      have b6187 := hb (x (-4) 12)
      clear * - r6181 e6182 e6183 b6184 b6185 b6186 b6187 d6176
      omega
    have d6188 : (x (-5) 2 && x (-5) 13).toNat = 0 := by
      have r6189 := hand2 (x (-5) 2) (x (-5) 13)
      have b6190 := hb (x (-5) 13)
      have b6191 := hb (x (-5) 2 && x (-5) 13)
      clear * - r6189 b6190 b6191 d6180
      omega
    have d6192 : (x (-7) 4).toNat = 1 := by
      have r6193 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := hcov11 (-3)
      have b6194 := hb (x (-7) 4)
      have b6195 := hb (x (-3) 11)
      have b6196 := hb (x (-4) 1 && x (-4) 12)
      have b6197 := hb (x (-5) 2 && x (-5) 13)
      have b6198 := hb (x (-6) 3 && x (-6) 14)
      clear * - r6193 b6194 b6195 b6196 b6197 b6198 g1 d6145 d6188 d6141
      omega
    have d6199 : (x (-7) 12).toNat = 1 := by
      have r6200 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
      have b6201 := hb (x (-7) 4)
      have b6202 := hb (x (-7) 12)
      clear * - r6200 b6201 b6202 d6192
      omega
    have d6203 : (x (-8) 13).toNat = 0 := by
      have r6204 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := hd12 (-7)
      have e6205 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
      have e6206 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
      have b6207 := hb (x (-10) 3)
      have b6208 := hb (x (-9) 2)
      have b6209 := hb (x (-8) 13)
      have b6210 := hb (x (-7) 12)
      clear * - r6204 e6205 e6206 b6207 b6208 b6209 b6210 d6199
      omega
    have d6211 : (x (-9) 2).toNat = 0 := by
      have r6212 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := hd12 (-7)
      have e6213 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
      have e6214 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
      have b6215 := hb (x (-10) 3)
      have b6216 := hb (x (-9) 2)
      have b6217 := hb (x (-8) 13)
      have b6218 := hb (x (-7) 12)
      clear * - r6212 e6213 e6214 b6215 b6216 b6217 b6218 d6199 d6203
      omega
    have d6219 : (x (-5) 5).toNat = 0 := by
      have r6220 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
      have b6221 := hb (x (-5) 5)
      have b6222 := hb (x (-5) 13)
      clear * - r6220 b6221 b6222 d6180
      omega
    have d6223 : (x (-7) 2).toNat = 1 := by
      have r6224 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := hcov13 (-5)
      have b6225 := hb (x (-7) 2)
      have b6226 := hb (x (-5) 13)
      have b6227 := hb (x (-6) 1 && x (-6) 14)
      clear * - r6224 b6225 b6226 b6227 d6180 d6113
      omega
    have d6228 : (x (-7) 14).toNat = 1 := by
      have r6229 : (x (-7) 2).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp2 (-7))
      have b6230 := hb (x (-7) 2)
      have b6231 := hb (x (-7) 14)
      clear * - r6229 b6230 b6231 d6223
      omega
    have d6232 : (x (-8) 1).toNat = 0 := by
      have r6233 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := hd14 (-7)
      have b6234 := hb (x (-8) 1)
      have b6235 := hb (x (-7) 14)
      clear * - r6233 b6234 b6235 d6228
      omega
    have d6236 : (x (-8) 1 && x (-8) 14).toNat = 0 := by
      have r6237 := hand1 (x (-8) 1) (x (-8) 14)
      have b6238 := hb (x (-8) 1)
      have b6239 := hb (x (-8) 1 && x (-8) 14)
      clear * - r6237 b6238 b6239 d6232
      omega
    have d6240 : (x (-7) 13).toNat = 1 := by
      have r6241 : 1 ≤ (x (-7) 13).toNat + (x (-8) 1 && x (-8) 14).toNat + (x (-9) 2).toNat := hcov13 (-7)
      have b6242 := hb (x (-9) 2)
      have b6243 := hb (x (-7) 13)
      have b6244 := hb (x (-8) 1 && x (-8) 14)
      clear * - r6241 b6242 b6243 b6244 d6236 d6211
      omega
    have d6245 : (x (-7) 1).toNat = 1 := by
      have r6246 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
      have b6247 := hb (x (-7) 1)
      have b6248 := hb (x (-7) 13)
      clear * - r6246 b6247 b6248 d6240
      omega
    have d6249 : (x (-6) 14).toNat = 0 := by
      have r6250 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := hd14 (-6)
      have b6251 := hb (x (-7) 1)
      have b6252 := hb (x (-6) 14)
      clear * - r6250 b6251 b6252 d6245
      omega
    have d6253 : (x (-6) 2).toNat = 0 := by
      have r6254 : (x (-6) 2).toNat ≤ (x (-6) 14).toNat := himp _ _ (hp2 (-6))
      have b6255 := hb (x (-6) 2)
      have b6256 := hb (x (-6) 14)
      clear * - r6254 b6255 b6256 d6249
      omega
    have d6257 : (x (-5) 1 && x (-5) 14).toNat = 1 := by
      have r6258 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := hcov13 (-4)
      have b6259 := hb (x (-6) 2)
      have b6260 := hb (x (-4) 13)
      have b6261 := hb (x (-5) 1 && x (-5) 14)
      clear * - r6258 b6259 b6260 b6261 d6125 d6253
      omega
    have d6262 : (x (-5) 1).toNat = 1 := by
      have r6263 := hand1 (x (-5) 1) (x (-5) 14)
      have b6264 := hb (x (-5) 1)
      have b6265 := hb (x (-5) 1 && x (-5) 14)
      clear * - r6263 b6264 b6265 d6257
      omega
    have d6266 : (x (-4) 14).toNat = 0 := by
      have r6267 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := hd14 (-4)
      have b6268 := hb (x (-5) 1)
      have b6269 := hb (x (-4) 14)
      clear * - r6267 b6268 b6269 d6262
      omega
    have d6270 : (x (-4) 4 && x (-4) 14).toNat = 0 := by
      have r6271 := hand2 (x (-4) 4) (x (-4) 14)
      have b6272 := hb (x (-4) 14)
      have b6273 := hb (x (-4) 4 && x (-4) 14)
      clear * - r6271 b6272 b6273 d6266
      omega
    have d6274 : (x (-2) 2 && x (-2) 12).toNat = 1 := by
      have r6275 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := hcov10 0
      have b6276 := hb (x (-5) 5)
      have b6277 := hb (x 0 10)
      have b6278 := hb (x (-1) 1 && x (-1) 11)
      have b6279 := hb (x (-2) 2 && x (-2) 12)
      have b6280 := hb (x (-3) 3 && x (-3) 13)
      have b6281 := hb (x (-4) 4 && x (-4) 14)
      clear * - r6275 b6276 b6277 b6278 b6279 b6280 b6281 g12 g42 g43 d6270 d6219
      omega
    have d6282 : (x (-2) 12).toNat = 1 := by
      have r6283 := hand2 (x (-2) 2) (x (-2) 12)
      have b6284 := hb (x (-2) 12)
      have b6285 := hb (x (-2) 2 && x (-2) 12)
      clear * - r6283 b6284 b6285 d6274
      omega
    have d6286 : (x (-4) 2).toNat = 0 := by
      have r6287 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := hd12 (-2)
      have e6288 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e6289 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have b6290 := hb (x (-5) 3)
      have b6291 := hb (x (-4) 2)
      have b6292 := hb (x (-3) 13)
      have b6293 := hb (x (-2) 12)
      clear * - r6287 e6288 e6289 b6290 b6291 b6292 b6293 d6282 g2
      omega
    have r6294 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := hcov13 (-2)
    have b6295 := hb (x (-4) 2)
    have b6296 := hb (x (-2) 13)
    have b6297 := hb (x (-3) 1 && x (-3) 14)
    linarith only [r6294, b6295, b6296, b6297, d6157, g56, d6286]

theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b0000100 (x : ℤ → Fin 16 → Bool)
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
    (g3 : (x (-2) 14).toNat = 1)
    (g4 : (x (-1) 5).toNat = 0)
    (g5 : (x (-1) 9).toNat = 0)
    (g6 : (x (-1) 13).toNat = 0)
    (g7 : (x 0 2).toNat = 0)
    (g8 : (x 0 3).toNat = 0)
    (g9 : (x 0 4).toNat = 0)
    (g10 : (x 0 5).toNat = 0)
    (g11 : (x 0 7).toNat = 0)
    (g12 : (x 0 10).toNat = 0)
    (g13 : (x 0 11).toNat = 0)
    (g14 : (x 0 12).toNat = 0)
    (g15 : (x 0 13).toNat = 0)
    (g16 : (x 0 14).toNat = 1)
    (g17 : (x 1 3).toNat = 1)
    (g18 : (x 1 4).toNat = 0)
    (g19 : (x 1 8).toNat = 0)
    (g20 : (x 2 2).toNat = 0)
    (g21 : (x 2 10).toNat = 0)
    (g22 : (x 3 5).toNat = 0)
    (g23 : (x 3 13).toNat = 0)
    (g24 : (x 4 4).toNat = 0)
    (g25 : (x 2 2 && x 2 3).toNat = 0)
    (g26 : (x 0 4 && x 0 5).toNat = 0)
    (g27 : (x (-1) 5 && x (-1) 6).toNat = 0)
    (g28 : (x 0 13 && x 0 14).toNat = 0)
    (g29 : (x 4 4 && x 4 10).toNat = 0)
    (g30 : (x 3 5 && x 3 11).toNat = 0)
    (g31 : (x 0 8 && x 0 14).toNat = 0)
    (g32 : (x 4 5 && x 4 12).toNat = 0)
    (g33 : (x 3 6 && x 3 13).toNat = 0)
    (g34 : (x 2 2 && x 2 11).toNat = 0)
    (g35 : (x 0 4 && x 0 13).toNat = 0)
    (g36 : (x (-1) 5 && x (-1) 14).toNat = 0)
    (g37 : (x 0 5 && x 0 14).toNat = 0)
    (g38 : (x 4 3 && x 4 12).toNat = 0)
    (g39 : (x 3 4 && x 3 13).toNat = 0)
    (g40 : (x 4 4 && x 4 13).toNat = 0)
    (g41 : (x 3 5 && x 3 14).toNat = 0)
    (g42 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g43 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g44 : (x 0 2 && x 0 12).toNat = 0)
    (g45 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g46 : (x 2 2 && x 2 12).toNat = 0)
    (g47 : (x 0 4 && x 0 14).toNat = 0)
    (g48 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g49 : (x (-3) 3 && x (-3) 14).toNat = 0)
    (g50 : (x 0 1 && x 0 12).toNat = 0)
    (g51 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g52 : (x 0 2 && x 0 13).toNat = 0)
    (g53 : (x 0 3 && x 0 14).toNat = 0)
    (g54 : (x 4 1 && x 4 12).toNat = 0)
    (g55 : (x 3 2 && x 3 13).toNat = 0)
    (g56 : (x (-3) 1 && x (-3) 14).toNat = 0)
    (g57 : (x 0 1 && x 0 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b0000100_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57
