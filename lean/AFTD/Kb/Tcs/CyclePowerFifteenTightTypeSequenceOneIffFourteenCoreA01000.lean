import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a01000

Topic: combinatorics   Node: b056e276da71

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core: under the layer-free tight-cover constraints for k = 15 and 49 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a01000_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-5) 5).toNat = 0)
    (g1 : (x (-4) 4).toNat = 0)
    (g2 : (x (-3) 11).toNat = 0)
    (g3 : (x (-2) 10).toNat = 0)
    (g4 : (x (-1) 9).toNat = 0)
    (g5 : (x 0 1).toNat = 1)
    (g6 : (x 0 2).toNat = 0)
    (g7 : (x 0 3).toNat = 0)
    (g8 : (x 0 4).toNat = 0)
    (g9 : (x 0 6).toNat = 0)
    (g10 : (x 0 7).toNat = 0)
    (g11 : (x 0 8).toNat = 1)
    (g12 : (x 0 10).toNat = 0)
    (g13 : (x 0 11).toNat = 0)
    (g14 : (x 1 2).toNat = 0)
    (g15 : (x 1 6).toNat = 0)
    (g16 : (x 1 10).toNat = 0)
    (g17 : (x 2 1).toNat = 1)
    (g18 : (x 3 2).toNat = 0)
    (g19 : (x 3 4).toNat = 0)
    (g20 : (x 1 2 && x 1 6).toNat = 0)
    (g21 : (x 0 3 && x 0 7).toNat = 0)
    (g22 : (x 3 4 && x 3 8).toNat = 0)
    (g23 : (x 1 6 && x 1 10).toNat = 0)
    (g24 : (x 0 7 && x 0 11).toNat = 0)
    (g25 : (x 1 2 && x 1 7).toNat = 0)
    (g26 : (x 0 3 && x 0 8).toNat = 0)
    (g27 : (x (-1) 4 && x (-1) 9).toNat = 0)
    (g28 : (x (-2) 5 && x (-2) 10).toNat = 0)
    (g29 : (x (-3) 6 && x (-3) 11).toNat = 0)
    (g30 : (x 0 1 && x 0 7).toNat = 0)
    (g31 : (x (-4) 4 && x (-4) 11).toNat = 0)
    (g32 : (x (-5) 5 && x (-5) 12).toNat = 0)
    (g33 : (x (-6) 6 && x (-6) 13).toNat = 0)
    (g34 : (x (-7) 7 && x (-7) 14).toNat = 0)
    (g35 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g36 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g37 : (x 3 3 && x 3 12).toNat = 0)
    (g38 : (x 1 5 && x 1 14).toNat = 0)
    (g39 : (x (-4) 4 && x (-4) 14).toNat = 0)
    (g40 : (x 0 1 && x 0 11).toNat = 0)
    (g41 : (x 1 2 && x 1 13).toNat = 0)
    (g42 : (x 0 3 && x 0 14).toNat = 0)
    (g43 : (x 3 1 && x 3 12).toNat = 0)
    (g44 : (x 1 3 && x 1 14).toNat = 0)
    (g45 : (x 3 2 && x 3 13).toNat = 0)
    (g46 : (x 3 3 && x 3 14).toNat = 0)
    (g47 : (x 0 1 && x 0 14).toNat = 0)
    (g48 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  cases h42550 : x 0 12
  · have f42551 : (x 0 12).toNat = 0 := by rw [h42550]; rfl
    cases h42552 : x 0 13
    · have f42553 : (x 0 13).toNat = 0 := by rw [h42552]; rfl
      cases h42554 : x 1 1
      · have f42555 : (x 1 1).toNat = 0 := by rw [h42554]; rfl
        have d42556 : (x 1 13).toNat = 0 := by
          have r42557 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
          have b42558 := hb (x 1 1)
          have b42559 := hb (x 1 13)
          clear * - r42557 b42558 b42559 f42555
          omega
        have d42560 : (x (-1) 2).toNat = 1 := by
          have r42561 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := hcov13 1
          have b42562 := hb (x (-1) 2)
          have b42563 := hb (x 1 13)
          have b42564 := hb (x 0 1 && x 0 14)
          clear * - r42561 b42562 b42563 b42564 d42556 g47
          omega
        have d42565 : (x (-1) 14).toNat = 1 := by
          have r42566 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
          have b42567 := hb (x (-1) 2)
          have b42568 := hb (x (-1) 14)
          clear * - r42566 b42567 b42568 d42560
          omega
        have d42569 : (x (-2) 1).toNat = 0 := by
          have r42570 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := hd14 (-1)
          have b42571 := hb (x (-2) 1)
          have b42572 := hb (x (-1) 14)
          clear * - r42570 b42571 b42572 d42565
          omega
        have d42573 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
          have r42574 := hand1 (x (-2) 1) (x (-2) 14)
          have b42575 := hb (x (-2) 1)
          have b42576 := hb (x (-2) 1 && x (-2) 14)
          clear * - r42574 b42575 b42576 d42569
          omega
        have d42577 : (x (-2) 13).toNat = 0 := by
          have r42578 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
          have b42579 := hb (x (-2) 1)
          have b42580 := hb (x (-2) 13)
          clear * - r42578 b42579 b42580 d42569
          omega
        have d42581 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
          have r42582 := hand2 (x (-2) 3) (x (-2) 13)
          have b42583 := hb (x (-2) 13)
          have b42584 := hb (x (-2) 3 && x (-2) 13)
          clear * - r42582 b42583 b42584 d42577
          omega
        have d42585 : (x (-2) 9 && x (-2) 13).toNat = 0 := by
          have r42586 := hand2 (x (-2) 9) (x (-2) 13)
          have b42587 := hb (x (-2) 13)
          have b42588 := hb (x (-2) 9 && x (-2) 13)
          clear * - r42586 b42587 b42588 d42577
          omega
        have d42589 : (x (-2) 5).toNat = 0 := by
          have r42590 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
          have b42591 := hb (x (-2) 5)
          have b42592 := hb (x (-2) 13)
          clear * - r42590 b42591 b42592 d42577
          omega
        have d42593 : (x (-2) 5 && x (-2) 9).toNat = 0 := by
          have r42594 := hand1 (x (-2) 5) (x (-2) 9)
          have b42595 := hb (x (-2) 5)
          have b42596 := hb (x (-2) 5 && x (-2) 9)
          clear * - r42594 b42595 b42596 d42589
          omega
        have d42597 : (x (-2) 9).toNat = 0 := by
          have r42598 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
          have b42599 := hb (x (-2) 1)
          have b42600 := hb (x (-2) 9)
          clear * - r42598 b42599 b42600 d42569
          omega
        have d42601 : (x (-2) 2 && x (-2) 9).toNat = 0 := by
          have r42602 := hand2 (x (-2) 2) (x (-2) 9)
          have b42603 := hb (x (-2) 9)
          have b42604 := hb (x (-2) 2 && x (-2) 9)
          clear * - r42602 b42603 b42604 d42597
          omega
        have d42605 : (x (-2) 3 && x (-2) 9).toNat = 0 := by
          have r42606 := hand2 (x (-2) 3) (x (-2) 9)
          have b42607 := hb (x (-2) 9)
          have b42608 := hb (x (-2) 3 && x (-2) 9)
          clear * - r42606 b42607 b42608 d42597
          omega
        have d42609 : (x 1 12).toNat = 0 := by
          have r42610 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
          have e42611 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
          have e42612 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
          have b42613 := hb (x (-2) 3)
          have b42614 := hb (x (-1) 2)
          have b42615 := hb (x 0 13)
          have b42616 := hb (x 1 12)
          clear * - r42610 e42611 e42612 b42613 b42614 b42615 b42616 f42553 d42560
          omega
        have d42617 : (x 1 4).toNat = 0 := by
          have r42618 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
          have b42619 := hb (x 1 4)
          have b42620 := hb (x 1 12)
          clear * - r42618 b42619 b42620 d42609
          omega
        have d42621 : (x (-2) 3).toNat = 0 := by
          have r42622 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
          have e42623 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
          have e42624 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
          have b42625 := hb (x (-2) 3)
          have b42626 := hb (x (-1) 2)
          have b42627 := hb (x 0 13)
          have b42628 := hb (x 1 12)
          clear * - r42622 e42623 e42624 b42625 b42626 b42627 b42628 d42609 f42553 d42560
          omega
        cases h42629 : x (-1) 3
        · have f42630 : (x (-1) 3).toNat = 0 := by rw [h42629]; rfl
          have d42631 : (x (-1) 11).toNat = 0 := by
            have r42632 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
            have b42633 := hb (x (-1) 3)
            have b42634 := hb (x (-1) 11)
            clear * - r42632 b42633 b42634 f42630
            omega
          have d42635 : (x (-1) 1 && x (-1) 11).toNat = 0 := by
            have r42636 := hand2 (x (-1) 1) (x (-1) 11)
            have b42637 := hb (x (-1) 11)
            have b42638 := hb (x (-1) 1 && x (-1) 11)
            clear * - r42636 b42637 b42638 d42631
            omega
          have r42639 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := hcount 1
          have r42640 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
          have e42641 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
          have e42642 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
          have e42643 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
          have e42644 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
          have e42645 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
          have e42646 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
          have r42647 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
          have e42648 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e42649 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have r42650 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := hd12 0
          have e42651 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
          have e42652 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
          have r42653 : 1 ≤ (x 1 6).toNat + (x 0 1 && x 0 7).toNat + (x (-1) 2 && x (-1) 8).toNat + (x (-2) 3 && x (-2) 9).toNat + (x (-3) 4 && x (-3) 10).toNat + (x (-4) 5 && x (-4) 11).toNat + (x (-5) 6 && x (-5) 12).toNat + (x (-6) 7 && x (-6) 13).toNat + (x (-7) 8 && x (-7) 14).toNat + (x (-8) 9).toNat := hcov6 1
          have r42654 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := hcov9 (-1)
          have r42655 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := hcov10 0
          have r42656 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := hcov10 1
          have r42657 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := hcov13 (-1)
          have r42658 := hand2 (x (-1) 2) (x (-1) 8)
          have r42659 := hand2 (x (-3) 4) (x (-3) 10)
          have r42660 := hand2 (x (-4) 5) (x (-4) 11)
          have r42661 := hand1 (x (-5) 6) (x (-5) 12)
          have r42662 := hand1 (x (-6) 7) (x (-6) 13)
          have r42663 := hand1 (x (-7) 8) (x (-7) 14)
          have r42664 := hand1 (x (-4) 3) (x (-4) 12)
          have r42665 := hand1 (x (-5) 4) (x (-5) 13)
          have r42666 := hand1 (x (-6) 5) (x (-6) 14)
          have r42667 := hand1 (x (-2) 2) (x (-2) 12)
          have r42668 := hand1 (x (-3) 3) (x (-3) 13)
          have r42669 := hand2 (x (-1) 2) (x (-1) 12)
          have r42670 := hand1 (x (-3) 4) (x (-3) 14)
          have b42671 := hb (x (-13) 14)
          have b42672 := hb (x (-12) 13)
          have b42673 := hb (x (-11) 12)
          have b42674 := hb (x (-10) 11)
          have b42675 := hb (x (-9) 10)
          have b42676 := hb (x (-8) 7)
          have b42677 := hb (x (-8) 9)
          have b42678 := hb (x (-7) 6)
          have b42679 := hb (x (-7) 8)
          have b42680 := hb (x (-6) 5)
          have b42681 := hb (x (-6) 7)
          have b42682 := hb (x (-5) 4)
          have b42683 := hb (x (-5) 5)
          have b42684 := hb (x (-5) 6)
          have b42685 := hb (x (-4) 3)
          have b42686 := hb (x (-4) 5)
          have b42687 := hb (x (-4) 11)
          have b42688 := hb (x (-3) 2)
          have b42689 := hb (x (-3) 3)
          have b42690 := hb (x (-3) 4)
          have b42691 := hb (x (-3) 10)
          have b42692 := hb (x (-2) 2)
          have b42693 := hb (x (-2) 3)
          have b42694 := hb (x (-2) 9)
          have b42695 := hb (x (-2) 13)
          have b42696 := hb (x (-1) 2)
          have b42697 := hb (x (-1) 8)
          have b42698 := hb (x (-1) 9)
          have b42699 := hb (x (-1) 12)
          have b42700 := hb (x (-1) 13)
          have b42701 := hb (x 0 1)
          have b42702 := hb (x 0 10)
          have b42703 := hb (x 0 12)
          have b42704 := hb (x 1 6)
          have b42705 := hb (x 1 10)
          have b42706 := hb (x 0 1 && x 0 7)
          have b42707 := hb (x (-1) 2 && x (-1) 8)
          have b42708 := hb (x (-2) 3 && x (-2) 9)
          have b42709 := hb (x (-3) 4 && x (-3) 10)
          have b42710 := hb (x (-4) 5 && x (-4) 11)
          have b42711 := hb (x (-5) 6 && x (-5) 12)
          have b42712 := hb (x (-6) 7 && x (-6) 13)
          have b42713 := hb (x (-7) 8 && x (-7) 14)
          have b42714 := hb (x (-2) 1 && x (-2) 10)
          have b42715 := hb (x (-3) 2 && x (-3) 11)
          have b42716 := hb (x (-4) 3 && x (-4) 12)
          have b42717 := hb (x (-5) 4 && x (-5) 13)
          have b42718 := hb (x (-6) 5 && x (-6) 14)
          have b42719 := hb (x (-1) 1 && x (-1) 11)
          have b42720 := hb (x (-2) 2 && x (-2) 12)
          have b42721 := hb (x (-3) 3 && x (-3) 13)
          have b42722 := hb (x (-4) 4 && x (-4) 14)
          have b42723 := hb (x 0 1 && x 0 11)
          have b42724 := hb (x (-1) 2 && x (-1) 12)
          have b42725 := hb (x (-2) 3 && x (-2) 13)
          have b42726 := hb (x (-3) 4 && x (-3) 14)
          have b42727 := hb (x (-2) 1 && x (-2) 14)
          linarith only [r42639, r42640, e42641, e42642, e42643, e42644, e42645, e42646, r42647, e42648, e42649, r42650, e42651, e42652, r42653, r42654, r42655, r42656, r42657, r42658, r42659, r42660, r42661, r42662, r42663, r42664, r42665, r42666, r42667, r42668, r42669, r42670, b42671, b42672, b42673, b42674, b42675, b42676, b42677, b42678, b42679, b42680, b42681, b42682, b42683, b42684, b42685, b42686, b42687, b42688, b42689, b42690, b42691, b42692, b42693, b42694, b42695, b42696, b42697, b42698, b42699, b42700, b42701, b42702, b42703, b42704, b42705, b42706, b42707, b42708, b42709, b42710, b42711, b42712, b42713, b42714, b42715, b42716, b42717, b42718, b42719, b42720, b42721, b42722, b42723, b42724, b42725, b42726, b42727, g0, d42621, d42597, d42577, d42560, g4, g5, g12, f42551, g15, g16, g30, d42605, g35, g36, d42635, g39, g40, d42581, d42573]
        · have f42728 : (x (-1) 3).toNat = 1 := by rw [h42629]; rfl
          have d42729 : (x 2 12).toNat = 0 := by
            have r42730 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := hd12 2
            have e42731 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
            have e42732 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
            have b42733 := hb (x (-1) 3)
            have b42734 := hb (x 0 2)
            have b42735 := hb (x 1 13)
            have b42736 := hb (x 2 12)
            clear * - r42730 e42731 e42732 b42733 b42734 b42735 b42736 d42556 g6 f42728
            omega
          have d42737 : (x 2 1 && x 2 12).toNat = 0 := by
            have r42738 := hand2 (x 2 1) (x 2 12)
            have b42739 := hb (x 2 12)
            have b42740 := hb (x 2 1 && x 2 12)
            clear * - r42738 b42739 b42740 d42729
            omega
          have d42741 : (x 2 4).toNat = 0 := by
            have r42742 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
            have b42743 := hb (x 2 4)
            have b42744 := hb (x 2 12)
            clear * - r42742 b42743 b42744 d42729
            omega
          have d42745 : (x 2 4 && x 2 13).toNat = 0 := by
            have r42746 := hand1 (x 2 4) (x 2 13)
            have b42747 := hb (x 2 4)
            have b42748 := hb (x 2 4 && x 2 13)
            clear * - r42746 b42747 b42748 d42741
            omega
          cases h42749 : x 1 3
          · have f42750 : (x 1 3).toNat = 0 := by rw [h42749]; rfl
            cases h42751 : x (-1) 4
            · have f42752 : (x (-1) 4).toNat = 0 := by rw [h42751]; rfl
              have d42753 : (x 3 11).toNat = 1 := by
                have r42754 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := hcov11 3
                have b42755 := hb (x (-1) 4)
                have b42756 := hb (x 3 11)
                have b42757 := hb (x 2 1 && x 2 12)
                have b42758 := hb (x 1 2 && x 1 13)
                have b42759 := hb (x 0 3 && x 0 14)
                clear * - r42754 b42755 b42756 b42757 b42758 b42759 d42737 g41 g42 f42752
                omega
              have d42760 : (x 3 3).toNat = 1 := by
                have r42761 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
                have b42762 := hb (x 3 3)
                have b42763 := hb (x 3 11)
                clear * - r42761 b42762 b42763 d42753
                omega
              have d42764 : (x 6 12).toNat = 0 := by
                have r42765 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
                have e42766 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                have e42767 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                have b42768 := hb (x 3 3)
                have b42769 := hb (x 4 2)
                have b42770 := hb (x 5 13)
                have b42771 := hb (x 6 12)
                clear * - r42765 e42766 e42767 b42768 b42769 b42770 b42771 d42760
                omega
              have d42772 : (x 6 1 && x 6 12).toNat = 0 := by
                have r42773 := hand2 (x 6 1) (x 6 12)
                have b42774 := hb (x 6 12)
                have b42775 := hb (x 6 1 && x 6 12)
                clear * - r42773 b42774 b42775 d42764
                omega
              have d42776 : (x 6 4).toNat = 0 := by
                have r42777 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
                have b42778 := hb (x 6 4)
                have b42779 := hb (x 6 12)
                clear * - r42777 b42778 b42779 d42764
                omega
              have d42780 : (x 5 13).toNat = 0 := by
                have r42781 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
                have e42782 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                have e42783 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                have b42784 := hb (x 3 3)
                have b42785 := hb (x 4 2)
                have b42786 := hb (x 5 13)
                have b42787 := hb (x 6 12)
                clear * - r42781 e42782 e42783 b42784 b42785 b42786 b42787 d42764 d42760
                omega
              have d42788 : (x 5 2 && x 5 13).toNat = 0 := by
                have r42789 := hand2 (x 5 2) (x 5 13)
                have b42790 := hb (x 5 13)
                have b42791 := hb (x 5 2 && x 5 13)
                clear * - r42789 b42790 b42791 d42780
                omega
              have d42792 : (x 4 1 && x 4 14).toNat = 1 := by
                have r42793 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := hcov13 5
                have b42794 := hb (x 3 2)
                have b42795 := hb (x 5 13)
                have b42796 := hb (x 4 1 && x 4 14)
                clear * - r42793 b42794 b42795 b42796 d42780 g18
                omega
              have d42797 : (x 4 1).toNat = 1 := by
                have r42798 := hand1 (x 4 1) (x 4 14)
                have b42799 := hb (x 4 1)
                have b42800 := hb (x 4 1 && x 4 14)
                clear * - r42798 b42799 b42800 d42792
                omega
              have d42801 : (x 5 14).toNat = 0 := by
                have r42802 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
                have b42803 := hb (x 4 1)
                have b42804 := hb (x 5 14)
                clear * - r42802 b42803 b42804 d42797
                omega
              have d42805 : (x 5 1 && x 5 14).toNat = 0 := by
                have r42806 := hand2 (x 5 1) (x 5 14)
                have b42807 := hb (x 5 14)
                have b42808 := hb (x 5 1 && x 5 14)
                clear * - r42806 b42807 b42808 d42801
                omega
              have d42809 : (x 5 2).toNat = 0 := by
                have r42810 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
                have b42811 := hb (x 5 2)
                have b42812 := hb (x 5 14)
                clear * - r42810 b42811 b42812 d42801
                omega
              have d42813 : (x 4 2).toNat = 0 := by
                have r42814 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
                have e42815 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                have e42816 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                have b42817 := hb (x 3 3)
                have b42818 := hb (x 4 2)
                have b42819 := hb (x 5 13)
                have b42820 := hb (x 6 12)
                clear * - r42814 e42815 e42816 b42817 b42818 b42819 b42820 d42764 d42780 d42760
                omega
              have d42821 : (x 4 2 && x 4 13).toNat = 0 := by
                have r42822 := hand1 (x 4 2) (x 4 13)
                have b42823 := hb (x 4 2)
                have b42824 := hb (x 4 2 && x 4 13)
                clear * - r42822 b42823 b42824 d42813
                omega
              have d42825 : (x 6 13).toNat = 1 := by
                have r42826 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := hcov13 6
                have b42827 := hb (x 4 2)
                have b42828 := hb (x 6 13)
                have b42829 := hb (x 5 1 && x 5 14)
                clear * - r42826 b42827 b42828 b42829 d42805 d42813
                omega
              have d42830 : (x 6 1).toNat = 1 := by
                have r42831 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
                have b42832 := hb (x 6 1)
                have b42833 := hb (x 6 13)
                clear * - r42831 b42832 b42833 d42825
                omega
              have d42834 : (x 7 14).toNat = 0 := by
                have r42835 : (x 7 14).toNat + (x 6 1).toNat = 1 := hd14 7
                have b42836 := hb (x 6 1)
                have b42837 := hb (x 7 14)
                clear * - r42835 b42836 b42837 d42830
                omega
              have d42838 : (x 7 3 && x 7 14).toNat = 0 := by
                have r42839 := hand2 (x 7 3) (x 7 14)
                have b42840 := hb (x 7 14)
                have b42841 := hb (x 7 3 && x 7 14)
                clear * - r42839 b42840 b42841 d42834
                omega
              have d42842 : (x 7 2).toNat = 0 := by
                have r42843 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
                have b42844 := hb (x 7 2)
                have b42845 := hb (x 7 14)
                clear * - r42843 b42844 b42845 d42834
                omega
              have d42846 : (x 7 12).toNat = 0 := by
                have r42847 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
                have e42848 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                have e42849 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                have b42850 := hb (x 4 3)
                have b42851 := hb (x 5 2)
                have b42852 := hb (x 6 13)
                have b42853 := hb (x 7 12)
                clear * - r42847 e42848 e42849 b42850 b42851 b42852 b42853 d42825 d42809
                omega
              have d42854 : (x 7 4).toNat = 0 := by
                have r42855 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
                have b42856 := hb (x 7 4)
                have b42857 := hb (x 7 12)
                clear * - r42855 b42856 b42857 d42846
                omega
              have d42858 : (x 4 3).toNat = 0 := by
                have r42859 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
                have e42860 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                have e42861 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                have b42862 := hb (x 4 3)
                have b42863 := hb (x 5 2)
                have b42864 := hb (x 6 13)
                have b42865 := hb (x 7 12)
                clear * - r42859 e42860 e42861 b42862 b42863 b42864 b42865 d42846 d42825 d42809
                omega
              have d42866 : (x 4 3 && x 4 14).toNat = 0 := by
                have r42867 := hand1 (x 4 3) (x 4 14)
                have b42868 := hb (x 4 3)
                have b42869 := hb (x 4 3 && x 4 14)
                clear * - r42867 b42868 b42869 d42858
                omega
              have d42870 : (x 7 11).toNat = 1 := by
                have r42871 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := hcov11 7
                have b42872 := hb (x 3 4)
                have b42873 := hb (x 7 11)
                have b42874 := hb (x 6 1 && x 6 12)
                have b42875 := hb (x 5 2 && x 5 13)
                have b42876 := hb (x 4 3 && x 4 14)
                clear * - r42871 b42872 b42873 b42874 b42875 b42876 d42772 d42788 d42866 g19
                omega
              have d42877 : (x 7 3).toNat = 1 := by
                have r42878 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
                have b42879 := hb (x 7 3)
                have b42880 := hb (x 7 11)
                clear * - r42878 b42879 b42880 d42870
                omega
              have d42881 : (x 10 12).toNat = 0 := by
                have r42882 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
                have e42883 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                have e42884 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                have b42885 := hb (x 7 3)
                have b42886 := hb (x 8 2)
                have b42887 := hb (x 9 13)
                have b42888 := hb (x 10 12)
                clear * - r42882 e42883 e42884 b42885 b42886 b42887 b42888 d42877
                omega
              have d42889 : (x 10 1 && x 10 12).toNat = 0 := by
                have r42890 := hand2 (x 10 1) (x 10 12)
                have b42891 := hb (x 10 12)
                have b42892 := hb (x 10 1 && x 10 12)
                clear * - r42890 b42891 b42892 d42881
                omega
              have d42893 : (x 10 4).toNat = 0 := by
                have r42894 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
                have b42895 := hb (x 10 4)
                have b42896 := hb (x 10 12)
                clear * - r42894 b42895 b42896 d42881
                omega
              have d42897 : (x 9 13).toNat = 0 := by
                have r42898 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
                have e42899 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                have e42900 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                have b42901 := hb (x 7 3)
                have b42902 := hb (x 8 2)
                have b42903 := hb (x 9 13)
                have b42904 := hb (x 10 12)
                clear * - r42898 e42899 e42900 b42901 b42902 b42903 b42904 d42881 d42877
                omega
              have d42905 : (x 9 2 && x 9 13).toNat = 0 := by
                have r42906 := hand2 (x 9 2) (x 9 13)
                have b42907 := hb (x 9 13)
                have b42908 := hb (x 9 2 && x 9 13)
                clear * - r42906 b42907 b42908 d42897
                omega
              have d42909 : (x 8 1 && x 8 14).toNat = 1 := by
                have r42910 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := hcov13 9
                have b42911 := hb (x 7 2)
                have b42912 := hb (x 9 13)
                have b42913 := hb (x 8 1 && x 8 14)
                clear * - r42910 b42911 b42912 b42913 d42897 d42842
                omega
              have d42914 : (x 8 14).toNat = 1 := by
                have r42915 := hand2 (x 8 1) (x 8 14)
                have b42916 := hb (x 8 14)
                have b42917 := hb (x 8 1 && x 8 14)
                clear * - r42915 b42916 b42917 d42909
                omega
              have d42918 : (x 7 1).toNat = 0 := by
                have r42919 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
                have b42920 := hb (x 7 1)
                have b42921 := hb (x 8 14)
                clear * - r42919 b42920 b42921 d42914
                omega
              have d42922 : (x 7 13).toNat = 0 := by
                have r42923 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
                have b42924 := hb (x 7 1)
                have b42925 := hb (x 7 13)
                clear * - r42923 b42924 b42925 d42918
                omega
              have d42926 : (x 6 1 && x 6 14).toNat = 1 := by
                have r42927 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
                have b42928 := hb (x 5 2)
                have b42929 := hb (x 7 13)
                have b42930 := hb (x 6 1 && x 6 14)
                clear * - r42927 b42928 b42929 b42930 d42922 d42809
                omega
              have d42931 : (x 6 14).toNat = 1 := by
                have r42932 := hand2 (x 6 1) (x 6 14)
                have b42933 := hb (x 6 14)
                have b42934 := hb (x 6 1 && x 6 14)
                clear * - r42932 b42933 b42934 d42926
                omega
              have d42935 : (x 5 1).toNat = 0 := by
                have r42936 : (x 6 14).toNat + (x 5 1).toNat = 1 := hd14 6
                have b42937 := hb (x 5 1)
                have b42938 := hb (x 6 14)
                clear * - r42936 b42937 b42938 d42931
                omega
              have d42939 : (x 5 1 && x 5 12).toNat = 0 := by
                have r42940 := hand1 (x 5 1) (x 5 12)
                have b42941 := hb (x 5 1)
                have b42942 := hb (x 5 1 && x 5 12)
                clear * - r42940 b42941 b42942 d42935
                omega
              have d42943 : (x 6 11).toNat = 1 := by
                have r42944 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := hcov11 6
                have b42945 := hb (x 2 4)
                have b42946 := hb (x 6 11)
                have b42947 := hb (x 5 1 && x 5 12)
                have b42948 := hb (x 4 2 && x 4 13)
                have b42949 := hb (x 3 3 && x 3 14)
                clear * - r42944 b42945 b42946 b42947 b42948 b42949 d42939 d42821 g46 d42741
                omega
              have d42950 : (x 6 3).toNat = 1 := by
                have r42951 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
                have b42952 := hb (x 6 3)
                have b42953 := hb (x 6 11)
                clear * - r42951 b42952 b42953 d42943
                omega
              have d42954 : (x 9 12).toNat = 0 := by
                have r42955 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
                have e42956 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                have e42957 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                have b42958 := hb (x 6 3)
                have b42959 := hb (x 7 2)
                have b42960 := hb (x 8 13)
                have b42961 := hb (x 9 12)
                clear * - r42955 e42956 e42957 b42958 b42959 b42960 b42961 d42842 d42950
                omega
              have d42962 : (x 9 1 && x 9 12).toNat = 0 := by
                have r42963 := hand2 (x 9 1) (x 9 12)
                have b42964 := hb (x 9 12)
                have b42965 := hb (x 9 1 && x 9 12)
                clear * - r42963 b42964 b42965 d42954
                omega
              have d42966 : (x 8 13).toNat = 0 := by
                have r42967 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
                have e42968 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                have e42969 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                have b42970 := hb (x 6 3)
                have b42971 := hb (x 7 2)
                have b42972 := hb (x 8 13)
                have b42973 := hb (x 9 12)
                clear * - r42967 e42968 e42969 b42970 b42971 b42972 b42973 d42954 d42842 d42950
                omega
              have d42974 : (x 8 2 && x 8 13).toNat = 0 := by
                have r42975 := hand2 (x 8 2) (x 8 13)
                have b42976 := hb (x 8 13)
                have b42977 := hb (x 8 2 && x 8 13)
                clear * - r42975 b42976 b42977 d42966
                omega
              have d42978 : (x 10 11).toNat = 1 := by
                have r42979 : 1 ≤ (x 10 11).toNat + (x 9 1 && x 9 12).toNat + (x 8 2 && x 8 13).toNat + (x 7 3 && x 7 14).toNat + (x 6 4).toNat := hcov11 10
                have b42980 := hb (x 6 4)
                have b42981 := hb (x 10 11)
                have b42982 := hb (x 9 1 && x 9 12)
                have b42983 := hb (x 8 2 && x 8 13)
                have b42984 := hb (x 7 3 && x 7 14)
                clear * - r42979 b42980 b42981 b42982 b42983 b42984 d42962 d42974 d42838 d42776
                omega
              have d42985 : (x 10 3).toNat = 1 := by
                have r42986 : (x 10 11).toNat ≤ (x 10 3).toNat := himp _ _ (hp11 10)
                have b42987 := hb (x 10 3)
                have b42988 := hb (x 10 11)
                clear * - r42986 b42987 b42988 d42978
                omega
              have d42989 : (x 13 12).toNat = 0 := by
                have r42990 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
                have e42991 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
                have e42992 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
                have b42993 := hb (x 10 3)
                have b42994 := hb (x 11 2)
                have b42995 := hb (x 12 13)
                have b42996 := hb (x 13 12)
                clear * - r42990 e42991 e42992 b42993 b42994 b42995 b42996 d42985
                omega
              have d42997 : (x 13 1 && x 13 12).toNat = 0 := by
                have r42998 := hand2 (x 13 1) (x 13 12)
                have b42999 := hb (x 13 12)
                have b43000 := hb (x 13 1 && x 13 12)
                clear * - r42998 b42999 b43000 d42989
                omega
              have d43001 : (x 12 13).toNat = 0 := by
                have r43002 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
                have e43003 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
                have e43004 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
                have b43005 := hb (x 10 3)
                have b43006 := hb (x 11 2)
                have b43007 := hb (x 12 13)
                have b43008 := hb (x 13 12)
                clear * - r43002 e43003 e43004 b43005 b43006 b43007 b43008 d42989 d42985
                omega
              have d43009 : (x 12 2 && x 12 13).toNat = 0 := by
                have r43010 := hand2 (x 12 2) (x 12 13)
                have b43011 := hb (x 12 13)
                have b43012 := hb (x 12 2 && x 12 13)
                clear * - r43010 b43011 b43012 d43001
                omega
              have d43013 : (x 11 2).toNat = 0 := by
                have r43014 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
                have e43015 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
                have e43016 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
                have b43017 := hb (x 10 3)
                have b43018 := hb (x 11 2)
                have b43019 := hb (x 12 13)
                have b43020 := hb (x 13 12)
                clear * - r43014 e43015 e43016 b43017 b43018 b43019 b43020 d42989 d43001 d42985
                omega
              have d43021 : (x 8 1).toNat = 1 := by
                have r43022 := hand1 (x 8 1) (x 8 14)
                have b43023 := hb (x 8 1)
                have b43024 := hb (x 8 1 && x 8 14)
                clear * - r43022 b43023 b43024 d42909
                omega
              have d43025 : (x 9 14).toNat = 0 := by
                have r43026 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
                have b43027 := hb (x 8 1)
                have b43028 := hb (x 9 14)
                clear * - r43026 b43027 b43028 d43021
                omega
              have d43029 : (x 9 1 && x 9 14).toNat = 0 := by
                have r43030 := hand2 (x 9 1) (x 9 14)
                have b43031 := hb (x 9 14)
                have b43032 := hb (x 9 1 && x 9 14)
                clear * - r43030 b43031 b43032 d43025
                omega
              have d43033 : (x 9 2).toNat = 0 := by
                have r43034 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
                have b43035 := hb (x 9 2)
                have b43036 := hb (x 9 14)
                clear * - r43034 b43035 b43036 d43025
                omega
              have d43037 : (x 8 2).toNat = 0 := by
                have r43038 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
                have e43039 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                have e43040 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                have b43041 := hb (x 7 3)
                have b43042 := hb (x 8 2)
                have b43043 := hb (x 9 13)
                have b43044 := hb (x 10 12)
                clear * - r43038 e43039 e43040 b43041 b43042 b43043 b43044 d42881 d42897 d42877
                omega
              have d43045 : (x 10 13).toNat = 1 := by
                have r43046 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := hcov13 10
                have b43047 := hb (x 8 2)
                have b43048 := hb (x 10 13)
                have b43049 := hb (x 9 1 && x 9 14)
                clear * - r43046 b43047 b43048 b43049 d43029 d43037
                omega
              have d43050 : (x 10 1).toNat = 1 := by
                have r43051 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
                have b43052 := hb (x 10 1)
                have b43053 := hb (x 10 13)
                clear * - r43051 b43052 b43053 d43045
                omega
              have d43054 : (x 11 14).toNat = 0 := by
                have r43055 : (x 11 14).toNat + (x 10 1).toNat = 1 := hd14 11
                have b43056 := hb (x 10 1)
                have b43057 := hb (x 11 14)
                clear * - r43055 b43056 b43057 d43050
                omega
              have d43058 : (x 11 1 && x 11 14).toNat = 0 := by
                have r43059 := hand2 (x 11 1) (x 11 14)
                have b43060 := hb (x 11 14)
                have b43061 := hb (x 11 1 && x 11 14)
                clear * - r43059 b43060 b43061 d43054
                omega
              have d43062 : (x 10 2).toNat = 1 := by
                have r43063 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := hcov13 12
                have b43064 := hb (x 10 2)
                have b43065 := hb (x 12 13)
                have b43066 := hb (x 11 1 && x 11 14)
                clear * - r43063 b43064 b43065 b43066 d43001 d43058
                omega
              have d43067 : (x 12 12).toNat = 0 := by
                have r43068 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
                have e43069 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
                have e43070 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
                have b43071 := hb (x 9 3)
                have b43072 := hb (x 10 2)
                have b43073 := hb (x 11 13)
                have b43074 := hb (x 12 12)
                clear * - r43068 e43069 e43070 b43071 b43072 b43073 b43074 d43062
                omega
              have d43075 : (x 12 4).toNat = 0 := by
                have r43076 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
                have b43077 := hb (x 12 4)
                have b43078 := hb (x 12 12)
                clear * - r43076 b43077 b43078 d43067
                omega
              have d43079 : (x 12 4 && x 12 14).toNat = 0 := by
                have r43080 := hand1 (x 12 4) (x 12 14)
                have b43081 := hb (x 12 4)
                have b43082 := hb (x 12 4 && x 12 14)
                clear * - r43080 b43081 b43082 d43075
                omega
              have d43083 : (x 11 13).toNat = 0 := by
                have r43084 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
                have e43085 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
                have e43086 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
                have b43087 := hb (x 9 3)
                have b43088 := hb (x 10 2)
                have b43089 := hb (x 11 13)
                have b43090 := hb (x 12 12)
                clear * - r43084 e43085 e43086 b43087 b43088 b43089 b43090 d43067 d43062
                omega
              have d43091 : (x 11 5).toNat = 0 := by
                have r43092 : (x 11 5).toNat ≤ (x 11 13).toNat := himp _ _ (hp5 11)
                have b43093 := hb (x 11 5)
                have b43094 := hb (x 11 13)
                clear * - r43092 b43093 b43094 d43083
                omega
              have d43095 : (x 11 3 && x 11 14).toNat = 0 := by
                have r43096 := hand2 (x 11 3) (x 11 14)
                have b43097 := hb (x 11 14)
                have b43098 := hb (x 11 3 && x 11 14)
                clear * - r43096 b43097 b43098 d43054
                omega
              have d43099 : (x 14 11).toNat = 1 := by
                have r43100 : 1 ≤ (x 14 11).toNat + (x 13 1 && x 13 12).toNat + (x 12 2 && x 12 13).toNat + (x 11 3 && x 11 14).toNat + (x 10 4).toNat := hcov11 14
                have b43101 := hb (x 10 4)
                have b43102 := hb (x 14 11)
                have b43103 := hb (x 13 1 && x 13 12)
                have b43104 := hb (x 12 2 && x 12 13)
                have b43105 := hb (x 11 3 && x 11 14)
                clear * - r43100 b43101 b43102 b43103 b43104 b43105 d42997 d43009 d43095 d42893
                omega
              have d43106 : (x 14 3).toNat = 1 := by
                have r43107 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
                have b43108 := hb (x 14 3)
                have b43109 := hb (x 14 11)
                clear * - r43107 b43108 b43109 d43099
                omega
              have d43110 : (x 17 12).toNat = 0 := by
                have r43111 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
                have e43112 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                have e43113 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                have b43114 := hb (x 14 3)
                have b43115 := hb (x 15 2)
                have b43116 := hb (x 16 13)
                have b43117 := hb (x 17 12)
                clear * - r43111 e43112 e43113 b43114 b43115 b43116 b43117 d43106
                omega
              have d43118 : (x 16 13).toNat = 0 := by
                have r43119 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
                have e43120 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                have e43121 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                have b43122 := hb (x 14 3)
                have b43123 := hb (x 15 2)
                have b43124 := hb (x 16 13)
                have b43125 := hb (x 17 12)
                clear * - r43119 e43120 e43121 b43122 b43123 b43124 b43125 d43110 d43106
                omega
              have d43126 : (x 15 2).toNat = 0 := by
                have r43127 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
                have e43128 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                have e43129 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                have b43130 := hb (x 14 3)
                have b43131 := hb (x 15 2)
                have b43132 := hb (x 16 13)
                have b43133 := hb (x 17 12)
                clear * - r43127 e43128 e43129 b43130 b43131 b43132 b43133 d43110 d43118 d43106
                omega
              have d43134 : (x 11 12).toNat = 0 := by
                have r43135 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
                have e43136 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                have e43137 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                have b43138 := hb (x 8 3)
                have b43139 := hb (x 9 2)
                have b43140 := hb (x 10 13)
                have b43141 := hb (x 11 12)
                clear * - r43135 e43136 e43137 b43138 b43139 b43140 b43141 d43045 d43033
                omega
              have d43142 : (x 11 4).toNat = 0 := by
                have r43143 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
                have b43144 := hb (x 11 4)
                have b43145 := hb (x 11 12)
                clear * - r43143 b43144 b43145 d43134
                omega
              have d43146 : (x 8 3).toNat = 0 := by
                have r43147 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
                have e43148 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                have e43149 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                have b43150 := hb (x 8 3)
                have b43151 := hb (x 9 2)
                have b43152 := hb (x 10 13)
                have b43153 := hb (x 11 12)
                clear * - r43147 e43148 e43149 b43150 b43151 b43152 b43153 d43134 d43045 d43033
                omega
              have d43154 : (x 8 3 && x 8 14).toNat = 0 := by
                have r43155 := hand1 (x 8 3) (x 8 14)
                have b43156 := hb (x 8 3)
                have b43157 := hb (x 8 3 && x 8 14)
                clear * - r43155 b43156 b43157 d43146
                omega
              have d43158 : (x 11 11).toNat = 1 := by
                have r43159 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := hcov11 11
                have b43160 := hb (x 7 4)
                have b43161 := hb (x 11 11)
                have b43162 := hb (x 10 1 && x 10 12)
                have b43163 := hb (x 9 2 && x 9 13)
                have b43164 := hb (x 8 3 && x 8 14)
                clear * - r43159 b43160 b43161 b43162 b43163 b43164 d42889 d42905 d43154 d42854
                omega
              have d43165 : (x 11 3).toNat = 1 := by
                have r43166 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
                have b43167 := hb (x 11 3)
                have b43168 := hb (x 11 11)
                clear * - r43166 b43167 b43168 d43158
                omega
              have d43169 : (x 14 12).toNat = 0 := by
                have r43170 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
                have e43171 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
                have e43172 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
                have b43173 := hb (x 11 3)
                have b43174 := hb (x 12 2)
                have b43175 := hb (x 13 13)
                have b43176 := hb (x 14 12)
                clear * - r43170 e43171 e43172 b43173 b43174 b43175 b43176 d43165
                omega
              have d43177 : (x 14 1 && x 14 12).toNat = 0 := by
                have r43178 := hand2 (x 14 1) (x 14 12)
                have b43179 := hb (x 14 12)
                have b43180 := hb (x 14 1 && x 14 12)
                clear * - r43178 b43179 b43180 d43169
                omega
              have d43181 : (x 14 2 && x 14 12).toNat = 0 := by
                have r43182 := hand2 (x 14 2) (x 14 12)
                have b43183 := hb (x 14 12)
                have b43184 := hb (x 14 2 && x 14 12)
                clear * - r43182 b43183 b43184 d43169
                omega
              have d43185 : (x 13 13).toNat = 0 := by
                have r43186 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
                have e43187 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
                have e43188 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
                have b43189 := hb (x 11 3)
                have b43190 := hb (x 12 2)
                have b43191 := hb (x 13 13)
                have b43192 := hb (x 14 12)
                clear * - r43186 e43187 e43188 b43189 b43190 b43191 b43192 d43169 d43165
                omega
              have d43193 : (x 13 2 && x 13 13).toNat = 0 := by
                have r43194 := hand2 (x 13 2) (x 13 13)
                have b43195 := hb (x 13 13)
                have b43196 := hb (x 13 2 && x 13 13)
                clear * - r43194 b43195 b43196 d43185
                omega
              have d43197 : (x 13 3 && x 13 13).toNat = 0 := by
                have r43198 := hand2 (x 13 3) (x 13 13)
                have b43199 := hb (x 13 13)
                have b43200 := hb (x 13 3 && x 13 13)
                clear * - r43198 b43199 b43200 d43185
                omega
              have d43201 : (x 12 1 && x 12 14).toNat = 1 := by
                have r43202 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := hcov13 13
                have b43203 := hb (x 11 2)
                have b43204 := hb (x 13 13)
                have b43205 := hb (x 12 1 && x 12 14)
                clear * - r43202 b43203 b43204 b43205 d43185 d43013
                omega
              have d43206 : (x 12 1).toNat = 1 := by
                have r43207 := hand1 (x 12 1) (x 12 14)
                have b43208 := hb (x 12 1)
                have b43209 := hb (x 12 1 && x 12 14)
                clear * - r43207 b43208 b43209 d43201
                omega
              have d43210 : (x 13 14).toNat = 0 := by
                have r43211 : (x 13 14).toNat + (x 12 1).toNat = 1 := hd14 13
                have b43212 := hb (x 12 1)
                have b43213 := hb (x 13 14)
                clear * - r43211 b43212 b43213 d43206
                omega
              have d43214 : (x 13 1 && x 13 14).toNat = 0 := by
                have r43215 := hand2 (x 13 1) (x 13 14)
                have b43216 := hb (x 13 14)
                have b43217 := hb (x 13 1 && x 13 14)
                clear * - r43215 b43216 b43217 d43210
                omega
              have d43218 : (x 13 2).toNat = 0 := by
                have r43219 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
                have b43220 := hb (x 13 2)
                have b43221 := hb (x 13 14)
                clear * - r43219 b43220 b43221 d43210
                omega
              have d43222 : (x 12 2).toNat = 0 := by
                have r43223 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
                have e43224 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
                have e43225 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
                have b43226 := hb (x 11 3)
                have b43227 := hb (x 12 2)
                have b43228 := hb (x 13 13)
                have b43229 := hb (x 14 12)
                clear * - r43223 e43224 e43225 b43226 b43227 b43228 b43229 d43169 d43185 d43165
                omega
              have d43230 : (x 14 13).toNat = 1 := by
                have r43231 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
                have b43232 := hb (x 12 2)
                have b43233 := hb (x 14 13)
                have b43234 := hb (x 13 1 && x 13 14)
                clear * - r43231 b43232 b43233 b43234 d43214 d43222
                omega
              have d43235 : (x 15 12).toNat = 0 := by
                have r43236 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
                have e43237 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
                have e43238 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
                have b43239 := hb (x 12 3)
                have b43240 := hb (x 13 2)
                have b43241 := hb (x 14 13)
                have b43242 := hb (x 15 12)
                clear * - r43236 e43237 e43238 b43239 b43240 b43241 b43242 d43230 d43218
                omega
              have d43243 : (x 12 3).toNat = 0 := by
                have r43244 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
                have e43245 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
                have e43246 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
                have b43247 := hb (x 12 3)
                have b43248 := hb (x 13 2)
                have b43249 := hb (x 14 13)
                have b43250 := hb (x 15 12)
                clear * - r43244 e43245 e43246 b43247 b43248 b43249 b43250 d43235 d43230 d43218
                omega
              have d43251 : (x 12 3 && x 12 14).toNat = 0 := by
                have r43252 := hand1 (x 12 3) (x 12 14)
                have b43253 := hb (x 12 3)
                have b43254 := hb (x 12 3 && x 12 14)
                clear * - r43252 b43253 b43254 d43243
                omega
              have d43255 : (x 15 11).toNat = 1 := by
                have r43256 : 1 ≤ (x 15 11).toNat + (x 14 1 && x 14 12).toNat + (x 13 2 && x 13 13).toNat + (x 12 3 && x 12 14).toNat + (x 11 4).toNat := hcov11 15
                have b43257 := hb (x 11 4)
                have b43258 := hb (x 15 11)
                have b43259 := hb (x 14 1 && x 14 12)
                have b43260 := hb (x 13 2 && x 13 13)
                have b43261 := hb (x 12 3 && x 12 14)
                clear * - r43256 b43257 b43258 b43259 b43260 b43261 d43177 d43193 d43251 d43142
                omega
              have d43262 : (x 15 3).toNat = 1 := by
                have r43263 : (x 15 11).toNat ≤ (x 15 3).toNat := himp _ _ (hp11 15)
                have b43264 := hb (x 15 3)
                have b43265 := hb (x 15 11)
                clear * - r43263 b43264 b43265 d43255
                omega
              have d43266 : (x 18 12).toNat = 0 := by
                have r43267 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
                have e43268 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
                have e43269 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
                have b43270 := hb (x 15 3)
                have b43271 := hb (x 16 2)
                have b43272 := hb (x 17 13)
                have b43273 := hb (x 18 12)
                clear * - r43267 e43268 e43269 b43270 b43271 b43272 b43273 d43262
                omega
              have d43274 : (x 17 13).toNat = 0 := by
                have r43275 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
                have e43276 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
                have e43277 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
                have b43278 := hb (x 15 3)
                have b43279 := hb (x 16 2)
                have b43280 := hb (x 17 13)
                have b43281 := hb (x 18 12)
                clear * - r43275 e43276 e43277 b43278 b43279 b43280 b43281 d43266 d43262
                omega
              have d43282 : (x 16 1 && x 16 14).toNat = 1 := by
                have r43283 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := hcov13 17
                have b43284 := hb (x 15 2)
                have b43285 := hb (x 17 13)
                have b43286 := hb (x 16 1 && x 16 14)
                clear * - r43283 b43284 b43285 b43286 d43274 d43126
                omega
              have d43287 : (x 16 14).toNat = 1 := by
                have r43288 := hand2 (x 16 1) (x 16 14)
                have b43289 := hb (x 16 14)
                have b43290 := hb (x 16 1 && x 16 14)
                clear * - r43288 b43289 b43290 d43282
                omega
              have d43291 : (x 15 1).toNat = 0 := by
                have r43292 : (x 16 14).toNat + (x 15 1).toNat = 1 := hd14 16
                have b43293 := hb (x 15 1)
                have b43294 := hb (x 16 14)
                clear * - r43292 b43293 b43294 d43287
                omega
              have d43295 : (x 15 1 && x 15 11).toNat = 0 := by
                have r43296 := hand1 (x 15 1) (x 15 11)
                have b43297 := hb (x 15 1)
                have b43298 := hb (x 15 1 && x 15 11)
                clear * - r43296 b43297 b43298 d43291
                omega
              have d43299 : (x 16 2).toNat = 0 := by
                have r43300 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
                have e43301 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
                have e43302 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
                have b43303 := hb (x 15 3)
                have b43304 := hb (x 16 2)
                have b43305 := hb (x 17 13)
                have b43306 := hb (x 18 12)
                clear * - r43300 e43301 e43302 b43303 b43304 b43305 b43306 d43266 d43274 d43262
                omega
              have d43307 : (x 16 10).toNat = 0 := by
                have r43308 : (x 16 10).toNat ≤ (x 16 2).toNat := himp _ _ (hp10 16)
                have b43309 := hb (x 16 2)
                have b43310 := hb (x 16 10)
                clear * - r43308 b43309 b43310 d43299
                omega
              have r43311 : 1 ≤ (x 16 10).toNat + (x 15 1 && x 15 11).toNat + (x 14 2 && x 14 12).toNat + (x 13 3 && x 13 13).toNat + (x 12 4 && x 12 14).toNat + (x 11 5).toNat := hcov10 16
              have b43312 := hb (x 11 5)
              have b43313 := hb (x 16 10)
              have b43314 := hb (x 15 1 && x 15 11)
              have b43315 := hb (x 14 2 && x 14 12)
              have b43316 := hb (x 13 3 && x 13 13)
              have b43317 := hb (x 12 4 && x 12 14)
              linarith only [r43311, b43312, b43313, b43314, b43315, b43316, b43317, d43307, d43295, d43181, d43197, d43079, d43091]
            · have f43318 : (x (-1) 4).toNat = 1 := by rw [h42751]; rfl
              have d43319 : (x (-1) 12).toNat = 1 := by
                have r43320 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
                have b43321 := hb (x (-1) 4)
                have b43322 := hb (x (-1) 12)
                clear * - r43320 b43321 b43322 f43318
                omega
              have d43323 : (x (-3) 2).toNat = 0 := by
                have r43324 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
                have e43325 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                have e43326 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                have b43327 := hb (x (-4) 3)
                have b43328 := hb (x (-3) 2)
                have b43329 := hb (x (-2) 13)
                have b43330 := hb (x (-1) 12)
                clear * - r43324 e43325 e43326 b43327 b43328 b43329 b43330 d43319 d42577
                omega
              have d43331 : (x (-3) 10).toNat = 0 := by
                have r43332 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
                have b43333 := hb (x (-3) 2)
                have b43334 := hb (x (-3) 10)
                clear * - r43332 b43333 b43334 d43323
                omega
              have d43335 : (x (-3) 3 && x (-3) 10).toNat = 0 := by
                have r43336 := hand2 (x (-3) 3) (x (-3) 10)
                have b43337 := hb (x (-3) 10)
                have b43338 := hb (x (-3) 3 && x (-3) 10)
                clear * - r43336 b43337 b43338 d43331
                omega
              have d43339 : (x (-3) 6 && x (-3) 10).toNat = 0 := by
                have r43340 := hand2 (x (-3) 6) (x (-3) 10)
                have b43341 := hb (x (-3) 10)
                have b43342 := hb (x (-3) 6 && x (-3) 10)
                clear * - r43340 b43341 b43342 d43331
                omega
              have d43343 : (x (-4) 3).toNat = 0 := by
                have r43344 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
                have e43345 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                have e43346 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                have b43347 := hb (x (-4) 3)
                have b43348 := hb (x (-3) 2)
                have b43349 := hb (x (-2) 13)
                have b43350 := hb (x (-1) 12)
                clear * - r43344 e43345 e43346 b43347 b43348 b43349 b43350 d43319 d42577 d43323
                omega
              have d43351 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
                have r43352 := hand1 (x (-4) 3) (x (-4) 12)
                have b43353 := hb (x (-4) 3)
                have b43354 := hb (x (-4) 3 && x (-4) 12)
                clear * - r43352 b43353 b43354 d43343
                omega
              have d43355 : (x (-4) 11).toNat = 0 := by
                have r43356 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
                have b43357 := hb (x (-4) 3)
                have b43358 := hb (x (-4) 11)
                clear * - r43356 b43357 b43358 d43343
                omega
              have d43359 : (x (-4) 7 && x (-4) 11).toNat = 0 := by
                have r43360 := hand2 (x (-4) 7) (x (-4) 11)
                have b43361 := hb (x (-4) 11)
                have b43362 := hb (x (-4) 7 && x (-4) 11)
                clear * - r43360 b43361 b43362 d43355
                omega
              have d43363 : (x 3 8).toNat = 0 := by
                have r43364 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := hd8 3
                have e43365 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
                have e43366 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
                have e43367 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
                have e43368 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
                have e43369 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
                have e43370 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
                have b43371 := hb (x (-4) 7)
                have b43372 := hb (x (-3) 6)
                have b43373 := hb (x (-2) 5)
                have b43374 := hb (x (-1) 4)
                have b43375 := hb (x 0 11)
                have b43376 := hb (x 1 10)
                have b43377 := hb (x 2 9)
                have b43378 := hb (x 3 8)
                clear * - r43364 e43365 e43366 e43367 e43368 e43369 e43370 b43371 b43372 b43373 b43374 b43375 b43376 b43377 b43378 g16 g13 f43318 d42589
                omega
              have d43379 : (x 2 9).toNat = 0 := by
                have r43380 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := hd8 3
                have e43381 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
                have e43382 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
                have e43383 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
                have e43384 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
                have e43385 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
                have e43386 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
                have b43387 := hb (x (-4) 7)
                have b43388 := hb (x (-3) 6)
                have b43389 := hb (x (-2) 5)
                have b43390 := hb (x (-1) 4)
                have b43391 := hb (x 0 11)
                have b43392 := hb (x 1 10)
                have b43393 := hb (x 2 9)
                have b43394 := hb (x 3 8)
                clear * - r43380 e43381 e43382 e43383 e43384 e43385 e43386 b43387 b43388 b43389 b43390 b43391 b43392 b43393 b43394 d43363 g16 g13 f43318 d42589
                omega
              have d43395 : (x 2 5 && x 2 9).toNat = 0 := by
                have r43396 := hand2 (x 2 5) (x 2 9)
                have b43397 := hb (x 2 9)
                have b43398 := hb (x 2 5 && x 2 9)
                clear * - r43396 b43397 b43398 d43379
                omega
              have d43399 : (x (-3) 6).toNat = 0 := by
                have r43400 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := hd8 3
                have e43401 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
                have e43402 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
                have e43403 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
                have e43404 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
                have e43405 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
                have e43406 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
                have b43407 := hb (x (-4) 7)
                have b43408 := hb (x (-3) 6)
                have b43409 := hb (x (-2) 5)
                have b43410 := hb (x (-1) 4)
                have b43411 := hb (x 0 11)
                have b43412 := hb (x 1 10)
                have b43413 := hb (x 2 9)
                have b43414 := hb (x 3 8)
                clear * - r43400 e43401 e43402 e43403 e43404 e43405 e43406 b43407 b43408 b43409 b43410 b43411 b43412 b43413 b43414 d43363 d43379 g16 g13 f43318 d42589
                omega
              have d43415 : (x (-4) 7).toNat = 0 := by
                have r43416 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := hd8 3
                have e43417 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
                have e43418 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
                have e43419 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
                have e43420 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
                have e43421 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
                have e43422 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
                have b43423 := hb (x (-4) 7)
                have b43424 := hb (x (-3) 6)
                have b43425 := hb (x (-2) 5)
                have b43426 := hb (x (-1) 4)
                have b43427 := hb (x 0 11)
                have b43428 := hb (x 1 10)
                have b43429 := hb (x 2 9)
                have b43430 := hb (x 3 8)
                clear * - r43416 e43417 e43418 e43419 e43420 e43421 e43422 b43423 b43424 b43425 b43426 b43427 b43428 b43429 b43430 d43363 d43379 g16 g13 f43318 d42589 d43399
                omega
              have d43431 : (x (-4) 7 && x (-4) 12).toNat = 0 := by
                have r43432 := hand1 (x (-4) 7) (x (-4) 12)
                have b43433 := hb (x (-4) 7)
                have b43434 := hb (x (-4) 7 && x (-4) 12)
                clear * - r43432 b43433 b43434 d43415
                omega
              have r43435 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := hcount 3
              have r43436 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := hcount 8
              have r43437 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := hd8 (-8)
              have e43438 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
              have e43439 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
              have e43440 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
              have e43441 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
              have e43442 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
              have e43443 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
              have r43444 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
              have e43445 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e43446 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e43447 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e43448 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e43449 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e43450 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have r43451 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
              have e43452 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
              have e43453 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
              have e43454 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
              have e43455 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
              have e43456 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
              have e43457 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
              have r43458 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := hd8 11
              have e43459 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
              have e43460 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
              have e43461 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
              have e43462 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
              have e43463 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
              have e43464 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
              have r43465 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := hd12 (-5)
              have e43466 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
              have e43467 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
              have r43468 : 1 ≤ (x 3 4).toNat + (x 2 1 && x 2 5).toNat + (x 1 2 && x 1 6).toNat + (x 0 3 && x 0 7).toNat + (x (-1) 4 && x (-1) 8).toNat + (x (-2) 5 && x (-2) 9).toNat + (x (-3) 6 && x (-3) 10).toNat + (x (-4) 7 && x (-4) 11).toNat + (x (-5) 8 && x (-5) 12).toNat + (x (-6) 9 && x (-6) 13).toNat + (x (-7) 10 && x (-7) 14).toNat + (x (-8) 11).toNat := hcov4 3
              have e43469 : (x 2 1 && x 2 5).toNat = (x 2 5).toNat := handr _ _ (fun h => hp13 2 (hp5 2 (h)))
              have e43470 : (x (-7) 10 && x (-7) 14).toNat = (x (-7) 10).toNat := handl _ _ (fun h => hp2 (-7) (hp10 (-7) (h)))
              have r43471 : 1 ≤ (x 7 4).toNat + (x 6 1 && x 6 5).toNat + (x 5 2 && x 5 6).toNat + (x 4 3 && x 4 7).toNat + (x 3 4 && x 3 8).toNat + (x 2 5 && x 2 9).toNat + (x 1 6 && x 1 10).toNat + (x 0 7 && x 0 11).toNat + (x (-1) 8 && x (-1) 12).toNat + (x (-2) 9 && x (-2) 13).toNat + (x (-3) 10 && x (-3) 14).toNat + (x (-4) 11).toNat := hcov4 7
              have e43472 : (x 6 1 && x 6 5).toNat = (x 6 5).toNat := handr _ _ (fun h => hp13 6 (hp5 6 (h)))
              have e43473 : (x (-3) 10 && x (-3) 14).toNat = (x (-3) 10).toNat := handl _ _ (fun h => hp2 (-3) (hp10 (-3) (h)))
              have r43474 : 1 ≤ (x 3 5).toNat + (x 2 1 && x 2 6).toNat + (x 1 2 && x 1 7).toNat + (x 0 3 && x 0 8).toNat + (x (-1) 4 && x (-1) 9).toNat + (x (-2) 5 && x (-2) 10).toNat + (x (-3) 6 && x (-3) 11).toNat + (x (-4) 7 && x (-4) 12).toNat + (x (-5) 8 && x (-5) 13).toNat + (x (-6) 9 && x (-6) 14).toNat + (x (-7) 10).toNat := hcov5 3
              have r43475 : 1 ≤ (x 0 7).toNat + (x (-1) 1 && x (-1) 8).toNat + (x (-2) 2 && x (-2) 9).toNat + (x (-3) 3 && x (-3) 10).toNat + (x (-4) 4 && x (-4) 11).toNat + (x (-5) 5 && x (-5) 12).toNat + (x (-6) 6 && x (-6) 13).toNat + (x (-7) 7 && x (-7) 14).toNat + (x (-8) 8).toNat := hcov7 0
              have r43476 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := hcov9 (-1)
              have r43477 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := hcov9 6
              have r43478 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := hcov11 (-8)
              have r43479 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := hcov11 8
              have r43480 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := hcov13 (-5)
              have r43481 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
              have r43482 := hand2 (x (-1) 4) (x (-1) 8)
              have r43483 := hand1 (x (-5) 8) (x (-5) 12)
              have r43484 := hand1 (x (-6) 9) (x (-6) 13)
              have r43485 := hand2 (x 5 2) (x 5 6)
              have r43486 := hand2 (x 4 3) (x 4 7)
              have r43487 := hand1 (x (-1) 8) (x (-1) 12)
              have r43488 := hand2 (x 2 1) (x 2 6)
              have r43489 := hand1 (x (-5) 8) (x (-5) 13)
              have r43490 := hand1 (x (-6) 9) (x (-6) 14)
              have r43491 := hand2 (x (-1) 1) (x (-1) 8)
              have r43492 := hand1 (x (-5) 4) (x (-5) 13)
              have r43493 := hand1 (x (-6) 5) (x (-6) 14)
              have r43494 := hand2 (x 5 1) (x 5 10)
              have r43495 := hand2 (x 4 2) (x 4 11)
              have r43496 := hand2 (x (-9) 1) (x (-9) 12)
              have r43497 := hand2 (x (-10) 2) (x (-10) 13)
              have r43498 := hand2 (x (-11) 3) (x (-11) 14)
              have r43499 := hand1 (x 7 1) (x 7 12)
              have r43500 := hand1 (x 6 2) (x 6 13)
              have r43501 := hand1 (x 5 3) (x 5 14)
              have r43502 := hand2 (x (-6) 1) (x (-6) 14)
              have b43503 := hb (x (-15) 7)
              have b43504 := hb (x (-14) 6)
              have b43505 := hb (x (-13) 5)
              have b43506 := hb (x (-12) 4)
              have b43507 := hb (x (-11) 11)
              have b43508 := hb (x (-11) 14)
              have b43509 := hb (x (-10) 10)
              have b43510 := hb (x (-10) 13)
              have b43511 := hb (x (-9) 9)
              have b43512 := hb (x (-9) 12)
              have b43513 := hb (x (-8) 3)
              have b43514 := hb (x (-8) 7)
              have b43515 := hb (x (-8) 8)
              have b43516 := hb (x (-8) 11)
              have b43517 := hb (x (-7) 2)
              have b43518 := hb (x (-7) 6)
              have b43519 := hb (x (-7) 10)
              have b43520 := hb (x (-6) 5)
              have b43521 := hb (x (-6) 9)
              have b43522 := hb (x (-6) 13)
              have b43523 := hb (x (-6) 14)
              have b43524 := hb (x (-5) 4)
              have b43525 := hb (x (-5) 8)
              have b43526 := hb (x (-5) 12)
              have b43527 := hb (x (-5) 13)
              have b43528 := hb (x (-4) 7)
              have b43529 := hb (x (-4) 11)
              have b43530 := hb (x (-4) 12)
              have b43531 := hb (x (-3) 6)
              have b43532 := hb (x (-3) 10)
              have b43533 := hb (x (-3) 11)
              have b43534 := hb (x (-2) 5)
              have b43535 := hb (x (-2) 9)
              have b43536 := hb (x (-2) 10)
              have b43537 := hb (x (-1) 4)
              have b43538 := hb (x (-1) 8)
              have b43539 := hb (x (-1) 9)
              have b43540 := hb (x 0 3)
              have b43541 := hb (x 0 6)
              have b43542 := hb (x 0 7)
              have b43543 := hb (x 0 8)
              have b43544 := hb (x 1 2)
              have b43545 := hb (x 1 6)
              have b43546 := hb (x 1 7)
              have b43547 := hb (x 2 1)
              have b43548 := hb (x 2 5)
              have b43549 := hb (x 2 6)
              have b43550 := hb (x 3 4)
              have b43551 := hb (x 3 5)
              have b43552 := hb (x 4 4)
              have b43553 := hb (x 4 7)
              have b43554 := hb (x 4 11)
              have b43555 := hb (x 5 3)
              have b43556 := hb (x 5 6)
              have b43557 := hb (x 5 10)
              have b43558 := hb (x 6 2)
              have b43559 := hb (x 6 5)
              have b43560 := hb (x 6 9)
              have b43561 := hb (x 7 1)
              have b43562 := hb (x 7 4)
              have b43563 := hb (x 7 8)
              have b43564 := hb (x 8 11)
              have b43565 := hb (x 9 10)
              have b43566 := hb (x 10 9)
              have b43567 := hb (x 11 8)
              have b43568 := hb (x 1 2 && x 1 6)
              have b43569 := hb (x 0 3 && x 0 7)
              have b43570 := hb (x (-1) 4 && x (-1) 8)
              have b43571 := hb (x (-2) 5 && x (-2) 9)
              have b43572 := hb (x (-3) 6 && x (-3) 10)
              have b43573 := hb (x (-4) 7 && x (-4) 11)
              have b43574 := hb (x (-5) 8 && x (-5) 12)
              have b43575 := hb (x (-6) 9 && x (-6) 13)
              have b43576 := hb (x 5 2 && x 5 6)
              have b43577 := hb (x 4 3 && x 4 7)
              have b43578 := hb (x 3 4 && x 3 8)
              have b43579 := hb (x 2 5 && x 2 9)
              have b43580 := hb (x 1 6 && x 1 10)
              have b43581 := hb (x 0 7 && x 0 11)
              have b43582 := hb (x (-1) 8 && x (-1) 12)
              have b43583 := hb (x (-2) 9 && x (-2) 13)
              have b43584 := hb (x 2 1 && x 2 6)
              have b43585 := hb (x 1 2 && x 1 7)
              have b43586 := hb (x 0 3 && x 0 8)
              have b43587 := hb (x (-1) 4 && x (-1) 9)
              have b43588 := hb (x (-2) 5 && x (-2) 10)
              have b43589 := hb (x (-3) 6 && x (-3) 11)
              have b43590 := hb (x (-4) 7 && x (-4) 12)
              have b43591 := hb (x (-5) 8 && x (-5) 13)
              have b43592 := hb (x (-6) 9 && x (-6) 14)
              have b43593 := hb (x (-1) 1 && x (-1) 8)
              have b43594 := hb (x (-2) 2 && x (-2) 9)
              have b43595 := hb (x (-3) 3 && x (-3) 10)
              have b43596 := hb (x (-4) 4 && x (-4) 11)
              have b43597 := hb (x (-5) 5 && x (-5) 12)
              have b43598 := hb (x (-6) 6 && x (-6) 13)
              have b43599 := hb (x (-7) 7 && x (-7) 14)
              have b43600 := hb (x (-2) 1 && x (-2) 10)
              have b43601 := hb (x (-3) 2 && x (-3) 11)
              have b43602 := hb (x (-4) 3 && x (-4) 12)
              have b43603 := hb (x (-5) 4 && x (-5) 13)
              have b43604 := hb (x (-6) 5 && x (-6) 14)
              have b43605 := hb (x 5 1 && x 5 10)
              have b43606 := hb (x 4 2 && x 4 11)
              have b43607 := hb (x 3 3 && x 3 12)
              have b43608 := hb (x 2 4 && x 2 13)
              have b43609 := hb (x 1 5 && x 1 14)
              have b43610 := hb (x (-9) 1 && x (-9) 12)
              have b43611 := hb (x (-10) 2 && x (-10) 13)
              have b43612 := hb (x (-11) 3 && x (-11) 14)
              have b43613 := hb (x 7 1 && x 7 12)
              have b43614 := hb (x 6 2 && x 6 13)
              have b43615 := hb (x 5 3 && x 5 14)
              have b43616 := hb (x (-6) 1 && x (-6) 14)
              linarith only [r43435, r43436, r43437, e43438, e43439, e43440, e43441, e43442, e43443, r43444, e43445, e43446, e43447, e43448, e43449, e43450, r43451, e43452, e43453, e43454, e43455, e43456, e43457, r43458, e43459, e43460, e43461, e43462, e43463, e43464, r43465, e43466, e43467, r43468, e43469, e43470, r43471, e43472, e43473, r43474, r43475, r43476, r43477, r43478, r43479, r43480, r43481, r43482, r43483, r43484, r43485, r43486, r43487, r43488, r43489, r43490, r43491, r43492, r43493, r43494, r43495, r43496, r43497, r43498, r43499, r43500, r43501, r43502, b43503, b43504, b43505, b43506, b43507, b43508, b43509, b43510, b43511, b43512, b43513, b43514, b43515, b43516, b43517, b43518, b43519, b43520, b43521, b43522, b43523, b43524, b43525, b43526, b43527, b43528, b43529, b43530, b43531, b43532, b43533, b43534, b43535, b43536, b43537, b43538, b43539, b43540, b43541, b43542, b43543, b43544, b43545, b43546, b43547, b43548, b43549, b43550, b43551, b43552, b43553, b43554, b43555, b43556, b43557, b43558, b43559, b43560, b43561, b43562, b43563, b43564, b43565, b43566, b43567, b43568, b43569, b43570, b43571, b43572, b43573, b43574, b43575, b43576, b43577, b43578, b43579, b43580, b43581, b43582, b43583, b43584, b43585, b43586, b43587, b43588, b43589, b43590, b43591, b43592, b43593, b43594, b43595, b43596, b43597, b43598, b43599, b43600, b43601, b43602, b43603, b43604, b43605, b43606, b43607, b43608, b43609, b43610, b43611, b43612, b43613, b43614, b43615, b43616, d43415, d43355, d43399, d43331, g2, d42589, d42597, g3, f43318, g4, g7, g9, g10, g11, g14, g15, g17, g19, g20, g21, d42593, d43339, d43359, g22, d43395, g23, g24, d42585, g25, g26, g27, g28, g29, d43431, d42601, d43335, g31, g32, g33, g34, g35, g36, d43351, g37, d42745, g38]
          · have f43617 : (x 1 3).toNat = 1 := by rw [h42749]; rfl
            have d43618 : (x 4 12).toNat = 0 := by
              have r43619 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
              have e43620 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e43621 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b43622 := hb (x 1 3)
              have b43623 := hb (x 2 2)
              have b43624 := hb (x 3 13)
              have b43625 := hb (x 4 12)
              clear * - r43619 e43620 e43621 b43622 b43623 b43624 b43625 f43617
              omega
            have d43626 : (x 4 1 && x 4 12).toNat = 0 := by
              have r43627 := hand2 (x 4 1) (x 4 12)
              have b43628 := hb (x 4 12)
              have b43629 := hb (x 4 1 && x 4 12)
              clear * - r43627 b43628 b43629 d43618
              omega
            have d43630 : (x 4 4).toNat = 0 := by
              have r43631 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
              have b43632 := hb (x 4 4)
              have b43633 := hb (x 4 12)
              clear * - r43631 b43632 b43633 d43618
              omega
            have d43634 : (x 3 13).toNat = 0 := by
              have r43635 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
              have e43636 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e43637 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b43638 := hb (x 1 3)
              have b43639 := hb (x 2 2)
              have b43640 := hb (x 3 13)
              have b43641 := hb (x 4 12)
              clear * - r43635 e43636 e43637 b43638 b43639 b43640 b43641 d43618 f43617
              omega
            have d43642 : (x 2 2).toNat = 0 := by
              have r43643 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
              have e43644 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e43645 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b43646 := hb (x 1 3)
              have b43647 := hb (x 2 2)
              have b43648 := hb (x 3 13)
              have b43649 := hb (x 4 12)
              clear * - r43643 e43644 e43645 b43646 b43647 b43648 b43649 d43618 d43634 f43617
              omega
            have d43650 : (x 4 13).toNat = 1 := by
              have r43651 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
              have b43652 := hb (x 2 2)
              have b43653 := hb (x 4 13)
              have b43654 := hb (x 3 1 && x 3 14)
              clear * - r43651 b43652 b43653 b43654 g48 d43642
              omega
            have d43655 : (x 4 1).toNat = 1 := by
              have r43656 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
              have b43657 := hb (x 4 1)
              have b43658 := hb (x 4 13)
              clear * - r43656 b43657 b43658 d43650
              omega
            have d43659 : (x 5 14).toNat = 0 := by
              have r43660 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
              have b43661 := hb (x 4 1)
              have b43662 := hb (x 5 14)
              clear * - r43660 b43661 b43662 d43655
              omega
            have d43663 : (x 5 3 && x 5 14).toNat = 0 := by
              have r43664 := hand2 (x 5 3) (x 5 14)
              have b43665 := hb (x 5 14)
              have b43666 := hb (x 5 3 && x 5 14)
              clear * - r43664 b43665 b43666 d43659
              omega
            have d43667 : (x 5 2).toNat = 0 := by
              have r43668 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
              have b43669 := hb (x 5 2)
              have b43670 := hb (x 5 14)
              clear * - r43668 b43669 b43670 d43659
              omega
            have d43671 : (x 5 12).toNat = 0 := by
              have r43672 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
              have e43673 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
              have e43674 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
              have b43675 := hb (x 2 3)
              have b43676 := hb (x 3 2)
              have b43677 := hb (x 4 13)
              have b43678 := hb (x 5 12)
              clear * - r43672 e43673 e43674 b43675 b43676 b43677 b43678 d43650 g18
              omega
            have d43679 : (x 5 4).toNat = 0 := by
              have r43680 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
              have b43681 := hb (x 5 4)
              have b43682 := hb (x 5 12)
              clear * - r43680 b43681 b43682 d43671
              omega
            have d43683 : (x 2 3).toNat = 0 := by
              have r43684 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
              have e43685 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
              have e43686 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
              have b43687 := hb (x 2 3)
              have b43688 := hb (x 3 2)
              have b43689 := hb (x 4 13)
              have b43690 := hb (x 5 12)
              clear * - r43684 e43685 e43686 b43687 b43688 b43689 b43690 d43671 d43650 g18
              omega
            have d43691 : (x 2 3 && x 2 14).toNat = 0 := by
              have r43692 := hand1 (x 2 3) (x 2 14)
              have b43693 := hb (x 2 3)
              have b43694 := hb (x 2 3 && x 2 14)
              clear * - r43692 b43693 b43694 d43683
              omega
            have d43695 : (x 5 11).toNat = 1 := by
              have r43696 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := hcov11 5
              have b43697 := hb (x 1 4)
              have b43698 := hb (x 5 11)
              have b43699 := hb (x 4 1 && x 4 12)
              have b43700 := hb (x 3 2 && x 3 13)
              have b43701 := hb (x 2 3 && x 2 14)
              clear * - r43696 b43697 b43698 b43699 b43700 b43701 d43626 g45 d43691 d42617
              omega
            have d43702 : (x 5 3).toNat = 1 := by
              have r43703 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
              have b43704 := hb (x 5 3)
              have b43705 := hb (x 5 11)
              clear * - r43703 b43704 b43705 d43695
              omega
            have d43706 : (x 8 12).toNat = 0 := by
              have r43707 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
              have e43708 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
              have e43709 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
              have b43710 := hb (x 5 3)
              have b43711 := hb (x 6 2)
              have b43712 := hb (x 7 13)
              have b43713 := hb (x 8 12)
              clear * - r43707 e43708 e43709 b43710 b43711 b43712 b43713 d43702
              omega
            have d43714 : (x 8 1 && x 8 12).toNat = 0 := by
              have r43715 := hand2 (x 8 1) (x 8 12)
              have b43716 := hb (x 8 12)
              have b43717 := hb (x 8 1 && x 8 12)
              clear * - r43715 b43716 b43717 d43706
              omega
            have d43718 : (x 8 4).toNat = 0 := by
              have r43719 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
              have b43720 := hb (x 8 4)
              have b43721 := hb (x 8 12)
              clear * - r43719 b43720 b43721 d43706
              omega
            have d43722 : (x 7 13).toNat = 0 := by
              have r43723 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
              have e43724 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
              have e43725 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
              have b43726 := hb (x 5 3)
              have b43727 := hb (x 6 2)
              have b43728 := hb (x 7 13)
              have b43729 := hb (x 8 12)
              clear * - r43723 e43724 e43725 b43726 b43727 b43728 b43729 d43706 d43702
              omega
            have d43730 : (x 7 2 && x 7 13).toNat = 0 := by
              have r43731 := hand2 (x 7 2) (x 7 13)
              have b43732 := hb (x 7 13)
              have b43733 := hb (x 7 2 && x 7 13)
              clear * - r43731 b43732 b43733 d43722
              omega
            have d43734 : (x 6 1 && x 6 14).toNat = 1 := by
              have r43735 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
              have b43736 := hb (x 5 2)
              have b43737 := hb (x 7 13)
              have b43738 := hb (x 6 1 && x 6 14)
              clear * - r43735 b43736 b43737 b43738 d43722 d43667
              omega
            have d43739 : (x 6 1).toNat = 1 := by
              have r43740 := hand1 (x 6 1) (x 6 14)
              have b43741 := hb (x 6 1)
              have b43742 := hb (x 6 1 && x 6 14)
              clear * - r43740 b43741 b43742 d43734
              omega
            have d43743 : (x 7 14).toNat = 0 := by
              have r43744 : (x 7 14).toNat + (x 6 1).toNat = 1 := hd14 7
              have b43745 := hb (x 6 1)
              have b43746 := hb (x 7 14)
              clear * - r43744 b43745 b43746 d43739
              omega
            have d43747 : (x 7 1 && x 7 14).toNat = 0 := by
              have r43748 := hand2 (x 7 1) (x 7 14)
              have b43749 := hb (x 7 14)
              have b43750 := hb (x 7 1 && x 7 14)
              clear * - r43748 b43749 b43750 d43743
              omega
            have d43751 : (x 7 2).toNat = 0 := by
              have r43752 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
              have b43753 := hb (x 7 2)
              have b43754 := hb (x 7 14)
              clear * - r43752 b43753 b43754 d43743
              omega
            have d43755 : (x 6 2).toNat = 0 := by
              have r43756 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
              have e43757 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
              have e43758 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
              have b43759 := hb (x 5 3)
              have b43760 := hb (x 6 2)
              have b43761 := hb (x 7 13)
              have b43762 := hb (x 8 12)
              clear * - r43756 e43757 e43758 b43759 b43760 b43761 b43762 d43706 d43722 d43702
              omega
            have d43763 : (x 6 2 && x 6 13).toNat = 0 := by
              have r43764 := hand1 (x 6 2) (x 6 13)
              have b43765 := hb (x 6 2)
              have b43766 := hb (x 6 2 && x 6 13)
              clear * - r43764 b43765 b43766 d43755
              omega
            have d43767 : (x 8 13).toNat = 1 := by
              have r43768 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := hcov13 8
              have b43769 := hb (x 6 2)
              have b43770 := hb (x 8 13)
              have b43771 := hb (x 7 1 && x 7 14)
              clear * - r43768 b43769 b43770 b43771 d43747 d43755
              omega
            have d43772 : (x 8 1).toNat = 1 := by
              have r43773 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
              have b43774 := hb (x 8 1)
              have b43775 := hb (x 8 13)
              clear * - r43773 b43774 b43775 d43767
              omega
            have d43776 : (x 9 14).toNat = 0 := by
              have r43777 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
              have b43778 := hb (x 8 1)
              have b43779 := hb (x 9 14)
              clear * - r43777 b43778 b43779 d43772
              omega
            have d43780 : (x 9 3 && x 9 14).toNat = 0 := by
              have r43781 := hand2 (x 9 3) (x 9 14)
              have b43782 := hb (x 9 14)
              have b43783 := hb (x 9 3 && x 9 14)
              clear * - r43781 b43782 b43783 d43776
              omega
            have d43784 : (x 9 2).toNat = 0 := by
              have r43785 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
              have b43786 := hb (x 9 2)
              have b43787 := hb (x 9 14)
              clear * - r43785 b43786 b43787 d43776
              omega
            have d43788 : (x 9 12).toNat = 0 := by
              have r43789 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
              have e43790 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
              have e43791 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
              have b43792 := hb (x 6 3)
              have b43793 := hb (x 7 2)
              have b43794 := hb (x 8 13)
              have b43795 := hb (x 9 12)
              clear * - r43789 e43790 e43791 b43792 b43793 b43794 b43795 d43767 d43751
              omega
            have d43796 : (x 9 4).toNat = 0 := by
              have r43797 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
              have b43798 := hb (x 9 4)
              have b43799 := hb (x 9 12)
              clear * - r43797 b43798 b43799 d43788
              omega
            have d43800 : (x 6 3).toNat = 0 := by
              have r43801 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
              have e43802 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
              have e43803 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
              have b43804 := hb (x 6 3)
              have b43805 := hb (x 7 2)
              have b43806 := hb (x 8 13)
              have b43807 := hb (x 9 12)
              clear * - r43801 e43802 e43803 b43804 b43805 b43806 b43807 d43788 d43767 d43751
              omega
            have d43808 : (x 6 3 && x 6 14).toNat = 0 := by
              have r43809 := hand1 (x 6 3) (x 6 14)
              have b43810 := hb (x 6 3)
              have b43811 := hb (x 6 3 && x 6 14)
              clear * - r43809 b43810 b43811 d43800
              omega
            have d43812 : (x 9 11).toNat = 1 := by
              have r43813 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := hcov11 9
              have b43814 := hb (x 5 4)
              have b43815 := hb (x 9 11)
              have b43816 := hb (x 8 1 && x 8 12)
              have b43817 := hb (x 7 2 && x 7 13)
              have b43818 := hb (x 6 3 && x 6 14)
              clear * - r43813 b43814 b43815 b43816 b43817 b43818 d43714 d43730 d43808 d43679
              omega
            have d43819 : (x 9 3).toNat = 1 := by
              have r43820 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
              have b43821 := hb (x 9 3)
              have b43822 := hb (x 9 11)
              clear * - r43820 b43821 b43822 d43812
              omega
            have d43823 : (x 12 12).toNat = 0 := by
              have r43824 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
              have e43825 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
              have e43826 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
              have b43827 := hb (x 9 3)
              have b43828 := hb (x 10 2)
              have b43829 := hb (x 11 13)
              have b43830 := hb (x 12 12)
              clear * - r43824 e43825 e43826 b43827 b43828 b43829 b43830 d43819
              omega
            have d43831 : (x 12 1 && x 12 12).toNat = 0 := by
              have r43832 := hand2 (x 12 1) (x 12 12)
              have b43833 := hb (x 12 12)
              have b43834 := hb (x 12 1 && x 12 12)
              clear * - r43832 b43833 b43834 d43823
              omega
            have d43835 : (x 12 4).toNat = 0 := by
              have r43836 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
              have b43837 := hb (x 12 4)
              have b43838 := hb (x 12 12)
              clear * - r43836 b43837 b43838 d43823
              omega
            have d43839 : (x 11 13).toNat = 0 := by
              have r43840 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
              have e43841 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
              have e43842 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
              have b43843 := hb (x 9 3)
              have b43844 := hb (x 10 2)
              have b43845 := hb (x 11 13)
              have b43846 := hb (x 12 12)
              clear * - r43840 e43841 e43842 b43843 b43844 b43845 b43846 d43823 d43819
              omega
            have d43847 : (x 11 2 && x 11 13).toNat = 0 := by
              have r43848 := hand2 (x 11 2) (x 11 13)
              have b43849 := hb (x 11 13)
              have b43850 := hb (x 11 2 && x 11 13)
              clear * - r43848 b43849 b43850 d43839
              omega
            have d43851 : (x 10 1 && x 10 14).toNat = 1 := by
              have r43852 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := hcov13 11
              have b43853 := hb (x 9 2)
              have b43854 := hb (x 11 13)
              have b43855 := hb (x 10 1 && x 10 14)
              clear * - r43852 b43853 b43854 b43855 d43839 d43784
              omega
            have d43856 : (x 10 14).toNat = 1 := by
              have r43857 := hand2 (x 10 1) (x 10 14)
              have b43858 := hb (x 10 14)
              have b43859 := hb (x 10 1 && x 10 14)
              clear * - r43857 b43858 b43859 d43851
              omega
            have d43860 : (x 9 1).toNat = 0 := by
              have r43861 : (x 10 14).toNat + (x 9 1).toNat = 1 := hd14 10
              have b43862 := hb (x 9 1)
              have b43863 := hb (x 10 14)
              clear * - r43861 b43862 b43863 d43856
              omega
            have d43864 : (x 9 13).toNat = 0 := by
              have r43865 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
              have b43866 := hb (x 9 1)
              have b43867 := hb (x 9 13)
              clear * - r43865 b43866 b43867 d43860
              omega
            have d43868 : (x 8 1 && x 8 14).toNat = 1 := by
              have r43869 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := hcov13 9
              have b43870 := hb (x 7 2)
              have b43871 := hb (x 9 13)
              have b43872 := hb (x 8 1 && x 8 14)
              clear * - r43869 b43870 b43871 b43872 d43864 d43751
              omega
            have d43873 : (x 8 14).toNat = 1 := by
              have r43874 := hand2 (x 8 1) (x 8 14)
              have b43875 := hb (x 8 14)
              have b43876 := hb (x 8 1 && x 8 14)
              clear * - r43874 b43875 b43876 d43868
              omega
            have d43877 : (x 7 1).toNat = 0 := by
              have r43878 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
              have b43879 := hb (x 7 1)
              have b43880 := hb (x 8 14)
              clear * - r43878 b43879 b43880 d43873
              omega
            have d43881 : (x 7 1 && x 7 12).toNat = 0 := by
              have r43882 := hand1 (x 7 1) (x 7 12)
              have b43883 := hb (x 7 1)
              have b43884 := hb (x 7 1 && x 7 12)
              clear * - r43882 b43883 b43884 d43877
              omega
            have d43885 : (x 8 11).toNat = 1 := by
              have r43886 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := hcov11 8
              have b43887 := hb (x 4 4)
              have b43888 := hb (x 8 11)
              have b43889 := hb (x 7 1 && x 7 12)
              have b43890 := hb (x 6 2 && x 6 13)
              have b43891 := hb (x 5 3 && x 5 14)
              clear * - r43886 b43887 b43888 b43889 b43890 b43891 d43881 d43763 d43663 d43630
              omega
            have d43892 : (x 8 3).toNat = 1 := by
              have r43893 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
              have b43894 := hb (x 8 3)
              have b43895 := hb (x 8 11)
              clear * - r43893 b43894 b43895 d43885
              omega
            have d43896 : (x 11 12).toNat = 0 := by
              have r43897 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
              have e43898 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
              have e43899 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
              have b43900 := hb (x 8 3)
              have b43901 := hb (x 9 2)
              have b43902 := hb (x 10 13)
              have b43903 := hb (x 11 12)
              clear * - r43897 e43898 e43899 b43900 b43901 b43902 b43903 d43784 d43892
              omega
            have d43904 : (x 11 1 && x 11 12).toNat = 0 := by
              have r43905 := hand2 (x 11 1) (x 11 12)
              have b43906 := hb (x 11 12)
              have b43907 := hb (x 11 1 && x 11 12)
              clear * - r43905 b43906 b43907 d43896
              omega
            have d43908 : (x 10 13).toNat = 0 := by
              have r43909 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
              have e43910 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
              have e43911 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
              have b43912 := hb (x 8 3)
              have b43913 := hb (x 9 2)
              have b43914 := hb (x 10 13)
              have b43915 := hb (x 11 12)
              clear * - r43909 e43910 e43911 b43912 b43913 b43914 b43915 d43896 d43784 d43892
              omega
            have d43916 : (x 10 2 && x 10 13).toNat = 0 := by
              have r43917 := hand2 (x 10 2) (x 10 13)
              have b43918 := hb (x 10 13)
              have b43919 := hb (x 10 2 && x 10 13)
              clear * - r43917 b43918 b43919 d43908
              omega
            have d43920 : (x 12 11).toNat = 1 := by
              have r43921 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := hcov11 12
              have b43922 := hb (x 8 4)
              have b43923 := hb (x 12 11)
              have b43924 := hb (x 11 1 && x 11 12)
              have b43925 := hb (x 10 2 && x 10 13)
              have b43926 := hb (x 9 3 && x 9 14)
              clear * - r43921 b43922 b43923 b43924 b43925 b43926 d43904 d43916 d43780 d43718
              omega
            have d43927 : (x 12 3).toNat = 1 := by
              have r43928 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
              have b43929 := hb (x 12 3)
              have b43930 := hb (x 12 11)
              clear * - r43928 b43929 b43930 d43920
              omega
            have d43931 : (x 15 12).toNat = 0 := by
              have r43932 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
              have e43933 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
              have e43934 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
              have b43935 := hb (x 12 3)
              have b43936 := hb (x 13 2)
              have b43937 := hb (x 14 13)
              have b43938 := hb (x 15 12)
              clear * - r43932 e43933 e43934 b43935 b43936 b43937 b43938 d43927
              omega
            have d43939 : (x 15 1 && x 15 12).toNat = 0 := by
              have r43940 := hand2 (x 15 1) (x 15 12)
              have b43941 := hb (x 15 12)
              have b43942 := hb (x 15 1 && x 15 12)
              clear * - r43940 b43941 b43942 d43931
              omega
            have d43943 : (x 14 13).toNat = 0 := by
              have r43944 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
              have e43945 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
              have e43946 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
              have b43947 := hb (x 12 3)
              have b43948 := hb (x 13 2)
              have b43949 := hb (x 14 13)
              have b43950 := hb (x 15 12)
              clear * - r43944 e43945 e43946 b43947 b43948 b43949 b43950 d43931 d43927
              omega
            have d43951 : (x 14 2 && x 14 13).toNat = 0 := by
              have r43952 := hand2 (x 14 2) (x 14 13)
              have b43953 := hb (x 14 13)
              have b43954 := hb (x 14 2 && x 14 13)
              clear * - r43952 b43953 b43954 d43943
              omega
            have d43955 : (x 13 2).toNat = 0 := by
              have r43956 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
              have e43957 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
              have e43958 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
              have b43959 := hb (x 12 3)
              have b43960 := hb (x 13 2)
              have b43961 := hb (x 14 13)
              have b43962 := hb (x 15 12)
              clear * - r43956 e43957 e43958 b43959 b43960 b43961 b43962 d43931 d43943 d43927
              omega
            have d43963 : (x 10 1).toNat = 1 := by
              have r43964 := hand1 (x 10 1) (x 10 14)
              have b43965 := hb (x 10 1)
              have b43966 := hb (x 10 1 && x 10 14)
              clear * - r43964 b43965 b43966 d43851
              omega
            have d43967 : (x 11 14).toNat = 0 := by
              have r43968 : (x 11 14).toNat + (x 10 1).toNat = 1 := hd14 11
              have b43969 := hb (x 10 1)
              have b43970 := hb (x 11 14)
              clear * - r43968 b43969 b43970 d43963
              omega
            have d43971 : (x 11 1 && x 11 14).toNat = 0 := by
              have r43972 := hand2 (x 11 1) (x 11 14)
              have b43973 := hb (x 11 14)
              have b43974 := hb (x 11 1 && x 11 14)
              clear * - r43972 b43973 b43974 d43967
              omega
            have d43975 : (x 11 2).toNat = 0 := by
              have r43976 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
              have b43977 := hb (x 11 2)
              have b43978 := hb (x 11 14)
              clear * - r43976 b43977 b43978 d43967
              omega
            have d43979 : (x 10 2).toNat = 0 := by
              have r43980 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
              have e43981 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
              have e43982 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
              have b43983 := hb (x 9 3)
              have b43984 := hb (x 10 2)
              have b43985 := hb (x 11 13)
              have b43986 := hb (x 12 12)
              clear * - r43980 e43981 e43982 b43983 b43984 b43985 b43986 d43823 d43839 d43819
              omega
            have d43987 : (x 12 13).toNat = 1 := by
              have r43988 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := hcov13 12
              have b43989 := hb (x 10 2)
              have b43990 := hb (x 12 13)
              have b43991 := hb (x 11 1 && x 11 14)
              clear * - r43988 b43989 b43990 b43991 d43971 d43979
              omega
            have d43992 : (x 12 1).toNat = 1 := by
              have r43993 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
              have b43994 := hb (x 12 1)
              have b43995 := hb (x 12 13)
              clear * - r43993 b43994 b43995 d43987
              omega
            have d43996 : (x 13 14).toNat = 0 := by
              have r43997 : (x 13 14).toNat + (x 12 1).toNat = 1 := hd14 13
              have b43998 := hb (x 12 1)
              have b43999 := hb (x 13 14)
              clear * - r43997 b43998 b43999 d43992
              omega
            have d44000 : (x 13 1 && x 13 14).toNat = 0 := by
              have r44001 := hand2 (x 13 1) (x 13 14)
              have b44002 := hb (x 13 14)
              have b44003 := hb (x 13 1 && x 13 14)
              clear * - r44001 b44002 b44003 d43996
              omega
            have d44004 : (x 12 2).toNat = 1 := by
              have r44005 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
              have b44006 := hb (x 12 2)
              have b44007 := hb (x 14 13)
              have b44008 := hb (x 13 1 && x 13 14)
              clear * - r44005 b44006 b44007 b44008 d43943 d44000
              omega
            have d44009 : (x 14 12).toNat = 0 := by
              have r44010 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
              have e44011 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
              have e44012 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
              have b44013 := hb (x 11 3)
              have b44014 := hb (x 12 2)
              have b44015 := hb (x 13 13)
              have b44016 := hb (x 14 12)
              clear * - r44010 e44011 e44012 b44013 b44014 b44015 b44016 d44004
              omega
            have d44017 : (x 14 4).toNat = 0 := by
              have r44018 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
              have b44019 := hb (x 14 4)
              have b44020 := hb (x 14 12)
              clear * - r44018 b44019 b44020 d44009
              omega
            have d44021 : (x 14 4 && x 14 14).toNat = 0 := by
              have r44022 := hand1 (x 14 4) (x 14 14)
              have b44023 := hb (x 14 4)
              have b44024 := hb (x 14 4 && x 14 14)
              clear * - r44022 b44023 b44024 d44017
              omega
            have d44025 : (x 13 13).toNat = 0 := by
              have r44026 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
              have e44027 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
              have e44028 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
              have b44029 := hb (x 11 3)
              have b44030 := hb (x 12 2)
              have b44031 := hb (x 13 13)
              have b44032 := hb (x 14 12)
              clear * - r44026 e44027 e44028 b44029 b44030 b44031 b44032 d44009 d44004
              omega
            have d44033 : (x 13 5).toNat = 0 := by
              have r44034 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
              have b44035 := hb (x 13 5)
              have b44036 := hb (x 13 13)
              clear * - r44034 b44035 b44036 d44025
              omega
            have d44037 : (x 13 3 && x 13 14).toNat = 0 := by
              have r44038 := hand2 (x 13 3) (x 13 14)
              have b44039 := hb (x 13 14)
              have b44040 := hb (x 13 3 && x 13 14)
              clear * - r44038 b44039 b44040 d43996
              omega
            have d44041 : (x 16 11).toNat = 1 := by
              have r44042 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := hcov11 16
              have b44043 := hb (x 12 4)
              have b44044 := hb (x 16 11)
              have b44045 := hb (x 15 1 && x 15 12)
              have b44046 := hb (x 14 2 && x 14 13)
              have b44047 := hb (x 13 3 && x 13 14)
              clear * - r44042 b44043 b44044 b44045 b44046 b44047 d43939 d43951 d44037 d43835
              omega
            have d44048 : (x 16 3).toNat = 1 := by
              have r44049 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
              have b44050 := hb (x 16 3)
              have b44051 := hb (x 16 11)
              clear * - r44049 b44050 b44051 d44041
              omega
            have d44052 : (x 19 12).toNat = 0 := by
              have r44053 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
              have e44054 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
              have e44055 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
              have b44056 := hb (x 16 3)
              have b44057 := hb (x 17 2)
              have b44058 := hb (x 18 13)
              have b44059 := hb (x 19 12)
              clear * - r44053 e44054 e44055 b44056 b44057 b44058 b44059 d44048
              omega
            have d44060 : (x 18 13).toNat = 0 := by
              have r44061 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
              have e44062 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
              have e44063 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
              have b44064 := hb (x 16 3)
              have b44065 := hb (x 17 2)
              have b44066 := hb (x 18 13)
              have b44067 := hb (x 19 12)
              clear * - r44061 e44062 e44063 b44064 b44065 b44066 b44067 d44052 d44048
              omega
            have d44068 : (x 17 2).toNat = 0 := by
              have r44069 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
              have e44070 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
              have e44071 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
              have b44072 := hb (x 16 3)
              have b44073 := hb (x 17 2)
              have b44074 := hb (x 18 13)
              have b44075 := hb (x 19 12)
              clear * - r44069 e44070 e44071 b44072 b44073 b44074 b44075 d44052 d44060 d44048
              omega
            have d44076 : (x 13 12).toNat = 0 := by
              have r44077 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
              have e44078 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
              have e44079 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
              have b44080 := hb (x 10 3)
              have b44081 := hb (x 11 2)
              have b44082 := hb (x 12 13)
              have b44083 := hb (x 13 12)
              clear * - r44077 e44078 e44079 b44080 b44081 b44082 b44083 d43987 d43975
              omega
            have d44084 : (x 13 4).toNat = 0 := by
              have r44085 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
              have b44086 := hb (x 13 4)
              have b44087 := hb (x 13 12)
              clear * - r44085 b44086 b44087 d44076
              omega
            have d44088 : (x 10 3).toNat = 0 := by
              have r44089 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
              have e44090 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
              have e44091 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
              have b44092 := hb (x 10 3)
              have b44093 := hb (x 11 2)
              have b44094 := hb (x 12 13)
              have b44095 := hb (x 13 12)
              clear * - r44089 e44090 e44091 b44092 b44093 b44094 b44095 d44076 d43987 d43975
              omega
            have d44096 : (x 10 3 && x 10 14).toNat = 0 := by
              have r44097 := hand1 (x 10 3) (x 10 14)
              have b44098 := hb (x 10 3)
              have b44099 := hb (x 10 3 && x 10 14)
              clear * - r44097 b44098 b44099 d44088
              omega
            have d44100 : (x 13 11).toNat = 1 := by
              have r44101 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := hcov11 13
              have b44102 := hb (x 9 4)
              have b44103 := hb (x 13 11)
              have b44104 := hb (x 12 1 && x 12 12)
              have b44105 := hb (x 11 2 && x 11 13)
              have b44106 := hb (x 10 3 && x 10 14)
              clear * - r44101 b44102 b44103 b44104 b44105 b44106 d43831 d43847 d44096 d43796
              omega
            have d44107 : (x 13 3).toNat = 1 := by
              have r44108 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
              have b44109 := hb (x 13 3)
              have b44110 := hb (x 13 11)
              clear * - r44108 b44109 b44110 d44100
              omega
            have d44111 : (x 16 12).toNat = 0 := by
              have r44112 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
              have e44113 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
              have e44114 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
              have b44115 := hb (x 13 3)
              have b44116 := hb (x 14 2)
              have b44117 := hb (x 15 13)
              have b44118 := hb (x 16 12)
              clear * - r44112 e44113 e44114 b44115 b44116 b44117 b44118 d44107
              omega
            have d44119 : (x 16 1 && x 16 12).toNat = 0 := by
              have r44120 := hand2 (x 16 1) (x 16 12)
              have b44121 := hb (x 16 12)
              have b44122 := hb (x 16 1 && x 16 12)
              clear * - r44120 b44121 b44122 d44111
              omega
            have d44123 : (x 16 2 && x 16 12).toNat = 0 := by
              have r44124 := hand2 (x 16 2) (x 16 12)
              have b44125 := hb (x 16 12)
              have b44126 := hb (x 16 2 && x 16 12)
              clear * - r44124 b44125 b44126 d44111
              omega
            have d44127 : (x 15 13).toNat = 0 := by
              have r44128 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
              have e44129 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
              have e44130 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
              have b44131 := hb (x 13 3)
              have b44132 := hb (x 14 2)
              have b44133 := hb (x 15 13)
              have b44134 := hb (x 16 12)
              clear * - r44128 e44129 e44130 b44131 b44132 b44133 b44134 d44111 d44107
              omega
            have d44135 : (x 15 2 && x 15 13).toNat = 0 := by
              have r44136 := hand2 (x 15 2) (x 15 13)
              have b44137 := hb (x 15 13)
              have b44138 := hb (x 15 2 && x 15 13)
              clear * - r44136 b44137 b44138 d44127
              omega
            have d44139 : (x 15 3 && x 15 13).toNat = 0 := by
              have r44140 := hand2 (x 15 3) (x 15 13)
              have b44141 := hb (x 15 13)
              have b44142 := hb (x 15 3 && x 15 13)
              clear * - r44140 b44141 b44142 d44127
              omega
            have d44143 : (x 14 1 && x 14 14).toNat = 1 := by
              have r44144 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := hcov13 15
              have b44145 := hb (x 13 2)
              have b44146 := hb (x 15 13)
              have b44147 := hb (x 14 1 && x 14 14)
              clear * - r44144 b44145 b44146 b44147 d44127 d43955
              omega
            have d44148 : (x 14 1).toNat = 1 := by
              have r44149 := hand1 (x 14 1) (x 14 14)
              have b44150 := hb (x 14 1)
              have b44151 := hb (x 14 1 && x 14 14)
              clear * - r44149 b44150 b44151 d44143
              omega
            have d44152 : (x 15 14).toNat = 0 := by
              have r44153 : (x 15 14).toNat + (x 14 1).toNat = 1 := hd14 15
              have b44154 := hb (x 14 1)
              have b44155 := hb (x 15 14)
              clear * - r44153 b44154 b44155 d44148
              omega
            have d44156 : (x 15 1 && x 15 14).toNat = 0 := by
              have r44157 := hand2 (x 15 1) (x 15 14)
              have b44158 := hb (x 15 14)
              have b44159 := hb (x 15 1 && x 15 14)
              clear * - r44157 b44158 b44159 d44152
              omega
            have d44160 : (x 15 2).toNat = 0 := by
              have r44161 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
              have b44162 := hb (x 15 2)
              have b44163 := hb (x 15 14)
              clear * - r44161 b44162 b44163 d44152
              omega
            have d44164 : (x 14 2).toNat = 0 := by
              have r44165 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
              have e44166 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
              have e44167 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
              have b44168 := hb (x 13 3)
              have b44169 := hb (x 14 2)
              have b44170 := hb (x 15 13)
              have b44171 := hb (x 16 12)
              clear * - r44165 e44166 e44167 b44168 b44169 b44170 b44171 d44111 d44127 d44107
              omega
            have d44172 : (x 16 13).toNat = 1 := by
              have r44173 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := hcov13 16
              have b44174 := hb (x 14 2)
              have b44175 := hb (x 16 13)
              have b44176 := hb (x 15 1 && x 15 14)
              clear * - r44173 b44174 b44175 b44176 d44156 d44164
              omega
            have d44177 : (x 17 12).toNat = 0 := by
              have r44178 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
              have e44179 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
              have e44180 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
              have b44181 := hb (x 14 3)
              have b44182 := hb (x 15 2)
              have b44183 := hb (x 16 13)
              have b44184 := hb (x 17 12)
              clear * - r44178 e44179 e44180 b44181 b44182 b44183 b44184 d44172 d44160
              omega
            have d44185 : (x 14 3).toNat = 0 := by
              have r44186 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
              have e44187 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
              have e44188 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
              have b44189 := hb (x 14 3)
              have b44190 := hb (x 15 2)
              have b44191 := hb (x 16 13)
              have b44192 := hb (x 17 12)
              clear * - r44186 e44187 e44188 b44189 b44190 b44191 b44192 d44177 d44172 d44160
              omega
            have d44193 : (x 14 3 && x 14 14).toNat = 0 := by
              have r44194 := hand1 (x 14 3) (x 14 14)
              have b44195 := hb (x 14 3)
              have b44196 := hb (x 14 3 && x 14 14)
              clear * - r44194 b44195 b44196 d44185
              omega
            have d44197 : (x 17 11).toNat = 1 := by
              have r44198 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := hcov11 17
              have b44199 := hb (x 13 4)
              have b44200 := hb (x 17 11)
              have b44201 := hb (x 16 1 && x 16 12)
              have b44202 := hb (x 15 2 && x 15 13)
              have b44203 := hb (x 14 3 && x 14 14)
              clear * - r44198 b44199 b44200 b44201 b44202 b44203 d44119 d44135 d44193 d44084
              omega
            have d44204 : (x 17 3).toNat = 1 := by
              have r44205 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
              have b44206 := hb (x 17 3)
              have b44207 := hb (x 17 11)
              clear * - r44205 b44206 b44207 d44197
              omega
            have d44208 : (x 20 12).toNat = 0 := by
              have r44209 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
              have e44210 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
              have e44211 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
              have b44212 := hb (x 17 3)
              have b44213 := hb (x 18 2)
              have b44214 := hb (x 19 13)
              have b44215 := hb (x 20 12)
              clear * - r44209 e44210 e44211 b44212 b44213 b44214 b44215 d44204
              omega
            have d44216 : (x 19 13).toNat = 0 := by
              have r44217 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
              have e44218 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
              have e44219 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
              have b44220 := hb (x 17 3)
              have b44221 := hb (x 18 2)
              have b44222 := hb (x 19 13)
              have b44223 := hb (x 20 12)
              clear * - r44217 e44218 e44219 b44220 b44221 b44222 b44223 d44208 d44204
              omega
            have d44224 : (x 18 1 && x 18 14).toNat = 1 := by
              have r44225 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := hcov13 19
              have b44226 := hb (x 17 2)
              have b44227 := hb (x 19 13)
              have b44228 := hb (x 18 1 && x 18 14)
              clear * - r44225 b44226 b44227 b44228 d44216 d44068
              omega
            have d44229 : (x 18 14).toNat = 1 := by
              have r44230 := hand2 (x 18 1) (x 18 14)
              have b44231 := hb (x 18 14)
              have b44232 := hb (x 18 1 && x 18 14)
              clear * - r44230 b44231 b44232 d44224
              omega
            have d44233 : (x 17 1).toNat = 0 := by
              have r44234 : (x 18 14).toNat + (x 17 1).toNat = 1 := hd14 18
              have b44235 := hb (x 17 1)
              have b44236 := hb (x 18 14)
              clear * - r44234 b44235 b44236 d44229
              omega
            have d44237 : (x 17 1 && x 17 11).toNat = 0 := by
              have r44238 := hand1 (x 17 1) (x 17 11)
              have b44239 := hb (x 17 1)
              have b44240 := hb (x 17 1 && x 17 11)
              clear * - r44238 b44239 b44240 d44233
              omega
            have d44241 : (x 18 2).toNat = 0 := by
              have r44242 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
              have e44243 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
              have e44244 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
              have b44245 := hb (x 17 3)
              have b44246 := hb (x 18 2)
              have b44247 := hb (x 19 13)
              have b44248 := hb (x 20 12)
              clear * - r44242 e44243 e44244 b44245 b44246 b44247 b44248 d44208 d44216 d44204
              omega
            have d44249 : (x 18 10).toNat = 0 := by
              have r44250 : (x 18 10).toNat ≤ (x 18 2).toNat := himp _ _ (hp10 18)
              have b44251 := hb (x 18 2)
              have b44252 := hb (x 18 10)
              clear * - r44250 b44251 b44252 d44241
              omega
            have r44253 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := hcov10 18
            have b44254 := hb (x 13 5)
            have b44255 := hb (x 18 10)
            have b44256 := hb (x 17 1 && x 17 11)
            have b44257 := hb (x 16 2 && x 16 12)
            have b44258 := hb (x 15 3 && x 15 13)
            have b44259 := hb (x 14 4 && x 14 14)
            linarith only [r44253, b44254, b44255, b44256, b44257, b44258, b44259, d44249, d44237, d44123, d44139, d44021, d44033]
      · have f44260 : (x 1 1).toNat = 1 := by rw [h42554]; rfl
        have d44261 : (x 2 14).toNat = 0 := by
          have r44262 : (x 2 14).toNat + (x 1 1).toNat = 1 := hd14 2
          have b44263 := hb (x 1 1)
          have b44264 := hb (x 2 14)
          clear * - r44262 b44263 b44264 f44260
          omega
        have d44265 : (x 2 1 && x 2 14).toNat = 0 := by
          have r44266 := hand2 (x 2 1) (x 2 14)
          have b44267 := hb (x 2 14)
          have b44268 := hb (x 2 1 && x 2 14)
          clear * - r44266 b44267 b44268 d44261
          omega
        have d44269 : (x 2 2).toNat = 0 := by
          have r44270 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
          have b44271 := hb (x 2 2)
          have b44272 := hb (x 2 14)
          clear * - r44270 b44271 b44272 d44261
          omega
        have d44273 : (x 4 13).toNat = 1 := by
          have r44274 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
          have b44275 := hb (x 2 2)
          have b44276 := hb (x 4 13)
          have b44277 := hb (x 3 1 && x 3 14)
          clear * - r44274 b44275 b44276 b44277 g48 d44269
          omega
        have d44278 : (x 4 1).toNat = 1 := by
          have r44279 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
          have b44280 := hb (x 4 1)
          have b44281 := hb (x 4 13)
          clear * - r44279 b44280 b44281 d44273
          omega
        have d44282 : (x 5 14).toNat = 0 := by
          have r44283 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
          have b44284 := hb (x 4 1)
          have b44285 := hb (x 5 14)
          clear * - r44283 b44284 b44285 d44278
          omega
        have d44286 : (x 5 1 && x 5 14).toNat = 0 := by
          have r44287 := hand2 (x 5 1) (x 5 14)
          have b44288 := hb (x 5 14)
          have b44289 := hb (x 5 1 && x 5 14)
          clear * - r44287 b44288 b44289 d44282
          omega
        have d44290 : (x 5 2).toNat = 0 := by
          have r44291 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
          have b44292 := hb (x 5 2)
          have b44293 := hb (x 5 14)
          clear * - r44291 b44292 b44293 d44282
          omega
        have d44294 : (x 3 13).toNat = 1 := by
          have r44295 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := hcov13 3
          have b44296 := hb (x 1 2)
          have b44297 := hb (x 3 13)
          have b44298 := hb (x 2 1 && x 2 14)
          clear * - r44295 b44296 b44297 b44298 d44265 g14
          omega
        have d44299 : (x 3 1).toNat = 1 := by
          have r44300 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
          have b44301 := hb (x 3 1)
          have b44302 := hb (x 3 13)
          clear * - r44300 b44301 b44302 d44294
          omega
        have d44303 : (x 4 14).toNat = 0 := by
          have r44304 : (x 4 14).toNat + (x 3 1).toNat = 1 := hd14 4
          have b44305 := hb (x 3 1)
          have b44306 := hb (x 4 14)
          clear * - r44304 b44305 b44306 d44299
          omega
        have d44307 : (x 4 1 && x 4 14).toNat = 0 := by
          have r44308 := hand2 (x 4 1) (x 4 14)
          have b44309 := hb (x 4 14)
          have b44310 := hb (x 4 1 && x 4 14)
          clear * - r44308 b44309 b44310 d44303
          omega
        have d44311 : (x 5 13).toNat = 1 := by
          have r44312 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := hcov13 5
          have b44313 := hb (x 3 2)
          have b44314 := hb (x 5 13)
          have b44315 := hb (x 4 1 && x 4 14)
          clear * - r44312 b44313 b44314 b44315 d44307 g18
          omega
        have d44316 : (x 5 1).toNat = 1 := by
          have r44317 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
          have b44318 := hb (x 5 1)
          have b44319 := hb (x 5 13)
          clear * - r44317 b44318 b44319 d44311
          omega
        have d44320 : (x 6 14).toNat = 0 := by
          have r44321 : (x 6 14).toNat + (x 5 1).toNat = 1 := hd14 6
          have b44322 := hb (x 5 1)
          have b44323 := hb (x 6 14)
          clear * - r44321 b44322 b44323 d44316
          omega
        have d44324 : (x 6 1 && x 6 14).toNat = 0 := by
          have r44325 := hand2 (x 6 1) (x 6 14)
          have b44326 := hb (x 6 14)
          have b44327 := hb (x 6 1 && x 6 14)
          clear * - r44325 b44326 b44327 d44320
          omega
        have d44328 : (x 7 13).toNat = 1 := by
          have r44329 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
          have b44330 := hb (x 5 2)
          have b44331 := hb (x 7 13)
          have b44332 := hb (x 6 1 && x 6 14)
          clear * - r44329 b44330 b44331 b44332 d44324 d44290
          omega
        have d44333 : (x 7 1).toNat = 1 := by
          have r44334 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
          have b44335 := hb (x 7 1)
          have b44336 := hb (x 7 13)
          clear * - r44334 b44335 b44336 d44328
          omega
        have d44337 : (x 8 14).toNat = 0 := by
          have r44338 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
          have b44339 := hb (x 7 1)
          have b44340 := hb (x 8 14)
          clear * - r44338 b44339 b44340 d44333
          omega
        have d44341 : (x 8 1 && x 8 14).toNat = 0 := by
          have r44342 := hand2 (x 8 1) (x 8 14)
          have b44343 := hb (x 8 14)
          have b44344 := hb (x 8 1 && x 8 14)
          clear * - r44342 b44343 b44344 d44337
          omega
        have d44345 : (x 8 2).toNat = 0 := by
          have r44346 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
          have b44347 := hb (x 8 2)
          have b44348 := hb (x 8 14)
          clear * - r44346 b44347 b44348 d44337
          omega
        have d44349 : (x 6 2).toNat = 0 := by
          have r44350 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
          have b44351 := hb (x 6 2)
          have b44352 := hb (x 6 14)
          clear * - r44350 b44351 b44352 d44320
          omega
        have d44353 : (x 4 2).toNat = 0 := by
          have r44354 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
          have b44355 := hb (x 4 2)
          have b44356 := hb (x 4 14)
          clear * - r44354 b44355 b44356 d44303
          omega
        have d44357 : (x 6 13).toNat = 1 := by
          have r44358 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := hcov13 6
          have b44359 := hb (x 4 2)
          have b44360 := hb (x 6 13)
          have b44361 := hb (x 5 1 && x 5 14)
          clear * - r44358 b44359 b44360 b44361 d44286 d44353
          omega
        have d44362 : (x 6 1).toNat = 1 := by
          have r44363 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
          have b44364 := hb (x 6 1)
          have b44365 := hb (x 6 13)
          clear * - r44363 b44364 b44365 d44357
          omega
        have d44366 : (x 7 14).toNat = 0 := by
          have r44367 : (x 7 14).toNat + (x 6 1).toNat = 1 := hd14 7
          have b44368 := hb (x 6 1)
          have b44369 := hb (x 7 14)
          clear * - r44367 b44368 b44369 d44362
          omega
        have d44370 : (x 7 1 && x 7 14).toNat = 0 := by
          have r44371 := hand2 (x 7 1) (x 7 14)
          have b44372 := hb (x 7 14)
          have b44373 := hb (x 7 1 && x 7 14)
          clear * - r44371 b44372 b44373 d44366
          omega
        have d44374 : (x 8 13).toNat = 1 := by
          have r44375 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := hcov13 8
          have b44376 := hb (x 6 2)
          have b44377 := hb (x 8 13)
          have b44378 := hb (x 7 1 && x 7 14)
          clear * - r44375 b44376 b44377 b44378 d44370 d44349
          omega
        have d44379 : (x 8 1).toNat = 1 := by
          have r44380 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
          have b44381 := hb (x 8 1)
          have b44382 := hb (x 8 13)
          clear * - r44380 b44381 b44382 d44374
          omega
        have d44383 : (x 9 14).toNat = 0 := by
          have r44384 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
          have b44385 := hb (x 8 1)
          have b44386 := hb (x 9 14)
          clear * - r44384 b44385 b44386 d44379
          omega
        have d44387 : (x 9 1 && x 9 14).toNat = 0 := by
          have r44388 := hand2 (x 9 1) (x 9 14)
          have b44389 := hb (x 9 14)
          have b44390 := hb (x 9 1 && x 9 14)
          clear * - r44388 b44389 b44390 d44383
          omega
        have d44391 : (x 10 13).toNat = 1 := by
          have r44392 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := hcov13 10
          have b44393 := hb (x 8 2)
          have b44394 := hb (x 10 13)
          have b44395 := hb (x 9 1 && x 9 14)
          clear * - r44392 b44393 b44394 b44395 d44387 d44345
          omega
        have d44396 : (x 10 1).toNat = 1 := by
          have r44397 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
          have b44398 := hb (x 10 1)
          have b44399 := hb (x 10 13)
          clear * - r44397 b44398 b44399 d44391
          omega
        have d44400 : (x 11 14).toNat = 0 := by
          have r44401 : (x 11 14).toNat + (x 10 1).toNat = 1 := hd14 11
          have b44402 := hb (x 10 1)
          have b44403 := hb (x 11 14)
          clear * - r44401 b44402 b44403 d44396
          omega
        have d44404 : (x 11 1 && x 11 14).toNat = 0 := by
          have r44405 := hand2 (x 11 1) (x 11 14)
          have b44406 := hb (x 11 14)
          have b44407 := hb (x 11 1 && x 11 14)
          clear * - r44405 b44406 b44407 d44400
          omega
        have d44408 : (x 11 2).toNat = 0 := by
          have r44409 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
          have b44410 := hb (x 11 2)
          have b44411 := hb (x 11 14)
          clear * - r44409 b44410 b44411 d44400
          omega
        have d44412 : (x 9 2).toNat = 0 := by
          have r44413 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
          have b44414 := hb (x 9 2)
          have b44415 := hb (x 9 14)
          clear * - r44413 b44414 b44415 d44383
          omega
        have d44416 : (x 7 2).toNat = 0 := by
          have r44417 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
          have b44418 := hb (x 7 2)
          have b44419 := hb (x 7 14)
          clear * - r44417 b44418 b44419 d44366
          omega
        have d44420 : (x 9 13).toNat = 1 := by
          have r44421 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := hcov13 9
          have b44422 := hb (x 7 2)
          have b44423 := hb (x 9 13)
          have b44424 := hb (x 8 1 && x 8 14)
          clear * - r44421 b44422 b44423 b44424 d44341 d44416
          omega
        have d44425 : (x 9 1).toNat = 1 := by
          have r44426 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
          have b44427 := hb (x 9 1)
          have b44428 := hb (x 9 13)
          clear * - r44426 b44427 b44428 d44420
          omega
        have d44429 : (x 10 14).toNat = 0 := by
          have r44430 : (x 10 14).toNat + (x 9 1).toNat = 1 := hd14 10
          have b44431 := hb (x 9 1)
          have b44432 := hb (x 10 14)
          clear * - r44430 b44431 b44432 d44425
          omega
        have d44433 : (x 10 1 && x 10 14).toNat = 0 := by
          have r44434 := hand2 (x 10 1) (x 10 14)
          have b44435 := hb (x 10 14)
          have b44436 := hb (x 10 1 && x 10 14)
          clear * - r44434 b44435 b44436 d44429
          omega
        have d44437 : (x 11 13).toNat = 1 := by
          have r44438 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := hcov13 11
          have b44439 := hb (x 9 2)
          have b44440 := hb (x 11 13)
          have b44441 := hb (x 10 1 && x 10 14)
          clear * - r44438 b44439 b44440 b44441 d44433 d44412
          omega
        have d44442 : (x 11 1).toNat = 1 := by
          have r44443 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
          have b44444 := hb (x 11 1)
          have b44445 := hb (x 11 13)
          clear * - r44443 b44444 b44445 d44437
          omega
        have d44446 : (x 12 14).toNat = 0 := by
          have r44447 : (x 12 14).toNat + (x 11 1).toNat = 1 := hd14 12
          have b44448 := hb (x 11 1)
          have b44449 := hb (x 12 14)
          clear * - r44447 b44448 b44449 d44442
          omega
        have d44450 : (x 12 1 && x 12 14).toNat = 0 := by
          have r44451 := hand2 (x 12 1) (x 12 14)
          have b44452 := hb (x 12 14)
          have b44453 := hb (x 12 1 && x 12 14)
          clear * - r44451 b44452 b44453 d44446
          omega
        have d44454 : (x 13 13).toNat = 1 := by
          have r44455 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := hcov13 13
          have b44456 := hb (x 11 2)
          have b44457 := hb (x 13 13)
          have b44458 := hb (x 12 1 && x 12 14)
          clear * - r44455 b44456 b44457 b44458 d44450 d44408
          omega
        have d44459 : (x 13 1).toNat = 1 := by
          have r44460 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
          have b44461 := hb (x 13 1)
          have b44462 := hb (x 13 13)
          clear * - r44460 b44461 b44462 d44454
          omega
        have d44463 : (x 14 14).toNat = 0 := by
          have r44464 : (x 14 14).toNat + (x 13 1).toNat = 1 := hd14 14
          have b44465 := hb (x 13 1)
          have b44466 := hb (x 14 14)
          clear * - r44464 b44465 b44466 d44459
          omega
        have d44467 : (x 14 1 && x 14 14).toNat = 0 := by
          have r44468 := hand2 (x 14 1) (x 14 14)
          have b44469 := hb (x 14 14)
          have b44470 := hb (x 14 1 && x 14 14)
          clear * - r44468 b44469 b44470 d44463
          omega
        have d44471 : (x 14 3 && x 14 14).toNat = 0 := by
          have r44472 := hand2 (x 14 3) (x 14 14)
          have b44473 := hb (x 14 14)
          have b44474 := hb (x 14 3 && x 14 14)
          clear * - r44472 b44473 b44474 d44463
          omega
        have d44475 : (x 14 2).toNat = 0 := by
          have r44476 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
          have b44477 := hb (x 14 2)
          have b44478 := hb (x 14 14)
          clear * - r44476 b44477 b44478 d44463
          omega
        have d44479 : (x 12 2).toNat = 0 := by
          have r44480 : (x 12 2).toNat ≤ (x 12 14).toNat := himp _ _ (hp2 12)
          have b44481 := hb (x 12 2)
          have b44482 := hb (x 12 14)
          clear * - r44480 b44481 b44482 d44446
          omega
        have d44483 : (x 10 2).toNat = 0 := by
          have r44484 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
          have b44485 := hb (x 10 2)
          have b44486 := hb (x 10 14)
          clear * - r44484 b44485 b44486 d44429
          omega
        have d44487 : (x 12 13).toNat = 1 := by
          have r44488 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := hcov13 12
          have b44489 := hb (x 10 2)
          have b44490 := hb (x 12 13)
          have b44491 := hb (x 11 1 && x 11 14)
          clear * - r44488 b44489 b44490 b44491 d44404 d44483
          omega
        have d44492 : (x 12 1).toNat = 1 := by
          have r44493 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
          have b44494 := hb (x 12 1)
          have b44495 := hb (x 12 13)
          clear * - r44493 b44494 b44495 d44487
          omega
        have d44496 : (x 13 14).toNat = 0 := by
          have r44497 : (x 13 14).toNat + (x 12 1).toNat = 1 := hd14 13
          have b44498 := hb (x 12 1)
          have b44499 := hb (x 13 14)
          clear * - r44497 b44498 b44499 d44492
          omega
        have d44500 : (x 13 1 && x 13 14).toNat = 0 := by
          have r44501 := hand2 (x 13 1) (x 13 14)
          have b44502 := hb (x 13 14)
          have b44503 := hb (x 13 1 && x 13 14)
          clear * - r44501 b44502 b44503 d44496
          omega
        have d44504 : (x 14 13).toNat = 1 := by
          have r44505 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
          have b44506 := hb (x 12 2)
          have b44507 := hb (x 14 13)
          have b44508 := hb (x 13 1 && x 13 14)
          clear * - r44505 b44506 b44507 b44508 d44500 d44479
          omega
        have d44509 : (x 14 1).toNat = 1 := by
          have r44510 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
          have b44511 := hb (x 14 1)
          have b44512 := hb (x 14 13)
          clear * - r44510 b44511 b44512 d44504
          omega
        have d44513 : (x 15 14).toNat = 0 := by
          have r44514 : (x 15 14).toNat + (x 14 1).toNat = 1 := hd14 15
          have b44515 := hb (x 14 1)
          have b44516 := hb (x 15 14)
          clear * - r44514 b44515 b44516 d44509
          omega
        have d44517 : (x 15 1 && x 15 14).toNat = 0 := by
          have r44518 := hand2 (x 15 1) (x 15 14)
          have b44519 := hb (x 15 14)
          have b44520 := hb (x 15 1 && x 15 14)
          clear * - r44518 b44519 b44520 d44513
          omega
        have d44521 : (x 16 13).toNat = 1 := by
          have r44522 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := hcov13 16
          have b44523 := hb (x 14 2)
          have b44524 := hb (x 16 13)
          have b44525 := hb (x 15 1 && x 15 14)
          clear * - r44522 b44523 b44524 b44525 d44517 d44475
          omega
        have d44526 : (x 16 1).toNat = 1 := by
          have r44527 : (x 16 13).toNat ≤ (x 16 1).toNat := himp _ _ (hp13 16)
          have b44528 := hb (x 16 1)
          have b44529 := hb (x 16 13)
          clear * - r44527 b44528 b44529 d44521
          omega
        have d44530 : (x 17 14).toNat = 0 := by
          have r44531 : (x 17 14).toNat + (x 16 1).toNat = 1 := hd14 17
          have b44532 := hb (x 16 1)
          have b44533 := hb (x 17 14)
          clear * - r44531 b44532 b44533 d44526
          omega
        have d44534 : (x 17 2).toNat = 0 := by
          have r44535 : (x 17 2).toNat ≤ (x 17 14).toNat := himp _ _ (hp2 17)
          have b44536 := hb (x 17 2)
          have b44537 := hb (x 17 14)
          clear * - r44535 b44536 b44537 d44530
          omega
        have d44538 : (x 15 2).toNat = 0 := by
          have r44539 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
          have b44540 := hb (x 15 2)
          have b44541 := hb (x 15 14)
          clear * - r44539 b44540 b44541 d44513
          omega
        have d44542 : (x 15 2 && x 15 13).toNat = 0 := by
          have r44543 := hand1 (x 15 2) (x 15 13)
          have b44544 := hb (x 15 2)
          have b44545 := hb (x 15 2 && x 15 13)
          clear * - r44543 b44544 b44545 d44538
          omega
        have d44546 : (x 13 2).toNat = 0 := by
          have r44547 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
          have b44548 := hb (x 13 2)
          have b44549 := hb (x 13 14)
          clear * - r44547 b44548 b44549 d44496
          omega
        have d44550 : (x 15 13).toNat = 1 := by
          have r44551 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := hcov13 15
          have b44552 := hb (x 13 2)
          have b44553 := hb (x 15 13)
          have b44554 := hb (x 14 1 && x 14 14)
          clear * - r44551 b44552 b44553 b44554 d44467 d44546
          omega
        have d44555 : (x 15 1).toNat = 1 := by
          have r44556 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
          have b44557 := hb (x 15 1)
          have b44558 := hb (x 15 13)
          clear * - r44556 b44557 b44558 d44550
          omega
        have d44559 : (x 16 14).toNat = 0 := by
          have r44560 : (x 16 14).toNat + (x 15 1).toNat = 1 := hd14 16
          have b44561 := hb (x 15 1)
          have b44562 := hb (x 16 14)
          clear * - r44560 b44561 b44562 d44555
          omega
        have d44563 : (x 16 1 && x 16 14).toNat = 0 := by
          have r44564 := hand2 (x 16 1) (x 16 14)
          have b44565 := hb (x 16 14)
          have b44566 := hb (x 16 1 && x 16 14)
          clear * - r44564 b44565 b44566 d44559
          omega
        have d44567 : (x 17 13).toNat = 1 := by
          have r44568 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := hcov13 17
          have b44569 := hb (x 15 2)
          have b44570 := hb (x 17 13)
          have b44571 := hb (x 16 1 && x 16 14)
          clear * - r44568 b44569 b44570 b44571 d44563 d44538
          omega
        have d44572 : (x 17 1).toNat = 1 := by
          have r44573 : (x 17 13).toNat ≤ (x 17 1).toNat := himp _ _ (hp13 17)
          have b44574 := hb (x 17 1)
          have b44575 := hb (x 17 13)
          clear * - r44573 b44574 b44575 d44567
          omega
        have d44576 : (x 18 14).toNat = 0 := by
          have r44577 : (x 18 14).toNat + (x 17 1).toNat = 1 := hd14 18
          have b44578 := hb (x 17 1)
          have b44579 := hb (x 18 14)
          clear * - r44577 b44578 b44579 d44572
          omega
        have d44580 : (x 18 1 && x 18 14).toNat = 0 := by
          have r44581 := hand2 (x 18 1) (x 18 14)
          have b44582 := hb (x 18 14)
          have b44583 := hb (x 18 1 && x 18 14)
          clear * - r44581 b44582 b44583 d44576
          omega
        have d44584 : (x 19 13).toNat = 1 := by
          have r44585 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := hcov13 19
          have b44586 := hb (x 17 2)
          have b44587 := hb (x 19 13)
          have b44588 := hb (x 18 1 && x 18 14)
          clear * - r44585 b44586 b44587 b44588 d44580 d44534
          omega
        have d44589 : (x 18 2).toNat = 0 := by
          have r44590 : (x 18 2).toNat ≤ (x 18 14).toNat := himp _ _ (hp2 18)
          have b44591 := hb (x 18 2)
          have b44592 := hb (x 18 14)
          clear * - r44590 b44591 b44592 d44576
          omega
        have d44593 : (x 20 12).toNat = 0 := by
          have r44594 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
          have e44595 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
          have e44596 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
          have b44597 := hb (x 17 3)
          have b44598 := hb (x 18 2)
          have b44599 := hb (x 19 13)
          have b44600 := hb (x 20 12)
          clear * - r44594 e44595 e44596 b44597 b44598 b44599 b44600 d44584 d44589
          omega
        have d44601 : (x 17 3).toNat = 0 := by
          have r44602 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
          have e44603 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
          have e44604 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
          have b44605 := hb (x 17 3)
          have b44606 := hb (x 18 2)
          have b44607 := hb (x 19 13)
          have b44608 := hb (x 20 12)
          clear * - r44602 e44603 e44604 b44605 b44606 b44607 b44608 d44593 d44584 d44589
          omega
        have d44609 : (x 17 11).toNat = 0 := by
          have r44610 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
          have b44611 := hb (x 17 3)
          have b44612 := hb (x 17 11)
          clear * - r44610 b44611 b44612 d44601
          omega
        have d44613 : (x 16 12).toNat = 0 := by
          have r44614 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
          have e44615 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
          have e44616 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
          have b44617 := hb (x 13 3)
          have b44618 := hb (x 14 2)
          have b44619 := hb (x 15 13)
          have b44620 := hb (x 16 12)
          clear * - r44614 e44615 e44616 b44617 b44618 b44619 b44620 d44550 d44475
          omega
        have d44621 : (x 16 1 && x 16 12).toNat = 0 := by
          have r44622 := hand2 (x 16 1) (x 16 12)
          have b44623 := hb (x 16 12)
          have b44624 := hb (x 16 1 && x 16 12)
          clear * - r44622 b44623 b44624 d44613
          omega
        have d44625 : (x 13 12).toNat = 0 := by
          have r44626 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
          have e44627 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
          have e44628 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
          have b44629 := hb (x 10 3)
          have b44630 := hb (x 11 2)
          have b44631 := hb (x 12 13)
          have b44632 := hb (x 13 12)
          clear * - r44626 e44627 e44628 b44629 b44630 b44631 b44632 d44487 d44408
          omega
        have d44633 : (x 13 4).toNat = 0 := by
          have r44634 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
          have b44635 := hb (x 13 4)
          have b44636 := hb (x 13 12)
          clear * - r44634 b44635 b44636 d44625
          omega
        have r44637 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := hcov11 17
        have b44638 := hb (x 13 4)
        have b44639 := hb (x 17 11)
        have b44640 := hb (x 16 1 && x 16 12)
        have b44641 := hb (x 15 2 && x 15 13)
        have b44642 := hb (x 14 3 && x 14 14)
        linarith only [r44637, b44638, b44639, b44640, b44641, b44642, d44609, d44621, d44542, d44471, d44633]
    · have f44643 : (x 0 13).toNat = 1 := by rw [h42552]; rfl
      have d44644 : (x 1 12).toNat = 0 := by
        have r44645 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
        have e44646 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e44647 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b44648 := hb (x (-2) 3)
        have b44649 := hb (x (-1) 2)
        have b44650 := hb (x 0 13)
        have b44651 := hb (x 1 12)
        clear * - r44645 e44646 e44647 b44648 b44649 b44650 b44651 f44643
        omega
      have d44652 : (x (-1) 2).toNat = 0 := by
        have r44653 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
        have e44654 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e44655 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b44656 := hb (x (-2) 3)
        have b44657 := hb (x (-1) 2)
        have b44658 := hb (x 0 13)
        have b44659 := hb (x 1 12)
        clear * - r44653 e44654 e44655 b44656 b44657 b44658 b44659 d44644 f44643
        omega
      have d44660 : (x 1 13).toNat = 1 := by
        have r44661 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := hcov13 1
        have b44662 := hb (x (-1) 2)
        have b44663 := hb (x 1 13)
        have b44664 := hb (x 0 1 && x 0 14)
        clear * - r44661 b44662 b44663 b44664 g47 d44652
        omega
      have d44665 : (x 1 1).toNat = 1 := by
        have r44666 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
        have b44667 := hb (x 1 1)
        have b44668 := hb (x 1 13)
        clear * - r44666 b44667 b44668 d44660
        omega
      have d44669 : (x 2 14).toNat = 0 := by
        have r44670 : (x 2 14).toNat + (x 1 1).toNat = 1 := hd14 2
        have b44671 := hb (x 1 1)
        have b44672 := hb (x 2 14)
        clear * - r44670 b44671 b44672 d44665
        omega
      have d44673 : (x 2 1 && x 2 14).toNat = 0 := by
        have r44674 := hand2 (x 2 1) (x 2 14)
        have b44675 := hb (x 2 14)
        have b44676 := hb (x 2 1 && x 2 14)
        clear * - r44674 b44675 b44676 d44669
        omega
      have d44677 : (x 3 13).toNat = 1 := by
        have r44678 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := hcov13 3
        have b44679 := hb (x 1 2)
        have b44680 := hb (x 3 13)
        have b44681 := hb (x 2 1 && x 2 14)
        clear * - r44678 b44679 b44680 b44681 d44673 g14
        omega
      have d44682 : (x 3 1).toNat = 1 := by
        have r44683 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
        have b44684 := hb (x 3 1)
        have b44685 := hb (x 3 13)
        clear * - r44683 b44684 b44685 d44677
        omega
      have d44686 : (x 4 14).toNat = 0 := by
        have r44687 : (x 4 14).toNat + (x 3 1).toNat = 1 := hd14 4
        have b44688 := hb (x 3 1)
        have b44689 := hb (x 4 14)
        clear * - r44687 b44688 b44689 d44682
        omega
      have d44690 : (x 4 1 && x 4 14).toNat = 0 := by
        have r44691 := hand2 (x 4 1) (x 4 14)
        have b44692 := hb (x 4 14)
        have b44693 := hb (x 4 1 && x 4 14)
        clear * - r44691 b44692 b44693 d44686
        omega
      have d44694 : (x 5 13).toNat = 1 := by
        have r44695 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := hcov13 5
        have b44696 := hb (x 3 2)
        have b44697 := hb (x 5 13)
        have b44698 := hb (x 4 1 && x 4 14)
        clear * - r44695 b44696 b44697 b44698 d44690 g18
        omega
      have d44699 : (x 5 1).toNat = 1 := by
        have r44700 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
        have b44701 := hb (x 5 1)
        have b44702 := hb (x 5 13)
        clear * - r44700 b44701 b44702 d44694
        omega
      have d44703 : (x 6 14).toNat = 0 := by
        have r44704 : (x 6 14).toNat + (x 5 1).toNat = 1 := hd14 6
        have b44705 := hb (x 5 1)
        have b44706 := hb (x 6 14)
        clear * - r44704 b44705 b44706 d44699
        omega
      have d44707 : (x 6 1 && x 6 14).toNat = 0 := by
        have r44708 := hand2 (x 6 1) (x 6 14)
        have b44709 := hb (x 6 14)
        have b44710 := hb (x 6 1 && x 6 14)
        clear * - r44708 b44709 b44710 d44703
        omega
      have d44711 : (x 6 2).toNat = 0 := by
        have r44712 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
        have b44713 := hb (x 6 2)
        have b44714 := hb (x 6 14)
        clear * - r44712 b44713 b44714 d44703
        omega
      have d44715 : (x 6 12).toNat = 0 := by
        have r44716 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
        have e44717 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
        have e44718 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
        have b44719 := hb (x 3 3)
        have b44720 := hb (x 4 2)
        have b44721 := hb (x 5 13)
        have b44722 := hb (x 6 12)
        clear * - r44716 e44717 e44718 b44719 b44720 b44721 b44722 d44694
        omega
      have d44723 : (x 4 2).toNat = 0 := by
        have r44724 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
        have e44725 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
        have e44726 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
        have b44727 := hb (x 3 3)
        have b44728 := hb (x 4 2)
        have b44729 := hb (x 5 13)
        have b44730 := hb (x 6 12)
        clear * - r44724 e44725 e44726 b44727 b44728 b44729 b44730 d44715 d44694
        omega
      have d44731 : (x 4 12).toNat = 0 := by
        have r44732 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
        have e44733 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e44734 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b44735 := hb (x 1 3)
        have b44736 := hb (x 2 2)
        have b44737 := hb (x 3 13)
        have b44738 := hb (x 4 12)
        clear * - r44732 e44733 e44734 b44735 b44736 b44737 b44738 d44677
        omega
      have d44739 : (x 2 2).toNat = 0 := by
        have r44740 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
        have e44741 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e44742 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b44743 := hb (x 1 3)
        have b44744 := hb (x 2 2)
        have b44745 := hb (x 3 13)
        have b44746 := hb (x 4 12)
        clear * - r44740 e44741 e44742 b44743 b44744 b44745 b44746 d44731 d44677
        omega
      have d44747 : (x 4 13).toNat = 1 := by
        have r44748 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
        have b44749 := hb (x 2 2)
        have b44750 := hb (x 4 13)
        have b44751 := hb (x 3 1 && x 3 14)
        clear * - r44748 b44749 b44750 b44751 g48 d44739
        omega
      have d44752 : (x 4 1).toNat = 1 := by
        have r44753 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
        have b44754 := hb (x 4 1)
        have b44755 := hb (x 4 13)
        clear * - r44753 b44754 b44755 d44747
        omega
      have d44756 : (x 5 14).toNat = 0 := by
        have r44757 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
        have b44758 := hb (x 4 1)
        have b44759 := hb (x 5 14)
        clear * - r44757 b44758 b44759 d44752
        omega
      have d44760 : (x 5 1 && x 5 14).toNat = 0 := by
        have r44761 := hand2 (x 5 1) (x 5 14)
        have b44762 := hb (x 5 14)
        have b44763 := hb (x 5 1 && x 5 14)
        clear * - r44761 b44762 b44763 d44756
        omega
      have d44764 : (x 6 13).toNat = 1 := by
        have r44765 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := hcov13 6
        have b44766 := hb (x 4 2)
        have b44767 := hb (x 6 13)
        have b44768 := hb (x 5 1 && x 5 14)
        clear * - r44765 b44766 b44767 b44768 d44760 d44723
        omega
      have d44769 : (x 6 1).toNat = 1 := by
        have r44770 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
        have b44771 := hb (x 6 1)
        have b44772 := hb (x 6 13)
        clear * - r44770 b44771 b44772 d44764
        omega
      have d44773 : (x 7 14).toNat = 0 := by
        have r44774 : (x 7 14).toNat + (x 6 1).toNat = 1 := hd14 7
        have b44775 := hb (x 6 1)
        have b44776 := hb (x 7 14)
        clear * - r44774 b44775 b44776 d44769
        omega
      have d44777 : (x 7 1 && x 7 14).toNat = 0 := by
        have r44778 := hand2 (x 7 1) (x 7 14)
        have b44779 := hb (x 7 14)
        have b44780 := hb (x 7 1 && x 7 14)
        clear * - r44778 b44779 b44780 d44773
        omega
      have d44781 : (x 8 13).toNat = 1 := by
        have r44782 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := hcov13 8
        have b44783 := hb (x 6 2)
        have b44784 := hb (x 8 13)
        have b44785 := hb (x 7 1 && x 7 14)
        clear * - r44782 b44783 b44784 b44785 d44777 d44711
        omega
      have d44786 : (x 8 1).toNat = 1 := by
        have r44787 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
        have b44788 := hb (x 8 1)
        have b44789 := hb (x 8 13)
        clear * - r44787 b44788 b44789 d44781
        omega
      have d44790 : (x 9 14).toNat = 0 := by
        have r44791 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
        have b44792 := hb (x 8 1)
        have b44793 := hb (x 9 14)
        clear * - r44791 b44792 b44793 d44786
        omega
      have d44794 : (x 9 1 && x 9 14).toNat = 0 := by
        have r44795 := hand2 (x 9 1) (x 9 14)
        have b44796 := hb (x 9 14)
        have b44797 := hb (x 9 1 && x 9 14)
        clear * - r44795 b44796 b44797 d44790
        omega
      have d44798 : (x 9 2).toNat = 0 := by
        have r44799 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
        have b44800 := hb (x 9 2)
        have b44801 := hb (x 9 14)
        clear * - r44799 b44800 b44801 d44790
        omega
      have d44802 : (x 9 12).toNat = 0 := by
        have r44803 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
        have e44804 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
        have e44805 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
        have b44806 := hb (x 6 3)
        have b44807 := hb (x 7 2)
        have b44808 := hb (x 8 13)
        have b44809 := hb (x 9 12)
        clear * - r44803 e44804 e44805 b44806 b44807 b44808 b44809 d44781
        omega
      have d44810 : (x 7 2).toNat = 0 := by
        have r44811 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
        have e44812 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
        have e44813 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
        have b44814 := hb (x 6 3)
        have b44815 := hb (x 7 2)
        have b44816 := hb (x 8 13)
        have b44817 := hb (x 9 12)
        clear * - r44811 e44812 e44813 b44814 b44815 b44816 b44817 d44802 d44781
        omega
      have d44818 : (x 7 12).toNat = 0 := by
        have r44819 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
        have e44820 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
        have e44821 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
        have b44822 := hb (x 4 3)
        have b44823 := hb (x 5 2)
        have b44824 := hb (x 6 13)
        have b44825 := hb (x 7 12)
        clear * - r44819 e44820 e44821 b44822 b44823 b44824 b44825 d44764
        omega
      have d44826 : (x 5 2).toNat = 0 := by
        have r44827 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
        have e44828 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
        have e44829 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
        have b44830 := hb (x 4 3)
        have b44831 := hb (x 5 2)
        have b44832 := hb (x 6 13)
        have b44833 := hb (x 7 12)
        clear * - r44827 e44828 e44829 b44830 b44831 b44832 b44833 d44818 d44764
        omega
      have d44834 : (x 7 13).toNat = 1 := by
        have r44835 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
        have b44836 := hb (x 5 2)
        have b44837 := hb (x 7 13)
        have b44838 := hb (x 6 1 && x 6 14)
        clear * - r44835 b44836 b44837 b44838 d44707 d44826
        omega
      have d44839 : (x 7 1).toNat = 1 := by
        have r44840 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
        have b44841 := hb (x 7 1)
        have b44842 := hb (x 7 13)
        clear * - r44840 b44841 b44842 d44834
        omega
      have d44843 : (x 8 14).toNat = 0 := by
        have r44844 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
        have b44845 := hb (x 7 1)
        have b44846 := hb (x 8 14)
        clear * - r44844 b44845 b44846 d44839
        omega
      have d44847 : (x 8 1 && x 8 14).toNat = 0 := by
        have r44848 := hand2 (x 8 1) (x 8 14)
        have b44849 := hb (x 8 14)
        have b44850 := hb (x 8 1 && x 8 14)
        clear * - r44848 b44849 b44850 d44843
        omega
      have d44851 : (x 9 13).toNat = 1 := by
        have r44852 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := hcov13 9
        have b44853 := hb (x 7 2)
        have b44854 := hb (x 9 13)
        have b44855 := hb (x 8 1 && x 8 14)
        clear * - r44852 b44853 b44854 b44855 d44847 d44810
        omega
      have d44856 : (x 9 1).toNat = 1 := by
        have r44857 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
        have b44858 := hb (x 9 1)
        have b44859 := hb (x 9 13)
        clear * - r44857 b44858 b44859 d44851
        omega
      have d44860 : (x 10 14).toNat = 0 := by
        have r44861 : (x 10 14).toNat + (x 9 1).toNat = 1 := hd14 10
        have b44862 := hb (x 9 1)
        have b44863 := hb (x 10 14)
        clear * - r44861 b44862 b44863 d44856
        omega
      have d44864 : (x 10 1 && x 10 14).toNat = 0 := by
        have r44865 := hand2 (x 10 1) (x 10 14)
        have b44866 := hb (x 10 14)
        have b44867 := hb (x 10 1 && x 10 14)
        clear * - r44865 b44866 b44867 d44860
        omega
      have d44868 : (x 11 13).toNat = 1 := by
        have r44869 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := hcov13 11
        have b44870 := hb (x 9 2)
        have b44871 := hb (x 11 13)
        have b44872 := hb (x 10 1 && x 10 14)
        clear * - r44869 b44870 b44871 b44872 d44864 d44798
        omega
      have d44873 : (x 11 1).toNat = 1 := by
        have r44874 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
        have b44875 := hb (x 11 1)
        have b44876 := hb (x 11 13)
        clear * - r44874 b44875 b44876 d44868
        omega
      have d44877 : (x 12 14).toNat = 0 := by
        have r44878 : (x 12 14).toNat + (x 11 1).toNat = 1 := hd14 12
        have b44879 := hb (x 11 1)
        have b44880 := hb (x 12 14)
        clear * - r44878 b44879 b44880 d44873
        omega
      have d44881 : (x 12 1 && x 12 14).toNat = 0 := by
        have r44882 := hand2 (x 12 1) (x 12 14)
        have b44883 := hb (x 12 14)
        have b44884 := hb (x 12 1 && x 12 14)
        clear * - r44882 b44883 b44884 d44877
        omega
      have d44885 : (x 12 2).toNat = 0 := by
        have r44886 : (x 12 2).toNat ≤ (x 12 14).toNat := himp _ _ (hp2 12)
        have b44887 := hb (x 12 2)
        have b44888 := hb (x 12 14)
        clear * - r44886 b44887 b44888 d44877
        omega
      have d44889 : (x 12 12).toNat = 0 := by
        have r44890 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
        have e44891 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
        have e44892 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
        have b44893 := hb (x 9 3)
        have b44894 := hb (x 10 2)
        have b44895 := hb (x 11 13)
        have b44896 := hb (x 12 12)
        clear * - r44890 e44891 e44892 b44893 b44894 b44895 b44896 d44868
        omega
      have d44897 : (x 10 2).toNat = 0 := by
        have r44898 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
        have e44899 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
        have e44900 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
        have b44901 := hb (x 9 3)
        have b44902 := hb (x 10 2)
        have b44903 := hb (x 11 13)
        have b44904 := hb (x 12 12)
        clear * - r44898 e44899 e44900 b44901 b44902 b44903 b44904 d44889 d44868
        omega
      have d44905 : (x 10 12).toNat = 0 := by
        have r44906 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
        have e44907 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
        have e44908 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
        have b44909 := hb (x 7 3)
        have b44910 := hb (x 8 2)
        have b44911 := hb (x 9 13)
        have b44912 := hb (x 10 12)
        clear * - r44906 e44907 e44908 b44909 b44910 b44911 b44912 d44851
        omega
      have d44913 : (x 8 2).toNat = 0 := by
        have r44914 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
        have e44915 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
        have e44916 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
        have b44917 := hb (x 7 3)
        have b44918 := hb (x 8 2)
        have b44919 := hb (x 9 13)
        have b44920 := hb (x 10 12)
        clear * - r44914 e44915 e44916 b44917 b44918 b44919 b44920 d44905 d44851
        omega
      have d44921 : (x 10 13).toNat = 1 := by
        have r44922 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := hcov13 10
        have b44923 := hb (x 8 2)
        have b44924 := hb (x 10 13)
        have b44925 := hb (x 9 1 && x 9 14)
        clear * - r44922 b44923 b44924 b44925 d44794 d44913
        omega
      have d44926 : (x 10 1).toNat = 1 := by
        have r44927 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
        have b44928 := hb (x 10 1)
        have b44929 := hb (x 10 13)
        clear * - r44927 b44928 b44929 d44921
        omega
      have d44930 : (x 11 14).toNat = 0 := by
        have r44931 : (x 11 14).toNat + (x 10 1).toNat = 1 := hd14 11
        have b44932 := hb (x 10 1)
        have b44933 := hb (x 11 14)
        clear * - r44931 b44932 b44933 d44926
        omega
      have d44934 : (x 11 1 && x 11 14).toNat = 0 := by
        have r44935 := hand2 (x 11 1) (x 11 14)
        have b44936 := hb (x 11 14)
        have b44937 := hb (x 11 1 && x 11 14)
        clear * - r44935 b44936 b44937 d44930
        omega
      have d44938 : (x 12 13).toNat = 1 := by
        have r44939 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := hcov13 12
        have b44940 := hb (x 10 2)
        have b44941 := hb (x 12 13)
        have b44942 := hb (x 11 1 && x 11 14)
        clear * - r44939 b44940 b44941 b44942 d44934 d44897
        omega
      have d44943 : (x 12 1).toNat = 1 := by
        have r44944 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
        have b44945 := hb (x 12 1)
        have b44946 := hb (x 12 13)
        clear * - r44944 b44945 b44946 d44938
        omega
      have d44947 : (x 13 14).toNat = 0 := by
        have r44948 : (x 13 14).toNat + (x 12 1).toNat = 1 := hd14 13
        have b44949 := hb (x 12 1)
        have b44950 := hb (x 13 14)
        clear * - r44948 b44949 b44950 d44943
        omega
      have d44951 : (x 13 1 && x 13 14).toNat = 0 := by
        have r44952 := hand2 (x 13 1) (x 13 14)
        have b44953 := hb (x 13 14)
        have b44954 := hb (x 13 1 && x 13 14)
        clear * - r44952 b44953 b44954 d44947
        omega
      have d44955 : (x 14 13).toNat = 1 := by
        have r44956 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
        have b44957 := hb (x 12 2)
        have b44958 := hb (x 14 13)
        have b44959 := hb (x 13 1 && x 13 14)
        clear * - r44956 b44957 b44958 b44959 d44951 d44885
        omega
      have d44960 : (x 14 1).toNat = 1 := by
        have r44961 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
        have b44962 := hb (x 14 1)
        have b44963 := hb (x 14 13)
        clear * - r44961 b44962 b44963 d44955
        omega
      have d44964 : (x 15 14).toNat = 0 := by
        have r44965 : (x 15 14).toNat + (x 14 1).toNat = 1 := hd14 15
        have b44966 := hb (x 14 1)
        have b44967 := hb (x 15 14)
        clear * - r44965 b44966 b44967 d44960
        omega
      have d44968 : (x 15 1 && x 15 14).toNat = 0 := by
        have r44969 := hand2 (x 15 1) (x 15 14)
        have b44970 := hb (x 15 14)
        have b44971 := hb (x 15 1 && x 15 14)
        clear * - r44969 b44970 b44971 d44964
        omega
      have d44972 : (x 15 2).toNat = 0 := by
        have r44973 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
        have b44974 := hb (x 15 2)
        have b44975 := hb (x 15 14)
        clear * - r44973 b44974 b44975 d44964
        omega
      have d44976 : (x 15 2 && x 15 13).toNat = 0 := by
        have r44977 := hand1 (x 15 2) (x 15 13)
        have b44978 := hb (x 15 2)
        have b44979 := hb (x 15 2 && x 15 13)
        clear * - r44977 b44978 b44979 d44972
        omega
      have d44980 : (x 15 12).toNat = 0 := by
        have r44981 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
        have e44982 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e44983 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b44984 := hb (x 12 3)
        have b44985 := hb (x 13 2)
        have b44986 := hb (x 14 13)
        have b44987 := hb (x 15 12)
        clear * - r44981 e44982 e44983 b44984 b44985 b44986 b44987 d44955
        omega
      have d44988 : (x 13 2).toNat = 0 := by
        have r44989 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
        have e44990 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e44991 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b44992 := hb (x 12 3)
        have b44993 := hb (x 13 2)
        have b44994 := hb (x 14 13)
        have b44995 := hb (x 15 12)
        clear * - r44989 e44990 e44991 b44992 b44993 b44994 b44995 d44980 d44955
        omega
      have d44996 : (x 13 12).toNat = 0 := by
        have r44997 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
        have e44998 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
        have e44999 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
        have b45000 := hb (x 10 3)
        have b45001 := hb (x 11 2)
        have b45002 := hb (x 12 13)
        have b45003 := hb (x 13 12)
        clear * - r44997 e44998 e44999 b45000 b45001 b45002 b45003 d44938
        omega
      have d45004 : (x 13 4).toNat = 0 := by
        have r45005 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
        have b45006 := hb (x 13 4)
        have b45007 := hb (x 13 12)
        clear * - r45005 b45006 b45007 d44996
        omega
      have d45008 : (x 11 2).toNat = 0 := by
        have r45009 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
        have e45010 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
        have e45011 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
        have b45012 := hb (x 10 3)
        have b45013 := hb (x 11 2)
        have b45014 := hb (x 12 13)
        have b45015 := hb (x 13 12)
        clear * - r45009 e45010 e45011 b45012 b45013 b45014 b45015 d44996 d44938
        omega
      have d45016 : (x 13 13).toNat = 1 := by
        have r45017 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := hcov13 13
        have b45018 := hb (x 11 2)
        have b45019 := hb (x 13 13)
        have b45020 := hb (x 12 1 && x 12 14)
        clear * - r45017 b45018 b45019 b45020 d44881 d45008
        omega
      have d45021 : (x 13 1).toNat = 1 := by
        have r45022 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
        have b45023 := hb (x 13 1)
        have b45024 := hb (x 13 13)
        clear * - r45022 b45023 b45024 d45016
        omega
      have d45025 : (x 14 14).toNat = 0 := by
        have r45026 : (x 14 14).toNat + (x 13 1).toNat = 1 := hd14 14
        have b45027 := hb (x 13 1)
        have b45028 := hb (x 14 14)
        clear * - r45026 b45027 b45028 d45021
        omega
      have d45029 : (x 14 1 && x 14 14).toNat = 0 := by
        have r45030 := hand2 (x 14 1) (x 14 14)
        have b45031 := hb (x 14 14)
        have b45032 := hb (x 14 1 && x 14 14)
        clear * - r45030 b45031 b45032 d45025
        omega
      have d45033 : (x 15 13).toNat = 1 := by
        have r45034 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := hcov13 15
        have b45035 := hb (x 13 2)
        have b45036 := hb (x 15 13)
        have b45037 := hb (x 14 1 && x 14 14)
        clear * - r45034 b45035 b45036 b45037 d45029 d44988
        omega
      have d45038 : (x 15 1).toNat = 1 := by
        have r45039 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
        have b45040 := hb (x 15 1)
        have b45041 := hb (x 15 13)
        clear * - r45039 b45040 b45041 d45033
        omega
      have d45042 : (x 16 14).toNat = 0 := by
        have r45043 : (x 16 14).toNat + (x 15 1).toNat = 1 := hd14 16
        have b45044 := hb (x 15 1)
        have b45045 := hb (x 16 14)
        clear * - r45043 b45044 b45045 d45038
        omega
      have d45046 : (x 16 1 && x 16 14).toNat = 0 := by
        have r45047 := hand2 (x 16 1) (x 16 14)
        have b45048 := hb (x 16 14)
        have b45049 := hb (x 16 1 && x 16 14)
        clear * - r45047 b45048 b45049 d45042
        omega
      have d45050 : (x 17 13).toNat = 1 := by
        have r45051 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := hcov13 17
        have b45052 := hb (x 15 2)
        have b45053 := hb (x 17 13)
        have b45054 := hb (x 16 1 && x 16 14)
        clear * - r45051 b45052 b45053 b45054 d45046 d44972
        omega
      have d45055 : (x 17 1).toNat = 1 := by
        have r45056 : (x 17 13).toNat ≤ (x 17 1).toNat := himp _ _ (hp13 17)
        have b45057 := hb (x 17 1)
        have b45058 := hb (x 17 13)
        clear * - r45056 b45057 b45058 d45050
        omega
      have d45059 : (x 18 14).toNat = 0 := by
        have r45060 : (x 18 14).toNat + (x 17 1).toNat = 1 := hd14 18
        have b45061 := hb (x 17 1)
        have b45062 := hb (x 18 14)
        clear * - r45060 b45061 b45062 d45055
        omega
      have d45063 : (x 18 1 && x 18 14).toNat = 0 := by
        have r45064 := hand2 (x 18 1) (x 18 14)
        have b45065 := hb (x 18 14)
        have b45066 := hb (x 18 1 && x 18 14)
        clear * - r45064 b45065 b45066 d45059
        omega
      have d45067 : (x 18 2).toNat = 0 := by
        have r45068 : (x 18 2).toNat ≤ (x 18 14).toNat := himp _ _ (hp2 18)
        have b45069 := hb (x 18 2)
        have b45070 := hb (x 18 14)
        clear * - r45068 b45069 b45070 d45059
        omega
      have d45071 : (x 18 12).toNat = 0 := by
        have r45072 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
        have e45073 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
        have e45074 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
        have b45075 := hb (x 15 3)
        have b45076 := hb (x 16 2)
        have b45077 := hb (x 17 13)
        have b45078 := hb (x 18 12)
        clear * - r45072 e45073 e45074 b45075 b45076 b45077 b45078 d45050
        omega
      have d45079 : (x 16 2).toNat = 0 := by
        have r45080 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
        have e45081 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
        have e45082 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
        have b45083 := hb (x 15 3)
        have b45084 := hb (x 16 2)
        have b45085 := hb (x 17 13)
        have b45086 := hb (x 18 12)
        clear * - r45080 e45081 e45082 b45083 b45084 b45085 b45086 d45071 d45050
        omega
      have d45087 : (x 16 12).toNat = 0 := by
        have r45088 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
        have e45089 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
        have e45090 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
        have b45091 := hb (x 13 3)
        have b45092 := hb (x 14 2)
        have b45093 := hb (x 15 13)
        have b45094 := hb (x 16 12)
        clear * - r45088 e45089 e45090 b45091 b45092 b45093 b45094 d45033
        omega
      have d45095 : (x 16 1 && x 16 12).toNat = 0 := by
        have r45096 := hand2 (x 16 1) (x 16 12)
        have b45097 := hb (x 16 12)
        have b45098 := hb (x 16 1 && x 16 12)
        clear * - r45096 b45097 b45098 d45087
        omega
      have d45099 : (x 14 2).toNat = 0 := by
        have r45100 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
        have e45101 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
        have e45102 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
        have b45103 := hb (x 13 3)
        have b45104 := hb (x 14 2)
        have b45105 := hb (x 15 13)
        have b45106 := hb (x 16 12)
        clear * - r45100 e45101 e45102 b45103 b45104 b45105 b45106 d45087 d45033
        omega
      have d45107 : (x 16 13).toNat = 1 := by
        have r45108 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := hcov13 16
        have b45109 := hb (x 14 2)
        have b45110 := hb (x 16 13)
        have b45111 := hb (x 15 1 && x 15 14)
        clear * - r45108 b45109 b45110 b45111 d44968 d45099
        omega
      have d45112 : (x 16 1).toNat = 1 := by
        have r45113 : (x 16 13).toNat ≤ (x 16 1).toNat := himp _ _ (hp13 16)
        have b45114 := hb (x 16 1)
        have b45115 := hb (x 16 13)
        clear * - r45113 b45114 b45115 d45107
        omega
      have d45116 : (x 17 14).toNat = 0 := by
        have r45117 : (x 17 14).toNat + (x 16 1).toNat = 1 := hd14 17
        have b45118 := hb (x 16 1)
        have b45119 := hb (x 17 14)
        clear * - r45117 b45118 b45119 d45112
        omega
      have d45120 : (x 17 1 && x 17 14).toNat = 0 := by
        have r45121 := hand2 (x 17 1) (x 17 14)
        have b45122 := hb (x 17 14)
        have b45123 := hb (x 17 1 && x 17 14)
        clear * - r45121 b45122 b45123 d45116
        omega
      have d45124 : (x 18 13).toNat = 1 := by
        have r45125 : 1 ≤ (x 18 13).toNat + (x 17 1 && x 17 14).toNat + (x 16 2).toNat := hcov13 18
        have b45126 := hb (x 16 2)
        have b45127 := hb (x 18 13)
        have b45128 := hb (x 17 1 && x 17 14)
        clear * - r45125 b45126 b45127 b45128 d45120 d45079
        omega
      have d45129 : (x 19 12).toNat = 0 := by
        have r45130 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
        have e45131 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
        have e45132 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
        have b45133 := hb (x 16 3)
        have b45134 := hb (x 17 2)
        have b45135 := hb (x 18 13)
        have b45136 := hb (x 19 12)
        clear * - r45130 e45131 e45132 b45133 b45134 b45135 b45136 d45124
        omega
      have d45137 : (x 17 2).toNat = 0 := by
        have r45138 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
        have e45139 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
        have e45140 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
        have b45141 := hb (x 16 3)
        have b45142 := hb (x 17 2)
        have b45143 := hb (x 18 13)
        have b45144 := hb (x 19 12)
        clear * - r45138 e45139 e45140 b45141 b45142 b45143 b45144 d45129 d45124
        omega
      have d45145 : (x 19 13).toNat = 1 := by
        have r45146 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := hcov13 19
        have b45147 := hb (x 17 2)
        have b45148 := hb (x 19 13)
        have b45149 := hb (x 18 1 && x 18 14)
        clear * - r45146 b45147 b45148 b45149 d45063 d45137
        omega
      have d45150 : (x 20 12).toNat = 0 := by
        have r45151 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
        have e45152 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
        have e45153 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
        have b45154 := hb (x 17 3)
        have b45155 := hb (x 18 2)
        have b45156 := hb (x 19 13)
        have b45157 := hb (x 20 12)
        clear * - r45151 e45152 e45153 b45154 b45155 b45156 b45157 d45145 d45067
        omega
      have d45158 : (x 17 3).toNat = 0 := by
        have r45159 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
        have e45160 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
        have e45161 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
        have b45162 := hb (x 17 3)
        have b45163 := hb (x 18 2)
        have b45164 := hb (x 19 13)
        have b45165 := hb (x 20 12)
        clear * - r45159 e45160 e45161 b45162 b45163 b45164 b45165 d45150 d45145 d45067
        omega
      have d45166 : (x 17 11).toNat = 0 := by
        have r45167 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
        have b45168 := hb (x 17 3)
        have b45169 := hb (x 17 11)
        clear * - r45167 b45168 b45169 d45158
        omega
      have d45170 : (x 17 12).toNat = 0 := by
        have r45171 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
        have e45172 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
        have e45173 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
        have b45174 := hb (x 14 3)
        have b45175 := hb (x 15 2)
        have b45176 := hb (x 16 13)
        have b45177 := hb (x 17 12)
        clear * - r45171 e45172 e45173 b45174 b45175 b45176 b45177 d45107 d44972
        omega
      have d45178 : (x 14 3).toNat = 0 := by
        have r45179 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
        have e45180 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
        have e45181 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
        have b45182 := hb (x 14 3)
        have b45183 := hb (x 15 2)
        have b45184 := hb (x 16 13)
        have b45185 := hb (x 17 12)
        clear * - r45179 e45180 e45181 b45182 b45183 b45184 b45185 d45170 d45107 d44972
        omega
      have d45186 : (x 14 3 && x 14 14).toNat = 0 := by
        have r45187 := hand1 (x 14 3) (x 14 14)
        have b45188 := hb (x 14 3)
        have b45189 := hb (x 14 3 && x 14 14)
        clear * - r45187 b45188 b45189 d45178
        omega
      have r45190 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := hcov11 17
      have b45191 := hb (x 13 4)
      have b45192 := hb (x 17 11)
      have b45193 := hb (x 16 1 && x 16 12)
      have b45194 := hb (x 15 2 && x 15 13)
      have b45195 := hb (x 14 3 && x 14 14)
      linarith only [r45190, b45191, b45192, b45193, b45194, b45195, d45166, d45095, d44976, d45186, d45004]
  · have f45196 : (x 0 12).toNat = 1 := by rw [h42550]; rfl
    have d45197 : (x (-1) 13).toNat = 0 := by
      have r45198 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := hd12 0
      have e45199 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e45200 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have b45201 := hb (x (-3) 3)
      have b45202 := hb (x (-2) 2)
      have b45203 := hb (x (-1) 13)
      have b45204 := hb (x 0 12)
      clear * - r45198 e45199 e45200 b45201 b45202 b45203 b45204 f45196
      omega
    have d45205 : (x (-2) 2).toNat = 0 := by
      have r45206 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := hd12 0
      have e45207 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e45208 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have b45209 := hb (x (-3) 3)
      have b45210 := hb (x (-2) 2)
      have b45211 := hb (x (-1) 13)
      have b45212 := hb (x 0 12)
      clear * - r45206 e45207 e45208 b45209 b45210 b45211 b45212 f45196 d45197
      omega
    have d45213 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
      have r45214 := hand1 (x (-2) 2) (x (-2) 13)
      have b45215 := hb (x (-2) 2)
      have b45216 := hb (x (-2) 2 && x (-2) 13)
      clear * - r45214 b45215 b45216 d45205
      omega
    have d45217 : (x (-3) 3).toNat = 0 := by
      have r45218 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := hd12 0
      have e45219 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e45220 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have b45221 := hb (x (-3) 3)
      have b45222 := hb (x (-2) 2)
      have b45223 := hb (x (-1) 13)
      have b45224 := hb (x 0 12)
      clear * - r45218 e45219 e45220 b45221 b45222 b45223 b45224 f45196 d45197 d45205
      omega
    have d45225 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
      have r45226 := hand1 (x (-3) 3) (x (-3) 14)
      have b45227 := hb (x (-3) 3)
      have b45228 := hb (x (-3) 3 && x (-3) 14)
      clear * - r45226 b45227 b45228 d45217
      omega
    have d45229 : (x (-1) 1 && x (-1) 12).toNat = 1 := by
      have r45230 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := hcov11 0
      have b45231 := hb (x (-4) 4)
      have b45232 := hb (x 0 11)
      have b45233 := hb (x (-1) 1 && x (-1) 12)
      have b45234 := hb (x (-2) 2 && x (-2) 13)
      have b45235 := hb (x (-3) 3 && x (-3) 14)
      clear * - r45230 b45231 b45232 b45233 b45234 b45235 g13 d45213 d45225 g1
      omega
    have d45236 : (x (-1) 12).toNat = 1 := by
      have r45237 := hand2 (x (-1) 1) (x (-1) 12)
      have b45238 := hb (x (-1) 12)
      have b45239 := hb (x (-1) 1 && x (-1) 12)
      clear * - r45237 b45238 b45239 d45229
      omega
    have d45240 : (x (-2) 13).toNat = 0 := by
      have r45241 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
      have e45242 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e45243 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b45244 := hb (x (-4) 3)
      have b45245 := hb (x (-3) 2)
      have b45246 := hb (x (-2) 13)
      have b45247 := hb (x (-1) 12)
      clear * - r45241 e45242 e45243 b45244 b45245 b45246 b45247 d45236
      omega
    have d45248 : (x (-3) 2).toNat = 0 := by
      have r45249 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
      have e45250 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e45251 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b45252 := hb (x (-4) 3)
      have b45253 := hb (x (-3) 2)
      have b45254 := hb (x (-2) 13)
      have b45255 := hb (x (-1) 12)
      clear * - r45249 e45250 e45251 b45252 b45253 b45254 b45255 d45236 d45240
      omega
    have d45256 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
      have r45257 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := hcov13 (-1)
      have b45258 := hb (x (-3) 2)
      have b45259 := hb (x (-1) 13)
      have b45260 := hb (x (-2) 1 && x (-2) 14)
      clear * - r45257 b45258 b45259 b45260 d45197 d45248
      omega
    have d45261 : (x (-2) 1).toNat = 1 := by
      have r45262 := hand1 (x (-2) 1) (x (-2) 14)
      have b45263 := hb (x (-2) 1)
      have b45264 := hb (x (-2) 1 && x (-2) 14)
      clear * - r45262 b45263 b45264 d45256
      omega
    have d45265 : (x (-1) 14).toNat = 0 := by
      have r45266 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := hd14 (-1)
      have b45267 := hb (x (-2) 1)
      have b45268 := hb (x (-1) 14)
      clear * - r45266 b45267 b45268 d45261
      omega
    have d45269 : (x (-1) 1 && x (-1) 14).toNat = 0 := by
      have r45270 := hand2 (x (-1) 1) (x (-1) 14)
      have b45271 := hb (x (-1) 14)
      have b45272 := hb (x (-1) 1 && x (-1) 14)
      clear * - r45270 b45271 b45272 d45265
      omega
    have d45273 : (x 0 13).toNat = 1 := by
      have r45274 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := hcov13 0
      have b45275 := hb (x (-2) 2)
      have b45276 := hb (x 0 13)
      have b45277 := hb (x (-1) 1 && x (-1) 14)
      clear * - r45274 b45275 b45276 b45277 d45269 d45205
      omega
    have d45278 : (x 1 12).toNat = 0 := by
      have r45279 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
      have e45280 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e45281 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b45282 := hb (x (-2) 3)
      have b45283 := hb (x (-1) 2)
      have b45284 := hb (x 0 13)
      have b45285 := hb (x 1 12)
      clear * - r45279 e45280 e45281 b45282 b45283 b45284 b45285 d45273
      omega
    have d45286 : (x (-1) 2).toNat = 0 := by
      have r45287 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
      have e45288 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e45289 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b45290 := hb (x (-2) 3)
      have b45291 := hb (x (-1) 2)
      have b45292 := hb (x 0 13)
      have b45293 := hb (x 1 12)
      clear * - r45287 e45288 e45289 b45290 b45291 b45292 b45293 d45278 d45273
      omega
    have d45294 : (x 1 13).toNat = 1 := by
      have r45295 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := hcov13 1
      have b45296 := hb (x (-1) 2)
      have b45297 := hb (x 1 13)
      have b45298 := hb (x 0 1 && x 0 14)
      clear * - r45295 b45296 b45297 b45298 g47 d45286
      omega
    have d45299 : (x 1 1).toNat = 1 := by
      have r45300 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
      have b45301 := hb (x 1 1)
      have b45302 := hb (x 1 13)
      clear * - r45300 b45301 b45302 d45294
      omega
    have d45303 : (x 2 14).toNat = 0 := by
      have r45304 : (x 2 14).toNat + (x 1 1).toNat = 1 := hd14 2
      have b45305 := hb (x 1 1)
      have b45306 := hb (x 2 14)
      clear * - r45304 b45305 b45306 d45299
      omega
    have d45307 : (x 2 1 && x 2 14).toNat = 0 := by
      have r45308 := hand2 (x 2 1) (x 2 14)
      have b45309 := hb (x 2 14)
      have b45310 := hb (x 2 1 && x 2 14)
      clear * - r45308 b45309 b45310 d45303
      omega
    have d45311 : (x 3 13).toNat = 1 := by
      have r45312 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := hcov13 3
      have b45313 := hb (x 1 2)
      have b45314 := hb (x 3 13)
      have b45315 := hb (x 2 1 && x 2 14)
      clear * - r45312 b45313 b45314 b45315 d45307 g14
      omega
    have d45316 : (x 3 1).toNat = 1 := by
      have r45317 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
      have b45318 := hb (x 3 1)
      have b45319 := hb (x 3 13)
      clear * - r45317 b45318 b45319 d45311
      omega
    have d45320 : (x 4 14).toNat = 0 := by
      have r45321 : (x 4 14).toNat + (x 3 1).toNat = 1 := hd14 4
      have b45322 := hb (x 3 1)
      have b45323 := hb (x 4 14)
      clear * - r45321 b45322 b45323 d45316
      omega
    have d45324 : (x 4 1 && x 4 14).toNat = 0 := by
      have r45325 := hand2 (x 4 1) (x 4 14)
      have b45326 := hb (x 4 14)
      have b45327 := hb (x 4 1 && x 4 14)
      clear * - r45325 b45326 b45327 d45320
      omega
    have d45328 : (x 5 13).toNat = 1 := by
      have r45329 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := hcov13 5
      have b45330 := hb (x 3 2)
      have b45331 := hb (x 5 13)
      have b45332 := hb (x 4 1 && x 4 14)
      clear * - r45329 b45330 b45331 b45332 d45324 g18
      omega
    have d45333 : (x 6 12).toNat = 0 := by
      have r45334 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
      have e45335 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e45336 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b45337 := hb (x 3 3)
      have b45338 := hb (x 4 2)
      have b45339 := hb (x 5 13)
      have b45340 := hb (x 6 12)
      clear * - r45334 e45335 e45336 b45337 b45338 b45339 b45340 d45328
      omega
    have d45341 : (x 4 2).toNat = 0 := by
      have r45342 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
      have e45343 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e45344 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b45345 := hb (x 3 3)
      have b45346 := hb (x 4 2)
      have b45347 := hb (x 5 13)
      have b45348 := hb (x 6 12)
      clear * - r45342 e45343 e45344 b45345 b45346 b45347 b45348 d45333 d45328
      omega
    have d45349 : (x 4 12).toNat = 0 := by
      have r45350 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
      have e45351 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e45352 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b45353 := hb (x 1 3)
      have b45354 := hb (x 2 2)
      have b45355 := hb (x 3 13)
      have b45356 := hb (x 4 12)
      clear * - r45350 e45351 e45352 b45353 b45354 b45355 b45356 d45311
      omega
    have d45357 : (x 2 2).toNat = 0 := by
      have r45358 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
      have e45359 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e45360 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b45361 := hb (x 1 3)
      have b45362 := hb (x 2 2)
      have b45363 := hb (x 3 13)
      have b45364 := hb (x 4 12)
      clear * - r45358 e45359 e45360 b45361 b45362 b45363 b45364 d45349 d45311
      omega
    have d45365 : (x 2 2 && x 2 13).toNat = 0 := by
      have r45366 := hand1 (x 2 2) (x 2 13)
      have b45367 := hb (x 2 2)
      have b45368 := hb (x 2 2 && x 2 13)
      clear * - r45366 b45367 b45368 d45357
      omega
    have d45369 : (x 4 11).toNat = 1 := by
      have r45370 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := hcov11 4
      have b45371 := hb (x 0 4)
      have b45372 := hb (x 4 11)
      have b45373 := hb (x 3 1 && x 3 12)
      have b45374 := hb (x 2 2 && x 2 13)
      have b45375 := hb (x 1 3 && x 1 14)
      clear * - r45370 b45371 b45372 b45373 b45374 b45375 g43 d45365 g44 g8
      omega
    have d45376 : (x 4 3).toNat = 1 := by
      have r45377 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
      have b45378 := hb (x 4 3)
      have b45379 := hb (x 4 11)
      clear * - r45377 b45378 b45379 d45369
      omega
    have d45380 : (x 7 12).toNat = 0 := by
      have r45381 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
      have e45382 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
      have e45383 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
      have b45384 := hb (x 4 3)
      have b45385 := hb (x 5 2)
      have b45386 := hb (x 6 13)
      have b45387 := hb (x 7 12)
      clear * - r45381 e45382 e45383 b45384 b45385 b45386 b45387 d45376
      omega
    have d45388 : (x 6 13).toNat = 0 := by
      have r45389 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
      have e45390 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
      have e45391 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
      have b45392 := hb (x 4 3)
      have b45393 := hb (x 5 2)
      have b45394 := hb (x 6 13)
      have b45395 := hb (x 7 12)
      clear * - r45389 e45390 e45391 b45392 b45393 b45394 b45395 d45380 d45376
      omega
    have d45396 : (x 5 1 && x 5 14).toNat = 1 := by
      have r45397 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := hcov13 6
      have b45398 := hb (x 4 2)
      have b45399 := hb (x 6 13)
      have b45400 := hb (x 5 1 && x 5 14)
      clear * - r45397 b45398 b45399 b45400 d45388 d45341
      omega
    have d45401 : (x 5 14).toNat = 1 := by
      have r45402 := hand2 (x 5 1) (x 5 14)
      have b45403 := hb (x 5 14)
      have b45404 := hb (x 5 1 && x 5 14)
      clear * - r45402 b45403 b45404 d45396
      omega
    have d45405 : (x 4 1).toNat = 0 := by
      have r45406 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
      have b45407 := hb (x 4 1)
      have b45408 := hb (x 5 14)
      clear * - r45406 b45407 b45408 d45401
      omega
    have d45409 : (x 4 13).toNat = 0 := by
      have r45410 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
      have b45411 := hb (x 4 1)
      have b45412 := hb (x 4 13)
      clear * - r45410 b45411 b45412 d45405
      omega
    have r45413 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
    have b45414 := hb (x 2 2)
    have b45415 := hb (x 4 13)
    have b45416 := hb (x 3 1 && x 3 14)
    linarith only [r45413, b45414, b45415, b45416, d45409, g48, d45357]

theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a01000 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-5) 5).toNat = 0)
    (g1 : (x (-4) 4).toNat = 0)
    (g2 : (x (-3) 11).toNat = 0)
    (g3 : (x (-2) 10).toNat = 0)
    (g4 : (x (-1) 9).toNat = 0)
    (g5 : (x 0 1).toNat = 1)
    (g6 : (x 0 2).toNat = 0)
    (g7 : (x 0 3).toNat = 0)
    (g8 : (x 0 4).toNat = 0)
    (g9 : (x 0 6).toNat = 0)
    (g10 : (x 0 7).toNat = 0)
    (g11 : (x 0 8).toNat = 1)
    (g12 : (x 0 10).toNat = 0)
    (g13 : (x 0 11).toNat = 0)
    (g14 : (x 1 2).toNat = 0)
    (g15 : (x 1 6).toNat = 0)
    (g16 : (x 1 10).toNat = 0)
    (g17 : (x 2 1).toNat = 1)
    (g18 : (x 3 2).toNat = 0)
    (g19 : (x 3 4).toNat = 0)
    (g20 : (x 1 2 && x 1 6).toNat = 0)
    (g21 : (x 0 3 && x 0 7).toNat = 0)
    (g22 : (x 3 4 && x 3 8).toNat = 0)
    (g23 : (x 1 6 && x 1 10).toNat = 0)
    (g24 : (x 0 7 && x 0 11).toNat = 0)
    (g25 : (x 1 2 && x 1 7).toNat = 0)
    (g26 : (x 0 3 && x 0 8).toNat = 0)
    (g27 : (x (-1) 4 && x (-1) 9).toNat = 0)
    (g28 : (x (-2) 5 && x (-2) 10).toNat = 0)
    (g29 : (x (-3) 6 && x (-3) 11).toNat = 0)
    (g30 : (x 0 1 && x 0 7).toNat = 0)
    (g31 : (x (-4) 4 && x (-4) 11).toNat = 0)
    (g32 : (x (-5) 5 && x (-5) 12).toNat = 0)
    (g33 : (x (-6) 6 && x (-6) 13).toNat = 0)
    (g34 : (x (-7) 7 && x (-7) 14).toNat = 0)
    (g35 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g36 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g37 : (x 3 3 && x 3 12).toNat = 0)
    (g38 : (x 1 5 && x 1 14).toNat = 0)
    (g39 : (x (-4) 4 && x (-4) 14).toNat = 0)
    (g40 : (x 0 1 && x 0 11).toNat = 0)
    (g41 : (x 1 2 && x 1 13).toNat = 0)
    (g42 : (x 0 3 && x 0 14).toNat = 0)
    (g43 : (x 3 1 && x 3 12).toNat = 0)
    (g44 : (x 1 3 && x 1 14).toNat = 0)
    (g45 : (x 3 2 && x 3 13).toNat = 0)
    (g46 : (x 3 3 && x 3 14).toNat = 0)
    (g47 : (x 0 1 && x 0 14).toNat = 0)
    (g48 : (x 3 1 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a01000_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48
