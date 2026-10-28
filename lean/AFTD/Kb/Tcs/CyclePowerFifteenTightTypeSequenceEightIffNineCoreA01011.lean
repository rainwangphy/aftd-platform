import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a01011

Topic: combinatorics   Node: 6a61e0b7684c

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core: under the layer-free tight-cover constraints for k = 15 and 5 fixed bits of the class-type sequence near position 0, the constraints are contradictory. Its module also proves the sibling branches cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a010100001, cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a01010001, cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a0101001, cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a010101.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a010100001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-5) 11).toNat = 0)
    (g1 : (x (-4) 10).toNat = 0)
    (g2 : (x (-4) 11).toNat = 0)
    (g3 : (x (-3) 5).toNat = 0)
    (g4 : (x (-3) 9).toNat = 0)
    (g5 : (x (-3) 10).toNat = 0)
    (g6 : (x (-3) 11).toNat = 0)
    (g7 : (x (-2) 10).toNat = 0)
    (g8 : (x (-1) 4).toNat = 0)
    (g9 : (x (-1) 5).toNat = 0)
    (g10 : (x (-1) 6).toNat = 0)
    (g11 : (x (-1) 9).toNat = 0)
    (g12 : (x 0 2).toNat = 0)
    (g13 : (x 0 4).toNat = 0)
    (g14 : (x 0 5).toNat = 0)
    (g15 : (x 0 7).toNat = 0)
    (g16 : (x 0 8).toNat = 1)
    (g17 : (x 0 10).toNat = 0)
    (g18 : (x 1 2).toNat = 0)
    (g19 : (x 1 4).toNat = 0)
    (g20 : (x 1 6).toNat = 0)
    (g21 : (x 1 7).toNat = 1)
    (g22 : (x 3 2).toNat = 0)
    (g23 : (x 3 4).toNat = 0)
    (g24 : (x 3 6).toNat = 0)
    (g25 : (x (-3) 3 && x (-3) 7).toNat = 0)
    (g26 : (x (-4) 4 && x (-4) 8).toNat = 0)
    (g27 : (x (-5) 5 && x (-5) 9).toNat = 0)
    (g28 : (x (-6) 6 && x (-6) 10).toNat = 0)
    (g29 : (x (-7) 7 && x (-7) 11).toNat = 0)
    (g30 : (x 0 4 && x 0 8).toNat = 0)
    (g31 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g32 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g33 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g34 : (x 3 2 && x 3 6).toNat = 0)
    (g35 : (x 1 4 && x 1 8).toNat = 0)
    (g36 : (x 0 5 && x 0 9).toNat = 0)
    (g37 : (x (-1) 6 && x (-1) 10).toNat = 0)
    (g38 : (x 1 5 && x 1 10).toNat = 0)
    (g39 : (x 0 6 && x 0 11).toNat = 0)
    (g40 : (x (-1) 7 && x (-1) 12).toNat = 0)
    (g41 : (x (-3) 9 && x (-3) 14).toNat = 0)
    (g42 : (x (-1) 1 && x (-1) 7).toNat = 0)
    (g43 : (x (-3) 3 && x (-3) 9).toNat = 0)
    (g44 : (x (-4) 4 && x (-4) 10).toNat = 0)
    (g45 : (x (-5) 5 && x (-5) 11).toNat = 0)
    (g46 : (x (-6) 6 && x (-6) 12).toNat = 0)
    (g47 : (x (-7) 7 && x (-7) 13).toNat = 0)
    (g48 : (x 0 2 && x 0 8).toNat = 0)
    (g49 : (x (-1) 3 && x (-1) 9).toNat = 0)
    (g50 : (x (-2) 4 && x (-2) 10).toNat = 0)
    (g51 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g52 : (x (-1) 1 && x (-1) 8).toNat = 0)
    (g53 : (x (-3) 3 && x (-3) 10).toNat = 0)
    (g54 : (x (-4) 4 && x (-4) 11).toNat = 0)
    (g55 : (x (-5) 5 && x (-5) 12).toNat = 0)
    (g56 : (x (-6) 6 && x (-6) 13).toNat = 0)
    (g57 : (x (-7) 7 && x (-7) 14).toNat = 0)
    (g58 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g59 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g60 : (x (-4) 3 && x (-4) 12).toNat = 0)
    (g61 : (x 3 2 && x 3 11).toNat = 0)
    (g62 : (x 1 4 && x 1 13).toNat = 0)
    (g63 : (x 0 5 && x 0 14).toNat = 0)
    (g64 : (x 3 3 && x 3 12).toNat = 0)
    (g65 : (x 1 5 && x 1 14).toNat = 0)
    (g66 : (x 3 4 && x 3 13).toNat = 0)
    (g67 : (x 3 5 && x 3 14).toNat = 0)
    (g68 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g69 : (x (-4) 2 && x (-4) 12).toNat = 0)
    (g70 : (x (-5) 3 && x (-5) 13).toNat = 0)
    (g71 : (x 0 4 && x 0 14).toNat = 0)
    (g72 : (x 1 1 && x 1 12).toNat = 0)
    (g73 : (x 0 2 && x 0 13).toNat = 0)
    (g74 : (x (-1) 3 && x (-1) 14).toNat = 0)
    (g75 : (x 1 2 && x 1 13).toNat = 0)
    (g76 : (x 0 3 && x 0 14).toNat = 0)
    (g77 : (x 3 1 && x 3 12).toNat = 0)
    (g78 : (x 1 3 && x 1 14).toNat = 0)
    (g79 : (x 3 2 && x 3 13).toNat = 0)
    (g80 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d43569 : (x 8 8).toNat = 0 := by
    have r43570 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e43571 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e43572 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e43573 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e43574 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e43575 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e43576 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have b43577 := hb (x 1 7)
    have b43578 := hb (x 2 6)
    have b43579 := hb (x 3 5)
    have b43580 := hb (x 4 4)
    have b43581 := hb (x 5 11)
    have b43582 := hb (x 6 10)
    have b43583 := hb (x 7 9)
    have b43584 := hb (x 8 8)
    clear * - r43570 e43571 e43572 e43573 e43574 e43575 e43576 b43577 b43578 b43579 b43580 b43581 b43582 b43583 b43584 g21
    omega
  have d43585 : (x 8 8 && x 8 10).toNat = 0 := by
    have r43586 := hand1 (x 8 8) (x 8 10)
    have b43587 := hb (x 8 8)
    have b43588 := hb (x 8 8 && x 8 10)
    clear * - r43586 b43587 b43588 d43569
    omega
  have d43589 : (x 7 9).toNat = 0 := by
    have r43590 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e43591 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e43592 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e43593 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e43594 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e43595 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e43596 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have b43597 := hb (x 1 7)
    have b43598 := hb (x 2 6)
    have b43599 := hb (x 3 5)
    have b43600 := hb (x 4 4)
    have b43601 := hb (x 5 11)
    have b43602 := hb (x 6 10)
    have b43603 := hb (x 7 9)
    have b43604 := hb (x 8 8)
    clear * - r43590 e43591 e43592 e43593 e43594 e43595 e43596 b43597 b43598 b43599 b43600 b43601 b43602 b43603 b43604 d43569 g21
    omega
  have d43605 : (x 7 9 && x 7 11).toNat = 0 := by
    have r43606 := hand1 (x 7 9) (x 7 11)
    have b43607 := hb (x 7 9)
    have b43608 := hb (x 7 9 && x 7 11)
    clear * - r43606 b43607 b43608 d43589
    omega
  have d43609 : (x 6 10).toNat = 0 := by
    have r43610 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e43611 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e43612 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e43613 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e43614 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e43615 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e43616 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have b43617 := hb (x 1 7)
    have b43618 := hb (x 2 6)
    have b43619 := hb (x 3 5)
    have b43620 := hb (x 4 4)
    have b43621 := hb (x 5 11)
    have b43622 := hb (x 6 10)
    have b43623 := hb (x 7 9)
    have b43624 := hb (x 8 8)
    clear * - r43610 e43611 e43612 e43613 e43614 e43615 e43616 b43617 b43618 b43619 b43620 b43621 b43622 b43623 b43624 d43569 d43589 g21
    omega
  have d43625 : (x 6 1 && x 6 10).toNat = 0 := by
    have r43626 := hand2 (x 6 1) (x 6 10)
    have b43627 := hb (x 6 10)
    have b43628 := hb (x 6 1 && x 6 10)
    clear * - r43626 b43627 b43628 d43609
    omega
  have d43629 : (x 6 10 && x 6 12).toNat = 0 := by
    have r43630 := hand1 (x 6 10) (x 6 12)
    have b43631 := hb (x 6 10)
    have b43632 := hb (x 6 10 && x 6 12)
    clear * - r43630 b43631 b43632 d43609
    omega
  have d43633 : (x 5 11).toNat = 0 := by
    have r43634 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e43635 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e43636 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e43637 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e43638 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e43639 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e43640 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have b43641 := hb (x 1 7)
    have b43642 := hb (x 2 6)
    have b43643 := hb (x 3 5)
    have b43644 := hb (x 4 4)
    have b43645 := hb (x 5 11)
    have b43646 := hb (x 6 10)
    have b43647 := hb (x 7 9)
    have b43648 := hb (x 8 8)
    clear * - r43634 e43635 e43636 e43637 e43638 e43639 e43640 b43641 b43642 b43643 b43644 b43645 b43646 b43647 b43648 d43569 d43589 d43609 g21
    omega
  have d43649 : (x 5 1 && x 5 11).toNat = 0 := by
    have r43650 := hand2 (x 5 1) (x 5 11)
    have b43651 := hb (x 5 11)
    have b43652 := hb (x 5 1 && x 5 11)
    clear * - r43650 b43651 b43652 d43633
    omega
  have d43653 : (x 5 2 && x 5 11).toNat = 0 := by
    have r43654 := hand2 (x 5 2) (x 5 11)
    have b43655 := hb (x 5 11)
    have b43656 := hb (x 5 2 && x 5 11)
    clear * - r43654 b43655 b43656 d43633
    omega
  have d43657 : (x 5 11 && x 5 13).toNat = 0 := by
    have r43658 := hand1 (x 5 11) (x 5 13)
    have b43659 := hb (x 5 11)
    have b43660 := hb (x 5 11 && x 5 13)
    clear * - r43658 b43659 b43660 d43633
    omega
  have d43661 : (x 4 4).toNat = 0 := by
    have r43662 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e43663 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e43664 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e43665 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e43666 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e43667 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e43668 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have b43669 := hb (x 1 7)
    have b43670 := hb (x 2 6)
    have b43671 := hb (x 3 5)
    have b43672 := hb (x 4 4)
    have b43673 := hb (x 5 11)
    have b43674 := hb (x 6 10)
    have b43675 := hb (x 7 9)
    have b43676 := hb (x 8 8)
    clear * - r43662 e43663 e43664 e43665 e43666 e43667 e43668 b43669 b43670 b43671 b43672 b43673 b43674 b43675 b43676 d43569 d43589 d43609 d43633 g21
    omega
  have d43677 : (x 4 4 && x 4 14).toNat = 0 := by
    have r43678 := hand1 (x 4 4) (x 4 14)
    have b43679 := hb (x 4 4)
    have b43680 := hb (x 4 4 && x 4 14)
    clear * - r43678 b43679 b43680 d43661
    omega
  have d43681 : (x 4 4 && x 4 13).toNat = 0 := by
    have r43682 := hand1 (x 4 4) (x 4 13)
    have b43683 := hb (x 4 4)
    have b43684 := hb (x 4 4 && x 4 13)
    clear * - r43682 b43683 b43684 d43661
    omega
  have d43685 : (x 3 5).toNat = 0 := by
    have r43686 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e43687 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e43688 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e43689 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e43690 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e43691 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e43692 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have b43693 := hb (x 1 7)
    have b43694 := hb (x 2 6)
    have b43695 := hb (x 3 5)
    have b43696 := hb (x 4 4)
    have b43697 := hb (x 5 11)
    have b43698 := hb (x 6 10)
    have b43699 := hb (x 7 9)
    have b43700 := hb (x 8 8)
    clear * - r43686 e43687 e43688 e43689 e43690 e43691 e43692 b43693 b43694 b43695 b43696 b43697 b43698 b43699 b43700 d43569 d43589 d43609 d43633 d43661 g21
    omega
  have d43701 : (x 2 6).toNat = 0 := by
    have r43702 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e43703 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e43704 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e43705 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e43706 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e43707 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e43708 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have b43709 := hb (x 1 7)
    have b43710 := hb (x 2 6)
    have b43711 := hb (x 3 5)
    have b43712 := hb (x 4 4)
    have b43713 := hb (x 5 11)
    have b43714 := hb (x 6 10)
    have b43715 := hb (x 7 9)
    have b43716 := hb (x 8 8)
    clear * - r43702 e43703 e43704 e43705 e43706 e43707 e43708 b43709 b43710 b43711 b43712 b43713 b43714 b43715 b43716 d43569 d43589 d43609 d43633 d43661 d43685 g21
    omega
  have d43717 : (x 2 2 && x 2 6).toNat = 0 := by
    have r43718 := hand2 (x 2 2) (x 2 6)
    have b43719 := hb (x 2 6)
    have b43720 := hb (x 2 2 && x 2 6)
    clear * - r43718 b43719 b43720 d43701
    omega
  cases h43721 : x 0 6
  · have f43722 : (x 0 6).toNat = 0 := by rw [h43721]; rfl
    cases h43723 : x 1 3
    · have f43724 : (x 1 3).toNat = 0 := by rw [h43723]; rfl
      have d43725 : (x 1 3 && x 1 13).toNat = 0 := by
        have r43726 := hand1 (x 1 3) (x 1 13)
        have b43727 := hb (x 1 3)
        have b43728 := hb (x 1 3 && x 1 13)
        clear * - r43726 b43727 b43728 f43724
        omega
      have d43729 : (x 1 3 && x 1 7).toNat = 0 := by
        have r43730 := hand1 (x 1 3) (x 1 7)
        have b43731 := hb (x 1 3)
        have b43732 := hb (x 1 3 && x 1 7)
        clear * - r43730 b43731 b43732 f43724
        omega
      cases h43733 : x 1 5
      · have f43734 : (x 1 5).toNat = 0 := by rw [h43733]; rfl
        cases h43735 : x (-1) 7
        · have f43736 : (x (-1) 7).toNat = 0 := by rw [h43735]; rfl
          cases h43737 : x (-1) 8
          · have f43738 : (x (-1) 8).toNat = 0 := by rw [h43737]; rfl
            cases h43739 : x 1 13
            · have f43740 : (x 1 13).toNat = 0 := by rw [h43739]; rfl
              cases h43741 : x 2 2
              · have f43742 : (x 2 2).toNat = 0 := by rw [h43741]; rfl
                have d43743 : (x 2 2 && x 2 13).toNat = 0 := by
                  have r43744 := hand1 (x 2 2) (x 2 13)
                  have b43745 := hb (x 2 2)
                  have b43746 := hb (x 2 2 && x 2 13)
                  clear * - r43744 b43745 b43746 f43742
                  omega
                have d43747 : (x 2 2 && x 2 12).toNat = 0 := by
                  have r43748 := hand1 (x 2 2) (x 2 12)
                  have b43749 := hb (x 2 2)
                  have b43750 := hb (x 2 2 && x 2 12)
                  clear * - r43748 b43749 b43750 f43742
                  omega
                have d43751 : (x 4 13).toNat = 1 := by
                  have r43752 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b43753 := hb (x 2 2)
                  have b43754 := hb (x 4 13)
                  have b43755 := hb (x 3 1 && x 3 14)
                  clear * - r43752 b43753 b43754 b43755 g80 f43742
                  omega
                have d43756 : (x 4 1).toNat = 1 := by
                  have r43757 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
                  have b43758 := hb (x 4 1)
                  have b43759 := hb (x 4 13)
                  clear * - r43757 b43758 b43759 d43751
                  omega
                have d43760 : (x 5 14).toNat = 0 := by
                  have r43761 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b43762 := hb (x 4 1)
                  have b43763 := hb (x 5 14)
                  clear * - r43761 b43762 b43763 d43756
                  omega
                have d43764 : (x 5 1 && x 5 14).toNat = 0 := by
                  have r43765 := hand2 (x 5 1) (x 5 14)
                  have b43766 := hb (x 5 14)
                  have b43767 := hb (x 5 1 && x 5 14)
                  clear * - r43765 b43766 b43767 d43760
                  omega
                have d43768 : (x 5 3 && x 5 14).toNat = 0 := by
                  have r43769 := hand2 (x 5 3) (x 5 14)
                  have b43770 := hb (x 5 14)
                  have b43771 := hb (x 5 3 && x 5 14)
                  clear * - r43769 b43770 b43771 d43760
                  omega
                have d43772 : (x 5 6).toNat = 0 := by
                  have r43773 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
                  have b43774 := hb (x 5 6)
                  have b43775 := hb (x 5 14)
                  clear * - r43773 b43774 b43775 d43760
                  omega
                have d43776 : (x 5 1 && x 5 6).toNat = 0 := by
                  have r43777 := hand2 (x 5 1) (x 5 6)
                  have b43778 := hb (x 5 6)
                  have b43779 := hb (x 5 1 && x 5 6)
                  clear * - r43777 b43778 b43779 d43772
                  omega
                have d43780 : (x 5 2).toNat = 0 := by
                  have r43781 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
                  have b43782 := hb (x 5 2)
                  have b43783 := hb (x 5 14)
                  clear * - r43781 b43782 b43783 d43760
                  omega
                have d43784 : (x 5 12).toNat = 0 := by
                  have r43785 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e43786 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                  have e43787 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                  have b43788 := hb (x 2 3)
                  have b43789 := hb (x 3 2)
                  have b43790 := hb (x 4 13)
                  have b43791 := hb (x 5 12)
                  clear * - r43785 e43786 e43787 b43788 b43789 b43790 b43791 d43751 g22
                  omega
                have d43792 : (x 2 3).toNat = 0 := by
                  have r43793 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e43794 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                  have e43795 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                  have b43796 := hb (x 2 3)
                  have b43797 := hb (x 3 2)
                  have b43798 := hb (x 4 13)
                  have b43799 := hb (x 5 12)
                  clear * - r43793 e43794 e43795 b43796 b43797 b43798 b43799 d43784 d43751 g22
                  omega
                have d43800 : (x 2 3 && x 2 14).toNat = 0 := by
                  have r43801 := hand1 (x 2 3) (x 2 14)
                  have b43802 := hb (x 2 3)
                  have b43803 := hb (x 2 3 && x 2 14)
                  clear * - r43801 b43802 b43803 d43792
                  omega
                have d43804 : (x 2 11).toNat = 0 := by
                  have r43805 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
                  have b43806 := hb (x 2 3)
                  have b43807 := hb (x 2 11)
                  clear * - r43805 b43806 b43807 d43792
                  omega
                have d43808 : (x 4 1 && x 4 12).toNat = 1 := by
                  have r43809 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b43810 := hb (x 1 4)
                  have b43811 := hb (x 5 11)
                  have b43812 := hb (x 4 1 && x 4 12)
                  have b43813 := hb (x 3 2 && x 3 13)
                  have b43814 := hb (x 2 3 && x 2 14)
                  clear * - r43809 b43810 b43811 b43812 b43813 b43814 d43633 g79 d43800 g19
                  omega
                have d43815 : (x 4 12).toNat = 1 := by
                  have r43816 := hand2 (x 4 1) (x 4 12)
                  have b43817 := hb (x 4 12)
                  have b43818 := hb (x 4 1 && x 4 12)
                  clear * - r43816 b43817 b43818 d43808
                  omega
                have d43819 : (x 3 13).toNat = 0 := by
                  have r43820 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e43821 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                  have e43822 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                  have b43823 := hb (x 1 3)
                  have b43824 := hb (x 2 2)
                  have b43825 := hb (x 3 13)
                  have b43826 := hb (x 4 12)
                  clear * - r43820 e43821 e43822 b43823 b43824 b43825 b43826 d43815 f43742 f43724
                  omega
                have d43827 : (x 2 1 && x 2 14).toNat = 1 := by
                  have r43828 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b43829 := hb (x 1 2)
                  have b43830 := hb (x 3 13)
                  have b43831 := hb (x 2 1 && x 2 14)
                  clear * - r43828 b43829 b43830 b43831 d43819 g18
                  omega
                have d43832 : (x 2 14).toNat = 1 := by
                  have r43833 := hand2 (x 2 1) (x 2 14)
                  have b43834 := hb (x 2 14)
                  have b43835 := hb (x 2 1 && x 2 14)
                  clear * - r43833 b43834 b43835 d43827
                  omega
                have d43836 : (x 1 1).toNat = 0 := by
                  have r43837 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b43838 := hb (x 1 1)
                  have b43839 := hb (x 2 14)
                  clear * - r43837 b43838 b43839 d43832
                  omega
                have d43840 : (x 1 1 && x 1 7).toNat = 0 := by
                  have r43841 := hand1 (x 1 1) (x 1 7)
                  have b43842 := hb (x 1 1)
                  have b43843 := hb (x 1 1 && x 1 7)
                  clear * - r43841 b43842 b43843 d43836
                  omega
                have d43844 : (x 1 9).toNat = 0 := by
                  have r43845 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
                  have b43846 := hb (x 1 1)
                  have b43847 := hb (x 1 9)
                  clear * - r43845 b43846 b43847 d43836
                  omega
                have d43848 : (x 4 11).toNat = 1 := by
                  have r43849 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b43850 := hb (x 0 4)
                  have b43851 := hb (x 4 11)
                  have b43852 := hb (x 3 1 && x 3 12)
                  have b43853 := hb (x 2 2 && x 2 13)
                  have b43854 := hb (x 1 3 && x 1 14)
                  clear * - r43849 b43850 b43851 b43852 b43853 b43854 g77 d43743 g78 g13
                  omega
                have d43855 : (x 4 3).toNat = 1 := by
                  have r43856 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
                  have b43857 := hb (x 4 3)
                  have b43858 := hb (x 4 11)
                  clear * - r43856 b43857 b43858 d43848
                  omega
                have d43859 : (x 7 12).toNat = 0 := by
                  have r43860 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e43861 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                  have e43862 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                  have b43863 := hb (x 4 3)
                  have b43864 := hb (x 5 2)
                  have b43865 := hb (x 6 13)
                  have b43866 := hb (x 7 12)
                  clear * - r43860 e43861 e43862 b43863 b43864 b43865 b43866 d43780 d43855
                  omega
                have d43867 : (x 7 1 && x 7 12).toNat = 0 := by
                  have r43868 := hand2 (x 7 1) (x 7 12)
                  have b43869 := hb (x 7 12)
                  have b43870 := hb (x 7 1 && x 7 12)
                  clear * - r43868 b43869 b43870 d43859
                  omega
                have d43871 : (x 7 4).toNat = 0 := by
                  have r43872 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
                  have b43873 := hb (x 7 4)
                  have b43874 := hb (x 7 12)
                  clear * - r43872 b43873 b43874 d43859
                  omega
                have d43875 : (x 6 13).toNat = 0 := by
                  have r43876 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e43877 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                  have e43878 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                  have b43879 := hb (x 4 3)
                  have b43880 := hb (x 5 2)
                  have b43881 := hb (x 6 13)
                  have b43882 := hb (x 7 12)
                  clear * - r43876 e43877 e43878 b43879 b43880 b43881 b43882 d43859 d43780 d43855
                  omega
                have d43883 : (x 6 2 && x 6 13).toNat = 0 := by
                  have r43884 := hand2 (x 6 2) (x 6 13)
                  have b43885 := hb (x 6 13)
                  have b43886 := hb (x 6 2 && x 6 13)
                  clear * - r43884 b43885 b43886 d43875
                  omega
                have d43887 : (x 8 11).toNat = 1 := by
                  have r43888 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b43889 := hb (x 4 4)
                  have b43890 := hb (x 8 11)
                  have b43891 := hb (x 7 1 && x 7 12)
                  have b43892 := hb (x 6 2 && x 6 13)
                  have b43893 := hb (x 5 3 && x 5 14)
                  clear * - r43888 b43889 b43890 b43891 b43892 b43893 d43867 d43883 d43768 d43661
                  omega
                have d43894 : (x 8 3).toNat = 1 := by
                  have r43895 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
                  have b43896 := hb (x 8 3)
                  have b43897 := hb (x 8 11)
                  clear * - r43895 b43896 b43897 d43887
                  omega
                have d43898 : (x 11 12).toNat = 0 := by
                  have r43899 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e43900 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                  have e43901 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                  have b43902 := hb (x 8 3)
                  have b43903 := hb (x 9 2)
                  have b43904 := hb (x 10 13)
                  have b43905 := hb (x 11 12)
                  clear * - r43899 e43900 e43901 b43902 b43903 b43904 b43905 d43894
                  omega
                have d43906 : (x 10 13).toNat = 0 := by
                  have r43907 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e43908 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                  have e43909 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                  have b43910 := hb (x 8 3)
                  have b43911 := hb (x 9 2)
                  have b43912 := hb (x 10 13)
                  have b43913 := hb (x 11 12)
                  clear * - r43907 e43908 e43909 b43910 b43911 b43912 b43913 d43898 d43894
                  omega
                have d43914 : (x 9 2).toNat = 0 := by
                  have r43915 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e43916 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                  have e43917 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                  have b43918 := hb (x 8 3)
                  have b43919 := hb (x 9 2)
                  have b43920 := hb (x 10 13)
                  have b43921 := hb (x 11 12)
                  clear * - r43915 e43916 e43917 b43918 b43919 b43920 b43921 d43898 d43906 d43894
                  omega
                have d43922 : (x 9 10).toNat = 0 := by
                  have r43923 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
                  have b43924 := hb (x 9 2)
                  have b43925 := hb (x 9 10)
                  clear * - r43923 b43924 b43925 d43914
                  omega
                have d43926 : (x 6 5).toNat = 0 := by
                  have r43927 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
                  have b43928 := hb (x 6 5)
                  have b43929 := hb (x 6 13)
                  clear * - r43927 b43928 b43929 d43875
                  omega
                have d43930 : (x 4 2).toNat = 1 := by
                  have r43931 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b43932 := hb (x 4 2)
                  have b43933 := hb (x 6 13)
                  have b43934 := hb (x 5 1 && x 5 14)
                  clear * - r43931 b43932 b43933 b43934 d43875 d43764
                  omega
                have d43935 : (x 4 14).toNat = 1 := by
                  have r43936 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
                  have b43937 := hb (x 4 2)
                  have b43938 := hb (x 4 14)
                  clear * - r43936 b43937 b43938 d43930
                  omega
                have d43939 : (x 3 1).toNat = 0 := by
                  have r43940 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b43941 := hb (x 3 1)
                  have b43942 := hb (x 4 14)
                  clear * - r43940 b43941 b43942 d43935
                  omega
                have d43943 : (x 3 1 && x 3 11).toNat = 0 := by
                  have r43944 := hand1 (x 3 1) (x 3 11)
                  have b43945 := hb (x 3 1)
                  have b43946 := hb (x 3 1 && x 3 11)
                  clear * - r43944 b43945 b43946 d43939
                  omega
                have d43947 : (x 6 12).toNat = 0 := by
                  have r43948 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e43949 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                  have e43950 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                  have b43951 := hb (x 3 3)
                  have b43952 := hb (x 4 2)
                  have b43953 := hb (x 5 13)
                  have b43954 := hb (x 6 12)
                  clear * - r43948 e43949 e43950 b43951 b43952 b43953 b43954 d43930
                  omega
                have d43955 : (x 5 13).toNat = 0 := by
                  have r43956 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e43957 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                  have e43958 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                  have b43959 := hb (x 3 3)
                  have b43960 := hb (x 4 2)
                  have b43961 := hb (x 5 13)
                  have b43962 := hb (x 6 12)
                  clear * - r43956 e43957 e43958 b43959 b43960 b43961 b43962 d43947 d43930
                  omega
                have d43963 : (x 3 3).toNat = 0 := by
                  have r43964 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e43965 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                  have e43966 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                  have b43967 := hb (x 3 3)
                  have b43968 := hb (x 4 2)
                  have b43969 := hb (x 5 13)
                  have b43970 := hb (x 6 12)
                  clear * - r43964 e43965 e43966 b43967 b43968 b43969 b43970 d43947 d43955 d43930
                  omega
                have d43971 : (x 3 3 && x 3 8).toNat = 0 := by
                  have r43972 := hand1 (x 3 3) (x 3 8)
                  have b43973 := hb (x 3 3)
                  have b43974 := hb (x 3 3 && x 3 8)
                  clear * - r43972 b43973 b43974 d43963
                  omega
                have d43975 : (x 3 11).toNat = 0 := by
                  have r43976 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
                  have b43977 := hb (x 3 3)
                  have b43978 := hb (x 3 11)
                  clear * - r43976 b43977 b43978 d43963
                  omega
                have d43979 : (x 2 1 && x 2 12).toNat = 1 := by
                  have r43980 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b43981 := hb (x (-1) 4)
                  have b43982 := hb (x 3 11)
                  have b43983 := hb (x 2 1 && x 2 12)
                  have b43984 := hb (x 1 2 && x 1 13)
                  have b43985 := hb (x 0 3 && x 0 14)
                  clear * - r43980 b43981 b43982 b43983 b43984 b43985 d43975 g75 g76 g8
                  omega
                have d43986 : (x 2 12).toNat = 1 := by
                  have r43987 := hand2 (x 2 1) (x 2 12)
                  have b43988 := hb (x 2 12)
                  have b43989 := hb (x 2 1 && x 2 12)
                  clear * - r43987 b43988 b43989 d43979
                  omega
                have d43990 : (x (-1) 3).toNat = 0 := by
                  have r43991 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e43992 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
                  have e43993 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
                  have b43994 := hb (x (-1) 3)
                  have b43995 := hb (x 0 2)
                  have b43996 := hb (x 1 13)
                  have b43997 := hb (x 2 12)
                  clear * - r43991 e43992 e43993 b43994 b43995 b43996 b43997 d43986 f43740 g12
                  omega
                have d43998 : (x (-1) 11).toNat = 0 := by
                  have r43999 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
                  have b44000 := hb (x (-1) 3)
                  have b44001 := hb (x (-1) 11)
                  clear * - r43999 b44000 b44001 d43990
                  omega
                have d44002 : (x (-2) 4).toNat = 1 := by
                  have r44003 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := by have q := hcov11 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b44004 := hb (x (-2) 4)
                  have b44005 := hb (x 2 11)
                  have b44006 := hb (x 1 1 && x 1 12)
                  have b44007 := hb (x 0 2 && x 0 13)
                  have b44008 := hb (x (-1) 3 && x (-1) 14)
                  clear * - r44003 b44004 b44005 b44006 b44007 b44008 d43804 g72 g73 g74
                  omega
                have d44009 : (x 4 10).toNat = 1 := by
                  have r44010 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b44011 := hb (x (-1) 5)
                  have b44012 := hb (x 4 10)
                  have b44013 := hb (x 3 1 && x 3 11)
                  have b44014 := hb (x 2 2 && x 2 12)
                  have b44015 := hb (x 1 3 && x 1 13)
                  have b44016 := hb (x 0 4 && x 0 14)
                  clear * - r44010 b44011 b44012 b44013 b44014 b44015 b44016 d43943 d43747 d43725 g71 g9
                  omega
                have d44017 : (x 11 8).toNat = 0 := by
                  have r44018 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44019 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
                  have e44020 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
                  have e44021 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
                  have e44022 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
                  have e44023 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
                  have e44024 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
                  have b44025 := hb (x 4 7)
                  have b44026 := hb (x 5 6)
                  have b44027 := hb (x 6 5)
                  have b44028 := hb (x 7 4)
                  have b44029 := hb (x 8 11)
                  have b44030 := hb (x 9 10)
                  have b44031 := hb (x 10 9)
                  have b44032 := hb (x 11 8)
                  clear * - r44018 e44019 e44020 e44021 e44022 e44023 e44024 b44025 b44026 b44027 b44028 b44029 b44030 b44031 b44032 d43922 d43887 d43871 d43926 d43772
                  omega
                have d44033 : (x 10 9).toNat = 0 := by
                  have r44034 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44035 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
                  have e44036 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
                  have e44037 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
                  have e44038 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
                  have e44039 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
                  have e44040 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
                  have b44041 := hb (x 4 7)
                  have b44042 := hb (x 5 6)
                  have b44043 := hb (x 6 5)
                  have b44044 := hb (x 7 4)
                  have b44045 := hb (x 8 11)
                  have b44046 := hb (x 9 10)
                  have b44047 := hb (x 10 9)
                  have b44048 := hb (x 11 8)
                  clear * - r44034 e44035 e44036 e44037 e44038 e44039 e44040 b44041 b44042 b44043 b44044 b44045 b44046 b44047 b44048 d44017 d43922 d43887 d43871 d43926 d43772
                  omega
                have d44049 : (x 4 7).toNat = 0 := by
                  have r44050 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44051 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
                  have e44052 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
                  have e44053 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
                  have e44054 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
                  have e44055 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
                  have e44056 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
                  have b44057 := hb (x 4 7)
                  have b44058 := hb (x 5 6)
                  have b44059 := hb (x 6 5)
                  have b44060 := hb (x 7 4)
                  have b44061 := hb (x 8 11)
                  have b44062 := hb (x 9 10)
                  have b44063 := hb (x 10 9)
                  have b44064 := hb (x 11 8)
                  clear * - r44050 e44051 e44052 e44053 e44054 e44055 e44056 b44057 b44058 b44059 b44060 b44061 b44062 b44063 b44064 d44017 d44033 d43922 d43887 d43871 d43926 d43772
                  omega
                have d44065 : (x 4 2 && x 4 7).toNat = 0 := by
                  have r44066 := hand2 (x 4 2) (x 4 7)
                  have b44067 := hb (x 4 7)
                  have b44068 := hb (x 4 2 && x 4 7)
                  clear * - r44066 b44067 b44068 d44049
                  omega
                have d44069 : (x 6 8).toNat = 0 := by
                  have r44070 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44071 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                  have e44072 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                  have e44073 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                  have e44074 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                  have e44075 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                  have e44076 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                  have b44077 := hb (x (-1) 7)
                  have b44078 := hb (x 0 6)
                  have b44079 := hb (x 1 5)
                  have b44080 := hb (x 2 4)
                  have b44081 := hb (x 3 11)
                  have b44082 := hb (x 4 10)
                  have b44083 := hb (x 5 9)
                  have b44084 := hb (x 6 8)
                  clear * - r44070 e44071 e44072 e44073 e44074 e44075 e44076 b44077 b44078 b44079 b44080 b44081 b44082 b44083 b44084 d44009 d43975 f43734 f43722 f43736
                  omega
                have d44085 : (x 5 9).toNat = 0 := by
                  have r44086 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44087 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                  have e44088 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                  have e44089 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                  have e44090 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                  have e44091 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                  have e44092 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                  have b44093 := hb (x (-1) 7)
                  have b44094 := hb (x 0 6)
                  have b44095 := hb (x 1 5)
                  have b44096 := hb (x 2 4)
                  have b44097 := hb (x 3 11)
                  have b44098 := hb (x 4 10)
                  have b44099 := hb (x 5 9)
                  have b44100 := hb (x 6 8)
                  clear * - r44086 e44087 e44088 e44089 e44090 e44091 e44092 b44093 b44094 b44095 b44096 b44097 b44098 b44099 b44100 d44069 d44009 d43975 f43734 f43722 f43736
                  omega
                have d44101 : (x 2 4).toNat = 0 := by
                  have r44102 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44103 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                  have e44104 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                  have e44105 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                  have e44106 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                  have e44107 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                  have e44108 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                  have b44109 := hb (x (-1) 7)
                  have b44110 := hb (x 0 6)
                  have b44111 := hb (x 1 5)
                  have b44112 := hb (x 2 4)
                  have b44113 := hb (x 3 11)
                  have b44114 := hb (x 4 10)
                  have b44115 := hb (x 5 9)
                  have b44116 := hb (x 6 8)
                  clear * - r44102 e44103 e44104 e44105 e44106 e44107 e44108 b44109 b44110 b44111 b44112 b44113 b44114 b44115 b44116 d44069 d44085 d44009 d43975 f43734 f43722 f43736
                  omega
                have d44117 : (x 2 4 && x 2 9).toNat = 0 := by
                  have r44118 := hand1 (x 2 4) (x 2 9)
                  have b44119 := hb (x 2 4)
                  have b44120 := hb (x 2 4 && x 2 9)
                  clear * - r44118 b44119 b44120 d44101
                  omega
                have d44121 : (x 2 8).toNat = 0 := by
                  have r44122 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44123 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                  have e44124 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                  have e44125 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                  have e44126 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                  have e44127 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                  have e44128 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                  have b44129 := hb (x (-5) 7)
                  have b44130 := hb (x (-4) 6)
                  have b44131 := hb (x (-3) 5)
                  have b44132 := hb (x (-2) 4)
                  have b44133 := hb (x (-1) 11)
                  have b44134 := hb (x 0 10)
                  have b44135 := hb (x 1 9)
                  have b44136 := hb (x 2 8)
                  clear * - r44122 e44123 e44124 e44125 e44126 e44127 e44128 b44129 b44130 b44131 b44132 b44133 b44134 b44135 b44136 d43844 g17 d43998 d44002 g3
                  omega
                have d44137 : (x (-4) 6).toNat = 0 := by
                  have r44138 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44139 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                  have e44140 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                  have e44141 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                  have e44142 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                  have e44143 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                  have e44144 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                  have b44145 := hb (x (-5) 7)
                  have b44146 := hb (x (-4) 6)
                  have b44147 := hb (x (-3) 5)
                  have b44148 := hb (x (-2) 4)
                  have b44149 := hb (x (-1) 11)
                  have b44150 := hb (x 0 10)
                  have b44151 := hb (x 1 9)
                  have b44152 := hb (x 2 8)
                  clear * - r44138 e44139 e44140 e44141 e44142 e44143 e44144 b44145 b44146 b44147 b44148 b44149 b44150 b44151 b44152 d44121 d43844 g17 d43998 d44002 g3
                  omega
                have d44153 : (x (-4) 6 && x (-4) 12).toNat = 0 := by
                  have r44154 := hand1 (x (-4) 6) (x (-4) 12)
                  have b44155 := hb (x (-4) 6)
                  have b44156 := hb (x (-4) 6 && x (-4) 12)
                  clear * - r44154 b44155 b44156 d44137
                  omega
                have d44157 : (x (-5) 7).toNat = 0 := by
                  have r44158 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44159 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                  have e44160 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                  have e44161 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                  have e44162 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                  have e44163 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                  have e44164 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                  have b44165 := hb (x (-5) 7)
                  have b44166 := hb (x (-4) 6)
                  have b44167 := hb (x (-3) 5)
                  have b44168 := hb (x (-2) 4)
                  have b44169 := hb (x (-1) 11)
                  have b44170 := hb (x 0 10)
                  have b44171 := hb (x 1 9)
                  have b44172 := hb (x 2 8)
                  clear * - r44158 e44159 e44160 e44161 e44162 e44163 e44164 b44165 b44166 b44167 b44168 b44169 b44170 b44171 b44172 d44121 d43844 g17 d43998 d44002 g3 d44137
                  omega
                have d44173 : (x (-5) 7 && x (-5) 13).toNat = 0 := by
                  have r44174 := hand1 (x (-5) 7) (x (-5) 13)
                  have b44175 := hb (x (-5) 7)
                  have b44176 := hb (x (-5) 7 && x (-5) 13)
                  clear * - r44174 b44175 b44176 d44157
                  omega
                have d44177 : (x (-2) 8 && x (-2) 13).toNat = 1 := by
                  have r44178 : 1 ≤ (x 6 5).toNat + (x 5 1 && x 5 6).toNat + (x 4 2 && x 4 7).toNat + (x 3 3 && x 3 8).toNat + (x 2 4 && x 2 9).toNat + (x 1 5 && x 1 10).toNat + (x 0 6 && x 0 11).toNat + (x (-1) 7 && x (-1) 12).toNat + (x (-2) 8 && x (-2) 13).toNat + (x (-3) 9 && x (-3) 14).toNat + (x (-4) 10).toNat := by have q := hcov5 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b44179 := hb (x (-4) 10)
                  have b44180 := hb (x 6 5)
                  have b44181 := hb (x 5 1 && x 5 6)
                  have b44182 := hb (x 4 2 && x 4 7)
                  have b44183 := hb (x 3 3 && x 3 8)
                  have b44184 := hb (x 2 4 && x 2 9)
                  have b44185 := hb (x 1 5 && x 1 10)
                  have b44186 := hb (x 0 6 && x 0 11)
                  have b44187 := hb (x (-1) 7 && x (-1) 12)
                  have b44188 := hb (x (-2) 8 && x (-2) 13)
                  have b44189 := hb (x (-3) 9 && x (-3) 14)
                  clear * - r44178 b44179 b44180 b44181 b44182 b44183 b44184 b44185 b44186 b44187 b44188 b44189 d43926 d43776 d44065 d43971 d44117 g38 g39 g40 g41 g1
                  omega
                have d44190 : (x (-2) 8).toNat = 1 := by
                  have r44191 := hand1 (x (-2) 8) (x (-2) 13)
                  have b44192 := hb (x (-2) 8)
                  have b44193 := hb (x (-2) 8 && x (-2) 13)
                  clear * - r44191 b44192 b44193 d44177
                  omega
                have d44194 : (x (-6) 4).toNat = 0 := by
                  have r44195 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44196 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                  have e44197 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                  have e44198 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                  have e44199 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                  have e44200 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                  have e44201 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                  have b44202 := hb (x (-9) 7)
                  have b44203 := hb (x (-8) 6)
                  have b44204 := hb (x (-7) 5)
                  have b44205 := hb (x (-6) 4)
                  have b44206 := hb (x (-5) 11)
                  have b44207 := hb (x (-4) 10)
                  have b44208 := hb (x (-3) 9)
                  have b44209 := hb (x (-2) 8)
                  clear * - r44195 e44196 e44197 e44198 e44199 e44200 e44201 b44202 b44203 b44204 b44205 b44206 b44207 b44208 b44209 d44190 g4 g1 g0
                  omega
                have d44210 : (x (-6) 4 && x (-6) 14).toNat = 0 := by
                  have r44211 := hand1 (x (-6) 4) (x (-6) 14)
                  have b44212 := hb (x (-6) 4)
                  have b44213 := hb (x (-6) 4 && x (-6) 14)
                  clear * - r44211 b44212 b44213 d44194
                  omega
                have d44214 : (x (-7) 5).toNat = 1 := by
                  have r44215 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b44216 := hb (x (-7) 5)
                  have b44217 := hb (x (-2) 10)
                  have b44218 := hb (x (-3) 1 && x (-3) 11)
                  have b44219 := hb (x (-4) 2 && x (-4) 12)
                  have b44220 := hb (x (-5) 3 && x (-5) 13)
                  have b44221 := hb (x (-6) 4 && x (-6) 14)
                  clear * - r44215 b44216 b44217 b44218 b44219 b44220 b44221 g7 g68 g69 g70 d44210
                  omega
                have d44222 : (x (-7) 13).toNat = 1 := by
                  have r44223 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
                  have b44224 := hb (x (-7) 5)
                  have b44225 := hb (x (-7) 13)
                  clear * - r44223 b44224 b44225 d44214
                  omega
                have d44226 : (x (-7) 1).toNat = 1 := by
                  have r44227 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
                  have b44228 := hb (x (-7) 1)
                  have b44229 := hb (x (-7) 13)
                  clear * - r44227 b44228 b44229 d44222
                  omega
                have d44230 : (x (-6) 14).toNat = 0 := by
                  have r44231 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b44232 := hb (x (-7) 1)
                  have b44233 := hb (x (-6) 14)
                  clear * - r44231 b44232 b44233 d44226
                  omega
                have d44234 : (x (-6) 3 && x (-6) 14).toNat = 0 := by
                  have r44235 := hand2 (x (-6) 3) (x (-6) 14)
                  have b44236 := hb (x (-6) 14)
                  have b44237 := hb (x (-6) 3 && x (-6) 14)
                  clear * - r44235 b44236 b44237 d44230
                  omega
                have d44238 : (x (-6) 5 && x (-6) 14).toNat = 0 := by
                  have r44239 := hand2 (x (-6) 5) (x (-6) 14)
                  have b44240 := hb (x (-6) 14)
                  have b44241 := hb (x (-6) 5 && x (-6) 14)
                  clear * - r44239 b44240 b44241 d44230
                  omega
                have d44242 : (x (-6) 8 && x (-6) 14).toNat = 0 := by
                  have r44243 := hand2 (x (-6) 8) (x (-6) 14)
                  have b44244 := hb (x (-6) 14)
                  have b44245 := hb (x (-6) 8 && x (-6) 14)
                  clear * - r44243 b44244 b44245 d44230
                  omega
                have d44246 : (x (-7) 9).toNat = 1 := by
                  have r44247 : 1 ≤ (x 2 6).toNat + (x 1 1 && x 1 7).toNat + (x 0 2 && x 0 8).toNat + (x (-1) 3 && x (-1) 9).toNat + (x (-2) 4 && x (-2) 10).toNat + (x (-3) 5 && x (-3) 11).toNat + (x (-4) 6 && x (-4) 12).toNat + (x (-5) 7 && x (-5) 13).toNat + (x (-6) 8 && x (-6) 14).toNat + (x (-7) 9).toNat := by have q := hcov6 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b44248 := hb (x (-7) 9)
                  have b44249 := hb (x 2 6)
                  have b44250 := hb (x 1 1 && x 1 7)
                  have b44251 := hb (x 0 2 && x 0 8)
                  have b44252 := hb (x (-1) 3 && x (-1) 9)
                  have b44253 := hb (x (-2) 4 && x (-2) 10)
                  have b44254 := hb (x (-3) 5 && x (-3) 11)
                  have b44255 := hb (x (-4) 6 && x (-4) 12)
                  have b44256 := hb (x (-5) 7 && x (-5) 13)
                  have b44257 := hb (x (-6) 8 && x (-6) 14)
                  clear * - r44247 b44248 b44249 b44250 b44251 b44252 b44253 b44254 b44255 b44256 b44257 d43701 d43840 g48 g49 g50 g51 d44153 d44173 d44242
                  omega
                have d44258 : (x (-6) 8).toNat = 0 := by
                  have r44259 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44260 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
                  have e44261 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
                  have e44262 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
                  have e44263 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
                  have e44264 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
                  have e44265 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
                  have b44266 := hb (x (-13) 7)
                  have b44267 := hb (x (-12) 6)
                  have b44268 := hb (x (-11) 5)
                  have b44269 := hb (x (-10) 4)
                  have b44270 := hb (x (-9) 11)
                  have b44271 := hb (x (-8) 10)
                  have b44272 := hb (x (-7) 9)
                  have b44273 := hb (x (-6) 8)
                  clear * - r44259 e44260 e44261 e44262 e44263 e44264 e44265 b44266 b44267 b44268 b44269 b44270 b44271 b44272 b44273 d44246
                  omega
                have d44274 : (x (-8) 10).toNat = 0 := by
                  have r44275 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44276 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
                  have e44277 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
                  have e44278 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
                  have e44279 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
                  have e44280 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
                  have e44281 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
                  have b44282 := hb (x (-13) 7)
                  have b44283 := hb (x (-12) 6)
                  have b44284 := hb (x (-11) 5)
                  have b44285 := hb (x (-10) 4)
                  have b44286 := hb (x (-9) 11)
                  have b44287 := hb (x (-8) 10)
                  have b44288 := hb (x (-7) 9)
                  have b44289 := hb (x (-6) 8)
                  clear * - r44275 e44276 e44277 e44278 e44279 e44280 e44281 b44282 b44283 b44284 b44285 b44286 b44287 b44288 b44289 d44258 d44246
                  omega
                have d44290 : (x (-9) 11).toNat = 0 := by
                  have r44291 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44292 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
                  have e44293 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
                  have e44294 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
                  have e44295 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
                  have e44296 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
                  have e44297 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
                  have b44298 := hb (x (-13) 7)
                  have b44299 := hb (x (-12) 6)
                  have b44300 := hb (x (-11) 5)
                  have b44301 := hb (x (-10) 4)
                  have b44302 := hb (x (-9) 11)
                  have b44303 := hb (x (-8) 10)
                  have b44304 := hb (x (-7) 9)
                  have b44305 := hb (x (-6) 8)
                  clear * - r44291 e44292 e44293 e44294 e44295 e44296 e44297 b44298 b44299 b44300 b44301 b44302 b44303 b44304 b44305 d44258 d44246 d44274
                  omega
                have d44306 : (x (-10) 4).toNat = 0 := by
                  have r44307 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44308 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
                  have e44309 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
                  have e44310 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
                  have e44311 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
                  have e44312 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
                  have e44313 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
                  have b44314 := hb (x (-13) 7)
                  have b44315 := hb (x (-12) 6)
                  have b44316 := hb (x (-11) 5)
                  have b44317 := hb (x (-10) 4)
                  have b44318 := hb (x (-9) 11)
                  have b44319 := hb (x (-8) 10)
                  have b44320 := hb (x (-7) 9)
                  have b44321 := hb (x (-6) 8)
                  clear * - r44307 e44308 e44309 e44310 e44311 e44312 e44313 b44314 b44315 b44316 b44317 b44318 b44319 b44320 b44321 d44258 d44246 d44274 d44290
                  omega
                have d44322 : (x (-10) 4 && x (-10) 14).toNat = 0 := by
                  have r44323 := hand1 (x (-10) 4) (x (-10) 14)
                  have b44324 := hb (x (-10) 4)
                  have b44325 := hb (x (-10) 4 && x (-10) 14)
                  clear * - r44323 b44324 b44325 d44306
                  omega
                have d44326 : (x (-11) 5).toNat = 0 := by
                  have r44327 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44328 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
                  have e44329 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
                  have e44330 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
                  have e44331 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
                  have e44332 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
                  have e44333 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
                  have b44334 := hb (x (-13) 7)
                  have b44335 := hb (x (-12) 6)
                  have b44336 := hb (x (-11) 5)
                  have b44337 := hb (x (-10) 4)
                  have b44338 := hb (x (-9) 11)
                  have b44339 := hb (x (-8) 10)
                  have b44340 := hb (x (-7) 9)
                  have b44341 := hb (x (-6) 8)
                  clear * - r44327 e44328 e44329 e44330 e44331 e44332 e44333 b44334 b44335 b44336 b44337 b44338 b44339 b44340 b44341 d44258 d44246 d44274 d44290 d44306
                  omega
                have d44342 : (x (-6) 2).toNat = 0 := by
                  have r44343 : (x (-6) 2).toNat ≤ (x (-6) 14).toNat := himp _ _ (hp2 (-6))
                  have b44344 := hb (x (-6) 2)
                  have b44345 := hb (x (-6) 14)
                  clear * - r44343 b44344 b44345 d44230
                  omega
                have d44346 : (x (-6) 10).toNat = 0 := by
                  have r44347 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
                  have b44348 := hb (x (-6) 2)
                  have b44349 := hb (x (-6) 10)
                  clear * - r44347 b44348 b44349 d44342
                  omega
                have d44350 : (x (-6) 12).toNat = 0 := by
                  have r44351 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44352 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
                  have e44353 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
                  have b44354 := hb (x (-9) 3)
                  have b44355 := hb (x (-8) 2)
                  have b44356 := hb (x (-7) 13)
                  have b44357 := hb (x (-6) 12)
                  clear * - r44351 e44352 e44353 b44354 b44355 b44356 b44357 d44222
                  omega
                have d44358 : (x (-8) 2).toNat = 0 := by
                  have r44359 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44360 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
                  have e44361 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
                  have b44362 := hb (x (-9) 3)
                  have b44363 := hb (x (-8) 2)
                  have b44364 := hb (x (-7) 13)
                  have b44365 := hb (x (-6) 12)
                  clear * - r44359 e44360 e44361 b44362 b44363 b44364 b44365 d44350 d44222
                  omega
                have d44366 : (x (-8) 2 && x (-8) 12).toNat = 0 := by
                  have r44367 := hand1 (x (-8) 2) (x (-8) 12)
                  have b44368 := hb (x (-8) 2)
                  have b44369 := hb (x (-8) 2 && x (-8) 12)
                  clear * - r44367 b44368 b44369 d44358
                  omega
                have d44370 : (x (-9) 3).toNat = 0 := by
                  have r44371 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44372 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
                  have e44373 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
                  have b44374 := hb (x (-9) 3)
                  have b44375 := hb (x (-8) 2)
                  have b44376 := hb (x (-7) 13)
                  have b44377 := hb (x (-6) 12)
                  clear * - r44371 e44372 e44373 b44374 b44375 b44376 b44377 d44350 d44222 d44358
                  omega
                have d44378 : (x (-9) 3 && x (-9) 13).toNat = 0 := by
                  have r44379 := hand1 (x (-9) 3) (x (-9) 13)
                  have b44380 := hb (x (-9) 3)
                  have b44381 := hb (x (-9) 3 && x (-9) 13)
                  clear * - r44379 b44380 b44381 d44370
                  omega
                have d44382 : (x (-7) 1 && x (-7) 11).toNat = 1 := by
                  have r44383 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b44384 := hb (x (-11) 5)
                  have b44385 := hb (x (-6) 10)
                  have b44386 := hb (x (-7) 1 && x (-7) 11)
                  have b44387 := hb (x (-8) 2 && x (-8) 12)
                  have b44388 := hb (x (-9) 3 && x (-9) 13)
                  have b44389 := hb (x (-10) 4 && x (-10) 14)
                  clear * - r44383 b44384 b44385 b44386 b44387 b44388 b44389 d44346 d44366 d44378 d44322 d44326
                  omega
                have d44390 : (x (-7) 11).toNat = 1 := by
                  have r44391 := hand2 (x (-7) 1) (x (-7) 11)
                  have b44392 := hb (x (-7) 11)
                  have b44393 := hb (x (-7) 1 && x (-7) 11)
                  clear * - r44391 b44392 b44393 d44382
                  omega
                have d44394 : (x (-7) 3).toNat = 1 := by
                  have r44395 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
                  have b44396 := hb (x (-7) 3)
                  have b44397 := hb (x (-7) 11)
                  clear * - r44395 b44396 b44397 d44390
                  omega
                have d44398 : (x (-4) 12).toNat = 0 := by
                  have r44399 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44400 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                  have e44401 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                  have b44402 := hb (x (-7) 3)
                  have b44403 := hb (x (-6) 2)
                  have b44404 := hb (x (-5) 13)
                  have b44405 := hb (x (-4) 12)
                  clear * - r44399 e44400 e44401 b44402 b44403 b44404 b44405 d44342 d44394
                  omega
                have d44406 : (x (-4) 1 && x (-4) 12).toNat = 0 := by
                  have r44407 := hand2 (x (-4) 1) (x (-4) 12)
                  have b44408 := hb (x (-4) 12)
                  have b44409 := hb (x (-4) 1 && x (-4) 12)
                  clear * - r44407 b44408 b44409 d44398
                  omega
                have d44410 : (x (-5) 13).toNat = 0 := by
                  have r44411 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44412 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                  have e44413 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                  have b44414 := hb (x (-7) 3)
                  have b44415 := hb (x (-6) 2)
                  have b44416 := hb (x (-5) 13)
                  have b44417 := hb (x (-4) 12)
                  clear * - r44411 e44412 e44413 b44414 b44415 b44416 b44417 d44398 d44342 d44394
                  omega
                have d44418 : (x (-5) 2 && x (-5) 13).toNat = 0 := by
                  have r44419 := hand2 (x (-5) 2) (x (-5) 13)
                  have b44420 := hb (x (-5) 13)
                  have b44421 := hb (x (-5) 2 && x (-5) 13)
                  clear * - r44419 b44420 b44421 d44410
                  omega
                have d44422 : (x (-7) 4).toNat = 1 := by
                  have r44423 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := by have q := hcov11 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b44424 := hb (x (-7) 4)
                  have b44425 := hb (x (-3) 11)
                  have b44426 := hb (x (-4) 1 && x (-4) 12)
                  have b44427 := hb (x (-5) 2 && x (-5) 13)
                  have b44428 := hb (x (-6) 3 && x (-6) 14)
                  clear * - r44423 b44424 b44425 b44426 b44427 b44428 g6 d44406 d44418 d44234
                  omega
                have d44429 : (x (-7) 12).toNat = 1 := by
                  have r44430 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
                  have b44431 := hb (x (-7) 4)
                  have b44432 := hb (x (-7) 12)
                  clear * - r44430 b44431 b44432 d44422
                  omega
                have d44433 : (x (-8) 13).toNat = 0 := by
                  have r44434 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44435 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
                  have e44436 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
                  have b44437 := hb (x (-10) 3)
                  have b44438 := hb (x (-9) 2)
                  have b44439 := hb (x (-8) 13)
                  have b44440 := hb (x (-7) 12)
                  clear * - r44434 e44435 e44436 b44437 b44438 b44439 b44440 d44429
                  omega
                have d44441 : (x (-9) 2).toNat = 0 := by
                  have r44442 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44443 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
                  have e44444 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
                  have b44445 := hb (x (-10) 3)
                  have b44446 := hb (x (-9) 2)
                  have b44447 := hb (x (-8) 13)
                  have b44448 := hb (x (-7) 12)
                  clear * - r44442 e44443 e44444 b44445 b44446 b44447 b44448 d44429 d44433
                  omega
                have d44449 : (x (-9) 10).toNat = 0 := by
                  have r44450 : (x (-9) 10).toNat ≤ (x (-9) 2).toNat := himp _ _ (hp10 (-9))
                  have b44451 := hb (x (-9) 2)
                  have b44452 := hb (x (-9) 10)
                  clear * - r44450 b44451 b44452 d44441
                  omega
                have d44453 : (x (-9) 1 && x (-9) 10).toNat = 0 := by
                  have r44454 := hand2 (x (-9) 1) (x (-9) 10)
                  have b44455 := hb (x (-9) 10)
                  have b44456 := hb (x (-9) 1 && x (-9) 10)
                  clear * - r44454 b44455 b44456 d44449
                  omega
                have d44457 : (x (-10) 3).toNat = 0 := by
                  have r44458 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44459 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
                  have e44460 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
                  have b44461 := hb (x (-10) 3)
                  have b44462 := hb (x (-9) 2)
                  have b44463 := hb (x (-8) 13)
                  have b44464 := hb (x (-7) 12)
                  clear * - r44458 e44459 e44460 b44461 b44462 b44463 b44464 d44429 d44433 d44441
                  omega
                have d44465 : (x (-10) 11).toNat = 0 := by
                  have r44466 : (x (-10) 11).toNat ≤ (x (-10) 3).toNat := himp _ _ (hp11 (-10))
                  have b44467 := hb (x (-10) 3)
                  have b44468 := hb (x (-10) 11)
                  clear * - r44466 b44467 b44468 d44457
                  omega
                have d44469 : (x (-10) 2 && x (-10) 11).toNat = 0 := by
                  have r44470 := hand2 (x (-10) 2) (x (-10) 11)
                  have b44471 := hb (x (-10) 11)
                  have b44472 := hb (x (-10) 2 && x (-10) 11)
                  clear * - r44470 b44471 b44472 d44465
                  omega
                have d44473 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
                  have r44474 := hand2 (x (-5) 4) (x (-5) 13)
                  have b44475 := hb (x (-5) 13)
                  have b44476 := hb (x (-5) 4 && x (-5) 13)
                  clear * - r44474 b44475 b44476 d44410
                  omega
                have d44477 : (x (-7) 6).toNat = 1 := by
                  have r44478 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b44479 := hb (x (-7) 6)
                  have b44480 := hb (x (-1) 9)
                  have b44481 := hb (x (-2) 1 && x (-2) 10)
                  have b44482 := hb (x (-3) 2 && x (-3) 11)
                  have b44483 := hb (x (-4) 3 && x (-4) 12)
                  have b44484 := hb (x (-5) 4 && x (-5) 13)
                  have b44485 := hb (x (-6) 5 && x (-6) 14)
                  clear * - r44478 b44479 b44480 b44481 b44482 b44483 b44484 b44485 g11 g58 g59 g60 d44473 d44238
                  omega
                have d44486 : (x (-7) 14).toNat = 1 := by
                  have r44487 : (x (-7) 6).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp6 (-7))
                  have b44488 := hb (x (-7) 6)
                  have b44489 := hb (x (-7) 14)
                  clear * - r44487 b44488 b44489 d44477
                  omega
                have d44490 : (x (-8) 1).toNat = 0 := by
                  have r44491 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b44492 := hb (x (-8) 1)
                  have b44493 := hb (x (-7) 14)
                  clear * - r44491 b44492 b44493 d44486
                  omega
                have d44494 : (x (-8) 9).toNat = 0 := by
                  have r44495 : (x (-8) 9).toNat ≤ (x (-8) 1).toNat := himp _ _ (hp9 (-8))
                  have b44496 := hb (x (-8) 1)
                  have b44497 := hb (x (-8) 9)
                  clear * - r44495 b44496 b44497 d44490
                  omega
                have d44498 : (x (-2) 9).toNat = 0 := by
                  have r44499 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44500 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                  have e44501 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                  have e44502 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                  have e44503 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                  have e44504 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                  have e44505 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                  have b44506 := hb (x (-8) 7)
                  have b44507 := hb (x (-7) 6)
                  have b44508 := hb (x (-6) 5)
                  have b44509 := hb (x (-5) 4)
                  have b44510 := hb (x (-4) 11)
                  have b44511 := hb (x (-3) 10)
                  have b44512 := hb (x (-2) 9)
                  have b44513 := hb (x (-1) 8)
                  clear * - r44499 e44500 e44501 e44502 e44503 e44504 e44505 b44506 b44507 b44508 b44509 b44510 b44511 b44512 b44513 f43738 g5 g2 d44477
                  omega
                have d44514 : (x (-2) 2 && x (-2) 9).toNat = 0 := by
                  have r44515 := hand2 (x (-2) 2) (x (-2) 9)
                  have b44516 := hb (x (-2) 9)
                  have b44517 := hb (x (-2) 2 && x (-2) 9)
                  clear * - r44515 b44516 b44517 d44498
                  omega
                have d44518 : (x (-8) 8).toNat = 1 := by
                  have r44519 : 1 ≤ (x 0 7).toNat + (x (-1) 1 && x (-1) 8).toNat + (x (-2) 2 && x (-2) 9).toNat + (x (-3) 3 && x (-3) 10).toNat + (x (-4) 4 && x (-4) 11).toNat + (x (-5) 5 && x (-5) 12).toNat + (x (-6) 6 && x (-6) 13).toNat + (x (-7) 7 && x (-7) 14).toNat + (x (-8) 8).toNat := by have q := hcov7 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b44520 := hb (x (-8) 8)
                  have b44521 := hb (x 0 7)
                  have b44522 := hb (x (-1) 1 && x (-1) 8)
                  have b44523 := hb (x (-2) 2 && x (-2) 9)
                  have b44524 := hb (x (-3) 3 && x (-3) 10)
                  have b44525 := hb (x (-4) 4 && x (-4) 11)
                  have b44526 := hb (x (-5) 5 && x (-5) 12)
                  have b44527 := hb (x (-6) 6 && x (-6) 13)
                  have b44528 := hb (x (-7) 7 && x (-7) 14)
                  clear * - r44519 b44520 b44521 b44522 b44523 b44524 b44525 b44526 b44527 b44528 g15 g52 d44514 g53 g54 g55 g56 g57
                  omega
                have d44529 : (x (-9) 9).toNat = 0 := by
                  have r44530 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44531 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
                  have e44532 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
                  have e44533 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
                  have e44534 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
                  have e44535 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
                  have e44536 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
                  have b44537 := hb (x (-15) 7)
                  have b44538 := hb (x (-14) 6)
                  have b44539 := hb (x (-13) 5)
                  have b44540 := hb (x (-12) 4)
                  have b44541 := hb (x (-11) 11)
                  have b44542 := hb (x (-10) 10)
                  have b44543 := hb (x (-9) 9)
                  have b44544 := hb (x (-8) 8)
                  clear * - r44530 e44531 e44532 e44533 e44534 e44535 e44536 b44537 b44538 b44539 b44540 b44541 b44542 b44543 b44544 d44518
                  omega
                have d44545 : (x (-10) 10).toNat = 0 := by
                  have r44546 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44547 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
                  have e44548 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
                  have e44549 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
                  have e44550 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
                  have e44551 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
                  have e44552 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
                  have b44553 := hb (x (-15) 7)
                  have b44554 := hb (x (-14) 6)
                  have b44555 := hb (x (-13) 5)
                  have b44556 := hb (x (-12) 4)
                  have b44557 := hb (x (-11) 11)
                  have b44558 := hb (x (-10) 10)
                  have b44559 := hb (x (-9) 9)
                  have b44560 := hb (x (-8) 8)
                  clear * - r44546 e44547 e44548 e44549 e44550 e44551 e44552 b44553 b44554 b44555 b44556 b44557 b44558 b44559 b44560 d44518 d44529
                  omega
                have d44561 : (x (-11) 11).toNat = 0 := by
                  have r44562 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44563 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
                  have e44564 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
                  have e44565 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
                  have e44566 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
                  have e44567 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
                  have e44568 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
                  have b44569 := hb (x (-15) 7)
                  have b44570 := hb (x (-14) 6)
                  have b44571 := hb (x (-13) 5)
                  have b44572 := hb (x (-12) 4)
                  have b44573 := hb (x (-11) 11)
                  have b44574 := hb (x (-10) 10)
                  have b44575 := hb (x (-9) 9)
                  have b44576 := hb (x (-8) 8)
                  clear * - r44562 e44563 e44564 e44565 e44566 e44567 e44568 b44569 b44570 b44571 b44572 b44573 b44574 b44575 b44576 d44518 d44529 d44545
                  omega
                have d44577 : (x (-12) 4).toNat = 0 := by
                  have r44578 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44579 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
                  have e44580 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
                  have e44581 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
                  have e44582 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
                  have e44583 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
                  have e44584 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
                  have b44585 := hb (x (-15) 7)
                  have b44586 := hb (x (-14) 6)
                  have b44587 := hb (x (-13) 5)
                  have b44588 := hb (x (-12) 4)
                  have b44589 := hb (x (-11) 11)
                  have b44590 := hb (x (-10) 10)
                  have b44591 := hb (x (-9) 9)
                  have b44592 := hb (x (-8) 8)
                  clear * - r44578 e44579 e44580 e44581 e44582 e44583 e44584 b44585 b44586 b44587 b44588 b44589 b44590 b44591 b44592 d44518 d44529 d44545 d44561
                  omega
                have d44593 : (x (-12) 4 && x (-12) 13).toNat = 0 := by
                  have r44594 := hand1 (x (-12) 4) (x (-12) 13)
                  have b44595 := hb (x (-12) 4)
                  have b44596 := hb (x (-12) 4 && x (-12) 13)
                  clear * - r44594 b44595 b44596 d44577
                  omega
                have d44597 : (x (-13) 5).toNat = 0 := by
                  have r44598 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44599 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
                  have e44600 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
                  have e44601 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
                  have e44602 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
                  have e44603 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
                  have e44604 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
                  have b44605 := hb (x (-15) 7)
                  have b44606 := hb (x (-14) 6)
                  have b44607 := hb (x (-13) 5)
                  have b44608 := hb (x (-12) 4)
                  have b44609 := hb (x (-11) 11)
                  have b44610 := hb (x (-10) 10)
                  have b44611 := hb (x (-9) 9)
                  have b44612 := hb (x (-8) 8)
                  clear * - r44598 e44599 e44600 e44601 e44602 e44603 e44604 b44605 b44606 b44607 b44608 b44609 b44610 b44611 b44612 d44518 d44529 d44545 d44561 d44577
                  omega
                have d44613 : (x (-13) 5 && x (-13) 14).toNat = 0 := by
                  have r44614 := hand1 (x (-13) 5) (x (-13) 14)
                  have b44615 := hb (x (-13) 5)
                  have b44616 := hb (x (-13) 5 && x (-13) 14)
                  clear * - r44614 b44615 b44616 d44597
                  omega
                have d44617 : (x (-14) 6).toNat = 0 := by
                  have r44618 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44619 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
                  have e44620 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
                  have e44621 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
                  have e44622 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
                  have e44623 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
                  have e44624 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
                  have b44625 := hb (x (-15) 7)
                  have b44626 := hb (x (-14) 6)
                  have b44627 := hb (x (-13) 5)
                  have b44628 := hb (x (-12) 4)
                  have b44629 := hb (x (-11) 11)
                  have b44630 := hb (x (-10) 10)
                  have b44631 := hb (x (-9) 9)
                  have b44632 := hb (x (-8) 8)
                  clear * - r44618 e44619 e44620 e44621 e44622 e44623 e44624 b44625 b44626 b44627 b44628 b44629 b44630 b44631 b44632 d44518 d44529 d44545 d44561 d44577 d44597
                  omega
                have d44633 : (x (-11) 3 && x (-11) 12).toNat = 1 := by
                  have r44634 : 1 ≤ (x (-8) 9).toNat + (x (-9) 1 && x (-9) 10).toNat + (x (-10) 2 && x (-10) 11).toNat + (x (-11) 3 && x (-11) 12).toNat + (x (-12) 4 && x (-12) 13).toNat + (x (-13) 5 && x (-13) 14).toNat + (x (-14) 6).toNat := by have q := hcov9 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b44635 := hb (x (-14) 6)
                  have b44636 := hb (x (-8) 9)
                  have b44637 := hb (x (-9) 1 && x (-9) 10)
                  have b44638 := hb (x (-10) 2 && x (-10) 11)
                  have b44639 := hb (x (-11) 3 && x (-11) 12)
                  have b44640 := hb (x (-12) 4 && x (-12) 13)
                  have b44641 := hb (x (-13) 5 && x (-13) 14)
                  clear * - r44634 b44635 b44636 b44637 b44638 b44639 b44640 b44641 d44494 d44453 d44469 d44593 d44613 d44617
                  omega
                have d44642 : (x (-11) 3).toNat = 1 := by
                  have r44643 := hand1 (x (-11) 3) (x (-11) 12)
                  have b44644 := hb (x (-11) 3)
                  have b44645 := hb (x (-11) 3 && x (-11) 12)
                  clear * - r44643 b44644 b44645 d44633
                  omega
                have d44646 : (x (-8) 12).toNat = 0 := by
                  have r44647 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44648 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
                  have e44649 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
                  have b44650 := hb (x (-11) 3)
                  have b44651 := hb (x (-10) 2)
                  have b44652 := hb (x (-9) 13)
                  have b44653 := hb (x (-8) 12)
                  clear * - r44647 e44648 e44649 b44650 b44651 b44652 b44653 d44642
                  omega
                have d44654 : (x (-9) 13).toNat = 0 := by
                  have r44655 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44656 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
                  have e44657 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
                  have b44658 := hb (x (-11) 3)
                  have b44659 := hb (x (-10) 2)
                  have b44660 := hb (x (-9) 13)
                  have b44661 := hb (x (-8) 12)
                  clear * - r44655 e44656 e44657 b44658 b44659 b44660 b44661 d44646 d44642
                  omega
                have d44662 : (x (-10) 2).toNat = 0 := by
                  have r44663 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44664 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
                  have e44665 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
                  have b44666 := hb (x (-11) 3)
                  have b44667 := hb (x (-10) 2)
                  have b44668 := hb (x (-9) 13)
                  have b44669 := hb (x (-8) 12)
                  clear * - r44663 e44664 e44665 b44666 b44667 b44668 b44669 d44646 d44654 d44642
                  omega
                have d44670 : (x (-9) 1 && x (-9) 14).toNat = 1 := by
                  have r44671 : 1 ≤ (x (-8) 13).toNat + (x (-9) 1 && x (-9) 14).toNat + (x (-10) 2).toNat := by have q := hcov13 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b44672 := hb (x (-10) 2)
                  have b44673 := hb (x (-8) 13)
                  have b44674 := hb (x (-9) 1 && x (-9) 14)
                  clear * - r44671 b44672 b44673 b44674 d44433 d44662
                  omega
                have d44675 : (x (-9) 1).toNat = 1 := by
                  have r44676 := hand1 (x (-9) 1) (x (-9) 14)
                  have b44677 := hb (x (-9) 1)
                  have b44678 := hb (x (-9) 1 && x (-9) 14)
                  clear * - r44676 b44677 b44678 d44670
                  omega
                have d44679 : (x (-8) 14).toNat = 0 := by
                  have r44680 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b44681 := hb (x (-9) 1)
                  have b44682 := hb (x (-8) 14)
                  clear * - r44680 b44681 b44682 d44675
                  omega
                have d44683 : (x (-8) 6).toNat = 0 := by
                  have r44684 : (x (-8) 6).toNat ≤ (x (-8) 14).toNat := himp _ _ (hp6 (-8))
                  have b44685 := hb (x (-8) 6)
                  have b44686 := hb (x (-8) 14)
                  clear * - r44684 b44685 b44686 d44679
                  omega
                have r44687 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e44688 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                have e44689 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                have e44690 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                have e44691 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                have e44692 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                have e44693 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                have b44694 := hb (x (-9) 7)
                have b44695 := hb (x (-8) 6)
                have b44696 := hb (x (-7) 5)
                have b44697 := hb (x (-6) 4)
                have b44698 := hb (x (-5) 11)
                have b44699 := hb (x (-4) 10)
                have b44700 := hb (x (-3) 9)
                have b44701 := hb (x (-2) 8)
                linarith only [r44687, e44688, e44689, e44690, e44691, e44692, e44693, b44694, b44695, b44696, b44697, b44698, b44699, b44700, b44701, d44190, g4, g1, g0, d44194, d44214, d44683]
              · have f44702 : (x 2 2).toNat = 1 := by rw [h43741]; rfl
                have d44703 : (x 4 12).toNat = 0 := by
                  have r44704 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44705 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                  have e44706 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                  have b44707 := hb (x 1 3)
                  have b44708 := hb (x 2 2)
                  have b44709 := hb (x 3 13)
                  have b44710 := hb (x 4 12)
                  clear * - r44704 e44705 e44706 b44707 b44708 b44709 b44710 f44702 f43724
                  omega
                have d44711 : (x 4 1 && x 4 12).toNat = 0 := by
                  have r44712 := hand2 (x 4 1) (x 4 12)
                  have b44713 := hb (x 4 12)
                  have b44714 := hb (x 4 1 && x 4 12)
                  clear * - r44712 b44713 b44714 d44703
                  omega
                have d44715 : (x 4 2 && x 4 12).toNat = 0 := by
                  have r44716 := hand2 (x 4 2) (x 4 12)
                  have b44717 := hb (x 4 12)
                  have b44718 := hb (x 4 2 && x 4 12)
                  clear * - r44716 b44717 b44718 d44703
                  omega
                have d44719 : (x 4 12 && x 4 14).toNat = 0 := by
                  have r44720 := hand1 (x 4 12) (x 4 14)
                  have b44721 := hb (x 4 12)
                  have b44722 := hb (x 4 12 && x 4 14)
                  clear * - r44720 b44721 b44722 d44703
                  omega
                have d44723 : (x 3 13).toNat = 0 := by
                  have r44724 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44725 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                  have e44726 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                  have b44727 := hb (x 1 3)
                  have b44728 := hb (x 2 2)
                  have b44729 := hb (x 3 13)
                  have b44730 := hb (x 4 12)
                  clear * - r44724 e44725 e44726 b44727 b44728 b44729 b44730 d44703 f44702 f43724
                  omega
                have d44731 : (x 3 3 && x 3 13).toNat = 0 := by
                  have r44732 := hand2 (x 3 3) (x 3 13)
                  have b44733 := hb (x 3 13)
                  have b44734 := hb (x 3 3 && x 3 13)
                  clear * - r44732 b44733 b44734 d44723
                  omega
                have d44735 : (x 2 3 && x 2 14).toNat = 1 := by
                  have r44736 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b44737 := hb (x 1 4)
                  have b44738 := hb (x 5 11)
                  have b44739 := hb (x 4 1 && x 4 12)
                  have b44740 := hb (x 3 2 && x 3 13)
                  have b44741 := hb (x 2 3 && x 2 14)
                  clear * - r44736 b44737 b44738 b44739 b44740 b44741 d43633 d44711 g79 g19
                  omega
                have d44742 : (x 2 3).toNat = 1 := by
                  have r44743 := hand1 (x 2 3) (x 2 14)
                  have b44744 := hb (x 2 3)
                  have b44745 := hb (x 2 3 && x 2 14)
                  clear * - r44743 b44744 b44745 d44735
                  omega
                have d44746 : (x 5 12).toNat = 0 := by
                  have r44747 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44748 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                  have e44749 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                  have b44750 := hb (x 2 3)
                  have b44751 := hb (x 3 2)
                  have b44752 := hb (x 4 13)
                  have b44753 := hb (x 5 12)
                  clear * - r44747 e44748 e44749 b44750 b44751 b44752 b44753 g22 d44742
                  omega
                have d44754 : (x 5 3 && x 5 12).toNat = 0 := by
                  have r44755 := hand2 (x 5 3) (x 5 12)
                  have b44756 := hb (x 5 12)
                  have b44757 := hb (x 5 3 && x 5 12)
                  clear * - r44755 b44756 b44757 d44746
                  omega
                have d44758 : (x 5 4).toNat = 0 := by
                  have r44759 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
                  have b44760 := hb (x 5 4)
                  have b44761 := hb (x 5 12)
                  clear * - r44759 b44760 b44761 d44746
                  omega
                have d44762 : (x 4 13).toNat = 0 := by
                  have r44763 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44764 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                  have e44765 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                  have b44766 := hb (x 2 3)
                  have b44767 := hb (x 3 2)
                  have b44768 := hb (x 4 13)
                  have b44769 := hb (x 5 12)
                  clear * - r44763 e44764 e44765 b44766 b44767 b44768 b44769 d44746 g22 d44742
                  omega
                have d44770 : (x 4 5).toNat = 0 := by
                  have r44771 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
                  have b44772 := hb (x 4 5)
                  have b44773 := hb (x 4 13)
                  clear * - r44771 b44772 b44773 d44762
                  omega
                have d44774 : (x 2 4 && x 2 14).toNat = 1 := by
                  have r44775 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b44776 := hb (x 1 5)
                  have b44777 := hb (x 6 10)
                  have b44778 := hb (x 5 1 && x 5 11)
                  have b44779 := hb (x 4 2 && x 4 12)
                  have b44780 := hb (x 3 3 && x 3 13)
                  have b44781 := hb (x 2 4 && x 2 14)
                  clear * - r44775 b44776 b44777 b44778 b44779 b44780 b44781 d43609 d43649 d44715 d44731 f43734
                  omega
                have d44782 : (x 2 4).toNat = 1 := by
                  have r44783 := hand1 (x 2 4) (x 2 14)
                  have b44784 := hb (x 2 4)
                  have b44785 := hb (x 2 4 && x 2 14)
                  clear * - r44783 b44784 b44785 d44774
                  omega
                have r44786 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r44787 : (x 4 1).toNat + (x 3 2).toNat + (x 2 3).toNat + (x 1 4).toNat + (x 0 5).toNat + (x (-1) 6).toNat + (x (-2) 7).toNat + (x (-3) 8).toNat + (x (-4) 9).toNat + (x (-5) 10).toNat + (x (-6) 11).toNat + (x (-7) 12).toNat + (x (-8) 13).toNat + (x (-9) 14).toNat = 3 := by have q := hcount 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r44788 : (x 5 1).toNat + (x 4 2).toNat + (x 3 3).toNat + (x 2 4).toNat + (x 1 5).toNat + (x 0 6).toNat + (x (-1) 7).toNat + (x (-2) 8).toNat + (x (-3) 9).toNat + (x (-4) 10).toNat + (x (-5) 11).toNat + (x (-6) 12).toNat + (x (-7) 13).toNat + (x (-8) 14).toNat = 3 := by have q := hcount 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r44789 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r44790 : (x 17 1).toNat + (x 16 2).toNat + (x 15 3).toNat + (x 14 4).toNat + (x 13 5).toNat + (x 12 6).toNat + (x 11 7).toNat + (x 10 8).toNat + (x 9 9).toNat + (x 8 10).toNat + (x 7 11).toNat + (x 6 12).toNat + (x 5 13).toNat + (x 4 14).toNat = 3 := by have q := hcount 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r44791 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e44792 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
                have e44793 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
                have e44794 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
                have e44795 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
                have e44796 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
                have e44797 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
                have r44798 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e44799 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e44800 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e44801 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e44802 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e44803 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e44804 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have r44805 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e44806 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                have e44807 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                have e44808 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                have e44809 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                have e44810 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                have e44811 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                have r44812 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e44813 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                have e44814 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                have r44815 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r44816 : 1 ≤ (x 16 2).toNat + (x 15 1 && x 15 3).toNat + (x 14 2 && x 14 4).toNat + (x 13 3 && x 13 5).toNat + (x 12 4 && x 12 6).toNat + (x 11 5 && x 11 7).toNat + (x 10 6 && x 10 8).toNat + (x 9 7 && x 9 9).toNat + (x 8 8 && x 8 10).toNat + (x 7 9 && x 7 11).toNat + (x 6 10 && x 6 12).toNat + (x 5 11 && x 5 13).toNat + (x 4 12 && x 4 14).toNat + (x 3 13).toNat := by have q := hcov2 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r44817 : 1 ≤ (x 0 4).toNat + (x (-1) 1 && x (-1) 5).toNat + (x (-2) 2 && x (-2) 6).toNat + (x (-3) 3 && x (-3) 7).toNat + (x (-4) 4 && x (-4) 8).toNat + (x (-5) 5 && x (-5) 9).toNat + (x (-6) 6 && x (-6) 10).toNat + (x (-7) 7 && x (-7) 11).toNat + (x (-8) 8 && x (-8) 12).toNat + (x (-9) 9 && x (-9) 13).toNat + (x (-10) 10 && x (-10) 14).toNat + (x (-11) 11).toNat := by have q := hcov4 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e44818 : (x (-1) 1 && x (-1) 5).toNat = (x (-1) 5).toNat := handr _ _ (fun h => hp13 (-1) (hp5 (-1) (h)))
                have e44819 : (x (-10) 10 && x (-10) 14).toNat = (x (-10) 10).toNat := handl _ _ (fun h => hp2 (-10) (hp10 (-10) (h)))
                have r44820 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e44821 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
                have e44822 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
                have r44823 : 1 ≤ (x 5 4).toNat + (x 4 1 && x 4 5).toNat + (x 3 2 && x 3 6).toNat + (x 2 3 && x 2 7).toNat + (x 1 4 && x 1 8).toNat + (x 0 5 && x 0 9).toNat + (x (-1) 6 && x (-1) 10).toNat + (x (-2) 7 && x (-2) 11).toNat + (x (-3) 8 && x (-3) 12).toNat + (x (-4) 9 && x (-4) 13).toNat + (x (-5) 10 && x (-5) 14).toNat + (x (-6) 11).toNat := by have q := hcov4 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e44824 : (x 4 1 && x 4 5).toNat = (x 4 5).toNat := handr _ _ (fun h => hp13 4 (hp5 4 (h)))
                have e44825 : (x (-5) 10 && x (-5) 14).toNat = (x (-5) 10).toNat := handl _ _ (fun h => hp2 (-5) (hp10 (-5) (h)))
                have r44826 : 1 ≤ (x 0 6).toNat + (x (-1) 1 && x (-1) 7).toNat + (x (-2) 2 && x (-2) 8).toNat + (x (-3) 3 && x (-3) 9).toNat + (x (-4) 4 && x (-4) 10).toNat + (x (-5) 5 && x (-5) 11).toNat + (x (-6) 6 && x (-6) 12).toNat + (x (-7) 7 && x (-7) 13).toNat + (x (-8) 8 && x (-8) 14).toNat + (x (-9) 9).toNat := by have q := hcov6 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r44827 : 1 ≤ (x 0 7).toNat + (x (-1) 1 && x (-1) 8).toNat + (x (-2) 2 && x (-2) 9).toNat + (x (-3) 3 && x (-3) 10).toNat + (x (-4) 4 && x (-4) 11).toNat + (x (-5) 5 && x (-5) 12).toNat + (x (-6) 6 && x (-6) 13).toNat + (x (-7) 7 && x (-7) 14).toNat + (x (-8) 8).toNat := by have q := hcov7 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r44828 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r44829 : 1 ≤ (x 8 9).toNat + (x 7 1 && x 7 10).toNat + (x 6 2 && x 6 11).toNat + (x 5 3 && x 5 12).toNat + (x 4 4 && x 4 13).toNat + (x 3 5 && x 3 14).toNat + (x 2 6).toNat := by have q := hcov9 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r44830 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r44831 : 1 ≤ (x 8 10).toNat + (x 7 1 && x 7 11).toNat + (x 6 2 && x 6 12).toNat + (x 5 3 && x 5 13).toNat + (x 4 4 && x 4 14).toNat + (x 3 5).toNat := by have q := hcov10 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r44832 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := by have q := hcov11 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r44833 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r44834 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
                have r44835 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
                have r44836 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
                have r44837 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
                have r44838 := hand2 (x 15 1) (x 15 3)
                have r44839 := hand2 (x 14 2) (x 14 4)
                have r44840 := hand2 (x 13 3) (x 13 5)
                have r44841 := hand2 (x 12 4) (x 12 6)
                have r44842 := hand2 (x 11 5) (x 11 7)
                have r44843 := hand2 (x 10 6) (x 10 8)
                have r44844 := hand2 (x 9 7) (x 9 9)
                have r44845 := hand2 (x (-2) 2) (x (-2) 6)
                have r44846 := hand2 (x (-8) 8) (x (-8) 12)
                have r44847 := hand2 (x (-9) 9) (x (-9) 13)
                have r44848 := hand1 (x (-4) 8) (x (-4) 12)
                have r44849 := hand1 (x (-5) 9) (x (-5) 13)
                have r44850 := hand2 (x 2 3) (x 2 7)
                have r44851 := hand1 (x (-2) 7) (x (-2) 11)
                have r44852 := hand1 (x (-3) 8) (x (-3) 12)
                have r44853 := hand1 (x (-4) 9) (x (-4) 13)
                have r44854 := hand2 (x (-2) 2) (x (-2) 8)
                have r44855 := hand2 (x (-8) 8) (x (-8) 14)
                have r44856 := hand2 (x (-2) 2) (x (-2) 9)
                have r44857 := hand1 (x (-5) 4) (x (-5) 13)
                have r44858 := hand1 (x (-6) 5) (x (-6) 14)
                have r44859 := hand2 (x 7 1) (x 7 10)
                have r44860 := hand2 (x 6 2) (x 6 11)
                have r44861 := hand1 (x (-6) 4) (x (-6) 14)
                have r44862 := hand1 (x 7 1) (x 7 11)
                have r44863 := hand1 (x 6 2) (x 6 12)
                have r44864 := hand1 (x 5 3) (x 5 13)
                have r44865 := hand2 (x (-4) 1) (x (-4) 12)
                have r44866 := hand2 (x (-5) 2) (x (-5) 13)
                have r44867 := hand2 (x (-6) 3) (x (-6) 14)
                have r44868 := hand1 (x 4 1) (x 4 14)
                linarith only [r44786, r44787, r44788, r44789, r44790, r44791, e44792, e44793, e44794, e44795, e44796, e44797, r44798, e44799, e44800, e44801, e44802, e44803, e44804, r44805, e44806, e44807, e44808, e44809, e44810, e44811, r44812, e44813, e44814, r44815, r44816, r44817, e44818, e44819, r44820, e44821, e44822, r44823, e44824, e44825, r44826, r44827, r44828, r44829, r44830, r44831, r44832, r44833, r44834, r44835, r44836, r44837, r44838, r44839, r44840, r44841, r44842, r44843, r44844, r44845, r44846, r44847, r44848, r44849, r44850, r44851, r44852, r44853, r44854, r44855, r44856, r44857, r44858, r44859, r44860, r44861, r44862, r44863, r44864, r44865, r44866, r44867, r44868, g0, g1, g2, g4, g5, g6, g7, g9, g10, f43736, f43738, g11, g13, g14, f43722, g15, g16, f43724, g19, f43734, g21, f44702, d44742, d44782, d43701, g22, d43685, g24, d44723, d43661, d44770, d44758, d43585, d43605, d43629, d43657, d44719, g25, g26, g27, g28, g29, d43717, d43729, g30, g31, g32, g33, g34, g35, g36, g37, g42, g43, g44, g45, g46, g47, g52, g53, g54, g55, g56, g57, g58, g59, g60, d44754, d43681, g67, g68, g69, g70, d43677]
            · have f45041 : (x 1 13).toNat = 1 := by rw [h43739]; rfl
              have d45042 : (x 1 1).toNat = 1 := by
                have r45043 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
                have b45044 := hb (x 1 1)
                have b45045 := hb (x 1 13)
                clear * - r45043 b45044 b45045 f45041
                omega
              have d45046 : (x 2 14).toNat = 0 := by
                have r45047 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45048 := hb (x 1 1)
                have b45049 := hb (x 2 14)
                clear * - r45047 b45048 b45049 d45042
                omega
              have d45050 : (x 2 1 && x 2 14).toNat = 0 := by
                have r45051 := hand2 (x 2 1) (x 2 14)
                have b45052 := hb (x 2 14)
                have b45053 := hb (x 2 1 && x 2 14)
                clear * - r45051 b45052 b45053 d45046
                omega
              have d45054 : (x 2 2).toNat = 0 := by
                have r45055 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
                have b45056 := hb (x 2 2)
                have b45057 := hb (x 2 14)
                clear * - r45055 b45056 b45057 d45046
                omega
              have d45058 : (x 4 13).toNat = 1 := by
                have r45059 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45060 := hb (x 2 2)
                have b45061 := hb (x 4 13)
                have b45062 := hb (x 3 1 && x 3 14)
                clear * - r45059 b45060 b45061 b45062 g80 d45054
                omega
              have d45063 : (x 4 1).toNat = 1 := by
                have r45064 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
                have b45065 := hb (x 4 1)
                have b45066 := hb (x 4 13)
                clear * - r45064 b45065 b45066 d45058
                omega
              have d45067 : (x 5 14).toNat = 0 := by
                have r45068 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45069 := hb (x 4 1)
                have b45070 := hb (x 5 14)
                clear * - r45068 b45069 b45070 d45063
                omega
              have d45071 : (x 5 1 && x 5 14).toNat = 0 := by
                have r45072 := hand2 (x 5 1) (x 5 14)
                have b45073 := hb (x 5 14)
                have b45074 := hb (x 5 1 && x 5 14)
                clear * - r45072 b45073 b45074 d45067
                omega
              have d45075 : (x 5 2).toNat = 0 := by
                have r45076 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
                have b45077 := hb (x 5 2)
                have b45078 := hb (x 5 14)
                clear * - r45076 b45077 b45078 d45067
                omega
              have d45079 : (x 3 13).toNat = 1 := by
                have r45080 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45081 := hb (x 1 2)
                have b45082 := hb (x 3 13)
                have b45083 := hb (x 2 1 && x 2 14)
                clear * - r45080 b45081 b45082 b45083 d45050 g18
                omega
              have d45084 : (x 3 1).toNat = 1 := by
                have r45085 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
                have b45086 := hb (x 3 1)
                have b45087 := hb (x 3 13)
                clear * - r45085 b45086 b45087 d45079
                omega
              have d45088 : (x 4 14).toNat = 0 := by
                have r45089 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45090 := hb (x 3 1)
                have b45091 := hb (x 4 14)
                clear * - r45089 b45090 b45091 d45084
                omega
              have d45092 : (x 4 1 && x 4 14).toNat = 0 := by
                have r45093 := hand2 (x 4 1) (x 4 14)
                have b45094 := hb (x 4 14)
                have b45095 := hb (x 4 1 && x 4 14)
                clear * - r45093 b45094 b45095 d45088
                omega
              have d45096 : (x 5 13).toNat = 1 := by
                have r45097 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45098 := hb (x 3 2)
                have b45099 := hb (x 5 13)
                have b45100 := hb (x 4 1 && x 4 14)
                clear * - r45097 b45098 b45099 b45100 d45092 g22
                omega
              have d45101 : (x 5 1).toNat = 1 := by
                have r45102 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
                have b45103 := hb (x 5 1)
                have b45104 := hb (x 5 13)
                clear * - r45102 b45103 b45104 d45096
                omega
              have d45105 : (x 6 14).toNat = 0 := by
                have r45106 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45107 := hb (x 5 1)
                have b45108 := hb (x 6 14)
                clear * - r45106 b45107 b45108 d45101
                omega
              have d45109 : (x 6 1 && x 6 14).toNat = 0 := by
                have r45110 := hand2 (x 6 1) (x 6 14)
                have b45111 := hb (x 6 14)
                have b45112 := hb (x 6 1 && x 6 14)
                clear * - r45110 b45111 b45112 d45105
                omega
              have d45113 : (x 7 13).toNat = 1 := by
                have r45114 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45115 := hb (x 5 2)
                have b45116 := hb (x 7 13)
                have b45117 := hb (x 6 1 && x 6 14)
                clear * - r45114 b45115 b45116 b45117 d45109 d45075
                omega
              have d45118 : (x 7 1).toNat = 1 := by
                have r45119 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
                have b45120 := hb (x 7 1)
                have b45121 := hb (x 7 13)
                clear * - r45119 b45120 b45121 d45113
                omega
              have d45122 : (x 8 14).toNat = 0 := by
                have r45123 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45124 := hb (x 7 1)
                have b45125 := hb (x 8 14)
                clear * - r45123 b45124 b45125 d45118
                omega
              have d45126 : (x 8 1 && x 8 14).toNat = 0 := by
                have r45127 := hand2 (x 8 1) (x 8 14)
                have b45128 := hb (x 8 14)
                have b45129 := hb (x 8 1 && x 8 14)
                clear * - r45127 b45128 b45129 d45122
                omega
              have d45130 : (x 8 2).toNat = 0 := by
                have r45131 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
                have b45132 := hb (x 8 2)
                have b45133 := hb (x 8 14)
                clear * - r45131 b45132 b45133 d45122
                omega
              have d45134 : (x 6 2).toNat = 0 := by
                have r45135 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
                have b45136 := hb (x 6 2)
                have b45137 := hb (x 6 14)
                clear * - r45135 b45136 b45137 d45105
                omega
              have d45138 : (x 4 2).toNat = 0 := by
                have r45139 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
                have b45140 := hb (x 4 2)
                have b45141 := hb (x 4 14)
                clear * - r45139 b45140 b45141 d45088
                omega
              have d45142 : (x 6 13).toNat = 1 := by
                have r45143 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45144 := hb (x 4 2)
                have b45145 := hb (x 6 13)
                have b45146 := hb (x 5 1 && x 5 14)
                clear * - r45143 b45144 b45145 b45146 d45071 d45138
                omega
              have d45147 : (x 6 1).toNat = 1 := by
                have r45148 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
                have b45149 := hb (x 6 1)
                have b45150 := hb (x 6 13)
                clear * - r45148 b45149 b45150 d45142
                omega
              have d45151 : (x 7 14).toNat = 0 := by
                have r45152 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45153 := hb (x 6 1)
                have b45154 := hb (x 7 14)
                clear * - r45152 b45153 b45154 d45147
                omega
              have d45155 : (x 7 1 && x 7 14).toNat = 0 := by
                have r45156 := hand2 (x 7 1) (x 7 14)
                have b45157 := hb (x 7 14)
                have b45158 := hb (x 7 1 && x 7 14)
                clear * - r45156 b45157 b45158 d45151
                omega
              have d45159 : (x 8 13).toNat = 1 := by
                have r45160 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45161 := hb (x 6 2)
                have b45162 := hb (x 8 13)
                have b45163 := hb (x 7 1 && x 7 14)
                clear * - r45160 b45161 b45162 b45163 d45155 d45134
                omega
              have d45164 : (x 8 1).toNat = 1 := by
                have r45165 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
                have b45166 := hb (x 8 1)
                have b45167 := hb (x 8 13)
                clear * - r45165 b45166 b45167 d45159
                omega
              have d45168 : (x 9 14).toNat = 0 := by
                have r45169 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45170 := hb (x 8 1)
                have b45171 := hb (x 9 14)
                clear * - r45169 b45170 b45171 d45164
                omega
              have d45172 : (x 9 1 && x 9 14).toNat = 0 := by
                have r45173 := hand2 (x 9 1) (x 9 14)
                have b45174 := hb (x 9 14)
                have b45175 := hb (x 9 1 && x 9 14)
                clear * - r45173 b45174 b45175 d45168
                omega
              have d45176 : (x 10 13).toNat = 1 := by
                have r45177 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45178 := hb (x 8 2)
                have b45179 := hb (x 10 13)
                have b45180 := hb (x 9 1 && x 9 14)
                clear * - r45177 b45178 b45179 b45180 d45172 d45130
                omega
              have d45181 : (x 10 1).toNat = 1 := by
                have r45182 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
                have b45183 := hb (x 10 1)
                have b45184 := hb (x 10 13)
                clear * - r45182 b45183 b45184 d45176
                omega
              have d45185 : (x 11 14).toNat = 0 := by
                have r45186 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45187 := hb (x 10 1)
                have b45188 := hb (x 11 14)
                clear * - r45186 b45187 b45188 d45181
                omega
              have d45189 : (x 11 1 && x 11 14).toNat = 0 := by
                have r45190 := hand2 (x 11 1) (x 11 14)
                have b45191 := hb (x 11 14)
                have b45192 := hb (x 11 1 && x 11 14)
                clear * - r45190 b45191 b45192 d45185
                omega
              have d45193 : (x 11 2).toNat = 0 := by
                have r45194 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
                have b45195 := hb (x 11 2)
                have b45196 := hb (x 11 14)
                clear * - r45194 b45195 b45196 d45185
                omega
              have d45197 : (x 9 2).toNat = 0 := by
                have r45198 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
                have b45199 := hb (x 9 2)
                have b45200 := hb (x 9 14)
                clear * - r45198 b45199 b45200 d45168
                omega
              have d45201 : (x 7 2).toNat = 0 := by
                have r45202 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
                have b45203 := hb (x 7 2)
                have b45204 := hb (x 7 14)
                clear * - r45202 b45203 b45204 d45151
                omega
              have d45205 : (x 9 13).toNat = 1 := by
                have r45206 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45207 := hb (x 7 2)
                have b45208 := hb (x 9 13)
                have b45209 := hb (x 8 1 && x 8 14)
                clear * - r45206 b45207 b45208 b45209 d45126 d45201
                omega
              have d45210 : (x 9 1).toNat = 1 := by
                have r45211 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
                have b45212 := hb (x 9 1)
                have b45213 := hb (x 9 13)
                clear * - r45211 b45212 b45213 d45205
                omega
              have d45214 : (x 10 14).toNat = 0 := by
                have r45215 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45216 := hb (x 9 1)
                have b45217 := hb (x 10 14)
                clear * - r45215 b45216 b45217 d45210
                omega
              have d45218 : (x 10 1 && x 10 14).toNat = 0 := by
                have r45219 := hand2 (x 10 1) (x 10 14)
                have b45220 := hb (x 10 14)
                have b45221 := hb (x 10 1 && x 10 14)
                clear * - r45219 b45220 b45221 d45214
                omega
              have d45222 : (x 11 13).toNat = 1 := by
                have r45223 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45224 := hb (x 9 2)
                have b45225 := hb (x 11 13)
                have b45226 := hb (x 10 1 && x 10 14)
                clear * - r45223 b45224 b45225 b45226 d45218 d45197
                omega
              have d45227 : (x 11 1).toNat = 1 := by
                have r45228 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
                have b45229 := hb (x 11 1)
                have b45230 := hb (x 11 13)
                clear * - r45228 b45229 b45230 d45222
                omega
              have d45231 : (x 12 14).toNat = 0 := by
                have r45232 : (x 12 14).toNat + (x 11 1).toNat = 1 := by have q := hd14 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45233 := hb (x 11 1)
                have b45234 := hb (x 12 14)
                clear * - r45232 b45233 b45234 d45227
                omega
              have d45235 : (x 12 1 && x 12 14).toNat = 0 := by
                have r45236 := hand2 (x 12 1) (x 12 14)
                have b45237 := hb (x 12 14)
                have b45238 := hb (x 12 1 && x 12 14)
                clear * - r45236 b45237 b45238 d45231
                omega
              have d45239 : (x 13 13).toNat = 1 := by
                have r45240 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45241 := hb (x 11 2)
                have b45242 := hb (x 13 13)
                have b45243 := hb (x 12 1 && x 12 14)
                clear * - r45240 b45241 b45242 b45243 d45235 d45193
                omega
              have d45244 : (x 13 1).toNat = 1 := by
                have r45245 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
                have b45246 := hb (x 13 1)
                have b45247 := hb (x 13 13)
                clear * - r45245 b45246 b45247 d45239
                omega
              have d45248 : (x 14 14).toNat = 0 := by
                have r45249 : (x 14 14).toNat + (x 13 1).toNat = 1 := by have q := hd14 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45250 := hb (x 13 1)
                have b45251 := hb (x 14 14)
                clear * - r45249 b45250 b45251 d45244
                omega
              have d45252 : (x 14 1 && x 14 14).toNat = 0 := by
                have r45253 := hand2 (x 14 1) (x 14 14)
                have b45254 := hb (x 14 14)
                have b45255 := hb (x 14 1 && x 14 14)
                clear * - r45253 b45254 b45255 d45248
                omega
              have d45256 : (x 14 3 && x 14 14).toNat = 0 := by
                have r45257 := hand2 (x 14 3) (x 14 14)
                have b45258 := hb (x 14 14)
                have b45259 := hb (x 14 3 && x 14 14)
                clear * - r45257 b45258 b45259 d45248
                omega
              have d45260 : (x 14 2).toNat = 0 := by
                have r45261 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
                have b45262 := hb (x 14 2)
                have b45263 := hb (x 14 14)
                clear * - r45261 b45262 b45263 d45248
                omega
              have d45264 : (x 12 2).toNat = 0 := by
                have r45265 : (x 12 2).toNat ≤ (x 12 14).toNat := himp _ _ (hp2 12)
                have b45266 := hb (x 12 2)
                have b45267 := hb (x 12 14)
                clear * - r45265 b45266 b45267 d45231
                omega
              have d45268 : (x 10 2).toNat = 0 := by
                have r45269 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
                have b45270 := hb (x 10 2)
                have b45271 := hb (x 10 14)
                clear * - r45269 b45270 b45271 d45214
                omega
              have d45272 : (x 12 13).toNat = 1 := by
                have r45273 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45274 := hb (x 10 2)
                have b45275 := hb (x 12 13)
                have b45276 := hb (x 11 1 && x 11 14)
                clear * - r45273 b45274 b45275 b45276 d45189 d45268
                omega
              have d45277 : (x 12 1).toNat = 1 := by
                have r45278 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
                have b45279 := hb (x 12 1)
                have b45280 := hb (x 12 13)
                clear * - r45278 b45279 b45280 d45272
                omega
              have d45281 : (x 13 14).toNat = 0 := by
                have r45282 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45283 := hb (x 12 1)
                have b45284 := hb (x 13 14)
                clear * - r45282 b45283 b45284 d45277
                omega
              have d45285 : (x 13 1 && x 13 14).toNat = 0 := by
                have r45286 := hand2 (x 13 1) (x 13 14)
                have b45287 := hb (x 13 14)
                have b45288 := hb (x 13 1 && x 13 14)
                clear * - r45286 b45287 b45288 d45281
                omega
              have d45289 : (x 14 13).toNat = 1 := by
                have r45290 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45291 := hb (x 12 2)
                have b45292 := hb (x 14 13)
                have b45293 := hb (x 13 1 && x 13 14)
                clear * - r45290 b45291 b45292 b45293 d45285 d45264
                omega
              have d45294 : (x 14 1).toNat = 1 := by
                have r45295 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
                have b45296 := hb (x 14 1)
                have b45297 := hb (x 14 13)
                clear * - r45295 b45296 b45297 d45289
                omega
              have d45298 : (x 15 14).toNat = 0 := by
                have r45299 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45300 := hb (x 14 1)
                have b45301 := hb (x 15 14)
                clear * - r45299 b45300 b45301 d45294
                omega
              have d45302 : (x 15 1 && x 15 14).toNat = 0 := by
                have r45303 := hand2 (x 15 1) (x 15 14)
                have b45304 := hb (x 15 14)
                have b45305 := hb (x 15 1 && x 15 14)
                clear * - r45303 b45304 b45305 d45298
                omega
              have d45306 : (x 16 13).toNat = 1 := by
                have r45307 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45308 := hb (x 14 2)
                have b45309 := hb (x 16 13)
                have b45310 := hb (x 15 1 && x 15 14)
                clear * - r45307 b45308 b45309 b45310 d45302 d45260
                omega
              have d45311 : (x 16 1).toNat = 1 := by
                have r45312 : (x 16 13).toNat ≤ (x 16 1).toNat := himp _ _ (hp13 16)
                have b45313 := hb (x 16 1)
                have b45314 := hb (x 16 13)
                clear * - r45312 b45313 b45314 d45306
                omega
              have d45315 : (x 17 14).toNat = 0 := by
                have r45316 : (x 17 14).toNat + (x 16 1).toNat = 1 := by have q := hd14 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45317 := hb (x 16 1)
                have b45318 := hb (x 17 14)
                clear * - r45316 b45317 b45318 d45311
                omega
              have d45319 : (x 17 2).toNat = 0 := by
                have r45320 : (x 17 2).toNat ≤ (x 17 14).toNat := himp _ _ (hp2 17)
                have b45321 := hb (x 17 2)
                have b45322 := hb (x 17 14)
                clear * - r45320 b45321 b45322 d45315
                omega
              have d45323 : (x 15 2).toNat = 0 := by
                have r45324 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
                have b45325 := hb (x 15 2)
                have b45326 := hb (x 15 14)
                clear * - r45324 b45325 b45326 d45298
                omega
              have d45327 : (x 15 2 && x 15 13).toNat = 0 := by
                have r45328 := hand1 (x 15 2) (x 15 13)
                have b45329 := hb (x 15 2)
                have b45330 := hb (x 15 2 && x 15 13)
                clear * - r45328 b45329 b45330 d45323
                omega
              have d45331 : (x 13 2).toNat = 0 := by
                have r45332 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
                have b45333 := hb (x 13 2)
                have b45334 := hb (x 13 14)
                clear * - r45332 b45333 b45334 d45281
                omega
              have d45335 : (x 15 13).toNat = 1 := by
                have r45336 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45337 := hb (x 13 2)
                have b45338 := hb (x 15 13)
                have b45339 := hb (x 14 1 && x 14 14)
                clear * - r45336 b45337 b45338 b45339 d45252 d45331
                omega
              have d45340 : (x 15 1).toNat = 1 := by
                have r45341 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
                have b45342 := hb (x 15 1)
                have b45343 := hb (x 15 13)
                clear * - r45341 b45342 b45343 d45335
                omega
              have d45344 : (x 16 14).toNat = 0 := by
                have r45345 : (x 16 14).toNat + (x 15 1).toNat = 1 := by have q := hd14 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45346 := hb (x 15 1)
                have b45347 := hb (x 16 14)
                clear * - r45345 b45346 b45347 d45340
                omega
              have d45348 : (x 16 1 && x 16 14).toNat = 0 := by
                have r45349 := hand2 (x 16 1) (x 16 14)
                have b45350 := hb (x 16 14)
                have b45351 := hb (x 16 1 && x 16 14)
                clear * - r45349 b45350 b45351 d45344
                omega
              have d45352 : (x 17 13).toNat = 1 := by
                have r45353 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := by have q := hcov13 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45354 := hb (x 15 2)
                have b45355 := hb (x 17 13)
                have b45356 := hb (x 16 1 && x 16 14)
                clear * - r45353 b45354 b45355 b45356 d45348 d45323
                omega
              have d45357 : (x 17 1).toNat = 1 := by
                have r45358 : (x 17 13).toNat ≤ (x 17 1).toNat := himp _ _ (hp13 17)
                have b45359 := hb (x 17 1)
                have b45360 := hb (x 17 13)
                clear * - r45358 b45359 b45360 d45352
                omega
              have d45361 : (x 18 14).toNat = 0 := by
                have r45362 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45363 := hb (x 17 1)
                have b45364 := hb (x 18 14)
                clear * - r45362 b45363 b45364 d45357
                omega
              have d45365 : (x 18 1 && x 18 14).toNat = 0 := by
                have r45366 := hand2 (x 18 1) (x 18 14)
                have b45367 := hb (x 18 14)
                have b45368 := hb (x 18 1 && x 18 14)
                clear * - r45366 b45367 b45368 d45361
                omega
              have d45369 : (x 19 13).toNat = 1 := by
                have r45370 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45371 := hb (x 17 2)
                have b45372 := hb (x 19 13)
                have b45373 := hb (x 18 1 && x 18 14)
                clear * - r45370 b45371 b45372 b45373 d45365 d45319
                omega
              have d45374 : (x 18 2).toNat = 0 := by
                have r45375 : (x 18 2).toNat ≤ (x 18 14).toNat := himp _ _ (hp2 18)
                have b45376 := hb (x 18 2)
                have b45377 := hb (x 18 14)
                clear * - r45375 b45376 b45377 d45361
                omega
              have d45378 : (x 20 12).toNat = 0 := by
                have r45379 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e45380 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
                have e45381 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
                have b45382 := hb (x 17 3)
                have b45383 := hb (x 18 2)
                have b45384 := hb (x 19 13)
                have b45385 := hb (x 20 12)
                clear * - r45379 e45380 e45381 b45382 b45383 b45384 b45385 d45369 d45374
                omega
              have d45386 : (x 17 3).toNat = 0 := by
                have r45387 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e45388 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
                have e45389 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
                have b45390 := hb (x 17 3)
                have b45391 := hb (x 18 2)
                have b45392 := hb (x 19 13)
                have b45393 := hb (x 20 12)
                clear * - r45387 e45388 e45389 b45390 b45391 b45392 b45393 d45378 d45369 d45374
                omega
              have d45394 : (x 17 11).toNat = 0 := by
                have r45395 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
                have b45396 := hb (x 17 3)
                have b45397 := hb (x 17 11)
                clear * - r45395 b45396 b45397 d45386
                omega
              have d45398 : (x 16 12).toNat = 0 := by
                have r45399 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e45400 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                have e45401 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                have b45402 := hb (x 13 3)
                have b45403 := hb (x 14 2)
                have b45404 := hb (x 15 13)
                have b45405 := hb (x 16 12)
                clear * - r45399 e45400 e45401 b45402 b45403 b45404 b45405 d45335 d45260
                omega
              have d45406 : (x 16 1 && x 16 12).toNat = 0 := by
                have r45407 := hand2 (x 16 1) (x 16 12)
                have b45408 := hb (x 16 12)
                have b45409 := hb (x 16 1 && x 16 12)
                clear * - r45407 b45408 b45409 d45398
                omega
              have d45410 : (x 13 12).toNat = 0 := by
                have r45411 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e45412 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
                have e45413 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
                have b45414 := hb (x 10 3)
                have b45415 := hb (x 11 2)
                have b45416 := hb (x 12 13)
                have b45417 := hb (x 13 12)
                clear * - r45411 e45412 e45413 b45414 b45415 b45416 b45417 d45272 d45193
                omega
              have d45418 : (x 13 4).toNat = 0 := by
                have r45419 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
                have b45420 := hb (x 13 4)
                have b45421 := hb (x 13 12)
                clear * - r45419 b45420 b45421 d45410
                omega
              have r45422 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b45423 := hb (x 13 4)
              have b45424 := hb (x 17 11)
              have b45425 := hb (x 16 1 && x 16 12)
              have b45426 := hb (x 15 2 && x 15 13)
              have b45427 := hb (x 14 3 && x 14 14)
              linarith only [r45422, b45423, b45424, b45425, b45426, b45427, d45394, d45406, d45327, d45256, d45418]
          · have f45428 : (x (-1) 8).toNat = 1 := by rw [h43737]; rfl
            have d45429 : (x (-2) 9).toNat = 0 := by
              have r45430 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e45431 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e45432 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e45433 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e45434 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e45435 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e45436 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b45437 := hb (x (-8) 7)
              have b45438 := hb (x (-7) 6)
              have b45439 := hb (x (-6) 5)
              have b45440 := hb (x (-5) 4)
              have b45441 := hb (x (-4) 11)
              have b45442 := hb (x (-3) 10)
              have b45443 := hb (x (-2) 9)
              have b45444 := hb (x (-1) 8)
              clear * - r45430 e45431 e45432 e45433 e45434 e45435 e45436 b45437 b45438 b45439 b45440 b45441 b45442 b45443 b45444 f45428 g5 g2
              omega
            have d45445 : (x (-5) 4).toNat = 0 := by
              have r45446 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e45447 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e45448 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e45449 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e45450 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e45451 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e45452 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b45453 := hb (x (-8) 7)
              have b45454 := hb (x (-7) 6)
              have b45455 := hb (x (-6) 5)
              have b45456 := hb (x (-5) 4)
              have b45457 := hb (x (-4) 11)
              have b45458 := hb (x (-3) 10)
              have b45459 := hb (x (-2) 9)
              have b45460 := hb (x (-1) 8)
              clear * - r45446 e45447 e45448 e45449 e45450 e45451 e45452 b45453 b45454 b45455 b45456 b45457 b45458 b45459 b45460 f45428 d45429 g5 g2
              omega
            have d45461 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
              have r45462 := hand1 (x (-5) 4) (x (-5) 13)
              have b45463 := hb (x (-5) 4)
              have b45464 := hb (x (-5) 4 && x (-5) 13)
              clear * - r45462 b45463 b45464 d45445
              omega
            have d45465 : (x (-6) 5).toNat = 0 := by
              have r45466 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e45467 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e45468 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e45469 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e45470 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e45471 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e45472 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b45473 := hb (x (-8) 7)
              have b45474 := hb (x (-7) 6)
              have b45475 := hb (x (-6) 5)
              have b45476 := hb (x (-5) 4)
              have b45477 := hb (x (-4) 11)
              have b45478 := hb (x (-3) 10)
              have b45479 := hb (x (-2) 9)
              have b45480 := hb (x (-1) 8)
              clear * - r45466 e45467 e45468 e45469 e45470 e45471 e45472 b45473 b45474 b45475 b45476 b45477 b45478 b45479 b45480 f45428 d45429 g5 g2 d45445
              omega
            have d45481 : (x (-6) 5 && x (-6) 14).toNat = 0 := by
              have r45482 := hand1 (x (-6) 5) (x (-6) 14)
              have b45483 := hb (x (-6) 5)
              have b45484 := hb (x (-6) 5 && x (-6) 14)
              clear * - r45482 b45483 b45484 d45465
              omega
            have d45485 : (x (-7) 6).toNat = 1 := by
              have r45486 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b45487 := hb (x (-7) 6)
              have b45488 := hb (x (-1) 9)
              have b45489 := hb (x (-2) 1 && x (-2) 10)
              have b45490 := hb (x (-3) 2 && x (-3) 11)
              have b45491 := hb (x (-4) 3 && x (-4) 12)
              have b45492 := hb (x (-5) 4 && x (-5) 13)
              have b45493 := hb (x (-6) 5 && x (-6) 14)
              clear * - r45486 b45487 b45488 b45489 b45490 b45491 b45492 b45493 g11 g58 g59 g60 d45461 d45481
              omega
            have r45494 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e45495 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e45496 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e45497 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e45498 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e45499 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e45500 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have b45501 := hb (x (-8) 7)
            have b45502 := hb (x (-7) 6)
            have b45503 := hb (x (-6) 5)
            have b45504 := hb (x (-5) 4)
            have b45505 := hb (x (-4) 11)
            have b45506 := hb (x (-3) 10)
            have b45507 := hb (x (-2) 9)
            have b45508 := hb (x (-1) 8)
            linarith only [r45494, e45495, e45496, e45497, e45498, e45499, e45500, b45501, b45502, b45503, b45504, b45505, b45506, b45507, b45508, f45428, d45429, g5, g2, d45445, d45465, d45485]
        · have f45509 : (x (-1) 7).toNat = 1 := by rw [h43735]; rfl
          have d45510 : (x 6 8).toNat = 0 := by
            have r45511 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e45512 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
            have e45513 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
            have e45514 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
            have e45515 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
            have e45516 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
            have e45517 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
            have b45518 := hb (x (-1) 7)
            have b45519 := hb (x 0 6)
            have b45520 := hb (x 1 5)
            have b45521 := hb (x 2 4)
            have b45522 := hb (x 3 11)
            have b45523 := hb (x 4 10)
            have b45524 := hb (x 5 9)
            have b45525 := hb (x 6 8)
            clear * - r45511 e45512 e45513 e45514 e45515 e45516 e45517 b45518 b45519 b45520 b45521 b45522 b45523 b45524 b45525 f43734 f43722 f45509
            omega
          have d45526 : (x 5 9).toNat = 0 := by
            have r45527 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e45528 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
            have e45529 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
            have e45530 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
            have e45531 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
            have e45532 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
            have e45533 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
            have b45534 := hb (x (-1) 7)
            have b45535 := hb (x 0 6)
            have b45536 := hb (x 1 5)
            have b45537 := hb (x 2 4)
            have b45538 := hb (x 3 11)
            have b45539 := hb (x 4 10)
            have b45540 := hb (x 5 9)
            have b45541 := hb (x 6 8)
            clear * - r45527 e45528 e45529 e45530 e45531 e45532 e45533 b45534 b45535 b45536 b45537 b45538 b45539 b45540 b45541 d45510 f43734 f43722 f45509
            omega
          have d45542 : (x 4 10).toNat = 0 := by
            have r45543 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e45544 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
            have e45545 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
            have e45546 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
            have e45547 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
            have e45548 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
            have e45549 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
            have b45550 := hb (x (-1) 7)
            have b45551 := hb (x 0 6)
            have b45552 := hb (x 1 5)
            have b45553 := hb (x 2 4)
            have b45554 := hb (x 3 11)
            have b45555 := hb (x 4 10)
            have b45556 := hb (x 5 9)
            have b45557 := hb (x 6 8)
            clear * - r45543 e45544 e45545 e45546 e45547 e45548 e45549 b45550 b45551 b45552 b45553 b45554 b45555 b45556 b45557 d45510 d45526 f43734 f43722 f45509
            omega
          have d45558 : (x 4 1 && x 4 10).toNat = 0 := by
            have r45559 := hand2 (x 4 1) (x 4 10)
            have b45560 := hb (x 4 10)
            have b45561 := hb (x 4 1 && x 4 10)
            clear * - r45559 b45560 b45561 d45542
            omega
          have d45562 : (x 2 3 && x 2 12).toNat = 1 := by
            have r45563 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b45564 := hb (x (-1) 6)
            have b45565 := hb (x 5 9)
            have b45566 := hb (x 4 1 && x 4 10)
            have b45567 := hb (x 3 2 && x 3 11)
            have b45568 := hb (x 2 3 && x 2 12)
            have b45569 := hb (x 1 4 && x 1 13)
            have b45570 := hb (x 0 5 && x 0 14)
            clear * - r45563 b45564 b45565 b45566 b45567 b45568 b45569 b45570 d45526 d45558 g61 g62 g63 g10
            omega
          have d45571 : (x 2 3).toNat = 1 := by
            have r45572 := hand1 (x 2 3) (x 2 12)
            have b45573 := hb (x 2 3)
            have b45574 := hb (x 2 3 && x 2 12)
            clear * - r45572 b45573 b45574 d45562
            omega
          have d45575 : (x 5 12).toNat = 0 := by
            have r45576 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e45577 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e45578 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b45579 := hb (x 2 3)
            have b45580 := hb (x 3 2)
            have b45581 := hb (x 4 13)
            have b45582 := hb (x 5 12)
            clear * - r45576 e45577 e45578 b45579 b45580 b45581 b45582 g22 d45571
            omega
          have d45583 : (x 4 13).toNat = 0 := by
            have r45584 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e45585 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e45586 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b45587 := hb (x 2 3)
            have b45588 := hb (x 3 2)
            have b45589 := hb (x 4 13)
            have b45590 := hb (x 5 12)
            clear * - r45584 e45585 e45586 b45587 b45588 b45589 b45590 d45575 g22 d45571
            omega
          have d45591 : (x 2 2).toNat = 1 := by
            have r45592 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b45593 := hb (x 2 2)
            have b45594 := hb (x 4 13)
            have b45595 := hb (x 3 1 && x 3 14)
            clear * - r45592 b45593 b45594 b45595 d45583 g80
            omega
          have d45596 : (x 4 12).toNat = 0 := by
            have r45597 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e45598 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e45599 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b45600 := hb (x 1 3)
            have b45601 := hb (x 2 2)
            have b45602 := hb (x 3 13)
            have b45603 := hb (x 4 12)
            clear * - r45597 e45598 e45599 b45600 b45601 b45602 b45603 d45591 f43724
            omega
          have d45604 : (x 4 3 && x 4 12).toNat = 0 := by
            have r45605 := hand2 (x 4 3) (x 4 12)
            have b45606 := hb (x 4 12)
            have b45607 := hb (x 4 3 && x 4 12)
            clear * - r45605 b45606 b45607 d45596
            omega
          have d45608 : (x 2 5 && x 2 14).toNat = 1 := by
            have r45609 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b45610 := hb (x 1 6)
            have b45611 := hb (x 7 9)
            have b45612 := hb (x 6 1 && x 6 10)
            have b45613 := hb (x 5 2 && x 5 11)
            have b45614 := hb (x 4 3 && x 4 12)
            have b45615 := hb (x 3 4 && x 3 13)
            have b45616 := hb (x 2 5 && x 2 14)
            clear * - r45609 b45610 b45611 b45612 b45613 b45614 b45615 b45616 d43589 d43625 d43653 d45604 g66 g20
            omega
          have d45617 : (x 2 5).toNat = 1 := by
            have r45618 := hand1 (x 2 5) (x 2 14)
            have b45619 := hb (x 2 5)
            have b45620 := hb (x 2 5 && x 2 14)
            clear * - r45618 b45619 b45620 d45608
            omega
          have d45621 : (x 7 8).toNat = 0 := by
            have r45622 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e45623 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
            have e45624 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
            have e45625 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
            have e45626 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
            have e45627 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
            have e45628 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
            have b45629 := hb (x 0 7)
            have b45630 := hb (x 1 6)
            have b45631 := hb (x 2 5)
            have b45632 := hb (x 3 4)
            have b45633 := hb (x 4 11)
            have b45634 := hb (x 5 10)
            have b45635 := hb (x 6 9)
            have b45636 := hb (x 7 8)
            clear * - r45622 e45623 e45624 e45625 e45626 e45627 e45628 b45629 b45630 b45631 b45632 b45633 b45634 b45635 b45636 g23 d45617 g20 g15
            omega
          have d45637 : (x 6 9).toNat = 0 := by
            have r45638 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e45639 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
            have e45640 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
            have e45641 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
            have e45642 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
            have e45643 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
            have e45644 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
            have b45645 := hb (x 0 7)
            have b45646 := hb (x 1 6)
            have b45647 := hb (x 2 5)
            have b45648 := hb (x 3 4)
            have b45649 := hb (x 4 11)
            have b45650 := hb (x 5 10)
            have b45651 := hb (x 6 9)
            have b45652 := hb (x 7 8)
            clear * - r45638 e45639 e45640 e45641 e45642 e45643 e45644 b45645 b45646 b45647 b45648 b45649 b45650 b45651 b45652 d45621 g23 d45617 g20 g15
            omega
          have d45653 : (x 5 10).toNat = 0 := by
            have r45654 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e45655 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
            have e45656 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
            have e45657 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
            have e45658 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
            have e45659 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
            have e45660 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
            have b45661 := hb (x 0 7)
            have b45662 := hb (x 1 6)
            have b45663 := hb (x 2 5)
            have b45664 := hb (x 3 4)
            have b45665 := hb (x 4 11)
            have b45666 := hb (x 5 10)
            have b45667 := hb (x 6 9)
            have b45668 := hb (x 7 8)
            clear * - r45654 e45655 e45656 e45657 e45658 e45659 e45660 b45661 b45662 b45663 b45664 b45665 b45666 b45667 b45668 d45621 d45637 g23 d45617 g20 g15
            omega
          have d45669 : (x 5 1 && x 5 10).toNat = 0 := by
            have r45670 := hand2 (x 5 1) (x 5 10)
            have b45671 := hb (x 5 10)
            have b45672 := hb (x 5 1 && x 5 10)
            clear * - r45670 b45671 b45672 d45653
            omega
          have d45673 : (x 4 11).toNat = 0 := by
            have r45674 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e45675 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
            have e45676 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
            have e45677 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
            have e45678 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
            have e45679 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
            have e45680 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
            have b45681 := hb (x 0 7)
            have b45682 := hb (x 1 6)
            have b45683 := hb (x 2 5)
            have b45684 := hb (x 3 4)
            have b45685 := hb (x 4 11)
            have b45686 := hb (x 5 10)
            have b45687 := hb (x 6 9)
            have b45688 := hb (x 7 8)
            clear * - r45674 e45675 e45676 e45677 e45678 e45679 e45680 b45681 b45682 b45683 b45684 b45685 b45686 b45687 b45688 d45621 d45637 d45653 g23 d45617 g20 g15
            omega
          have d45689 : (x 4 2 && x 4 11).toNat = 0 := by
            have r45690 := hand2 (x 4 2) (x 4 11)
            have b45691 := hb (x 4 11)
            have b45692 := hb (x 4 2 && x 4 11)
            clear * - r45690 b45691 b45692 d45673
            omega
          have d45693 : (x 2 4 && x 2 13).toNat = 1 := by
            have r45694 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b45695 := hb (x 0 6)
            have b45696 := hb (x 6 9)
            have b45697 := hb (x 5 1 && x 5 10)
            have b45698 := hb (x 4 2 && x 4 11)
            have b45699 := hb (x 3 3 && x 3 12)
            have b45700 := hb (x 2 4 && x 2 13)
            have b45701 := hb (x 1 5 && x 1 14)
            clear * - r45694 b45695 b45696 b45697 b45698 b45699 b45700 b45701 d45637 d45669 d45689 g64 g65 f43722
            omega
          have d45702 : (x 2 4).toNat = 1 := by
            have r45703 := hand1 (x 2 4) (x 2 13)
            have b45704 := hb (x 2 4)
            have b45705 := hb (x 2 4 && x 2 13)
            clear * - r45703 b45704 b45705 d45693
            omega
          have r45706 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e45707 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
          have e45708 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
          have e45709 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
          have e45710 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
          have e45711 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
          have e45712 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
          have b45713 := hb (x (-1) 7)
          have b45714 := hb (x 0 6)
          have b45715 := hb (x 1 5)
          have b45716 := hb (x 2 4)
          have b45717 := hb (x 3 11)
          have b45718 := hb (x 4 10)
          have b45719 := hb (x 5 9)
          have b45720 := hb (x 6 8)
          linarith only [r45706, e45707, e45708, e45709, e45710, e45711, e45712, b45713, b45714, b45715, b45716, b45717, b45718, b45719, b45720, d45510, d45526, d45542, d45702, f43734, f43722, f45509]
      · have f45721 : (x 1 5).toNat = 1 := by rw [h43733]; rfl
        have d45722 : (x 1 13).toNat = 1 := by
          have r45723 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
          have b45724 := hb (x 1 5)
          have b45725 := hb (x 1 13)
          clear * - r45723 b45724 b45725 f45721
          omega
        have d45726 : (x 1 1).toNat = 1 := by
          have r45727 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
          have b45728 := hb (x 1 1)
          have b45729 := hb (x 1 13)
          clear * - r45727 b45728 b45729 d45722
          omega
        have d45730 : (x 2 14).toNat = 0 := by
          have r45731 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b45732 := hb (x 1 1)
          have b45733 := hb (x 2 14)
          clear * - r45731 b45732 b45733 d45726
          omega
        have d45734 : (x 2 1 && x 2 14).toNat = 0 := by
          have r45735 := hand2 (x 2 1) (x 2 14)
          have b45736 := hb (x 2 14)
          have b45737 := hb (x 2 1 && x 2 14)
          clear * - r45735 b45736 b45737 d45730
          omega
        have d45738 : (x 2 2).toNat = 0 := by
          have r45739 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
          have b45740 := hb (x 2 2)
          have b45741 := hb (x 2 14)
          clear * - r45739 b45740 b45741 d45730
          omega
        have d45742 : (x 4 13).toNat = 1 := by
          have r45743 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b45744 := hb (x 2 2)
          have b45745 := hb (x 4 13)
          have b45746 := hb (x 3 1 && x 3 14)
          clear * - r45743 b45744 b45745 b45746 g80 d45738
          omega
        have d45747 : (x 4 1).toNat = 1 := by
          have r45748 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
          have b45749 := hb (x 4 1)
          have b45750 := hb (x 4 13)
          clear * - r45748 b45749 b45750 d45742
          omega
        have d45751 : (x 5 14).toNat = 0 := by
          have r45752 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b45753 := hb (x 4 1)
          have b45754 := hb (x 5 14)
          clear * - r45752 b45753 b45754 d45747
          omega
        have d45755 : (x 5 1 && x 5 14).toNat = 0 := by
          have r45756 := hand2 (x 5 1) (x 5 14)
          have b45757 := hb (x 5 14)
          have b45758 := hb (x 5 1 && x 5 14)
          clear * - r45756 b45757 b45758 d45751
          omega
        have d45759 : (x 5 2).toNat = 0 := by
          have r45760 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
          have b45761 := hb (x 5 2)
          have b45762 := hb (x 5 14)
          clear * - r45760 b45761 b45762 d45751
          omega
        have d45763 : (x 3 13).toNat = 1 := by
          have r45764 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b45765 := hb (x 1 2)
          have b45766 := hb (x 3 13)
          have b45767 := hb (x 2 1 && x 2 14)
          clear * - r45764 b45765 b45766 b45767 d45734 g18
          omega
        have d45768 : (x 3 1).toNat = 1 := by
          have r45769 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
          have b45770 := hb (x 3 1)
          have b45771 := hb (x 3 13)
          clear * - r45769 b45770 b45771 d45763
          omega
        have d45772 : (x 4 14).toNat = 0 := by
          have r45773 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b45774 := hb (x 3 1)
          have b45775 := hb (x 4 14)
          clear * - r45773 b45774 b45775 d45768
          omega
        have d45776 : (x 4 1 && x 4 14).toNat = 0 := by
          have r45777 := hand2 (x 4 1) (x 4 14)
          have b45778 := hb (x 4 14)
          have b45779 := hb (x 4 1 && x 4 14)
          clear * - r45777 b45778 b45779 d45772
          omega
        have d45780 : (x 5 13).toNat = 1 := by
          have r45781 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b45782 := hb (x 3 2)
          have b45783 := hb (x 5 13)
          have b45784 := hb (x 4 1 && x 4 14)
          clear * - r45781 b45782 b45783 b45784 d45776 g22
          omega
        have d45785 : (x 5 1).toNat = 1 := by
          have r45786 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
          have b45787 := hb (x 5 1)
          have b45788 := hb (x 5 13)
          clear * - r45786 b45787 b45788 d45780
          omega
        have d45789 : (x 6 14).toNat = 0 := by
          have r45790 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b45791 := hb (x 5 1)
          have b45792 := hb (x 6 14)
          clear * - r45790 b45791 b45792 d45785
          omega
        have d45793 : (x 6 1 && x 6 14).toNat = 0 := by
          have r45794 := hand2 (x 6 1) (x 6 14)
          have b45795 := hb (x 6 14)
          have b45796 := hb (x 6 1 && x 6 14)
          clear * - r45794 b45795 b45796 d45789
          omega
        have d45797 : (x 7 13).toNat = 1 := by
          have r45798 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b45799 := hb (x 5 2)
          have b45800 := hb (x 7 13)
          have b45801 := hb (x 6 1 && x 6 14)
          clear * - r45798 b45799 b45800 b45801 d45793 d45759
          omega
        have d45802 : (x 7 1).toNat = 1 := by
          have r45803 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
          have b45804 := hb (x 7 1)
          have b45805 := hb (x 7 13)
          clear * - r45803 b45804 b45805 d45797
          omega
        have d45806 : (x 8 14).toNat = 0 := by
          have r45807 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b45808 := hb (x 7 1)
          have b45809 := hb (x 8 14)
          clear * - r45807 b45808 b45809 d45802
          omega
        have d45810 : (x 8 1 && x 8 14).toNat = 0 := by
          have r45811 := hand2 (x 8 1) (x 8 14)
          have b45812 := hb (x 8 14)
          have b45813 := hb (x 8 1 && x 8 14)
          clear * - r45811 b45812 b45813 d45806
          omega
        have d45814 : (x 8 2).toNat = 0 := by
          have r45815 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
          have b45816 := hb (x 8 2)
          have b45817 := hb (x 8 14)
          clear * - r45815 b45816 b45817 d45806
          omega
        have d45818 : (x 6 2).toNat = 0 := by
          have r45819 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
          have b45820 := hb (x 6 2)
          have b45821 := hb (x 6 14)
          clear * - r45819 b45820 b45821 d45789
          omega
        have d45822 : (x 4 2).toNat = 0 := by
          have r45823 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
          have b45824 := hb (x 4 2)
          have b45825 := hb (x 4 14)
          clear * - r45823 b45824 b45825 d45772
          omega
        have d45826 : (x 6 13).toNat = 1 := by
          have r45827 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b45828 := hb (x 4 2)
          have b45829 := hb (x 6 13)
          have b45830 := hb (x 5 1 && x 5 14)
          clear * - r45827 b45828 b45829 b45830 d45755 d45822
          omega
        have d45831 : (x 6 1).toNat = 1 := by
          have r45832 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
          have b45833 := hb (x 6 1)
          have b45834 := hb (x 6 13)
          clear * - r45832 b45833 b45834 d45826
          omega
        have d45835 : (x 7 14).toNat = 0 := by
          have r45836 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b45837 := hb (x 6 1)
          have b45838 := hb (x 7 14)
          clear * - r45836 b45837 b45838 d45831
          omega
        have d45839 : (x 7 1 && x 7 14).toNat = 0 := by
          have r45840 := hand2 (x 7 1) (x 7 14)
          have b45841 := hb (x 7 14)
          have b45842 := hb (x 7 1 && x 7 14)
          clear * - r45840 b45841 b45842 d45835
          omega
        have d45843 : (x 8 13).toNat = 1 := by
          have r45844 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b45845 := hb (x 6 2)
          have b45846 := hb (x 8 13)
          have b45847 := hb (x 7 1 && x 7 14)
          clear * - r45844 b45845 b45846 b45847 d45839 d45818
          omega
        have d45848 : (x 8 1).toNat = 1 := by
          have r45849 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
          have b45850 := hb (x 8 1)
          have b45851 := hb (x 8 13)
          clear * - r45849 b45850 b45851 d45843
          omega
        have d45852 : (x 9 14).toNat = 0 := by
          have r45853 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b45854 := hb (x 8 1)
          have b45855 := hb (x 9 14)
          clear * - r45853 b45854 b45855 d45848
          omega
        have d45856 : (x 9 1 && x 9 14).toNat = 0 := by
          have r45857 := hand2 (x 9 1) (x 9 14)
          have b45858 := hb (x 9 14)
          have b45859 := hb (x 9 1 && x 9 14)
          clear * - r45857 b45858 b45859 d45852
          omega
        have d45860 : (x 10 13).toNat = 1 := by
          have r45861 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b45862 := hb (x 8 2)
          have b45863 := hb (x 10 13)
          have b45864 := hb (x 9 1 && x 9 14)
          clear * - r45861 b45862 b45863 b45864 d45856 d45814
          omega
        have d45865 : (x 10 1).toNat = 1 := by
          have r45866 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
          have b45867 := hb (x 10 1)
          have b45868 := hb (x 10 13)
          clear * - r45866 b45867 b45868 d45860
          omega
        have d45869 : (x 11 14).toNat = 0 := by
          have r45870 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b45871 := hb (x 10 1)
          have b45872 := hb (x 11 14)
          clear * - r45870 b45871 b45872 d45865
          omega
        have d45873 : (x 11 1 && x 11 14).toNat = 0 := by
          have r45874 := hand2 (x 11 1) (x 11 14)
          have b45875 := hb (x 11 14)
          have b45876 := hb (x 11 1 && x 11 14)
          clear * - r45874 b45875 b45876 d45869
          omega
        have d45877 : (x 11 2).toNat = 0 := by
          have r45878 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
          have b45879 := hb (x 11 2)
          have b45880 := hb (x 11 14)
          clear * - r45878 b45879 b45880 d45869
          omega
        have d45881 : (x 9 2).toNat = 0 := by
          have r45882 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
          have b45883 := hb (x 9 2)
          have b45884 := hb (x 9 14)
          clear * - r45882 b45883 b45884 d45852
          omega
        have d45885 : (x 7 2).toNat = 0 := by
          have r45886 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
          have b45887 := hb (x 7 2)
          have b45888 := hb (x 7 14)
          clear * - r45886 b45887 b45888 d45835
          omega
        have d45889 : (x 9 13).toNat = 1 := by
          have r45890 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b45891 := hb (x 7 2)
          have b45892 := hb (x 9 13)
          have b45893 := hb (x 8 1 && x 8 14)
          clear * - r45890 b45891 b45892 b45893 d45810 d45885
          omega
        have d45894 : (x 9 1).toNat = 1 := by
          have r45895 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
          have b45896 := hb (x 9 1)
          have b45897 := hb (x 9 13)
          clear * - r45895 b45896 b45897 d45889
          omega
        have d45898 : (x 10 14).toNat = 0 := by
          have r45899 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b45900 := hb (x 9 1)
          have b45901 := hb (x 10 14)
          clear * - r45899 b45900 b45901 d45894
          omega
        have d45902 : (x 10 1 && x 10 14).toNat = 0 := by
          have r45903 := hand2 (x 10 1) (x 10 14)
          have b45904 := hb (x 10 14)
          have b45905 := hb (x 10 1 && x 10 14)
          clear * - r45903 b45904 b45905 d45898
          omega
        have d45906 : (x 11 13).toNat = 1 := by
          have r45907 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b45908 := hb (x 9 2)
          have b45909 := hb (x 11 13)
          have b45910 := hb (x 10 1 && x 10 14)
          clear * - r45907 b45908 b45909 b45910 d45902 d45881
          omega
        have d45911 : (x 11 1).toNat = 1 := by
          have r45912 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
          have b45913 := hb (x 11 1)
          have b45914 := hb (x 11 13)
          clear * - r45912 b45913 b45914 d45906
          omega
        have d45915 : (x 12 14).toNat = 0 := by
          have r45916 : (x 12 14).toNat + (x 11 1).toNat = 1 := by have q := hd14 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b45917 := hb (x 11 1)
          have b45918 := hb (x 12 14)
          clear * - r45916 b45917 b45918 d45911
          omega
        have d45919 : (x 12 1 && x 12 14).toNat = 0 := by
          have r45920 := hand2 (x 12 1) (x 12 14)
          have b45921 := hb (x 12 14)
          have b45922 := hb (x 12 1 && x 12 14)
          clear * - r45920 b45921 b45922 d45915
          omega
        have d45923 : (x 13 13).toNat = 1 := by
          have r45924 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b45925 := hb (x 11 2)
          have b45926 := hb (x 13 13)
          have b45927 := hb (x 12 1 && x 12 14)
          clear * - r45924 b45925 b45926 b45927 d45919 d45877
          omega
        have d45928 : (x 13 1).toNat = 1 := by
          have r45929 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
          have b45930 := hb (x 13 1)
          have b45931 := hb (x 13 13)
          clear * - r45929 b45930 b45931 d45923
          omega
        have d45932 : (x 14 14).toNat = 0 := by
          have r45933 : (x 14 14).toNat + (x 13 1).toNat = 1 := by have q := hd14 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b45934 := hb (x 13 1)
          have b45935 := hb (x 14 14)
          clear * - r45933 b45934 b45935 d45928
          omega
        have d45936 : (x 14 1 && x 14 14).toNat = 0 := by
          have r45937 := hand2 (x 14 1) (x 14 14)
          have b45938 := hb (x 14 14)
          have b45939 := hb (x 14 1 && x 14 14)
          clear * - r45937 b45938 b45939 d45932
          omega
        have d45940 : (x 14 3 && x 14 14).toNat = 0 := by
          have r45941 := hand2 (x 14 3) (x 14 14)
          have b45942 := hb (x 14 14)
          have b45943 := hb (x 14 3 && x 14 14)
          clear * - r45941 b45942 b45943 d45932
          omega
        have d45944 : (x 14 2).toNat = 0 := by
          have r45945 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
          have b45946 := hb (x 14 2)
          have b45947 := hb (x 14 14)
          clear * - r45945 b45946 b45947 d45932
          omega
        have d45948 : (x 12 2).toNat = 0 := by
          have r45949 : (x 12 2).toNat ≤ (x 12 14).toNat := himp _ _ (hp2 12)
          have b45950 := hb (x 12 2)
          have b45951 := hb (x 12 14)
          clear * - r45949 b45950 b45951 d45915
          omega
        have d45952 : (x 10 2).toNat = 0 := by
          have r45953 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
          have b45954 := hb (x 10 2)
          have b45955 := hb (x 10 14)
          clear * - r45953 b45954 b45955 d45898
          omega
        have d45956 : (x 12 13).toNat = 1 := by
          have r45957 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b45958 := hb (x 10 2)
          have b45959 := hb (x 12 13)
          have b45960 := hb (x 11 1 && x 11 14)
          clear * - r45957 b45958 b45959 b45960 d45873 d45952
          omega
        have d45961 : (x 12 1).toNat = 1 := by
          have r45962 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
          have b45963 := hb (x 12 1)
          have b45964 := hb (x 12 13)
          clear * - r45962 b45963 b45964 d45956
          omega
        have d45965 : (x 13 14).toNat = 0 := by
          have r45966 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b45967 := hb (x 12 1)
          have b45968 := hb (x 13 14)
          clear * - r45966 b45967 b45968 d45961
          omega
        have d45969 : (x 13 1 && x 13 14).toNat = 0 := by
          have r45970 := hand2 (x 13 1) (x 13 14)
          have b45971 := hb (x 13 14)
          have b45972 := hb (x 13 1 && x 13 14)
          clear * - r45970 b45971 b45972 d45965
          omega
        have d45973 : (x 14 13).toNat = 1 := by
          have r45974 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b45975 := hb (x 12 2)
          have b45976 := hb (x 14 13)
          have b45977 := hb (x 13 1 && x 13 14)
          clear * - r45974 b45975 b45976 b45977 d45969 d45948
          omega
        have d45978 : (x 14 1).toNat = 1 := by
          have r45979 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
          have b45980 := hb (x 14 1)
          have b45981 := hb (x 14 13)
          clear * - r45979 b45980 b45981 d45973
          omega
        have d45982 : (x 15 14).toNat = 0 := by
          have r45983 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b45984 := hb (x 14 1)
          have b45985 := hb (x 15 14)
          clear * - r45983 b45984 b45985 d45978
          omega
        have d45986 : (x 15 1 && x 15 14).toNat = 0 := by
          have r45987 := hand2 (x 15 1) (x 15 14)
          have b45988 := hb (x 15 14)
          have b45989 := hb (x 15 1 && x 15 14)
          clear * - r45987 b45988 b45989 d45982
          omega
        have d45990 : (x 16 13).toNat = 1 := by
          have r45991 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b45992 := hb (x 14 2)
          have b45993 := hb (x 16 13)
          have b45994 := hb (x 15 1 && x 15 14)
          clear * - r45991 b45992 b45993 b45994 d45986 d45944
          omega
        have d45995 : (x 16 1).toNat = 1 := by
          have r45996 : (x 16 13).toNat ≤ (x 16 1).toNat := himp _ _ (hp13 16)
          have b45997 := hb (x 16 1)
          have b45998 := hb (x 16 13)
          clear * - r45996 b45997 b45998 d45990
          omega
        have d45999 : (x 17 14).toNat = 0 := by
          have r46000 : (x 17 14).toNat + (x 16 1).toNat = 1 := by have q := hd14 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b46001 := hb (x 16 1)
          have b46002 := hb (x 17 14)
          clear * - r46000 b46001 b46002 d45995
          omega
        have d46003 : (x 17 2).toNat = 0 := by
          have r46004 : (x 17 2).toNat ≤ (x 17 14).toNat := himp _ _ (hp2 17)
          have b46005 := hb (x 17 2)
          have b46006 := hb (x 17 14)
          clear * - r46004 b46005 b46006 d45999
          omega
        have d46007 : (x 15 2).toNat = 0 := by
          have r46008 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
          have b46009 := hb (x 15 2)
          have b46010 := hb (x 15 14)
          clear * - r46008 b46009 b46010 d45982
          omega
        have d46011 : (x 15 2 && x 15 13).toNat = 0 := by
          have r46012 := hand1 (x 15 2) (x 15 13)
          have b46013 := hb (x 15 2)
          have b46014 := hb (x 15 2 && x 15 13)
          clear * - r46012 b46013 b46014 d46007
          omega
        have d46015 : (x 13 2).toNat = 0 := by
          have r46016 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
          have b46017 := hb (x 13 2)
          have b46018 := hb (x 13 14)
          clear * - r46016 b46017 b46018 d45965
          omega
        have d46019 : (x 15 13).toNat = 1 := by
          have r46020 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b46021 := hb (x 13 2)
          have b46022 := hb (x 15 13)
          have b46023 := hb (x 14 1 && x 14 14)
          clear * - r46020 b46021 b46022 b46023 d45936 d46015
          omega
        have d46024 : (x 15 1).toNat = 1 := by
          have r46025 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
          have b46026 := hb (x 15 1)
          have b46027 := hb (x 15 13)
          clear * - r46025 b46026 b46027 d46019
          omega
        have d46028 : (x 16 14).toNat = 0 := by
          have r46029 : (x 16 14).toNat + (x 15 1).toNat = 1 := by have q := hd14 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b46030 := hb (x 15 1)
          have b46031 := hb (x 16 14)
          clear * - r46029 b46030 b46031 d46024
          omega
        have d46032 : (x 16 1 && x 16 14).toNat = 0 := by
          have r46033 := hand2 (x 16 1) (x 16 14)
          have b46034 := hb (x 16 14)
          have b46035 := hb (x 16 1 && x 16 14)
          clear * - r46033 b46034 b46035 d46028
          omega
        have d46036 : (x 17 13).toNat = 1 := by
          have r46037 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := by have q := hcov13 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b46038 := hb (x 15 2)
          have b46039 := hb (x 17 13)
          have b46040 := hb (x 16 1 && x 16 14)
          clear * - r46037 b46038 b46039 b46040 d46032 d46007
          omega
        have d46041 : (x 17 1).toNat = 1 := by
          have r46042 : (x 17 13).toNat ≤ (x 17 1).toNat := himp _ _ (hp13 17)
          have b46043 := hb (x 17 1)
          have b46044 := hb (x 17 13)
          clear * - r46042 b46043 b46044 d46036
          omega
        have d46045 : (x 18 14).toNat = 0 := by
          have r46046 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b46047 := hb (x 17 1)
          have b46048 := hb (x 18 14)
          clear * - r46046 b46047 b46048 d46041
          omega
        have d46049 : (x 18 1 && x 18 14).toNat = 0 := by
          have r46050 := hand2 (x 18 1) (x 18 14)
          have b46051 := hb (x 18 14)
          have b46052 := hb (x 18 1 && x 18 14)
          clear * - r46050 b46051 b46052 d46045
          omega
        have d46053 : (x 19 13).toNat = 1 := by
          have r46054 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b46055 := hb (x 17 2)
          have b46056 := hb (x 19 13)
          have b46057 := hb (x 18 1 && x 18 14)
          clear * - r46054 b46055 b46056 b46057 d46049 d46003
          omega
        have d46058 : (x 18 2).toNat = 0 := by
          have r46059 : (x 18 2).toNat ≤ (x 18 14).toNat := himp _ _ (hp2 18)
          have b46060 := hb (x 18 2)
          have b46061 := hb (x 18 14)
          clear * - r46059 b46060 b46061 d46045
          omega
        have d46062 : (x 20 12).toNat = 0 := by
          have r46063 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e46064 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
          have e46065 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
          have b46066 := hb (x 17 3)
          have b46067 := hb (x 18 2)
          have b46068 := hb (x 19 13)
          have b46069 := hb (x 20 12)
          clear * - r46063 e46064 e46065 b46066 b46067 b46068 b46069 d46053 d46058
          omega
        have d46070 : (x 17 3).toNat = 0 := by
          have r46071 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e46072 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
          have e46073 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
          have b46074 := hb (x 17 3)
          have b46075 := hb (x 18 2)
          have b46076 := hb (x 19 13)
          have b46077 := hb (x 20 12)
          clear * - r46071 e46072 e46073 b46074 b46075 b46076 b46077 d46062 d46053 d46058
          omega
        have d46078 : (x 17 11).toNat = 0 := by
          have r46079 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
          have b46080 := hb (x 17 3)
          have b46081 := hb (x 17 11)
          clear * - r46079 b46080 b46081 d46070
          omega
        have d46082 : (x 16 12).toNat = 0 := by
          have r46083 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e46084 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
          have e46085 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
          have b46086 := hb (x 13 3)
          have b46087 := hb (x 14 2)
          have b46088 := hb (x 15 13)
          have b46089 := hb (x 16 12)
          clear * - r46083 e46084 e46085 b46086 b46087 b46088 b46089 d46019 d45944
          omega
        have d46090 : (x 16 1 && x 16 12).toNat = 0 := by
          have r46091 := hand2 (x 16 1) (x 16 12)
          have b46092 := hb (x 16 12)
          have b46093 := hb (x 16 1 && x 16 12)
          clear * - r46091 b46092 b46093 d46082
          omega
        have d46094 : (x 13 12).toNat = 0 := by
          have r46095 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e46096 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
          have e46097 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
          have b46098 := hb (x 10 3)
          have b46099 := hb (x 11 2)
          have b46100 := hb (x 12 13)
          have b46101 := hb (x 13 12)
          clear * - r46095 e46096 e46097 b46098 b46099 b46100 b46101 d45956 d45877
          omega
        have d46102 : (x 13 4).toNat = 0 := by
          have r46103 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
          have b46104 := hb (x 13 4)
          have b46105 := hb (x 13 12)
          clear * - r46103 b46104 b46105 d46094
          omega
        have r46106 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b46107 := hb (x 13 4)
        have b46108 := hb (x 17 11)
        have b46109 := hb (x 16 1 && x 16 12)
        have b46110 := hb (x 15 2 && x 15 13)
        have b46111 := hb (x 14 3 && x 14 14)
        linarith only [r46106, b46107, b46108, b46109, b46110, b46111, d46078, d46090, d46011, d45940, d46102]
    · have f46112 : (x 1 3).toNat = 1 := by rw [h43723]; rfl
      have d46113 : (x 4 12).toNat = 0 := by
        have r46114 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e46115 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e46116 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b46117 := hb (x 1 3)
        have b46118 := hb (x 2 2)
        have b46119 := hb (x 3 13)
        have b46120 := hb (x 4 12)
        clear * - r46114 e46115 e46116 b46117 b46118 b46119 b46120 f46112
        omega
      have d46121 : (x 4 1 && x 4 12).toNat = 0 := by
        have r46122 := hand2 (x 4 1) (x 4 12)
        have b46123 := hb (x 4 12)
        have b46124 := hb (x 4 1 && x 4 12)
        clear * - r46122 b46123 b46124 d46113
        omega
      have d46125 : (x 3 13).toNat = 0 := by
        have r46126 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e46127 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e46128 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b46129 := hb (x 1 3)
        have b46130 := hb (x 2 2)
        have b46131 := hb (x 3 13)
        have b46132 := hb (x 4 12)
        clear * - r46126 e46127 e46128 b46129 b46130 b46131 b46132 d46113 f46112
        omega
      have d46133 : (x 2 2).toNat = 0 := by
        have r46134 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e46135 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e46136 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b46137 := hb (x 1 3)
        have b46138 := hb (x 2 2)
        have b46139 := hb (x 3 13)
        have b46140 := hb (x 4 12)
        clear * - r46134 e46135 e46136 b46137 b46138 b46139 b46140 d46113 d46125 f46112
        omega
      have d46141 : (x 4 13).toNat = 1 := by
        have r46142 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b46143 := hb (x 2 2)
        have b46144 := hb (x 4 13)
        have b46145 := hb (x 3 1 && x 3 14)
        clear * - r46142 b46143 b46144 b46145 g80 d46133
        omega
      have d46146 : (x 5 12).toNat = 0 := by
        have r46147 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e46148 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e46149 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b46150 := hb (x 2 3)
        have b46151 := hb (x 3 2)
        have b46152 := hb (x 4 13)
        have b46153 := hb (x 5 12)
        clear * - r46147 e46148 e46149 b46150 b46151 b46152 b46153 d46141 g22
        omega
      have d46154 : (x 2 3).toNat = 0 := by
        have r46155 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e46156 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e46157 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b46158 := hb (x 2 3)
        have b46159 := hb (x 3 2)
        have b46160 := hb (x 4 13)
        have b46161 := hb (x 5 12)
        clear * - r46155 e46156 e46157 b46158 b46159 b46160 b46161 d46146 d46141 g22
        omega
      have d46162 : (x 2 3 && x 2 14).toNat = 0 := by
        have r46163 := hand1 (x 2 3) (x 2 14)
        have b46164 := hb (x 2 3)
        have b46165 := hb (x 2 3 && x 2 14)
        clear * - r46163 b46164 b46165 d46154
        omega
      have r46166 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b46167 := hb (x 1 4)
      have b46168 := hb (x 5 11)
      have b46169 := hb (x 4 1 && x 4 12)
      have b46170 := hb (x 3 2 && x 3 13)
      have b46171 := hb (x 2 3 && x 2 14)
      linarith only [r46166, b46167, b46168, b46169, b46170, b46171, d43633, d46121, g79, d46162, g19]
  · have f46172 : (x 0 6).toNat = 1 := by rw [h43721]; rfl
    have d46173 : (x 6 8).toNat = 0 := by
      have r46174 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e46175 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e46176 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e46177 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e46178 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e46179 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e46180 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b46181 := hb (x (-1) 7)
      have b46182 := hb (x 0 6)
      have b46183 := hb (x 1 5)
      have b46184 := hb (x 2 4)
      have b46185 := hb (x 3 11)
      have b46186 := hb (x 4 10)
      have b46187 := hb (x 5 9)
      have b46188 := hb (x 6 8)
      clear * - r46174 e46175 e46176 e46177 e46178 e46179 e46180 b46181 b46182 b46183 b46184 b46185 b46186 b46187 b46188 f46172
      omega
    have d46189 : (x 5 9).toNat = 0 := by
      have r46190 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e46191 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e46192 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e46193 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e46194 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e46195 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e46196 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b46197 := hb (x (-1) 7)
      have b46198 := hb (x 0 6)
      have b46199 := hb (x 1 5)
      have b46200 := hb (x 2 4)
      have b46201 := hb (x 3 11)
      have b46202 := hb (x 4 10)
      have b46203 := hb (x 5 9)
      have b46204 := hb (x 6 8)
      clear * - r46190 e46191 e46192 e46193 e46194 e46195 e46196 b46197 b46198 b46199 b46200 b46201 b46202 b46203 b46204 d46173 f46172
      omega
    have d46205 : (x 4 10).toNat = 0 := by
      have r46206 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e46207 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e46208 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e46209 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e46210 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e46211 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e46212 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b46213 := hb (x (-1) 7)
      have b46214 := hb (x 0 6)
      have b46215 := hb (x 1 5)
      have b46216 := hb (x 2 4)
      have b46217 := hb (x 3 11)
      have b46218 := hb (x 4 10)
      have b46219 := hb (x 5 9)
      have b46220 := hb (x 6 8)
      clear * - r46206 e46207 e46208 e46209 e46210 e46211 e46212 b46213 b46214 b46215 b46216 b46217 b46218 b46219 b46220 d46173 d46189 f46172
      omega
    have d46221 : (x 4 1 && x 4 10).toNat = 0 := by
      have r46222 := hand2 (x 4 1) (x 4 10)
      have b46223 := hb (x 4 10)
      have b46224 := hb (x 4 1 && x 4 10)
      clear * - r46222 b46223 b46224 d46205
      omega
    have d46225 : (x 2 3 && x 2 12).toNat = 1 := by
      have r46226 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b46227 := hb (x (-1) 6)
      have b46228 := hb (x 5 9)
      have b46229 := hb (x 4 1 && x 4 10)
      have b46230 := hb (x 3 2 && x 3 11)
      have b46231 := hb (x 2 3 && x 2 12)
      have b46232 := hb (x 1 4 && x 1 13)
      have b46233 := hb (x 0 5 && x 0 14)
      clear * - r46226 b46227 b46228 b46229 b46230 b46231 b46232 b46233 d46189 d46221 g61 g62 g63 g10
      omega
    have d46234 : (x 2 12).toNat = 1 := by
      have r46235 := hand2 (x 2 3) (x 2 12)
      have b46236 := hb (x 2 12)
      have b46237 := hb (x 2 3 && x 2 12)
      clear * - r46235 b46236 b46237 d46225
      omega
    have d46238 : (x 1 13).toNat = 0 := by
      have r46239 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e46240 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e46241 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b46242 := hb (x (-1) 3)
      have b46243 := hb (x 0 2)
      have b46244 := hb (x 1 13)
      have b46245 := hb (x 2 12)
      clear * - r46239 e46240 e46241 b46242 b46243 b46244 b46245 d46234 g12
      omega
    have d46246 : (x 1 5).toNat = 0 := by
      have r46247 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
      have b46248 := hb (x 1 5)
      have b46249 := hb (x 1 13)
      clear * - r46247 b46248 b46249 d46238
      omega
    have d46250 : (x 2 3).toNat = 1 := by
      have r46251 := hand1 (x 2 3) (x 2 12)
      have b46252 := hb (x 2 3)
      have b46253 := hb (x 2 3 && x 2 12)
      clear * - r46251 b46252 b46253 d46225
      omega
    have d46254 : (x 5 12).toNat = 0 := by
      have r46255 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e46256 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e46257 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b46258 := hb (x 2 3)
      have b46259 := hb (x 3 2)
      have b46260 := hb (x 4 13)
      have b46261 := hb (x 5 12)
      clear * - r46255 e46256 e46257 b46258 b46259 b46260 b46261 g22 d46250
      omega
    have d46262 : (x 4 13).toNat = 0 := by
      have r46263 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e46264 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e46265 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b46266 := hb (x 2 3)
      have b46267 := hb (x 3 2)
      have b46268 := hb (x 4 13)
      have b46269 := hb (x 5 12)
      clear * - r46263 e46264 e46265 b46266 b46267 b46268 b46269 d46254 g22 d46250
      omega
    have d46270 : (x 2 2).toNat = 1 := by
      have r46271 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b46272 := hb (x 2 2)
      have b46273 := hb (x 4 13)
      have b46274 := hb (x 3 1 && x 3 14)
      clear * - r46271 b46272 b46273 b46274 d46262 g80
      omega
    have d46275 : (x 4 12).toNat = 0 := by
      have r46276 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e46277 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e46278 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b46279 := hb (x 1 3)
      have b46280 := hb (x 2 2)
      have b46281 := hb (x 3 13)
      have b46282 := hb (x 4 12)
      clear * - r46276 e46277 e46278 b46279 b46280 b46281 b46282 d46270
      omega
    have d46283 : (x 4 2 && x 4 12).toNat = 0 := by
      have r46284 := hand2 (x 4 2) (x 4 12)
      have b46285 := hb (x 4 12)
      have b46286 := hb (x 4 2 && x 4 12)
      clear * - r46284 b46285 b46286 d46275
      omega
    have d46287 : (x 3 13).toNat = 0 := by
      have r46288 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e46289 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e46290 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b46291 := hb (x 1 3)
      have b46292 := hb (x 2 2)
      have b46293 := hb (x 3 13)
      have b46294 := hb (x 4 12)
      clear * - r46288 e46289 e46290 b46291 b46292 b46293 b46294 d46275 d46270
      omega
    have d46295 : (x 3 3 && x 3 13).toNat = 0 := by
      have r46296 := hand2 (x 3 3) (x 3 13)
      have b46297 := hb (x 3 13)
      have b46298 := hb (x 3 3 && x 3 13)
      clear * - r46296 b46297 b46298 d46287
      omega
    have d46299 : (x 2 4 && x 2 14).toNat = 1 := by
      have r46300 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b46301 := hb (x 1 5)
      have b46302 := hb (x 6 10)
      have b46303 := hb (x 5 1 && x 5 11)
      have b46304 := hb (x 4 2 && x 4 12)
      have b46305 := hb (x 3 3 && x 3 13)
      have b46306 := hb (x 2 4 && x 2 14)
      clear * - r46300 b46301 b46302 b46303 b46304 b46305 b46306 d43609 d43649 d46283 d46295 d46246
      omega
    have d46307 : (x 2 4).toNat = 1 := by
      have r46308 := hand1 (x 2 4) (x 2 14)
      have b46309 := hb (x 2 4)
      have b46310 := hb (x 2 4 && x 2 14)
      clear * - r46308 b46309 b46310 d46299
      omega
    have r46311 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e46312 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e46313 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e46314 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e46315 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e46316 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e46317 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b46318 := hb (x (-1) 7)
    have b46319 := hb (x 0 6)
    have b46320 := hb (x 1 5)
    have b46321 := hb (x 2 4)
    have b46322 := hb (x 3 11)
    have b46323 := hb (x 4 10)
    have b46324 := hb (x 5 9)
    have b46325 := hb (x 6 8)
    linarith only [r46311, e46312, e46313, e46314, e46315, e46316, e46317, b46318, b46319, b46320, b46321, b46322, b46323, b46324, b46325, d46173, d46189, d46205, d46307, d46246, f46172]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a01010001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-6) 6).toNat = 0)
    (g1 : (x (-4) 4).toNat = 0)
    (g2 : (x (-3) 11).toNat = 0)
    (g3 : (x (-1) 13).toNat = 0)
    (g4 : (x 0 1).toNat = 1)
    (g5 : (x 0 5).toNat = 0)
    (g6 : (x 0 9).toNat = 0)
    (g7 : (x 0 11).toNat = 0)
    (g8 : (x 0 12).toNat = 0)
    (g9 : (x 0 13).toNat = 1)
    (g10 : (x 1 10).toNat = 0)
    (g11 : (x (-1) 1 && x (-1) 6).toNat = 0)
    (g12 : (x (-4) 4 && x (-4) 9).toNat = 0)
    (g13 : (x (-5) 5 && x (-5) 10).toNat = 0)
    (g14 : (x (-6) 6 && x (-6) 11).toNat = 0)
    (g15 : (x (-7) 7 && x (-7) 12).toNat = 0)
    (g16 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g17 : (x (-4) 4 && x (-4) 13).toNat = 0)
    (g18 : (x (-5) 5 && x (-5) 14).toNat = 0)
    (g19 : (x 0 1 && x 0 11).toNat = 0)
    (g20 : (x (-1) 1 && x (-1) 12).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d46327 : (x 1 12).toNat = 0 := by
    have r46328 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e46329 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e46330 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b46331 := hb (x (-2) 3)
    have b46332 := hb (x (-1) 2)
    have b46333 := hb (x 0 13)
    have b46334 := hb (x 1 12)
    clear * - r46328 e46329 e46330 b46331 b46332 b46333 b46334 g9
    omega
  have d46335 : (x 1 4).toNat = 0 := by
    have r46336 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
    have b46337 := hb (x 1 4)
    have b46338 := hb (x 1 12)
    clear * - r46336 b46337 b46338 d46327
    omega
  have d46339 : (x (-1) 2).toNat = 0 := by
    have r46340 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e46341 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e46342 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b46343 := hb (x (-2) 3)
    have b46344 := hb (x (-1) 2)
    have b46345 := hb (x 0 13)
    have b46346 := hb (x 1 12)
    clear * - r46340 e46341 e46342 b46343 b46344 b46345 b46346 d46327 g9
    omega
  have d46347 : (x (-1) 2 && x (-1) 12).toNat = 0 := by
    have r46348 := hand1 (x (-1) 2) (x (-1) 12)
    have b46349 := hb (x (-1) 2)
    have b46350 := hb (x (-1) 2 && x (-1) 12)
    clear * - r46348 b46349 b46350 d46339
    omega
  have d46351 : (x (-1) 2 && x (-1) 6).toNat = 0 := by
    have r46352 := hand1 (x (-1) 2) (x (-1) 6)
    have b46353 := hb (x (-1) 2)
    have b46354 := hb (x (-1) 2 && x (-1) 6)
    clear * - r46352 b46353 b46354 d46339
    omega
  have d46355 : (x (-1) 10).toNat = 0 := by
    have r46356 : (x (-1) 10).toNat ≤ (x (-1) 2).toNat := himp _ _ (hp10 (-1))
    have b46357 := hb (x (-1) 2)
    have b46358 := hb (x (-1) 10)
    clear * - r46356 b46357 b46358 d46339
    omega
  have d46359 : (x (-2) 3).toNat = 0 := by
    have r46360 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e46361 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e46362 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b46363 := hb (x (-2) 3)
    have b46364 := hb (x (-1) 2)
    have b46365 := hb (x 0 13)
    have b46366 := hb (x 1 12)
    clear * - r46360 e46361 e46362 b46363 b46364 b46365 b46366 d46327 g9 d46339
    omega
  have d46367 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
    have r46368 := hand1 (x (-2) 3) (x (-2) 13)
    have b46369 := hb (x (-2) 3)
    have b46370 := hb (x (-2) 3 && x (-2) 13)
    clear * - r46368 b46369 b46370 d46359
    omega
  have d46371 : (x (-2) 3 && x (-2) 7).toNat = 0 := by
    have r46372 := hand1 (x (-2) 3) (x (-2) 7)
    have b46373 := hb (x (-2) 3)
    have b46374 := hb (x (-2) 3 && x (-2) 7)
    clear * - r46372 b46373 b46374 d46359
    omega
  have d46375 : (x (-2) 11).toNat = 0 := by
    have r46376 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
    have b46377 := hb (x (-2) 3)
    have b46378 := hb (x (-2) 11)
    clear * - r46376 b46377 b46378 d46359
    omega
  have d46379 : (x (-2) 2 && x (-2) 11).toNat = 0 := by
    have r46380 := hand2 (x (-2) 2) (x (-2) 11)
    have b46381 := hb (x (-2) 11)
    have b46382 := hb (x (-2) 2 && x (-2) 11)
    clear * - r46380 b46381 b46382 d46375
    omega
  have d46383 : (x (-3) 3 && x (-3) 12).toNat = 1 := by
    have r46384 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b46385 := hb (x (-6) 6)
    have b46386 := hb (x 0 9)
    have b46387 := hb (x (-1) 1 && x (-1) 10)
    have b46388 := hb (x (-2) 2 && x (-2) 11)
    have b46389 := hb (x (-3) 3 && x (-3) 12)
    have b46390 := hb (x (-4) 4 && x (-4) 13)
    have b46391 := hb (x (-5) 5 && x (-5) 14)
    clear * - r46384 b46385 b46386 b46387 b46388 b46389 b46390 b46391 g6 g16 d46379 g17 g18 g0
    omega
  have d46392 : (x (-3) 12).toNat = 1 := by
    have r46393 := hand2 (x (-3) 3) (x (-3) 12)
    have b46394 := hb (x (-3) 12)
    have b46395 := hb (x (-3) 3 && x (-3) 12)
    clear * - r46393 b46394 b46395 d46383
    omega
  have d46396 : (x (-4) 13).toNat = 0 := by
    have r46397 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e46398 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
    have e46399 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
    have b46400 := hb (x (-6) 3)
    have b46401 := hb (x (-5) 2)
    have b46402 := hb (x (-4) 13)
    have b46403 := hb (x (-3) 12)
    clear * - r46397 e46398 e46399 b46400 b46401 b46402 b46403 d46392
    omega
  have d46404 : (x (-4) 5).toNat = 0 := by
    have r46405 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
    have b46406 := hb (x (-4) 5)
    have b46407 := hb (x (-4) 13)
    clear * - r46405 b46406 b46407 d46396
    omega
  have d46408 : (x (-4) 5 && x (-4) 9).toNat = 0 := by
    have r46409 := hand1 (x (-4) 5) (x (-4) 9)
    have b46410 := hb (x (-4) 5)
    have b46411 := hb (x (-4) 5 && x (-4) 9)
    clear * - r46409 b46410 b46411 d46404
    omega
  have d46412 : (x (-3) 4 && x (-3) 14).toNat = 1 := by
    have r46413 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b46414 := hb (x (-4) 5)
    have b46415 := hb (x 1 10)
    have b46416 := hb (x 0 1 && x 0 11)
    have b46417 := hb (x (-1) 2 && x (-1) 12)
    have b46418 := hb (x (-2) 3 && x (-2) 13)
    have b46419 := hb (x (-3) 4 && x (-3) 14)
    clear * - r46413 b46414 b46415 b46416 b46417 b46418 b46419 g10 g19 d46347 d46367 d46404
    omega
  have d46420 : (x (-3) 14).toNat = 1 := by
    have r46421 := hand2 (x (-3) 4) (x (-3) 14)
    have b46422 := hb (x (-3) 14)
    have b46423 := hb (x (-3) 4 && x (-3) 14)
    clear * - r46421 b46422 b46423 d46412
    omega
  have d46424 : (x (-4) 1).toNat = 0 := by
    have r46425 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b46426 := hb (x (-4) 1)
    have b46427 := hb (x (-3) 14)
    clear * - r46425 b46426 b46427 d46420
    omega
  have d46428 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
    have r46429 := hand1 (x (-4) 1) (x (-4) 14)
    have b46430 := hb (x (-4) 1)
    have b46431 := hb (x (-4) 1 && x (-4) 14)
    clear * - r46429 b46430 b46431 d46424
    omega
  have d46432 : (x (-4) 1 && x (-4) 12).toNat = 0 := by
    have r46433 := hand1 (x (-4) 1) (x (-4) 12)
    have b46434 := hb (x (-4) 1)
    have b46435 := hb (x (-4) 1 && x (-4) 12)
    clear * - r46433 b46434 b46435 d46424
    omega
  have d46436 : (x (-4) 9).toNat = 0 := by
    have r46437 : (x (-4) 9).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp9 (-4))
    have b46438 := hb (x (-4) 1)
    have b46439 := hb (x (-4) 9)
    clear * - r46437 b46438 b46439 d46424
    omega
  have d46440 : (x (-3) 4).toNat = 1 := by
    have r46441 := hand1 (x (-3) 4) (x (-3) 14)
    have b46442 := hb (x (-3) 4)
    have b46443 := hb (x (-3) 4 && x (-3) 14)
    clear * - r46441 b46442 b46443 d46412
    omega
  have d46444 : (x (-5) 2).toNat = 0 := by
    have r46445 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e46446 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
    have e46447 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
    have b46448 := hb (x (-6) 3)
    have b46449 := hb (x (-5) 2)
    have b46450 := hb (x (-4) 13)
    have b46451 := hb (x (-3) 12)
    clear * - r46445 e46446 e46447 b46448 b46449 b46450 b46451 d46392 d46396
    omega
  have d46452 : (x (-5) 2 && x (-5) 13).toNat = 0 := by
    have r46453 := hand1 (x (-5) 2) (x (-5) 13)
    have b46454 := hb (x (-5) 2)
    have b46455 := hb (x (-5) 2 && x (-5) 13)
    clear * - r46453 b46454 b46455 d46444
    omega
  have d46456 : (x (-5) 10).toNat = 0 := by
    have r46457 : (x (-5) 10).toNat ≤ (x (-5) 2).toNat := himp _ _ (hp10 (-5))
    have b46458 := hb (x (-5) 2)
    have b46459 := hb (x (-5) 10)
    clear * - r46457 b46458 b46459 d46444
    omega
  have d46460 : (x (-5) 6 && x (-5) 10).toNat = 0 := by
    have r46461 := hand2 (x (-5) 6) (x (-5) 10)
    have b46462 := hb (x (-5) 10)
    have b46463 := hb (x (-5) 6 && x (-5) 10)
    clear * - r46461 b46462 b46463 d46456
    omega
  have d46464 : (x (-3) 13).toNat = 1 := by
    have r46465 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b46466 := hb (x (-5) 2)
    have b46467 := hb (x (-3) 13)
    have b46468 := hb (x (-4) 1 && x (-4) 14)
    clear * - r46465 b46466 b46467 b46468 d46428 d46444
    omega
  have d46469 : (x (-3) 1).toNat = 1 := by
    have r46470 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
    have b46471 := hb (x (-3) 1)
    have b46472 := hb (x (-3) 13)
    clear * - r46470 b46471 b46472 d46464
    omega
  have d46473 : (x (-2) 14).toNat = 0 := by
    have r46474 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b46475 := hb (x (-3) 1)
    have b46476 := hb (x (-2) 14)
    clear * - r46474 b46475 b46476 d46469
    omega
  have d46477 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
    have r46478 := hand2 (x (-2) 1) (x (-2) 14)
    have b46479 := hb (x (-2) 14)
    have b46480 := hb (x (-2) 1 && x (-2) 14)
    clear * - r46478 b46479 b46480 d46473
    omega
  have d46481 : (x (-3) 2).toNat = 1 := by
    have r46482 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b46483 := hb (x (-3) 2)
    have b46484 := hb (x (-1) 13)
    have b46485 := hb (x (-2) 1 && x (-2) 14)
    clear * - r46482 b46483 b46484 b46485 g3 d46477
    omega
  have d46486 : (x (-1) 12).toNat = 0 := by
    have r46487 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e46488 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e46489 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b46490 := hb (x (-4) 3)
    have b46491 := hb (x (-3) 2)
    have b46492 := hb (x (-2) 13)
    have b46493 := hb (x (-1) 12)
    clear * - r46487 e46488 e46489 b46490 b46491 b46492 b46493 d46481
    omega
  have d46494 : (x (-2) 13).toNat = 0 := by
    have r46495 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e46496 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e46497 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b46498 := hb (x (-4) 3)
    have b46499 := hb (x (-3) 2)
    have b46500 := hb (x (-2) 13)
    have b46501 := hb (x (-1) 12)
    clear * - r46495 e46496 e46497 b46498 b46499 b46500 b46501 d46486 d46481
    omega
  have d46502 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
    have r46503 := hand2 (x (-2) 2) (x (-2) 13)
    have b46504 := hb (x (-2) 13)
    have b46505 := hb (x (-2) 2 && x (-2) 13)
    clear * - r46503 b46504 b46505 d46494
    omega
  have d46506 : (x (-3) 3 && x (-3) 14).toNat = 1 := by
    have r46507 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b46508 := hb (x (-4) 4)
    have b46509 := hb (x 0 11)
    have b46510 := hb (x (-1) 1 && x (-1) 12)
    have b46511 := hb (x (-2) 2 && x (-2) 13)
    have b46512 := hb (x (-3) 3 && x (-3) 14)
    clear * - r46507 b46508 b46509 b46510 b46511 b46512 g7 g20 d46502 g1
    omega
  have d46513 : (x (-3) 3).toNat = 1 := by
    have r46514 := hand1 (x (-3) 3) (x (-3) 14)
    have b46515 := hb (x (-3) 3)
    have b46516 := hb (x (-3) 3 && x (-3) 14)
    clear * - r46514 b46515 b46516 d46506
    omega
  have d46517 : (x (-2) 2).toNat = 0 := by
    have r46518 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e46519 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e46520 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b46521 := hb (x (-3) 3)
    have b46522 := hb (x (-2) 2)
    have b46523 := hb (x (-1) 13)
    have b46524 := hb (x 0 12)
    clear * - r46518 e46519 e46520 b46521 b46522 b46523 b46524 g8 g3 d46513
    omega
  have d46525 : (x (-2) 2 && x (-2) 7).toNat = 0 := by
    have r46526 := hand1 (x (-2) 2) (x (-2) 7)
    have b46527 := hb (x (-2) 2)
    have b46528 := hb (x (-2) 2 && x (-2) 7)
    clear * - r46526 b46527 b46528 d46517
    omega
  have d46529 : (x (-6) 3).toNat = 0 := by
    have r46530 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e46531 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
    have e46532 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
    have b46533 := hb (x (-6) 3)
    have b46534 := hb (x (-5) 2)
    have b46535 := hb (x (-4) 13)
    have b46536 := hb (x (-3) 12)
    clear * - r46530 e46531 e46532 b46533 b46534 b46535 b46536 d46392 d46396 d46444
    omega
  have d46537 : (x (-6) 3 && x (-6) 14).toNat = 0 := by
    have r46538 := hand1 (x (-6) 3) (x (-6) 14)
    have b46539 := hb (x (-6) 3)
    have b46540 := hb (x (-6) 3 && x (-6) 14)
    clear * - r46538 b46539 b46540 d46529
    omega
  have d46541 : (x (-7) 4).toNat = 1 := by
    have r46542 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := by have q := hcov11 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b46543 := hb (x (-7) 4)
    have b46544 := hb (x (-3) 11)
    have b46545 := hb (x (-4) 1 && x (-4) 12)
    have b46546 := hb (x (-5) 2 && x (-5) 13)
    have b46547 := hb (x (-6) 3 && x (-6) 14)
    clear * - r46542 b46543 b46544 b46545 b46546 b46547 g2 d46432 d46452 d46537
    omega
  have d46548 : (x (-7) 12).toNat = 1 := by
    have r46549 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
    have b46550 := hb (x (-7) 4)
    have b46551 := hb (x (-7) 12)
    clear * - r46549 b46550 b46551 d46541
    omega
  have d46552 : (x (-8) 13).toNat = 0 := by
    have r46553 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e46554 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
    have e46555 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
    have b46556 := hb (x (-10) 3)
    have b46557 := hb (x (-9) 2)
    have b46558 := hb (x (-8) 13)
    have b46559 := hb (x (-7) 12)
    clear * - r46553 e46554 e46555 b46556 b46557 b46558 b46559 d46548
    omega
  have d46560 : (x (-8) 8 && x (-8) 13).toNat = 0 := by
    have r46561 := hand2 (x (-8) 8) (x (-8) 13)
    have b46562 := hb (x (-8) 13)
    have b46563 := hb (x (-8) 8 && x (-8) 13)
    clear * - r46561 b46562 b46563 d46552
    omega
  have d46564 : (x (-8) 9 && x (-8) 13).toNat = 0 := by
    have r46565 := hand2 (x (-8) 9) (x (-8) 13)
    have b46566 := hb (x (-8) 13)
    have b46567 := hb (x (-8) 9 && x (-8) 13)
    clear * - r46565 b46566 b46567 d46552
    omega
  have d46568 : (x (-8) 5).toNat = 0 := by
    have r46569 : (x (-8) 5).toNat ≤ (x (-8) 13).toNat := himp _ _ (hp5 (-8))
    have b46570 := hb (x (-8) 5)
    have b46571 := hb (x (-8) 13)
    clear * - r46569 b46570 b46571 d46552
    omega
  have d46572 : (x (-9) 2).toNat = 0 := by
    have r46573 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e46574 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
    have e46575 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
    have b46576 := hb (x (-10) 3)
    have b46577 := hb (x (-9) 2)
    have b46578 := hb (x (-8) 13)
    have b46579 := hb (x (-7) 12)
    clear * - r46573 e46574 e46575 b46576 b46577 b46578 b46579 d46548 d46552
    omega
  have d46580 : (x (-9) 10).toNat = 0 := by
    have r46581 : (x (-9) 10).toNat ≤ (x (-9) 2).toNat := himp _ _ (hp10 (-9))
    have b46582 := hb (x (-9) 2)
    have b46583 := hb (x (-9) 10)
    clear * - r46581 b46582 b46583 d46572
    omega
  have d46584 : (x (-9) 1 && x (-9) 10).toNat = 0 := by
    have r46585 := hand2 (x (-9) 1) (x (-9) 10)
    have b46586 := hb (x (-9) 10)
    have b46587 := hb (x (-9) 1 && x (-9) 10)
    clear * - r46585 b46586 b46587 d46580
    omega
  have d46588 : (x (-10) 3).toNat = 0 := by
    have r46589 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e46590 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
    have e46591 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
    have b46592 := hb (x (-10) 3)
    have b46593 := hb (x (-9) 2)
    have b46594 := hb (x (-8) 13)
    have b46595 := hb (x (-7) 12)
    clear * - r46589 e46590 e46591 b46592 b46593 b46594 b46595 d46548 d46552 d46572
    omega
  have d46596 : (x (-10) 11).toNat = 0 := by
    have r46597 : (x (-10) 11).toNat ≤ (x (-10) 3).toNat := himp _ _ (hp11 (-10))
    have b46598 := hb (x (-10) 3)
    have b46599 := hb (x (-10) 11)
    clear * - r46597 b46598 b46599 d46588
    omega
  have d46600 : (x (-10) 2 && x (-10) 11).toNat = 0 := by
    have r46601 := hand2 (x (-10) 2) (x (-10) 11)
    have b46602 := hb (x (-10) 11)
    have b46603 := hb (x (-10) 2 && x (-10) 11)
    clear * - r46601 b46602 b46603 d46596
    omega
  have d46604 : (x (-6) 11).toNat = 0 := by
    have r46605 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
    have b46606 := hb (x (-6) 3)
    have b46607 := hb (x (-6) 11)
    clear * - r46605 b46606 b46607 d46529
    omega
  have d46608 : (x (-6) 7 && x (-6) 11).toNat = 0 := by
    have r46609 := hand2 (x (-6) 7) (x (-6) 11)
    have b46610 := hb (x (-6) 11)
    have b46611 := hb (x (-6) 7 && x (-6) 11)
    clear * - r46609 b46610 b46611 d46604
    omega
  have d46612 : (x 1 8).toNat = 0 := by
    have r46613 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e46614 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e46615 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e46616 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e46617 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e46618 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e46619 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b46620 := hb (x (-6) 7)
    have b46621 := hb (x (-5) 6)
    have b46622 := hb (x (-4) 5)
    have b46623 := hb (x (-3) 4)
    have b46624 := hb (x (-2) 11)
    have b46625 := hb (x (-1) 10)
    have b46626 := hb (x 0 9)
    have b46627 := hb (x 1 8)
    clear * - r46613 e46614 e46615 e46616 e46617 e46618 e46619 b46620 b46621 b46622 b46623 b46624 b46625 b46626 b46627 g6 d46355 d46375 d46440 d46404
    omega
  have d46628 : (x (-5) 6).toNat = 0 := by
    have r46629 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e46630 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e46631 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e46632 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e46633 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e46634 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e46635 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b46636 := hb (x (-6) 7)
    have b46637 := hb (x (-5) 6)
    have b46638 := hb (x (-4) 5)
    have b46639 := hb (x (-3) 4)
    have b46640 := hb (x (-2) 11)
    have b46641 := hb (x (-1) 10)
    have b46642 := hb (x 0 9)
    have b46643 := hb (x 1 8)
    clear * - r46629 e46630 e46631 e46632 e46633 e46634 e46635 b46636 b46637 b46638 b46639 b46640 b46641 b46642 b46643 d46612 g6 d46355 d46375 d46440 d46404
    omega
  have d46644 : (x (-6) 7).toNat = 0 := by
    have r46645 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e46646 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e46647 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e46648 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e46649 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e46650 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e46651 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b46652 := hb (x (-6) 7)
    have b46653 := hb (x (-5) 6)
    have b46654 := hb (x (-4) 5)
    have b46655 := hb (x (-3) 4)
    have b46656 := hb (x (-2) 11)
    have b46657 := hb (x (-1) 10)
    have b46658 := hb (x 0 9)
    have b46659 := hb (x 1 8)
    clear * - r46645 e46646 e46647 e46648 e46649 e46650 e46651 b46652 b46653 b46654 b46655 b46656 b46657 b46658 b46659 d46612 g6 d46355 d46375 d46440 d46404 d46628
    omega
  have d46660 : (x (-3) 8).toNat = 0 := by
    have r46661 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e46662 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
    have e46663 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
    have e46664 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
    have e46665 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
    have e46666 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
    have e46667 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
    have b46668 := hb (x (-10) 7)
    have b46669 := hb (x (-9) 6)
    have b46670 := hb (x (-8) 5)
    have b46671 := hb (x (-7) 4)
    have b46672 := hb (x (-6) 11)
    have b46673 := hb (x (-5) 10)
    have b46674 := hb (x (-4) 9)
    have b46675 := hb (x (-3) 8)
    clear * - r46661 e46662 e46663 e46664 e46665 e46666 e46667 b46668 b46669 b46670 b46671 b46672 b46673 b46674 b46675 d46436 d46456 d46604 d46541 d46568
    omega
  have d46676 : (x (-3) 3 && x (-3) 8).toNat = 0 := by
    have r46677 := hand2 (x (-3) 3) (x (-3) 8)
    have b46678 := hb (x (-3) 8)
    have b46679 := hb (x (-3) 3 && x (-3) 8)
    clear * - r46677 b46678 b46679 d46660
    omega
  have d46680 : (x (-3) 4 && x (-3) 8).toNat = 0 := by
    have r46681 := hand2 (x (-3) 4) (x (-3) 8)
    have b46682 := hb (x (-3) 8)
    have b46683 := hb (x (-3) 4 && x (-3) 8)
    clear * - r46681 b46682 b46683 d46660
    omega
  have d46684 : (x (-7) 8 && x (-7) 12).toNat = 1 := by
    have r46685 : 1 ≤ (x 1 4).toNat + (x 0 1 && x 0 5).toNat + (x (-1) 2 && x (-1) 6).toNat + (x (-2) 3 && x (-2) 7).toNat + (x (-3) 4 && x (-3) 8).toNat + (x (-4) 5 && x (-4) 9).toNat + (x (-5) 6 && x (-5) 10).toNat + (x (-6) 7 && x (-6) 11).toNat + (x (-7) 8 && x (-7) 12).toNat + (x (-8) 9 && x (-8) 13).toNat + (x (-9) 10 && x (-9) 14).toNat + (x (-10) 11).toNat := by have q := hcov4 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e46686 : (x 0 1 && x 0 5).toNat = (x 0 5).toNat := handr _ _ (fun h => hp13 0 (hp5 0 (h)))
    have e46687 : (x (-9) 10 && x (-9) 14).toNat = (x (-9) 10).toNat := handl _ _ (fun h => hp2 (-9) (hp10 (-9) (h)))
    have b46688 := hb (x (-10) 11)
    have b46689 := hb (x (-9) 10)
    have b46690 := hb (x 0 5)
    have b46691 := hb (x 1 4)
    have b46692 := hb (x (-1) 2 && x (-1) 6)
    have b46693 := hb (x (-2) 3 && x (-2) 7)
    have b46694 := hb (x (-3) 4 && x (-3) 8)
    have b46695 := hb (x (-4) 5 && x (-4) 9)
    have b46696 := hb (x (-5) 6 && x (-5) 10)
    have b46697 := hb (x (-6) 7 && x (-6) 11)
    have b46698 := hb (x (-7) 8 && x (-7) 12)
    have b46699 := hb (x (-8) 9 && x (-8) 13)
    clear * - r46685 e46686 e46687 b46688 b46689 b46690 b46691 b46692 b46693 b46694 b46695 b46696 b46697 b46698 b46699 d46335 g5 d46351 d46371 d46680 d46408 d46460 d46608 d46564 d46580 d46596
    omega
  have d46700 : (x (-7) 8).toNat = 1 := by
    have r46701 := hand1 (x (-7) 8) (x (-7) 12)
    have b46702 := hb (x (-7) 8)
    have b46703 := hb (x (-7) 8 && x (-7) 12)
    clear * - r46701 b46702 b46703 d46684
    omega
  have d46704 : (x (-8) 9).toNat = 0 := by
    have r46705 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e46706 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
    have e46707 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
    have e46708 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
    have e46709 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
    have e46710 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
    have e46711 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
    have b46712 := hb (x (-14) 7)
    have b46713 := hb (x (-13) 6)
    have b46714 := hb (x (-12) 5)
    have b46715 := hb (x (-11) 4)
    have b46716 := hb (x (-10) 11)
    have b46717 := hb (x (-9) 10)
    have b46718 := hb (x (-8) 9)
    have b46719 := hb (x (-7) 8)
    clear * - r46705 e46706 e46707 e46708 e46709 e46710 e46711 b46712 b46713 b46714 b46715 b46716 b46717 b46718 b46719 d46700 d46580 d46596
    omega
  have d46720 : (x (-11) 12).toNat = 0 := by
    have r46721 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b46722 := hb (x (-13) 14)
    have b46723 := hb (x (-12) 13)
    have b46724 := hb (x (-11) 12)
    have b46725 := hb (x (-10) 11)
    have b46726 := hb (x (-9) 10)
    have b46727 := hb (x (-8) 9)
    have b46728 := hb (x (-7) 8)
    have b46729 := hb (x (-6) 7)
    have b46730 := hb (x (-5) 6)
    have b46731 := hb (x (-4) 5)
    have b46732 := hb (x (-3) 4)
    have b46733 := hb (x (-2) 3)
    have b46734 := hb (x (-1) 2)
    have b46735 := hb (x 0 1)
    clear * - r46721 b46722 b46723 b46724 b46725 b46726 b46727 b46728 b46729 b46730 b46731 b46732 b46733 b46734 b46735 g4 d46339 d46359 d46440 d46404 d46628 d46644 d46700 d46704 d46580 d46596
    omega
  have d46736 : (x (-11) 3 && x (-11) 12).toNat = 0 := by
    have r46737 := hand2 (x (-11) 3) (x (-11) 12)
    have b46738 := hb (x (-11) 12)
    have b46739 := hb (x (-11) 3 && x (-11) 12)
    clear * - r46737 b46738 b46739 d46720
    omega
  have d46740 : (x (-12) 13).toNat = 0 := by
    have r46741 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b46742 := hb (x (-13) 14)
    have b46743 := hb (x (-12) 13)
    have b46744 := hb (x (-11) 12)
    have b46745 := hb (x (-10) 11)
    have b46746 := hb (x (-9) 10)
    have b46747 := hb (x (-8) 9)
    have b46748 := hb (x (-7) 8)
    have b46749 := hb (x (-6) 7)
    have b46750 := hb (x (-5) 6)
    have b46751 := hb (x (-4) 5)
    have b46752 := hb (x (-3) 4)
    have b46753 := hb (x (-2) 3)
    have b46754 := hb (x (-1) 2)
    have b46755 := hb (x 0 1)
    clear * - r46741 b46742 b46743 b46744 b46745 b46746 b46747 b46748 b46749 b46750 b46751 b46752 b46753 b46754 b46755 g4 d46339 d46359 d46440 d46404 d46628 d46644 d46700 d46704 d46580 d46596 d46720
    omega
  have d46756 : (x (-12) 4 && x (-12) 13).toNat = 0 := by
    have r46757 := hand2 (x (-12) 4) (x (-12) 13)
    have b46758 := hb (x (-12) 13)
    have b46759 := hb (x (-12) 4 && x (-12) 13)
    clear * - r46757 b46758 b46759 d46740
    omega
  have d46760 : (x (-13) 14).toNat = 0 := by
    have r46761 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b46762 := hb (x (-13) 14)
    have b46763 := hb (x (-12) 13)
    have b46764 := hb (x (-11) 12)
    have b46765 := hb (x (-10) 11)
    have b46766 := hb (x (-9) 10)
    have b46767 := hb (x (-8) 9)
    have b46768 := hb (x (-7) 8)
    have b46769 := hb (x (-6) 7)
    have b46770 := hb (x (-5) 6)
    have b46771 := hb (x (-4) 5)
    have b46772 := hb (x (-3) 4)
    have b46773 := hb (x (-2) 3)
    have b46774 := hb (x (-1) 2)
    have b46775 := hb (x 0 1)
    clear * - r46761 b46762 b46763 b46764 b46765 b46766 b46767 b46768 b46769 b46770 b46771 b46772 b46773 b46774 b46775 g4 d46339 d46359 d46440 d46404 d46628 d46644 d46700 d46704 d46580 d46596 d46720 d46740
    omega
  have d46776 : (x (-13) 1 && x (-13) 14).toNat = 0 := by
    have r46777 := hand2 (x (-13) 1) (x (-13) 14)
    have b46778 := hb (x (-13) 14)
    have b46779 := hb (x (-13) 1 && x (-13) 14)
    clear * - r46777 b46778 b46779 d46760
    omega
  have d46780 : (x (-14) 2).toNat = 1 := by
    have r46781 : 1 ≤ (x (-12) 13).toNat + (x (-13) 1 && x (-13) 14).toNat + (x (-14) 2).toNat := by have q := hcov13 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b46782 := hb (x (-14) 2)
    have b46783 := hb (x (-12) 13)
    have b46784 := hb (x (-13) 1 && x (-13) 14)
    clear * - r46781 b46782 b46783 b46784 d46740 d46776
    omega
  have d46785 : (x (-12) 12).toNat = 0 := by
    have r46786 : (x (-12) 12).toNat + (x (-13) 1 && x (-13) 13).toNat + (x (-14) 2 && x (-14) 14).toNat + (x (-15) 3).toNat = 1 := by have q := hd12 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e46787 : (x (-13) 1 && x (-13) 13).toNat = (x (-13) 13).toNat := handr _ _ (fun h => hp13 (-13) (h))
    have e46788 : (x (-14) 2 && x (-14) 14).toNat = (x (-14) 2).toNat := handl _ _ (fun h => hp2 (-14) (h))
    have b46789 := hb (x (-15) 3)
    have b46790 := hb (x (-14) 2)
    have b46791 := hb (x (-13) 13)
    have b46792 := hb (x (-12) 12)
    clear * - r46786 e46787 e46788 b46789 b46790 b46791 b46792 d46780
    omega
  have d46793 : (x (-12) 4).toNat = 0 := by
    have r46794 : (x (-12) 4).toNat ≤ (x (-12) 12).toNat := himp _ _ (hp4 (-12))
    have b46795 := hb (x (-12) 4)
    have b46796 := hb (x (-12) 12)
    clear * - r46794 b46795 b46796 d46785
    omega
  have d46797 : (x (-13) 13).toNat = 0 := by
    have r46798 : (x (-12) 12).toNat + (x (-13) 1 && x (-13) 13).toNat + (x (-14) 2 && x (-14) 14).toNat + (x (-15) 3).toNat = 1 := by have q := hd12 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e46799 : (x (-13) 1 && x (-13) 13).toNat = (x (-13) 13).toNat := handr _ _ (fun h => hp13 (-13) (h))
    have e46800 : (x (-14) 2 && x (-14) 14).toNat = (x (-14) 2).toNat := handl _ _ (fun h => hp2 (-14) (h))
    have b46801 := hb (x (-15) 3)
    have b46802 := hb (x (-14) 2)
    have b46803 := hb (x (-13) 13)
    have b46804 := hb (x (-12) 12)
    clear * - r46798 e46799 e46800 b46801 b46802 b46803 b46804 d46785 d46780
    omega
  have d46805 : (x (-13) 5).toNat = 0 := by
    have r46806 : (x (-13) 5).toNat ≤ (x (-13) 13).toNat := himp _ _ (hp5 (-13))
    have b46807 := hb (x (-13) 5)
    have b46808 := hb (x (-13) 13)
    clear * - r46806 b46807 b46808 d46797
    omega
  have d46809 : (x (-13) 5 && x (-13) 14).toNat = 0 := by
    have r46810 := hand1 (x (-13) 5) (x (-13) 14)
    have b46811 := hb (x (-13) 5)
    have b46812 := hb (x (-13) 5 && x (-13) 14)
    clear * - r46810 b46811 b46812 d46805
    omega
  have d46813 : (x (-14) 6).toNat = 1 := by
    have r46814 : 1 ≤ (x (-8) 9).toNat + (x (-9) 1 && x (-9) 10).toNat + (x (-10) 2 && x (-10) 11).toNat + (x (-11) 3 && x (-11) 12).toNat + (x (-12) 4 && x (-12) 13).toNat + (x (-13) 5 && x (-13) 14).toNat + (x (-14) 6).toNat := by have q := hcov9 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b46815 := hb (x (-14) 6)
    have b46816 := hb (x (-8) 9)
    have b46817 := hb (x (-9) 1 && x (-9) 10)
    have b46818 := hb (x (-10) 2 && x (-10) 11)
    have b46819 := hb (x (-11) 3 && x (-11) 12)
    have b46820 := hb (x (-12) 4 && x (-12) 13)
    have b46821 := hb (x (-13) 5 && x (-13) 14)
    clear * - r46814 b46815 b46816 b46817 b46818 b46819 b46820 b46821 d46704 d46584 d46600 d46736 d46756 d46809
    omega
  have d46822 : (x (-8) 8).toNat = 0 := by
    have r46823 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e46824 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
    have e46825 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
    have e46826 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
    have e46827 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
    have e46828 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
    have e46829 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
    have b46830 := hb (x (-15) 7)
    have b46831 := hb (x (-14) 6)
    have b46832 := hb (x (-13) 5)
    have b46833 := hb (x (-12) 4)
    have b46834 := hb (x (-11) 11)
    have b46835 := hb (x (-10) 10)
    have b46836 := hb (x (-9) 9)
    have b46837 := hb (x (-8) 8)
    clear * - r46823 e46824 e46825 e46826 e46827 e46828 e46829 b46830 b46831 b46832 b46833 b46834 b46835 b46836 b46837 d46793 d46805 d46813
    omega
  have d46838 : (x (-9) 9).toNat = 0 := by
    have r46839 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e46840 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
    have e46841 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
    have e46842 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
    have e46843 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
    have e46844 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
    have e46845 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
    have b46846 := hb (x (-15) 7)
    have b46847 := hb (x (-14) 6)
    have b46848 := hb (x (-13) 5)
    have b46849 := hb (x (-12) 4)
    have b46850 := hb (x (-11) 11)
    have b46851 := hb (x (-10) 10)
    have b46852 := hb (x (-9) 9)
    have b46853 := hb (x (-8) 8)
    clear * - r46839 e46840 e46841 e46842 e46843 e46844 e46845 b46846 b46847 b46848 b46849 b46850 b46851 b46852 b46853 d46822 d46793 d46805 d46813
    omega
  have d46854 : (x (-9) 9 && x (-9) 14).toNat = 0 := by
    have r46855 := hand1 (x (-9) 9) (x (-9) 14)
    have b46856 := hb (x (-9) 9)
    have b46857 := hb (x (-9) 9 && x (-9) 14)
    clear * - r46855 b46856 b46857 d46838
    omega
  have d46858 : (x (-10) 10).toNat = 1 := by
    have r46859 : 1 ≤ (x 0 5).toNat + (x (-1) 1 && x (-1) 6).toNat + (x (-2) 2 && x (-2) 7).toNat + (x (-3) 3 && x (-3) 8).toNat + (x (-4) 4 && x (-4) 9).toNat + (x (-5) 5 && x (-5) 10).toNat + (x (-6) 6 && x (-6) 11).toNat + (x (-7) 7 && x (-7) 12).toNat + (x (-8) 8 && x (-8) 13).toNat + (x (-9) 9 && x (-9) 14).toNat + (x (-10) 10).toNat := by have q := hcov5 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b46860 := hb (x (-10) 10)
    have b46861 := hb (x 0 5)
    have b46862 := hb (x (-1) 1 && x (-1) 6)
    have b46863 := hb (x (-2) 2 && x (-2) 7)
    have b46864 := hb (x (-3) 3 && x (-3) 8)
    have b46865 := hb (x (-4) 4 && x (-4) 9)
    have b46866 := hb (x (-5) 5 && x (-5) 10)
    have b46867 := hb (x (-6) 6 && x (-6) 11)
    have b46868 := hb (x (-7) 7 && x (-7) 12)
    have b46869 := hb (x (-8) 8 && x (-8) 13)
    have b46870 := hb (x (-9) 9 && x (-9) 14)
    clear * - r46859 b46860 b46861 b46862 b46863 b46864 b46865 b46866 b46867 b46868 b46869 b46870 g5 g11 d46525 d46676 g12 g13 g14 g15 d46560 d46854
    omega
  have d46871 : (x (-10) 2).toNat = 1 := by
    have r46872 : (x (-10) 10).toNat ≤ (x (-10) 2).toNat := himp _ _ (hp10 (-10))
    have b46873 := hb (x (-10) 2)
    have b46874 := hb (x (-10) 10)
    clear * - r46872 b46873 b46874 d46858
    omega
  have d46875 : (x (-8) 12).toNat = 0 := by
    have r46876 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e46877 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
    have e46878 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
    have b46879 := hb (x (-11) 3)
    have b46880 := hb (x (-10) 2)
    have b46881 := hb (x (-9) 13)
    have b46882 := hb (x (-8) 12)
    clear * - r46876 e46877 e46878 b46879 b46880 b46881 b46882 d46871
    omega
  have d46883 : (x (-9) 13).toNat = 0 := by
    have r46884 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e46885 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
    have e46886 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
    have b46887 := hb (x (-11) 3)
    have b46888 := hb (x (-10) 2)
    have b46889 := hb (x (-9) 13)
    have b46890 := hb (x (-8) 12)
    clear * - r46884 e46885 e46886 b46887 b46888 b46889 b46890 d46875 d46871
    omega
  have d46891 : (x (-11) 3).toNat = 0 := by
    have r46892 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e46893 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
    have e46894 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
    have b46895 := hb (x (-11) 3)
    have b46896 := hb (x (-10) 2)
    have b46897 := hb (x (-9) 13)
    have b46898 := hb (x (-8) 12)
    clear * - r46892 e46893 e46894 b46895 b46896 b46897 b46898 d46875 d46883 d46871
    omega
  have d46899 : (x (-11) 11).toNat = 0 := by
    have r46900 : (x (-11) 11).toNat ≤ (x (-11) 3).toNat := himp _ _ (hp11 (-11))
    have b46901 := hb (x (-11) 3)
    have b46902 := hb (x (-11) 11)
    clear * - r46900 b46901 b46902 d46891
    omega
  have r46903 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e46904 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
  have e46905 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
  have e46906 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
  have e46907 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
  have e46908 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
  have e46909 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
  have b46910 := hb (x (-15) 7)
  have b46911 := hb (x (-14) 6)
  have b46912 := hb (x (-13) 5)
  have b46913 := hb (x (-12) 4)
  have b46914 := hb (x (-11) 11)
  have b46915 := hb (x (-10) 10)
  have b46916 := hb (x (-9) 9)
  have b46917 := hb (x (-8) 8)
  linarith only [r46903, e46904, e46905, e46906, e46907, e46908, e46909, b46910, b46911, b46912, b46913, b46914, b46915, b46916, b46917, d46822, d46838, d46858, d46899, d46793, d46805, d46813]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a0101001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-4) 4).toNat = 0)
    (g1 : (x (-1) 13).toNat = 0)
    (g2 : (x 0 11).toNat = 0)
    (g3 : (x 0 12).toNat = 1)
    (g4 : (x (-1) 1 && x (-1) 12).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d46919 : (x (-2) 2).toNat = 0 := by
    have r46920 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e46921 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e46922 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b46923 := hb (x (-3) 3)
    have b46924 := hb (x (-2) 2)
    have b46925 := hb (x (-1) 13)
    have b46926 := hb (x 0 12)
    clear * - r46920 e46921 e46922 b46923 b46924 b46925 b46926 g3 g1
    omega
  have d46927 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
    have r46928 := hand1 (x (-2) 2) (x (-2) 13)
    have b46929 := hb (x (-2) 2)
    have b46930 := hb (x (-2) 2 && x (-2) 13)
    clear * - r46928 b46929 b46930 d46919
    omega
  have d46931 : (x (-3) 3).toNat = 0 := by
    have r46932 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e46933 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e46934 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b46935 := hb (x (-3) 3)
    have b46936 := hb (x (-2) 2)
    have b46937 := hb (x (-1) 13)
    have b46938 := hb (x 0 12)
    clear * - r46932 e46933 e46934 b46935 b46936 b46937 b46938 g3 g1 d46919
    omega
  have d46939 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
    have r46940 := hand1 (x (-3) 3) (x (-3) 14)
    have b46941 := hb (x (-3) 3)
    have b46942 := hb (x (-3) 3 && x (-3) 14)
    clear * - r46940 b46941 b46942 d46931
    omega
  have r46943 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have b46944 := hb (x (-4) 4)
  have b46945 := hb (x 0 11)
  have b46946 := hb (x (-1) 1 && x (-1) 12)
  have b46947 := hb (x (-2) 2 && x (-2) 13)
  have b46948 := hb (x (-3) 3 && x (-3) 14)
  linarith only [r46943, b46944, b46945, b46946, b46947, b46948, g2, g4, d46927, d46939, g0]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a010101 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-6) 6).toNat = 0)
    (g1 : (x (-1) 13).toNat = 0)
    (g2 : (x 0 5).toNat = 1)
    (g3 : (x 0 9).toNat = 0)
    (g4 : (x 1 10).toNat = 0)
    (g5 : (x 3 10).toNat = 0)
    (g6 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g7 : (x (-4) 4 && x (-4) 13).toNat = 0)
    (g8 : (x (-5) 5 && x (-5) 14).toNat = 0)
    (g9 : (x 0 1 && x 0 11).toNat = 0)
    (g10 : (x 1 2 && x 1 12).toNat = 0)
    (g11 : (x 0 3 && x 0 13).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d46950 : (x 0 13).toNat = 1 := by
    have r46951 : (x 0 5).toNat ≤ (x 0 13).toNat := himp _ _ (hp5 0)
    have b46952 := hb (x 0 5)
    have b46953 := hb (x 0 13)
    clear * - r46951 b46952 b46953 g2
    omega
  have d46954 : (x 1 12).toNat = 0 := by
    have r46955 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e46956 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e46957 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b46958 := hb (x (-2) 3)
    have b46959 := hb (x (-1) 2)
    have b46960 := hb (x 0 13)
    have b46961 := hb (x 1 12)
    clear * - r46955 e46956 e46957 b46958 b46959 b46960 b46961 d46950
    omega
  have d46962 : (x 1 4).toNat = 0 := by
    have r46963 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
    have b46964 := hb (x 1 4)
    have b46965 := hb (x 1 12)
    clear * - r46963 b46964 b46965 d46954
    omega
  have d46966 : (x (-1) 2).toNat = 0 := by
    have r46967 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e46968 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e46969 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b46970 := hb (x (-2) 3)
    have b46971 := hb (x (-1) 2)
    have b46972 := hb (x 0 13)
    have b46973 := hb (x 1 12)
    clear * - r46967 e46968 e46969 b46970 b46971 b46972 b46973 d46954 d46950
    omega
  have d46974 : (x (-1) 2 && x (-1) 12).toNat = 0 := by
    have r46975 := hand1 (x (-1) 2) (x (-1) 12)
    have b46976 := hb (x (-1) 2)
    have b46977 := hb (x (-1) 2 && x (-1) 12)
    clear * - r46975 b46976 b46977 d46966
    omega
  have d46978 : (x (-2) 3).toNat = 0 := by
    have r46979 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e46980 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e46981 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b46982 := hb (x (-2) 3)
    have b46983 := hb (x (-1) 2)
    have b46984 := hb (x 0 13)
    have b46985 := hb (x 1 12)
    clear * - r46979 e46980 e46981 b46982 b46983 b46984 b46985 d46954 d46950 d46966
    omega
  have d46986 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
    have r46987 := hand1 (x (-2) 3) (x (-2) 13)
    have b46988 := hb (x (-2) 3)
    have b46989 := hb (x (-2) 3 && x (-2) 13)
    clear * - r46987 b46988 b46989 d46978
    omega
  have d46990 : (x (-2) 11).toNat = 0 := by
    have r46991 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
    have b46992 := hb (x (-2) 3)
    have b46993 := hb (x (-2) 11)
    clear * - r46991 b46992 b46993 d46978
    omega
  have d46994 : (x (-2) 2 && x (-2) 11).toNat = 0 := by
    have r46995 := hand2 (x (-2) 2) (x (-2) 11)
    have b46996 := hb (x (-2) 11)
    have b46997 := hb (x (-2) 2 && x (-2) 11)
    clear * - r46995 b46996 b46997 d46990
    omega
  have d46998 : (x (-3) 3 && x (-3) 12).toNat = 1 := by
    have r46999 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b47000 := hb (x (-6) 6)
    have b47001 := hb (x 0 9)
    have b47002 := hb (x (-1) 1 && x (-1) 10)
    have b47003 := hb (x (-2) 2 && x (-2) 11)
    have b47004 := hb (x (-3) 3 && x (-3) 12)
    have b47005 := hb (x (-4) 4 && x (-4) 13)
    have b47006 := hb (x (-5) 5 && x (-5) 14)
    clear * - r46999 b47000 b47001 b47002 b47003 b47004 b47005 b47006 g3 g6 d46994 g7 g8 g0
    omega
  have d47007 : (x (-3) 12).toNat = 1 := by
    have r47008 := hand2 (x (-3) 3) (x (-3) 12)
    have b47009 := hb (x (-3) 12)
    have b47010 := hb (x (-3) 3 && x (-3) 12)
    clear * - r47008 b47009 b47010 d46998
    omega
  have d47011 : (x (-4) 13).toNat = 0 := by
    have r47012 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e47013 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
    have e47014 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
    have b47015 := hb (x (-6) 3)
    have b47016 := hb (x (-5) 2)
    have b47017 := hb (x (-4) 13)
    have b47018 := hb (x (-3) 12)
    clear * - r47012 e47013 e47014 b47015 b47016 b47017 b47018 d47007
    omega
  have d47019 : (x (-4) 5).toNat = 0 := by
    have r47020 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
    have b47021 := hb (x (-4) 5)
    have b47022 := hb (x (-4) 13)
    clear * - r47020 b47021 b47022 d47011
    omega
  have d47023 : (x (-3) 4 && x (-3) 14).toNat = 1 := by
    have r47024 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b47025 := hb (x (-4) 5)
    have b47026 := hb (x 1 10)
    have b47027 := hb (x 0 1 && x 0 11)
    have b47028 := hb (x (-1) 2 && x (-1) 12)
    have b47029 := hb (x (-2) 3 && x (-2) 13)
    have b47030 := hb (x (-3) 4 && x (-3) 14)
    clear * - r47024 b47025 b47026 b47027 b47028 b47029 b47030 g4 g9 d46974 d46986 d47019
    omega
  have d47031 : (x (-3) 14).toNat = 1 := by
    have r47032 := hand2 (x (-3) 4) (x (-3) 14)
    have b47033 := hb (x (-3) 14)
    have b47034 := hb (x (-3) 4 && x (-3) 14)
    clear * - r47032 b47033 b47034 d47023
    omega
  have d47035 : (x (-4) 1).toNat = 0 := by
    have r47036 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b47037 := hb (x (-4) 1)
    have b47038 := hb (x (-3) 14)
    clear * - r47036 b47037 b47038 d47031
    omega
  have d47039 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
    have r47040 := hand1 (x (-4) 1) (x (-4) 14)
    have b47041 := hb (x (-4) 1)
    have b47042 := hb (x (-4) 1 && x (-4) 14)
    clear * - r47040 b47041 b47042 d47035
    omega
  have d47043 : (x (-5) 2).toNat = 0 := by
    have r47044 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e47045 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
    have e47046 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
    have b47047 := hb (x (-6) 3)
    have b47048 := hb (x (-5) 2)
    have b47049 := hb (x (-4) 13)
    have b47050 := hb (x (-3) 12)
    clear * - r47044 e47045 e47046 b47047 b47048 b47049 b47050 d47007 d47011
    omega
  have d47051 : (x (-3) 13).toNat = 1 := by
    have r47052 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b47053 := hb (x (-5) 2)
    have b47054 := hb (x (-3) 13)
    have b47055 := hb (x (-4) 1 && x (-4) 14)
    clear * - r47052 b47053 b47054 b47055 d47039 d47043
    omega
  have d47056 : (x (-3) 1).toNat = 1 := by
    have r47057 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
    have b47058 := hb (x (-3) 1)
    have b47059 := hb (x (-3) 13)
    clear * - r47057 b47058 b47059 d47051
    omega
  have d47060 : (x (-2) 14).toNat = 0 := by
    have r47061 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b47062 := hb (x (-3) 1)
    have b47063 := hb (x (-2) 14)
    clear * - r47061 b47062 b47063 d47056
    omega
  have d47064 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
    have r47065 := hand2 (x (-2) 1) (x (-2) 14)
    have b47066 := hb (x (-2) 14)
    have b47067 := hb (x (-2) 1 && x (-2) 14)
    clear * - r47065 b47066 b47067 d47060
    omega
  have d47068 : (x (-3) 2).toNat = 1 := by
    have r47069 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b47070 := hb (x (-3) 2)
    have b47071 := hb (x (-1) 13)
    have b47072 := hb (x (-2) 1 && x (-2) 14)
    clear * - r47069 b47070 b47071 b47072 g1 d47064
    omega
  have d47073 : (x (-1) 12).toNat = 0 := by
    have r47074 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e47075 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e47076 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b47077 := hb (x (-4) 3)
    have b47078 := hb (x (-3) 2)
    have b47079 := hb (x (-2) 13)
    have b47080 := hb (x (-1) 12)
    clear * - r47074 e47075 e47076 b47077 b47078 b47079 b47080 d47068
    omega
  have d47081 : (x (-1) 4).toNat = 0 := by
    have r47082 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
    have b47083 := hb (x (-1) 4)
    have b47084 := hb (x (-1) 12)
    clear * - r47082 b47083 b47084 d47073
    omega
  have d47085 : (x (-1) 4 && x (-1) 14).toNat = 0 := by
    have r47086 := hand1 (x (-1) 4) (x (-1) 14)
    have b47087 := hb (x (-1) 4)
    have b47088 := hb (x (-1) 4 && x (-1) 14)
    clear * - r47086 b47087 b47088 d47081
    omega
  have d47089 : (x (-2) 13).toNat = 0 := by
    have r47090 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e47091 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e47092 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b47093 := hb (x (-4) 3)
    have b47094 := hb (x (-3) 2)
    have b47095 := hb (x (-2) 13)
    have b47096 := hb (x (-1) 12)
    clear * - r47090 e47091 e47092 b47093 b47094 b47095 b47096 d47073 d47068
    omega
  have d47097 : (x (-2) 5).toNat = 0 := by
    have r47098 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
    have b47099 := hb (x (-2) 5)
    have b47100 := hb (x (-2) 13)
    clear * - r47098 b47099 b47100 d47089
    omega
  have d47101 : (x 2 1 && x 2 11).toNat = 1 := by
    have r47102 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b47103 := hb (x (-2) 5)
    have b47104 := hb (x 3 10)
    have b47105 := hb (x 2 1 && x 2 11)
    have b47106 := hb (x 1 2 && x 1 12)
    have b47107 := hb (x 0 3 && x 0 13)
    have b47108 := hb (x (-1) 4 && x (-1) 14)
    clear * - r47102 b47103 b47104 b47105 b47106 b47107 b47108 g5 g10 g11 d47085 d47097
    omega
  have d47109 : (x 2 11).toNat = 1 := by
    have r47110 := hand2 (x 2 1) (x 2 11)
    have b47111 := hb (x 2 11)
    have b47112 := hb (x 2 1 && x 2 11)
    clear * - r47110 b47111 b47112 d47101
    omega
  have r47113 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e47114 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
  have e47115 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
  have e47116 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
  have e47117 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
  have e47118 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
  have e47119 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
  have b47120 := hb (x (-2) 7)
  have b47121 := hb (x (-1) 6)
  have b47122 := hb (x 0 5)
  have b47123 := hb (x 1 4)
  have b47124 := hb (x 2 11)
  have b47125 := hb (x 3 10)
  have b47126 := hb (x 4 9)
  have b47127 := hb (x 5 8)
  linarith only [r47113, e47114, e47115, e47116, e47117, e47118, e47119, b47120, b47121, b47122, b47123, b47124, b47125, b47126, b47127, g5, d47109, d46962, g2]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a01011_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-4) 4).toNat = 0)
    (g1 : (x (-1) 13).toNat = 0)
    (g2 : (x 0 4).toNat = 1)
    (g3 : (x 0 11).toNat = 0)
    (g4 : (x (-1) 1 && x (-1) 12).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d47129 : (x 0 12).toNat = 1 := by
    have r47130 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
    have b47131 := hb (x 0 4)
    have b47132 := hb (x 0 12)
    clear * - r47130 b47131 b47132 g2
    omega
  have d47133 : (x (-2) 2).toNat = 0 := by
    have r47134 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e47135 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e47136 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b47137 := hb (x (-3) 3)
    have b47138 := hb (x (-2) 2)
    have b47139 := hb (x (-1) 13)
    have b47140 := hb (x 0 12)
    clear * - r47134 e47135 e47136 b47137 b47138 b47139 b47140 d47129 g1
    omega
  have d47141 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
    have r47142 := hand1 (x (-2) 2) (x (-2) 13)
    have b47143 := hb (x (-2) 2)
    have b47144 := hb (x (-2) 2 && x (-2) 13)
    clear * - r47142 b47143 b47144 d47133
    omega
  have d47145 : (x (-3) 3).toNat = 0 := by
    have r47146 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e47147 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e47148 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b47149 := hb (x (-3) 3)
    have b47150 := hb (x (-2) 2)
    have b47151 := hb (x (-1) 13)
    have b47152 := hb (x 0 12)
    clear * - r47146 e47147 e47148 b47149 b47150 b47151 b47152 d47129 g1 d47133
    omega
  have d47153 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
    have r47154 := hand1 (x (-3) 3) (x (-3) 14)
    have b47155 := hb (x (-3) 3)
    have b47156 := hb (x (-3) 3 && x (-3) 14)
    clear * - r47154 b47155 b47156 d47145
    omega
  have r47157 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have b47158 := hb (x (-4) 4)
  have b47159 := hb (x 0 11)
  have b47160 := hb (x (-1) 1 && x (-1) 12)
  have b47161 := hb (x (-2) 2 && x (-2) 13)
  have b47162 := hb (x (-3) 3 && x (-3) 14)
  linarith only [r47157, b47158, b47159, b47160, b47161, b47162, g3, g4, d47141, d47153, g0]

theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a01011 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-4) 4).toNat = 0)
    (g1 : (x (-1) 13).toNat = 0)
    (g2 : (x 0 4).toNat = 1)
    (g3 : (x 0 11).toNat = 0)
    (g4 : (x (-1) 1 && x (-1) 12).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a01011_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4
