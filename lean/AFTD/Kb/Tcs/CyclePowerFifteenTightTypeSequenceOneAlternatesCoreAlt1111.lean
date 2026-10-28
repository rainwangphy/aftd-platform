import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt1111

Topic: combinatorics   Node: 70d39ae9b1c4

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_alternates_core: under the layer-free tight-cover constraints for k = 15 and 57 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt1111_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 3).toNat = 0)
    (g1 : (x (-3) 7).toNat = 0)
    (g2 : (x (-3) 11).toNat = 0)
    (g3 : (x (-2) 2).toNat = 0)
    (g4 : (x (-2) 6).toNat = 0)
    (g5 : (x (-2) 10).toNat = 0)
    (g6 : (x (-1) 5).toNat = 0)
    (g7 : (x (-1) 13).toNat = 0)
    (g8 : (x 0 1).toNat = 1)
    (g9 : (x 0 4).toNat = 1)
    (g10 : (x 0 7).toNat = 1)
    (g11 : (x 1 1).toNat = 1)
    (g12 : (x 1 2).toNat = 0)
    (g13 : (x 1 3).toNat = 0)
    (g14 : (x 1 6).toNat = 0)
    (g15 : (x 1 10).toNat = 0)
    (g16 : (x 1 14).toNat = 0)
    (g17 : (x 2 2).toNat = 0)
    (g18 : (x 2 6).toNat = 0)
    (g19 : (x 2 14).toNat = 0)
    (g20 : (x 3 1).toNat = 1)
    (g21 : (x 3 13).toNat = 1)
    (g22 : (x 4 2).toNat = 0)
    (g23 : (x 4 4).toNat = 0)
    (g24 : (x 4 10).toNat = 0)
    (g25 : (x 4 12).toNat = 0)
    (g26 : (x (-3) 1 && x (-3) 3).toNat = 0)
    (g27 : (x 2 2 && x 2 6).toNat = 0)
    (g28 : (x 1 3 && x 1 7).toNat = 0)
    (g29 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g30 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g31 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g32 : (x 4 7 && x 4 12).toNat = 0)
    (g33 : (x 2 9 && x 2 14).toNat = 0)
    (g34 : (x (-2) 4 && x (-2) 10).toNat = 0)
    (g35 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g36 : (x 4 5 && x 4 12).toNat = 0)
    (g37 : (x 2 7 && x 2 14).toNat = 0)
    (g38 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g39 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g40 : (x (-2) 2 && x (-2) 11).toNat = 0)
    (g41 : (x (-3) 3 && x (-3) 12).toNat = 0)
    (g42 : (x 4 2 && x 4 11).toNat = 0)
    (g43 : (x 1 5 && x 1 14).toNat = 0)
    (g44 : (x 4 3 && x 4 12).toNat = 0)
    (g45 : (x 2 5 && x 2 14).toNat = 0)
    (g46 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g47 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g48 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g49 : (x 1 4 && x 1 14).toNat = 0)
    (g50 : (x (-2) 2 && x (-2) 13).toNat = 0)
    (g51 : (x (-3) 3 && x (-3) 14).toNat = 0)
    (g52 : (x 4 1 && x 4 12).toNat = 0)
    (g53 : (x 2 3 && x 2 14).toNat = 0)
    (g54 : (x 4 2 && x 4 13).toNat = 0)
    (g55 : (x 1 1 && x 1 14).toNat = 0)
    (g56 : (x 4 1 && x 4 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d42439 : (x 7 8).toNat = 0 := by
    have r42440 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e42441 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e42442 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e42443 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e42444 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e42445 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e42446 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b42447 := hb (x 0 7)
    have b42448 := hb (x 1 6)
    have b42449 := hb (x 2 5)
    have b42450 := hb (x 3 4)
    have b42451 := hb (x 4 11)
    have b42452 := hb (x 5 10)
    have b42453 := hb (x 6 9)
    have b42454 := hb (x 7 8)
    clear * - r42440 e42441 e42442 e42443 e42444 e42445 e42446 b42447 b42448 b42449 b42450 b42451 b42452 b42453 b42454 g14 g10
    omega
  have d42455 : (x 7 8 && x 7 12).toNat = 0 := by
    have r42456 := hand1 (x 7 8) (x 7 12)
    have b42457 := hb (x 7 8)
    have b42458 := hb (x 7 8 && x 7 12)
    clear * - r42456 b42457 b42458 d42439
    omega
  have d42459 : (x 7 8 && x 7 10).toNat = 0 := by
    have r42460 := hand1 (x 7 8) (x 7 10)
    have b42461 := hb (x 7 8)
    have b42462 := hb (x 7 8 && x 7 10)
    clear * - r42460 b42461 b42462 d42439
    omega
  have d42463 : (x 6 9).toNat = 0 := by
    have r42464 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e42465 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e42466 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e42467 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e42468 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e42469 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e42470 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b42471 := hb (x 0 7)
    have b42472 := hb (x 1 6)
    have b42473 := hb (x 2 5)
    have b42474 := hb (x 3 4)
    have b42475 := hb (x 4 11)
    have b42476 := hb (x 5 10)
    have b42477 := hb (x 6 9)
    have b42478 := hb (x 7 8)
    clear * - r42464 e42465 e42466 e42467 e42468 e42469 e42470 b42471 b42472 b42473 b42474 b42475 b42476 b42477 b42478 d42439 g14 g10
    omega
  have d42479 : (x 6 9 && x 6 13).toNat = 0 := by
    have r42480 := hand1 (x 6 9) (x 6 13)
    have b42481 := hb (x 6 9)
    have b42482 := hb (x 6 9 && x 6 13)
    clear * - r42480 b42481 b42482 d42463
    omega
  have d42483 : (x 6 9 && x 6 11).toNat = 0 := by
    have r42484 := hand1 (x 6 9) (x 6 11)
    have b42485 := hb (x 6 9)
    have b42486 := hb (x 6 9 && x 6 11)
    clear * - r42484 b42485 b42486 d42463
    omega
  have d42487 : (x 5 10).toNat = 0 := by
    have r42488 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e42489 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e42490 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e42491 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e42492 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e42493 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e42494 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b42495 := hb (x 0 7)
    have b42496 := hb (x 1 6)
    have b42497 := hb (x 2 5)
    have b42498 := hb (x 3 4)
    have b42499 := hb (x 4 11)
    have b42500 := hb (x 5 10)
    have b42501 := hb (x 6 9)
    have b42502 := hb (x 7 8)
    clear * - r42488 e42489 e42490 e42491 e42492 e42493 e42494 b42495 b42496 b42497 b42498 b42499 b42500 b42501 b42502 d42439 d42463 g14 g10
    omega
  have d42503 : (x 5 1 && x 5 10).toNat = 0 := by
    have r42504 := hand2 (x 5 1) (x 5 10)
    have b42505 := hb (x 5 10)
    have b42506 := hb (x 5 1 && x 5 10)
    clear * - r42504 b42505 b42506 d42487
    omega
  have d42507 : (x 5 10 && x 5 12).toNat = 0 := by
    have r42508 := hand1 (x 5 10) (x 5 12)
    have b42509 := hb (x 5 10)
    have b42510 := hb (x 5 10 && x 5 12)
    clear * - r42508 b42509 b42510 d42487
    omega
  have d42511 : (x 4 11).toNat = 0 := by
    have r42512 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e42513 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e42514 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e42515 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e42516 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e42517 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e42518 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b42519 := hb (x 0 7)
    have b42520 := hb (x 1 6)
    have b42521 := hb (x 2 5)
    have b42522 := hb (x 3 4)
    have b42523 := hb (x 4 11)
    have b42524 := hb (x 5 10)
    have b42525 := hb (x 6 9)
    have b42526 := hb (x 7 8)
    clear * - r42512 e42513 e42514 e42515 e42516 e42517 e42518 b42519 b42520 b42521 b42522 b42523 b42524 b42525 b42526 d42439 d42463 d42487 g14 g10
    omega
  have d42527 : (x 4 1 && x 4 11).toNat = 0 := by
    have r42528 := hand2 (x 4 1) (x 4 11)
    have b42529 := hb (x 4 11)
    have b42530 := hb (x 4 1 && x 4 11)
    clear * - r42528 b42529 b42530 d42511
    omega
  have d42531 : (x 4 11 && x 4 13).toNat = 0 := by
    have r42532 := hand1 (x 4 11) (x 4 13)
    have b42533 := hb (x 4 11)
    have b42534 := hb (x 4 11 && x 4 13)
    clear * - r42532 b42533 b42534 d42511
    omega
  have d42535 : (x 3 4).toNat = 0 := by
    have r42536 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e42537 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e42538 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e42539 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e42540 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e42541 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e42542 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b42543 := hb (x 0 7)
    have b42544 := hb (x 1 6)
    have b42545 := hb (x 2 5)
    have b42546 := hb (x 3 4)
    have b42547 := hb (x 4 11)
    have b42548 := hb (x 5 10)
    have b42549 := hb (x 6 9)
    have b42550 := hb (x 7 8)
    clear * - r42536 e42537 e42538 e42539 e42540 e42541 e42542 b42543 b42544 b42545 b42546 b42547 b42548 b42549 b42550 d42439 d42463 d42487 d42511 g14 g10
    omega
  have d42551 : (x 3 4 && x 3 14).toNat = 0 := by
    have r42552 := hand1 (x 3 4) (x 3 14)
    have b42553 := hb (x 3 4)
    have b42554 := hb (x 3 4 && x 3 14)
    clear * - r42552 b42553 b42554 d42535
    omega
  have d42555 : (x 3 4 && x 3 13).toNat = 0 := by
    have r42556 := hand1 (x 3 4) (x 3 13)
    have b42557 := hb (x 3 4)
    have b42558 := hb (x 3 4 && x 3 13)
    clear * - r42556 b42557 b42558 d42535
    omega
  have d42559 : (x 2 5).toNat = 0 := by
    have r42560 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e42561 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e42562 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e42563 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e42564 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e42565 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e42566 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b42567 := hb (x 0 7)
    have b42568 := hb (x 1 6)
    have b42569 := hb (x 2 5)
    have b42570 := hb (x 3 4)
    have b42571 := hb (x 4 11)
    have b42572 := hb (x 5 10)
    have b42573 := hb (x 6 9)
    have b42574 := hb (x 7 8)
    clear * - r42560 e42561 e42562 e42563 e42564 e42565 e42566 b42567 b42568 b42569 b42570 b42571 b42572 b42573 b42574 d42439 d42463 d42487 d42511 d42535 g14 g10
    omega
  cases h42575 : x 0 2
  · have f42576 : (x 0 2).toNat = 0 := by rw [h42575]; rfl
    have d42577 : (x 2 13).toNat = 1 := by
      have r42578 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42579 := hb (x 0 2)
      have b42580 := hb (x 2 13)
      have b42581 := hb (x 1 1 && x 1 14)
      clear * - r42578 b42579 b42580 b42581 g55 f42576
      omega
    have d42582 : (x 2 1).toNat = 1 := by
      have r42583 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
      have b42584 := hb (x 2 1)
      have b42585 := hb (x 2 13)
      clear * - r42583 b42584 b42585 d42577
      omega
    have d42586 : (x 3 14).toNat = 0 := by
      have r42587 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42588 := hb (x 2 1)
      have b42589 := hb (x 3 14)
      clear * - r42587 b42588 b42589 d42582
      omega
    have d42590 : (x 3 1 && x 3 14).toNat = 0 := by
      have r42591 := hand2 (x 3 1) (x 3 14)
      have b42592 := hb (x 3 14)
      have b42593 := hb (x 3 1 && x 3 14)
      clear * - r42591 b42592 b42593 d42586
      omega
    have d42594 : (x 4 13).toNat = 1 := by
      have r42595 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42596 := hb (x 2 2)
      have b42597 := hb (x 4 13)
      have b42598 := hb (x 3 1 && x 3 14)
      clear * - r42595 b42596 b42597 b42598 d42590 g17
      omega
    have d42599 : (x 4 1).toNat = 1 := by
      have r42600 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
      have b42601 := hb (x 4 1)
      have b42602 := hb (x 4 13)
      clear * - r42600 b42601 b42602 d42594
      omega
    have d42603 : (x 5 14).toNat = 0 := by
      have r42604 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42605 := hb (x 4 1)
      have b42606 := hb (x 5 14)
      clear * - r42604 b42605 b42606 d42599
      omega
    have d42607 : (x 5 1 && x 5 14).toNat = 0 := by
      have r42608 := hand2 (x 5 1) (x 5 14)
      have b42609 := hb (x 5 14)
      have b42610 := hb (x 5 1 && x 5 14)
      clear * - r42608 b42609 b42610 d42603
      omega
    have d42611 : (x 6 13).toNat = 1 := by
      have r42612 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42613 := hb (x 4 2)
      have b42614 := hb (x 6 13)
      have b42615 := hb (x 5 1 && x 5 14)
      clear * - r42612 b42613 b42614 b42615 d42607 g22
      omega
    have d42616 : (x 6 1).toNat = 1 := by
      have r42617 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
      have b42618 := hb (x 6 1)
      have b42619 := hb (x 6 13)
      clear * - r42617 b42618 b42619 d42611
      omega
    have d42620 : (x 7 14).toNat = 0 := by
      have r42621 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42622 := hb (x 6 1)
      have b42623 := hb (x 7 14)
      clear * - r42621 b42622 b42623 d42616
      omega
    have d42624 : (x 7 1 && x 7 14).toNat = 0 := by
      have r42625 := hand2 (x 7 1) (x 7 14)
      have b42626 := hb (x 7 14)
      have b42627 := hb (x 7 1 && x 7 14)
      clear * - r42625 b42626 b42627 d42620
      omega
    have d42628 : (x 7 2).toNat = 0 := by
      have r42629 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
      have b42630 := hb (x 7 2)
      have b42631 := hb (x 7 14)
      clear * - r42629 b42630 b42631 d42620
      omega
    have d42632 : (x 5 2).toNat = 0 := by
      have r42633 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
      have b42634 := hb (x 5 2)
      have b42635 := hb (x 5 14)
      clear * - r42633 b42634 b42635 d42603
      omega
    have d42636 : (x 3 2).toNat = 0 := by
      have r42637 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
      have b42638 := hb (x 3 2)
      have b42639 := hb (x 3 14)
      clear * - r42637 b42638 b42639 d42586
      omega
    have d42640 : (x 5 13).toNat = 1 := by
      have r42641 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42642 := hb (x 3 2)
      have b42643 := hb (x 5 13)
      have b42644 := hb (x 4 1 && x 4 14)
      clear * - r42641 b42642 b42643 b42644 g56 d42636
      omega
    have d42645 : (x 5 1).toNat = 1 := by
      have r42646 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
      have b42647 := hb (x 5 1)
      have b42648 := hb (x 5 13)
      clear * - r42646 b42647 b42648 d42640
      omega
    have d42649 : (x 6 14).toNat = 0 := by
      have r42650 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42651 := hb (x 5 1)
      have b42652 := hb (x 6 14)
      clear * - r42650 b42651 b42652 d42645
      omega
    have d42653 : (x 6 1 && x 6 14).toNat = 0 := by
      have r42654 := hand2 (x 6 1) (x 6 14)
      have b42655 := hb (x 6 14)
      have b42656 := hb (x 6 1 && x 6 14)
      clear * - r42654 b42655 b42656 d42649
      omega
    have d42657 : (x 7 13).toNat = 1 := by
      have r42658 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42659 := hb (x 5 2)
      have b42660 := hb (x 7 13)
      have b42661 := hb (x 6 1 && x 6 14)
      clear * - r42658 b42659 b42660 b42661 d42653 d42632
      omega
    have d42662 : (x 7 1).toNat = 1 := by
      have r42663 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
      have b42664 := hb (x 7 1)
      have b42665 := hb (x 7 13)
      clear * - r42663 b42664 b42665 d42657
      omega
    have d42666 : (x 8 14).toNat = 0 := by
      have r42667 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42668 := hb (x 7 1)
      have b42669 := hb (x 8 14)
      clear * - r42667 b42668 b42669 d42662
      omega
    have d42670 : (x 8 1 && x 8 14).toNat = 0 := by
      have r42671 := hand2 (x 8 1) (x 8 14)
      have b42672 := hb (x 8 14)
      have b42673 := hb (x 8 1 && x 8 14)
      clear * - r42671 b42672 b42673 d42666
      omega
    have d42674 : (x 9 13).toNat = 1 := by
      have r42675 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42676 := hb (x 7 2)
      have b42677 := hb (x 9 13)
      have b42678 := hb (x 8 1 && x 8 14)
      clear * - r42675 b42676 b42677 b42678 d42670 d42628
      omega
    have d42679 : (x 9 1).toNat = 1 := by
      have r42680 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
      have b42681 := hb (x 9 1)
      have b42682 := hb (x 9 13)
      clear * - r42680 b42681 b42682 d42674
      omega
    have d42683 : (x 10 14).toNat = 0 := by
      have r42684 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42685 := hb (x 9 1)
      have b42686 := hb (x 10 14)
      clear * - r42684 b42685 b42686 d42679
      omega
    have d42687 : (x 10 1 && x 10 14).toNat = 0 := by
      have r42688 := hand2 (x 10 1) (x 10 14)
      have b42689 := hb (x 10 14)
      have b42690 := hb (x 10 1 && x 10 14)
      clear * - r42688 b42689 b42690 d42683
      omega
    have d42691 : (x 10 2).toNat = 0 := by
      have r42692 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
      have b42693 := hb (x 10 2)
      have b42694 := hb (x 10 14)
      clear * - r42692 b42693 b42694 d42683
      omega
    have d42695 : (x 8 2).toNat = 0 := by
      have r42696 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
      have b42697 := hb (x 8 2)
      have b42698 := hb (x 8 14)
      clear * - r42696 b42697 b42698 d42666
      omega
    have d42699 : (x 6 2).toNat = 0 := by
      have r42700 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
      have b42701 := hb (x 6 2)
      have b42702 := hb (x 6 14)
      clear * - r42700 b42701 b42702 d42649
      omega
    have d42703 : (x 8 13).toNat = 1 := by
      have r42704 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42705 := hb (x 6 2)
      have b42706 := hb (x 8 13)
      have b42707 := hb (x 7 1 && x 7 14)
      clear * - r42704 b42705 b42706 b42707 d42624 d42699
      omega
    have d42708 : (x 8 1).toNat = 1 := by
      have r42709 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
      have b42710 := hb (x 8 1)
      have b42711 := hb (x 8 13)
      clear * - r42709 b42710 b42711 d42703
      omega
    have d42712 : (x 9 14).toNat = 0 := by
      have r42713 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42714 := hb (x 8 1)
      have b42715 := hb (x 9 14)
      clear * - r42713 b42714 b42715 d42708
      omega
    have d42716 : (x 9 1 && x 9 14).toNat = 0 := by
      have r42717 := hand2 (x 9 1) (x 9 14)
      have b42718 := hb (x 9 14)
      have b42719 := hb (x 9 1 && x 9 14)
      clear * - r42717 b42718 b42719 d42712
      omega
    have d42720 : (x 10 13).toNat = 1 := by
      have r42721 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42722 := hb (x 8 2)
      have b42723 := hb (x 10 13)
      have b42724 := hb (x 9 1 && x 9 14)
      clear * - r42721 b42722 b42723 b42724 d42716 d42695
      omega
    have d42725 : (x 10 1).toNat = 1 := by
      have r42726 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
      have b42727 := hb (x 10 1)
      have b42728 := hb (x 10 13)
      clear * - r42726 b42727 b42728 d42720
      omega
    have d42729 : (x 11 14).toNat = 0 := by
      have r42730 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42731 := hb (x 10 1)
      have b42732 := hb (x 11 14)
      clear * - r42730 b42731 b42732 d42725
      omega
    have d42733 : (x 11 1 && x 11 14).toNat = 0 := by
      have r42734 := hand2 (x 11 1) (x 11 14)
      have b42735 := hb (x 11 14)
      have b42736 := hb (x 11 1 && x 11 14)
      clear * - r42734 b42735 b42736 d42729
      omega
    have d42737 : (x 12 13).toNat = 1 := by
      have r42738 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42739 := hb (x 10 2)
      have b42740 := hb (x 12 13)
      have b42741 := hb (x 11 1 && x 11 14)
      clear * - r42738 b42739 b42740 b42741 d42733 d42691
      omega
    have d42742 : (x 12 1).toNat = 1 := by
      have r42743 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
      have b42744 := hb (x 12 1)
      have b42745 := hb (x 12 13)
      clear * - r42743 b42744 b42745 d42737
      omega
    have d42746 : (x 13 14).toNat = 0 := by
      have r42747 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42748 := hb (x 12 1)
      have b42749 := hb (x 13 14)
      clear * - r42747 b42748 b42749 d42742
      omega
    have d42750 : (x 13 1 && x 13 14).toNat = 0 := by
      have r42751 := hand2 (x 13 1) (x 13 14)
      have b42752 := hb (x 13 14)
      have b42753 := hb (x 13 1 && x 13 14)
      clear * - r42751 b42752 b42753 d42746
      omega
    have d42754 : (x 13 2).toNat = 0 := by
      have r42755 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
      have b42756 := hb (x 13 2)
      have b42757 := hb (x 13 14)
      clear * - r42755 b42756 b42757 d42746
      omega
    have d42758 : (x 11 2).toNat = 0 := by
      have r42759 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
      have b42760 := hb (x 11 2)
      have b42761 := hb (x 11 14)
      clear * - r42759 b42760 b42761 d42729
      omega
    have d42762 : (x 9 2).toNat = 0 := by
      have r42763 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
      have b42764 := hb (x 9 2)
      have b42765 := hb (x 9 14)
      clear * - r42763 b42764 b42765 d42712
      omega
    have d42766 : (x 11 13).toNat = 1 := by
      have r42767 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42768 := hb (x 9 2)
      have b42769 := hb (x 11 13)
      have b42770 := hb (x 10 1 && x 10 14)
      clear * - r42767 b42768 b42769 b42770 d42687 d42762
      omega
    have d42771 : (x 11 1).toNat = 1 := by
      have r42772 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
      have b42773 := hb (x 11 1)
      have b42774 := hb (x 11 13)
      clear * - r42772 b42773 b42774 d42766
      omega
    have d42775 : (x 12 14).toNat = 0 := by
      have r42776 : (x 12 14).toNat + (x 11 1).toNat = 1 := by have q := hd14 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42777 := hb (x 11 1)
      have b42778 := hb (x 12 14)
      clear * - r42776 b42777 b42778 d42771
      omega
    have d42779 : (x 12 1 && x 12 14).toNat = 0 := by
      have r42780 := hand2 (x 12 1) (x 12 14)
      have b42781 := hb (x 12 14)
      have b42782 := hb (x 12 1 && x 12 14)
      clear * - r42780 b42781 b42782 d42775
      omega
    have d42783 : (x 13 13).toNat = 1 := by
      have r42784 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42785 := hb (x 11 2)
      have b42786 := hb (x 13 13)
      have b42787 := hb (x 12 1 && x 12 14)
      clear * - r42784 b42785 b42786 b42787 d42779 d42758
      omega
    have d42788 : (x 13 1).toNat = 1 := by
      have r42789 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
      have b42790 := hb (x 13 1)
      have b42791 := hb (x 13 13)
      clear * - r42789 b42790 b42791 d42783
      omega
    have d42792 : (x 14 14).toNat = 0 := by
      have r42793 : (x 14 14).toNat + (x 13 1).toNat = 1 := by have q := hd14 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42794 := hb (x 13 1)
      have b42795 := hb (x 14 14)
      clear * - r42793 b42794 b42795 d42788
      omega
    have d42796 : (x 14 1 && x 14 14).toNat = 0 := by
      have r42797 := hand2 (x 14 1) (x 14 14)
      have b42798 := hb (x 14 14)
      have b42799 := hb (x 14 1 && x 14 14)
      clear * - r42797 b42798 b42799 d42792
      omega
    have d42800 : (x 15 13).toNat = 1 := by
      have r42801 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42802 := hb (x 13 2)
      have b42803 := hb (x 15 13)
      have b42804 := hb (x 14 1 && x 14 14)
      clear * - r42801 b42802 b42803 b42804 d42796 d42754
      omega
    have d42805 : (x 15 1).toNat = 1 := by
      have r42806 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
      have b42807 := hb (x 15 1)
      have b42808 := hb (x 15 13)
      clear * - r42806 b42807 b42808 d42800
      omega
    have d42809 : (x 16 14).toNat = 0 := by
      have r42810 : (x 16 14).toNat + (x 15 1).toNat = 1 := by have q := hd14 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42811 := hb (x 15 1)
      have b42812 := hb (x 16 14)
      clear * - r42810 b42811 b42812 d42805
      omega
    have d42813 : (x 16 1 && x 16 14).toNat = 0 := by
      have r42814 := hand2 (x 16 1) (x 16 14)
      have b42815 := hb (x 16 14)
      have b42816 := hb (x 16 1 && x 16 14)
      clear * - r42814 b42815 b42816 d42809
      omega
    have d42817 : (x 14 3 && x 14 14).toNat = 0 := by
      have r42818 := hand2 (x 14 3) (x 14 14)
      have b42819 := hb (x 14 14)
      have b42820 := hb (x 14 3 && x 14 14)
      clear * - r42818 b42819 b42820 d42792
      omega
    have d42821 : (x 14 2).toNat = 0 := by
      have r42822 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
      have b42823 := hb (x 14 2)
      have b42824 := hb (x 14 14)
      clear * - r42822 b42823 b42824 d42792
      omega
    have d42825 : (x 12 2).toNat = 0 := by
      have r42826 : (x 12 2).toNat ≤ (x 12 14).toNat := himp _ _ (hp2 12)
      have b42827 := hb (x 12 2)
      have b42828 := hb (x 12 14)
      clear * - r42826 b42827 b42828 d42775
      omega
    have d42829 : (x 14 13).toNat = 1 := by
      have r42830 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42831 := hb (x 12 2)
      have b42832 := hb (x 14 13)
      have b42833 := hb (x 13 1 && x 13 14)
      clear * - r42830 b42831 b42832 b42833 d42750 d42825
      omega
    have d42834 : (x 14 1).toNat = 1 := by
      have r42835 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
      have b42836 := hb (x 14 1)
      have b42837 := hb (x 14 13)
      clear * - r42835 b42836 b42837 d42829
      omega
    have d42838 : (x 15 14).toNat = 0 := by
      have r42839 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42840 := hb (x 14 1)
      have b42841 := hb (x 15 14)
      clear * - r42839 b42840 b42841 d42834
      omega
    have d42842 : (x 15 1 && x 15 14).toNat = 0 := by
      have r42843 := hand2 (x 15 1) (x 15 14)
      have b42844 := hb (x 15 14)
      have b42845 := hb (x 15 1 && x 15 14)
      clear * - r42843 b42844 b42845 d42838
      omega
    have d42846 : (x 16 13).toNat = 1 := by
      have r42847 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42848 := hb (x 14 2)
      have b42849 := hb (x 16 13)
      have b42850 := hb (x 15 1 && x 15 14)
      clear * - r42847 b42848 b42849 b42850 d42842 d42821
      omega
    have d42851 : (x 16 1).toNat = 1 := by
      have r42852 : (x 16 13).toNat ≤ (x 16 1).toNat := himp _ _ (hp13 16)
      have b42853 := hb (x 16 1)
      have b42854 := hb (x 16 13)
      clear * - r42852 b42853 b42854 d42846
      omega
    have d42855 : (x 17 14).toNat = 0 := by
      have r42856 : (x 17 14).toNat + (x 16 1).toNat = 1 := by have q := hd14 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42857 := hb (x 16 1)
      have b42858 := hb (x 17 14)
      clear * - r42856 b42857 b42858 d42851
      omega
    have d42859 : (x 17 2).toNat = 0 := by
      have r42860 : (x 17 2).toNat ≤ (x 17 14).toNat := himp _ _ (hp2 17)
      have b42861 := hb (x 17 2)
      have b42862 := hb (x 17 14)
      clear * - r42860 b42861 b42862 d42855
      omega
    have d42863 : (x 15 2).toNat = 0 := by
      have r42864 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
      have b42865 := hb (x 15 2)
      have b42866 := hb (x 15 14)
      clear * - r42864 b42865 b42866 d42838
      omega
    have d42867 : (x 15 2 && x 15 13).toNat = 0 := by
      have r42868 := hand1 (x 15 2) (x 15 13)
      have b42869 := hb (x 15 2)
      have b42870 := hb (x 15 2 && x 15 13)
      clear * - r42868 b42869 b42870 d42863
      omega
    have d42871 : (x 17 13).toNat = 1 := by
      have r42872 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := by have q := hcov13 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42873 := hb (x 15 2)
      have b42874 := hb (x 17 13)
      have b42875 := hb (x 16 1 && x 16 14)
      clear * - r42872 b42873 b42874 b42875 d42813 d42863
      omega
    have d42876 : (x 17 1).toNat = 1 := by
      have r42877 : (x 17 13).toNat ≤ (x 17 1).toNat := himp _ _ (hp13 17)
      have b42878 := hb (x 17 1)
      have b42879 := hb (x 17 13)
      clear * - r42877 b42878 b42879 d42871
      omega
    have d42880 : (x 18 14).toNat = 0 := by
      have r42881 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42882 := hb (x 17 1)
      have b42883 := hb (x 18 14)
      clear * - r42881 b42882 b42883 d42876
      omega
    have d42884 : (x 18 1 && x 18 14).toNat = 0 := by
      have r42885 := hand2 (x 18 1) (x 18 14)
      have b42886 := hb (x 18 14)
      have b42887 := hb (x 18 1 && x 18 14)
      clear * - r42885 b42886 b42887 d42880
      omega
    have d42888 : (x 19 13).toNat = 1 := by
      have r42889 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42890 := hb (x 17 2)
      have b42891 := hb (x 19 13)
      have b42892 := hb (x 18 1 && x 18 14)
      clear * - r42889 b42890 b42891 b42892 d42884 d42859
      omega
    have d42893 : (x 18 2).toNat = 0 := by
      have r42894 : (x 18 2).toNat ≤ (x 18 14).toNat := himp _ _ (hp2 18)
      have b42895 := hb (x 18 2)
      have b42896 := hb (x 18 14)
      clear * - r42894 b42895 b42896 d42880
      omega
    have d42897 : (x 20 12).toNat = 0 := by
      have r42898 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e42899 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
      have e42900 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
      have b42901 := hb (x 17 3)
      have b42902 := hb (x 18 2)
      have b42903 := hb (x 19 13)
      have b42904 := hb (x 20 12)
      clear * - r42898 e42899 e42900 b42901 b42902 b42903 b42904 d42888 d42893
      omega
    have d42905 : (x 17 3).toNat = 0 := by
      have r42906 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e42907 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
      have e42908 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
      have b42909 := hb (x 17 3)
      have b42910 := hb (x 18 2)
      have b42911 := hb (x 19 13)
      have b42912 := hb (x 20 12)
      clear * - r42906 e42907 e42908 b42909 b42910 b42911 b42912 d42897 d42888 d42893
      omega
    have d42913 : (x 17 11).toNat = 0 := by
      have r42914 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
      have b42915 := hb (x 17 3)
      have b42916 := hb (x 17 11)
      clear * - r42914 b42915 b42916 d42905
      omega
    have d42917 : (x 16 12).toNat = 0 := by
      have r42918 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e42919 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
      have e42920 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
      have b42921 := hb (x 13 3)
      have b42922 := hb (x 14 2)
      have b42923 := hb (x 15 13)
      have b42924 := hb (x 16 12)
      clear * - r42918 e42919 e42920 b42921 b42922 b42923 b42924 d42800 d42821
      omega
    have d42925 : (x 16 1 && x 16 12).toNat = 0 := by
      have r42926 := hand2 (x 16 1) (x 16 12)
      have b42927 := hb (x 16 12)
      have b42928 := hb (x 16 1 && x 16 12)
      clear * - r42926 b42927 b42928 d42917
      omega
    have d42929 : (x 13 12).toNat = 0 := by
      have r42930 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e42931 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
      have e42932 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
      have b42933 := hb (x 10 3)
      have b42934 := hb (x 11 2)
      have b42935 := hb (x 12 13)
      have b42936 := hb (x 13 12)
      clear * - r42930 e42931 e42932 b42933 b42934 b42935 b42936 d42737 d42758
      omega
    have d42937 : (x 13 4).toNat = 0 := by
      have r42938 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
      have b42939 := hb (x 13 4)
      have b42940 := hb (x 13 12)
      clear * - r42938 b42939 b42940 d42929
      omega
    have r42941 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b42942 := hb (x 13 4)
    have b42943 := hb (x 17 11)
    have b42944 := hb (x 16 1 && x 16 12)
    have b42945 := hb (x 15 2 && x 15 13)
    have b42946 := hb (x 14 3 && x 14 14)
    linarith only [r42941, b42942, b42943, b42944, b42945, b42946, d42913, d42925, d42867, d42817, d42937]
  · have f42947 : (x 0 2).toNat = 1 := by rw [h42575]; rfl
    have d42948 : (x 0 14).toNat = 1 := by
      have r42949 : (x 0 2).toNat ≤ (x 0 14).toNat := himp _ _ (hp2 0)
      have b42950 := hb (x 0 2)
      have b42951 := hb (x 0 14)
      clear * - r42949 b42950 b42951 f42947
      omega
    have d42952 : (x (-1) 1).toNat = 0 := by
      have r42953 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42954 := hb (x (-1) 1)
      have b42955 := hb (x 0 14)
      clear * - r42953 b42954 b42955 d42948
      omega
    have d42956 : (x (-1) 1 && x (-1) 14).toNat = 0 := by
      have r42957 := hand1 (x (-1) 1) (x (-1) 14)
      have b42958 := hb (x (-1) 1)
      have b42959 := hb (x (-1) 1 && x (-1) 14)
      clear * - r42957 b42958 b42959 d42952
      omega
    have d42960 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
      have r42961 := hand1 (x (-1) 1) (x (-1) 12)
      have b42962 := hb (x (-1) 1)
      have b42963 := hb (x (-1) 1 && x (-1) 12)
      clear * - r42961 b42962 b42963 d42952
      omega
    have d42964 : (x (-1) 1 && x (-1) 11).toNat = 0 := by
      have r42965 := hand1 (x (-1) 1) (x (-1) 11)
      have b42966 := hb (x (-1) 1)
      have b42967 := hb (x (-1) 1 && x (-1) 11)
      clear * - r42965 b42966 b42967 d42952
      omega
    have d42968 : (x (-1) 1 && x (-1) 10).toNat = 0 := by
      have r42969 := hand1 (x (-1) 1) (x (-1) 10)
      have b42970 := hb (x (-1) 1)
      have b42971 := hb (x (-1) 1 && x (-1) 10)
      clear * - r42969 b42970 b42971 d42952
      omega
    have d42972 : (x (-1) 9).toNat = 0 := by
      have r42973 : (x (-1) 9).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp9 (-1))
      have b42974 := hb (x (-1) 1)
      have b42975 := hb (x (-1) 9)
      clear * - r42973 b42974 b42975 d42952
      omega
    have d42976 : (x (-1) 3 && x (-1) 9).toNat = 0 := by
      have r42977 := hand2 (x (-1) 3) (x (-1) 9)
      have b42978 := hb (x (-1) 9)
      have b42979 := hb (x (-1) 3 && x (-1) 9)
      clear * - r42977 b42978 b42979 d42972
      omega
    have d42980 : (x 0 13).toNat = 1 := by
      have r42981 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b42982 := hb (x (-2) 2)
      have b42983 := hb (x 0 13)
      have b42984 := hb (x (-1) 1 && x (-1) 14)
      clear * - r42981 b42982 b42983 b42984 d42956 g3
      omega
    have d42985 : (x 2 12).toNat = 0 := by
      have r42986 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e42987 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e42988 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b42989 := hb (x (-1) 3)
      have b42990 := hb (x 0 2)
      have b42991 := hb (x 1 13)
      have b42992 := hb (x 2 12)
      clear * - r42986 e42987 e42988 b42989 b42990 b42991 b42992 f42947
      omega
    have d42993 : (x 2 4).toNat = 0 := by
      have r42994 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
      have b42995 := hb (x 2 4)
      have b42996 := hb (x 2 12)
      clear * - r42994 b42995 b42996 d42985
      omega
    have d42997 : (x 2 4 && x 2 13).toNat = 0 := by
      have r42998 := hand1 (x 2 4) (x 2 13)
      have b42999 := hb (x 2 4)
      have b43000 := hb (x 2 4 && x 2 13)
      clear * - r42998 b42999 b43000 d42993
      omega
    have d43001 : (x 1 13).toNat = 0 := by
      have r43002 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e43003 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e43004 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b43005 := hb (x (-1) 3)
      have b43006 := hb (x 0 2)
      have b43007 := hb (x 1 13)
      have b43008 := hb (x 2 12)
      clear * - r43002 e43003 e43004 b43005 b43006 b43007 b43008 d42985 f42947
      omega
    have d43009 : (x 1 5).toNat = 0 := by
      have r43010 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
      have b43011 := hb (x 1 5)
      have b43012 := hb (x 1 13)
      clear * - r43010 b43011 b43012 d43001
      omega
    have d43013 : (x (-1) 3).toNat = 0 := by
      have r43014 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e43015 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e43016 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b43017 := hb (x (-1) 3)
      have b43018 := hb (x 0 2)
      have b43019 := hb (x 1 13)
      have b43020 := hb (x 2 12)
      clear * - r43014 e43015 e43016 b43017 b43018 b43019 b43020 d42985 d43001 f42947
      omega
    have d43021 : (x (-1) 11).toNat = 0 := by
      have r43022 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
      have b43023 := hb (x (-1) 3)
      have b43024 := hb (x (-1) 11)
      clear * - r43022 b43023 b43024 d43013
      omega
    have d43025 : (x 1 12).toNat = 0 := by
      have r43026 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e43027 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e43028 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b43029 := hb (x (-2) 3)
      have b43030 := hb (x (-1) 2)
      have b43031 := hb (x 0 13)
      have b43032 := hb (x 1 12)
      clear * - r43026 e43027 e43028 b43029 b43030 b43031 b43032 d42980
      omega
    have d43033 : (x 1 4).toNat = 0 := by
      have r43034 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
      have b43035 := hb (x 1 4)
      have b43036 := hb (x 1 12)
      clear * - r43034 b43035 b43036 d43025
      omega
    have d43037 : (x (-1) 2).toNat = 0 := by
      have r43038 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e43039 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e43040 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b43041 := hb (x (-2) 3)
      have b43042 := hb (x (-1) 2)
      have b43043 := hb (x 0 13)
      have b43044 := hb (x 1 12)
      clear * - r43038 e43039 e43040 b43041 b43042 b43043 b43044 d43025 d42980
      omega
    have d43045 : (x (-1) 10).toNat = 0 := by
      have r43046 : (x (-1) 10).toNat ≤ (x (-1) 2).toNat := himp _ _ (hp10 (-1))
      have b43047 := hb (x (-1) 2)
      have b43048 := hb (x (-1) 10)
      clear * - r43046 b43047 b43048 d43037
      omega
    have d43049 : (x (-2) 3).toNat = 0 := by
      have r43050 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e43051 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e43052 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b43053 := hb (x (-2) 3)
      have b43054 := hb (x (-1) 2)
      have b43055 := hb (x 0 13)
      have b43056 := hb (x 1 12)
      clear * - r43050 e43051 e43052 b43053 b43054 b43055 b43056 d43025 d42980 d43037
      omega
    have d43057 : (x (-2) 11).toNat = 0 := by
      have r43058 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
      have b43059 := hb (x (-2) 3)
      have b43060 := hb (x (-2) 11)
      clear * - r43058 b43059 b43060 d43049
      omega
    have d43061 : (x (-2) 1 && x (-2) 11).toNat = 0 := by
      have r43062 := hand2 (x (-2) 1) (x (-2) 11)
      have b43063 := hb (x (-2) 11)
      have b43064 := hb (x (-2) 1 && x (-2) 11)
      clear * - r43062 b43063 b43064 d43057
      omega
    cases h43065 : x 0 3
    · have f43066 : (x 0 3).toNat = 0 := by rw [h43065]; rfl
      have d43067 : (x 0 11).toNat = 0 := by
        have r43068 : (x 0 11).toNat ≤ (x 0 3).toNat := himp _ _ (hp11 0)
        have b43069 := hb (x 0 3)
        have b43070 := hb (x 0 11)
        clear * - r43068 b43069 b43070 f43066
        omega
      have d43071 : (x (-4) 4).toNat = 1 := by
        have r43072 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b43073 := hb (x (-4) 4)
        have b43074 := hb (x 0 11)
        have b43075 := hb (x (-1) 1 && x (-1) 12)
        have b43076 := hb (x (-2) 2 && x (-2) 13)
        have b43077 := hb (x (-3) 3 && x (-3) 14)
        clear * - r43072 b43073 b43074 b43075 b43076 b43077 d43067 d42960 g50 g51
        omega
      have d43078 : (x (-4) 12).toNat = 1 := by
        have r43079 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
        have b43080 := hb (x (-4) 4)
        have b43081 := hb (x (-4) 12)
        clear * - r43079 b43080 b43081 d43071
        omega
      have d43082 : (x (-5) 13).toNat = 0 := by
        have r43083 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43084 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e43085 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have b43086 := hb (x (-7) 3)
        have b43087 := hb (x (-6) 2)
        have b43088 := hb (x (-5) 13)
        have b43089 := hb (x (-4) 12)
        clear * - r43083 e43084 e43085 b43086 b43087 b43088 b43089 d43078
        omega
      have d43090 : (x (-5) 7 && x (-5) 13).toNat = 0 := by
        have r43091 := hand2 (x (-5) 7) (x (-5) 13)
        have b43092 := hb (x (-5) 13)
        have b43093 := hb (x (-5) 7 && x (-5) 13)
        clear * - r43091 b43092 b43093 d43082
        omega
      have d43094 : (x (-5) 9 && x (-5) 13).toNat = 0 := by
        have r43095 := hand2 (x (-5) 9) (x (-5) 13)
        have b43096 := hb (x (-5) 13)
        have b43097 := hb (x (-5) 9 && x (-5) 13)
        clear * - r43095 b43096 b43097 d43082
        omega
      have d43098 : (x (-5) 5).toNat = 0 := by
        have r43099 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
        have b43100 := hb (x (-5) 5)
        have b43101 := hb (x (-5) 13)
        clear * - r43099 b43100 b43101 d43082
        omega
      have d43102 : (x (-6) 2).toNat = 0 := by
        have r43103 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43104 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e43105 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have b43106 := hb (x (-7) 3)
        have b43107 := hb (x (-6) 2)
        have b43108 := hb (x (-5) 13)
        have b43109 := hb (x (-4) 12)
        clear * - r43103 e43104 e43105 b43106 b43107 b43108 b43109 d43078 d43082
        omega
      have d43110 : (x (-6) 10).toNat = 0 := by
        have r43111 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
        have b43112 := hb (x (-6) 2)
        have b43113 := hb (x (-6) 10)
        clear * - r43111 b43112 b43113 d43102
        omega
      have d43114 : (x (-7) 3).toNat = 0 := by
        have r43115 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43116 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e43117 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have b43118 := hb (x (-7) 3)
        have b43119 := hb (x (-6) 2)
        have b43120 := hb (x (-5) 13)
        have b43121 := hb (x (-4) 12)
        clear * - r43115 e43116 e43117 b43118 b43119 b43120 b43121 d43078 d43082 d43102
        omega
      have d43122 : (x (-7) 11).toNat = 0 := by
        have r43123 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
        have b43124 := hb (x (-7) 3)
        have b43125 := hb (x (-7) 11)
        clear * - r43123 b43124 b43125 d43114
        omega
      have d43126 : (x (-7) 1 && x (-7) 11).toNat = 0 := by
        have r43127 := hand2 (x (-7) 1) (x (-7) 11)
        have b43128 := hb (x (-7) 11)
        have b43129 := hb (x (-7) 1 && x (-7) 11)
        clear * - r43127 b43128 b43129 d43122
        omega
      have d43130 : (x 0 8).toNat = 0 := by
        have r43131 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43132 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
        have e43133 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
        have e43134 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
        have e43135 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
        have e43136 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
        have e43137 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
        have b43138 := hb (x (-7) 7)
        have b43139 := hb (x (-6) 6)
        have b43140 := hb (x (-5) 5)
        have b43141 := hb (x (-4) 4)
        have b43142 := hb (x (-3) 11)
        have b43143 := hb (x (-2) 10)
        have b43144 := hb (x (-1) 9)
        have b43145 := hb (x 0 8)
        clear * - r43131 e43132 e43133 e43134 e43135 e43136 e43137 b43138 b43139 b43140 b43141 b43142 b43143 b43144 b43145 d42972 g5 g2 d43071 d43098
        omega
      have d43146 : (x 0 2 && x 0 8).toNat = 0 := by
        have r43147 := hand2 (x 0 2) (x 0 8)
        have b43148 := hb (x 0 8)
        have b43149 := hb (x 0 2 && x 0 8)
        clear * - r43147 b43148 b43149 d43130
        omega
      have d43150 : (x 0 4 && x 0 8).toNat = 0 := by
        have r43151 := hand2 (x 0 4) (x 0 8)
        have b43152 := hb (x 0 8)
        have b43153 := hb (x 0 4 && x 0 8)
        clear * - r43151 b43152 b43153 d43130
        omega
      have r43154 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r43155 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r43156 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e43157 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e43158 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e43159 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e43160 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e43161 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e43162 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have r43163 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e43164 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
      have e43165 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
      have r43166 : 1 ≤ (x 2 6).toNat + (x 1 1 && x 1 7).toNat + (x 0 2 && x 0 8).toNat + (x (-1) 3 && x (-1) 9).toNat + (x (-2) 4 && x (-2) 10).toNat + (x (-3) 5 && x (-3) 11).toNat + (x (-4) 6 && x (-4) 12).toNat + (x (-5) 7 && x (-5) 13).toNat + (x (-6) 8 && x (-6) 14).toNat + (x (-7) 9).toNat := by have q := hcov6 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r43167 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r43168 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r43169 : (x (-11) 5).toNat ≤ (x (-11) 13).toNat := himp _ _ (hp5 (-11))
      have r43170 := hand1 (x (-4) 8) (x (-4) 12)
      have r43171 := hand2 (x 1 1) (x 1 7)
      have r43172 := hand1 (x (-4) 6) (x (-4) 12)
      have r43173 := hand1 (x (-6) 8) (x (-6) 14)
      have r43174 := hand2 (x 6 1) (x 6 10)
      have r43175 := hand2 (x 5 2) (x 5 11)
      have r43176 := hand2 (x (-8) 2) (x (-8) 12)
      have r43177 := hand2 (x (-9) 3) (x (-9) 13)
      have r43178 := hand2 (x (-10) 4) (x (-10) 14)
      linarith only [r43154, r43155, r43156, e43157, e43158, e43159, e43160, e43161, e43162, r43163, e43164, e43165, r43166, r43167, r43168, r43169, r43170, r43171, r43172, r43173, r43174, r43175, r43176, r43177, r43178, d43122, d43110, g1, g4, d43013, g6, f42947, g9, g11, g13, g14, g17, g18, g20, g23, g27, g28, d43150, g29, g30, g31, d43094, d43146, d42976, g34, g35, d43090, g44, d42555, g45, d43126]
    · have f43242 : (x 0 3).toNat = 1 := by rw [h43065]; rfl
      have d43243 : (x 3 12).toNat = 0 := by
        have r43244 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43245 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
        have e43246 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
        have b43247 := hb (x 0 3)
        have b43248 := hb (x 1 2)
        have b43249 := hb (x 2 13)
        have b43250 := hb (x 3 12)
        clear * - r43244 e43245 e43246 b43247 b43248 b43249 b43250 g12 f43242
        omega
      have d43251 : (x 3 2 && x 3 12).toNat = 0 := by
        have r43252 := hand2 (x 3 2) (x 3 12)
        have b43253 := hb (x 3 12)
        have b43254 := hb (x 3 2 && x 3 12)
        clear * - r43252 b43253 b43254 d43243
        omega
      have d43255 : (x 3 3 && x 3 12).toNat = 0 := by
        have r43256 := hand2 (x 3 3) (x 3 12)
        have b43257 := hb (x 3 12)
        have b43258 := hb (x 3 3 && x 3 12)
        clear * - r43256 b43257 b43258 d43243
        omega
      have d43259 : (x 3 12 && x 3 14).toNat = 0 := by
        have r43260 := hand1 (x 3 12) (x 3 14)
        have b43261 := hb (x 3 12)
        have b43262 := hb (x 3 12 && x 3 14)
        clear * - r43260 b43261 b43262 d43243
        omega
      have d43263 : (x 2 13).toNat = 0 := by
        have r43264 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43265 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
        have e43266 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
        have b43267 := hb (x 0 3)
        have b43268 := hb (x 1 2)
        have b43269 := hb (x 2 13)
        have b43270 := hb (x 3 12)
        clear * - r43264 e43265 e43266 b43267 b43268 b43269 b43270 d43243 g12 f43242
        omega
      have d43271 : (x 2 3 && x 2 13).toNat = 0 := by
        have r43272 := hand2 (x 2 3) (x 2 13)
        have b43273 := hb (x 2 13)
        have b43274 := hb (x 2 3 && x 2 13)
        clear * - r43272 b43273 b43274 d43263
        omega
      have d43275 : (x 0 5).toNat = 1 := by
        have r43276 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b43277 := hb (x 0 5)
        have b43278 := hb (x 5 10)
        have b43279 := hb (x 4 1 && x 4 11)
        have b43280 := hb (x 3 2 && x 3 12)
        have b43281 := hb (x 2 3 && x 2 13)
        have b43282 := hb (x 1 4 && x 1 14)
        clear * - r43276 b43277 b43278 b43279 b43280 b43281 b43282 d42487 d42527 d43251 d43271 g49
        omega
      have d43283 : (x 0 6).toNat = 1 := by
        have r43284 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b43285 := hb (x 0 6)
        have b43286 := hb (x 6 9)
        have b43287 := hb (x 5 1 && x 5 10)
        have b43288 := hb (x 4 2 && x 4 11)
        have b43289 := hb (x 3 3 && x 3 12)
        have b43290 := hb (x 2 4 && x 2 13)
        have b43291 := hb (x 1 5 && x 1 14)
        clear * - r43284 b43285 b43286 b43287 b43288 b43289 b43290 b43291 d42463 d42503 g42 d43255 d42997 g43
        omega
      have d43292 : (x 6 8).toNat = 0 := by
        have r43293 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43294 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e43295 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e43296 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e43297 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e43298 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e43299 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b43300 := hb (x (-1) 7)
        have b43301 := hb (x 0 6)
        have b43302 := hb (x 1 5)
        have b43303 := hb (x 2 4)
        have b43304 := hb (x 3 11)
        have b43305 := hb (x 4 10)
        have b43306 := hb (x 5 9)
        have b43307 := hb (x 6 8)
        clear * - r43293 e43294 e43295 e43296 e43297 e43298 e43299 b43300 b43301 b43302 b43303 b43304 b43305 b43306 b43307 g24 d42993 d43009 d43283
        omega
      have d43308 : (x 5 9).toNat = 0 := by
        have r43309 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43310 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e43311 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e43312 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e43313 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e43314 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e43315 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b43316 := hb (x (-1) 7)
        have b43317 := hb (x 0 6)
        have b43318 := hb (x 1 5)
        have b43319 := hb (x 2 4)
        have b43320 := hb (x 3 11)
        have b43321 := hb (x 4 10)
        have b43322 := hb (x 5 9)
        have b43323 := hb (x 6 8)
        clear * - r43309 e43310 e43311 e43312 e43313 e43314 e43315 b43316 b43317 b43318 b43319 b43320 b43321 b43322 b43323 d43292 g24 d42993 d43009 d43283
        omega
      have d43324 : (x 3 11).toNat = 0 := by
        have r43325 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43326 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e43327 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e43328 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e43329 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e43330 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e43331 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b43332 := hb (x (-1) 7)
        have b43333 := hb (x 0 6)
        have b43334 := hb (x 1 5)
        have b43335 := hb (x 2 4)
        have b43336 := hb (x 3 11)
        have b43337 := hb (x 4 10)
        have b43338 := hb (x 5 9)
        have b43339 := hb (x 6 8)
        clear * - r43325 e43326 e43327 e43328 e43329 e43330 e43331 b43332 b43333 b43334 b43335 b43336 b43337 b43338 b43339 d43292 d43308 g24 d42993 d43009 d43283
        omega
      have d43340 : (x (-1) 7).toNat = 0 := by
        have r43341 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43342 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e43343 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e43344 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e43345 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e43346 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e43347 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b43348 := hb (x (-1) 7)
        have b43349 := hb (x 0 6)
        have b43350 := hb (x 1 5)
        have b43351 := hb (x 2 4)
        have b43352 := hb (x 3 11)
        have b43353 := hb (x 4 10)
        have b43354 := hb (x 5 9)
        have b43355 := hb (x 6 8)
        clear * - r43341 e43342 e43343 e43344 e43345 e43346 e43347 b43348 b43349 b43350 b43351 b43352 b43353 b43354 b43355 d43292 d43308 g24 d43324 d42993 d43009 d43283
        omega
      have d43356 : (x 5 8).toNat = 0 := by
        have r43357 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43358 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
        have e43359 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
        have e43360 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
        have e43361 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
        have e43362 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
        have e43363 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
        have b43364 := hb (x (-2) 7)
        have b43365 := hb (x (-1) 6)
        have b43366 := hb (x 0 5)
        have b43367 := hb (x 1 4)
        have b43368 := hb (x 2 11)
        have b43369 := hb (x 3 10)
        have b43370 := hb (x 4 9)
        have b43371 := hb (x 5 8)
        clear * - r43357 e43358 e43359 e43360 e43361 e43362 e43363 b43364 b43365 b43366 b43367 b43368 b43369 b43370 b43371 d43033 d43275
        omega
      have d43372 : (x 5 8 && x 5 12).toNat = 0 := by
        have r43373 := hand1 (x 5 8) (x 5 12)
        have b43374 := hb (x 5 8)
        have b43375 := hb (x 5 8 && x 5 12)
        clear * - r43373 b43374 b43375 d43356
        omega
      have d43376 : (x 4 9).toNat = 0 := by
        have r43377 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43378 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
        have e43379 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
        have e43380 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
        have e43381 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
        have e43382 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
        have e43383 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
        have b43384 := hb (x (-2) 7)
        have b43385 := hb (x (-1) 6)
        have b43386 := hb (x 0 5)
        have b43387 := hb (x 1 4)
        have b43388 := hb (x 2 11)
        have b43389 := hb (x 3 10)
        have b43390 := hb (x 4 9)
        have b43391 := hb (x 5 8)
        clear * - r43377 e43378 e43379 e43380 e43381 e43382 e43383 b43384 b43385 b43386 b43387 b43388 b43389 b43390 b43391 d43356 d43033 d43275
        omega
      have d43392 : (x 4 9 && x 4 13).toNat = 0 := by
        have r43393 := hand1 (x 4 9) (x 4 13)
        have b43394 := hb (x 4 9)
        have b43395 := hb (x 4 9 && x 4 13)
        clear * - r43393 b43394 b43395 d43376
        omega
      have d43396 : (x 3 10).toNat = 0 := by
        have r43397 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43398 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
        have e43399 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
        have e43400 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
        have e43401 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
        have e43402 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
        have e43403 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
        have b43404 := hb (x (-2) 7)
        have b43405 := hb (x (-1) 6)
        have b43406 := hb (x 0 5)
        have b43407 := hb (x 1 4)
        have b43408 := hb (x 2 11)
        have b43409 := hb (x 3 10)
        have b43410 := hb (x 4 9)
        have b43411 := hb (x 5 8)
        clear * - r43397 e43398 e43399 e43400 e43401 e43402 e43403 b43404 b43405 b43406 b43407 b43408 b43409 b43410 b43411 d43356 d43376 d43033 d43275
        omega
      have d43412 : (x 2 11).toNat = 0 := by
        have r43413 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43414 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
        have e43415 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
        have e43416 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
        have e43417 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
        have e43418 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
        have e43419 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
        have b43420 := hb (x (-2) 7)
        have b43421 := hb (x (-1) 6)
        have b43422 := hb (x 0 5)
        have b43423 := hb (x 1 4)
        have b43424 := hb (x 2 11)
        have b43425 := hb (x 3 10)
        have b43426 := hb (x 4 9)
        have b43427 := hb (x 5 8)
        clear * - r43413 e43414 e43415 e43416 e43417 e43418 e43419 b43420 b43421 b43422 b43423 b43424 b43425 b43426 b43427 d43356 d43376 d43396 d43033 d43275
        omega
      cases h43428 : x 0 8
      · have f43429 : (x 0 8).toNat = 0 := by rw [h43428]; rfl
        have d43430 : (x 0 2 && x 0 8).toNat = 0 := by
          have r43431 := hand2 (x 0 2) (x 0 8)
          have b43432 := hb (x 0 8)
          have b43433 := hb (x 0 2 && x 0 8)
          clear * - r43431 b43432 b43433 f43429
          omega
        have d43434 : (x 0 4 && x 0 8).toNat = 0 := by
          have r43435 := hand2 (x 0 4) (x 0 8)
          have b43436 := hb (x 0 8)
          have b43437 := hb (x 0 4 && x 0 8)
          clear * - r43435 b43436 b43437 f43429
          omega
        have r43438 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r43439 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r43440 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r43441 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43442 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e43443 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e43444 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e43445 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e43446 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e43447 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have r43448 : (x (-11) 12).toNat + (x (-12) 1 && x (-12) 13).toNat + (x (-13) 2 && x (-13) 14).toNat + (x (-14) 3).toNat = 1 := by have q := hd12 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43449 : (x (-12) 1 && x (-12) 13).toNat = (x (-12) 13).toNat := handr _ _ (fun h => hp13 (-12) (h))
        have e43450 : (x (-13) 2 && x (-13) 14).toNat = (x (-13) 2).toNat := handl _ _ (fun h => hp2 (-13) (h))
        have r43451 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43452 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e43453 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have r43454 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43455 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e43456 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have r43457 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r43458 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e43459 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
        have e43460 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
        have r43461 : 1 ≤ (x 2 6).toNat + (x 1 1 && x 1 7).toNat + (x 0 2 && x 0 8).toNat + (x (-1) 3 && x (-1) 9).toNat + (x (-2) 4 && x (-2) 10).toNat + (x (-3) 5 && x (-3) 11).toNat + (x (-4) 6 && x (-4) 12).toNat + (x (-5) 7 && x (-5) 13).toNat + (x (-6) 8 && x (-6) 14).toNat + (x (-7) 9).toNat := by have q := hcov6 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r43462 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r43463 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r43464 : 1 ≤ (x (-7) 11).toNat + (x (-8) 1 && x (-8) 12).toNat + (x (-9) 2 && x (-9) 13).toNat + (x (-10) 3 && x (-10) 14).toNat + (x (-11) 4).toNat := by have q := hcov11 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r43465 : 1 ≤ (x (-11) 13).toNat + (x (-12) 1 && x (-12) 14).toNat + (x (-13) 2).toNat := by have q := hcov13 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r43466 : (x (-11) 4).toNat ≤ (x (-11) 12).toNat := himp _ _ (hp4 (-11))
        have r43467 : (x (-11) 5).toNat ≤ (x (-11) 13).toNat := himp _ _ (hp5 (-11))
        have r43468 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
        have r43469 := hand1 (x (-4) 8) (x (-4) 12)
        have r43470 := hand1 (x (-5) 9) (x (-5) 13)
        have r43471 := hand2 (x 1 1) (x 1 7)
        have r43472 := hand1 (x (-4) 6) (x (-4) 12)
        have r43473 := hand1 (x (-5) 7) (x (-5) 13)
        have r43474 := hand1 (x (-6) 8) (x (-6) 14)
        have r43475 := hand2 (x 6 1) (x 6 10)
        have r43476 := hand2 (x 5 2) (x 5 11)
        have r43477 := hand1 (x (-7) 1) (x (-7) 11)
        have r43478 := hand2 (x (-8) 2) (x (-8) 12)
        have r43479 := hand2 (x (-9) 3) (x (-9) 13)
        have r43480 := hand2 (x (-10) 4) (x (-10) 14)
        have r43481 := hand2 (x (-8) 1) (x (-8) 12)
        have r43482 := hand2 (x (-9) 2) (x (-9) 13)
        have r43483 := hand2 (x (-10) 3) (x (-10) 14)
        have r43484 := hand2 (x (-12) 1) (x (-12) 14)
        have b43538 := hb (x 7 1)
        linarith only [r43438, r43439, r43440, r43441, e43442, e43443, e43444, e43445, e43446, e43447, r43448, e43449, e43450, r43451, e43452, e43453, r43454, e43455, e43456, r43457, r43458, e43459, e43460, r43461, r43462, r43463, r43464, r43465, r43466, r43467, r43468, r43469, r43470, r43471, r43472, r43473, r43474, r43475, r43476, r43477, r43478, r43479, r43480, r43481, r43482, r43483, r43484, b43538, g1, g2, g4, g5, d43013, g6, d42972, f42947, g9, f43429, g11, g13, g14, g17, g18, g20, g23, g27, g28, d43434, g29, g30, g31, d43430, d42976, g34, g35, g44, d42555, g45]
      · have f43572 : (x 0 8).toNat = 1 := by rw [h43428]; rfl
        have d43573 : (x (-4) 4).toNat = 0 := by
          have r43574 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e43575 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e43576 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e43577 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e43578 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e43579 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e43580 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b43581 := hb (x (-7) 7)
          have b43582 := hb (x (-6) 6)
          have b43583 := hb (x (-5) 5)
          have b43584 := hb (x (-4) 4)
          have b43585 := hb (x (-3) 11)
          have b43586 := hb (x (-2) 10)
          have b43587 := hb (x (-1) 9)
          have b43588 := hb (x 0 8)
          clear * - r43574 e43575 e43576 e43577 e43578 e43579 e43580 b43581 b43582 b43583 b43584 b43585 b43586 b43587 b43588 f43572 d42972 g5 g2
          omega
        have d43589 : (x (-4) 4 && x (-4) 14).toNat = 0 := by
          have r43590 := hand1 (x (-4) 4) (x (-4) 14)
          have b43591 := hb (x (-4) 4)
          have b43592 := hb (x (-4) 4 && x (-4) 14)
          clear * - r43590 b43591 b43592 d43573
          omega
        have d43593 : (x (-4) 4 && x (-4) 13).toNat = 0 := by
          have r43594 := hand1 (x (-4) 4) (x (-4) 13)
          have b43595 := hb (x (-4) 4)
          have b43596 := hb (x (-4) 4 && x (-4) 13)
          clear * - r43594 b43595 b43596 d43573
          omega
        have d43597 : (x (-4) 2 && x (-4) 4).toNat = 0 := by
          have r43598 := hand2 (x (-4) 2) (x (-4) 4)
          have b43599 := hb (x (-4) 4)
          have b43600 := hb (x (-4) 2 && x (-4) 4)
          clear * - r43598 b43599 b43600 d43573
          omega
        have d43601 : (x 0 11).toNat = 1 := by
          have r43602 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b43603 := hb (x (-4) 4)
          have b43604 := hb (x 0 11)
          have b43605 := hb (x (-1) 1 && x (-1) 12)
          have b43606 := hb (x (-2) 2 && x (-2) 13)
          have b43607 := hb (x (-3) 3 && x (-3) 14)
          clear * - r43602 b43603 b43604 b43605 b43606 b43607 d42960 g50 g51 d43573
          omega
        have d43608 : (x 3 8).toNat = 0 := by
          have r43609 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e43610 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e43611 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e43612 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e43613 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e43614 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e43615 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b43616 := hb (x (-4) 7)
          have b43617 := hb (x (-3) 6)
          have b43618 := hb (x (-2) 5)
          have b43619 := hb (x (-1) 4)
          have b43620 := hb (x 0 11)
          have b43621 := hb (x 1 10)
          have b43622 := hb (x 2 9)
          have b43623 := hb (x 3 8)
          clear * - r43609 e43610 e43611 e43612 e43613 e43614 e43615 b43616 b43617 b43618 b43619 b43620 b43621 b43622 b43623 g15 d43601
          omega
        have d43624 : (x 3 8 && x 3 13).toNat = 0 := by
          have r43625 := hand1 (x 3 8) (x 3 13)
          have b43626 := hb (x 3 8)
          have b43627 := hb (x 3 8 && x 3 13)
          clear * - r43625 b43626 b43627 d43608
          omega
        have d43628 : (x 2 9).toNat = 0 := by
          have r43629 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e43630 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e43631 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e43632 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e43633 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e43634 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e43635 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b43636 := hb (x (-4) 7)
          have b43637 := hb (x (-3) 6)
          have b43638 := hb (x (-2) 5)
          have b43639 := hb (x (-1) 4)
          have b43640 := hb (x 0 11)
          have b43641 := hb (x 1 10)
          have b43642 := hb (x 2 9)
          have b43643 := hb (x 3 8)
          clear * - r43629 e43630 e43631 e43632 e43633 e43634 e43635 b43636 b43637 b43638 b43639 b43640 b43641 b43642 b43643 d43608 g15 d43601
          omega
        have d43644 : (x (-1) 4).toNat = 0 := by
          have r43645 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e43646 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e43647 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e43648 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e43649 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e43650 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e43651 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b43652 := hb (x (-4) 7)
          have b43653 := hb (x (-3) 6)
          have b43654 := hb (x (-2) 5)
          have b43655 := hb (x (-1) 4)
          have b43656 := hb (x 0 11)
          have b43657 := hb (x 1 10)
          have b43658 := hb (x 2 9)
          have b43659 := hb (x 3 8)
          clear * - r43645 e43646 e43647 e43648 e43649 e43650 e43651 b43652 b43653 b43654 b43655 b43656 b43657 b43658 b43659 d43608 d43628 g15 d43601
          omega
        have d43660 : (x (-2) 5).toNat = 0 := by
          have r43661 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e43662 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e43663 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e43664 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e43665 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e43666 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e43667 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b43668 := hb (x (-4) 7)
          have b43669 := hb (x (-3) 6)
          have b43670 := hb (x (-2) 5)
          have b43671 := hb (x (-1) 4)
          have b43672 := hb (x 0 11)
          have b43673 := hb (x 1 10)
          have b43674 := hb (x 2 9)
          have b43675 := hb (x 3 8)
          clear * - r43661 e43662 e43663 e43664 e43665 e43666 e43667 b43668 b43669 b43670 b43671 b43672 b43673 b43674 b43675 d43608 d43628 g15 d43601 d43644
          omega
        have d43676 : (x (-3) 6).toNat = 0 := by
          have r43677 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e43678 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e43679 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e43680 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e43681 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e43682 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e43683 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b43684 := hb (x (-4) 7)
          have b43685 := hb (x (-3) 6)
          have b43686 := hb (x (-2) 5)
          have b43687 := hb (x (-1) 4)
          have b43688 := hb (x 0 11)
          have b43689 := hb (x 1 10)
          have b43690 := hb (x 2 9)
          have b43691 := hb (x 3 8)
          clear * - r43677 e43678 e43679 e43680 e43681 e43682 e43683 b43684 b43685 b43686 b43687 b43688 b43689 b43690 b43691 d43608 d43628 g15 d43601 d43644 d43660
          omega
        have d43692 : (x (-3) 2 && x (-3) 6).toNat = 0 := by
          have r43693 := hand2 (x (-3) 2) (x (-3) 6)
          have b43694 := hb (x (-3) 6)
          have b43695 := hb (x (-3) 2 && x (-3) 6)
          clear * - r43693 b43694 b43695 d43676
          omega
        have d43696 : (x (-4) 7).toNat = 0 := by
          have r43697 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e43698 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e43699 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e43700 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e43701 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e43702 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e43703 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b43704 := hb (x (-4) 7)
          have b43705 := hb (x (-3) 6)
          have b43706 := hb (x (-2) 5)
          have b43707 := hb (x (-1) 4)
          have b43708 := hb (x 0 11)
          have b43709 := hb (x 1 10)
          have b43710 := hb (x 2 9)
          have b43711 := hb (x 3 8)
          clear * - r43697 e43698 e43699 e43700 e43701 e43702 e43703 b43704 b43705 b43706 b43707 b43708 b43709 b43710 b43711 d43608 d43628 g15 d43601 d43644 d43660 d43676
          omega
        have d43712 : (x (-4) 3 && x (-4) 7).toNat = 0 := by
          have r43713 := hand2 (x (-4) 3) (x (-4) 7)
          have b43714 := hb (x (-4) 7)
          have b43715 := hb (x (-4) 3 && x (-4) 7)
          clear * - r43713 b43714 b43715 d43696
          omega
        have d43716 : (x (-5) 5).toNat = 0 := by
          have r43717 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e43718 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e43719 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e43720 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e43721 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e43722 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e43723 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b43724 := hb (x (-7) 7)
          have b43725 := hb (x (-6) 6)
          have b43726 := hb (x (-5) 5)
          have b43727 := hb (x (-4) 4)
          have b43728 := hb (x (-3) 11)
          have b43729 := hb (x (-2) 10)
          have b43730 := hb (x (-1) 9)
          have b43731 := hb (x 0 8)
          clear * - r43717 e43718 e43719 e43720 e43721 e43722 e43723 b43724 b43725 b43726 b43727 b43728 b43729 b43730 b43731 f43572 d42972 g5 g2 d43573
          omega
        have d43732 : (x (-5) 5 && x (-5) 14).toNat = 0 := by
          have r43733 := hand1 (x (-5) 5) (x (-5) 14)
          have b43734 := hb (x (-5) 5)
          have b43735 := hb (x (-5) 5 && x (-5) 14)
          clear * - r43733 b43734 b43735 d43716
          omega
        have d43736 : (x (-5) 3 && x (-5) 5).toNat = 0 := by
          have r43737 := hand2 (x (-5) 3) (x (-5) 5)
          have b43738 := hb (x (-5) 5)
          have b43739 := hb (x (-5) 3 && x (-5) 5)
          clear * - r43737 b43738 b43739 d43716
          omega
        have d43740 : (x 0 10).toNat = 1 := by
          have r43741 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b43742 := hb (x (-5) 5)
          have b43743 := hb (x 0 10)
          have b43744 := hb (x (-1) 1 && x (-1) 11)
          have b43745 := hb (x (-2) 2 && x (-2) 12)
          have b43746 := hb (x (-3) 3 && x (-3) 13)
          have b43747 := hb (x (-4) 4 && x (-4) 14)
          clear * - r43741 b43742 b43743 b43744 b43745 b43746 b43747 d42964 g47 g48 d43589 d43716
          omega
        have d43748 : (x 2 8).toNat = 0 := by
          have r43749 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e43750 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
          have e43751 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
          have e43752 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
          have e43753 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
          have e43754 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
          have e43755 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
          have b43756 := hb (x (-5) 7)
          have b43757 := hb (x (-4) 6)
          have b43758 := hb (x (-3) 5)
          have b43759 := hb (x (-2) 4)
          have b43760 := hb (x (-1) 11)
          have b43761 := hb (x 0 10)
          have b43762 := hb (x 1 9)
          have b43763 := hb (x 2 8)
          clear * - r43749 e43750 e43751 e43752 e43753 e43754 e43755 b43756 b43757 b43758 b43759 b43760 b43761 b43762 b43763 d43740 d43021
          omega
        have d43764 : (x 1 9).toNat = 0 := by
          have r43765 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e43766 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
          have e43767 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
          have e43768 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
          have e43769 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
          have e43770 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
          have e43771 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
          have b43772 := hb (x (-5) 7)
          have b43773 := hb (x (-4) 6)
          have b43774 := hb (x (-3) 5)
          have b43775 := hb (x (-2) 4)
          have b43776 := hb (x (-1) 11)
          have b43777 := hb (x 0 10)
          have b43778 := hb (x 1 9)
          have b43779 := hb (x 2 8)
          clear * - r43765 e43766 e43767 e43768 e43769 e43770 e43771 b43772 b43773 b43774 b43775 b43776 b43777 b43778 b43779 d43748 d43740 d43021
          omega
        have d43780 : (x (-2) 4).toNat = 0 := by
          have r43781 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e43782 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
          have e43783 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
          have e43784 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
          have e43785 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
          have e43786 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
          have e43787 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
          have b43788 := hb (x (-5) 7)
          have b43789 := hb (x (-4) 6)
          have b43790 := hb (x (-3) 5)
          have b43791 := hb (x (-2) 4)
          have b43792 := hb (x (-1) 11)
          have b43793 := hb (x 0 10)
          have b43794 := hb (x 1 9)
          have b43795 := hb (x 2 8)
          clear * - r43781 e43782 e43783 e43784 e43785 e43786 e43787 b43788 b43789 b43790 b43791 b43792 b43793 b43794 b43795 d43748 d43764 d43740 d43021
          omega
        have d43796 : (x (-3) 5).toNat = 0 := by
          have r43797 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e43798 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
          have e43799 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
          have e43800 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
          have e43801 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
          have e43802 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
          have e43803 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
          have b43804 := hb (x (-5) 7)
          have b43805 := hb (x (-4) 6)
          have b43806 := hb (x (-3) 5)
          have b43807 := hb (x (-2) 4)
          have b43808 := hb (x (-1) 11)
          have b43809 := hb (x 0 10)
          have b43810 := hb (x 1 9)
          have b43811 := hb (x 2 8)
          clear * - r43797 e43798 e43799 e43800 e43801 e43802 e43803 b43804 b43805 b43806 b43807 b43808 b43809 b43810 b43811 d43748 d43764 d43740 d43021 d43780
          omega
        have d43812 : (x (-4) 6).toNat = 0 := by
          have r43813 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e43814 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
          have e43815 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
          have e43816 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
          have e43817 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
          have e43818 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
          have e43819 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
          have b43820 := hb (x (-5) 7)
          have b43821 := hb (x (-4) 6)
          have b43822 := hb (x (-3) 5)
          have b43823 := hb (x (-2) 4)
          have b43824 := hb (x (-1) 11)
          have b43825 := hb (x 0 10)
          have b43826 := hb (x 1 9)
          have b43827 := hb (x 2 8)
          clear * - r43813 e43814 e43815 e43816 e43817 e43818 e43819 b43820 b43821 b43822 b43823 b43824 b43825 b43826 b43827 d43748 d43764 d43740 d43021 d43780 d43796
          omega
        have d43828 : (x (-4) 2 && x (-4) 6).toNat = 0 := by
          have r43829 := hand2 (x (-4) 2) (x (-4) 6)
          have b43830 := hb (x (-4) 6)
          have b43831 := hb (x (-4) 2 && x (-4) 6)
          clear * - r43829 b43830 b43831 d43812
          omega
        have d43832 : (x (-5) 7).toNat = 0 := by
          have r43833 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e43834 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
          have e43835 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
          have e43836 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
          have e43837 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
          have e43838 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
          have e43839 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
          have b43840 := hb (x (-5) 7)
          have b43841 := hb (x (-4) 6)
          have b43842 := hb (x (-3) 5)
          have b43843 := hb (x (-2) 4)
          have b43844 := hb (x (-1) 11)
          have b43845 := hb (x 0 10)
          have b43846 := hb (x 1 9)
          have b43847 := hb (x 2 8)
          clear * - r43833 e43834 e43835 e43836 e43837 e43838 e43839 b43840 b43841 b43842 b43843 b43844 b43845 b43846 b43847 d43748 d43764 d43740 d43021 d43780 d43796 d43812
          omega
        have d43848 : (x (-5) 3 && x (-5) 7).toNat = 0 := by
          have r43849 := hand2 (x (-5) 3) (x (-5) 7)
          have b43850 := hb (x (-5) 7)
          have b43851 := hb (x (-5) 3 && x (-5) 7)
          clear * - r43849 b43850 b43851 d43832
          omega
        have d43852 : (x (-6) 6).toNat = 0 := by
          have r43853 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e43854 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e43855 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e43856 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e43857 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e43858 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e43859 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b43860 := hb (x (-7) 7)
          have b43861 := hb (x (-6) 6)
          have b43862 := hb (x (-5) 5)
          have b43863 := hb (x (-4) 4)
          have b43864 := hb (x (-3) 11)
          have b43865 := hb (x (-2) 10)
          have b43866 := hb (x (-1) 9)
          have b43867 := hb (x 0 8)
          clear * - r43853 e43854 e43855 e43856 e43857 e43858 e43859 b43860 b43861 b43862 b43863 b43864 b43865 b43866 b43867 f43572 d42972 g5 g2 d43573 d43716
          omega
        have d43868 : (x (-6) 4 && x (-6) 6).toNat = 0 := by
          have r43869 := hand2 (x (-6) 4) (x (-6) 6)
          have b43870 := hb (x (-6) 6)
          have b43871 := hb (x (-6) 4 && x (-6) 6)
          clear * - r43869 b43870 b43871 d43852
          omega
        have d43872 : (x 0 9).toNat = 1 := by
          have r43873 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b43874 := hb (x (-6) 6)
          have b43875 := hb (x 0 9)
          have b43876 := hb (x (-1) 1 && x (-1) 10)
          have b43877 := hb (x (-2) 2 && x (-2) 11)
          have b43878 := hb (x (-3) 3 && x (-3) 12)
          have b43879 := hb (x (-4) 4 && x (-4) 13)
          have b43880 := hb (x (-5) 5 && x (-5) 14)
          clear * - r43873 b43874 b43875 b43876 b43877 b43878 b43879 b43880 d42968 g40 g41 d43593 d43732 d43852
          omega
        have d43881 : (x 1 8).toNat = 0 := by
          have r43882 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e43883 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e43884 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e43885 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e43886 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e43887 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e43888 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b43889 := hb (x (-6) 7)
          have b43890 := hb (x (-5) 6)
          have b43891 := hb (x (-4) 5)
          have b43892 := hb (x (-3) 4)
          have b43893 := hb (x (-2) 11)
          have b43894 := hb (x (-1) 10)
          have b43895 := hb (x 0 9)
          have b43896 := hb (x 1 8)
          clear * - r43882 e43883 e43884 e43885 e43886 e43887 e43888 b43889 b43890 b43891 b43892 b43893 b43894 b43895 b43896 d43872 d43045 d43057
          omega
        have d43897 : (x (-3) 4).toNat = 0 := by
          have r43898 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e43899 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e43900 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e43901 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e43902 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e43903 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e43904 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b43905 := hb (x (-6) 7)
          have b43906 := hb (x (-5) 6)
          have b43907 := hb (x (-4) 5)
          have b43908 := hb (x (-3) 4)
          have b43909 := hb (x (-2) 11)
          have b43910 := hb (x (-1) 10)
          have b43911 := hb (x 0 9)
          have b43912 := hb (x 1 8)
          clear * - r43898 e43899 e43900 e43901 e43902 e43903 e43904 b43905 b43906 b43907 b43908 b43909 b43910 b43911 b43912 d43881 d43872 d43045 d43057
          omega
        have d43913 : (x (-4) 5).toNat = 0 := by
          have r43914 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e43915 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e43916 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e43917 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e43918 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e43919 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e43920 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b43921 := hb (x (-6) 7)
          have b43922 := hb (x (-5) 6)
          have b43923 := hb (x (-4) 5)
          have b43924 := hb (x (-3) 4)
          have b43925 := hb (x (-2) 11)
          have b43926 := hb (x (-1) 10)
          have b43927 := hb (x 0 9)
          have b43928 := hb (x 1 8)
          clear * - r43914 e43915 e43916 e43917 e43918 e43919 e43920 b43921 b43922 b43923 b43924 b43925 b43926 b43927 b43928 d43881 d43872 d43045 d43057 d43897
          omega
        have d43929 : (x (-5) 6).toNat = 0 := by
          have r43930 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e43931 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e43932 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e43933 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e43934 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e43935 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e43936 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b43937 := hb (x (-6) 7)
          have b43938 := hb (x (-5) 6)
          have b43939 := hb (x (-4) 5)
          have b43940 := hb (x (-3) 4)
          have b43941 := hb (x (-2) 11)
          have b43942 := hb (x (-1) 10)
          have b43943 := hb (x 0 9)
          have b43944 := hb (x 1 8)
          clear * - r43930 e43931 e43932 e43933 e43934 e43935 e43936 b43937 b43938 b43939 b43940 b43941 b43942 b43943 b43944 d43881 d43872 d43045 d43057 d43897 d43913
          omega
        have d43945 : (x (-6) 7).toNat = 0 := by
          have r43946 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e43947 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e43948 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e43949 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e43950 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e43951 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e43952 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b43953 := hb (x (-6) 7)
          have b43954 := hb (x (-5) 6)
          have b43955 := hb (x (-4) 5)
          have b43956 := hb (x (-3) 4)
          have b43957 := hb (x (-2) 11)
          have b43958 := hb (x (-1) 10)
          have b43959 := hb (x 0 9)
          have b43960 := hb (x 1 8)
          clear * - r43946 e43947 e43948 e43949 e43950 e43951 e43952 b43953 b43954 b43955 b43956 b43957 b43958 b43959 b43960 d43881 d43872 d43045 d43057 d43897 d43913 d43929
          omega
        have d43961 : (x (-7) 7).toNat = 0 := by
          have r43962 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e43963 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e43964 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e43965 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e43966 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e43967 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e43968 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b43969 := hb (x (-7) 7)
          have b43970 := hb (x (-6) 6)
          have b43971 := hb (x (-5) 5)
          have b43972 := hb (x (-4) 4)
          have b43973 := hb (x (-3) 11)
          have b43974 := hb (x (-2) 10)
          have b43975 := hb (x (-1) 9)
          have b43976 := hb (x 0 8)
          clear * - r43962 e43963 e43964 e43965 e43966 e43967 e43968 b43969 b43970 b43971 b43972 b43973 b43974 b43975 b43976 f43572 d42972 g5 g2 d43573 d43716 d43852
          omega
        have d43977 : (x (-7) 5 && x (-7) 7).toNat = 0 := by
          have r43978 := hand2 (x (-7) 5) (x (-7) 7)
          have b43979 := hb (x (-7) 7)
          have b43980 := hb (x (-7) 5 && x (-7) 7)
          clear * - r43978 b43979 b43980 d43961
          omega
        cases h43981 : x 1 7
        · have f43982 : (x 1 7).toNat = 0 := by rw [h43981]; rfl
          cases h43983 : x (-1) 8
          · have f43984 : (x (-1) 8).toNat = 0 := by rw [h43983]; rfl
            cases h43985 : x (-1) 12
            · have f43986 : (x (-1) 12).toNat = 0 := by rw [h43985]; rfl
              cases h43987 : x (-1) 14
              · have f43988 : (x (-1) 14).toNat = 0 := by rw [h43987]; rfl
                cases h43989 : x 2 1
                · have f43990 : (x 2 1).toNat = 0 := by rw [h43989]; rfl
                  have d43991 : (x 3 14).toNat = 1 := by
                    have r43992 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b43993 := hb (x 2 1)
                    have b43994 := hb (x 3 14)
                    clear * - r43992 b43993 b43994 f43990
                    omega
                  have r43995 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r43996 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r43997 : (x 16 1).toNat + (x 15 2).toNat + (x 14 3).toNat + (x 13 4).toNat + (x 12 5).toNat + (x 11 6).toNat + (x 10 7).toNat + (x 9 8).toNat + (x 8 9).toNat + (x 7 10).toNat + (x 6 11).toNat + (x 5 12).toNat + (x 4 13).toNat + (x 3 14).toNat = 3 := by have q := hcount 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r43998 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e43999 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
                  have e44000 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
                  have e44001 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
                  have e44002 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
                  have e44003 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
                  have e44004 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
                  have r44005 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44006 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                  have e44007 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                  have e44008 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                  have e44009 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                  have e44010 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                  have e44011 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                  have r44012 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44013 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
                  have e44014 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
                  have e44015 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
                  have e44016 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
                  have e44017 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
                  have e44018 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
                  have r44019 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44020 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
                  have e44021 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
                  have r44022 : 1 ≤ (x 15 2).toNat + (x 14 1 && x 14 3).toNat + (x 13 2 && x 13 4).toNat + (x 12 3 && x 12 5).toNat + (x 11 4 && x 11 6).toNat + (x 10 5 && x 10 7).toNat + (x 9 6 && x 9 8).toNat + (x 8 7 && x 8 9).toNat + (x 7 8 && x 7 10).toNat + (x 6 9 && x 6 11).toNat + (x 5 10 && x 5 12).toNat + (x 4 11 && x 4 13).toNat + (x 3 12 && x 3 14).toNat + (x 2 13).toNat := by have q := hcov2 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r44023 : 1 ≤ (x 15 4).toNat + (x 14 1 && x 14 5).toNat + (x 13 2 && x 13 6).toNat + (x 12 3 && x 12 7).toNat + (x 11 4 && x 11 8).toNat + (x 10 5 && x 10 9).toNat + (x 9 6 && x 9 10).toNat + (x 8 7 && x 8 11).toNat + (x 7 8 && x 7 12).toNat + (x 6 9 && x 6 13).toNat + (x 5 10 && x 5 14).toNat + (x 4 11).toNat := by have q := hcov4 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44024 : (x 14 1 && x 14 5).toNat = (x 14 5).toNat := handr _ _ (fun h => hp13 14 (hp5 14 (h)))
                  have e44025 : (x 5 10 && x 5 14).toNat = (x 5 10).toNat := handl _ _ (fun h => hp2 5 (hp10 5 (h)))
                  have r44026 : 1 ≤ (x 11 5).toNat + (x 10 1 && x 10 6).toNat + (x 9 2 && x 9 7).toNat + (x 8 3 && x 8 8).toNat + (x 7 4 && x 7 9).toNat + (x 6 5 && x 6 10).toNat + (x 5 6 && x 5 11).toNat + (x 4 7 && x 4 12).toNat + (x 3 8 && x 3 13).toNat + (x 2 9 && x 2 14).toNat + (x 1 10).toNat := by have q := hcov5 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r44027 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r44028 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r44029 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r44030 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r44031 : (x 16 13).toNat ≤ (x 16 1).toNat := himp _ _ (hp13 16)
                  have r44032 := hand2 (x 14 1) (x 14 3)
                  have r44033 := hand2 (x 13 2) (x 13 4)
                  have r44034 := hand2 (x 12 3) (x 12 5)
                  have r44035 := hand2 (x 11 4) (x 11 6)
                  have r44036 := hand2 (x 10 5) (x 10 7)
                  have r44037 := hand2 (x 9 6) (x 9 8)
                  have r44038 := hand2 (x 8 7) (x 8 9)
                  have r44039 := hand2 (x 13 2) (x 13 6)
                  have r44040 := hand2 (x 12 3) (x 12 7)
                  have r44041 := hand2 (x 11 4) (x 11 8)
                  have r44042 := hand2 (x 10 5) (x 10 9)
                  have r44043 := hand2 (x 9 6) (x 9 10)
                  have r44044 := hand2 (x 8 7) (x 8 11)
                  have r44045 := hand2 (x 10 1) (x 10 6)
                  have r44046 := hand2 (x 9 2) (x 9 7)
                  have r44047 := hand2 (x 8 3) (x 8 8)
                  have r44048 := hand1 (x 7 4) (x 7 9)
                  have r44049 := hand1 (x 6 5) (x 6 10)
                  have r44050 := hand1 (x 5 6) (x 5 11)
                  have r44051 := hand2 (x 6 1) (x 6 10)
                  have r44052 := hand2 (x 5 2) (x 5 11)
                  have r44053 := hand2 (x 6 1) (x 6 11)
                  have r44054 := hand2 (x 5 2) (x 5 12)
                  have r44055 := hand2 (x 4 3) (x 4 13)
                  have r44056 := hand2 (x 15 1) (x 15 12)
                  have r44057 := hand2 (x 14 2) (x 14 13)
                  have r44058 := hand1 (x 13 3) (x 13 14)
                  have r44059 := hand1 (x 15 1) (x 15 14)
                  have b44111 := hb (x 14 1)
                  linarith only [r43995, r43996, r43997, r43998, e43999, e44000, e44001, e44002, e44003, e44004, r44005, e44006, e44007, e44008, e44009, e44010, e44011, r44012, e44013, e44014, e44015, e44016, e44017, e44018, r44019, e44020, e44021, r44022, r44023, e44024, e44025, r44026, r44027, r44028, r44029, r44030, r44031, r44032, r44033, r44034, r44035, r44036, r44037, r44038, r44039, r44040, r44041, r44042, r44043, r44044, r44045, r44046, r44047, r44048, r44049, r44050, r44051, r44052, r44053, r44054, r44055, r44056, r44057, r44058, r44059, b44111, g14, g15, g16, d42559, d43263, g19, d43243, g21, d43991, d42511, g25, d42487, d42463, d42439, d42459, d42483, d42507, d42531, d43259, d42455, d42479, g32, d43624, g33, g44, d42555, g45, d42551]
                · have f44170 : (x 2 1).toNat = 1 := by rw [h43989]; rfl
                  have d44171 : (x 3 14).toNat = 0 := by
                    have r44172 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b44173 := hb (x 2 1)
                    have b44174 := hb (x 3 14)
                    clear * - r44172 b44173 b44174 f44170
                    omega
                  have d44175 : (x 3 1 && x 3 14).toNat = 0 := by
                    have r44176 := hand2 (x 3 1) (x 3 14)
                    have b44177 := hb (x 3 14)
                    have b44178 := hb (x 3 1 && x 3 14)
                    clear * - r44176 b44177 b44178 d44171
                    omega
                  have d44179 : (x 3 2).toNat = 0 := by
                    have r44180 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
                    have b44181 := hb (x 3 2)
                    have b44182 := hb (x 3 14)
                    clear * - r44180 b44181 b44182 d44171
                    omega
                  have d44183 : (x 5 13).toNat = 1 := by
                    have r44184 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b44185 := hb (x 3 2)
                    have b44186 := hb (x 5 13)
                    have b44187 := hb (x 4 1 && x 4 14)
                    clear * - r44184 b44185 b44186 b44187 g56 d44179
                    omega
                  have d44188 : (x 5 1).toNat = 1 := by
                    have r44189 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
                    have b44190 := hb (x 5 1)
                    have b44191 := hb (x 5 13)
                    clear * - r44189 b44190 b44191 d44183
                    omega
                  have d44192 : (x 6 14).toNat = 0 := by
                    have r44193 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b44194 := hb (x 5 1)
                    have b44195 := hb (x 6 14)
                    clear * - r44193 b44194 b44195 d44188
                    omega
                  have d44196 : (x 6 1 && x 6 14).toNat = 0 := by
                    have r44197 := hand2 (x 6 1) (x 6 14)
                    have b44198 := hb (x 6 14)
                    have b44199 := hb (x 6 1 && x 6 14)
                    clear * - r44197 b44198 b44199 d44192
                    omega
                  have d44200 : (x 6 2).toNat = 0 := by
                    have r44201 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
                    have b44202 := hb (x 6 2)
                    have b44203 := hb (x 6 14)
                    clear * - r44201 b44202 b44203 d44192
                    omega
                  have d44204 : (x 4 13).toNat = 1 := by
                    have r44205 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b44206 := hb (x 2 2)
                    have b44207 := hb (x 4 13)
                    have b44208 := hb (x 3 1 && x 3 14)
                    clear * - r44205 b44206 b44207 b44208 d44175 g17
                    omega
                  have d44209 : (x 4 1).toNat = 1 := by
                    have r44210 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
                    have b44211 := hb (x 4 1)
                    have b44212 := hb (x 4 13)
                    clear * - r44210 b44211 b44212 d44204
                    omega
                  have d44213 : (x 5 14).toNat = 0 := by
                    have r44214 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b44215 := hb (x 4 1)
                    have b44216 := hb (x 5 14)
                    clear * - r44214 b44215 b44216 d44209
                    omega
                  have d44217 : (x 5 1 && x 5 14).toNat = 0 := by
                    have r44218 := hand2 (x 5 1) (x 5 14)
                    have b44219 := hb (x 5 14)
                    have b44220 := hb (x 5 1 && x 5 14)
                    clear * - r44218 b44219 b44220 d44213
                    omega
                  have d44221 : (x 6 13).toNat = 1 := by
                    have r44222 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b44223 := hb (x 4 2)
                    have b44224 := hb (x 6 13)
                    have b44225 := hb (x 5 1 && x 5 14)
                    clear * - r44222 b44223 b44224 b44225 d44217 g22
                    omega
                  have d44226 : (x 6 1).toNat = 1 := by
                    have r44227 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
                    have b44228 := hb (x 6 1)
                    have b44229 := hb (x 6 13)
                    clear * - r44227 b44228 b44229 d44221
                    omega
                  have d44230 : (x 7 14).toNat = 0 := by
                    have r44231 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b44232 := hb (x 6 1)
                    have b44233 := hb (x 7 14)
                    clear * - r44231 b44232 b44233 d44226
                    omega
                  have d44234 : (x 7 1 && x 7 14).toNat = 0 := by
                    have r44235 := hand2 (x 7 1) (x 7 14)
                    have b44236 := hb (x 7 14)
                    have b44237 := hb (x 7 1 && x 7 14)
                    clear * - r44235 b44236 b44237 d44230
                    omega
                  have d44238 : (x 8 13).toNat = 1 := by
                    have r44239 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b44240 := hb (x 6 2)
                    have b44241 := hb (x 8 13)
                    have b44242 := hb (x 7 1 && x 7 14)
                    clear * - r44239 b44240 b44241 b44242 d44234 d44200
                    omega
                  have d44243 : (x 8 1).toNat = 1 := by
                    have r44244 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
                    have b44245 := hb (x 8 1)
                    have b44246 := hb (x 8 13)
                    clear * - r44244 b44245 b44246 d44238
                    omega
                  have d44247 : (x 9 14).toNat = 0 := by
                    have r44248 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b44249 := hb (x 8 1)
                    have b44250 := hb (x 9 14)
                    clear * - r44248 b44249 b44250 d44243
                    omega
                  have d44251 : (x 9 1 && x 9 14).toNat = 0 := by
                    have r44252 := hand2 (x 9 1) (x 9 14)
                    have b44253 := hb (x 9 14)
                    have b44254 := hb (x 9 1 && x 9 14)
                    clear * - r44252 b44253 b44254 d44247
                    omega
                  have d44255 : (x 9 2).toNat = 0 := by
                    have r44256 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
                    have b44257 := hb (x 9 2)
                    have b44258 := hb (x 9 14)
                    clear * - r44256 b44257 b44258 d44247
                    omega
                  have d44259 : (x 7 2).toNat = 0 := by
                    have r44260 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
                    have b44261 := hb (x 7 2)
                    have b44262 := hb (x 7 14)
                    clear * - r44260 b44261 b44262 d44230
                    omega
                  have d44263 : (x 5 2).toNat = 0 := by
                    have r44264 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
                    have b44265 := hb (x 5 2)
                    have b44266 := hb (x 5 14)
                    clear * - r44264 b44265 b44266 d44213
                    omega
                  have d44267 : (x 7 13).toNat = 1 := by
                    have r44268 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b44269 := hb (x 5 2)
                    have b44270 := hb (x 7 13)
                    have b44271 := hb (x 6 1 && x 6 14)
                    clear * - r44268 b44269 b44270 b44271 d44196 d44263
                    omega
                  have d44272 : (x 7 1).toNat = 1 := by
                    have r44273 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
                    have b44274 := hb (x 7 1)
                    have b44275 := hb (x 7 13)
                    clear * - r44273 b44274 b44275 d44267
                    omega
                  have d44276 : (x 8 14).toNat = 0 := by
                    have r44277 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b44278 := hb (x 7 1)
                    have b44279 := hb (x 8 14)
                    clear * - r44277 b44278 b44279 d44272
                    omega
                  have d44280 : (x 8 1 && x 8 14).toNat = 0 := by
                    have r44281 := hand2 (x 8 1) (x 8 14)
                    have b44282 := hb (x 8 14)
                    have b44283 := hb (x 8 1 && x 8 14)
                    clear * - r44281 b44282 b44283 d44276
                    omega
                  have d44284 : (x 9 13).toNat = 1 := by
                    have r44285 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b44286 := hb (x 7 2)
                    have b44287 := hb (x 9 13)
                    have b44288 := hb (x 8 1 && x 8 14)
                    clear * - r44285 b44286 b44287 b44288 d44280 d44259
                    omega
                  have d44289 : (x 9 1).toNat = 1 := by
                    have r44290 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
                    have b44291 := hb (x 9 1)
                    have b44292 := hb (x 9 13)
                    clear * - r44290 b44291 b44292 d44284
                    omega
                  have d44293 : (x 10 14).toNat = 0 := by
                    have r44294 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b44295 := hb (x 9 1)
                    have b44296 := hb (x 10 14)
                    clear * - r44294 b44295 b44296 d44289
                    omega
                  have d44297 : (x 10 1 && x 10 14).toNat = 0 := by
                    have r44298 := hand2 (x 10 1) (x 10 14)
                    have b44299 := hb (x 10 14)
                    have b44300 := hb (x 10 1 && x 10 14)
                    clear * - r44298 b44299 b44300 d44293
                    omega
                  have d44301 : (x 11 13).toNat = 1 := by
                    have r44302 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b44303 := hb (x 9 2)
                    have b44304 := hb (x 11 13)
                    have b44305 := hb (x 10 1 && x 10 14)
                    clear * - r44302 b44303 b44304 b44305 d44297 d44255
                    omega
                  have d44306 : (x 11 1).toNat = 1 := by
                    have r44307 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
                    have b44308 := hb (x 11 1)
                    have b44309 := hb (x 11 13)
                    clear * - r44307 b44308 b44309 d44301
                    omega
                  have d44310 : (x 12 14).toNat = 0 := by
                    have r44311 : (x 12 14).toNat + (x 11 1).toNat = 1 := by have q := hd14 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b44312 := hb (x 11 1)
                    have b44313 := hb (x 12 14)
                    clear * - r44311 b44312 b44313 d44306
                    omega
                  have d44314 : (x 12 1 && x 12 14).toNat = 0 := by
                    have r44315 := hand2 (x 12 1) (x 12 14)
                    have b44316 := hb (x 12 14)
                    have b44317 := hb (x 12 1 && x 12 14)
                    clear * - r44315 b44316 b44317 d44310
                    omega
                  have d44318 : (x 12 2).toNat = 0 := by
                    have r44319 : (x 12 2).toNat ≤ (x 12 14).toNat := himp _ _ (hp2 12)
                    have b44320 := hb (x 12 2)
                    have b44321 := hb (x 12 14)
                    clear * - r44319 b44320 b44321 d44310
                    omega
                  have d44322 : (x 10 2).toNat = 0 := by
                    have r44323 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
                    have b44324 := hb (x 10 2)
                    have b44325 := hb (x 10 14)
                    clear * - r44323 b44324 b44325 d44293
                    omega
                  have d44326 : (x 8 2).toNat = 0 := by
                    have r44327 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
                    have b44328 := hb (x 8 2)
                    have b44329 := hb (x 8 14)
                    clear * - r44327 b44328 b44329 d44276
                    omega
                  have d44330 : (x 10 13).toNat = 1 := by
                    have r44331 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b44332 := hb (x 8 2)
                    have b44333 := hb (x 10 13)
                    have b44334 := hb (x 9 1 && x 9 14)
                    clear * - r44331 b44332 b44333 b44334 d44251 d44326
                    omega
                  have d44335 : (x 10 1).toNat = 1 := by
                    have r44336 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
                    have b44337 := hb (x 10 1)
                    have b44338 := hb (x 10 13)
                    clear * - r44336 b44337 b44338 d44330
                    omega
                  have d44339 : (x 11 14).toNat = 0 := by
                    have r44340 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b44341 := hb (x 10 1)
                    have b44342 := hb (x 11 14)
                    clear * - r44340 b44341 b44342 d44335
                    omega
                  have d44343 : (x 11 1 && x 11 14).toNat = 0 := by
                    have r44344 := hand2 (x 11 1) (x 11 14)
                    have b44345 := hb (x 11 14)
                    have b44346 := hb (x 11 1 && x 11 14)
                    clear * - r44344 b44345 b44346 d44339
                    omega
                  have d44347 : (x 12 13).toNat = 1 := by
                    have r44348 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b44349 := hb (x 10 2)
                    have b44350 := hb (x 12 13)
                    have b44351 := hb (x 11 1 && x 11 14)
                    clear * - r44348 b44349 b44350 b44351 d44343 d44322
                    omega
                  have d44352 : (x 12 1).toNat = 1 := by
                    have r44353 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
                    have b44354 := hb (x 12 1)
                    have b44355 := hb (x 12 13)
                    clear * - r44353 b44354 b44355 d44347
                    omega
                  have d44356 : (x 13 14).toNat = 0 := by
                    have r44357 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b44358 := hb (x 12 1)
                    have b44359 := hb (x 13 14)
                    clear * - r44357 b44358 b44359 d44352
                    omega
                  have d44360 : (x 13 1 && x 13 14).toNat = 0 := by
                    have r44361 := hand2 (x 13 1) (x 13 14)
                    have b44362 := hb (x 13 14)
                    have b44363 := hb (x 13 1 && x 13 14)
                    clear * - r44361 b44362 b44363 d44356
                    omega
                  have d44364 : (x 14 13).toNat = 1 := by
                    have r44365 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b44366 := hb (x 12 2)
                    have b44367 := hb (x 14 13)
                    have b44368 := hb (x 13 1 && x 13 14)
                    clear * - r44365 b44366 b44367 b44368 d44360 d44318
                    omega
                  have d44369 : (x 14 1).toNat = 1 := by
                    have r44370 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
                    have b44371 := hb (x 14 1)
                    have b44372 := hb (x 14 13)
                    clear * - r44370 b44371 b44372 d44364
                    omega
                  have d44373 : (x 15 14).toNat = 0 := by
                    have r44374 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b44375 := hb (x 14 1)
                    have b44376 := hb (x 15 14)
                    clear * - r44374 b44375 b44376 d44369
                    omega
                  have d44377 : (x 15 1 && x 15 14).toNat = 0 := by
                    have r44378 := hand2 (x 15 1) (x 15 14)
                    have b44379 := hb (x 15 14)
                    have b44380 := hb (x 15 1 && x 15 14)
                    clear * - r44378 b44379 b44380 d44373
                    omega
                  have d44381 : (x 15 2).toNat = 0 := by
                    have r44382 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
                    have b44383 := hb (x 15 2)
                    have b44384 := hb (x 15 14)
                    clear * - r44382 b44383 b44384 d44373
                    omega
                  have d44385 : (x 15 2 && x 15 13).toNat = 0 := by
                    have r44386 := hand1 (x 15 2) (x 15 13)
                    have b44387 := hb (x 15 2)
                    have b44388 := hb (x 15 2 && x 15 13)
                    clear * - r44386 b44387 b44388 d44381
                    omega
                  have d44389 : (x 13 2).toNat = 0 := by
                    have r44390 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
                    have b44391 := hb (x 13 2)
                    have b44392 := hb (x 13 14)
                    clear * - r44390 b44391 b44392 d44356
                    omega
                  have d44393 : (x 11 2).toNat = 0 := by
                    have r44394 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
                    have b44395 := hb (x 11 2)
                    have b44396 := hb (x 11 14)
                    clear * - r44394 b44395 b44396 d44339
                    omega
                  have d44397 : (x 13 13).toNat = 1 := by
                    have r44398 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b44399 := hb (x 11 2)
                    have b44400 := hb (x 13 13)
                    have b44401 := hb (x 12 1 && x 12 14)
                    clear * - r44398 b44399 b44400 b44401 d44314 d44393
                    omega
                  have d44402 : (x 13 1).toNat = 1 := by
                    have r44403 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
                    have b44404 := hb (x 13 1)
                    have b44405 := hb (x 13 13)
                    clear * - r44403 b44404 b44405 d44397
                    omega
                  have d44406 : (x 14 14).toNat = 0 := by
                    have r44407 : (x 14 14).toNat + (x 13 1).toNat = 1 := by have q := hd14 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b44408 := hb (x 13 1)
                    have b44409 := hb (x 14 14)
                    clear * - r44407 b44408 b44409 d44402
                    omega
                  have d44410 : (x 14 1 && x 14 14).toNat = 0 := by
                    have r44411 := hand2 (x 14 1) (x 14 14)
                    have b44412 := hb (x 14 14)
                    have b44413 := hb (x 14 1 && x 14 14)
                    clear * - r44411 b44412 b44413 d44406
                    omega
                  have d44414 : (x 15 13).toNat = 1 := by
                    have r44415 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b44416 := hb (x 13 2)
                    have b44417 := hb (x 15 13)
                    have b44418 := hb (x 14 1 && x 14 14)
                    clear * - r44415 b44416 b44417 b44418 d44410 d44389
                    omega
                  have d44419 : (x 15 1).toNat = 1 := by
                    have r44420 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
                    have b44421 := hb (x 15 1)
                    have b44422 := hb (x 15 13)
                    clear * - r44420 b44421 b44422 d44414
                    omega
                  have d44423 : (x 16 14).toNat = 0 := by
                    have r44424 : (x 16 14).toNat + (x 15 1).toNat = 1 := by have q := hd14 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b44425 := hb (x 15 1)
                    have b44426 := hb (x 16 14)
                    clear * - r44424 b44425 b44426 d44419
                    omega
                  have d44427 : (x 16 1 && x 16 14).toNat = 0 := by
                    have r44428 := hand2 (x 16 1) (x 16 14)
                    have b44429 := hb (x 16 14)
                    have b44430 := hb (x 16 1 && x 16 14)
                    clear * - r44428 b44429 b44430 d44423
                    omega
                  have d44431 : (x 17 13).toNat = 1 := by
                    have r44432 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := by have q := hcov13 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b44433 := hb (x 15 2)
                    have b44434 := hb (x 17 13)
                    have b44435 := hb (x 16 1 && x 16 14)
                    clear * - r44432 b44433 b44434 b44435 d44427 d44381
                    omega
                  have d44436 : (x 17 1).toNat = 1 := by
                    have r44437 : (x 17 13).toNat ≤ (x 17 1).toNat := himp _ _ (hp13 17)
                    have b44438 := hb (x 17 1)
                    have b44439 := hb (x 17 13)
                    clear * - r44437 b44438 b44439 d44431
                    omega
                  have d44440 : (x 18 14).toNat = 0 := by
                    have r44441 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b44442 := hb (x 17 1)
                    have b44443 := hb (x 18 14)
                    clear * - r44441 b44442 b44443 d44436
                    omega
                  have d44444 : (x 18 1 && x 18 14).toNat = 0 := by
                    have r44445 := hand2 (x 18 1) (x 18 14)
                    have b44446 := hb (x 18 14)
                    have b44447 := hb (x 18 1 && x 18 14)
                    clear * - r44445 b44446 b44447 d44440
                    omega
                  have d44448 : (x 18 2).toNat = 0 := by
                    have r44449 : (x 18 2).toNat ≤ (x 18 14).toNat := himp _ _ (hp2 18)
                    have b44450 := hb (x 18 2)
                    have b44451 := hb (x 18 14)
                    clear * - r44449 b44450 b44451 d44440
                    omega
                  have d44452 : (x 14 3 && x 14 14).toNat = 0 := by
                    have r44453 := hand2 (x 14 3) (x 14 14)
                    have b44454 := hb (x 14 14)
                    have b44455 := hb (x 14 3 && x 14 14)
                    clear * - r44453 b44454 b44455 d44406
                    omega
                  have d44456 : (x 14 2).toNat = 0 := by
                    have r44457 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
                    have b44458 := hb (x 14 2)
                    have b44459 := hb (x 14 14)
                    clear * - r44457 b44458 b44459 d44406
                    omega
                  have d44460 : (x 16 13).toNat = 1 := by
                    have r44461 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b44462 := hb (x 14 2)
                    have b44463 := hb (x 16 13)
                    have b44464 := hb (x 15 1 && x 15 14)
                    clear * - r44461 b44462 b44463 b44464 d44377 d44456
                    omega
                  have d44465 : (x 16 1).toNat = 1 := by
                    have r44466 : (x 16 13).toNat ≤ (x 16 1).toNat := himp _ _ (hp13 16)
                    have b44467 := hb (x 16 1)
                    have b44468 := hb (x 16 13)
                    clear * - r44466 b44467 b44468 d44460
                    omega
                  have d44469 : (x 17 14).toNat = 0 := by
                    have r44470 : (x 17 14).toNat + (x 16 1).toNat = 1 := by have q := hd14 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b44471 := hb (x 16 1)
                    have b44472 := hb (x 17 14)
                    clear * - r44470 b44471 b44472 d44465
                    omega
                  have d44473 : (x 17 2).toNat = 0 := by
                    have r44474 : (x 17 2).toNat ≤ (x 17 14).toNat := himp _ _ (hp2 17)
                    have b44475 := hb (x 17 2)
                    have b44476 := hb (x 17 14)
                    clear * - r44474 b44475 b44476 d44469
                    omega
                  have d44477 : (x 19 13).toNat = 1 := by
                    have r44478 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b44479 := hb (x 17 2)
                    have b44480 := hb (x 19 13)
                    have b44481 := hb (x 18 1 && x 18 14)
                    clear * - r44478 b44479 b44480 b44481 d44444 d44473
                    omega
                  have d44482 : (x 20 12).toNat = 0 := by
                    have r44483 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e44484 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
                    have e44485 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
                    have b44486 := hb (x 17 3)
                    have b44487 := hb (x 18 2)
                    have b44488 := hb (x 19 13)
                    have b44489 := hb (x 20 12)
                    clear * - r44483 e44484 e44485 b44486 b44487 b44488 b44489 d44477 d44448
                    omega
                  have d44490 : (x 17 3).toNat = 0 := by
                    have r44491 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e44492 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
                    have e44493 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
                    have b44494 := hb (x 17 3)
                    have b44495 := hb (x 18 2)
                    have b44496 := hb (x 19 13)
                    have b44497 := hb (x 20 12)
                    clear * - r44491 e44492 e44493 b44494 b44495 b44496 b44497 d44482 d44477 d44448
                    omega
                  have d44498 : (x 17 11).toNat = 0 := by
                    have r44499 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
                    have b44500 := hb (x 17 3)
                    have b44501 := hb (x 17 11)
                    clear * - r44499 b44500 b44501 d44490
                    omega
                  have d44502 : (x 16 12).toNat = 0 := by
                    have r44503 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e44504 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                    have e44505 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                    have b44506 := hb (x 13 3)
                    have b44507 := hb (x 14 2)
                    have b44508 := hb (x 15 13)
                    have b44509 := hb (x 16 12)
                    clear * - r44503 e44504 e44505 b44506 b44507 b44508 b44509 d44414 d44456
                    omega
                  have d44510 : (x 16 1 && x 16 12).toNat = 0 := by
                    have r44511 := hand2 (x 16 1) (x 16 12)
                    have b44512 := hb (x 16 12)
                    have b44513 := hb (x 16 1 && x 16 12)
                    clear * - r44511 b44512 b44513 d44502
                    omega
                  have d44514 : (x 13 12).toNat = 0 := by
                    have r44515 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e44516 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
                    have e44517 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
                    have b44518 := hb (x 10 3)
                    have b44519 := hb (x 11 2)
                    have b44520 := hb (x 12 13)
                    have b44521 := hb (x 13 12)
                    clear * - r44515 e44516 e44517 b44518 b44519 b44520 b44521 d44347 d44393
                    omega
                  have d44522 : (x 13 4).toNat = 0 := by
                    have r44523 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
                    have b44524 := hb (x 13 4)
                    have b44525 := hb (x 13 12)
                    clear * - r44523 b44524 b44525 d44514
                    omega
                  have r44526 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b44527 := hb (x 13 4)
                  have b44528 := hb (x 17 11)
                  have b44529 := hb (x 16 1 && x 16 12)
                  have b44530 := hb (x 15 2 && x 15 13)
                  have b44531 := hb (x 14 3 && x 14 14)
                  linarith only [r44526, b44527, b44528, b44529, b44530, b44531, d44498, d44510, d44385, d44452, d44522]
              · have f44532 : (x (-1) 14).toNat = 1 := by rw [h43987]; rfl
                have d44533 : (x (-2) 1).toNat = 0 := by
                  have r44534 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b44535 := hb (x (-2) 1)
                  have b44536 := hb (x (-1) 14)
                  clear * - r44534 b44535 b44536 f44532
                  omega
                have d44537 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
                  have r44538 := hand1 (x (-2) 1) (x (-2) 14)
                  have b44539 := hb (x (-2) 1)
                  have b44540 := hb (x (-2) 1 && x (-2) 14)
                  clear * - r44538 b44539 b44540 d44533
                  omega
                have d44541 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
                  have r44542 := hand1 (x (-2) 1) (x (-2) 12)
                  have b44543 := hb (x (-2) 1)
                  have b44544 := hb (x (-2) 1 && x (-2) 12)
                  clear * - r44542 b44543 b44544 d44533
                  omega
                have d44545 : (x (-2) 1 && x (-2) 8).toNat = 0 := by
                  have r44546 := hand1 (x (-2) 1) (x (-2) 8)
                  have b44547 := hb (x (-2) 1)
                  have b44548 := hb (x (-2) 1 && x (-2) 8)
                  clear * - r44546 b44547 b44548 d44533
                  omega
                have d44549 : (x (-2) 13).toNat = 0 := by
                  have r44550 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
                  have b44551 := hb (x (-2) 1)
                  have b44552 := hb (x (-2) 13)
                  clear * - r44550 b44551 b44552 d44533
                  omega
                have d44553 : (x (-3) 2).toNat = 1 := by
                  have r44554 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b44555 := hb (x (-3) 2)
                  have b44556 := hb (x (-1) 13)
                  have b44557 := hb (x (-2) 1 && x (-2) 14)
                  clear * - r44554 b44555 b44556 b44557 g7 d44537
                  omega
                have d44558 : (x (-3) 14).toNat = 1 := by
                  have r44559 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
                  have b44560 := hb (x (-3) 2)
                  have b44561 := hb (x (-3) 14)
                  clear * - r44559 b44560 b44561 d44553
                  omega
                have d44562 : (x (-4) 1).toNat = 0 := by
                  have r44563 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b44564 := hb (x (-4) 1)
                  have b44565 := hb (x (-3) 14)
                  clear * - r44563 b44564 b44565 d44558
                  omega
                have d44566 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
                  have r44567 := hand1 (x (-4) 1) (x (-4) 14)
                  have b44568 := hb (x (-4) 1)
                  have b44569 := hb (x (-4) 1 && x (-4) 14)
                  clear * - r44567 b44568 b44569 d44562
                  omega
                have d44570 : (x (-4) 13).toNat = 0 := by
                  have r44571 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
                  have b44572 := hb (x (-4) 1)
                  have b44573 := hb (x (-4) 13)
                  clear * - r44571 b44572 b44573 d44562
                  omega
                have d44574 : (x (-4) 2 && x (-4) 13).toNat = 0 := by
                  have r44575 := hand2 (x (-4) 2) (x (-4) 13)
                  have b44576 := hb (x (-4) 13)
                  have b44577 := hb (x (-4) 2 && x (-4) 13)
                  clear * - r44575 b44576 b44577 d44570
                  omega
                have d44578 : (x (-4) 3).toNat = 0 := by
                  have r44579 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e44580 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                  have e44581 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                  have b44582 := hb (x (-4) 3)
                  have b44583 := hb (x (-3) 2)
                  have b44584 := hb (x (-2) 13)
                  have b44585 := hb (x (-1) 12)
                  clear * - r44579 e44580 e44581 b44582 b44583 b44584 b44585 f43986 d44549 d44553
                  omega
                have d44586 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
                  have r44587 := hand1 (x (-4) 3) (x (-4) 14)
                  have b44588 := hb (x (-4) 3)
                  have b44589 := hb (x (-4) 3 && x (-4) 14)
                  clear * - r44587 b44588 b44589 d44578
                  omega
                have d44590 : (x (-4) 3 && x (-4) 10).toNat = 0 := by
                  have r44591 := hand1 (x (-4) 3) (x (-4) 10)
                  have b44592 := hb (x (-4) 3)
                  have b44593 := hb (x (-4) 3 && x (-4) 10)
                  clear * - r44591 b44592 b44593 d44578
                  omega
                cases h44594 : x 2 3
                · have f44595 : (x 2 3).toNat = 0 := by rw [h44594]; rfl
                  cases h44596 : x 2 7
                  · have f44597 : (x 2 7).toNat = 0 := by rw [h44596]; rfl
                    cases h44598 : x (-2) 8
                    · have f44599 : (x (-2) 8).toNat = 0 := by rw [h44598]; rfl
                      cases h44600 : x (-2) 12
                      · have f44601 : (x (-2) 12).toNat = 0 := by rw [h44600]; rfl
                        cases h44602 : x (-3) 1
                        · have f44603 : (x (-3) 1).toNat = 0 := by rw [h44602]; rfl
                          have d44604 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
                            have r44605 := hand1 (x (-3) 1) (x (-3) 14)
                            have b44606 := hb (x (-3) 1)
                            have b44607 := hb (x (-3) 1 && x (-3) 14)
                            clear * - r44605 b44606 b44607 f44603
                            omega
                          have d44608 : (x (-3) 13).toNat = 0 := by
                            have r44609 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
                            have b44610 := hb (x (-3) 1)
                            have b44611 := hb (x (-3) 13)
                            clear * - r44609 b44610 b44611 f44603
                            omega
                          have d44612 : (x (-3) 2 && x (-3) 13).toNat = 0 := by
                            have r44613 := hand2 (x (-3) 2) (x (-3) 13)
                            have b44614 := hb (x (-3) 13)
                            have b44615 := hb (x (-3) 2 && x (-3) 13)
                            clear * - r44613 b44614 b44615 d44608
                            omega
                          have d44616 : (x (-4) 2).toNat = 1 := by
                            have r44617 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have b44618 := hb (x (-4) 2)
                            have b44619 := hb (x (-2) 13)
                            have b44620 := hb (x (-3) 1 && x (-3) 14)
                            clear * - r44617 b44618 b44619 b44620 d44549 d44604
                            omega
                          have d44621 : (x (-4) 14).toNat = 1 := by
                            have r44622 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
                            have b44623 := hb (x (-4) 2)
                            have b44624 := hb (x (-4) 14)
                            clear * - r44622 b44623 b44624 d44616
                            omega
                          have d44625 : (x (-5) 1).toNat = 0 := by
                            have r44626 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have b44627 := hb (x (-5) 1)
                            have b44628 := hb (x (-4) 14)
                            clear * - r44626 b44627 b44628 d44621
                            omega
                          have d44629 : (x (-5) 13).toNat = 0 := by
                            have r44630 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
                            have b44631 := hb (x (-5) 1)
                            have b44632 := hb (x (-5) 13)
                            clear * - r44630 b44631 b44632 d44625
                            omega
                          have d44633 : (x (-5) 2).toNat = 1 := by
                            have r44634 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have b44635 := hb (x (-5) 2)
                            have b44636 := hb (x (-3) 13)
                            have b44637 := hb (x (-4) 1 && x (-4) 14)
                            clear * - r44634 b44635 b44636 b44637 d44608 d44566
                            omega
                          have d44638 : (x (-5) 14).toNat = 1 := by
                            have r44639 : (x (-5) 2).toNat ≤ (x (-5) 14).toNat := himp _ _ (hp2 (-5))
                            have b44640 := hb (x (-5) 2)
                            have b44641 := hb (x (-5) 14)
                            clear * - r44639 b44640 b44641 d44633
                            omega
                          have d44642 : (x (-6) 1).toNat = 0 := by
                            have r44643 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have b44644 := hb (x (-6) 1)
                            have b44645 := hb (x (-5) 14)
                            clear * - r44643 b44644 b44645 d44638
                            omega
                          have d44646 : (x (-6) 1 && x (-6) 14).toNat = 0 := by
                            have r44647 := hand1 (x (-6) 1) (x (-6) 14)
                            have b44648 := hb (x (-6) 1)
                            have b44649 := hb (x (-6) 1 && x (-6) 14)
                            clear * - r44647 b44648 b44649 d44642
                            omega
                          have d44650 : (x (-6) 13).toNat = 0 := by
                            have r44651 : (x (-6) 13).toNat ≤ (x (-6) 1).toNat := himp _ _ (hp13 (-6))
                            have b44652 := hb (x (-6) 1)
                            have b44653 := hb (x (-6) 13)
                            clear * - r44651 b44652 b44653 d44642
                            omega
                          have d44654 : (x (-7) 2).toNat = 1 := by
                            have r44655 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have b44656 := hb (x (-7) 2)
                            have b44657 := hb (x (-5) 13)
                            have b44658 := hb (x (-6) 1 && x (-6) 14)
                            clear * - r44655 b44656 b44657 b44658 d44629 d44646
                            omega
                          have d44659 : (x (-5) 12).toNat = 0 := by
                            have r44660 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e44661 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                            have e44662 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                            have b44663 := hb (x (-8) 3)
                            have b44664 := hb (x (-7) 2)
                            have b44665 := hb (x (-6) 13)
                            have b44666 := hb (x (-5) 12)
                            clear * - r44660 e44661 e44662 b44663 b44664 b44665 b44666 d44650 d44654
                            omega
                          have d44667 : (x (-5) 4).toNat = 0 := by
                            have r44668 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
                            have b44669 := hb (x (-5) 4)
                            have b44670 := hb (x (-5) 12)
                            clear * - r44668 b44669 b44670 d44659
                            omega
                          have r44671 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b44672 := hb (x (-5) 4)
                          have b44673 := hb (x (-1) 11)
                          have b44674 := hb (x (-2) 1 && x (-2) 12)
                          have b44675 := hb (x (-3) 2 && x (-3) 13)
                          have b44676 := hb (x (-4) 3 && x (-4) 14)
                          linarith only [r44671, b44672, b44673, b44674, b44675, b44676, d43021, d44541, d44612, d44586, d44667]
                        · have f44677 : (x (-3) 1).toNat = 1 := by rw [h44602]; rfl
                          have r44678 : (x (-3) 1).toNat + (x (-4) 2).toNat + (x (-5) 3).toNat + (x (-6) 4).toNat + (x (-7) 5).toNat + (x (-8) 6).toNat + (x (-9) 7).toNat + (x (-10) 8).toNat + (x (-11) 9).toNat + (x (-12) 10).toNat + (x (-13) 11).toNat + (x (-14) 12).toNat + (x (-15) 13).toNat + (x (-16) 14).toNat = 3 := by have q := hcount (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r44679 : (x (-1) 1).toNat + (x (-2) 2).toNat + (x (-3) 3).toNat + (x (-4) 4).toNat + (x (-5) 5).toNat + (x (-6) 6).toNat + (x (-7) 7).toNat + (x (-8) 8).toNat + (x (-9) 9).toNat + (x (-10) 10).toNat + (x (-11) 11).toNat + (x (-12) 12).toNat + (x (-13) 13).toNat + (x (-14) 14).toNat = 3 := by have q := hcount 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r44680 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r44681 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r44682 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e44683 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
                          have e44684 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
                          have e44685 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
                          have e44686 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
                          have e44687 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
                          have e44688 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
                          have r44689 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e44690 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
                          have e44691 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
                          have e44692 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
                          have e44693 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
                          have e44694 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
                          have e44695 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
                          have r44696 : (x (-12) 12).toNat + (x (-13) 1 && x (-13) 13).toNat + (x (-14) 2 && x (-14) 14).toNat + (x (-15) 3).toNat = 1 := by have q := hd12 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e44697 : (x (-13) 1 && x (-13) 13).toNat = (x (-13) 13).toNat := handr _ _ (fun h => hp13 (-13) (h))
                          have e44698 : (x (-14) 2 && x (-14) 14).toNat = (x (-14) 2).toNat := handl _ _ (fun h => hp2 (-14) (h))
                          have r44699 : (x (-11) 12).toNat + (x (-12) 1 && x (-12) 13).toNat + (x (-13) 2 && x (-13) 14).toNat + (x (-14) 3).toNat = 1 := by have q := hd12 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e44700 : (x (-12) 1 && x (-12) 13).toNat = (x (-12) 13).toNat := handr _ _ (fun h => hp13 (-12) (h))
                          have e44701 : (x (-13) 2 && x (-13) 14).toNat = (x (-13) 2).toNat := handl _ _ (fun h => hp2 (-13) (h))
                          have r44702 : (x (-14) 14).toNat + (x (-15) 1).toNat = 1 := by have q := hd14 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r44703 : (x (-13) 14).toNat + (x (-14) 1).toNat = 1 := by have q := hd14 (-13); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r44704 : 1 ≤ (x (-2) 2).toNat + (x (-3) 1 && x (-3) 3).toNat + (x (-4) 2 && x (-4) 4).toNat + (x (-5) 3 && x (-5) 5).toNat + (x (-6) 4 && x (-6) 6).toNat + (x (-7) 5 && x (-7) 7).toNat + (x (-8) 6 && x (-8) 8).toNat + (x (-9) 7 && x (-9) 9).toNat + (x (-10) 8 && x (-10) 10).toNat + (x (-11) 9 && x (-11) 11).toNat + (x (-12) 10 && x (-12) 12).toNat + (x (-13) 11 && x (-13) 13).toNat + (x (-14) 12 && x (-14) 14).toNat + (x (-15) 13).toNat := by have q := hcov2 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r44705 : 1 ≤ (x (-7) 9).toNat + (x (-8) 1 && x (-8) 10).toNat + (x (-9) 2 && x (-9) 11).toNat + (x (-10) 3 && x (-10) 12).toNat + (x (-11) 4 && x (-11) 13).toNat + (x (-12) 5 && x (-12) 14).toNat + (x (-13) 6).toNat := by have q := hcov9 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r44706 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r44707 : 1 ≤ (x (-14) 13).toNat + (x (-15) 1 && x (-15) 14).toNat + (x (-16) 2).toNat := by have q := hcov13 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r44708 : 1 ≤ (x (-11) 13).toNat + (x (-12) 1 && x (-12) 14).toNat + (x (-13) 2).toNat := by have q := hcov13 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r44709 : (x (-16) 2).toNat ≤ (x (-16) 14).toNat := himp _ _ (hp2 (-16))
                          have r44710 : (x (-14) 13).toNat ≤ (x (-14) 1).toNat := himp _ _ (hp13 (-14))
                          have r44711 := hand1 (x (-8) 6) (x (-8) 8)
                          have r44712 := hand1 (x (-9) 7) (x (-9) 9)
                          have r44713 := hand1 (x (-10) 8) (x (-10) 10)
                          have r44714 := hand1 (x (-11) 9) (x (-11) 11)
                          have r44715 := hand1 (x (-12) 10) (x (-12) 12)
                          have r44716 := hand1 (x (-13) 11) (x (-13) 13)
                          have r44717 := hand1 (x (-14) 12) (x (-14) 14)
                          have r44718 := hand2 (x (-8) 1) (x (-8) 10)
                          have r44719 := hand2 (x (-9) 2) (x (-9) 11)
                          have r44720 := hand2 (x (-10) 3) (x (-10) 12)
                          have r44721 := hand1 (x (-11) 4) (x (-11) 13)
                          have r44722 := hand1 (x (-12) 5) (x (-12) 14)
                          have r44723 := hand1 (x (-4) 2) (x (-4) 12)
                          have r44724 := hand1 (x (-5) 3) (x (-5) 13)
                          have r44725 := hand1 (x (-6) 4) (x (-6) 14)
                          have r44726 := hand1 (x (-15) 1) (x (-15) 14)
                          have r44727 := hand2 (x (-12) 1) (x (-12) 14)
                          linarith only [r44678, r44679, r44680, r44681, r44682, e44683, e44684, e44685, e44686, e44687, e44688, r44689, e44690, e44691, e44692, e44693, e44694, e44695, r44696, e44697, e44698, r44699, e44700, e44701, r44702, r44703, r44704, r44705, r44706, r44707, r44708, r44709, r44710, r44711, r44712, r44713, r44714, r44715, r44716, r44717, r44718, r44719, r44720, r44721, r44722, r44723, r44724, r44725, r44726, r44727, d43961, d43852, d43945, d43716, d43929, d43832, d43573, d43913, d43812, f44677, g0, d43897, d43796, g3, d43049, d43780, g5, d42952, d43037, d43013, g8, f42947, g11, g26, d43597, d43736, d43868, d43977, g46]
                      · have f44824 : (x (-2) 12).toNat = 1 := by rw [h44600]; rfl
                        have d44825 : (x (-3) 13).toNat = 0 := by
                          have r44826 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e44827 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                          have e44828 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                          have b44829 := hb (x (-5) 3)
                          have b44830 := hb (x (-4) 2)
                          have b44831 := hb (x (-3) 13)
                          have b44832 := hb (x (-2) 12)
                          clear * - r44826 e44827 e44828 b44829 b44830 b44831 b44832 f44824
                          omega
                        have d44833 : (x (-5) 2).toNat = 1 := by
                          have r44834 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b44835 := hb (x (-5) 2)
                          have b44836 := hb (x (-3) 13)
                          have b44837 := hb (x (-4) 1 && x (-4) 14)
                          clear * - r44834 b44835 b44836 b44837 d44825 d44566
                          omega
                        have d44838 : (x (-5) 14).toNat = 1 := by
                          have r44839 : (x (-5) 2).toNat ≤ (x (-5) 14).toNat := himp _ _ (hp2 (-5))
                          have b44840 := hb (x (-5) 2)
                          have b44841 := hb (x (-5) 14)
                          clear * - r44839 b44840 b44841 d44833
                          omega
                        have d44842 : (x (-6) 1).toNat = 0 := by
                          have r44843 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b44844 := hb (x (-6) 1)
                          have b44845 := hb (x (-5) 14)
                          clear * - r44843 b44844 b44845 d44838
                          omega
                        have d44846 : (x (-6) 13).toNat = 0 := by
                          have r44847 : (x (-6) 13).toNat ≤ (x (-6) 1).toNat := himp _ _ (hp13 (-6))
                          have b44848 := hb (x (-6) 1)
                          have b44849 := hb (x (-6) 13)
                          clear * - r44847 b44848 b44849 d44842
                          omega
                        have d44850 : (x (-4) 2).toNat = 0 := by
                          have r44851 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e44852 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                          have e44853 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                          have b44854 := hb (x (-5) 3)
                          have b44855 := hb (x (-4) 2)
                          have b44856 := hb (x (-3) 13)
                          have b44857 := hb (x (-2) 12)
                          clear * - r44851 e44852 e44853 b44854 b44855 b44856 b44857 f44824 d44825
                          omega
                        have d44858 : (x (-4) 2 && x (-4) 12).toNat = 0 := by
                          have r44859 := hand1 (x (-4) 2) (x (-4) 12)
                          have b44860 := hb (x (-4) 2)
                          have b44861 := hb (x (-4) 2 && x (-4) 12)
                          clear * - r44859 b44860 b44861 d44850
                          omega
                        have d44862 : (x (-5) 3).toNat = 0 := by
                          have r44863 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e44864 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                          have e44865 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                          have b44866 := hb (x (-5) 3)
                          have b44867 := hb (x (-4) 2)
                          have b44868 := hb (x (-3) 13)
                          have b44869 := hb (x (-2) 12)
                          clear * - r44863 e44864 e44865 b44866 b44867 b44868 b44869 f44824 d44825 d44850
                          omega
                        have d44870 : (x (-5) 3 && x (-5) 14).toNat = 0 := by
                          have r44871 := hand1 (x (-5) 3) (x (-5) 14)
                          have b44872 := hb (x (-5) 3)
                          have b44873 := hb (x (-5) 3 && x (-5) 14)
                          clear * - r44871 b44872 b44873 d44862
                          omega
                        have d44874 : (x (-5) 3 && x (-5) 13).toNat = 0 := by
                          have r44875 := hand1 (x (-5) 3) (x (-5) 13)
                          have b44876 := hb (x (-5) 3)
                          have b44877 := hb (x (-5) 3 && x (-5) 13)
                          clear * - r44875 b44876 b44877 d44862
                          omega
                        have d44878 : (x (-3) 12).toNat = 0 := by
                          have r44879 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e44880 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                          have e44881 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                          have b44882 := hb (x (-6) 3)
                          have b44883 := hb (x (-5) 2)
                          have b44884 := hb (x (-4) 13)
                          have b44885 := hb (x (-3) 12)
                          clear * - r44879 e44880 e44881 b44882 b44883 b44884 b44885 d44570 d44833
                          omega
                        have d44886 : (x (-3) 1 && x (-3) 12).toNat = 0 := by
                          have r44887 := hand2 (x (-3) 1) (x (-3) 12)
                          have b44888 := hb (x (-3) 12)
                          have b44889 := hb (x (-3) 1 && x (-3) 12)
                          clear * - r44887 b44888 b44889 d44878
                          omega
                        have d44890 : (x (-6) 4).toNat = 1 := by
                          have r44891 : 1 ≤ (x (-2) 11).toNat + (x (-3) 1 && x (-3) 12).toNat + (x (-4) 2 && x (-4) 13).toNat + (x (-5) 3 && x (-5) 14).toNat + (x (-6) 4).toNat := by have q := hcov11 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b44892 := hb (x (-6) 4)
                          have b44893 := hb (x (-2) 11)
                          have b44894 := hb (x (-3) 1 && x (-3) 12)
                          have b44895 := hb (x (-4) 2 && x (-4) 13)
                          have b44896 := hb (x (-5) 3 && x (-5) 14)
                          clear * - r44891 b44892 b44893 b44894 b44895 b44896 d43057 d44886 d44574 d44870
                          omega
                        have d44897 : (x (-6) 12).toNat = 1 := by
                          have r44898 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
                          have b44899 := hb (x (-6) 4)
                          have b44900 := hb (x (-6) 12)
                          clear * - r44898 b44899 b44900 d44890
                          omega
                        have d44901 : (x (-7) 13).toNat = 0 := by
                          have r44902 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e44903 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
                          have e44904 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
                          have b44905 := hb (x (-9) 3)
                          have b44906 := hb (x (-8) 2)
                          have b44907 := hb (x (-7) 13)
                          have b44908 := hb (x (-6) 12)
                          clear * - r44902 e44903 e44904 b44905 b44906 b44907 b44908 d44897
                          omega
                        have d44909 : (x (-7) 5).toNat = 0 := by
                          have r44910 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
                          have b44911 := hb (x (-7) 5)
                          have b44912 := hb (x (-7) 13)
                          clear * - r44910 b44911 b44912 d44901
                          omega
                        have d44913 : (x (-8) 2).toNat = 0 := by
                          have r44914 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e44915 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
                          have e44916 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
                          have b44917 := hb (x (-9) 3)
                          have b44918 := hb (x (-8) 2)
                          have b44919 := hb (x (-7) 13)
                          have b44920 := hb (x (-6) 12)
                          clear * - r44914 e44915 e44916 b44917 b44918 b44919 b44920 d44897 d44901
                          omega
                        have d44921 : (x (-7) 1 && x (-7) 14).toNat = 1 := by
                          have r44922 : 1 ≤ (x (-6) 13).toNat + (x (-7) 1 && x (-7) 14).toNat + (x (-8) 2).toNat := by have q := hcov13 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b44923 := hb (x (-8) 2)
                          have b44924 := hb (x (-6) 13)
                          have b44925 := hb (x (-7) 1 && x (-7) 14)
                          clear * - r44922 b44923 b44924 b44925 d44846 d44913
                          omega
                        have d44926 : (x (-7) 1).toNat = 1 := by
                          have r44927 := hand1 (x (-7) 1) (x (-7) 14)
                          have b44928 := hb (x (-7) 1)
                          have b44929 := hb (x (-7) 1 && x (-7) 14)
                          clear * - r44927 b44928 b44929 d44921
                          omega
                        have d44930 : (x (-6) 14).toNat = 0 := by
                          have r44931 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b44932 := hb (x (-7) 1)
                          have b44933 := hb (x (-6) 14)
                          clear * - r44931 b44932 b44933 d44926
                          omega
                        have d44934 : (x (-6) 4 && x (-6) 14).toNat = 0 := by
                          have r44935 := hand2 (x (-6) 4) (x (-6) 14)
                          have b44936 := hb (x (-6) 14)
                          have b44937 := hb (x (-6) 4 && x (-6) 14)
                          clear * - r44935 b44936 b44937 d44930
                          omega
                        have r44938 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b44939 := hb (x (-7) 5)
                        have b44940 := hb (x (-2) 10)
                        have b44941 := hb (x (-3) 1 && x (-3) 11)
                        have b44942 := hb (x (-4) 2 && x (-4) 12)
                        have b44943 := hb (x (-5) 3 && x (-5) 13)
                        have b44944 := hb (x (-6) 4 && x (-6) 14)
                        linarith only [r44938, b44939, b44940, b44941, b44942, b44943, b44944, g5, g46, d44858, d44874, d44934, d44909]
                    · have f44945 : (x (-2) 8).toNat = 1 := by rw [h44598]; rfl
                      have d44946 : (x (-3) 9).toNat = 0 := by
                        have r44947 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e44948 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                        have e44949 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                        have e44950 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                        have e44951 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                        have e44952 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                        have e44953 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                        have b44954 := hb (x (-9) 7)
                        have b44955 := hb (x (-8) 6)
                        have b44956 := hb (x (-7) 5)
                        have b44957 := hb (x (-6) 4)
                        have b44958 := hb (x (-5) 11)
                        have b44959 := hb (x (-4) 10)
                        have b44960 := hb (x (-3) 9)
                        have b44961 := hb (x (-2) 8)
                        clear * - r44947 e44948 e44949 e44950 e44951 e44952 e44953 b44954 b44955 b44956 b44957 b44958 b44959 b44960 b44961 f44945
                        omega
                      have d44962 : (x (-3) 2 && x (-3) 9).toNat = 0 := by
                        have r44963 := hand2 (x (-3) 2) (x (-3) 9)
                        have b44964 := hb (x (-3) 9)
                        have b44965 := hb (x (-3) 2 && x (-3) 9)
                        clear * - r44963 b44964 b44965 d44946
                        omega
                      have d44966 : (x (-4) 10).toNat = 0 := by
                        have r44967 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e44968 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                        have e44969 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                        have e44970 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                        have e44971 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                        have e44972 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                        have e44973 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                        have b44974 := hb (x (-9) 7)
                        have b44975 := hb (x (-8) 6)
                        have b44976 := hb (x (-7) 5)
                        have b44977 := hb (x (-6) 4)
                        have b44978 := hb (x (-5) 11)
                        have b44979 := hb (x (-4) 10)
                        have b44980 := hb (x (-3) 9)
                        have b44981 := hb (x (-2) 8)
                        clear * - r44967 e44968 e44969 e44970 e44971 e44972 e44973 b44974 b44975 b44976 b44977 b44978 b44979 b44980 b44981 f44945 d44946
                        omega
                      have d44982 : (x (-5) 11).toNat = 0 := by
                        have r44983 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e44984 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                        have e44985 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                        have e44986 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                        have e44987 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                        have e44988 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                        have e44989 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                        have b44990 := hb (x (-9) 7)
                        have b44991 := hb (x (-8) 6)
                        have b44992 := hb (x (-7) 5)
                        have b44993 := hb (x (-6) 4)
                        have b44994 := hb (x (-5) 11)
                        have b44995 := hb (x (-4) 10)
                        have b44996 := hb (x (-3) 9)
                        have b44997 := hb (x (-2) 8)
                        clear * - r44983 e44984 e44985 e44986 e44987 e44988 e44989 b44990 b44991 b44992 b44993 b44994 b44995 b44996 b44997 f44945 d44946 d44966
                        omega
                      have d44998 : (x (-5) 4 && x (-5) 11).toNat = 0 := by
                        have r44999 := hand2 (x (-5) 4) (x (-5) 11)
                        have b45000 := hb (x (-5) 11)
                        have b45001 := hb (x (-5) 4 && x (-5) 11)
                        clear * - r44999 b45000 b45001 d44982
                        omega
                      have d45002 : (x (-6) 4).toNat = 0 := by
                        have r45003 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e45004 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                        have e45005 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                        have e45006 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                        have e45007 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                        have e45008 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                        have e45009 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                        have b45010 := hb (x (-9) 7)
                        have b45011 := hb (x (-8) 6)
                        have b45012 := hb (x (-7) 5)
                        have b45013 := hb (x (-6) 4)
                        have b45014 := hb (x (-5) 11)
                        have b45015 := hb (x (-4) 10)
                        have b45016 := hb (x (-3) 9)
                        have b45017 := hb (x (-2) 8)
                        clear * - r45003 e45004 e45005 e45006 e45007 e45008 e45009 b45010 b45011 b45012 b45013 b45014 b45015 b45016 b45017 f44945 d44946 d44966 d44982
                        omega
                      have d45018 : (x (-6) 4 && x (-6) 14).toNat = 0 := by
                        have r45019 := hand1 (x (-6) 4) (x (-6) 14)
                        have b45020 := hb (x (-6) 4)
                        have b45021 := hb (x (-6) 4 && x (-6) 14)
                        clear * - r45019 b45020 b45021 d45002
                        omega
                      have d45022 : (x (-6) 4 && x (-6) 8).toNat = 0 := by
                        have r45023 := hand1 (x (-6) 4) (x (-6) 8)
                        have b45024 := hb (x (-6) 4)
                        have b45025 := hb (x (-6) 4 && x (-6) 8)
                        clear * - r45023 b45024 b45025 d45002
                        omega
                      have d45026 : (x (-7) 5).toNat = 0 := by
                        have r45027 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e45028 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                        have e45029 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                        have e45030 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                        have e45031 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                        have e45032 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                        have e45033 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                        have b45034 := hb (x (-9) 7)
                        have b45035 := hb (x (-8) 6)
                        have b45036 := hb (x (-7) 5)
                        have b45037 := hb (x (-6) 4)
                        have b45038 := hb (x (-5) 11)
                        have b45039 := hb (x (-4) 10)
                        have b45040 := hb (x (-3) 9)
                        have b45041 := hb (x (-2) 8)
                        clear * - r45027 e45028 e45029 e45030 e45031 e45032 e45033 b45034 b45035 b45036 b45037 b45038 b45039 b45040 b45041 f44945 d44946 d44966 d44982 d45002
                        omega
                      have d45042 : (x (-7) 5 && x (-7) 9).toNat = 0 := by
                        have r45043 := hand1 (x (-7) 5) (x (-7) 9)
                        have b45044 := hb (x (-7) 5)
                        have b45045 := hb (x (-7) 5 && x (-7) 9)
                        clear * - r45043 b45044 b45045 d45026
                        omega
                      have d45046 : (x (-8) 6).toNat = 0 := by
                        have r45047 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e45048 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                        have e45049 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                        have e45050 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                        have e45051 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                        have e45052 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                        have e45053 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                        have b45054 := hb (x (-9) 7)
                        have b45055 := hb (x (-8) 6)
                        have b45056 := hb (x (-7) 5)
                        have b45057 := hb (x (-6) 4)
                        have b45058 := hb (x (-5) 11)
                        have b45059 := hb (x (-4) 10)
                        have b45060 := hb (x (-3) 9)
                        have b45061 := hb (x (-2) 8)
                        clear * - r45047 e45048 e45049 e45050 e45051 e45052 e45053 b45054 b45055 b45056 b45057 b45058 b45059 b45060 b45061 f44945 d44946 d44966 d44982 d45002 d45026
                        omega
                      have d45062 : (x (-8) 6 && x (-8) 10).toNat = 0 := by
                        have r45063 := hand1 (x (-8) 6) (x (-8) 10)
                        have b45064 := hb (x (-8) 6)
                        have b45065 := hb (x (-8) 6 && x (-8) 10)
                        clear * - r45063 b45064 b45065 d45046
                        omega
                      have d45066 : (x (-9) 7).toNat = 0 := by
                        have r45067 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e45068 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                        have e45069 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                        have e45070 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                        have e45071 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                        have e45072 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                        have e45073 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                        have b45074 := hb (x (-9) 7)
                        have b45075 := hb (x (-8) 6)
                        have b45076 := hb (x (-7) 5)
                        have b45077 := hb (x (-6) 4)
                        have b45078 := hb (x (-5) 11)
                        have b45079 := hb (x (-4) 10)
                        have b45080 := hb (x (-3) 9)
                        have b45081 := hb (x (-2) 8)
                        clear * - r45067 e45068 e45069 e45070 e45071 e45072 e45073 b45074 b45075 b45076 b45077 b45078 b45079 b45080 b45081 f44945 d44946 d44966 d44982 d45002 d45026 d45046
                        omega
                      have d45082 : (x (-9) 7 && x (-9) 11).toNat = 0 := by
                        have r45083 := hand1 (x (-9) 7) (x (-9) 11)
                        have b45084 := hb (x (-9) 7)
                        have b45085 := hb (x (-9) 7 && x (-9) 11)
                        clear * - r45083 b45084 b45085 d45066
                        omega
                      have r45086 : (x (-2) 1).toNat + (x (-3) 2).toNat + (x (-4) 3).toNat + (x (-5) 4).toNat + (x (-6) 5).toNat + (x (-7) 6).toNat + (x (-8) 7).toNat + (x (-9) 8).toNat + (x (-10) 9).toNat + (x (-11) 10).toNat + (x (-12) 11).toNat + (x (-13) 12).toNat + (x (-14) 13).toNat + (x (-15) 14).toNat = 3 := by have q := hcount (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r45087 : (x (-10) 8).toNat + (x (-11) 1 && x (-11) 9).toNat + (x (-12) 2 && x (-12) 10).toNat + (x (-13) 3 && x (-13) 11).toNat + (x (-14) 4 && x (-14) 12).toNat + (x (-15) 5 && x (-15) 13).toNat + (x (-16) 6 && x (-16) 14).toNat + (x (-17) 7).toNat = 1 := by have q := hd8 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e45088 : (x (-11) 1 && x (-11) 9).toNat = (x (-11) 9).toNat := handr _ _ (fun h => hp9 (-11) (h))
                      have e45089 : (x (-12) 2 && x (-12) 10).toNat = (x (-12) 10).toNat := handr _ _ (fun h => hp10 (-12) (h))
                      have e45090 : (x (-13) 3 && x (-13) 11).toNat = (x (-13) 11).toNat := handr _ _ (fun h => hp11 (-13) (h))
                      have e45091 : (x (-14) 4 && x (-14) 12).toNat = (x (-14) 4).toNat := handl _ _ (fun h => hp4 (-14) (h))
                      have e45092 : (x (-15) 5 && x (-15) 13).toNat = (x (-15) 5).toNat := handl _ _ (fun h => hp5 (-15) (h))
                      have e45093 : (x (-16) 6 && x (-16) 14).toNat = (x (-16) 6).toNat := handl _ _ (fun h => hp6 (-16) (h))
                      have r45094 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e45095 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                      have e45096 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                      have r45097 : 1 ≤ (x (-2) 4).toNat + (x (-3) 1 && x (-3) 5).toNat + (x (-4) 2 && x (-4) 6).toNat + (x (-5) 3 && x (-5) 7).toNat + (x (-6) 4 && x (-6) 8).toNat + (x (-7) 5 && x (-7) 9).toNat + (x (-8) 6 && x (-8) 10).toNat + (x (-9) 7 && x (-9) 11).toNat + (x (-10) 8 && x (-10) 12).toNat + (x (-11) 9 && x (-11) 13).toNat + (x (-12) 10 && x (-12) 14).toNat + (x (-13) 11).toNat := by have q := hcov4 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e45098 : (x (-3) 1 && x (-3) 5).toNat = (x (-3) 5).toNat := handr _ _ (fun h => hp13 (-3) (hp5 (-3) (h)))
                      have e45099 : (x (-12) 10 && x (-12) 14).toNat = (x (-12) 10).toNat := handl _ _ (fun h => hp2 (-12) (hp10 (-12) (h)))
                      have r45100 : 1 ≤ (x (-1) 7).toNat + (x (-2) 1 && x (-2) 8).toNat + (x (-3) 2 && x (-3) 9).toNat + (x (-4) 3 && x (-4) 10).toNat + (x (-5) 4 && x (-5) 11).toNat + (x (-6) 5 && x (-6) 12).toNat + (x (-7) 6 && x (-7) 13).toNat + (x (-8) 7 && x (-8) 14).toNat + (x (-9) 8).toNat := by have q := hcov7 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r45101 : 1 ≤ (x (-10) 9).toNat + (x (-11) 1 && x (-11) 10).toNat + (x (-12) 2 && x (-12) 11).toNat + (x (-13) 3 && x (-13) 12).toNat + (x (-14) 4 && x (-14) 13).toNat + (x (-15) 5 && x (-15) 14).toNat + (x (-16) 6).toNat := by have q := hcov9 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r45102 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r45103 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r45104 := hand1 (x (-10) 8) (x (-10) 12)
                      have r45105 := hand1 (x (-11) 9) (x (-11) 13)
                      have r45106 := hand1 (x (-6) 5) (x (-6) 12)
                      have r45107 := hand1 (x (-7) 6) (x (-7) 13)
                      have r45108 := hand1 (x (-8) 7) (x (-8) 14)
                      have r45109 := hand2 (x (-11) 1) (x (-11) 10)
                      have r45110 := hand2 (x (-12) 2) (x (-12) 11)
                      have r45111 := hand2 (x (-13) 3) (x (-13) 12)
                      have r45112 := hand1 (x (-14) 4) (x (-14) 13)
                      have r45113 := hand1 (x (-15) 5) (x (-15) 14)
                      have r45114 := hand1 (x (-4) 2) (x (-4) 12)
                      have r45115 := hand1 (x (-5) 3) (x (-5) 13)
                      have r45116 := hand2 (x (-3) 2) (x (-3) 13)
                      linarith only [r45086, r45087, e45088, e45089, e45090, e45091, e45092, e45093, r45094, e45095, e45096, r45097, e45098, e45099, r45100, r45101, r45102, r45103, r45104, r45105, r45106, r45107, r45108, r45109, r45110, r45111, r45112, r45113, r45114, r45115, r45116, d45026, d44578, d44553, d43796, d44533, d43780, g5, d43340, d43021, d43828, d43848, d45022, d45042, d45062, d45082, d44545, d44962, d44590, d44998, g46, d45018, d44541, d44586]
                  · have f45176 : (x 2 7).toNat = 1 := by rw [h44596]; rfl
                    have d45177 : (x 9 8).toNat = 0 := by
                      have r45178 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e45179 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                      have e45180 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                      have e45181 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                      have e45182 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                      have e45183 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                      have e45184 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                      have b45185 := hb (x 2 7)
                      have b45186 := hb (x 3 6)
                      have b45187 := hb (x 4 5)
                      have b45188 := hb (x 5 4)
                      have b45189 := hb (x 6 11)
                      have b45190 := hb (x 7 10)
                      have b45191 := hb (x 8 9)
                      have b45192 := hb (x 9 8)
                      clear * - r45178 e45179 e45180 e45181 e45182 e45183 e45184 b45185 b45186 b45187 b45188 b45189 b45190 b45191 b45192 f45176
                      omega
                    have d45193 : (x 9 4 && x 9 8).toNat = 0 := by
                      have r45194 := hand2 (x 9 4) (x 9 8)
                      have b45195 := hb (x 9 8)
                      have b45196 := hb (x 9 4 && x 9 8)
                      clear * - r45194 b45195 b45196 d45177
                      omega
                    have d45197 : (x 8 9).toNat = 0 := by
                      have r45198 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e45199 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                      have e45200 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                      have e45201 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                      have e45202 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                      have e45203 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                      have e45204 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                      have b45205 := hb (x 2 7)
                      have b45206 := hb (x 3 6)
                      have b45207 := hb (x 4 5)
                      have b45208 := hb (x 5 4)
                      have b45209 := hb (x 6 11)
                      have b45210 := hb (x 7 10)
                      have b45211 := hb (x 8 9)
                      have b45212 := hb (x 9 8)
                      clear * - r45198 e45199 e45200 e45201 e45202 e45203 e45204 b45205 b45206 b45207 b45208 b45209 b45210 b45211 b45212 d45177 f45176
                      omega
                    have d45213 : (x 8 5 && x 8 9).toNat = 0 := by
                      have r45214 := hand2 (x 8 5) (x 8 9)
                      have b45215 := hb (x 8 9)
                      have b45216 := hb (x 8 5 && x 8 9)
                      clear * - r45214 b45215 b45216 d45197
                      omega
                    have d45217 : (x 7 10).toNat = 0 := by
                      have r45218 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e45219 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                      have e45220 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                      have e45221 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                      have e45222 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                      have e45223 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                      have e45224 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                      have b45225 := hb (x 2 7)
                      have b45226 := hb (x 3 6)
                      have b45227 := hb (x 4 5)
                      have b45228 := hb (x 5 4)
                      have b45229 := hb (x 6 11)
                      have b45230 := hb (x 7 10)
                      have b45231 := hb (x 8 9)
                      have b45232 := hb (x 9 8)
                      clear * - r45218 e45219 e45220 e45221 e45222 e45223 e45224 b45225 b45226 b45227 b45228 b45229 b45230 b45231 b45232 d45177 d45197 f45176
                      omega
                    have d45233 : (x 7 6 && x 7 10).toNat = 0 := by
                      have r45234 := hand2 (x 7 6) (x 7 10)
                      have b45235 := hb (x 7 10)
                      have b45236 := hb (x 7 6 && x 7 10)
                      clear * - r45234 b45235 b45236 d45217
                      omega
                    have d45237 : (x 6 11).toNat = 0 := by
                      have r45238 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e45239 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                      have e45240 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                      have e45241 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                      have e45242 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                      have e45243 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                      have e45244 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                      have b45245 := hb (x 2 7)
                      have b45246 := hb (x 3 6)
                      have b45247 := hb (x 4 5)
                      have b45248 := hb (x 5 4)
                      have b45249 := hb (x 6 11)
                      have b45250 := hb (x 7 10)
                      have b45251 := hb (x 8 9)
                      have b45252 := hb (x 9 8)
                      clear * - r45238 e45239 e45240 e45241 e45242 e45243 e45244 b45245 b45246 b45247 b45248 b45249 b45250 b45251 b45252 d45177 d45197 d45217 f45176
                      omega
                    have d45253 : (x 6 1 && x 6 11).toNat = 0 := by
                      have r45254 := hand2 (x 6 1) (x 6 11)
                      have b45255 := hb (x 6 11)
                      have b45256 := hb (x 6 1 && x 6 11)
                      clear * - r45254 b45255 b45256 d45237
                      omega
                    have d45257 : (x 6 7 && x 6 11).toNat = 0 := by
                      have r45258 := hand2 (x 6 7) (x 6 11)
                      have b45259 := hb (x 6 11)
                      have b45260 := hb (x 6 7 && x 6 11)
                      clear * - r45258 b45259 b45260 d45237
                      omega
                    have d45261 : (x 5 4).toNat = 0 := by
                      have r45262 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e45263 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                      have e45264 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                      have e45265 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                      have e45266 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                      have e45267 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                      have e45268 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                      have b45269 := hb (x 2 7)
                      have b45270 := hb (x 3 6)
                      have b45271 := hb (x 4 5)
                      have b45272 := hb (x 5 4)
                      have b45273 := hb (x 6 11)
                      have b45274 := hb (x 7 10)
                      have b45275 := hb (x 8 9)
                      have b45276 := hb (x 9 8)
                      clear * - r45262 e45263 e45264 e45265 e45266 e45267 e45268 b45269 b45270 b45271 b45272 b45273 b45274 b45275 b45276 d45177 d45197 d45217 d45237 f45176
                      omega
                    have d45277 : (x 5 4 && x 5 11).toNat = 0 := by
                      have r45278 := hand1 (x 5 4) (x 5 11)
                      have b45279 := hb (x 5 4)
                      have b45280 := hb (x 5 4 && x 5 11)
                      clear * - r45278 b45279 b45280 d45261
                      omega
                    have d45281 : (x 4 5).toNat = 0 := by
                      have r45282 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e45283 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                      have e45284 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                      have e45285 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                      have e45286 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                      have e45287 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                      have e45288 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                      have b45289 := hb (x 2 7)
                      have b45290 := hb (x 3 6)
                      have b45291 := hb (x 4 5)
                      have b45292 := hb (x 5 4)
                      have b45293 := hb (x 6 11)
                      have b45294 := hb (x 7 10)
                      have b45295 := hb (x 8 9)
                      have b45296 := hb (x 9 8)
                      clear * - r45282 e45283 e45284 e45285 e45286 e45287 e45288 b45289 b45290 b45291 b45292 b45293 b45294 b45295 b45296 d45177 d45197 d45217 d45237 d45261 f45176
                      omega
                    have d45297 : (x 3 6).toNat = 0 := by
                      have r45298 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e45299 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                      have e45300 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                      have e45301 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                      have e45302 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                      have e45303 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                      have e45304 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                      have b45305 := hb (x 2 7)
                      have b45306 := hb (x 3 6)
                      have b45307 := hb (x 4 5)
                      have b45308 := hb (x 5 4)
                      have b45309 := hb (x 6 11)
                      have b45310 := hb (x 7 10)
                      have b45311 := hb (x 8 9)
                      have b45312 := hb (x 9 8)
                      clear * - r45298 e45299 e45300 e45301 e45302 e45303 e45304 b45305 b45306 b45307 b45308 b45309 b45310 b45311 b45312 d45177 d45197 d45217 d45237 d45261 d45281 f45176
                      omega
                    have d45313 : (x 3 6 && x 3 13).toNat = 0 := by
                      have r45314 := hand1 (x 3 6) (x 3 13)
                      have b45315 := hb (x 3 6)
                      have b45316 := hb (x 3 6 && x 3 13)
                      clear * - r45314 b45315 b45316 d45297
                      omega
                    have r45317 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r45318 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e45319 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
                    have e45320 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
                    have e45321 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
                    have e45322 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
                    have e45323 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
                    have e45324 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
                    have r45325 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e45326 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                    have e45327 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                    have r45328 : 1 ≤ (x 13 4).toNat + (x 12 1 && x 12 5).toNat + (x 11 2 && x 11 6).toNat + (x 10 3 && x 10 7).toNat + (x 9 4 && x 9 8).toNat + (x 8 5 && x 8 9).toNat + (x 7 6 && x 7 10).toNat + (x 6 7 && x 6 11).toNat + (x 5 8 && x 5 12).toNat + (x 4 9 && x 4 13).toNat + (x 3 10 && x 3 14).toNat + (x 2 11).toNat := by have q := hcov4 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e45329 : (x 12 1 && x 12 5).toNat = (x 12 5).toNat := handr _ _ (fun h => hp13 12 (hp5 12 (h)))
                    have e45330 : (x 3 10 && x 3 14).toNat = (x 3 10).toNat := handl _ _ (fun h => hp2 3 (hp10 3 (h)))
                    have r45331 : 1 ≤ (x 9 7).toNat + (x 8 1 && x 8 8).toNat + (x 7 2 && x 7 9).toNat + (x 6 3 && x 6 10).toNat + (x 5 4 && x 5 11).toNat + (x 4 5 && x 4 12).toNat + (x 3 6 && x 3 13).toNat + (x 2 7 && x 2 14).toNat + (x 1 8).toNat := by have q := hcov7 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r45332 : 1 ≤ (x 16 9).toNat + (x 15 1 && x 15 10).toNat + (x 14 2 && x 14 11).toNat + (x 13 3 && x 13 12).toNat + (x 12 4 && x 12 13).toNat + (x 11 5 && x 11 14).toNat + (x 10 6).toNat := by have q := hcov9 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r45333 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r45334 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r45335 := hand2 (x 11 2) (x 11 6)
                    have r45336 := hand2 (x 10 3) (x 10 7)
                    have r45337 := hand2 (x 8 1) (x 8 8)
                    have r45338 := hand2 (x 7 2) (x 7 9)
                    have r45339 := hand2 (x 6 3) (x 6 10)
                    have r45340 := hand2 (x 15 1) (x 15 10)
                    have r45341 := hand2 (x 14 2) (x 14 11)
                    have r45342 := hand1 (x 13 3) (x 13 12)
                    have r45343 := hand1 (x 12 4) (x 12 13)
                    have r45344 := hand1 (x 11 5) (x 11 14)
                    have r45345 := hand2 (x 5 2) (x 5 12)
                    have r45346 := hand2 (x 4 3) (x 4 13)
                    have r45347 := hand1 (x 3 2) (x 3 13)
                    linarith only [r45317, r45318, e45319, e45320, e45321, e45322, e45323, e45324, r45325, e45326, e45327, r45328, e45329, e45330, r45331, r45332, r45333, r45334, r45335, r45336, r45337, r45338, r45339, r45340, r45341, r45342, r45343, r45344, r45345, r45346, r45347, d43033, d43881, f44595, d42559, d43412, g19, d43396, g21, g25, d45217, d45193, d45213, d45233, d45257, d43372, d43392, d45277, g36, d45313, g37, d45253, d42551, g52, g53]
                · have f45407 : (x 2 3).toNat = 1 := by rw [h44594]; rfl
                  have d45408 : (x 5 12).toNat = 0 := by
                    have r45409 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e45410 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                    have e45411 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                    have b45412 := hb (x 2 3)
                    have b45413 := hb (x 3 2)
                    have b45414 := hb (x 4 13)
                    have b45415 := hb (x 5 12)
                    clear * - r45409 e45410 e45411 b45412 b45413 b45414 b45415 f45407
                    omega
                  have d45416 : (x 5 1 && x 5 12).toNat = 0 := by
                    have r45417 := hand2 (x 5 1) (x 5 12)
                    have b45418 := hb (x 5 12)
                    have b45419 := hb (x 5 1 && x 5 12)
                    clear * - r45417 b45418 b45419 d45408
                    omega
                  have d45420 : (x 5 4).toNat = 0 := by
                    have r45421 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
                    have b45422 := hb (x 5 4)
                    have b45423 := hb (x 5 12)
                    clear * - r45421 b45422 b45423 d45408
                    omega
                  have d45424 : (x 4 13).toNat = 0 := by
                    have r45425 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e45426 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                    have e45427 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                    have b45428 := hb (x 2 3)
                    have b45429 := hb (x 3 2)
                    have b45430 := hb (x 4 13)
                    have b45431 := hb (x 5 12)
                    clear * - r45425 e45426 e45427 b45428 b45429 b45430 b45431 d45408 f45407
                    omega
                  have d45432 : (x 3 2).toNat = 0 := by
                    have r45433 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e45434 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                    have e45435 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                    have b45436 := hb (x 2 3)
                    have b45437 := hb (x 3 2)
                    have b45438 := hb (x 4 13)
                    have b45439 := hb (x 5 12)
                    clear * - r45433 e45434 e45435 b45436 b45437 b45438 b45439 d45408 d45424 f45407
                    omega
                  have d45440 : (x 5 13).toNat = 1 := by
                    have r45441 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b45442 := hb (x 3 2)
                    have b45443 := hb (x 5 13)
                    have b45444 := hb (x 4 1 && x 4 14)
                    clear * - r45441 b45442 b45443 b45444 g56 d45432
                    omega
                  have d45445 : (x 5 1).toNat = 1 := by
                    have r45446 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
                    have b45447 := hb (x 5 1)
                    have b45448 := hb (x 5 13)
                    clear * - r45446 b45447 b45448 d45440
                    omega
                  have d45449 : (x 6 14).toNat = 0 := by
                    have r45450 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b45451 := hb (x 5 1)
                    have b45452 := hb (x 6 14)
                    clear * - r45450 b45451 b45452 d45445
                    omega
                  have d45453 : (x 6 3 && x 6 14).toNat = 0 := by
                    have r45454 := hand2 (x 6 3) (x 6 14)
                    have b45455 := hb (x 6 14)
                    have b45456 := hb (x 6 3 && x 6 14)
                    clear * - r45454 b45455 b45456 d45449
                    omega
                  have d45457 : (x 6 2).toNat = 0 := by
                    have r45458 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
                    have b45459 := hb (x 6 2)
                    have b45460 := hb (x 6 14)
                    clear * - r45458 b45459 b45460 d45449
                    omega
                  have d45461 : (x 6 12).toNat = 0 := by
                    have r45462 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e45463 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                    have e45464 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                    have b45465 := hb (x 3 3)
                    have b45466 := hb (x 4 2)
                    have b45467 := hb (x 5 13)
                    have b45468 := hb (x 6 12)
                    clear * - r45462 e45463 e45464 b45465 b45466 b45467 b45468 d45440 g22
                    omega
                  have d45469 : (x 6 4).toNat = 0 := by
                    have r45470 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
                    have b45471 := hb (x 6 4)
                    have b45472 := hb (x 6 12)
                    clear * - r45470 b45471 b45472 d45461
                    omega
                  have d45473 : (x 3 3).toNat = 0 := by
                    have r45474 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e45475 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                    have e45476 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                    have b45477 := hb (x 3 3)
                    have b45478 := hb (x 4 2)
                    have b45479 := hb (x 5 13)
                    have b45480 := hb (x 6 12)
                    clear * - r45474 e45475 e45476 b45477 b45478 b45479 b45480 d45461 d45440 g22
                    omega
                  have d45481 : (x 3 3 && x 3 14).toNat = 0 := by
                    have r45482 := hand1 (x 3 3) (x 3 14)
                    have b45483 := hb (x 3 3)
                    have b45484 := hb (x 3 3 && x 3 14)
                    clear * - r45482 b45483 b45484 d45473
                    omega
                  have d45485 : (x 6 11).toNat = 1 := by
                    have r45486 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := by have q := hcov11 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b45487 := hb (x 2 4)
                    have b45488 := hb (x 6 11)
                    have b45489 := hb (x 5 1 && x 5 12)
                    have b45490 := hb (x 4 2 && x 4 13)
                    have b45491 := hb (x 3 3 && x 3 14)
                    clear * - r45486 b45487 b45488 b45489 b45490 b45491 d45416 g54 d45481 d42993
                    omega
                  have d45492 : (x 6 3).toNat = 1 := by
                    have r45493 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
                    have b45494 := hb (x 6 3)
                    have b45495 := hb (x 6 11)
                    clear * - r45493 b45494 b45495 d45485
                    omega
                  have d45496 : (x 9 12).toNat = 0 := by
                    have r45497 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e45498 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                    have e45499 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                    have b45500 := hb (x 6 3)
                    have b45501 := hb (x 7 2)
                    have b45502 := hb (x 8 13)
                    have b45503 := hb (x 9 12)
                    clear * - r45497 e45498 e45499 b45500 b45501 b45502 b45503 d45492
                    omega
                  have d45504 : (x 9 1 && x 9 12).toNat = 0 := by
                    have r45505 := hand2 (x 9 1) (x 9 12)
                    have b45506 := hb (x 9 12)
                    have b45507 := hb (x 9 1 && x 9 12)
                    clear * - r45505 b45506 b45507 d45496
                    omega
                  have d45508 : (x 9 4).toNat = 0 := by
                    have r45509 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
                    have b45510 := hb (x 9 4)
                    have b45511 := hb (x 9 12)
                    clear * - r45509 b45510 b45511 d45496
                    omega
                  have d45512 : (x 8 13).toNat = 0 := by
                    have r45513 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e45514 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                    have e45515 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                    have b45516 := hb (x 6 3)
                    have b45517 := hb (x 7 2)
                    have b45518 := hb (x 8 13)
                    have b45519 := hb (x 9 12)
                    clear * - r45513 e45514 e45515 b45516 b45517 b45518 b45519 d45496 d45492
                    omega
                  have d45520 : (x 8 2 && x 8 13).toNat = 0 := by
                    have r45521 := hand2 (x 8 2) (x 8 13)
                    have b45522 := hb (x 8 13)
                    have b45523 := hb (x 8 2 && x 8 13)
                    clear * - r45521 b45522 b45523 d45512
                    omega
                  have d45524 : (x 7 1 && x 7 14).toNat = 1 := by
                    have r45525 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b45526 := hb (x 6 2)
                    have b45527 := hb (x 8 13)
                    have b45528 := hb (x 7 1 && x 7 14)
                    clear * - r45525 b45526 b45527 b45528 d45512 d45457
                    omega
                  have d45529 : (x 7 1).toNat = 1 := by
                    have r45530 := hand1 (x 7 1) (x 7 14)
                    have b45531 := hb (x 7 1)
                    have b45532 := hb (x 7 1 && x 7 14)
                    clear * - r45530 b45531 b45532 d45524
                    omega
                  have d45533 : (x 8 14).toNat = 0 := by
                    have r45534 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b45535 := hb (x 7 1)
                    have b45536 := hb (x 8 14)
                    clear * - r45534 b45535 b45536 d45529
                    omega
                  have d45537 : (x 8 1 && x 8 14).toNat = 0 := by
                    have r45538 := hand2 (x 8 1) (x 8 14)
                    have b45539 := hb (x 8 14)
                    have b45540 := hb (x 8 1 && x 8 14)
                    clear * - r45538 b45539 b45540 d45533
                    omega
                  have d45541 : (x 8 2).toNat = 0 := by
                    have r45542 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
                    have b45543 := hb (x 8 2)
                    have b45544 := hb (x 8 14)
                    clear * - r45542 b45543 b45544 d45533
                    omega
                  have d45545 : (x 7 2).toNat = 0 := by
                    have r45546 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e45547 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                    have e45548 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                    have b45549 := hb (x 6 3)
                    have b45550 := hb (x 7 2)
                    have b45551 := hb (x 8 13)
                    have b45552 := hb (x 9 12)
                    clear * - r45546 e45547 e45548 b45549 b45550 b45551 b45552 d45496 d45512 d45492
                    omega
                  have d45553 : (x 7 2 && x 7 13).toNat = 0 := by
                    have r45554 := hand1 (x 7 2) (x 7 13)
                    have b45555 := hb (x 7 2)
                    have b45556 := hb (x 7 2 && x 7 13)
                    clear * - r45554 b45555 b45556 d45545
                    omega
                  have d45557 : (x 9 13).toNat = 1 := by
                    have r45558 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b45559 := hb (x 7 2)
                    have b45560 := hb (x 9 13)
                    have b45561 := hb (x 8 1 && x 8 14)
                    clear * - r45558 b45559 b45560 b45561 d45537 d45545
                    omega
                  have d45562 : (x 9 1).toNat = 1 := by
                    have r45563 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
                    have b45564 := hb (x 9 1)
                    have b45565 := hb (x 9 13)
                    clear * - r45563 b45564 b45565 d45557
                    omega
                  have d45566 : (x 10 14).toNat = 0 := by
                    have r45567 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b45568 := hb (x 9 1)
                    have b45569 := hb (x 10 14)
                    clear * - r45567 b45568 b45569 d45562
                    omega
                  have d45570 : (x 10 1 && x 10 14).toNat = 0 := by
                    have r45571 := hand2 (x 10 1) (x 10 14)
                    have b45572 := hb (x 10 14)
                    have b45573 := hb (x 10 1 && x 10 14)
                    clear * - r45571 b45572 b45573 d45566
                    omega
                  have d45574 : (x 10 3 && x 10 14).toNat = 0 := by
                    have r45575 := hand2 (x 10 3) (x 10 14)
                    have b45576 := hb (x 10 14)
                    have b45577 := hb (x 10 3 && x 10 14)
                    clear * - r45575 b45576 b45577 d45566
                    omega
                  have d45578 : (x 10 2).toNat = 0 := by
                    have r45579 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
                    have b45580 := hb (x 10 2)
                    have b45581 := hb (x 10 14)
                    clear * - r45579 b45580 b45581 d45566
                    omega
                  have d45582 : (x 10 12).toNat = 0 := by
                    have r45583 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e45584 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                    have e45585 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                    have b45586 := hb (x 7 3)
                    have b45587 := hb (x 8 2)
                    have b45588 := hb (x 9 13)
                    have b45589 := hb (x 10 12)
                    clear * - r45583 e45584 e45585 b45586 b45587 b45588 b45589 d45557 d45541
                    omega
                  have d45590 : (x 10 4).toNat = 0 := by
                    have r45591 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
                    have b45592 := hb (x 10 4)
                    have b45593 := hb (x 10 12)
                    clear * - r45591 b45592 b45593 d45582
                    omega
                  have d45594 : (x 7 3).toNat = 0 := by
                    have r45595 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e45596 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                    have e45597 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                    have b45598 := hb (x 7 3)
                    have b45599 := hb (x 8 2)
                    have b45600 := hb (x 9 13)
                    have b45601 := hb (x 10 12)
                    clear * - r45595 e45596 e45597 b45598 b45599 b45600 b45601 d45582 d45557 d45541
                    omega
                  have d45602 : (x 7 3 && x 7 14).toNat = 0 := by
                    have r45603 := hand1 (x 7 3) (x 7 14)
                    have b45604 := hb (x 7 3)
                    have b45605 := hb (x 7 3 && x 7 14)
                    clear * - r45603 b45604 b45605 d45594
                    omega
                  have d45606 : (x 10 11).toNat = 1 := by
                    have r45607 : 1 ≤ (x 10 11).toNat + (x 9 1 && x 9 12).toNat + (x 8 2 && x 8 13).toNat + (x 7 3 && x 7 14).toNat + (x 6 4).toNat := by have q := hcov11 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b45608 := hb (x 6 4)
                    have b45609 := hb (x 10 11)
                    have b45610 := hb (x 9 1 && x 9 12)
                    have b45611 := hb (x 8 2 && x 8 13)
                    have b45612 := hb (x 7 3 && x 7 14)
                    clear * - r45607 b45608 b45609 b45610 b45611 b45612 d45504 d45520 d45602 d45469
                    omega
                  have d45613 : (x 10 3).toNat = 1 := by
                    have r45614 : (x 10 11).toNat ≤ (x 10 3).toNat := himp _ _ (hp11 10)
                    have b45615 := hb (x 10 3)
                    have b45616 := hb (x 10 11)
                    clear * - r45614 b45615 b45616 d45606
                    omega
                  have d45617 : (x 13 12).toNat = 0 := by
                    have r45618 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e45619 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
                    have e45620 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
                    have b45621 := hb (x 10 3)
                    have b45622 := hb (x 11 2)
                    have b45623 := hb (x 12 13)
                    have b45624 := hb (x 13 12)
                    clear * - r45618 e45619 e45620 b45621 b45622 b45623 b45624 d45613
                    omega
                  have d45625 : (x 13 1 && x 13 12).toNat = 0 := by
                    have r45626 := hand2 (x 13 1) (x 13 12)
                    have b45627 := hb (x 13 12)
                    have b45628 := hb (x 13 1 && x 13 12)
                    clear * - r45626 b45627 b45628 d45617
                    omega
                  have d45629 : (x 13 2 && x 13 12).toNat = 0 := by
                    have r45630 := hand2 (x 13 2) (x 13 12)
                    have b45631 := hb (x 13 12)
                    have b45632 := hb (x 13 2 && x 13 12)
                    clear * - r45630 b45631 b45632 d45617
                    omega
                  have d45633 : (x 12 13).toNat = 0 := by
                    have r45634 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e45635 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
                    have e45636 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
                    have b45637 := hb (x 10 3)
                    have b45638 := hb (x 11 2)
                    have b45639 := hb (x 12 13)
                    have b45640 := hb (x 13 12)
                    clear * - r45634 e45635 e45636 b45637 b45638 b45639 b45640 d45617 d45613
                    omega
                  have d45641 : (x 12 2 && x 12 13).toNat = 0 := by
                    have r45642 := hand2 (x 12 2) (x 12 13)
                    have b45643 := hb (x 12 13)
                    have b45644 := hb (x 12 2 && x 12 13)
                    clear * - r45642 b45643 b45644 d45633
                    omega
                  have d45645 : (x 12 3 && x 12 13).toNat = 0 := by
                    have r45646 := hand2 (x 12 3) (x 12 13)
                    have b45647 := hb (x 12 13)
                    have b45648 := hb (x 12 3 && x 12 13)
                    clear * - r45646 b45647 b45648 d45633
                    omega
                  have d45649 : (x 11 1 && x 11 14).toNat = 1 := by
                    have r45650 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b45651 := hb (x 10 2)
                    have b45652 := hb (x 12 13)
                    have b45653 := hb (x 11 1 && x 11 14)
                    clear * - r45650 b45651 b45652 b45653 d45633 d45578
                    omega
                  have d45654 : (x 11 14).toNat = 1 := by
                    have r45655 := hand2 (x 11 1) (x 11 14)
                    have b45656 := hb (x 11 14)
                    have b45657 := hb (x 11 1 && x 11 14)
                    clear * - r45655 b45656 b45657 d45649
                    omega
                  have d45658 : (x 10 1).toNat = 0 := by
                    have r45659 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b45660 := hb (x 10 1)
                    have b45661 := hb (x 11 14)
                    clear * - r45659 b45660 b45661 d45654
                    omega
                  have d45662 : (x 10 13).toNat = 0 := by
                    have r45663 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
                    have b45664 := hb (x 10 1)
                    have b45665 := hb (x 10 13)
                    clear * - r45663 b45664 b45665 d45658
                    omega
                  have d45666 : (x 10 5).toNat = 0 := by
                    have r45667 : (x 10 5).toNat ≤ (x 10 13).toNat := himp _ _ (hp5 10)
                    have b45668 := hb (x 10 5)
                    have b45669 := hb (x 10 13)
                    clear * - r45667 b45668 b45669 d45662
                    omega
                  have d45670 : (x 9 1 && x 9 14).toNat = 1 := by
                    have r45671 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b45672 := hb (x 8 2)
                    have b45673 := hb (x 10 13)
                    have b45674 := hb (x 9 1 && x 9 14)
                    clear * - r45671 b45672 b45673 b45674 d45662 d45541
                    omega
                  have d45675 : (x 9 14).toNat = 1 := by
                    have r45676 := hand2 (x 9 1) (x 9 14)
                    have b45677 := hb (x 9 14)
                    have b45678 := hb (x 9 1 && x 9 14)
                    clear * - r45676 b45677 b45678 d45670
                    omega
                  have d45679 : (x 8 1).toNat = 0 := by
                    have r45680 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b45681 := hb (x 8 1)
                    have b45682 := hb (x 9 14)
                    clear * - r45680 b45681 b45682 d45675
                    omega
                  have d45683 : (x 8 1 && x 8 12).toNat = 0 := by
                    have r45684 := hand1 (x 8 1) (x 8 12)
                    have b45685 := hb (x 8 1)
                    have b45686 := hb (x 8 1 && x 8 12)
                    clear * - r45684 b45685 b45686 d45679
                    omega
                  have d45687 : (x 9 11).toNat = 1 := by
                    have r45688 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b45689 := hb (x 5 4)
                    have b45690 := hb (x 9 11)
                    have b45691 := hb (x 8 1 && x 8 12)
                    have b45692 := hb (x 7 2 && x 7 13)
                    have b45693 := hb (x 6 3 && x 6 14)
                    clear * - r45688 b45689 b45690 b45691 b45692 b45693 d45683 d45553 d45453 d45420
                    omega
                  have d45694 : (x 9 3).toNat = 1 := by
                    have r45695 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
                    have b45696 := hb (x 9 3)
                    have b45697 := hb (x 9 11)
                    clear * - r45695 b45696 b45697 d45687
                    omega
                  have d45698 : (x 12 12).toNat = 0 := by
                    have r45699 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e45700 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
                    have e45701 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
                    have b45702 := hb (x 9 3)
                    have b45703 := hb (x 10 2)
                    have b45704 := hb (x 11 13)
                    have b45705 := hb (x 12 12)
                    clear * - r45699 e45700 e45701 b45702 b45703 b45704 b45705 d45578 d45694
                    omega
                  have d45706 : (x 12 1 && x 12 12).toNat = 0 := by
                    have r45707 := hand2 (x 12 1) (x 12 12)
                    have b45708 := hb (x 12 12)
                    have b45709 := hb (x 12 1 && x 12 12)
                    clear * - r45707 b45708 b45709 d45698
                    omega
                  have d45710 : (x 11 13).toNat = 0 := by
                    have r45711 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e45712 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
                    have e45713 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
                    have b45714 := hb (x 9 3)
                    have b45715 := hb (x 10 2)
                    have b45716 := hb (x 11 13)
                    have b45717 := hb (x 12 12)
                    clear * - r45711 e45712 e45713 b45714 b45715 b45716 b45717 d45698 d45578 d45694
                    omega
                  have d45718 : (x 11 2 && x 11 13).toNat = 0 := by
                    have r45719 := hand2 (x 11 2) (x 11 13)
                    have b45720 := hb (x 11 13)
                    have b45721 := hb (x 11 2 && x 11 13)
                    clear * - r45719 b45720 b45721 d45710
                    omega
                  have d45722 : (x 13 11).toNat = 1 := by
                    have r45723 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b45724 := hb (x 9 4)
                    have b45725 := hb (x 13 11)
                    have b45726 := hb (x 12 1 && x 12 12)
                    have b45727 := hb (x 11 2 && x 11 13)
                    have b45728 := hb (x 10 3 && x 10 14)
                    clear * - r45723 b45724 b45725 b45726 b45727 b45728 d45706 d45718 d45574 d45508
                    omega
                  have d45729 : (x 13 3).toNat = 1 := by
                    have r45730 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
                    have b45731 := hb (x 13 3)
                    have b45732 := hb (x 13 11)
                    clear * - r45730 b45731 b45732 d45722
                    omega
                  have d45733 : (x 16 12).toNat = 0 := by
                    have r45734 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e45735 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                    have e45736 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                    have b45737 := hb (x 13 3)
                    have b45738 := hb (x 14 2)
                    have b45739 := hb (x 15 13)
                    have b45740 := hb (x 16 12)
                    clear * - r45734 e45735 e45736 b45737 b45738 b45739 b45740 d45729
                    omega
                  have d45741 : (x 15 13).toNat = 0 := by
                    have r45742 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e45743 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                    have e45744 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                    have b45745 := hb (x 13 3)
                    have b45746 := hb (x 14 2)
                    have b45747 := hb (x 15 13)
                    have b45748 := hb (x 16 12)
                    clear * - r45742 e45743 e45744 b45745 b45746 b45747 b45748 d45733 d45729
                    omega
                  have d45749 : (x 14 2).toNat = 0 := by
                    have r45750 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e45751 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                    have e45752 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                    have b45753 := hb (x 13 3)
                    have b45754 := hb (x 14 2)
                    have b45755 := hb (x 15 13)
                    have b45756 := hb (x 16 12)
                    clear * - r45750 e45751 e45752 b45753 b45754 b45755 b45756 d45733 d45741 d45729
                    omega
                  have d45757 : (x 9 2).toNat = 1 := by
                    have r45758 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b45759 := hb (x 9 2)
                    have b45760 := hb (x 11 13)
                    have b45761 := hb (x 10 1 && x 10 14)
                    clear * - r45758 b45759 b45760 b45761 d45710 d45570
                    omega
                  have d45762 : (x 11 12).toNat = 0 := by
                    have r45763 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e45764 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                    have e45765 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                    have b45766 := hb (x 8 3)
                    have b45767 := hb (x 9 2)
                    have b45768 := hb (x 10 13)
                    have b45769 := hb (x 11 12)
                    clear * - r45763 e45764 e45765 b45766 b45767 b45768 b45769 d45662 d45757
                    omega
                  have d45770 : (x 11 4).toNat = 0 := by
                    have r45771 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
                    have b45772 := hb (x 11 4)
                    have b45773 := hb (x 11 12)
                    clear * - r45771 b45772 b45773 d45762
                    omega
                  have d45774 : (x 11 4 && x 11 14).toNat = 0 := by
                    have r45775 := hand1 (x 11 4) (x 11 14)
                    have b45776 := hb (x 11 4)
                    have b45777 := hb (x 11 4 && x 11 14)
                    clear * - r45775 b45776 b45777 d45770
                    omega
                  have d45778 : (x 11 1).toNat = 1 := by
                    have r45779 := hand1 (x 11 1) (x 11 14)
                    have b45780 := hb (x 11 1)
                    have b45781 := hb (x 11 1 && x 11 14)
                    clear * - r45779 b45780 b45781 d45649
                    omega
                  have d45782 : (x 12 14).toNat = 0 := by
                    have r45783 : (x 12 14).toNat + (x 11 1).toNat = 1 := by have q := hd14 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b45784 := hb (x 11 1)
                    have b45785 := hb (x 12 14)
                    clear * - r45783 b45784 b45785 d45778
                    omega
                  have d45786 : (x 12 1 && x 12 14).toNat = 0 := by
                    have r45787 := hand2 (x 12 1) (x 12 14)
                    have b45788 := hb (x 12 14)
                    have b45789 := hb (x 12 1 && x 12 14)
                    clear * - r45787 b45788 b45789 d45782
                    omega
                  have d45790 : (x 12 2).toNat = 0 := by
                    have r45791 : (x 12 2).toNat ≤ (x 12 14).toNat := himp _ _ (hp2 12)
                    have b45792 := hb (x 12 2)
                    have b45793 := hb (x 12 14)
                    clear * - r45791 b45792 b45793 d45782
                    omega
                  have d45794 : (x 11 2).toNat = 0 := by
                    have r45795 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e45796 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
                    have e45797 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
                    have b45798 := hb (x 10 3)
                    have b45799 := hb (x 11 2)
                    have b45800 := hb (x 12 13)
                    have b45801 := hb (x 13 12)
                    clear * - r45795 e45796 e45797 b45798 b45799 b45800 b45801 d45617 d45633 d45613
                    omega
                  have d45802 : (x 13 13).toNat = 1 := by
                    have r45803 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b45804 := hb (x 11 2)
                    have b45805 := hb (x 13 13)
                    have b45806 := hb (x 12 1 && x 12 14)
                    clear * - r45803 b45804 b45805 b45806 d45786 d45794
                    omega
                  have d45807 : (x 14 12).toNat = 0 := by
                    have r45808 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e45809 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
                    have e45810 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
                    have b45811 := hb (x 11 3)
                    have b45812 := hb (x 12 2)
                    have b45813 := hb (x 13 13)
                    have b45814 := hb (x 14 12)
                    clear * - r45808 e45809 e45810 b45811 b45812 b45813 b45814 d45802 d45790
                    omega
                  have d45815 : (x 11 3).toNat = 0 := by
                    have r45816 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e45817 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
                    have e45818 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
                    have b45819 := hb (x 11 3)
                    have b45820 := hb (x 12 2)
                    have b45821 := hb (x 13 13)
                    have b45822 := hb (x 14 12)
                    clear * - r45816 e45817 e45818 b45819 b45820 b45821 b45822 d45807 d45802 d45790
                    omega
                  have d45823 : (x 11 3 && x 11 14).toNat = 0 := by
                    have r45824 := hand1 (x 11 3) (x 11 14)
                    have b45825 := hb (x 11 3)
                    have b45826 := hb (x 11 3 && x 11 14)
                    clear * - r45824 b45825 b45826 d45815
                    omega
                  have d45827 : (x 14 11).toNat = 1 := by
                    have r45828 : 1 ≤ (x 14 11).toNat + (x 13 1 && x 13 12).toNat + (x 12 2 && x 12 13).toNat + (x 11 3 && x 11 14).toNat + (x 10 4).toNat := by have q := hcov11 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b45829 := hb (x 10 4)
                    have b45830 := hb (x 14 11)
                    have b45831 := hb (x 13 1 && x 13 12)
                    have b45832 := hb (x 12 2 && x 12 13)
                    have b45833 := hb (x 11 3 && x 11 14)
                    clear * - r45828 b45829 b45830 b45831 b45832 b45833 d45625 d45641 d45823 d45590
                    omega
                  have d45834 : (x 14 3).toNat = 1 := by
                    have r45835 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
                    have b45836 := hb (x 14 3)
                    have b45837 := hb (x 14 11)
                    clear * - r45835 b45836 b45837 d45827
                    omega
                  have d45838 : (x 17 12).toNat = 0 := by
                    have r45839 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e45840 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                    have e45841 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                    have b45842 := hb (x 14 3)
                    have b45843 := hb (x 15 2)
                    have b45844 := hb (x 16 13)
                    have b45845 := hb (x 17 12)
                    clear * - r45839 e45840 e45841 b45842 b45843 b45844 b45845 d45834
                    omega
                  have d45846 : (x 16 13).toNat = 0 := by
                    have r45847 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e45848 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                    have e45849 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                    have b45850 := hb (x 14 3)
                    have b45851 := hb (x 15 2)
                    have b45852 := hb (x 16 13)
                    have b45853 := hb (x 17 12)
                    clear * - r45847 e45848 e45849 b45850 b45851 b45852 b45853 d45838 d45834
                    omega
                  have d45854 : (x 15 1 && x 15 14).toNat = 1 := by
                    have r45855 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b45856 := hb (x 14 2)
                    have b45857 := hb (x 16 13)
                    have b45858 := hb (x 15 1 && x 15 14)
                    clear * - r45855 b45856 b45857 b45858 d45846 d45749
                    omega
                  have d45859 : (x 15 14).toNat = 1 := by
                    have r45860 := hand2 (x 15 1) (x 15 14)
                    have b45861 := hb (x 15 14)
                    have b45862 := hb (x 15 1 && x 15 14)
                    clear * - r45860 b45861 b45862 d45854
                    omega
                  have d45863 : (x 14 1).toNat = 0 := by
                    have r45864 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b45865 := hb (x 14 1)
                    have b45866 := hb (x 15 14)
                    clear * - r45864 b45865 b45866 d45859
                    omega
                  have d45867 : (x 14 1 && x 14 11).toNat = 0 := by
                    have r45868 := hand1 (x 14 1) (x 14 11)
                    have b45869 := hb (x 14 1)
                    have b45870 := hb (x 14 1 && x 14 11)
                    clear * - r45868 b45869 b45870 d45863
                    omega
                  have d45871 : (x 15 2).toNat = 0 := by
                    have r45872 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e45873 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                    have e45874 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                    have b45875 := hb (x 14 3)
                    have b45876 := hb (x 15 2)
                    have b45877 := hb (x 16 13)
                    have b45878 := hb (x 17 12)
                    clear * - r45872 e45873 e45874 b45875 b45876 b45877 b45878 d45838 d45846 d45834
                    omega
                  have d45879 : (x 15 10).toNat = 0 := by
                    have r45880 : (x 15 10).toNat ≤ (x 15 2).toNat := himp _ _ (hp10 15)
                    have b45881 := hb (x 15 2)
                    have b45882 := hb (x 15 10)
                    clear * - r45880 b45881 b45882 d45871
                    omega
                  have r45883 : 1 ≤ (x 15 10).toNat + (x 14 1 && x 14 11).toNat + (x 13 2 && x 13 12).toNat + (x 12 3 && x 12 13).toNat + (x 11 4 && x 11 14).toNat + (x 10 5).toNat := by have q := hcov10 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b45884 := hb (x 10 5)
                  have b45885 := hb (x 15 10)
                  have b45886 := hb (x 14 1 && x 14 11)
                  have b45887 := hb (x 13 2 && x 13 12)
                  have b45888 := hb (x 12 3 && x 12 13)
                  have b45889 := hb (x 11 4 && x 11 14)
                  linarith only [r45883, b45884, b45885, b45886, b45887, b45888, b45889, d45879, d45867, d45629, d45645, d45774, d45666]
            · have f45890 : (x (-1) 12).toNat = 1 := by rw [h43985]; rfl
              have d45891 : (x (-2) 13).toNat = 0 := by
                have r45892 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e45893 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                have e45894 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                have b45895 := hb (x (-4) 3)
                have b45896 := hb (x (-3) 2)
                have b45897 := hb (x (-2) 13)
                have b45898 := hb (x (-1) 12)
                clear * - r45892 e45893 e45894 b45895 b45896 b45897 b45898 f45890
                omega
              have d45899 : (x (-3) 2).toNat = 0 := by
                have r45900 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e45901 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                have e45902 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                have b45903 := hb (x (-4) 3)
                have b45904 := hb (x (-3) 2)
                have b45905 := hb (x (-2) 13)
                have b45906 := hb (x (-1) 12)
                clear * - r45900 e45901 e45902 b45903 b45904 b45905 b45906 f45890 d45891
                omega
              have d45907 : (x (-3) 2 && x (-3) 13).toNat = 0 := by
                have r45908 := hand1 (x (-3) 2) (x (-3) 13)
                have b45909 := hb (x (-3) 2)
                have b45910 := hb (x (-3) 2 && x (-3) 13)
                clear * - r45908 b45909 b45910 d45899
                omega
              have d45911 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
                have r45912 := hand1 (x (-3) 2) (x (-3) 12)
                have b45913 := hb (x (-3) 2)
                have b45914 := hb (x (-3) 2 && x (-3) 12)
                clear * - r45912 b45913 b45914 d45899
                omega
              have d45915 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
                have r45916 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45917 := hb (x (-3) 2)
                have b45918 := hb (x (-1) 13)
                have b45919 := hb (x (-2) 1 && x (-2) 14)
                clear * - r45916 b45917 b45918 b45919 g7 d45899
                omega
              have d45920 : (x (-2) 14).toNat = 1 := by
                have r45921 := hand2 (x (-2) 1) (x (-2) 14)
                have b45922 := hb (x (-2) 14)
                have b45923 := hb (x (-2) 1 && x (-2) 14)
                clear * - r45921 b45922 b45923 d45915
                omega
              have d45924 : (x (-3) 1).toNat = 0 := by
                have r45925 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45926 := hb (x (-3) 1)
                have b45927 := hb (x (-2) 14)
                clear * - r45925 b45926 b45927 d45920
                omega
              have d45928 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
                have r45929 := hand1 (x (-3) 1) (x (-3) 14)
                have b45930 := hb (x (-3) 1)
                have b45931 := hb (x (-3) 1 && x (-3) 14)
                clear * - r45929 b45930 b45931 d45924
                omega
              have d45932 : (x (-4) 2).toNat = 1 := by
                have r45933 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45934 := hb (x (-4) 2)
                have b45935 := hb (x (-2) 13)
                have b45936 := hb (x (-3) 1 && x (-3) 14)
                clear * - r45933 b45934 b45935 b45936 d45891 d45928
                omega
              have d45937 : (x (-4) 14).toNat = 1 := by
                have r45938 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
                have b45939 := hb (x (-4) 2)
                have b45940 := hb (x (-4) 14)
                clear * - r45938 b45939 b45940 d45932
                omega
              have d45941 : (x (-5) 1).toNat = 0 := by
                have r45942 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45943 := hb (x (-5) 1)
                have b45944 := hb (x (-4) 14)
                clear * - r45942 b45943 b45944 d45937
                omega
              have d45945 : (x (-5) 13).toNat = 0 := by
                have r45946 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
                have b45947 := hb (x (-5) 1)
                have b45948 := hb (x (-5) 13)
                clear * - r45946 b45947 b45948 d45941
                omega
              have d45949 : (x (-3) 13).toNat = 0 := by
                have r45950 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
                have b45951 := hb (x (-3) 1)
                have b45952 := hb (x (-3) 13)
                clear * - r45950 b45951 b45952 d45924
                omega
              have d45953 : (x (-4) 3).toNat = 0 := by
                have r45954 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e45955 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                have e45956 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                have b45957 := hb (x (-4) 3)
                have b45958 := hb (x (-3) 2)
                have b45959 := hb (x (-2) 13)
                have b45960 := hb (x (-1) 12)
                clear * - r45954 e45955 e45956 b45957 b45958 b45959 b45960 f45890 d45891 d45899
                omega
              have d45961 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
                have r45962 := hand1 (x (-4) 3) (x (-4) 14)
                have b45963 := hb (x (-4) 3)
                have b45964 := hb (x (-4) 3 && x (-4) 14)
                clear * - r45962 b45963 b45964 d45953
                omega
              have d45965 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
                have r45966 := hand1 (x (-4) 3) (x (-4) 13)
                have b45967 := hb (x (-4) 3)
                have b45968 := hb (x (-4) 3 && x (-4) 13)
                clear * - r45966 b45967 b45968 d45953
                omega
              have d45969 : (x (-2) 12).toNat = 0 := by
                have r45970 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e45971 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                have e45972 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                have b45973 := hb (x (-5) 3)
                have b45974 := hb (x (-4) 2)
                have b45975 := hb (x (-3) 13)
                have b45976 := hb (x (-2) 12)
                clear * - r45970 e45971 e45972 b45973 b45974 b45975 b45976 d45949 d45932
                omega
              have d45977 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
                have r45978 := hand2 (x (-2) 1) (x (-2) 12)
                have b45979 := hb (x (-2) 12)
                have b45980 := hb (x (-2) 1 && x (-2) 12)
                clear * - r45978 b45979 b45980 d45969
                omega
              have d45981 : (x (-5) 4).toNat = 1 := by
                have r45982 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b45983 := hb (x (-5) 4)
                have b45984 := hb (x (-1) 11)
                have b45985 := hb (x (-2) 1 && x (-2) 12)
                have b45986 := hb (x (-3) 2 && x (-3) 13)
                have b45987 := hb (x (-4) 3 && x (-4) 14)
                clear * - r45982 b45983 b45984 b45985 b45986 b45987 d43021 d45977 d45907 d45961
                omega
              have d45988 : (x (-5) 12).toNat = 1 := by
                have r45989 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
                have b45990 := hb (x (-5) 4)
                have b45991 := hb (x (-5) 12)
                clear * - r45989 b45990 b45991 d45981
                omega
              have d45992 : (x (-6) 13).toNat = 0 := by
                have r45993 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e45994 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                have e45995 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                have b45996 := hb (x (-8) 3)
                have b45997 := hb (x (-7) 2)
                have b45998 := hb (x (-6) 13)
                have b45999 := hb (x (-5) 12)
                clear * - r45993 e45994 e45995 b45996 b45997 b45998 b45999 d45988
                omega
              have d46000 : (x (-6) 5).toNat = 0 := by
                have r46001 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
                have b46002 := hb (x (-6) 5)
                have b46003 := hb (x (-6) 13)
                clear * - r46001 b46002 b46003 d45992
                omega
              have d46004 : (x (-7) 2).toNat = 0 := by
                have r46005 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e46006 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                have e46007 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                have b46008 := hb (x (-8) 3)
                have b46009 := hb (x (-7) 2)
                have b46010 := hb (x (-6) 13)
                have b46011 := hb (x (-5) 12)
                clear * - r46005 e46006 e46007 b46008 b46009 b46010 b46011 d45988 d45992
                omega
              have d46012 : (x (-6) 1 && x (-6) 14).toNat = 1 := by
                have r46013 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b46014 := hb (x (-7) 2)
                have b46015 := hb (x (-5) 13)
                have b46016 := hb (x (-6) 1 && x (-6) 14)
                clear * - r46013 b46014 b46015 b46016 d45945 d46004
                omega
              have d46017 : (x (-6) 1).toNat = 1 := by
                have r46018 := hand1 (x (-6) 1) (x (-6) 14)
                have b46019 := hb (x (-6) 1)
                have b46020 := hb (x (-6) 1 && x (-6) 14)
                clear * - r46018 b46019 b46020 d46012
                omega
              have d46021 : (x (-5) 14).toNat = 0 := by
                have r46022 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b46023 := hb (x (-6) 1)
                have b46024 := hb (x (-5) 14)
                clear * - r46022 b46023 b46024 d46017
                omega
              have d46025 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
                have r46026 := hand2 (x (-5) 4) (x (-5) 14)
                have b46027 := hb (x (-5) 14)
                have b46028 := hb (x (-5) 4 && x (-5) 14)
                clear * - r46026 b46027 b46028 d46021
                omega
              have r46029 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b46030 := hb (x (-6) 5)
              have b46031 := hb (x (-1) 10)
              have b46032 := hb (x (-2) 1 && x (-2) 11)
              have b46033 := hb (x (-3) 2 && x (-3) 12)
              have b46034 := hb (x (-4) 3 && x (-4) 13)
              have b46035 := hb (x (-5) 4 && x (-5) 14)
              linarith only [r46029, b46030, b46031, b46032, b46033, b46034, b46035, d43045, d43061, d45911, d45965, d46025, d46000]
          · have f46036 : (x (-1) 8).toNat = 1 := by rw [h43983]; rfl
            have d46037 : (x (-2) 9).toNat = 0 := by
              have r46038 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46039 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e46040 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e46041 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e46042 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e46043 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e46044 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b46045 := hb (x (-8) 7)
              have b46046 := hb (x (-7) 6)
              have b46047 := hb (x (-6) 5)
              have b46048 := hb (x (-5) 4)
              have b46049 := hb (x (-4) 11)
              have b46050 := hb (x (-3) 10)
              have b46051 := hb (x (-2) 9)
              have b46052 := hb (x (-1) 8)
              clear * - r46038 e46039 e46040 e46041 e46042 e46043 e46044 b46045 b46046 b46047 b46048 b46049 b46050 b46051 b46052 f46036
              omega
            have d46053 : (x (-3) 10).toNat = 0 := by
              have r46054 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46055 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e46056 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e46057 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e46058 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e46059 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e46060 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b46061 := hb (x (-8) 7)
              have b46062 := hb (x (-7) 6)
              have b46063 := hb (x (-6) 5)
              have b46064 := hb (x (-5) 4)
              have b46065 := hb (x (-4) 11)
              have b46066 := hb (x (-3) 10)
              have b46067 := hb (x (-2) 9)
              have b46068 := hb (x (-1) 8)
              clear * - r46054 e46055 e46056 e46057 e46058 e46059 e46060 b46061 b46062 b46063 b46064 b46065 b46066 b46067 b46068 f46036 d46037
              omega
            have d46069 : (x (-3) 1 && x (-3) 10).toNat = 0 := by
              have r46070 := hand2 (x (-3) 1) (x (-3) 10)
              have b46071 := hb (x (-3) 10)
              have b46072 := hb (x (-3) 1 && x (-3) 10)
              clear * - r46070 b46071 b46072 d46053
              omega
            have d46073 : (x (-4) 11).toNat = 0 := by
              have r46074 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46075 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e46076 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e46077 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e46078 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e46079 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e46080 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b46081 := hb (x (-8) 7)
              have b46082 := hb (x (-7) 6)
              have b46083 := hb (x (-6) 5)
              have b46084 := hb (x (-5) 4)
              have b46085 := hb (x (-4) 11)
              have b46086 := hb (x (-3) 10)
              have b46087 := hb (x (-2) 9)
              have b46088 := hb (x (-1) 8)
              clear * - r46074 e46075 e46076 e46077 e46078 e46079 e46080 b46081 b46082 b46083 b46084 b46085 b46086 b46087 b46088 f46036 d46037 d46053
              omega
            have d46089 : (x (-4) 2 && x (-4) 11).toNat = 0 := by
              have r46090 := hand2 (x (-4) 2) (x (-4) 11)
              have b46091 := hb (x (-4) 11)
              have b46092 := hb (x (-4) 2 && x (-4) 11)
              clear * - r46090 b46091 b46092 d46073
              omega
            have d46093 : (x (-5) 4).toNat = 0 := by
              have r46094 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46095 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e46096 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e46097 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e46098 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e46099 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e46100 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b46101 := hb (x (-8) 7)
              have b46102 := hb (x (-7) 6)
              have b46103 := hb (x (-6) 5)
              have b46104 := hb (x (-5) 4)
              have b46105 := hb (x (-4) 11)
              have b46106 := hb (x (-3) 10)
              have b46107 := hb (x (-2) 9)
              have b46108 := hb (x (-1) 8)
              clear * - r46094 e46095 e46096 e46097 e46098 e46099 e46100 b46101 b46102 b46103 b46104 b46105 b46106 b46107 b46108 f46036 d46037 d46053 d46073
              omega
            have d46109 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
              have r46110 := hand1 (x (-5) 4) (x (-5) 14)
              have b46111 := hb (x (-5) 4)
              have b46112 := hb (x (-5) 4 && x (-5) 14)
              clear * - r46110 b46111 b46112 d46093
              omega
            have d46113 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
              have r46114 := hand1 (x (-5) 4) (x (-5) 13)
              have b46115 := hb (x (-5) 4)
              have b46116 := hb (x (-5) 4 && x (-5) 13)
              clear * - r46114 b46115 b46116 d46093
              omega
            have d46117 : (x (-5) 4 && x (-5) 8).toNat = 0 := by
              have r46118 := hand1 (x (-5) 4) (x (-5) 8)
              have b46119 := hb (x (-5) 4)
              have b46120 := hb (x (-5) 4 && x (-5) 8)
              clear * - r46118 b46119 b46120 d46093
              omega
            have d46121 : (x (-6) 5).toNat = 0 := by
              have r46122 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46123 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e46124 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e46125 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e46126 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e46127 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e46128 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b46129 := hb (x (-8) 7)
              have b46130 := hb (x (-7) 6)
              have b46131 := hb (x (-6) 5)
              have b46132 := hb (x (-5) 4)
              have b46133 := hb (x (-4) 11)
              have b46134 := hb (x (-3) 10)
              have b46135 := hb (x (-2) 9)
              have b46136 := hb (x (-1) 8)
              clear * - r46122 e46123 e46124 e46125 e46126 e46127 e46128 b46129 b46130 b46131 b46132 b46133 b46134 b46135 b46136 f46036 d46037 d46053 d46073 d46093
              omega
            have d46137 : (x (-6) 5 && x (-6) 14).toNat = 0 := by
              have r46138 := hand1 (x (-6) 5) (x (-6) 14)
              have b46139 := hb (x (-6) 5)
              have b46140 := hb (x (-6) 5 && x (-6) 14)
              clear * - r46138 b46139 b46140 d46121
              omega
            have d46141 : (x (-6) 5 && x (-6) 9).toNat = 0 := by
              have r46142 := hand1 (x (-6) 5) (x (-6) 9)
              have b46143 := hb (x (-6) 5)
              have b46144 := hb (x (-6) 5 && x (-6) 9)
              clear * - r46142 b46143 b46144 d46121
              omega
            have d46145 : (x (-7) 6).toNat = 0 := by
              have r46146 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46147 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e46148 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e46149 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e46150 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e46151 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e46152 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b46153 := hb (x (-8) 7)
              have b46154 := hb (x (-7) 6)
              have b46155 := hb (x (-6) 5)
              have b46156 := hb (x (-5) 4)
              have b46157 := hb (x (-4) 11)
              have b46158 := hb (x (-3) 10)
              have b46159 := hb (x (-2) 9)
              have b46160 := hb (x (-1) 8)
              clear * - r46146 e46147 e46148 e46149 e46150 e46151 e46152 b46153 b46154 b46155 b46156 b46157 b46158 b46159 b46160 f46036 d46037 d46053 d46073 d46093 d46121
              omega
            have d46161 : (x (-7) 6 && x (-7) 10).toNat = 0 := by
              have r46162 := hand1 (x (-7) 6) (x (-7) 10)
              have b46163 := hb (x (-7) 6)
              have b46164 := hb (x (-7) 6 && x (-7) 10)
              clear * - r46162 b46163 b46164 d46145
              omega
            have d46165 : (x (-4) 3 && x (-4) 12).toNat = 1 := by
              have r46166 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b46167 := hb (x (-7) 6)
              have b46168 := hb (x (-1) 9)
              have b46169 := hb (x (-2) 1 && x (-2) 10)
              have b46170 := hb (x (-3) 2 && x (-3) 11)
              have b46171 := hb (x (-4) 3 && x (-4) 12)
              have b46172 := hb (x (-5) 4 && x (-5) 13)
              have b46173 := hb (x (-6) 5 && x (-6) 14)
              clear * - r46166 b46167 b46168 b46169 b46170 b46171 b46172 b46173 d42972 g38 g39 d46113 d46137 d46145
              omega
            have d46174 : (x (-4) 12).toNat = 1 := by
              have r46175 := hand2 (x (-4) 3) (x (-4) 12)
              have b46176 := hb (x (-4) 12)
              have b46177 := hb (x (-4) 3 && x (-4) 12)
              clear * - r46175 b46176 b46177 d46165
              omega
            have d46178 : (x (-5) 13).toNat = 0 := by
              have r46179 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46180 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
              have e46181 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
              have b46182 := hb (x (-7) 3)
              have b46183 := hb (x (-6) 2)
              have b46184 := hb (x (-5) 13)
              have b46185 := hb (x (-4) 12)
              clear * - r46179 e46180 e46181 b46182 b46183 b46184 b46185 d46174
              omega
            have d46186 : (x (-6) 2).toNat = 0 := by
              have r46187 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46188 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
              have e46189 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
              have b46190 := hb (x (-7) 3)
              have b46191 := hb (x (-6) 2)
              have b46192 := hb (x (-5) 13)
              have b46193 := hb (x (-4) 12)
              clear * - r46187 e46188 e46189 b46190 b46191 b46192 b46193 d46174 d46178
              omega
            have d46194 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
              have r46195 := hand1 (x (-6) 2) (x (-6) 13)
              have b46196 := hb (x (-6) 2)
              have b46197 := hb (x (-6) 2 && x (-6) 13)
              clear * - r46195 b46196 b46197 d46186
              omega
            have d46198 : (x (-6) 2 && x (-6) 12).toNat = 0 := by
              have r46199 := hand1 (x (-6) 2) (x (-6) 12)
              have b46200 := hb (x (-6) 2)
              have b46201 := hb (x (-6) 2 && x (-6) 12)
              clear * - r46199 b46200 b46201 d46186
              omega
            have d46202 : (x (-6) 10).toNat = 0 := by
              have r46203 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
              have b46204 := hb (x (-6) 2)
              have b46205 := hb (x (-6) 10)
              clear * - r46203 b46204 b46205 d46186
              omega
            have d46206 : (x (-7) 3).toNat = 0 := by
              have r46207 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46208 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
              have e46209 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
              have b46210 := hb (x (-7) 3)
              have b46211 := hb (x (-6) 2)
              have b46212 := hb (x (-5) 13)
              have b46213 := hb (x (-4) 12)
              clear * - r46207 e46208 e46209 b46210 b46211 b46212 b46213 d46174 d46178 d46186
              omega
            have d46214 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
              have r46215 := hand1 (x (-7) 3) (x (-7) 14)
              have b46216 := hb (x (-7) 3)
              have b46217 := hb (x (-7) 3 && x (-7) 14)
              clear * - r46215 b46216 b46217 d46206
              omega
            have d46218 : (x (-7) 3 && x (-7) 13).toNat = 0 := by
              have r46219 := hand1 (x (-7) 3) (x (-7) 13)
              have b46220 := hb (x (-7) 3)
              have b46221 := hb (x (-7) 3 && x (-7) 13)
              clear * - r46219 b46220 b46221 d46206
              omega
            have d46222 : (x (-7) 11).toNat = 0 := by
              have r46223 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
              have b46224 := hb (x (-7) 3)
              have b46225 := hb (x (-7) 11)
              clear * - r46223 b46224 b46225 d46206
              omega
            have d46226 : (x (-4) 3).toNat = 1 := by
              have r46227 := hand1 (x (-4) 3) (x (-4) 12)
              have b46228 := hb (x (-4) 3)
              have b46229 := hb (x (-4) 3 && x (-4) 12)
              clear * - r46227 b46228 b46229 d46165
              omega
            have d46230 : (x (-1) 12).toNat = 0 := by
              have r46231 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46232 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e46233 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b46234 := hb (x (-4) 3)
              have b46235 := hb (x (-3) 2)
              have b46236 := hb (x (-2) 13)
              have b46237 := hb (x (-1) 12)
              clear * - r46231 e46232 e46233 b46234 b46235 b46236 b46237 d46226
              omega
            have d46238 : (x (-2) 13).toNat = 0 := by
              have r46239 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46240 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e46241 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b46242 := hb (x (-4) 3)
              have b46243 := hb (x (-3) 2)
              have b46244 := hb (x (-2) 13)
              have b46245 := hb (x (-1) 12)
              clear * - r46239 e46240 e46241 b46242 b46243 b46244 b46245 d46230 d46226
              omega
            have d46246 : (x (-3) 2).toNat = 0 := by
              have r46247 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46248 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e46249 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b46250 := hb (x (-4) 3)
              have b46251 := hb (x (-3) 2)
              have b46252 := hb (x (-2) 13)
              have b46253 := hb (x (-1) 12)
              clear * - r46247 e46248 e46249 b46250 b46251 b46252 b46253 d46230 d46238 d46226
              omega
            have d46254 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
              have r46255 := hand1 (x (-3) 2) (x (-3) 12)
              have b46256 := hb (x (-3) 2)
              have b46257 := hb (x (-3) 2 && x (-3) 12)
              clear * - r46255 b46256 b46257 d46246
              omega
            have d46258 : (x (-4) 3 && x (-4) 13).toNat = 1 := by
              have r46259 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b46260 := hb (x (-6) 5)
              have b46261 := hb (x (-1) 10)
              have b46262 := hb (x (-2) 1 && x (-2) 11)
              have b46263 := hb (x (-3) 2 && x (-3) 12)
              have b46264 := hb (x (-4) 3 && x (-4) 13)
              have b46265 := hb (x (-5) 4 && x (-5) 14)
              clear * - r46259 b46260 b46261 b46262 b46263 b46264 b46265 d43045 d43061 d46254 d46109 d46121
              omega
            have d46266 : (x (-4) 13).toNat = 1 := by
              have r46267 := hand2 (x (-4) 3) (x (-4) 13)
              have b46268 := hb (x (-4) 13)
              have b46269 := hb (x (-4) 3 && x (-4) 13)
              clear * - r46267 b46268 b46269 d46258
              omega
            have d46270 : (x (-4) 1).toNat = 1 := by
              have r46271 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
              have b46272 := hb (x (-4) 1)
              have b46273 := hb (x (-4) 13)
              clear * - r46271 b46272 b46273 d46266
              omega
            have d46274 : (x (-3) 14).toNat = 0 := by
              have r46275 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b46276 := hb (x (-4) 1)
              have b46277 := hb (x (-3) 14)
              clear * - r46275 b46276 b46277 d46270
              omega
            have d46278 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
              have r46279 := hand2 (x (-3) 1) (x (-3) 14)
              have b46280 := hb (x (-3) 14)
              have b46281 := hb (x (-3) 1 && x (-3) 14)
              clear * - r46279 b46280 b46281 d46274
              omega
            have d46282 : (x (-4) 2).toNat = 1 := by
              have r46283 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b46284 := hb (x (-4) 2)
              have b46285 := hb (x (-2) 13)
              have b46286 := hb (x (-3) 1 && x (-3) 14)
              clear * - r46283 b46284 b46285 b46286 d46238 d46278
              omega
            have d46287 : (x (-4) 14).toNat = 1 := by
              have r46288 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
              have b46289 := hb (x (-4) 2)
              have b46290 := hb (x (-4) 14)
              clear * - r46288 b46289 b46290 d46282
              omega
            have d46291 : (x (-5) 1).toNat = 0 := by
              have r46292 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b46293 := hb (x (-5) 1)
              have b46294 := hb (x (-4) 14)
              clear * - r46292 b46293 b46294 d46287
              omega
            have d46295 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
              have r46296 := hand1 (x (-5) 1) (x (-5) 12)
              have b46297 := hb (x (-5) 1)
              have b46298 := hb (x (-5) 1 && x (-5) 12)
              clear * - r46296 b46297 b46298 d46291
              omega
            have d46299 : (x (-8) 4).toNat = 1 := by
              have r46300 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b46301 := hb (x (-8) 4)
              have b46302 := hb (x (-4) 11)
              have b46303 := hb (x (-5) 1 && x (-5) 12)
              have b46304 := hb (x (-6) 2 && x (-6) 13)
              have b46305 := hb (x (-7) 3 && x (-7) 14)
              clear * - r46300 b46301 b46302 b46303 b46304 b46305 d46073 d46295 d46194 d46214
              omega
            have d46306 : (x (-8) 12).toNat = 1 := by
              have r46307 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
              have b46308 := hb (x (-8) 4)
              have b46309 := hb (x (-8) 12)
              clear * - r46307 b46308 b46309 d46299
              omega
            have d46310 : (x (-9) 13).toNat = 0 := by
              have r46311 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46312 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
              have e46313 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
              have b46314 := hb (x (-11) 3)
              have b46315 := hb (x (-10) 2)
              have b46316 := hb (x (-9) 13)
              have b46317 := hb (x (-8) 12)
              clear * - r46311 e46312 e46313 b46314 b46315 b46316 b46317 d46306
              omega
            have d46318 : (x (-9) 5).toNat = 0 := by
              have r46319 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
              have b46320 := hb (x (-9) 5)
              have b46321 := hb (x (-9) 13)
              clear * - r46319 b46320 b46321 d46310
              omega
            have d46322 : (x (-10) 2).toNat = 0 := by
              have r46323 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46324 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
              have e46325 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
              have b46326 := hb (x (-11) 3)
              have b46327 := hb (x (-10) 2)
              have b46328 := hb (x (-9) 13)
              have b46329 := hb (x (-8) 12)
              clear * - r46323 e46324 e46325 b46326 b46327 b46328 b46329 d46306 d46310
              omega
            have d46330 : (x (-10) 10).toNat = 0 := by
              have r46331 : (x (-10) 10).toNat ≤ (x (-10) 2).toNat := himp _ _ (hp10 (-10))
              have b46332 := hb (x (-10) 2)
              have b46333 := hb (x (-10) 10)
              clear * - r46331 b46332 b46333 d46322
              omega
            have d46334 : (x (-10) 1 && x (-10) 10).toNat = 0 := by
              have r46335 := hand2 (x (-10) 1) (x (-10) 10)
              have b46336 := hb (x (-10) 10)
              have b46337 := hb (x (-10) 1 && x (-10) 10)
              clear * - r46335 b46336 b46337 d46330
              omega
            have d46338 : (x (-11) 3).toNat = 0 := by
              have r46339 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46340 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
              have e46341 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
              have b46342 := hb (x (-11) 3)
              have b46343 := hb (x (-10) 2)
              have b46344 := hb (x (-9) 13)
              have b46345 := hb (x (-8) 12)
              clear * - r46339 e46340 e46341 b46342 b46343 b46344 b46345 d46306 d46310 d46322
              omega
            have d46346 : (x (-11) 11).toNat = 0 := by
              have r46347 : (x (-11) 11).toNat ≤ (x (-11) 3).toNat := himp _ _ (hp11 (-11))
              have b46348 := hb (x (-11) 3)
              have b46349 := hb (x (-11) 11)
              clear * - r46347 b46348 b46349 d46338
              omega
            have d46350 : (x (-11) 2 && x (-11) 11).toNat = 0 := by
              have r46351 := hand2 (x (-11) 2) (x (-11) 11)
              have b46352 := hb (x (-11) 11)
              have b46353 := hb (x (-11) 2 && x (-11) 11)
              clear * - r46351 b46352 b46353 d46346
              omega
            have d46354 : (x (-5) 1 && x (-5) 11).toNat = 0 := by
              have r46355 := hand1 (x (-5) 1) (x (-5) 11)
              have b46356 := hb (x (-5) 1)
              have b46357 := hb (x (-5) 1 && x (-5) 11)
              clear * - r46355 b46356 b46357 d46291
              omega
            have d46358 : (x (-5) 9).toNat = 0 := by
              have r46359 : (x (-5) 9).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp9 (-5))
              have b46360 := hb (x (-5) 1)
              have b46361 := hb (x (-5) 9)
              clear * - r46359 b46360 b46361 d46291
              omega
            have d46362 : (x (-2) 12).toNat = 0 := by
              have r46363 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46364 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
              have e46365 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
              have b46366 := hb (x (-5) 3)
              have b46367 := hb (x (-4) 2)
              have b46368 := hb (x (-3) 13)
              have b46369 := hb (x (-2) 12)
              clear * - r46363 e46364 e46365 b46366 b46367 b46368 b46369 d46282
              omega
            have d46370 : (x (-3) 13).toNat = 0 := by
              have r46371 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46372 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
              have e46373 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
              have b46374 := hb (x (-5) 3)
              have b46375 := hb (x (-4) 2)
              have b46376 := hb (x (-3) 13)
              have b46377 := hb (x (-2) 12)
              clear * - r46371 e46372 e46373 b46374 b46375 b46376 b46377 d46362 d46282
              omega
            have d46378 : (x (-5) 3).toNat = 0 := by
              have r46379 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46380 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
              have e46381 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
              have b46382 := hb (x (-5) 3)
              have b46383 := hb (x (-4) 2)
              have b46384 := hb (x (-3) 13)
              have b46385 := hb (x (-2) 12)
              clear * - r46379 e46380 e46381 b46382 b46383 b46384 b46385 d46362 d46370 d46282
              omega
            have d46386 : (x (-5) 3 && x (-5) 12).toNat = 0 := by
              have r46387 := hand1 (x (-5) 3) (x (-5) 12)
              have b46388 := hb (x (-5) 3)
              have b46389 := hb (x (-5) 3 && x (-5) 12)
              clear * - r46387 b46388 b46389 d46378
              omega
            have d46390 : (x (-5) 11).toNat = 0 := by
              have r46391 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
              have b46392 := hb (x (-5) 3)
              have b46393 := hb (x (-5) 11)
              clear * - r46391 b46392 b46393 d46378
              omega
            have d46394 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
              have r46395 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b46396 := hb (x (-3) 2)
              have b46397 := hb (x (-1) 13)
              have b46398 := hb (x (-2) 1 && x (-2) 14)
              clear * - r46395 b46396 b46397 b46398 g7 d46246
              omega
            have d46399 : (x (-2) 14).toNat = 1 := by
              have r46400 := hand2 (x (-2) 1) (x (-2) 14)
              have b46401 := hb (x (-2) 14)
              have b46402 := hb (x (-2) 1 && x (-2) 14)
              clear * - r46400 b46401 b46402 d46394
              omega
            have d46403 : (x (-3) 1).toNat = 0 := by
              have r46404 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b46405 := hb (x (-3) 1)
              have b46406 := hb (x (-2) 14)
              clear * - r46404 b46405 b46406 d46399
              omega
            have d46407 : (x (-3) 9).toNat = 0 := by
              have r46408 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
              have b46409 := hb (x (-3) 1)
              have b46410 := hb (x (-3) 9)
              clear * - r46408 b46409 b46410 d46403
              omega
            have d46411 : (x (-8) 7).toNat = 0 := by
              have r46412 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46413 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e46414 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e46415 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e46416 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e46417 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e46418 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b46419 := hb (x (-8) 7)
              have b46420 := hb (x (-7) 6)
              have b46421 := hb (x (-6) 5)
              have b46422 := hb (x (-5) 4)
              have b46423 := hb (x (-4) 11)
              have b46424 := hb (x (-3) 10)
              have b46425 := hb (x (-2) 9)
              have b46426 := hb (x (-1) 8)
              clear * - r46412 e46413 e46414 e46415 e46416 e46417 e46418 b46419 b46420 b46421 b46422 b46423 b46424 b46425 b46426 f46036 d46037 d46053 d46073 d46093 d46121 d46145
              omega
            have d46427 : (x (-8) 7 && x (-8) 11).toNat = 0 := by
              have r46428 := hand1 (x (-8) 7) (x (-8) 11)
              have b46429 := hb (x (-8) 7)
              have b46430 := hb (x (-8) 7 && x (-8) 11)
              clear * - r46428 b46429 b46430 d46411
              omega
            have d46431 : (x (-4) 8).toNat = 0 := by
              have r46432 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46433 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
              have e46434 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
              have e46435 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
              have e46436 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
              have e46437 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
              have e46438 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
              have b46439 := hb (x (-11) 7)
              have b46440 := hb (x (-10) 6)
              have b46441 := hb (x (-9) 5)
              have b46442 := hb (x (-8) 4)
              have b46443 := hb (x (-7) 11)
              have b46444 := hb (x (-6) 10)
              have b46445 := hb (x (-5) 9)
              have b46446 := hb (x (-4) 8)
              clear * - r46432 e46433 e46434 e46435 e46436 e46437 e46438 b46439 b46440 b46441 b46442 b46443 b46444 b46445 b46446 d46358 d46202 d46222 d46299 d46318
              omega
            have d46447 : (x (-10) 14).toNat = 0 := by
              have r46448 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b46449 := hb (x (-10) 14)
              have b46450 := hb (x (-9) 13)
              have b46451 := hb (x (-8) 12)
              have b46452 := hb (x (-7) 11)
              have b46453 := hb (x (-6) 10)
              have b46454 := hb (x (-5) 9)
              have b46455 := hb (x (-4) 8)
              have b46456 := hb (x (-3) 7)
              have b46457 := hb (x (-2) 6)
              have b46458 := hb (x (-1) 5)
              have b46459 := hb (x 0 4)
              have b46460 := hb (x 1 3)
              have b46461 := hb (x 2 2)
              have b46462 := hb (x 3 1)
              clear * - r46448 b46449 b46450 b46451 b46452 b46453 b46454 b46455 b46456 b46457 b46458 b46459 b46460 b46461 b46462 g20 g17 g13 g9 g6 g4 g1 d46431 d46358 d46202 d46222 d46306 d46310
              omega
            have d46463 : (x (-10) 1 && x (-10) 14).toNat = 0 := by
              have r46464 := hand2 (x (-10) 1) (x (-10) 14)
              have b46465 := hb (x (-10) 14)
              have b46466 := hb (x (-10) 1 && x (-10) 14)
              clear * - r46464 b46465 b46466 d46447
              omega
            have d46467 : (x (-11) 2).toNat = 1 := by
              have r46468 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b46469 := hb (x (-11) 2)
              have b46470 := hb (x (-9) 13)
              have b46471 := hb (x (-10) 1 && x (-10) 14)
              clear * - r46468 b46469 b46470 b46471 d46310 d46463
              omega
            have d46472 : (x (-9) 12).toNat = 0 := by
              have r46473 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46474 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
              have e46475 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
              have b46476 := hb (x (-12) 3)
              have b46477 := hb (x (-11) 2)
              have b46478 := hb (x (-10) 13)
              have b46479 := hb (x (-9) 12)
              clear * - r46473 e46474 e46475 b46476 b46477 b46478 b46479 d46467
              omega
            have d46480 : (x (-9) 8 && x (-9) 12).toNat = 0 := by
              have r46481 := hand2 (x (-9) 8) (x (-9) 12)
              have b46482 := hb (x (-9) 12)
              have b46483 := hb (x (-9) 8 && x (-9) 12)
              clear * - r46481 b46482 b46483 d46472
              omega
            have d46484 : (x (-10) 13).toNat = 0 := by
              have r46485 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46486 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
              have e46487 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
              have b46488 := hb (x (-12) 3)
              have b46489 := hb (x (-11) 2)
              have b46490 := hb (x (-10) 13)
              have b46491 := hb (x (-9) 12)
              clear * - r46485 e46486 e46487 b46488 b46489 b46490 b46491 d46472 d46467
              omega
            have d46492 : (x (-10) 9 && x (-10) 13).toNat = 0 := by
              have r46493 := hand2 (x (-10) 9) (x (-10) 13)
              have b46494 := hb (x (-10) 13)
              have b46495 := hb (x (-10) 9 && x (-10) 13)
              clear * - r46493 b46494 b46495 d46484
              omega
            have d46496 : (x (-12) 3).toNat = 0 := by
              have r46497 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46498 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
              have e46499 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
              have b46500 := hb (x (-12) 3)
              have b46501 := hb (x (-11) 2)
              have b46502 := hb (x (-10) 13)
              have b46503 := hb (x (-9) 12)
              clear * - r46497 e46498 e46499 b46500 b46501 b46502 b46503 d46472 d46484 d46467
              omega
            have d46504 : (x (-12) 3 && x (-12) 12).toNat = 0 := by
              have r46505 := hand1 (x (-12) 3) (x (-12) 12)
              have b46506 := hb (x (-12) 3)
              have b46507 := hb (x (-12) 3 && x (-12) 12)
              clear * - r46505 b46506 b46507 d46496
              omega
            have d46508 : (x (-12) 11).toNat = 0 := by
              have r46509 : (x (-12) 11).toNat ≤ (x (-12) 3).toNat := himp _ _ (hp11 (-12))
              have b46510 := hb (x (-12) 3)
              have b46511 := hb (x (-12) 11)
              clear * - r46509 b46510 b46511 d46496
              omega
            have d46512 : (x (-11) 10).toNat = 1 := by
              have r46513 : 1 ≤ (x (-1) 4).toNat + (x (-2) 1 && x (-2) 5).toNat + (x (-3) 2 && x (-3) 6).toNat + (x (-4) 3 && x (-4) 7).toNat + (x (-5) 4 && x (-5) 8).toNat + (x (-6) 5 && x (-6) 9).toNat + (x (-7) 6 && x (-7) 10).toNat + (x (-8) 7 && x (-8) 11).toNat + (x (-9) 8 && x (-9) 12).toNat + (x (-10) 9 && x (-10) 13).toNat + (x (-11) 10 && x (-11) 14).toNat + (x (-12) 11).toNat := by have q := hcov4 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46514 : (x (-2) 1 && x (-2) 5).toNat = (x (-2) 5).toNat := handr _ _ (fun h => hp13 (-2) (hp5 (-2) (h)))
              have e46515 : (x (-11) 10 && x (-11) 14).toNat = (x (-11) 10).toNat := handl _ _ (fun h => hp2 (-11) (hp10 (-11) (h)))
              have b46516 := hb (x (-12) 11)
              have b46517 := hb (x (-11) 10)
              have b46518 := hb (x (-2) 5)
              have b46519 := hb (x (-1) 4)
              have b46520 := hb (x (-3) 2 && x (-3) 6)
              have b46521 := hb (x (-4) 3 && x (-4) 7)
              have b46522 := hb (x (-5) 4 && x (-5) 8)
              have b46523 := hb (x (-6) 5 && x (-6) 9)
              have b46524 := hb (x (-7) 6 && x (-7) 10)
              have b46525 := hb (x (-8) 7 && x (-8) 11)
              have b46526 := hb (x (-9) 8 && x (-9) 12)
              have b46527 := hb (x (-10) 9 && x (-10) 13)
              clear * - r46513 e46514 e46515 b46516 b46517 b46518 b46519 b46520 b46521 b46522 b46523 b46524 b46525 b46526 b46527 d43644 d43660 d43692 d43712 d46117 d46141 d46161 d46427 d46480 d46492 d46508
              omega
            have d46528 : (x (-9) 8).toNat = 0 := by
              have r46529 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46530 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
              have e46531 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
              have e46532 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
              have e46533 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
              have e46534 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
              have e46535 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
              have b46536 := hb (x (-16) 7)
              have b46537 := hb (x (-15) 6)
              have b46538 := hb (x (-14) 5)
              have b46539 := hb (x (-13) 4)
              have b46540 := hb (x (-12) 11)
              have b46541 := hb (x (-11) 10)
              have b46542 := hb (x (-10) 9)
              have b46543 := hb (x (-9) 8)
              clear * - r46529 e46530 e46531 e46532 e46533 e46534 e46535 b46536 b46537 b46538 b46539 b46540 b46541 b46542 b46543 d46512 d46508
              omega
            have d46544 : (x (-10) 9).toNat = 0 := by
              have r46545 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46546 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
              have e46547 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
              have e46548 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
              have e46549 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
              have e46550 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
              have e46551 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
              have b46552 := hb (x (-16) 7)
              have b46553 := hb (x (-15) 6)
              have b46554 := hb (x (-14) 5)
              have b46555 := hb (x (-13) 4)
              have b46556 := hb (x (-12) 11)
              have b46557 := hb (x (-11) 10)
              have b46558 := hb (x (-10) 9)
              have b46559 := hb (x (-9) 8)
              clear * - r46545 e46546 e46547 e46548 e46549 e46550 e46551 b46552 b46553 b46554 b46555 b46556 b46557 b46558 b46559 d46528 d46512 d46508
              omega
            have d46560 : (x (-13) 4).toNat = 0 := by
              have r46561 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46562 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
              have e46563 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
              have e46564 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
              have e46565 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
              have e46566 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
              have e46567 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
              have b46568 := hb (x (-16) 7)
              have b46569 := hb (x (-15) 6)
              have b46570 := hb (x (-14) 5)
              have b46571 := hb (x (-13) 4)
              have b46572 := hb (x (-12) 11)
              have b46573 := hb (x (-11) 10)
              have b46574 := hb (x (-10) 9)
              have b46575 := hb (x (-9) 8)
              clear * - r46561 e46562 e46563 e46564 e46565 e46566 e46567 b46568 b46569 b46570 b46571 b46572 b46573 b46574 b46575 d46528 d46544 d46512 d46508
              omega
            have d46576 : (x (-13) 4 && x (-13) 13).toNat = 0 := by
              have r46577 := hand1 (x (-13) 4) (x (-13) 13)
              have b46578 := hb (x (-13) 4)
              have b46579 := hb (x (-13) 4 && x (-13) 13)
              clear * - r46577 b46578 b46579 d46560
              omega
            have d46580 : (x (-14) 5).toNat = 0 := by
              have r46581 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46582 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
              have e46583 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
              have e46584 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
              have e46585 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
              have e46586 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
              have e46587 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
              have b46588 := hb (x (-16) 7)
              have b46589 := hb (x (-15) 6)
              have b46590 := hb (x (-14) 5)
              have b46591 := hb (x (-13) 4)
              have b46592 := hb (x (-12) 11)
              have b46593 := hb (x (-11) 10)
              have b46594 := hb (x (-10) 9)
              have b46595 := hb (x (-9) 8)
              clear * - r46581 e46582 e46583 e46584 e46585 e46586 e46587 b46588 b46589 b46590 b46591 b46592 b46593 b46594 b46595 d46528 d46544 d46512 d46508 d46560
              omega
            have d46596 : (x (-14) 5 && x (-14) 14).toNat = 0 := by
              have r46597 := hand1 (x (-14) 5) (x (-14) 14)
              have b46598 := hb (x (-14) 5)
              have b46599 := hb (x (-14) 5 && x (-14) 14)
              clear * - r46597 b46598 b46599 d46580
              omega
            have d46600 : (x (-15) 6).toNat = 0 := by
              have r46601 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46602 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
              have e46603 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
              have e46604 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
              have e46605 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
              have e46606 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
              have e46607 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
              have b46608 := hb (x (-16) 7)
              have b46609 := hb (x (-15) 6)
              have b46610 := hb (x (-14) 5)
              have b46611 := hb (x (-13) 4)
              have b46612 := hb (x (-12) 11)
              have b46613 := hb (x (-11) 10)
              have b46614 := hb (x (-10) 9)
              have b46615 := hb (x (-9) 8)
              clear * - r46601 e46602 e46603 e46604 e46605 e46606 e46607 b46608 b46609 b46610 b46611 b46612 b46613 b46614 b46615 d46528 d46544 d46512 d46508 d46560 d46580
              omega
            have d46616 : (x (-9) 9).toNat = 1 := by
              have r46617 : 1 ≤ (x (-9) 9).toNat + (x (-10) 1 && x (-10) 10).toNat + (x (-11) 2 && x (-11) 11).toNat + (x (-12) 3 && x (-12) 12).toNat + (x (-13) 4 && x (-13) 13).toNat + (x (-14) 5 && x (-14) 14).toNat + (x (-15) 6).toNat := by have q := hcov9 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b46618 := hb (x (-15) 6)
              have b46619 := hb (x (-9) 9)
              have b46620 := hb (x (-10) 1 && x (-10) 10)
              have b46621 := hb (x (-11) 2 && x (-11) 11)
              have b46622 := hb (x (-12) 3 && x (-12) 12)
              have b46623 := hb (x (-13) 4 && x (-13) 13)
              have b46624 := hb (x (-14) 5 && x (-14) 14)
              clear * - r46617 b46618 b46619 b46620 b46621 b46622 b46623 b46624 d46334 d46350 d46504 d46576 d46596 d46600
              omega
            have d46625 : (x (-9) 1).toNat = 1 := by
              have r46626 : (x (-9) 9).toNat ≤ (x (-9) 1).toNat := himp _ _ (hp9 (-9))
              have b46627 := hb (x (-9) 1)
              have b46628 := hb (x (-9) 9)
              clear * - r46626 b46627 b46628 d46616
              omega
            have d46629 : (x (-8) 14).toNat = 0 := by
              have r46630 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b46631 := hb (x (-9) 1)
              have b46632 := hb (x (-8) 14)
              clear * - r46630 b46631 b46632 d46625
              omega
            have d46633 : (x (-8) 4 && x (-8) 14).toNat = 0 := by
              have r46634 := hand2 (x (-8) 4) (x (-8) 14)
              have b46635 := hb (x (-8) 14)
              have b46636 := hb (x (-8) 4 && x (-8) 14)
              clear * - r46634 b46635 b46636 d46629
              omega
            have d46637 : (x (-4) 10).toNat = 1 := by
              have r46638 : 1 ≤ (x (-4) 10).toNat + (x (-5) 1 && x (-5) 11).toNat + (x (-6) 2 && x (-6) 12).toNat + (x (-7) 3 && x (-7) 13).toNat + (x (-8) 4 && x (-8) 14).toNat + (x (-9) 5).toNat := by have q := hcov10 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b46639 := hb (x (-9) 5)
              have b46640 := hb (x (-4) 10)
              have b46641 := hb (x (-5) 1 && x (-5) 11)
              have b46642 := hb (x (-6) 2 && x (-6) 12)
              have b46643 := hb (x (-7) 3 && x (-7) 13)
              have b46644 := hb (x (-8) 4 && x (-8) 14)
              clear * - r46638 b46639 b46640 b46641 b46642 b46643 b46644 d46354 d46198 d46218 d46633 d46318
              omega
            have d46645 : (x (-2) 8).toNat = 0 := by
              have r46646 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46647 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
              have e46648 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
              have e46649 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
              have e46650 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
              have e46651 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
              have e46652 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
              have b46653 := hb (x (-9) 7)
              have b46654 := hb (x (-8) 6)
              have b46655 := hb (x (-7) 5)
              have b46656 := hb (x (-6) 4)
              have b46657 := hb (x (-5) 11)
              have b46658 := hb (x (-4) 10)
              have b46659 := hb (x (-3) 9)
              have b46660 := hb (x (-2) 8)
              clear * - r46646 e46647 e46648 e46649 e46650 e46651 e46652 b46653 b46654 b46655 b46656 b46657 b46658 b46659 b46660 d46407 d46637 d46390
              omega
            have d46661 : (x (-6) 4).toNat = 0 := by
              have r46662 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46663 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
              have e46664 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
              have e46665 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
              have e46666 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
              have e46667 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
              have e46668 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
              have b46669 := hb (x (-9) 7)
              have b46670 := hb (x (-8) 6)
              have b46671 := hb (x (-7) 5)
              have b46672 := hb (x (-6) 4)
              have b46673 := hb (x (-5) 11)
              have b46674 := hb (x (-4) 10)
              have b46675 := hb (x (-3) 9)
              have b46676 := hb (x (-2) 8)
              clear * - r46662 e46663 e46664 e46665 e46666 e46667 e46668 b46669 b46670 b46671 b46672 b46673 b46674 b46675 b46676 d46645 d46407 d46637 d46390
              omega
            have d46677 : (x (-6) 4 && x (-6) 13).toNat = 0 := by
              have r46678 := hand1 (x (-6) 4) (x (-6) 13)
              have b46679 := hb (x (-6) 4)
              have b46680 := hb (x (-6) 4 && x (-6) 13)
              clear * - r46678 b46679 b46680 d46661
              omega
            have d46681 : (x (-7) 5).toNat = 0 := by
              have r46682 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e46683 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
              have e46684 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
              have e46685 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
              have e46686 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
              have e46687 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
              have e46688 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
              have b46689 := hb (x (-9) 7)
              have b46690 := hb (x (-8) 6)
              have b46691 := hb (x (-7) 5)
              have b46692 := hb (x (-6) 4)
              have b46693 := hb (x (-5) 11)
              have b46694 := hb (x (-4) 10)
              have b46695 := hb (x (-3) 9)
              have b46696 := hb (x (-2) 8)
              clear * - r46682 e46683 e46684 e46685 e46686 e46687 e46688 b46689 b46690 b46691 b46692 b46693 b46694 b46695 b46696 d46645 d46407 d46637 d46390 d46661
              omega
            have d46697 : (x (-7) 5 && x (-7) 14).toNat = 0 := by
              have r46698 := hand1 (x (-7) 5) (x (-7) 14)
              have b46699 := hb (x (-7) 5)
              have b46700 := hb (x (-7) 5 && x (-7) 14)
              clear * - r46698 b46699 b46700 d46681
              omega
            have d46701 : (x (-8) 6).toNat = 1 := by
              have r46702 : 1 ≤ (x (-2) 9).toNat + (x (-3) 1 && x (-3) 10).toNat + (x (-4) 2 && x (-4) 11).toNat + (x (-5) 3 && x (-5) 12).toNat + (x (-6) 4 && x (-6) 13).toNat + (x (-7) 5 && x (-7) 14).toNat + (x (-8) 6).toNat := by have q := hcov9 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b46703 := hb (x (-8) 6)
              have b46704 := hb (x (-2) 9)
              have b46705 := hb (x (-3) 1 && x (-3) 10)
              have b46706 := hb (x (-4) 2 && x (-4) 11)
              have b46707 := hb (x (-5) 3 && x (-5) 12)
              have b46708 := hb (x (-6) 4 && x (-6) 13)
              have b46709 := hb (x (-7) 5 && x (-7) 14)
              clear * - r46702 b46703 b46704 b46705 b46706 b46707 b46708 b46709 d46037 d46069 d46089 d46386 d46677 d46697
              omega
            have r46710 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e46711 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
            have e46712 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
            have e46713 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
            have e46714 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
            have e46715 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
            have e46716 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
            have b46717 := hb (x (-9) 7)
            have b46718 := hb (x (-8) 6)
            have b46719 := hb (x (-7) 5)
            have b46720 := hb (x (-6) 4)
            have b46721 := hb (x (-5) 11)
            have b46722 := hb (x (-4) 10)
            have b46723 := hb (x (-3) 9)
            have b46724 := hb (x (-2) 8)
            linarith only [r46710, e46711, e46712, e46713, e46714, e46715, e46716, b46717, b46718, b46719, b46720, b46721, b46722, b46723, b46724, d46645, d46407, d46637, d46390, d46661, d46681, d46701]
        · have f46725 : (x 1 7).toNat = 1 := by rw [h43981]; rfl
          have d46726 : (x 8 8).toNat = 0 := by
            have r46727 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e46728 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e46729 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e46730 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e46731 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e46732 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e46733 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have b46734 := hb (x 1 7)
            have b46735 := hb (x 2 6)
            have b46736 := hb (x 3 5)
            have b46737 := hb (x 4 4)
            have b46738 := hb (x 5 11)
            have b46739 := hb (x 6 10)
            have b46740 := hb (x 7 9)
            have b46741 := hb (x 8 8)
            clear * - r46727 e46728 e46729 e46730 e46731 e46732 e46733 b46734 b46735 b46736 b46737 b46738 b46739 b46740 b46741 g23 g18 f46725
            omega
          have d46742 : (x 7 9).toNat = 0 := by
            have r46743 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e46744 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e46745 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e46746 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e46747 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e46748 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e46749 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have b46750 := hb (x 1 7)
            have b46751 := hb (x 2 6)
            have b46752 := hb (x 3 5)
            have b46753 := hb (x 4 4)
            have b46754 := hb (x 5 11)
            have b46755 := hb (x 6 10)
            have b46756 := hb (x 7 9)
            have b46757 := hb (x 8 8)
            clear * - r46743 e46744 e46745 e46746 e46747 e46748 e46749 b46750 b46751 b46752 b46753 b46754 b46755 b46756 b46757 d46726 g23 g18 f46725
            omega
          have d46758 : (x 6 10).toNat = 0 := by
            have r46759 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e46760 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e46761 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e46762 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e46763 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e46764 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e46765 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have b46766 := hb (x 1 7)
            have b46767 := hb (x 2 6)
            have b46768 := hb (x 3 5)
            have b46769 := hb (x 4 4)
            have b46770 := hb (x 5 11)
            have b46771 := hb (x 6 10)
            have b46772 := hb (x 7 9)
            have b46773 := hb (x 8 8)
            clear * - r46759 e46760 e46761 e46762 e46763 e46764 e46765 b46766 b46767 b46768 b46769 b46770 b46771 b46772 b46773 d46726 d46742 g23 g18 f46725
            omega
          have d46774 : (x 6 1 && x 6 10).toNat = 0 := by
            have r46775 := hand2 (x 6 1) (x 6 10)
            have b46776 := hb (x 6 10)
            have b46777 := hb (x 6 1 && x 6 10)
            clear * - r46775 b46776 b46777 d46758
            omega
          have d46778 : (x 5 2 && x 5 11).toNat = 1 := by
            have r46779 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b46780 := hb (x 1 6)
            have b46781 := hb (x 7 9)
            have b46782 := hb (x 6 1 && x 6 10)
            have b46783 := hb (x 5 2 && x 5 11)
            have b46784 := hb (x 4 3 && x 4 12)
            have b46785 := hb (x 3 4 && x 3 13)
            have b46786 := hb (x 2 5 && x 2 14)
            clear * - r46779 b46780 b46781 b46782 b46783 b46784 b46785 b46786 d46742 d46774 g44 d42555 g45 g14
            omega
          have d46787 : (x 5 11).toNat = 1 := by
            have r46788 := hand2 (x 5 2) (x 5 11)
            have b46789 := hb (x 5 11)
            have b46790 := hb (x 5 2 && x 5 11)
            clear * - r46788 b46789 b46790 d46778
            omega
          have r46791 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e46792 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e46793 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e46794 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e46795 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e46796 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e46797 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have b46798 := hb (x 1 7)
          have b46799 := hb (x 2 6)
          have b46800 := hb (x 3 5)
          have b46801 := hb (x 4 4)
          have b46802 := hb (x 5 11)
          have b46803 := hb (x 6 10)
          have b46804 := hb (x 7 9)
          have b46805 := hb (x 8 8)
          linarith only [r46791, e46792, e46793, e46794, e46795, e46796, e46797, b46798, b46799, b46800, b46801, b46802, b46803, b46804, b46805, d46726, d46742, d46758, d46787, g23, g18, f46725]

theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt1111 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 3).toNat = 0)
    (g1 : (x (-3) 7).toNat = 0)
    (g2 : (x (-3) 11).toNat = 0)
    (g3 : (x (-2) 2).toNat = 0)
    (g4 : (x (-2) 6).toNat = 0)
    (g5 : (x (-2) 10).toNat = 0)
    (g6 : (x (-1) 5).toNat = 0)
    (g7 : (x (-1) 13).toNat = 0)
    (g8 : (x 0 1).toNat = 1)
    (g9 : (x 0 4).toNat = 1)
    (g10 : (x 0 7).toNat = 1)
    (g11 : (x 1 1).toNat = 1)
    (g12 : (x 1 2).toNat = 0)
    (g13 : (x 1 3).toNat = 0)
    (g14 : (x 1 6).toNat = 0)
    (g15 : (x 1 10).toNat = 0)
    (g16 : (x 1 14).toNat = 0)
    (g17 : (x 2 2).toNat = 0)
    (g18 : (x 2 6).toNat = 0)
    (g19 : (x 2 14).toNat = 0)
    (g20 : (x 3 1).toNat = 1)
    (g21 : (x 3 13).toNat = 1)
    (g22 : (x 4 2).toNat = 0)
    (g23 : (x 4 4).toNat = 0)
    (g24 : (x 4 10).toNat = 0)
    (g25 : (x 4 12).toNat = 0)
    (g26 : (x (-3) 1 && x (-3) 3).toNat = 0)
    (g27 : (x 2 2 && x 2 6).toNat = 0)
    (g28 : (x 1 3 && x 1 7).toNat = 0)
    (g29 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g30 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g31 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g32 : (x 4 7 && x 4 12).toNat = 0)
    (g33 : (x 2 9 && x 2 14).toNat = 0)
    (g34 : (x (-2) 4 && x (-2) 10).toNat = 0)
    (g35 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g36 : (x 4 5 && x 4 12).toNat = 0)
    (g37 : (x 2 7 && x 2 14).toNat = 0)
    (g38 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g39 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g40 : (x (-2) 2 && x (-2) 11).toNat = 0)
    (g41 : (x (-3) 3 && x (-3) 12).toNat = 0)
    (g42 : (x 4 2 && x 4 11).toNat = 0)
    (g43 : (x 1 5 && x 1 14).toNat = 0)
    (g44 : (x 4 3 && x 4 12).toNat = 0)
    (g45 : (x 2 5 && x 2 14).toNat = 0)
    (g46 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g47 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g48 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g49 : (x 1 4 && x 1 14).toNat = 0)
    (g50 : (x (-2) 2 && x (-2) 13).toNat = 0)
    (g51 : (x (-3) 3 && x (-3) 14).toNat = 0)
    (g52 : (x 4 1 && x 4 12).toNat = 0)
    (g53 : (x 2 3 && x 2 14).toNat = 0)
    (g54 : (x 4 2 && x 4 13).toNat = 0)
    (g55 : (x 1 1 && x 1 14).toNat = 0)
    (g56 : (x 4 1 && x 4 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt1111_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56
