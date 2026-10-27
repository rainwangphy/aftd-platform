import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b011

Topic: combinatorics   Node: 1794bc8c1861

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core: under the layer-free tight-cover constraints for k = 15 and 88 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b011_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-4) 7).toNat = 0)
    (g1 : (x (-3) 6).toNat = 0)
    (g2 : (x (-3) 7).toNat = 0)
    (g3 : (x (-3) 11).toNat = 0)
    (g4 : (x (-2) 2).toNat = 0)
    (g5 : (x (-2) 5).toNat = 0)
    (g6 : (x (-2) 6).toNat = 0)
    (g7 : (x (-2) 10).toNat = 0)
    (g8 : (x (-1) 4).toNat = 0)
    (g9 : (x (-1) 5).toNat = 0)
    (g10 : (x (-1) 13).toNat = 0)
    (g11 : (x 0 1).toNat = 1)
    (g12 : (x 0 3).toNat = 1)
    (g13 : (x 0 4).toNat = 1)
    (g14 : (x 0 5).toNat = 0)
    (g15 : (x 0 10).toNat = 0)
    (g16 : (x 0 11).toNat = 1)
    (g17 : (x 1 2).toNat = 0)
    (g18 : (x 1 10).toNat = 0)
    (g19 : (x 1 11).toNat = 0)
    (g20 : (x 2 5).toNat = 0)
    (g21 : (x 2 9).toNat = 0)
    (g22 : (x 2 10).toNat = 0)
    (g23 : (x 2 13).toNat = 0)
    (g24 : (x 3 4).toNat = 0)
    (g25 : (x 3 8).toNat = 0)
    (g26 : (x 1 2 && x 1 5).toNat = 0)
    (g27 : (x (-1) 4 && x (-1) 7).toNat = 0)
    (g28 : (x (-2) 5 && x (-2) 8).toNat = 0)
    (g29 : (x (-3) 6 && x (-3) 9).toNat = 0)
    (g30 : (x (-4) 7 && x (-4) 10).toNat = 0)
    (g31 : (x 1 2 && x 1 6).toNat = 0)
    (g32 : (x (-1) 4 && x (-1) 8).toNat = 0)
    (g33 : (x (-2) 5 && x (-2) 9).toNat = 0)
    (g34 : (x (-3) 6 && x (-3) 10).toNat = 0)
    (g35 : (x (-4) 7 && x (-4) 11).toNat = 0)
    (g36 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g37 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g38 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g39 : (x 3 4 && x 3 8).toNat = 0)
    (g40 : (x 2 5 && x 2 9).toNat = 0)
    (g41 : (x 1 6 && x 1 10).toNat = 0)
    (g42 : (x 4 4 && x 4 8).toNat = 0)
    (g43 : (x 3 5 && x 3 9).toNat = 0)
    (g44 : (x 2 6 && x 2 10).toNat = 0)
    (g45 : (x 1 7 && x 1 11).toNat = 0)
    (g46 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g47 : (x 4 8 && x 4 12).toNat = 0)
    (g48 : (x 3 9 && x 3 13).toNat = 0)
    (g49 : (x (-3) 1 && x (-3) 6).toNat = 0)
    (g50 : (x (-4) 2 && x (-4) 7).toNat = 0)
    (g51 : (x (-2) 1 && x (-2) 6).toNat = 0)
    (g52 : (x (-3) 2 && x (-3) 7).toNat = 0)
    (g53 : (x 4 3 && x 4 8).toNat = 0)
    (g54 : (x 3 4 && x 3 9).toNat = 0)
    (g55 : (x 2 5 && x 2 10).toNat = 0)
    (g56 : (x 1 6 && x 1 11).toNat = 0)
    (g57 : (x (-1) 8 && x (-1) 13).toNat = 0)
    (g58 : (x 3 8 && x 3 13).toNat = 0)
    (g59 : (x 2 9 && x 2 14).toNat = 0)
    (g60 : (x (-3) 1 && x (-3) 7).toNat = 0)
    (g61 : (x (-2) 4 && x (-2) 10).toNat = 0)
    (g62 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g63 : (x 4 2 && x 4 8).toNat = 0)
    (g64 : (x 3 3 && x 3 9).toNat = 0)
    (g65 : (x 2 4 && x 2 10).toNat = 0)
    (g66 : (x 1 5 && x 1 11).toNat = 0)
    (g67 : (x (-1) 7 && x (-1) 13).toNat = 0)
    (g68 : (x 3 4 && x 3 10).toNat = 0)
    (g69 : (x 2 5 && x 2 11).toNat = 0)
    (g70 : (x (-2) 3 && x (-2) 10).toNat = 0)
    (g71 : (x (-3) 4 && x (-3) 11).toNat = 0)
    (g72 : (x 3 5 && x 3 12).toNat = 0)
    (g73 : (x 2 6 && x 2 13).toNat = 0)
    (g74 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g75 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g76 : (x (-2) 2 && x (-2) 11).toNat = 0)
    (g77 : (x (-3) 3 && x (-3) 12).toNat = 0)
    (g78 : (x 0 1 && x 0 10).toNat = 0)
    (g79 : (x 0 5 && x 0 14).toNat = 0)
    (g80 : (x 3 3 && x 3 12).toNat = 0)
    (g81 : (x 2 4 && x 2 13).toNat = 0)
    (g82 : (x 3 4 && x 3 13).toNat = 0)
    (g83 : (x 2 5 && x 2 14).toNat = 0)
    (g84 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g85 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g86 : (x 3 2 && x 3 12).toNat = 0)
    (g87 : (x 2 3 && x 2 13).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d12402 : (x 1 14).toNat = 0 := by
    have r12403 : (x 1 14).toNat + (x 0 1).toNat = 1 := by have q := hd14 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12404 := hb (x 0 1)
    have b12405 := hb (x 1 14)
    clear * - r12403 b12404 b12405 g11
    omega
  have d12406 : (x 1 1 && x 1 14).toNat = 0 := by
    have r12407 := hand2 (x 1 1) (x 1 14)
    have b12408 := hb (x 1 14)
    have b12409 := hb (x 1 1 && x 1 14)
    clear * - r12407 b12408 b12409 d12402
    omega
  have d12410 : (x 1 4 && x 1 14).toNat = 0 := by
    have r12411 := hand2 (x 1 4) (x 1 14)
    have b12412 := hb (x 1 14)
    have b12413 := hb (x 1 4 && x 1 14)
    clear * - r12411 b12412 b12413 d12402
    omega
  have d12414 : (x 1 5 && x 1 14).toNat = 0 := by
    have r12415 := hand2 (x 1 5) (x 1 14)
    have b12416 := hb (x 1 14)
    have b12417 := hb (x 1 5 && x 1 14)
    clear * - r12415 b12416 b12417 d12402
    omega
  have d12418 : (x 1 7 && x 1 14).toNat = 0 := by
    have r12419 := hand2 (x 1 7) (x 1 14)
    have b12420 := hb (x 1 14)
    have b12421 := hb (x 1 7 && x 1 14)
    clear * - r12419 b12420 b12421 d12402
    omega
  have d12422 : (x 1 6).toNat = 0 := by
    have r12423 : (x 1 6).toNat ≤ (x 1 14).toNat := himp _ _ (hp6 1)
    have b12424 := hb (x 1 6)
    have b12425 := hb (x 1 14)
    clear * - r12423 b12424 b12425 d12402
    omega
  have d12426 : (x 1 6 && x 1 12).toNat = 0 := by
    have r12427 := hand1 (x 1 6) (x 1 12)
    have b12428 := hb (x 1 6)
    have b12429 := hb (x 1 6 && x 1 12)
    clear * - r12427 b12428 b12429 d12422
    omega
  have d12430 : (x 0 2).toNat = 1 := by
    have r12431 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12432 := hb (x 0 2)
    have b12433 := hb (x 2 13)
    have b12434 := hb (x 1 1 && x 1 14)
    clear * - r12431 b12432 b12433 b12434 g23 d12406
    omega
  have d12435 : (x 0 14).toNat = 1 := by
    have r12436 : (x 0 2).toNat ≤ (x 0 14).toNat := himp _ _ (hp2 0)
    have b12437 := hb (x 0 2)
    have b12438 := hb (x 0 14)
    clear * - r12436 b12437 b12438 d12430
    omega
  have d12439 : (x (-1) 1).toNat = 0 := by
    have r12440 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12441 := hb (x (-1) 1)
    have b12442 := hb (x 0 14)
    clear * - r12440 b12441 b12442 d12435
    omega
  have d12443 : (x (-1) 1 && x (-1) 14).toNat = 0 := by
    have r12444 := hand1 (x (-1) 1) (x (-1) 14)
    have b12445 := hb (x (-1) 1)
    have b12446 := hb (x (-1) 1 && x (-1) 14)
    clear * - r12444 b12445 b12446 d12439
    omega
  have d12447 : (x (-1) 1 && x (-1) 11).toNat = 0 := by
    have r12448 := hand1 (x (-1) 1) (x (-1) 11)
    have b12449 := hb (x (-1) 1)
    have b12450 := hb (x (-1) 1 && x (-1) 11)
    clear * - r12448 b12449 b12450 d12439
    omega
  have d12451 : (x (-1) 1 && x (-1) 10).toNat = 0 := by
    have r12452 := hand1 (x (-1) 1) (x (-1) 10)
    have b12453 := hb (x (-1) 1)
    have b12454 := hb (x (-1) 1 && x (-1) 10)
    clear * - r12452 b12453 b12454 d12439
    omega
  have d12455 : (x (-1) 9).toNat = 0 := by
    have r12456 : (x (-1) 9).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp9 (-1))
    have b12457 := hb (x (-1) 1)
    have b12458 := hb (x (-1) 9)
    clear * - r12456 b12457 b12458 d12439
    omega
  have d12459 : (x (-1) 2 && x (-1) 9).toNat = 0 := by
    have r12460 := hand2 (x (-1) 2) (x (-1) 9)
    have b12461 := hb (x (-1) 9)
    have b12462 := hb (x (-1) 2 && x (-1) 9)
    clear * - r12460 b12461 b12462 d12455
    omega
  have d12463 : (x (-1) 3 && x (-1) 9).toNat = 0 := by
    have r12464 := hand2 (x (-1) 3) (x (-1) 9)
    have b12465 := hb (x (-1) 9)
    have b12466 := hb (x (-1) 3 && x (-1) 9)
    clear * - r12464 b12465 b12466 d12455
    omega
  have d12467 : (x 0 13).toNat = 1 := by
    have r12468 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12469 := hb (x (-2) 2)
    have b12470 := hb (x 0 13)
    have b12471 := hb (x (-1) 1 && x (-1) 14)
    clear * - r12468 b12469 b12470 b12471 d12443 g4
    omega
  have d12472 : (x 2 12).toNat = 0 := by
    have r12473 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12474 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e12475 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b12476 := hb (x (-1) 3)
    have b12477 := hb (x 0 2)
    have b12478 := hb (x 1 13)
    have b12479 := hb (x 2 12)
    clear * - r12473 e12474 e12475 b12476 b12477 b12478 b12479 d12430
    omega
  have d12480 : (x 2 3 && x 2 12).toNat = 0 := by
    have r12481 := hand2 (x 2 3) (x 2 12)
    have b12482 := hb (x 2 12)
    have b12483 := hb (x 2 3 && x 2 12)
    clear * - r12481 b12482 b12483 d12472
    omega
  have d12484 : (x 2 8 && x 2 12).toNat = 0 := by
    have r12485 := hand2 (x 2 8) (x 2 12)
    have b12486 := hb (x 2 12)
    have b12487 := hb (x 2 8 && x 2 12)
    clear * - r12485 b12486 b12487 d12472
    omega
  have d12488 : (x 2 4).toNat = 0 := by
    have r12489 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
    have b12490 := hb (x 2 4)
    have b12491 := hb (x 2 12)
    clear * - r12489 b12490 b12491 d12472
    omega
  have d12492 : (x 2 4 && x 2 14).toNat = 0 := by
    have r12493 := hand1 (x 2 4) (x 2 14)
    have b12494 := hb (x 2 4)
    have b12495 := hb (x 2 4 && x 2 14)
    clear * - r12493 b12494 b12495 d12488
    omega
  have d12496 : (x 2 1 && x 2 4).toNat = 0 := by
    have r12497 := hand2 (x 2 1) (x 2 4)
    have b12498 := hb (x 2 4)
    have b12499 := hb (x 2 1 && x 2 4)
    clear * - r12497 b12498 b12499 d12488
    omega
  have d12500 : (x 1 13).toNat = 0 := by
    have r12501 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12502 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e12503 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b12504 := hb (x (-1) 3)
    have b12505 := hb (x 0 2)
    have b12506 := hb (x 1 13)
    have b12507 := hb (x 2 12)
    clear * - r12501 e12502 e12503 b12504 b12505 b12506 b12507 d12472 d12430
    omega
  have d12508 : (x 1 4 && x 1 13).toNat = 0 := by
    have r12509 := hand2 (x 1 4) (x 1 13)
    have b12510 := hb (x 1 13)
    have b12511 := hb (x 1 4 && x 1 13)
    clear * - r12509 b12510 b12511 d12500
    omega
  have d12512 : (x 1 9 && x 1 13).toNat = 0 := by
    have r12513 := hand2 (x 1 9) (x 1 13)
    have b12514 := hb (x 1 13)
    have b12515 := hb (x 1 9 && x 1 13)
    clear * - r12513 b12514 b12515 d12500
    omega
  have d12516 : (x 1 5).toNat = 0 := by
    have r12517 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
    have b12518 := hb (x 1 5)
    have b12519 := hb (x 1 13)
    clear * - r12517 b12518 b12519 d12500
    omega
  have d12520 : (x (-1) 3).toNat = 0 := by
    have r12521 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12522 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e12523 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b12524 := hb (x (-1) 3)
    have b12525 := hb (x 0 2)
    have b12526 := hb (x 1 13)
    have b12527 := hb (x 2 12)
    clear * - r12521 e12522 e12523 b12524 b12525 b12526 b12527 d12472 d12500 d12430
    omega
  have d12528 : (x (-1) 3 && x (-1) 7).toNat = 0 := by
    have r12529 := hand1 (x (-1) 3) (x (-1) 7)
    have b12530 := hb (x (-1) 3)
    have b12531 := hb (x (-1) 3 && x (-1) 7)
    clear * - r12529 b12530 b12531 d12520
    omega
  have d12532 : (x (-1) 11).toNat = 0 := by
    have r12533 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
    have b12534 := hb (x (-1) 3)
    have b12535 := hb (x (-1) 11)
    clear * - r12533 b12534 b12535 d12520
    omega
  have d12536 : (x (-1) 2 && x (-1) 11).toNat = 0 := by
    have r12537 := hand2 (x (-1) 2) (x (-1) 11)
    have b12538 := hb (x (-1) 11)
    have b12539 := hb (x (-1) 2 && x (-1) 11)
    clear * - r12537 b12538 b12539 d12532
    omega
  have d12540 : (x 1 12).toNat = 0 := by
    have r12541 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12542 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e12543 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b12544 := hb (x (-2) 3)
    have b12545 := hb (x (-1) 2)
    have b12546 := hb (x 0 13)
    have b12547 := hb (x 1 12)
    clear * - r12541 e12542 e12543 b12544 b12545 b12546 b12547 d12467
    omega
  have d12548 : (x 1 8 && x 1 12).toNat = 0 := by
    have r12549 := hand2 (x 1 8) (x 1 12)
    have b12550 := hb (x 1 12)
    have b12551 := hb (x 1 8 && x 1 12)
    clear * - r12549 b12550 b12551 d12540
    omega
  have d12552 : (x 1 4).toNat = 0 := by
    have r12553 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
    have b12554 := hb (x 1 4)
    have b12555 := hb (x 1 12)
    clear * - r12553 b12554 b12555 d12540
    omega
  have d12556 : (x (-1) 2).toNat = 0 := by
    have r12557 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12558 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e12559 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b12560 := hb (x (-2) 3)
    have b12561 := hb (x (-1) 2)
    have b12562 := hb (x 0 13)
    have b12563 := hb (x 1 12)
    clear * - r12557 e12558 e12559 b12560 b12561 b12562 b12563 d12540 d12467
    omega
  have d12564 : (x (-1) 2 && x (-1) 7).toNat = 0 := by
    have r12565 := hand1 (x (-1) 2) (x (-1) 7)
    have b12566 := hb (x (-1) 2)
    have b12567 := hb (x (-1) 2 && x (-1) 7)
    clear * - r12565 b12566 b12567 d12556
    omega
  have d12568 : (x (-1) 10).toNat = 0 := by
    have r12569 : (x (-1) 10).toNat ≤ (x (-1) 2).toNat := himp _ _ (hp10 (-1))
    have b12570 := hb (x (-1) 2)
    have b12571 := hb (x (-1) 10)
    clear * - r12569 b12570 b12571 d12556
    omega
  have d12572 : (x (-2) 3).toNat = 0 := by
    have r12573 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12574 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e12575 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b12576 := hb (x (-2) 3)
    have b12577 := hb (x (-1) 2)
    have b12578 := hb (x 0 13)
    have b12579 := hb (x 1 12)
    clear * - r12573 e12574 e12575 b12576 b12577 b12578 b12579 d12540 d12467 d12556
    omega
  have d12580 : (x (-2) 3 && x (-2) 12).toNat = 0 := by
    have r12581 := hand1 (x (-2) 3) (x (-2) 12)
    have b12582 := hb (x (-2) 3)
    have b12583 := hb (x (-2) 3 && x (-2) 12)
    clear * - r12581 b12582 b12583 d12572
    omega
  have d12584 : (x (-2) 3 && x (-2) 8).toNat = 0 := by
    have r12585 := hand1 (x (-2) 3) (x (-2) 8)
    have b12586 := hb (x (-2) 3)
    have b12587 := hb (x (-2) 3 && x (-2) 8)
    clear * - r12585 b12586 b12587 d12572
    omega
  have d12588 : (x (-2) 11).toNat = 0 := by
    have r12589 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
    have b12590 := hb (x (-2) 3)
    have b12591 := hb (x (-2) 11)
    clear * - r12589 b12590 b12591 d12572
    omega
  have d12592 : (x (-2) 1 && x (-2) 11).toNat = 0 := by
    have r12593 := hand2 (x (-2) 1) (x (-2) 11)
    have b12594 := hb (x (-2) 11)
    have b12595 := hb (x (-2) 1 && x (-2) 11)
    clear * - r12593 b12594 b12595 d12588
    omega
  cases h12596 : x 0 6
  · have f12597 : (x 0 6).toNat = 0 := by rw [h12596]; rfl
    have d12598 : (x 0 6 && x 0 12).toNat = 0 := by
      have r12599 := hand1 (x 0 6) (x 0 12)
      have b12600 := hb (x 0 6)
      have b12601 := hb (x 0 6 && x 0 12)
      clear * - r12599 b12600 b12601 f12597
      omega
    have d12602 : (x 0 1 && x 0 6).toNat = 0 := by
      have r12603 := hand2 (x 0 1) (x 0 6)
      have b12604 := hb (x 0 6)
      have b12605 := hb (x 0 1 && x 0 6)
      clear * - r12603 b12604 b12605 f12597
      omega
    have d12606 : (x 0 2 && x 0 6).toNat = 0 := by
      have r12607 := hand2 (x 0 2) (x 0 6)
      have b12608 := hb (x 0 6)
      have b12609 := hb (x 0 2 && x 0 6)
      clear * - r12607 b12608 b12609 f12597
      omega
    have d12610 : (x 0 3 && x 0 6).toNat = 0 := by
      have r12611 := hand2 (x 0 3) (x 0 6)
      have b12612 := hb (x 0 6)
      have b12613 := hb (x 0 3 && x 0 6)
      clear * - r12611 b12612 b12613 f12597
      omega
    cases h12614 : x 0 7
    · have f12615 : (x 0 7).toNat = 0 := by rw [h12614]; rfl
      have d12616 : (x 0 7 && x 0 13).toNat = 0 := by
        have r12617 := hand1 (x 0 7) (x 0 13)
        have b12618 := hb (x 0 7)
        have b12619 := hb (x 0 7 && x 0 13)
        clear * - r12617 b12618 b12619 f12615
        omega
      have d12620 : (x 0 7 && x 0 12).toNat = 0 := by
        have r12621 := hand1 (x 0 7) (x 0 12)
        have b12622 := hb (x 0 7)
        have b12623 := hb (x 0 7 && x 0 12)
        clear * - r12621 b12622 b12623 f12615
        omega
      have d12624 : (x 0 7 && x 0 11).toNat = 0 := by
        have r12625 := hand1 (x 0 7) (x 0 11)
        have b12626 := hb (x 0 7)
        have b12627 := hb (x 0 7 && x 0 11)
        clear * - r12625 b12626 b12627 f12615
        omega
      have d12628 : (x 0 3 && x 0 7).toNat = 0 := by
        have r12629 := hand2 (x 0 3) (x 0 7)
        have b12630 := hb (x 0 7)
        have b12631 := hb (x 0 3 && x 0 7)
        clear * - r12629 b12630 b12631 f12615
        omega
      cases h12632 : x 0 8
      · have f12633 : (x 0 8).toNat = 0 := by rw [h12632]; rfl
        have d12634 : (x 0 1 && x 0 8).toNat = 0 := by
          have r12635 := hand2 (x 0 1) (x 0 8)
          have b12636 := hb (x 0 8)
          have b12637 := hb (x 0 1 && x 0 8)
          clear * - r12635 b12636 b12637 f12633
          omega
        have d12638 : (x 0 2 && x 0 8).toNat = 0 := by
          have r12639 := hand2 (x 0 2) (x 0 8)
          have b12640 := hb (x 0 8)
          have b12641 := hb (x 0 2 && x 0 8)
          clear * - r12639 b12640 b12641 f12633
          omega
        have d12642 : (x 0 8 && x 0 12).toNat = 0 := by
          have r12643 := hand1 (x 0 8) (x 0 12)
          have b12644 := hb (x 0 8)
          have b12645 := hb (x 0 8 && x 0 12)
          clear * - r12643 b12644 b12645 f12633
          omega
        have d12646 : (x 0 4 && x 0 8).toNat = 0 := by
          have r12647 := hand2 (x 0 4) (x 0 8)
          have b12648 := hb (x 0 8)
          have b12649 := hb (x 0 4 && x 0 8)
          clear * - r12647 b12648 b12649 f12633
          omega
        cases h12650 : x 0 9
        · have f12651 : (x 0 9).toNat = 0 := by rw [h12650]; rfl
          have d12652 : (x 0 9 && x 0 13).toNat = 0 := by
            have r12653 := hand1 (x 0 9) (x 0 13)
            have b12654 := hb (x 0 9)
            have b12655 := hb (x 0 9 && x 0 13)
            clear * - r12653 b12654 b12655 f12651
            omega
          cases h12656 : x 1 1
          · have f12657 : (x 1 1).toNat = 0 := by rw [h12656]; rfl
            have d12658 : (x 2 14).toNat = 1 := by
              have r12659 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b12660 := hb (x 1 1)
              have b12661 := hb (x 2 14)
              clear * - r12659 b12660 b12661 f12657
              omega
            cases h12662 : x 1 3
            · have f12663 : (x 1 3).toNat = 0 := by rw [h12662]; rfl
              have d12664 : (x 1 3 && x 1 7).toNat = 0 := by
                have r12665 := hand1 (x 1 3) (x 1 7)
                have b12666 := hb (x 1 3)
                have b12667 := hb (x 1 3 && x 1 7)
                clear * - r12665 b12666 b12667 f12663
                omega
              cases h12668 : x (-1) 6
              · have f12669 : (x (-1) 6).toNat = 0 := by rw [h12668]; rfl
                cases h12670 : x (-1) 7
                · have f12671 : (x (-1) 7).toNat = 0 := by rw [h12670]; rfl
                  cases h12672 : x 1 7
                  · have f12673 : (x 1 7).toNat = 0 := by rw [h12672]; rfl
                    cases h12674 : x (-1) 8
                    · have f12675 : (x (-1) 8).toNat = 0 := by rw [h12674]; rfl
                      have d12676 : (x (-1) 8 && x (-1) 14).toNat = 0 := by
                        have r12677 := hand1 (x (-1) 8) (x (-1) 14)
                        have b12678 := hb (x (-1) 8)
                        have b12679 := hb (x (-1) 8 && x (-1) 14)
                        clear * - r12677 b12678 b12679 f12675
                        omega
                      have d12680 : (x (-1) 8 && x (-1) 12).toNat = 0 := by
                        have r12681 := hand1 (x (-1) 8) (x (-1) 12)
                        have b12682 := hb (x (-1) 8)
                        have b12683 := hb (x (-1) 8 && x (-1) 12)
                        clear * - r12681 b12682 b12683 f12675
                        omega
                      cases h12684 : x (-1) 12
                      · have f12685 : (x (-1) 12).toNat = 0 := by rw [h12684]; rfl
                        cases h12686 : x (-1) 14
                        · have f12687 : (x (-1) 14).toNat = 0 := by rw [h12686]; rfl
                          cases h12688 : x 2 1
                          · have f12689 : (x 2 1).toNat = 0 := by rw [h12688]; rfl
                            have d12690 : (x 2 1 && x 2 14).toNat = 0 := by
                              have r12691 := hand1 (x 2 1) (x 2 14)
                              have b12692 := hb (x 2 1)
                              have b12693 := hb (x 2 1 && x 2 14)
                              clear * - r12691 b12692 b12693 f12689
                              omega
                            have d12694 : (x 3 13).toNat = 1 := by
                              have r12695 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have b12696 := hb (x 1 2)
                              have b12697 := hb (x 3 13)
                              have b12698 := hb (x 2 1 && x 2 14)
                              clear * - r12695 b12696 b12697 b12698 d12690 g17
                              omega
                            have d12699 : (x 3 1).toNat = 1 := by
                              have r12700 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
                              have b12701 := hb (x 3 1)
                              have b12702 := hb (x 3 13)
                              clear * - r12700 b12701 b12702 d12694
                              omega
                            have d12703 : (x 4 14).toNat = 0 := by
                              have r12704 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have b12705 := hb (x 3 1)
                              have b12706 := hb (x 4 14)
                              clear * - r12704 b12705 b12706 d12699
                              omega
                            have d12707 : (x 4 6).toNat = 0 := by
                              have r12708 : (x 4 6).toNat ≤ (x 4 14).toNat := himp _ _ (hp6 4)
                              have b12709 := hb (x 4 6)
                              have b12710 := hb (x 4 14)
                              clear * - r12708 b12709 b12710 d12703
                              omega
                            have d12711 : (x 4 2).toNat = 0 := by
                              have r12712 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
                              have b12713 := hb (x 4 2)
                              have b12714 := hb (x 4 14)
                              clear * - r12712 b12713 b12714 d12703
                              omega
                            have d12715 : (x 4 2 && x 4 12).toNat = 0 := by
                              have r12716 := hand1 (x 4 2) (x 4 12)
                              have b12717 := hb (x 4 2)
                              have b12718 := hb (x 4 2 && x 4 12)
                              clear * - r12716 b12717 b12718 d12711
                              omega
                            have d12719 : (x 4 12).toNat = 0 := by
                              have r12720 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e12721 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                              have e12722 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                              have b12723 := hb (x 1 3)
                              have b12724 := hb (x 2 2)
                              have b12725 := hb (x 3 13)
                              have b12726 := hb (x 4 12)
                              clear * - r12720 e12721 e12722 b12723 b12724 b12725 b12726 d12694 f12663
                              omega
                            have d12727 : (x 4 3 && x 4 12).toNat = 0 := by
                              have r12728 := hand2 (x 4 3) (x 4 12)
                              have b12729 := hb (x 4 12)
                              have b12730 := hb (x 4 3 && x 4 12)
                              clear * - r12728 b12729 b12730 d12719
                              omega
                            have d12731 : (x 4 7 && x 4 12).toNat = 0 := by
                              have r12732 := hand2 (x 4 7) (x 4 12)
                              have b12733 := hb (x 4 12)
                              have b12734 := hb (x 4 7 && x 4 12)
                              clear * - r12732 b12733 b12734 d12719
                              omega
                            have r12735 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r12736 : (x 17 1).toNat + (x 16 2).toNat + (x 15 3).toNat + (x 14 4).toNat + (x 13 5).toNat + (x 12 6).toNat + (x 11 7).toNat + (x 10 8).toNat + (x 9 9).toNat + (x 8 10).toNat + (x 7 11).toNat + (x 6 12).toNat + (x 5 13).toNat + (x 4 14).toNat = 3 := by have q := hcount 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r12737 : (x 19 1).toNat + (x 18 2).toNat + (x 17 3).toNat + (x 16 4).toNat + (x 15 5).toNat + (x 14 6).toNat + (x 13 7).toNat + (x 12 8).toNat + (x 11 9).toNat + (x 10 10).toNat + (x 9 11).toNat + (x 8 12).toNat + (x 7 13).toNat + (x 6 14).toNat = 3 := by have q := hcount 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r12738 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e12739 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                            have e12740 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                            have e12741 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                            have e12742 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                            have e12743 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                            have e12744 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                            have r12745 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e12746 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
                            have e12747 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
                            have e12748 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
                            have e12749 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
                            have e12750 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
                            have e12751 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
                            have r12752 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e12753 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
                            have e12754 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
                            have e12755 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
                            have e12756 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
                            have e12757 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
                            have e12758 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
                            have r12759 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e12760 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
                            have e12761 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
                            have e12762 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
                            have e12763 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
                            have e12764 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
                            have e12765 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
                            have r12766 : (x 20 8).toNat + (x 19 1 && x 19 9).toNat + (x 18 2 && x 18 10).toNat + (x 17 3 && x 17 11).toNat + (x 16 4 && x 16 12).toNat + (x 15 5 && x 15 13).toNat + (x 14 6 && x 14 14).toNat + (x 13 7).toNat = 1 := by have q := hd8 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e12767 : (x 19 1 && x 19 9).toNat = (x 19 9).toNat := handr _ _ (fun h => hp9 19 (h))
                            have e12768 : (x 18 2 && x 18 10).toNat = (x 18 10).toNat := handr _ _ (fun h => hp10 18 (h))
                            have e12769 : (x 17 3 && x 17 11).toNat = (x 17 11).toNat := handr _ _ (fun h => hp11 17 (h))
                            have e12770 : (x 16 4 && x 16 12).toNat = (x 16 4).toNat := handl _ _ (fun h => hp4 16 (h))
                            have e12771 : (x 15 5 && x 15 13).toNat = (x 15 5).toNat := handl _ _ (fun h => hp5 15 (h))
                            have e12772 : (x 14 6 && x 14 14).toNat = (x 14 6).toNat := handl _ _ (fun h => hp6 14 (h))
                            have r12773 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e12774 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                            have e12775 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                            have r12776 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e12777 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                            have e12778 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                            have r12779 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e12780 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                            have e12781 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                            have r12782 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e12783 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
                            have e12784 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
                            have r12785 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e12786 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
                            have e12787 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
                            have r12788 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r12789 : (x 17 14).toNat + (x 16 1).toNat = 1 := by have q := hd14 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r12790 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r12791 : 1 ≤ (x 8 4).toNat + (x 7 1 && x 7 5).toNat + (x 6 2 && x 6 6).toNat + (x 5 3 && x 5 7).toNat + (x 4 4 && x 4 8).toNat + (x 3 5 && x 3 9).toNat + (x 2 6 && x 2 10).toNat + (x 1 7 && x 1 11).toNat + (x 0 8 && x 0 12).toNat + (x (-1) 9 && x (-1) 13).toNat + (x (-2) 10 && x (-2) 14).toNat + (x (-3) 11).toNat := by have q := hcov4 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e12792 : (x 7 1 && x 7 5).toNat = (x 7 5).toNat := handr _ _ (fun h => hp13 7 (hp5 7 (h)))
                            have e12793 : (x (-2) 10 && x (-2) 14).toNat = (x (-2) 10).toNat := handl _ _ (fun h => hp2 (-2) (hp10 (-2) (h)))
                            have r12794 : 1 ≤ (x 11 5).toNat + (x 10 1 && x 10 6).toNat + (x 9 2 && x 9 7).toNat + (x 8 3 && x 8 8).toNat + (x 7 4 && x 7 9).toNat + (x 6 5 && x 6 10).toNat + (x 5 6 && x 5 11).toNat + (x 4 7 && x 4 12).toNat + (x 3 8 && x 3 13).toNat + (x 2 9 && x 2 14).toNat + (x 1 10).toNat := by have q := hcov5 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r12795 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r12796 : 1 ≤ (x 10 9).toNat + (x 9 1 && x 9 10).toNat + (x 8 2 && x 8 11).toNat + (x 7 3 && x 7 12).toNat + (x 6 4 && x 6 13).toNat + (x 5 5 && x 5 14).toNat + (x 4 6).toNat := by have q := hcov9 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r12797 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r12798 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r12799 : 1 ≤ (x 16 10).toNat + (x 15 1 && x 15 11).toNat + (x 14 2 && x 14 12).toNat + (x 13 3 && x 13 13).toNat + (x 12 4 && x 12 14).toNat + (x 11 5).toNat := by have q := hcov10 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r12800 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r12801 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r12802 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r12803 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
                            have r12804 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
                            have r12805 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
                            have r12806 : (x 6 10).toNat ≤ (x 6 2).toNat := himp _ _ (hp10 6)
                            have r12807 : (x 16 13).toNat ≤ (x 16 1).toNat := himp _ _ (hp13 16)
                            have r12808 : (x 17 2).toNat ≤ (x 17 14).toNat := himp _ _ (hp2 17)
                            have r12809 := hand2 (x 6 2) (x 6 6)
                            have r12810 := hand2 (x 5 3) (x 5 7)
                            have r12811 := hand2 (x 10 1) (x 10 6)
                            have r12812 := hand2 (x 9 2) (x 9 7)
                            have r12813 := hand2 (x 8 3) (x 8 8)
                            have r12814 := hand1 (x 7 4) (x 7 9)
                            have r12815 := hand1 (x 6 5) (x 6 10)
                            have r12816 := hand1 (x 5 6) (x 5 11)
                            have r12817 := hand2 (x 6 1) (x 6 10)
                            have r12818 := hand2 (x 5 2) (x 5 11)
                            have r12819 := hand2 (x 9 1) (x 9 10)
                            have r12820 := hand2 (x 8 2) (x 8 11)
                            have r12821 := hand2 (x 7 3) (x 7 12)
                            have r12822 := hand1 (x 6 4) (x 6 13)
                            have r12823 := hand1 (x 5 5) (x 5 14)
                            have r12824 := hand2 (x 4 1) (x 4 11)
                            have r12825 := hand2 (x 5 1) (x 5 11)
                            have r12826 := hand1 (x 3 3) (x 3 13)
                            have r12827 := hand1 (x 15 1) (x 15 11)
                            have r12828 := hand1 (x 14 2) (x 14 12)
                            have r12829 := hand1 (x 13 3) (x 13 13)
                            have r12830 := hand1 (x 12 4) (x 12 14)
                            have r12831 := hand1 (x 5 1) (x 5 14)
                            have r12832 := hand1 (x 15 1) (x 15 14)
                            have r12833 := hand2 (x 18 1) (x 18 14)
                            have b12921 := hb (x 19 1)
                            linarith only [r12735, r12736, r12737, r12738, e12739, e12740, e12741, e12742, e12743, e12744, r12745, e12746, e12747, e12748, e12749, e12750, e12751, r12752, e12753, e12754, e12755, e12756, e12757, e12758, r12759, e12760, e12761, e12762, e12763, e12764, e12765, r12766, e12767, e12768, e12769, e12770, e12771, e12772, r12773, e12774, e12775, r12776, e12777, e12778, r12779, e12780, e12781, r12782, e12783, e12784, r12785, e12786, e12787, r12788, r12789, r12790, r12791, e12792, e12793, r12794, r12795, r12796, r12797, r12798, r12799, r12800, r12801, r12802, r12803, r12804, r12805, r12806, r12807, r12808, r12809, r12810, r12811, r12812, r12813, r12814, r12815, r12816, r12817, r12818, r12819, r12820, r12821, r12822, r12823, r12824, r12825, r12826, r12827, r12828, r12829, r12830, r12831, r12832, r12833, b12921, g3, g7, g14, d12516, d12422, g18, d12658, d12694, d12711, d12707, d12719, d12703, g42, g43, g44, g45, d12642, g46, d12731, g58, g59, d12727, g82, g83, g86, g87, d12410, d12715, d12492]
                          · have f12968 : (x 2 1).toNat = 1 := by rw [h12688]; rfl
                            have d12969 : (x 3 14).toNat = 0 := by
                              have r12970 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have b12971 := hb (x 2 1)
                              have b12972 := hb (x 3 14)
                              clear * - r12970 b12971 b12972 f12968
                              omega
                            have d12973 : (x 3 1 && x 3 14).toNat = 0 := by
                              have r12974 := hand2 (x 3 1) (x 3 14)
                              have b12975 := hb (x 3 14)
                              have b12976 := hb (x 3 1 && x 3 14)
                              clear * - r12974 b12975 b12976 d12969
                              omega
                            cases h12977 : x 2 2
                            · have f12978 : (x 2 2).toNat = 0 := by rw [h12977]; rfl
                              have d12979 : (x 4 13).toNat = 1 := by
                                have r12980 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                                have b12981 := hb (x 2 2)
                                have b12982 := hb (x 4 13)
                                have b12983 := hb (x 3 1 && x 3 14)
                                clear * - r12980 b12981 b12982 b12983 d12973 f12978
                                omega
                              have d12984 : (x 4 1).toNat = 1 := by
                                have r12985 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
                                have b12986 := hb (x 4 1)
                                have b12987 := hb (x 4 13)
                                clear * - r12985 b12986 b12987 d12979
                                omega
                              have d12988 : (x 5 14).toNat = 0 := by
                                have r12989 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                                have b12990 := hb (x 4 1)
                                have b12991 := hb (x 5 14)
                                clear * - r12989 b12990 b12991 d12984
                                omega
                              have d12992 : (x 5 1 && x 5 14).toNat = 0 := by
                                have r12993 := hand2 (x 5 1) (x 5 14)
                                have b12994 := hb (x 5 14)
                                have b12995 := hb (x 5 1 && x 5 14)
                                clear * - r12993 b12994 b12995 d12988
                                omega
                              have d12996 : (x 5 6).toNat = 0 := by
                                have r12997 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
                                have b12998 := hb (x 5 6)
                                have b12999 := hb (x 5 14)
                                clear * - r12997 b12998 b12999 d12988
                                omega
                              have d13000 : (x 5 2).toNat = 0 := by
                                have r13001 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
                                have b13002 := hb (x 5 2)
                                have b13003 := hb (x 5 14)
                                clear * - r13001 b13002 b13003 d12988
                                omega
                              have d13004 : (x 5 2 && x 5 7).toNat = 0 := by
                                have r13005 := hand1 (x 5 2) (x 5 7)
                                have b13006 := hb (x 5 2)
                                have b13007 := hb (x 5 2 && x 5 7)
                                clear * - r13005 b13006 b13007 d13000
                                omega
                              have d13008 : (x 5 10).toNat = 0 := by
                                have r13009 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
                                have b13010 := hb (x 5 2)
                                have b13011 := hb (x 5 10)
                                clear * - r13009 b13010 b13011 d13000
                                omega
                              have d13012 : (x 4 1 && x 4 11).toNat = 1 := by
                                have r13013 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                                have b13014 := hb (x 0 5)
                                have b13015 := hb (x 5 10)
                                have b13016 := hb (x 4 1 && x 4 11)
                                have b13017 := hb (x 3 2 && x 3 12)
                                have b13018 := hb (x 2 3 && x 2 13)
                                have b13019 := hb (x 1 4 && x 1 14)
                                clear * - r13013 b13014 b13015 b13016 b13017 b13018 b13019 d13008 g86 g87 d12410 g14
                                omega
                              have d13020 : (x 4 11).toNat = 1 := by
                                have r13021 := hand2 (x 4 1) (x 4 11)
                                have b13022 := hb (x 4 11)
                                have b13023 := hb (x 4 1 && x 4 11)
                                clear * - r13021 b13022 b13023 d13012
                                omega
                              have d13024 : (x 4 3).toNat = 1 := by
                                have r13025 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
                                have b13026 := hb (x 4 3)
                                have b13027 := hb (x 4 11)
                                clear * - r13025 b13026 b13027 d13020
                                omega
                              have d13028 : (x 7 12).toNat = 0 := by
                                have r13029 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                                have e13030 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                                have e13031 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                                have b13032 := hb (x 4 3)
                                have b13033 := hb (x 5 2)
                                have b13034 := hb (x 6 13)
                                have b13035 := hb (x 7 12)
                                clear * - r13029 e13030 e13031 b13032 b13033 b13034 b13035 d13000 d13024
                                omega
                              have d13036 : (x 7 4).toNat = 0 := by
                                have r13037 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
                                have b13038 := hb (x 7 4)
                                have b13039 := hb (x 7 12)
                                clear * - r13037 b13038 b13039 d13028
                                omega
                              have d13040 : (x 7 4 && x 7 13).toNat = 0 := by
                                have r13041 := hand1 (x 7 4) (x 7 13)
                                have b13042 := hb (x 7 4)
                                have b13043 := hb (x 7 4 && x 7 13)
                                clear * - r13041 b13042 b13043 d13036
                                omega
                              have d13044 : (x 6 13).toNat = 0 := by
                                have r13045 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                                have e13046 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                                have e13047 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                                have b13048 := hb (x 4 3)
                                have b13049 := hb (x 5 2)
                                have b13050 := hb (x 6 13)
                                have b13051 := hb (x 7 12)
                                clear * - r13045 e13046 e13047 b13048 b13049 b13050 b13051 d13028 d13000 d13024
                                omega
                              have d13052 : (x 6 5).toNat = 0 := by
                                have r13053 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
                                have b13054 := hb (x 6 5)
                                have b13055 := hb (x 6 13)
                                clear * - r13053 b13054 b13055 d13044
                                omega
                              have d13056 : (x 6 5 && x 6 14).toNat = 0 := by
                                have r13057 := hand1 (x 6 5) (x 6 14)
                                have b13058 := hb (x 6 5)
                                have b13059 := hb (x 6 5 && x 6 14)
                                clear * - r13057 b13058 b13059 d13052
                                omega
                              have d13060 : (x 4 2).toNat = 1 := by
                                have r13061 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                                have b13062 := hb (x 4 2)
                                have b13063 := hb (x 6 13)
                                have b13064 := hb (x 5 1 && x 5 14)
                                clear * - r13061 b13062 b13063 b13064 d13044 d12992
                                omega
                              have d13065 : (x 6 12).toNat = 0 := by
                                have r13066 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                                have e13067 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                                have e13068 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                                have b13069 := hb (x 3 3)
                                have b13070 := hb (x 4 2)
                                have b13071 := hb (x 5 13)
                                have b13072 := hb (x 6 12)
                                clear * - r13066 e13067 e13068 b13069 b13070 b13071 b13072 d13060
                                omega
                              have d13073 : (x 5 13).toNat = 0 := by
                                have r13074 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                                have e13075 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                                have e13076 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                                have b13077 := hb (x 3 3)
                                have b13078 := hb (x 4 2)
                                have b13079 := hb (x 5 13)
                                have b13080 := hb (x 6 12)
                                clear * - r13074 e13075 e13076 b13077 b13078 b13079 b13080 d13065 d13060
                                omega
                              have d13081 : (x 3 3).toNat = 0 := by
                                have r13082 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                                have e13083 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                                have e13084 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                                have b13085 := hb (x 3 3)
                                have b13086 := hb (x 4 2)
                                have b13087 := hb (x 5 13)
                                have b13088 := hb (x 6 12)
                                clear * - r13082 e13083 e13084 b13085 b13086 b13087 b13088 d13065 d13073 d13060
                                omega
                              have r13089 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r13090 : (x 6 1).toNat + (x 5 2).toNat + (x 4 3).toNat + (x 3 4).toNat + (x 2 5).toNat + (x 1 6).toNat + (x 0 7).toNat + (x (-1) 8).toNat + (x (-2) 9).toNat + (x (-3) 10).toNat + (x (-4) 11).toNat + (x (-5) 12).toNat + (x (-6) 13).toNat + (x (-7) 14).toNat = 3 := by have q := hcount 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r13091 : (x (-10) 8).toNat + (x (-11) 1 && x (-11) 9).toNat + (x (-12) 2 && x (-12) 10).toNat + (x (-13) 3 && x (-13) 11).toNat + (x (-14) 4 && x (-14) 12).toNat + (x (-15) 5 && x (-15) 13).toNat + (x (-16) 6 && x (-16) 14).toNat + (x (-17) 7).toNat = 1 := by have q := hd8 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e13092 : (x (-11) 1 && x (-11) 9).toNat = (x (-11) 9).toNat := handr _ _ (fun h => hp9 (-11) (h))
                              have e13093 : (x (-12) 2 && x (-12) 10).toNat = (x (-12) 10).toNat := handr _ _ (fun h => hp10 (-12) (h))
                              have e13094 : (x (-13) 3 && x (-13) 11).toNat = (x (-13) 11).toNat := handr _ _ (fun h => hp11 (-13) (h))
                              have e13095 : (x (-14) 4 && x (-14) 12).toNat = (x (-14) 4).toNat := handl _ _ (fun h => hp4 (-14) (h))
                              have e13096 : (x (-15) 5 && x (-15) 13).toNat = (x (-15) 5).toNat := handl _ _ (fun h => hp5 (-15) (h))
                              have e13097 : (x (-16) 6 && x (-16) 14).toNat = (x (-16) 6).toNat := handl _ _ (fun h => hp6 (-16) (h))
                              have r13098 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e13099 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
                              have e13100 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
                              have e13101 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
                              have e13102 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
                              have e13103 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
                              have e13104 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
                              have r13105 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e13106 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                              have e13107 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                              have e13108 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                              have e13109 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                              have e13110 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                              have e13111 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                              have r13112 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e13113 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
                              have e13114 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
                              have e13115 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
                              have e13116 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
                              have e13117 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
                              have e13118 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
                              have r13119 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e13120 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
                              have e13121 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
                              have r13122 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e13123 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                              have e13124 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                              have r13125 : 1 ≤ (x 3 3).toNat + (x 2 1 && x 2 4).toNat + (x 1 2 && x 1 5).toNat + (x 0 3 && x 0 6).toNat + (x (-1) 4 && x (-1) 7).toNat + (x (-2) 5 && x (-2) 8).toNat + (x (-3) 6 && x (-3) 9).toNat + (x (-4) 7 && x (-4) 10).toNat + (x (-5) 8 && x (-5) 11).toNat + (x (-6) 9 && x (-6) 12).toNat + (x (-7) 10 && x (-7) 13).toNat + (x (-8) 11 && x (-8) 14).toNat + (x (-9) 12).toNat := by have q := hcov3 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r13126 : 1 ≤ (x 8 4).toNat + (x 7 1 && x 7 5).toNat + (x 6 2 && x 6 6).toNat + (x 5 3 && x 5 7).toNat + (x 4 4 && x 4 8).toNat + (x 3 5 && x 3 9).toNat + (x 2 6 && x 2 10).toNat + (x 1 7 && x 1 11).toNat + (x 0 8 && x 0 12).toNat + (x (-1) 9 && x (-1) 13).toNat + (x (-2) 10 && x (-2) 14).toNat + (x (-3) 11).toNat := by have q := hcov4 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e13127 : (x 7 1 && x 7 5).toNat = (x 7 5).toNat := handr _ _ (fun h => hp13 7 (hp5 7 (h)))
                              have e13128 : (x (-2) 10 && x (-2) 14).toNat = (x (-2) 10).toNat := handl _ _ (fun h => hp2 (-2) (hp10 (-2) (h)))
                              have r13129 : 1 ≤ (x (-2) 5).toNat + (x (-3) 1 && x (-3) 6).toNat + (x (-4) 2 && x (-4) 7).toNat + (x (-5) 3 && x (-5) 8).toNat + (x (-6) 4 && x (-6) 9).toNat + (x (-7) 5 && x (-7) 10).toNat + (x (-8) 6 && x (-8) 11).toNat + (x (-9) 7 && x (-9) 12).toNat + (x (-10) 8 && x (-10) 13).toNat + (x (-11) 9 && x (-11) 14).toNat + (x (-12) 10).toNat := by have q := hcov5 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r13130 : 1 ≤ (x 7 5).toNat + (x 6 1 && x 6 6).toNat + (x 5 2 && x 5 7).toNat + (x 4 3 && x 4 8).toNat + (x 3 4 && x 3 9).toNat + (x 2 5 && x 2 10).toNat + (x 1 6 && x 1 11).toNat + (x 0 7 && x 0 12).toNat + (x (-1) 8 && x (-1) 13).toNat + (x (-2) 9 && x (-2) 14).toNat + (x (-3) 10).toNat := by have q := hcov5 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r13131 : 1 ≤ (x (-2) 6).toNat + (x (-3) 1 && x (-3) 7).toNat + (x (-4) 2 && x (-4) 8).toNat + (x (-5) 3 && x (-5) 9).toNat + (x (-6) 4 && x (-6) 10).toNat + (x (-7) 5 && x (-7) 11).toNat + (x (-8) 6 && x (-8) 12).toNat + (x (-9) 7 && x (-9) 13).toNat + (x (-10) 8 && x (-10) 14).toNat + (x (-11) 9).toNat := by have q := hcov6 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r13132 : 1 ≤ (x 6 6).toNat + (x 5 1 && x 5 7).toNat + (x 4 2 && x 4 8).toNat + (x 3 3 && x 3 9).toNat + (x 2 4 && x 2 10).toNat + (x 1 5 && x 1 11).toNat + (x 0 6 && x 0 12).toNat + (x (-1) 7 && x (-1) 13).toNat + (x (-2) 8 && x (-2) 14).toNat + (x (-3) 9).toNat := by have q := hcov6 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r13133 : 1 ≤ (x 11 9).toNat + (x 10 1 && x 10 10).toNat + (x 9 2 && x 9 11).toNat + (x 8 3 && x 8 12).toNat + (x 7 4 && x 7 13).toNat + (x 6 5 && x 6 14).toNat + (x 5 6).toNat := by have q := hcov9 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r13134 : 1 ≤ (x (-4) 10).toNat + (x (-5) 1 && x (-5) 11).toNat + (x (-6) 2 && x (-6) 12).toNat + (x (-7) 3 && x (-7) 13).toNat + (x (-8) 4 && x (-8) 14).toNat + (x (-9) 5).toNat := by have q := hcov10 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r13135 : 1 ≤ (x (-6) 13).toNat + (x (-7) 1 && x (-7) 14).toNat + (x (-8) 2).toNat := by have q := hcov13 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r13136 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r13137 : (x 7 5).toNat ≤ (x 7 13).toNat := himp _ _ (hp5 7)
                              have r13138 := hand2 (x (-5) 8) (x (-5) 11)
                              have r13139 := hand1 (x (-6) 9) (x (-6) 12)
                              have r13140 := hand1 (x (-7) 10) (x (-7) 13)
                              have r13141 := hand1 (x (-8) 11) (x (-8) 14)
                              have r13142 := hand1 (x 6 2) (x 6 6)
                              have r13143 := hand1 (x 5 3) (x 5 7)
                              have r13144 := hand2 (x (-5) 3) (x (-5) 8)
                              have r13145 := hand1 (x (-6) 4) (x (-6) 9)
                              have r13146 := hand1 (x (-7) 5) (x (-7) 10)
                              have r13147 := hand1 (x (-8) 6) (x (-8) 11)
                              have r13148 := hand1 (x (-9) 7) (x (-9) 12)
                              have r13149 := hand2 (x (-10) 8) (x (-10) 13)
                              have r13150 := hand2 (x (-11) 9) (x (-11) 14)
                              have r13151 := hand2 (x 6 1) (x 6 6)
                              have r13152 := hand1 (x (-2) 9) (x (-2) 14)
                              have r13153 := hand2 (x (-4) 2) (x (-4) 8)
                              have r13154 := hand2 (x (-5) 3) (x (-5) 9)
                              have r13155 := hand1 (x (-6) 4) (x (-6) 10)
                              have r13156 := hand1 (x (-7) 5) (x (-7) 11)
                              have r13157 := hand1 (x (-8) 6) (x (-8) 12)
                              have r13158 := hand1 (x (-9) 7) (x (-9) 13)
                              have r13159 := hand1 (x (-10) 8) (x (-10) 14)
                              have r13160 := hand2 (x 5 1) (x 5 7)
                              have r13161 := hand1 (x (-2) 8) (x (-2) 14)
                              have r13162 := hand2 (x 10 1) (x 10 10)
                              have r13163 := hand2 (x 9 2) (x 9 11)
                              have r13164 := hand2 (x 8 3) (x 8 12)
                              have r13165 := hand2 (x (-5) 1) (x (-5) 11)
                              have r13166 := hand2 (x (-6) 2) (x (-6) 12)
                              have r13167 := hand2 (x (-7) 3) (x (-7) 13)
                              have r13168 := hand1 (x (-8) 4) (x (-8) 14)
                              have r13169 := hand2 (x (-7) 1) (x (-7) 14)
                              have r13170 := hand1 (x 6 1) (x 6 14)
                              linarith only [r13089, r13090, r13091, e13092, e13093, e13094, e13095, e13096, e13097, r13098, e13099, e13100, e13101, e13102, e13103, e13104, r13105, e13106, e13107, e13108, e13109, e13110, e13111, r13112, e13113, e13114, e13115, e13116, e13117, e13118, r13119, e13120, e13121, r13122, e13123, e13124, r13125, r13126, e13127, e13128, r13129, r13130, r13131, r13132, r13133, r13134, r13135, r13136, r13137, r13138, r13139, r13140, r13141, r13142, r13143, r13144, r13145, r13146, r13147, r13148, r13149, r13150, r13151, r13152, r13153, r13154, r13155, r13156, r13157, r13158, r13159, r13160, r13161, r13162, r13163, r13164, r13165, r13166, r13167, r13168, r13169, r13170, g0, g1, g3, g5, g6, g7, g8, f12675, g12, f12615, g17, d12422, f12968, g20, d13081, g24, d13024, d13000, d12996, d12496, g26, d12610, g27, g28, g29, g30, g42, g43, g44, g45, d12642, g46, g49, g50, d13004, g53, g54, g55, g56, d12620, g57, g60, g63, g64, g65, g66, d12598, g67, d13040, d13056]
                            · have f13308 : (x 2 2).toNat = 1 := by rw [h12977]; rfl
                              have d13309 : (x 4 12).toNat = 0 := by
                                have r13310 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                                have e13311 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                                have e13312 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                                have b13313 := hb (x 1 3)
                                have b13314 := hb (x 2 2)
                                have b13315 := hb (x 3 13)
                                have b13316 := hb (x 4 12)
                                clear * - r13310 e13311 e13312 b13313 b13314 b13315 b13316 f13308 f12663
                                omega
                              have d13317 : (x 4 2 && x 4 12).toNat = 0 := by
                                have r13318 := hand2 (x 4 2) (x 4 12)
                                have b13319 := hb (x 4 12)
                                have b13320 := hb (x 4 2 && x 4 12)
                                clear * - r13318 b13319 b13320 d13309
                                omega
                              have d13321 : (x 4 4).toNat = 0 := by
                                have r13322 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
                                have b13323 := hb (x 4 4)
                                have b13324 := hb (x 4 12)
                                clear * - r13322 b13323 b13324 d13309
                                omega
                              have d13325 : (x 3 13).toNat = 0 := by
                                have r13326 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                                have e13327 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                                have e13328 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                                have b13329 := hb (x 1 3)
                                have b13330 := hb (x 2 2)
                                have b13331 := hb (x 3 13)
                                have b13332 := hb (x 4 12)
                                clear * - r13326 e13327 e13328 b13329 b13330 b13331 b13332 d13309 f13308 f12663
                                omega
                              have d13333 : (x 3 3 && x 3 13).toNat = 0 := by
                                have r13334 := hand2 (x 3 3) (x 3 13)
                                have b13335 := hb (x 3 13)
                                have b13336 := hb (x 3 3 && x 3 13)
                                clear * - r13334 b13335 b13336 d13325
                                omega
                              have d13337 : (x 3 5).toNat = 0 := by
                                have r13338 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
                                have b13339 := hb (x 3 5)
                                have b13340 := hb (x 3 13)
                                clear * - r13338 b13339 b13340 d13325
                                omega
                              have r13341 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r13342 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r13343 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e13344 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                              have e13345 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                              have e13346 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                              have e13347 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                              have e13348 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                              have e13349 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                              have r13350 : 1 ≤ (x 3 4).toNat + (x 2 1 && x 2 5).toNat + (x 1 2 && x 1 6).toNat + (x 0 3 && x 0 7).toNat + (x (-1) 4 && x (-1) 8).toNat + (x (-2) 5 && x (-2) 9).toNat + (x (-3) 6 && x (-3) 10).toNat + (x (-4) 7 && x (-4) 11).toNat + (x (-5) 8 && x (-5) 12).toNat + (x (-6) 9 && x (-6) 13).toNat + (x (-7) 10 && x (-7) 14).toNat + (x (-8) 11).toNat := by have q := hcov4 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e13351 : (x 2 1 && x 2 5).toNat = (x 2 5).toNat := handr _ _ (fun h => hp13 2 (hp5 2 (h)))
                              have e13352 : (x (-7) 10 && x (-7) 14).toNat = (x (-7) 10).toNat := handl _ _ (fun h => hp2 (-7) (hp10 (-7) (h)))
                              have r13353 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e13354 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
                              have e13355 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
                              have r13356 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r13357 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r13358 : (x (-11) 2).toNat ≤ (x (-11) 14).toNat := himp _ _ (hp2 (-11))
                              have r13359 := hand1 (x (-5) 8) (x (-5) 12)
                              have r13360 := hand1 (x (-6) 9) (x (-6) 13)
                              have r13361 := hand2 (x 2 2) (x 2 6)
                              have r13362 := hand1 (x (-4) 8) (x (-4) 12)
                              have r13363 := hand1 (x (-5) 9) (x (-5) 13)
                              have r13364 := hand2 (x 5 1) (x 5 11)
                              have r13365 := hand2 (x (-10) 1) (x (-10) 14)
                              linarith only [r13341, r13342, r13343, e13344, e13345, e13346, e13347, e13348, e13349, r13350, e13351, e13352, r13353, e13354, e13355, r13356, r13357, r13358, r13359, r13360, r13361, r13362, r13363, r13364, r13365, g0, g1, g2, g5, g6, g8, g9, g12, g13, g17, f12663, d12516, f12673, f12968, f13308, g20, g24, d13337, d13321, g31, d12628, g32, g33, g34, g35, d12664, d12646, g36, g37, g38, d13317, d13333, d12492]
                        · have f13427 : (x (-1) 14).toNat = 1 := by rw [h12686]; rfl
                          have d13428 : (x (-2) 1).toNat = 0 := by
                            have r13429 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have b13430 := hb (x (-2) 1)
                            have b13431 := hb (x (-1) 14)
                            clear * - r13429 b13430 b13431 f13427
                            omega
                          have d13432 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
                            have r13433 := hand1 (x (-2) 1) (x (-2) 14)
                            have b13434 := hb (x (-2) 1)
                            have b13435 := hb (x (-2) 1 && x (-2) 14)
                            clear * - r13433 b13434 b13435 d13428
                            omega
                          have d13436 : (x (-2) 13).toNat = 0 := by
                            have r13437 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
                            have b13438 := hb (x (-2) 1)
                            have b13439 := hb (x (-2) 13)
                            clear * - r13437 b13438 b13439 d13428
                            omega
                          have d13440 : (x (-2) 9 && x (-2) 13).toNat = 0 := by
                            have r13441 := hand2 (x (-2) 9) (x (-2) 13)
                            have b13442 := hb (x (-2) 13)
                            have b13443 := hb (x (-2) 9 && x (-2) 13)
                            clear * - r13441 b13442 b13443 d13436
                            omega
                          have d13444 : (x (-2) 9).toNat = 0 := by
                            have r13445 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
                            have b13446 := hb (x (-2) 1)
                            have b13447 := hb (x (-2) 9)
                            clear * - r13445 b13446 b13447 d13428
                            omega
                          have d13448 : (x (-3) 2).toNat = 1 := by
                            have r13449 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have b13450 := hb (x (-3) 2)
                            have b13451 := hb (x (-1) 13)
                            have b13452 := hb (x (-2) 1 && x (-2) 14)
                            clear * - r13449 b13450 b13451 b13452 g10 d13432
                            omega
                          have d13453 : (x (-3) 14).toNat = 1 := by
                            have r13454 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
                            have b13455 := hb (x (-3) 2)
                            have b13456 := hb (x (-3) 14)
                            clear * - r13454 b13455 b13456 d13448
                            omega
                          have d13457 : (x (-4) 3).toNat = 0 := by
                            have r13458 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e13459 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                            have e13460 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                            have b13461 := hb (x (-4) 3)
                            have b13462 := hb (x (-3) 2)
                            have b13463 := hb (x (-2) 13)
                            have b13464 := hb (x (-1) 12)
                            clear * - r13458 e13459 e13460 b13461 b13462 b13463 b13464 f12685 d13436 d13448
                            omega
                          have d13465 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
                            have r13466 := hand1 (x (-4) 3) (x (-4) 12)
                            have b13467 := hb (x (-4) 3)
                            have b13468 := hb (x (-4) 3 && x (-4) 12)
                            clear * - r13466 b13467 b13468 d13457
                            omega
                          have d13469 : (x (-4) 11).toNat = 0 := by
                            have r13470 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
                            have b13471 := hb (x (-4) 3)
                            have b13472 := hb (x (-4) 11)
                            clear * - r13470 b13471 b13472 d13457
                            omega
                          have r13473 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r13474 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r13475 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e13476 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                          have e13477 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                          have e13478 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                          have e13479 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                          have e13480 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                          have e13481 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                          have r13482 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e13483 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                          have e13484 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                          have r13485 : 1 ≤ (x 7 4).toNat + (x 6 1 && x 6 5).toNat + (x 5 2 && x 5 6).toNat + (x 4 3 && x 4 7).toNat + (x 3 4 && x 3 8).toNat + (x 2 5 && x 2 9).toNat + (x 1 6 && x 1 10).toNat + (x 0 7 && x 0 11).toNat + (x (-1) 8 && x (-1) 12).toNat + (x (-2) 9 && x (-2) 13).toNat + (x (-3) 10 && x (-3) 14).toNat + (x (-4) 11).toNat := by have q := hcov4 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e13486 : (x 6 1 && x 6 5).toNat = (x 6 5).toNat := handr _ _ (fun h => hp13 6 (hp5 6 (h)))
                          have e13487 : (x (-3) 10 && x (-3) 14).toNat = (x (-3) 10).toNat := handl _ _ (fun h => hp2 (-3) (hp10 (-3) (h)))
                          have r13488 : 1 ≤ (x 7 6).toNat + (x 6 1 && x 6 7).toNat + (x 5 2 && x 5 8).toNat + (x 4 3 && x 4 9).toNat + (x 3 4 && x 3 10).toNat + (x 2 5 && x 2 11).toNat + (x 1 6 && x 1 12).toNat + (x 0 7 && x 0 13).toNat + (x (-1) 8 && x (-1) 14).toNat + (x (-2) 9).toNat := by have q := hcov6 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r13489 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r13490 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r13491 : 1 ≤ (x 11 10).toNat + (x 10 1 && x 10 11).toNat + (x 9 2 && x 9 12).toNat + (x 8 3 && x 8 13).toNat + (x 7 4 && x 7 14).toNat + (x 6 5).toNat := by have q := hcov10 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r13492 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
                          have r13493 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
                          have r13494 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
                          have r13495 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
                          have r13496 : (x 11 10).toNat ≤ (x 11 2).toNat := himp _ _ (hp10 11)
                          have r13497 := hand2 (x 5 2) (x 5 6)
                          have r13498 := hand2 (x 4 3) (x 4 7)
                          have r13499 := hand2 (x 6 1) (x 6 7)
                          have r13500 := hand2 (x 5 2) (x 5 8)
                          have r13501 := hand2 (x 4 3) (x 4 9)
                          have r13502 := hand1 (x (-5) 4) (x (-5) 13)
                          have r13503 := hand1 (x (-6) 5) (x (-6) 14)
                          have r13504 := hand2 (x 4 1) (x 4 11)
                          have r13505 := hand1 (x 10 1) (x 10 11)
                          have r13506 := hand1 (x 9 2) (x 9 12)
                          have r13507 := hand1 (x 8 3) (x 8 13)
                          have r13508 := hand1 (x 7 4) (x 7 14)
                          linarith only [r13473, r13474, r13475, e13476, e13477, e13478, e13479, e13480, e13481, r13482, e13483, e13484, r13485, e13486, e13487, r13488, r13489, r13490, r13491, r13492, r13493, r13494, r13495, r13496, r13497, r13498, r13499, r13500, r13501, r13502, r13503, r13504, r13505, r13506, r13507, r13508, d13469, d13453, d13444, d13436, f12675, d12455, f12685, f13427, g14, g16, d12467, g18, d12540, g21, g25, g39, g40, g41, d12624, d12680, d13440, g68, g69, d12426, d12616, d12676, g74, g75, d13465, g86, g87, d12410]
                      · have f13583 : (x (-1) 12).toNat = 1 := by rw [h12684]; rfl
                        have d13584 : (x (-2) 13).toNat = 0 := by
                          have r13585 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e13586 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                          have e13587 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                          have b13588 := hb (x (-4) 3)
                          have b13589 := hb (x (-3) 2)
                          have b13590 := hb (x (-2) 13)
                          have b13591 := hb (x (-1) 12)
                          clear * - r13585 e13586 e13587 b13588 b13589 b13590 b13591 f13583
                          omega
                        have d13592 : (x (-3) 2).toNat = 0 := by
                          have r13593 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e13594 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                          have e13595 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                          have b13596 := hb (x (-4) 3)
                          have b13597 := hb (x (-3) 2)
                          have b13598 := hb (x (-2) 13)
                          have b13599 := hb (x (-1) 12)
                          clear * - r13593 e13594 e13595 b13596 b13597 b13598 b13599 f13583 d13584
                          omega
                        have d13600 : (x (-3) 2 && x (-3) 13).toNat = 0 := by
                          have r13601 := hand1 (x (-3) 2) (x (-3) 13)
                          have b13602 := hb (x (-3) 2)
                          have b13603 := hb (x (-3) 2 && x (-3) 13)
                          clear * - r13601 b13602 b13603 d13592
                          omega
                        have d13604 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
                          have r13605 := hand1 (x (-3) 2) (x (-3) 12)
                          have b13606 := hb (x (-3) 2)
                          have b13607 := hb (x (-3) 2 && x (-3) 12)
                          clear * - r13605 b13606 b13607 d13592
                          omega
                        have d13608 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
                          have r13609 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b13610 := hb (x (-3) 2)
                          have b13611 := hb (x (-1) 13)
                          have b13612 := hb (x (-2) 1 && x (-2) 14)
                          clear * - r13609 b13610 b13611 b13612 g10 d13592
                          omega
                        have d13613 : (x (-2) 14).toNat = 1 := by
                          have r13614 := hand2 (x (-2) 1) (x (-2) 14)
                          have b13615 := hb (x (-2) 14)
                          have b13616 := hb (x (-2) 1 && x (-2) 14)
                          clear * - r13614 b13615 b13616 d13608
                          omega
                        have d13617 : (x (-3) 1).toNat = 0 := by
                          have r13618 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b13619 := hb (x (-3) 1)
                          have b13620 := hb (x (-2) 14)
                          clear * - r13618 b13619 b13620 d13613
                          omega
                        have d13621 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
                          have r13622 := hand1 (x (-3) 1) (x (-3) 14)
                          have b13623 := hb (x (-3) 1)
                          have b13624 := hb (x (-3) 1 && x (-3) 14)
                          clear * - r13622 b13623 b13624 d13617
                          omega
                        have d13625 : (x (-4) 2).toNat = 1 := by
                          have r13626 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b13627 := hb (x (-4) 2)
                          have b13628 := hb (x (-2) 13)
                          have b13629 := hb (x (-3) 1 && x (-3) 14)
                          clear * - r13626 b13627 b13628 b13629 d13584 d13621
                          omega
                        have d13630 : (x (-4) 14).toNat = 1 := by
                          have r13631 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
                          have b13632 := hb (x (-4) 2)
                          have b13633 := hb (x (-4) 14)
                          clear * - r13631 b13632 b13633 d13625
                          omega
                        have d13634 : (x (-5) 1).toNat = 0 := by
                          have r13635 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b13636 := hb (x (-5) 1)
                          have b13637 := hb (x (-4) 14)
                          clear * - r13635 b13636 b13637 d13630
                          omega
                        have d13638 : (x (-5) 13).toNat = 0 := by
                          have r13639 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
                          have b13640 := hb (x (-5) 1)
                          have b13641 := hb (x (-5) 13)
                          clear * - r13639 b13640 b13641 d13634
                          omega
                        have d13642 : (x (-3) 13).toNat = 0 := by
                          have r13643 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
                          have b13644 := hb (x (-3) 1)
                          have b13645 := hb (x (-3) 13)
                          clear * - r13643 b13644 b13645 d13617
                          omega
                        have d13646 : (x (-4) 3).toNat = 0 := by
                          have r13647 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e13648 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                          have e13649 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                          have b13650 := hb (x (-4) 3)
                          have b13651 := hb (x (-3) 2)
                          have b13652 := hb (x (-2) 13)
                          have b13653 := hb (x (-1) 12)
                          clear * - r13647 e13648 e13649 b13650 b13651 b13652 b13653 f13583 d13584 d13592
                          omega
                        have d13654 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
                          have r13655 := hand1 (x (-4) 3) (x (-4) 14)
                          have b13656 := hb (x (-4) 3)
                          have b13657 := hb (x (-4) 3 && x (-4) 14)
                          clear * - r13655 b13656 b13657 d13646
                          omega
                        have d13658 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
                          have r13659 := hand1 (x (-4) 3) (x (-4) 13)
                          have b13660 := hb (x (-4) 3)
                          have b13661 := hb (x (-4) 3 && x (-4) 13)
                          clear * - r13659 b13660 b13661 d13646
                          omega
                        have d13662 : (x (-2) 12).toNat = 0 := by
                          have r13663 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e13664 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                          have e13665 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                          have b13666 := hb (x (-5) 3)
                          have b13667 := hb (x (-4) 2)
                          have b13668 := hb (x (-3) 13)
                          have b13669 := hb (x (-2) 12)
                          clear * - r13663 e13664 e13665 b13666 b13667 b13668 b13669 d13642 d13625
                          omega
                        have d13670 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
                          have r13671 := hand2 (x (-2) 1) (x (-2) 12)
                          have b13672 := hb (x (-2) 12)
                          have b13673 := hb (x (-2) 1 && x (-2) 12)
                          clear * - r13671 b13672 b13673 d13662
                          omega
                        have d13674 : (x (-5) 4).toNat = 1 := by
                          have r13675 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b13676 := hb (x (-5) 4)
                          have b13677 := hb (x (-1) 11)
                          have b13678 := hb (x (-2) 1 && x (-2) 12)
                          have b13679 := hb (x (-3) 2 && x (-3) 13)
                          have b13680 := hb (x (-4) 3 && x (-4) 14)
                          clear * - r13675 b13676 b13677 b13678 b13679 b13680 d12532 d13670 d13600 d13654
                          omega
                        have d13681 : (x (-5) 12).toNat = 1 := by
                          have r13682 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
                          have b13683 := hb (x (-5) 4)
                          have b13684 := hb (x (-5) 12)
                          clear * - r13682 b13683 b13684 d13674
                          omega
                        have d13685 : (x (-6) 13).toNat = 0 := by
                          have r13686 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e13687 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                          have e13688 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                          have b13689 := hb (x (-8) 3)
                          have b13690 := hb (x (-7) 2)
                          have b13691 := hb (x (-6) 13)
                          have b13692 := hb (x (-5) 12)
                          clear * - r13686 e13687 e13688 b13689 b13690 b13691 b13692 d13681
                          omega
                        have d13693 : (x (-6) 5).toNat = 0 := by
                          have r13694 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
                          have b13695 := hb (x (-6) 5)
                          have b13696 := hb (x (-6) 13)
                          clear * - r13694 b13695 b13696 d13685
                          omega
                        have d13697 : (x (-7) 2).toNat = 0 := by
                          have r13698 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e13699 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                          have e13700 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                          have b13701 := hb (x (-8) 3)
                          have b13702 := hb (x (-7) 2)
                          have b13703 := hb (x (-6) 13)
                          have b13704 := hb (x (-5) 12)
                          clear * - r13698 e13699 e13700 b13701 b13702 b13703 b13704 d13681 d13685
                          omega
                        have d13705 : (x (-6) 1 && x (-6) 14).toNat = 1 := by
                          have r13706 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b13707 := hb (x (-7) 2)
                          have b13708 := hb (x (-5) 13)
                          have b13709 := hb (x (-6) 1 && x (-6) 14)
                          clear * - r13706 b13707 b13708 b13709 d13638 d13697
                          omega
                        have d13710 : (x (-6) 1).toNat = 1 := by
                          have r13711 := hand1 (x (-6) 1) (x (-6) 14)
                          have b13712 := hb (x (-6) 1)
                          have b13713 := hb (x (-6) 1 && x (-6) 14)
                          clear * - r13711 b13712 b13713 d13705
                          omega
                        have d13714 : (x (-5) 14).toNat = 0 := by
                          have r13715 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b13716 := hb (x (-6) 1)
                          have b13717 := hb (x (-5) 14)
                          clear * - r13715 b13716 b13717 d13710
                          omega
                        have d13718 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
                          have r13719 := hand2 (x (-5) 4) (x (-5) 14)
                          have b13720 := hb (x (-5) 14)
                          have b13721 := hb (x (-5) 4 && x (-5) 14)
                          clear * - r13719 b13720 b13721 d13714
                          omega
                        have r13722 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b13723 := hb (x (-6) 5)
                        have b13724 := hb (x (-1) 10)
                        have b13725 := hb (x (-2) 1 && x (-2) 11)
                        have b13726 := hb (x (-3) 2 && x (-3) 12)
                        have b13727 := hb (x (-4) 3 && x (-4) 13)
                        have b13728 := hb (x (-5) 4 && x (-5) 14)
                        linarith only [r13722, b13723, b13724, b13725, b13726, b13727, b13728, d12568, d12592, d13604, d13658, d13718, d13693]
                    · have f13729 : (x (-1) 8).toNat = 1 := by rw [h12674]; rfl
                      have d13730 : (x (-2) 9).toNat = 0 := by
                        have r13731 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e13732 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                        have e13733 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                        have e13734 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                        have e13735 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                        have e13736 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                        have e13737 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                        have b13738 := hb (x (-8) 7)
                        have b13739 := hb (x (-7) 6)
                        have b13740 := hb (x (-6) 5)
                        have b13741 := hb (x (-5) 4)
                        have b13742 := hb (x (-4) 11)
                        have b13743 := hb (x (-3) 10)
                        have b13744 := hb (x (-2) 9)
                        have b13745 := hb (x (-1) 8)
                        clear * - r13731 e13732 e13733 e13734 e13735 e13736 e13737 b13738 b13739 b13740 b13741 b13742 b13743 b13744 b13745 f13729
                        omega
                      have d13746 : (x (-3) 10).toNat = 0 := by
                        have r13747 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e13748 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                        have e13749 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                        have e13750 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                        have e13751 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                        have e13752 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                        have e13753 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                        have b13754 := hb (x (-8) 7)
                        have b13755 := hb (x (-7) 6)
                        have b13756 := hb (x (-6) 5)
                        have b13757 := hb (x (-5) 4)
                        have b13758 := hb (x (-4) 11)
                        have b13759 := hb (x (-3) 10)
                        have b13760 := hb (x (-2) 9)
                        have b13761 := hb (x (-1) 8)
                        clear * - r13747 e13748 e13749 e13750 e13751 e13752 e13753 b13754 b13755 b13756 b13757 b13758 b13759 b13760 b13761 f13729 d13730
                        omega
                      have d13762 : (x (-3) 1 && x (-3) 10).toNat = 0 := by
                        have r13763 := hand2 (x (-3) 1) (x (-3) 10)
                        have b13764 := hb (x (-3) 10)
                        have b13765 := hb (x (-3) 1 && x (-3) 10)
                        clear * - r13763 b13764 b13765 d13746
                        omega
                      have d13766 : (x (-4) 11).toNat = 0 := by
                        have r13767 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e13768 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                        have e13769 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                        have e13770 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                        have e13771 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                        have e13772 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                        have e13773 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                        have b13774 := hb (x (-8) 7)
                        have b13775 := hb (x (-7) 6)
                        have b13776 := hb (x (-6) 5)
                        have b13777 := hb (x (-5) 4)
                        have b13778 := hb (x (-4) 11)
                        have b13779 := hb (x (-3) 10)
                        have b13780 := hb (x (-2) 9)
                        have b13781 := hb (x (-1) 8)
                        clear * - r13767 e13768 e13769 e13770 e13771 e13772 e13773 b13774 b13775 b13776 b13777 b13778 b13779 b13780 b13781 f13729 d13730 d13746
                        omega
                      have d13782 : (x (-4) 2 && x (-4) 11).toNat = 0 := by
                        have r13783 := hand2 (x (-4) 2) (x (-4) 11)
                        have b13784 := hb (x (-4) 11)
                        have b13785 := hb (x (-4) 2 && x (-4) 11)
                        clear * - r13783 b13784 b13785 d13766
                        omega
                      have d13786 : (x (-5) 4).toNat = 0 := by
                        have r13787 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e13788 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                        have e13789 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                        have e13790 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                        have e13791 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                        have e13792 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                        have e13793 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                        have b13794 := hb (x (-8) 7)
                        have b13795 := hb (x (-7) 6)
                        have b13796 := hb (x (-6) 5)
                        have b13797 := hb (x (-5) 4)
                        have b13798 := hb (x (-4) 11)
                        have b13799 := hb (x (-3) 10)
                        have b13800 := hb (x (-2) 9)
                        have b13801 := hb (x (-1) 8)
                        clear * - r13787 e13788 e13789 e13790 e13791 e13792 e13793 b13794 b13795 b13796 b13797 b13798 b13799 b13800 b13801 f13729 d13730 d13746 d13766
                        omega
                      have d13802 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
                        have r13803 := hand1 (x (-5) 4) (x (-5) 14)
                        have b13804 := hb (x (-5) 4)
                        have b13805 := hb (x (-5) 4 && x (-5) 14)
                        clear * - r13803 b13804 b13805 d13786
                        omega
                      have d13806 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
                        have r13807 := hand1 (x (-5) 4) (x (-5) 13)
                        have b13808 := hb (x (-5) 4)
                        have b13809 := hb (x (-5) 4 && x (-5) 13)
                        clear * - r13807 b13808 b13809 d13786
                        omega
                      have d13810 : (x (-5) 4 && x (-5) 11).toNat = 0 := by
                        have r13811 := hand1 (x (-5) 4) (x (-5) 11)
                        have b13812 := hb (x (-5) 4)
                        have b13813 := hb (x (-5) 4 && x (-5) 11)
                        clear * - r13811 b13812 b13813 d13786
                        omega
                      have d13814 : (x (-5) 4 && x (-5) 9).toNat = 0 := by
                        have r13815 := hand1 (x (-5) 4) (x (-5) 9)
                        have b13816 := hb (x (-5) 4)
                        have b13817 := hb (x (-5) 4 && x (-5) 9)
                        clear * - r13815 b13816 b13817 d13786
                        omega
                      have d13818 : (x (-6) 5).toNat = 0 := by
                        have r13819 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e13820 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                        have e13821 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                        have e13822 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                        have e13823 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                        have e13824 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                        have e13825 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                        have b13826 := hb (x (-8) 7)
                        have b13827 := hb (x (-7) 6)
                        have b13828 := hb (x (-6) 5)
                        have b13829 := hb (x (-5) 4)
                        have b13830 := hb (x (-4) 11)
                        have b13831 := hb (x (-3) 10)
                        have b13832 := hb (x (-2) 9)
                        have b13833 := hb (x (-1) 8)
                        clear * - r13819 e13820 e13821 e13822 e13823 e13824 e13825 b13826 b13827 b13828 b13829 b13830 b13831 b13832 b13833 f13729 d13730 d13746 d13766 d13786
                        omega
                      have d13834 : (x (-6) 5 && x (-6) 14).toNat = 0 := by
                        have r13835 := hand1 (x (-6) 5) (x (-6) 14)
                        have b13836 := hb (x (-6) 5)
                        have b13837 := hb (x (-6) 5 && x (-6) 14)
                        clear * - r13835 b13836 b13837 d13818
                        omega
                      have d13838 : (x (-6) 5 && x (-6) 12).toNat = 0 := by
                        have r13839 := hand1 (x (-6) 5) (x (-6) 12)
                        have b13840 := hb (x (-6) 5)
                        have b13841 := hb (x (-6) 5 && x (-6) 12)
                        clear * - r13839 b13840 b13841 d13818
                        omega
                      have d13842 : (x (-6) 5 && x (-6) 10).toNat = 0 := by
                        have r13843 := hand1 (x (-6) 5) (x (-6) 10)
                        have b13844 := hb (x (-6) 5)
                        have b13845 := hb (x (-6) 5 && x (-6) 10)
                        clear * - r13843 b13844 b13845 d13818
                        omega
                      have d13846 : (x (-7) 6).toNat = 0 := by
                        have r13847 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e13848 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                        have e13849 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                        have e13850 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                        have e13851 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                        have e13852 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                        have e13853 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                        have b13854 := hb (x (-8) 7)
                        have b13855 := hb (x (-7) 6)
                        have b13856 := hb (x (-6) 5)
                        have b13857 := hb (x (-5) 4)
                        have b13858 := hb (x (-4) 11)
                        have b13859 := hb (x (-3) 10)
                        have b13860 := hb (x (-2) 9)
                        have b13861 := hb (x (-1) 8)
                        clear * - r13847 e13848 e13849 e13850 e13851 e13852 e13853 b13854 b13855 b13856 b13857 b13858 b13859 b13860 b13861 f13729 d13730 d13746 d13766 d13786 d13818
                        omega
                      have d13862 : (x (-7) 6 && x (-7) 13).toNat = 0 := by
                        have r13863 := hand1 (x (-7) 6) (x (-7) 13)
                        have b13864 := hb (x (-7) 6)
                        have b13865 := hb (x (-7) 6 && x (-7) 13)
                        clear * - r13863 b13864 b13865 d13846
                        omega
                      have d13866 : (x (-7) 6 && x (-7) 11).toNat = 0 := by
                        have r13867 := hand1 (x (-7) 6) (x (-7) 11)
                        have b13868 := hb (x (-7) 6)
                        have b13869 := hb (x (-7) 6 && x (-7) 11)
                        clear * - r13867 b13868 b13869 d13846
                        omega
                      have d13870 : (x (-4) 3 && x (-4) 12).toNat = 1 := by
                        have r13871 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b13872 := hb (x (-7) 6)
                        have b13873 := hb (x (-1) 9)
                        have b13874 := hb (x (-2) 1 && x (-2) 10)
                        have b13875 := hb (x (-3) 2 && x (-3) 11)
                        have b13876 := hb (x (-4) 3 && x (-4) 12)
                        have b13877 := hb (x (-5) 4 && x (-5) 13)
                        have b13878 := hb (x (-6) 5 && x (-6) 14)
                        clear * - r13871 b13872 b13873 b13874 b13875 b13876 b13877 b13878 d12455 g74 g75 d13806 d13834 d13846
                        omega
                      have d13879 : (x (-4) 12).toNat = 1 := by
                        have r13880 := hand2 (x (-4) 3) (x (-4) 12)
                        have b13881 := hb (x (-4) 12)
                        have b13882 := hb (x (-4) 3 && x (-4) 12)
                        clear * - r13880 b13881 b13882 d13870
                        omega
                      have d13883 : (x (-5) 13).toNat = 0 := by
                        have r13884 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e13885 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                        have e13886 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                        have b13887 := hb (x (-7) 3)
                        have b13888 := hb (x (-6) 2)
                        have b13889 := hb (x (-5) 13)
                        have b13890 := hb (x (-4) 12)
                        clear * - r13884 e13885 e13886 b13887 b13888 b13889 b13890 d13879
                        omega
                      have d13891 : (x (-5) 5).toNat = 0 := by
                        have r13892 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
                        have b13893 := hb (x (-5) 5)
                        have b13894 := hb (x (-5) 13)
                        clear * - r13892 b13893 b13894 d13883
                        omega
                      have d13895 : (x (-5) 5 && x (-5) 14).toNat = 0 := by
                        have r13896 := hand1 (x (-5) 5) (x (-5) 14)
                        have b13897 := hb (x (-5) 5)
                        have b13898 := hb (x (-5) 5 && x (-5) 14)
                        clear * - r13896 b13897 b13898 d13891
                        omega
                      have d13899 : (x (-4) 4 && x (-4) 14).toNat = 1 := by
                        have r13900 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b13901 := hb (x (-5) 5)
                        have b13902 := hb (x 0 10)
                        have b13903 := hb (x (-1) 1 && x (-1) 11)
                        have b13904 := hb (x (-2) 2 && x (-2) 12)
                        have b13905 := hb (x (-3) 3 && x (-3) 13)
                        have b13906 := hb (x (-4) 4 && x (-4) 14)
                        clear * - r13900 b13901 b13902 b13903 b13904 b13905 b13906 g15 d12447 g84 g85 d13891
                        omega
                      have d13907 : (x (-4) 14).toNat = 1 := by
                        have r13908 := hand2 (x (-4) 4) (x (-4) 14)
                        have b13909 := hb (x (-4) 14)
                        have b13910 := hb (x (-4) 4 && x (-4) 14)
                        clear * - r13908 b13909 b13910 d13899
                        omega
                      have d13911 : (x (-5) 1).toNat = 0 := by
                        have r13912 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b13913 := hb (x (-5) 1)
                        have b13914 := hb (x (-4) 14)
                        clear * - r13912 b13913 b13914 d13907
                        omega
                      have d13915 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
                        have r13916 := hand1 (x (-5) 1) (x (-5) 12)
                        have b13917 := hb (x (-5) 1)
                        have b13918 := hb (x (-5) 1 && x (-5) 12)
                        clear * - r13916 b13917 b13918 d13911
                        omega
                      have d13919 : (x (-5) 9).toNat = 0 := by
                        have r13920 : (x (-5) 9).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp9 (-5))
                        have b13921 := hb (x (-5) 1)
                        have b13922 := hb (x (-5) 9)
                        clear * - r13920 b13921 b13922 d13911
                        omega
                      have d13923 : (x (-4) 4).toNat = 1 := by
                        have r13924 := hand1 (x (-4) 4) (x (-4) 14)
                        have b13925 := hb (x (-4) 4)
                        have b13926 := hb (x (-4) 4 && x (-4) 14)
                        clear * - r13924 b13925 b13926 d13899
                        omega
                      have d13927 : (x (-6) 6).toNat = 0 := by
                        have r13928 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e13929 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                        have e13930 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                        have e13931 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                        have e13932 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                        have e13933 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                        have e13934 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                        have b13935 := hb (x (-7) 7)
                        have b13936 := hb (x (-6) 6)
                        have b13937 := hb (x (-5) 5)
                        have b13938 := hb (x (-4) 4)
                        have b13939 := hb (x (-3) 11)
                        have b13940 := hb (x (-2) 10)
                        have b13941 := hb (x (-1) 9)
                        have b13942 := hb (x 0 8)
                        clear * - r13928 e13929 e13930 e13931 e13932 e13933 e13934 b13935 b13936 b13937 b13938 b13939 b13940 b13941 b13942 f12633 d12455 g7 g3 d13923 d13891
                        omega
                      have d13943 : (x (-4) 4 && x (-4) 13).toNat = 1 := by
                        have r13944 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b13945 := hb (x (-6) 6)
                        have b13946 := hb (x 0 9)
                        have b13947 := hb (x (-1) 1 && x (-1) 10)
                        have b13948 := hb (x (-2) 2 && x (-2) 11)
                        have b13949 := hb (x (-3) 3 && x (-3) 12)
                        have b13950 := hb (x (-4) 4 && x (-4) 13)
                        have b13951 := hb (x (-5) 5 && x (-5) 14)
                        clear * - r13944 b13945 b13946 b13947 b13948 b13949 b13950 b13951 f12651 d12451 g76 g77 d13895 d13927
                        omega
                      have d13952 : (x (-4) 13).toNat = 1 := by
                        have r13953 := hand2 (x (-4) 4) (x (-4) 13)
                        have b13954 := hb (x (-4) 13)
                        have b13955 := hb (x (-4) 4 && x (-4) 13)
                        clear * - r13953 b13954 b13955 d13943
                        omega
                      have d13956 : (x (-4) 1).toNat = 1 := by
                        have r13957 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
                        have b13958 := hb (x (-4) 1)
                        have b13959 := hb (x (-4) 13)
                        clear * - r13957 b13958 b13959 d13952
                        omega
                      have d13960 : (x (-3) 14).toNat = 0 := by
                        have r13961 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b13962 := hb (x (-4) 1)
                        have b13963 := hb (x (-3) 14)
                        clear * - r13961 b13962 b13963 d13956
                        omega
                      have d13964 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
                        have r13965 := hand2 (x (-3) 1) (x (-3) 14)
                        have b13966 := hb (x (-3) 14)
                        have b13967 := hb (x (-3) 1 && x (-3) 14)
                        clear * - r13965 b13966 b13967 d13960
                        omega
                      have d13968 : (x (-3) 2).toNat = 0 := by
                        have r13969 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
                        have b13970 := hb (x (-3) 2)
                        have b13971 := hb (x (-3) 14)
                        clear * - r13969 b13970 b13971 d13960
                        omega
                      have d13972 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
                        have r13973 := hand1 (x (-3) 2) (x (-3) 12)
                        have b13974 := hb (x (-3) 2)
                        have b13975 := hb (x (-3) 2 && x (-3) 12)
                        clear * - r13973 b13974 b13975 d13968
                        omega
                      have d13976 : (x (-4) 3 && x (-4) 13).toNat = 1 := by
                        have r13977 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b13978 := hb (x (-6) 5)
                        have b13979 := hb (x (-1) 10)
                        have b13980 := hb (x (-2) 1 && x (-2) 11)
                        have b13981 := hb (x (-3) 2 && x (-3) 12)
                        have b13982 := hb (x (-4) 3 && x (-4) 13)
                        have b13983 := hb (x (-5) 4 && x (-5) 14)
                        clear * - r13977 b13978 b13979 b13980 b13981 b13982 b13983 d12568 d12592 d13972 d13802 d13818
                        omega
                      have d13984 : (x (-4) 3).toNat = 1 := by
                        have r13985 := hand1 (x (-4) 3) (x (-4) 13)
                        have b13986 := hb (x (-4) 3)
                        have b13987 := hb (x (-4) 3 && x (-4) 13)
                        clear * - r13985 b13986 b13987 d13976
                        omega
                      have d13988 : (x (-3) 2 && x (-3) 9).toNat = 0 := by
                        have r13989 := hand1 (x (-3) 2) (x (-3) 9)
                        have b13990 := hb (x (-3) 2)
                        have b13991 := hb (x (-3) 2 && x (-3) 9)
                        clear * - r13989 b13990 b13991 d13968
                        omega
                      have d13992 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
                        have r13993 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b13994 := hb (x (-3) 2)
                        have b13995 := hb (x (-1) 13)
                        have b13996 := hb (x (-2) 1 && x (-2) 14)
                        clear * - r13993 b13994 b13995 b13996 g10 d13968
                        omega
                      have d13997 : (x (-2) 14).toNat = 1 := by
                        have r13998 := hand2 (x (-2) 1) (x (-2) 14)
                        have b13999 := hb (x (-2) 14)
                        have b14000 := hb (x (-2) 1 && x (-2) 14)
                        clear * - r13998 b13999 b14000 d13992
                        omega
                      have d14001 : (x (-3) 1).toNat = 0 := by
                        have r14002 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b14003 := hb (x (-3) 1)
                        have b14004 := hb (x (-2) 14)
                        clear * - r14002 b14003 b14004 d13997
                        omega
                      have d14005 : (x (-3) 13).toNat = 0 := by
                        have r14006 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
                        have b14007 := hb (x (-3) 1)
                        have b14008 := hb (x (-3) 13)
                        clear * - r14006 b14007 b14008 d14001
                        omega
                      have d14009 : (x (-3) 9).toNat = 0 := by
                        have r14010 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
                        have b14011 := hb (x (-3) 1)
                        have b14012 := hb (x (-3) 9)
                        clear * - r14010 b14011 b14012 d14001
                        omega
                      have d14013 : (x (-1) 12).toNat = 0 := by
                        have r14014 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e14015 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                        have e14016 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                        have b14017 := hb (x (-4) 3)
                        have b14018 := hb (x (-3) 2)
                        have b14019 := hb (x (-2) 13)
                        have b14020 := hb (x (-1) 12)
                        clear * - r14014 e14015 e14016 b14017 b14018 b14019 b14020 d13968 d13984
                        omega
                      have d14021 : (x (-2) 13).toNat = 0 := by
                        have r14022 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e14023 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                        have e14024 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                        have b14025 := hb (x (-4) 3)
                        have b14026 := hb (x (-3) 2)
                        have b14027 := hb (x (-2) 13)
                        have b14028 := hb (x (-1) 12)
                        clear * - r14022 e14023 e14024 b14025 b14026 b14027 b14028 d14013 d13968 d13984
                        omega
                      have d14029 : (x (-4) 2).toNat = 1 := by
                        have r14030 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b14031 := hb (x (-4) 2)
                        have b14032 := hb (x (-2) 13)
                        have b14033 := hb (x (-3) 1 && x (-3) 14)
                        clear * - r14030 b14031 b14032 b14033 d14021 d13964
                        omega
                      have d14034 : (x (-2) 12).toNat = 0 := by
                        have r14035 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e14036 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                        have e14037 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                        have b14038 := hb (x (-5) 3)
                        have b14039 := hb (x (-4) 2)
                        have b14040 := hb (x (-3) 13)
                        have b14041 := hb (x (-2) 12)
                        clear * - r14035 e14036 e14037 b14038 b14039 b14040 b14041 d14005 d14029
                        omega
                      have d14042 : (x (-5) 3).toNat = 0 := by
                        have r14043 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e14044 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                        have e14045 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                        have b14046 := hb (x (-5) 3)
                        have b14047 := hb (x (-4) 2)
                        have b14048 := hb (x (-3) 13)
                        have b14049 := hb (x (-2) 12)
                        clear * - r14043 e14044 e14045 b14046 b14047 b14048 b14049 d14034 d14005 d14029
                        omega
                      have d14050 : (x (-5) 3 && x (-5) 12).toNat = 0 := by
                        have r14051 := hand1 (x (-5) 3) (x (-5) 12)
                        have b14052 := hb (x (-5) 3)
                        have b14053 := hb (x (-5) 3 && x (-5) 12)
                        clear * - r14051 b14052 b14053 d14042
                        omega
                      have d14054 : (x (-5) 11).toNat = 0 := by
                        have r14055 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
                        have b14056 := hb (x (-5) 3)
                        have b14057 := hb (x (-5) 11)
                        clear * - r14055 b14056 b14057 d14042
                        omega
                      have d14058 : (x (-6) 2).toNat = 0 := by
                        have r14059 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e14060 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                        have e14061 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                        have b14062 := hb (x (-7) 3)
                        have b14063 := hb (x (-6) 2)
                        have b14064 := hb (x (-5) 13)
                        have b14065 := hb (x (-4) 12)
                        clear * - r14059 e14060 e14061 b14062 b14063 b14064 b14065 d13879 d13883
                        omega
                      have d14066 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
                        have r14067 := hand1 (x (-6) 2) (x (-6) 13)
                        have b14068 := hb (x (-6) 2)
                        have b14069 := hb (x (-6) 2 && x (-6) 13)
                        clear * - r14067 b14068 b14069 d14058
                        omega
                      have d14070 : (x (-6) 10).toNat = 0 := by
                        have r14071 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
                        have b14072 := hb (x (-6) 2)
                        have b14073 := hb (x (-6) 10)
                        clear * - r14071 b14072 b14073 d14058
                        omega
                      have d14074 : (x (-7) 3).toNat = 0 := by
                        have r14075 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e14076 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                        have e14077 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                        have b14078 := hb (x (-7) 3)
                        have b14079 := hb (x (-6) 2)
                        have b14080 := hb (x (-5) 13)
                        have b14081 := hb (x (-4) 12)
                        clear * - r14075 e14076 e14077 b14078 b14079 b14080 b14081 d13879 d13883 d14058
                        omega
                      have d14082 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
                        have r14083 := hand1 (x (-7) 3) (x (-7) 14)
                        have b14084 := hb (x (-7) 3)
                        have b14085 := hb (x (-7) 3 && x (-7) 14)
                        clear * - r14083 b14084 b14085 d14074
                        omega
                      have d14086 : (x (-8) 4).toNat = 1 := by
                        have r14087 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b14088 := hb (x (-8) 4)
                        have b14089 := hb (x (-4) 11)
                        have b14090 := hb (x (-5) 1 && x (-5) 12)
                        have b14091 := hb (x (-6) 2 && x (-6) 13)
                        have b14092 := hb (x (-7) 3 && x (-7) 14)
                        clear * - r14087 b14088 b14089 b14090 b14091 b14092 d13766 d13915 d14066 d14082
                        omega
                      have d14093 : (x (-8) 12).toNat = 1 := by
                        have r14094 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
                        have b14095 := hb (x (-8) 4)
                        have b14096 := hb (x (-8) 12)
                        clear * - r14094 b14095 b14096 d14086
                        omega
                      have d14097 : (x (-9) 13).toNat = 0 := by
                        have r14098 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e14099 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
                        have e14100 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
                        have b14101 := hb (x (-11) 3)
                        have b14102 := hb (x (-10) 2)
                        have b14103 := hb (x (-9) 13)
                        have b14104 := hb (x (-8) 12)
                        clear * - r14098 e14099 e14100 b14101 b14102 b14103 b14104 d14093
                        omega
                      have d14105 : (x (-9) 8 && x (-9) 13).toNat = 0 := by
                        have r14106 := hand2 (x (-9) 8) (x (-9) 13)
                        have b14107 := hb (x (-9) 13)
                        have b14108 := hb (x (-9) 8 && x (-9) 13)
                        clear * - r14106 b14107 b14108 d14097
                        omega
                      have d14109 : (x (-9) 5).toNat = 0 := by
                        have r14110 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
                        have b14111 := hb (x (-9) 5)
                        have b14112 := hb (x (-9) 13)
                        clear * - r14110 b14111 b14112 d14097
                        omega
                      have d14113 : (x (-7) 11).toNat = 0 := by
                        have r14114 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
                        have b14115 := hb (x (-7) 3)
                        have b14116 := hb (x (-7) 11)
                        clear * - r14114 b14115 b14116 d14074
                        omega
                      have d14117 : (x (-8) 7).toNat = 0 := by
                        have r14118 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e14119 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                        have e14120 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                        have e14121 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                        have e14122 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                        have e14123 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                        have e14124 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                        have b14125 := hb (x (-8) 7)
                        have b14126 := hb (x (-7) 6)
                        have b14127 := hb (x (-6) 5)
                        have b14128 := hb (x (-5) 4)
                        have b14129 := hb (x (-4) 11)
                        have b14130 := hb (x (-3) 10)
                        have b14131 := hb (x (-2) 9)
                        have b14132 := hb (x (-1) 8)
                        clear * - r14118 e14119 e14120 e14121 e14122 e14123 e14124 b14125 b14126 b14127 b14128 b14129 b14130 b14131 b14132 f13729 d13730 d13746 d13766 d13786 d13818 d13846
                        omega
                      have d14133 : (x (-8) 7 && x (-8) 14).toNat = 0 := by
                        have r14134 := hand1 (x (-8) 7) (x (-8) 14)
                        have b14135 := hb (x (-8) 7)
                        have b14136 := hb (x (-8) 7 && x (-8) 14)
                        clear * - r14134 b14135 b14136 d14117
                        omega
                      have d14137 : (x (-8) 7 && x (-8) 12).toNat = 0 := by
                        have r14138 := hand1 (x (-8) 7) (x (-8) 12)
                        have b14139 := hb (x (-8) 7)
                        have b14140 := hb (x (-8) 7 && x (-8) 12)
                        clear * - r14138 b14139 b14140 d14117
                        omega
                      have d14141 : (x (-4) 8).toNat = 0 := by
                        have r14142 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e14143 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
                        have e14144 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
                        have e14145 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
                        have e14146 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
                        have e14147 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
                        have e14148 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
                        have b14149 := hb (x (-11) 7)
                        have b14150 := hb (x (-10) 6)
                        have b14151 := hb (x (-9) 5)
                        have b14152 := hb (x (-8) 4)
                        have b14153 := hb (x (-7) 11)
                        have b14154 := hb (x (-6) 10)
                        have b14155 := hb (x (-5) 9)
                        have b14156 := hb (x (-4) 8)
                        clear * - r14142 e14143 e14144 e14145 e14146 e14147 e14148 b14149 b14150 b14151 b14152 b14153 b14154 b14155 b14156 d13919 d14070 d14113 d14086 d14109
                        omega
                      have d14157 : (x (-4) 3 && x (-4) 8).toNat = 0 := by
                        have r14158 := hand2 (x (-4) 3) (x (-4) 8)
                        have b14159 := hb (x (-4) 8)
                        have b14160 := hb (x (-4) 3 && x (-4) 8)
                        clear * - r14158 b14159 b14160 d14141
                        omega
                      have r14161 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e14162 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
                      have e14163 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
                      have e14164 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
                      have e14165 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
                      have e14166 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
                      have e14167 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
                      have r14168 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e14169 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                      have e14170 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                      have e14171 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                      have e14172 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                      have e14173 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                      have e14174 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                      have r14175 : 1 ≤ (x (-1) 5).toNat + (x (-2) 1 && x (-2) 6).toNat + (x (-3) 2 && x (-3) 7).toNat + (x (-4) 3 && x (-4) 8).toNat + (x (-5) 4 && x (-5) 9).toNat + (x (-6) 5 && x (-6) 10).toNat + (x (-7) 6 && x (-7) 11).toNat + (x (-8) 7 && x (-8) 12).toNat + (x (-9) 8 && x (-9) 13).toNat + (x (-10) 9 && x (-10) 14).toNat + (x (-11) 10).toNat := by have q := hcov5 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r14176 : 1 ≤ (x (-1) 7).toNat + (x (-2) 1 && x (-2) 8).toNat + (x (-3) 2 && x (-3) 9).toNat + (x (-4) 3 && x (-4) 10).toNat + (x (-5) 4 && x (-5) 11).toNat + (x (-6) 5 && x (-6) 12).toNat + (x (-7) 6 && x (-7) 13).toNat + (x (-8) 7 && x (-8) 14).toNat + (x (-9) 8).toNat := by have q := hcov7 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r14177 : 1 ≤ (x (-2) 9).toNat + (x (-3) 1 && x (-3) 10).toNat + (x (-4) 2 && x (-4) 11).toNat + (x (-5) 3 && x (-5) 12).toNat + (x (-6) 4 && x (-6) 13).toNat + (x (-7) 5 && x (-7) 14).toNat + (x (-8) 6).toNat := by have q := hcov9 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r14178 := hand1 (x (-10) 9) (x (-10) 14)
                      have r14179 := hand2 (x (-2) 1) (x (-2) 8)
                      have r14180 := hand2 (x (-4) 3) (x (-4) 10)
                      have r14181 := hand1 (x (-6) 4) (x (-6) 13)
                      have r14182 := hand1 (x (-7) 5) (x (-7) 14)
                      linarith only [r14161, e14162, e14163, e14164, e14165, e14166, e14167, r14168, e14169, e14170, e14171, e14172, e14173, e14174, r14175, r14176, r14177, r14178, r14179, r14180, r14181, r14182, d14054, d14009, d13730, g9, f12671, g51, g52, d14157, d13814, d13842, d13866, d14137, d14105, d13988, d13810, d13838, d13862, d14133, d13762, d13782, d14050]
                  · have f14223 : (x 1 7).toNat = 1 := by rw [h12672]; rfl
                    have d14224 : (x 8 8).toNat = 0 := by
                      have r14225 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e14226 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                      have e14227 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                      have e14228 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                      have e14229 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                      have e14230 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                      have e14231 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                      have b14232 := hb (x 1 7)
                      have b14233 := hb (x 2 6)
                      have b14234 := hb (x 3 5)
                      have b14235 := hb (x 4 4)
                      have b14236 := hb (x 5 11)
                      have b14237 := hb (x 6 10)
                      have b14238 := hb (x 7 9)
                      have b14239 := hb (x 8 8)
                      clear * - r14225 e14226 e14227 e14228 e14229 e14230 e14231 b14232 b14233 b14234 b14235 b14236 b14237 b14238 b14239 f14223
                      omega
                    have d14240 : (x 8 3 && x 8 8).toNat = 0 := by
                      have r14241 := hand2 (x 8 3) (x 8 8)
                      have b14242 := hb (x 8 8)
                      have b14243 := hb (x 8 3 && x 8 8)
                      clear * - r14241 b14242 b14243 d14224
                      omega
                    have d14244 : (x 8 4 && x 8 8).toNat = 0 := by
                      have r14245 := hand2 (x 8 4) (x 8 8)
                      have b14246 := hb (x 8 8)
                      have b14247 := hb (x 8 4 && x 8 8)
                      clear * - r14245 b14246 b14247 d14224
                      omega
                    have d14248 : (x 7 9).toNat = 0 := by
                      have r14249 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e14250 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                      have e14251 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                      have e14252 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                      have e14253 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                      have e14254 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                      have e14255 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                      have b14256 := hb (x 1 7)
                      have b14257 := hb (x 2 6)
                      have b14258 := hb (x 3 5)
                      have b14259 := hb (x 4 4)
                      have b14260 := hb (x 5 11)
                      have b14261 := hb (x 6 10)
                      have b14262 := hb (x 7 9)
                      have b14263 := hb (x 8 8)
                      clear * - r14249 e14250 e14251 e14252 e14253 e14254 e14255 b14256 b14257 b14258 b14259 b14260 b14261 b14262 b14263 d14224 f14223
                      omega
                    have d14264 : (x 7 4 && x 7 9).toNat = 0 := by
                      have r14265 := hand2 (x 7 4) (x 7 9)
                      have b14266 := hb (x 7 9)
                      have b14267 := hb (x 7 4 && x 7 9)
                      clear * - r14265 b14266 b14267 d14248
                      omega
                    have d14268 : (x 7 5 && x 7 9).toNat = 0 := by
                      have r14269 := hand2 (x 7 5) (x 7 9)
                      have b14270 := hb (x 7 9)
                      have b14271 := hb (x 7 5 && x 7 9)
                      clear * - r14269 b14270 b14271 d14248
                      omega
                    have d14272 : (x 6 10).toNat = 0 := by
                      have r14273 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e14274 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                      have e14275 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                      have e14276 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                      have e14277 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                      have e14278 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                      have e14279 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                      have b14280 := hb (x 1 7)
                      have b14281 := hb (x 2 6)
                      have b14282 := hb (x 3 5)
                      have b14283 := hb (x 4 4)
                      have b14284 := hb (x 5 11)
                      have b14285 := hb (x 6 10)
                      have b14286 := hb (x 7 9)
                      have b14287 := hb (x 8 8)
                      clear * - r14273 e14274 e14275 e14276 e14277 e14278 e14279 b14280 b14281 b14282 b14283 b14284 b14285 b14286 b14287 d14224 d14248 f14223
                      omega
                    have d14288 : (x 6 1 && x 6 10).toNat = 0 := by
                      have r14289 := hand2 (x 6 1) (x 6 10)
                      have b14290 := hb (x 6 10)
                      have b14291 := hb (x 6 1 && x 6 10)
                      clear * - r14289 b14290 b14291 d14272
                      omega
                    have d14292 : (x 6 5 && x 6 10).toNat = 0 := by
                      have r14293 := hand2 (x 6 5) (x 6 10)
                      have b14294 := hb (x 6 10)
                      have b14295 := hb (x 6 5 && x 6 10)
                      clear * - r14293 b14294 b14295 d14272
                      omega
                    have d14296 : (x 6 6 && x 6 10).toNat = 0 := by
                      have r14297 := hand2 (x 6 6) (x 6 10)
                      have b14298 := hb (x 6 10)
                      have b14299 := hb (x 6 6 && x 6 10)
                      clear * - r14297 b14298 b14299 d14272
                      omega
                    have d14300 : (x 5 11).toNat = 0 := by
                      have r14301 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e14302 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                      have e14303 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                      have e14304 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                      have e14305 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                      have e14306 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                      have e14307 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                      have b14308 := hb (x 1 7)
                      have b14309 := hb (x 2 6)
                      have b14310 := hb (x 3 5)
                      have b14311 := hb (x 4 4)
                      have b14312 := hb (x 5 11)
                      have b14313 := hb (x 6 10)
                      have b14314 := hb (x 7 9)
                      have b14315 := hb (x 8 8)
                      clear * - r14301 e14302 e14303 e14304 e14305 e14306 e14307 b14308 b14309 b14310 b14311 b14312 b14313 b14314 b14315 d14224 d14248 d14272 f14223
                      omega
                    have d14316 : (x 5 1 && x 5 11).toNat = 0 := by
                      have r14317 := hand2 (x 5 1) (x 5 11)
                      have b14318 := hb (x 5 11)
                      have b14319 := hb (x 5 1 && x 5 11)
                      clear * - r14317 b14318 b14319 d14300
                      omega
                    have d14320 : (x 5 2 && x 5 11).toNat = 0 := by
                      have r14321 := hand2 (x 5 2) (x 5 11)
                      have b14322 := hb (x 5 11)
                      have b14323 := hb (x 5 2 && x 5 11)
                      clear * - r14321 b14322 b14323 d14300
                      omega
                    have d14324 : (x 4 3 && x 4 12).toNat = 1 := by
                      have r14325 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b14326 := hb (x 1 6)
                      have b14327 := hb (x 7 9)
                      have b14328 := hb (x 6 1 && x 6 10)
                      have b14329 := hb (x 5 2 && x 5 11)
                      have b14330 := hb (x 4 3 && x 4 12)
                      have b14331 := hb (x 3 4 && x 3 13)
                      have b14332 := hb (x 2 5 && x 2 14)
                      clear * - r14325 b14326 b14327 b14328 b14329 b14330 b14331 b14332 d14248 d14288 d14320 g82 g83 d12422
                      omega
                    have d14333 : (x 4 12).toNat = 1 := by
                      have r14334 := hand2 (x 4 3) (x 4 12)
                      have b14335 := hb (x 4 12)
                      have b14336 := hb (x 4 3 && x 4 12)
                      clear * - r14334 b14335 b14336 d14324
                      omega
                    have d14337 : (x 3 13).toNat = 0 := by
                      have r14338 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e14339 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                      have e14340 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                      have b14341 := hb (x 1 3)
                      have b14342 := hb (x 2 2)
                      have b14343 := hb (x 3 13)
                      have b14344 := hb (x 4 12)
                      clear * - r14338 e14339 e14340 b14341 b14342 b14343 b14344 d14333 f12663
                      omega
                    have d14345 : (x 3 3 && x 3 13).toNat = 0 := by
                      have r14346 := hand2 (x 3 3) (x 3 13)
                      have b14347 := hb (x 3 13)
                      have b14348 := hb (x 3 3 && x 3 13)
                      clear * - r14346 b14347 b14348 d14337
                      omega
                    have d14349 : (x 4 2 && x 4 12).toNat = 1 := by
                      have r14350 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b14351 := hb (x 1 5)
                      have b14352 := hb (x 6 10)
                      have b14353 := hb (x 5 1 && x 5 11)
                      have b14354 := hb (x 4 2 && x 4 12)
                      have b14355 := hb (x 3 3 && x 3 13)
                      have b14356 := hb (x 2 4 && x 2 14)
                      clear * - r14350 b14351 b14352 b14353 b14354 b14355 b14356 d14272 d14316 d14345 d12492 d12516
                      omega
                    have d14357 : (x 4 2).toNat = 1 := by
                      have r14358 := hand1 (x 4 2) (x 4 12)
                      have b14359 := hb (x 4 2)
                      have b14360 := hb (x 4 2 && x 4 12)
                      clear * - r14358 b14359 b14360 d14349
                      omega
                    have d14361 : (x 6 12).toNat = 0 := by
                      have r14362 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e14363 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                      have e14364 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                      have b14365 := hb (x 3 3)
                      have b14366 := hb (x 4 2)
                      have b14367 := hb (x 5 13)
                      have b14368 := hb (x 6 12)
                      clear * - r14362 e14363 e14364 b14365 b14366 b14367 b14368 d14357
                      omega
                    have d14369 : (x 5 13).toNat = 0 := by
                      have r14370 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e14371 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                      have e14372 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                      have b14373 := hb (x 3 3)
                      have b14374 := hb (x 4 2)
                      have b14375 := hb (x 5 13)
                      have b14376 := hb (x 6 12)
                      clear * - r14370 e14371 e14372 b14373 b14374 b14375 b14376 d14361 d14357
                      omega
                    have d14377 : (x 3 5).toNat = 0 := by
                      have r14378 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
                      have b14379 := hb (x 3 5)
                      have b14380 := hb (x 3 13)
                      clear * - r14378 b14379 b14380 d14337
                      omega
                    have d14381 : (x 2 1 && x 2 14).toNat = 1 := by
                      have r14382 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b14383 := hb (x 1 2)
                      have b14384 := hb (x 3 13)
                      have b14385 := hb (x 2 1 && x 2 14)
                      clear * - r14382 b14383 b14384 b14385 d14337 g17
                      omega
                    have d14386 : (x 2 1).toNat = 1 := by
                      have r14387 := hand1 (x 2 1) (x 2 14)
                      have b14388 := hb (x 2 1)
                      have b14389 := hb (x 2 1 && x 2 14)
                      clear * - r14387 b14388 b14389 d14381
                      omega
                    have d14390 : (x 3 14).toNat = 0 := by
                      have r14391 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b14392 := hb (x 2 1)
                      have b14393 := hb (x 3 14)
                      clear * - r14391 b14392 b14393 d14386
                      omega
                    have d14394 : (x 3 2).toNat = 0 := by
                      have r14395 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
                      have b14396 := hb (x 3 2)
                      have b14397 := hb (x 3 14)
                      clear * - r14395 b14396 b14397 d14390
                      omega
                    have d14398 : (x 4 1 && x 4 14).toNat = 1 := by
                      have r14399 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b14400 := hb (x 3 2)
                      have b14401 := hb (x 5 13)
                      have b14402 := hb (x 4 1 && x 4 14)
                      clear * - r14399 b14400 b14401 b14402 d14369 d14394
                      omega
                    have d14403 : (x 4 1).toNat = 1 := by
                      have r14404 := hand1 (x 4 1) (x 4 14)
                      have b14405 := hb (x 4 1)
                      have b14406 := hb (x 4 1 && x 4 14)
                      clear * - r14404 b14405 b14406 d14398
                      omega
                    have d14407 : (x 5 14).toNat = 0 := by
                      have r14408 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b14409 := hb (x 4 1)
                      have b14410 := hb (x 5 14)
                      clear * - r14408 b14409 b14410 d14403
                      omega
                    have d14411 : (x 5 3 && x 5 14).toNat = 0 := by
                      have r14412 := hand2 (x 5 3) (x 5 14)
                      have b14413 := hb (x 5 14)
                      have b14414 := hb (x 5 3 && x 5 14)
                      clear * - r14412 b14413 b14414 d14407
                      omega
                    have d14415 : (x 5 6).toNat = 0 := by
                      have r14416 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
                      have b14417 := hb (x 5 6)
                      have b14418 := hb (x 5 14)
                      clear * - r14416 b14417 b14418 d14407
                      omega
                    have d14419 : (x 5 6 && x 5 11).toNat = 0 := by
                      have r14420 := hand1 (x 5 6) (x 5 11)
                      have b14421 := hb (x 5 6)
                      have b14422 := hb (x 5 6 && x 5 11)
                      clear * - r14420 b14421 b14422 d14415
                      omega
                    have d14423 : (x 5 2).toNat = 0 := by
                      have r14424 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
                      have b14425 := hb (x 5 2)
                      have b14426 := hb (x 5 14)
                      clear * - r14424 b14425 b14426 d14407
                      omega
                    have d14427 : (x 5 10).toNat = 0 := by
                      have r14428 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
                      have b14429 := hb (x 5 2)
                      have b14430 := hb (x 5 10)
                      clear * - r14428 b14429 b14430 d14423
                      omega
                    have d14431 : (x 5 3 && x 5 10).toNat = 0 := by
                      have r14432 := hand2 (x 5 3) (x 5 10)
                      have b14433 := hb (x 5 10)
                      have b14434 := hb (x 5 3 && x 5 10)
                      clear * - r14432 b14433 b14434 d14427
                      omega
                    have d14435 : (x 4 1 && x 4 11).toNat = 1 := by
                      have r14436 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b14437 := hb (x 0 5)
                      have b14438 := hb (x 5 10)
                      have b14439 := hb (x 4 1 && x 4 11)
                      have b14440 := hb (x 3 2 && x 3 12)
                      have b14441 := hb (x 2 3 && x 2 13)
                      have b14442 := hb (x 1 4 && x 1 14)
                      clear * - r14436 b14437 b14438 b14439 b14440 b14441 b14442 d14427 g86 g87 d12410 g14
                      omega
                    have d14443 : (x 4 11).toNat = 1 := by
                      have r14444 := hand2 (x 4 1) (x 4 11)
                      have b14445 := hb (x 4 11)
                      have b14446 := hb (x 4 1 && x 4 11)
                      clear * - r14444 b14445 b14446 d14435
                      omega
                    have d14447 : (x 4 3).toNat = 1 := by
                      have r14448 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
                      have b14449 := hb (x 4 3)
                      have b14450 := hb (x 4 11)
                      clear * - r14448 b14449 b14450 d14443
                      omega
                    have d14451 : (x 7 12).toNat = 0 := by
                      have r14452 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e14453 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                      have e14454 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                      have b14455 := hb (x 4 3)
                      have b14456 := hb (x 5 2)
                      have b14457 := hb (x 6 13)
                      have b14458 := hb (x 7 12)
                      clear * - r14452 e14453 e14454 b14455 b14456 b14457 b14458 d14423 d14447
                      omega
                    have d14459 : (x 7 1 && x 7 12).toNat = 0 := by
                      have r14460 := hand2 (x 7 1) (x 7 12)
                      have b14461 := hb (x 7 12)
                      have b14462 := hb (x 7 1 && x 7 12)
                      clear * - r14460 b14461 b14462 d14451
                      omega
                    have d14463 : (x 7 4).toNat = 0 := by
                      have r14464 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
                      have b14465 := hb (x 7 4)
                      have b14466 := hb (x 7 12)
                      clear * - r14464 b14465 b14466 d14451
                      omega
                    have d14467 : (x 6 13).toNat = 0 := by
                      have r14468 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e14469 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                      have e14470 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                      have b14471 := hb (x 4 3)
                      have b14472 := hb (x 5 2)
                      have b14473 := hb (x 6 13)
                      have b14474 := hb (x 7 12)
                      clear * - r14468 e14469 e14470 b14471 b14472 b14473 b14474 d14451 d14423 d14447
                      omega
                    have d14475 : (x 6 2 && x 6 13).toNat = 0 := by
                      have r14476 := hand2 (x 6 2) (x 6 13)
                      have b14477 := hb (x 6 13)
                      have b14478 := hb (x 6 2 && x 6 13)
                      clear * - r14476 b14477 b14478 d14467
                      omega
                    have d14479 : (x 6 5).toNat = 0 := by
                      have r14480 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
                      have b14481 := hb (x 6 5)
                      have b14482 := hb (x 6 13)
                      clear * - r14480 b14481 b14482 d14467
                      omega
                    have d14483 : (x 5 7 && x 5 11).toNat = 0 := by
                      have r14484 := hand2 (x 5 7) (x 5 11)
                      have b14485 := hb (x 5 11)
                      have b14486 := hb (x 5 7 && x 5 11)
                      clear * - r14484 b14485 b14486 d14300
                      omega
                    have d14487 : (x 4 4).toNat = 0 := by
                      have r14488 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e14489 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                      have e14490 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                      have e14491 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                      have e14492 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                      have e14493 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                      have e14494 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                      have b14495 := hb (x 1 7)
                      have b14496 := hb (x 2 6)
                      have b14497 := hb (x 3 5)
                      have b14498 := hb (x 4 4)
                      have b14499 := hb (x 5 11)
                      have b14500 := hb (x 6 10)
                      have b14501 := hb (x 7 9)
                      have b14502 := hb (x 8 8)
                      clear * - r14488 e14489 e14490 e14491 e14492 e14493 e14494 b14495 b14496 b14497 b14498 b14499 b14500 b14501 b14502 d14224 d14248 d14272 d14300 d14377 f14223
                      omega
                    have d14503 : (x 4 4 && x 4 11).toNat = 0 := by
                      have r14504 := hand1 (x 4 4) (x 4 11)
                      have b14505 := hb (x 4 4)
                      have b14506 := hb (x 4 4 && x 4 11)
                      clear * - r14504 b14505 b14506 d14487
                      omega
                    have d14507 : (x 8 11).toNat = 1 := by
                      have r14508 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b14509 := hb (x 4 4)
                      have b14510 := hb (x 8 11)
                      have b14511 := hb (x 7 1 && x 7 12)
                      have b14512 := hb (x 6 2 && x 6 13)
                      have b14513 := hb (x 5 3 && x 5 14)
                      clear * - r14508 b14509 b14510 b14511 b14512 b14513 d14459 d14475 d14411 d14487
                      omega
                    have d14514 : (x 8 3).toNat = 1 := by
                      have r14515 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
                      have b14516 := hb (x 8 3)
                      have b14517 := hb (x 8 11)
                      clear * - r14515 b14516 b14517 d14507
                      omega
                    have d14518 : (x 11 12).toNat = 0 := by
                      have r14519 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e14520 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                      have e14521 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                      have b14522 := hb (x 8 3)
                      have b14523 := hb (x 9 2)
                      have b14524 := hb (x 10 13)
                      have b14525 := hb (x 11 12)
                      clear * - r14519 e14520 e14521 b14522 b14523 b14524 b14525 d14514
                      omega
                    have d14526 : (x 11 4).toNat = 0 := by
                      have r14527 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
                      have b14528 := hb (x 11 4)
                      have b14529 := hb (x 11 12)
                      clear * - r14527 b14528 b14529 d14518
                      omega
                    have d14530 : (x 11 4 && x 11 13).toNat = 0 := by
                      have r14531 := hand1 (x 11 4) (x 11 13)
                      have b14532 := hb (x 11 4)
                      have b14533 := hb (x 11 4 && x 11 13)
                      clear * - r14531 b14532 b14533 d14526
                      omega
                    have d14534 : (x 10 13).toNat = 0 := by
                      have r14535 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e14536 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                      have e14537 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                      have b14538 := hb (x 8 3)
                      have b14539 := hb (x 9 2)
                      have b14540 := hb (x 10 13)
                      have b14541 := hb (x 11 12)
                      clear * - r14535 e14536 e14537 b14538 b14539 b14540 b14541 d14518 d14514
                      omega
                    have d14542 : (x 10 5).toNat = 0 := by
                      have r14543 : (x 10 5).toNat ≤ (x 10 13).toNat := himp _ _ (hp5 10)
                      have b14544 := hb (x 10 5)
                      have b14545 := hb (x 10 13)
                      clear * - r14543 b14544 b14545 d14534
                      omega
                    have d14546 : (x 10 5 && x 10 14).toNat = 0 := by
                      have r14547 := hand1 (x 10 5) (x 10 14)
                      have b14548 := hb (x 10 5)
                      have b14549 := hb (x 10 5 && x 10 14)
                      clear * - r14547 b14548 b14549 d14542
                      omega
                    have d14550 : (x 9 2).toNat = 0 := by
                      have r14551 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e14552 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                      have e14553 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                      have b14554 := hb (x 8 3)
                      have b14555 := hb (x 9 2)
                      have b14556 := hb (x 10 13)
                      have b14557 := hb (x 11 12)
                      clear * - r14551 e14552 e14553 b14554 b14555 b14556 b14557 d14518 d14534 d14514
                      omega
                    have d14558 : (x 9 2 && x 9 7).toNat = 0 := by
                      have r14559 := hand1 (x 9 2) (x 9 7)
                      have b14560 := hb (x 9 2)
                      have b14561 := hb (x 9 2 && x 9 7)
                      clear * - r14559 b14560 b14561 d14550
                      omega
                    have d14562 : (x 9 10).toNat = 0 := by
                      have r14563 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
                      have b14564 := hb (x 9 2)
                      have b14565 := hb (x 9 10)
                      clear * - r14563 b14564 b14565 d14550
                      omega
                    have d14566 : (x 11 8).toNat = 0 := by
                      have r14567 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e14568 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
                      have e14569 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
                      have e14570 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
                      have e14571 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
                      have e14572 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
                      have e14573 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
                      have b14574 := hb (x 4 7)
                      have b14575 := hb (x 5 6)
                      have b14576 := hb (x 6 5)
                      have b14577 := hb (x 7 4)
                      have b14578 := hb (x 8 11)
                      have b14579 := hb (x 9 10)
                      have b14580 := hb (x 10 9)
                      have b14581 := hb (x 11 8)
                      clear * - r14567 e14568 e14569 e14570 e14571 e14572 e14573 b14574 b14575 b14576 b14577 b14578 b14579 b14580 b14581 d14562 d14507 d14463 d14479 d14415
                      omega
                    have d14582 : (x 10 9).toNat = 0 := by
                      have r14583 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e14584 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
                      have e14585 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
                      have e14586 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
                      have e14587 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
                      have e14588 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
                      have e14589 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
                      have b14590 := hb (x 4 7)
                      have b14591 := hb (x 5 6)
                      have b14592 := hb (x 6 5)
                      have b14593 := hb (x 7 4)
                      have b14594 := hb (x 8 11)
                      have b14595 := hb (x 9 10)
                      have b14596 := hb (x 10 9)
                      have b14597 := hb (x 11 8)
                      clear * - r14583 e14584 e14585 e14586 e14587 e14588 e14589 b14590 b14591 b14592 b14593 b14594 b14595 b14596 b14597 d14566 d14562 d14507 d14463 d14479 d14415
                      omega
                    have d14598 : (x 4 7).toNat = 0 := by
                      have r14599 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e14600 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
                      have e14601 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
                      have e14602 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
                      have e14603 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
                      have e14604 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
                      have e14605 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
                      have b14606 := hb (x 4 7)
                      have b14607 := hb (x 5 6)
                      have b14608 := hb (x 6 5)
                      have b14609 := hb (x 7 4)
                      have b14610 := hb (x 8 11)
                      have b14611 := hb (x 9 10)
                      have b14612 := hb (x 10 9)
                      have b14613 := hb (x 11 8)
                      clear * - r14599 e14600 e14601 e14602 e14603 e14604 e14605 b14606 b14607 b14608 b14609 b14610 b14611 b14612 b14613 d14566 d14582 d14562 d14507 d14463 d14479 d14415
                      omega
                    have d14614 : (x 4 7 && x 4 12).toNat = 0 := by
                      have r14615 := hand1 (x 4 7) (x 4 12)
                      have b14616 := hb (x 4 7)
                      have b14617 := hb (x 4 7 && x 4 12)
                      clear * - r14615 b14616 b14617 d14598
                      omega
                    have d14618 : (x 7 8).toNat = 0 := by
                      have r14619 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e14620 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
                      have e14621 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
                      have e14622 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
                      have e14623 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
                      have e14624 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
                      have e14625 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
                      have b14626 := hb (x 0 7)
                      have b14627 := hb (x 1 6)
                      have b14628 := hb (x 2 5)
                      have b14629 := hb (x 3 4)
                      have b14630 := hb (x 4 11)
                      have b14631 := hb (x 5 10)
                      have b14632 := hb (x 6 9)
                      have b14633 := hb (x 7 8)
                      clear * - r14619 e14620 e14621 e14622 e14623 e14624 e14625 b14626 b14627 b14628 b14629 b14630 b14631 b14632 b14633 d14427 d14443 g24 g20 d12422 f12615
                      omega
                    have d14634 : (x 7 1 && x 7 8).toNat = 0 := by
                      have r14635 := hand2 (x 7 1) (x 7 8)
                      have b14636 := hb (x 7 8)
                      have b14637 := hb (x 7 1 && x 7 8)
                      clear * - r14635 b14636 b14637 d14618
                      omega
                    have d14638 : (x 6 9).toNat = 0 := by
                      have r14639 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e14640 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
                      have e14641 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
                      have e14642 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
                      have e14643 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
                      have e14644 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
                      have e14645 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
                      have b14646 := hb (x 0 7)
                      have b14647 := hb (x 1 6)
                      have b14648 := hb (x 2 5)
                      have b14649 := hb (x 3 4)
                      have b14650 := hb (x 4 11)
                      have b14651 := hb (x 5 10)
                      have b14652 := hb (x 6 9)
                      have b14653 := hb (x 7 8)
                      clear * - r14639 e14640 e14641 e14642 e14643 e14644 e14645 b14646 b14647 b14648 b14649 b14650 b14651 b14652 b14653 d14618 d14427 d14443 g24 g20 d12422 f12615
                      omega
                    have d14654 : (x 6 2 && x 6 9).toNat = 0 := by
                      have r14655 := hand2 (x 6 2) (x 6 9)
                      have b14656 := hb (x 6 9)
                      have b14657 := hb (x 6 2 && x 6 9)
                      clear * - r14655 b14656 b14657 d14638
                      omega
                    have d14658 : (x 8 7).toNat = 1 := by
                      have r14659 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := by have q := hcov7 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b14660 := hb (x 0 8)
                      have b14661 := hb (x 8 7)
                      have b14662 := hb (x 7 1 && x 7 8)
                      have b14663 := hb (x 6 2 && x 6 9)
                      have b14664 := hb (x 5 3 && x 5 10)
                      have b14665 := hb (x 4 4 && x 4 11)
                      have b14666 := hb (x 3 5 && x 3 12)
                      have b14667 := hb (x 2 6 && x 2 13)
                      have b14668 := hb (x 1 7 && x 1 14)
                      clear * - r14659 b14660 b14661 b14662 b14663 b14664 b14665 b14666 b14667 b14668 d14634 d14654 d14431 d14503 g72 g73 d12418 f12633
                      omega
                    have d14669 : (x 15 8).toNat = 0 := by
                      have r14670 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e14671 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                      have e14672 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                      have e14673 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                      have e14674 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                      have e14675 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                      have e14676 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                      have b14677 := hb (x 8 7)
                      have b14678 := hb (x 9 6)
                      have b14679 := hb (x 10 5)
                      have b14680 := hb (x 11 4)
                      have b14681 := hb (x 12 11)
                      have b14682 := hb (x 13 10)
                      have b14683 := hb (x 14 9)
                      have b14684 := hb (x 15 8)
                      clear * - r14670 e14671 e14672 e14673 e14674 e14675 e14676 b14677 b14678 b14679 b14680 b14681 b14682 b14683 b14684 d14526 d14542 d14658
                      omega
                    have d14685 : (x 14 9).toNat = 0 := by
                      have r14686 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e14687 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                      have e14688 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                      have e14689 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                      have e14690 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                      have e14691 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                      have e14692 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                      have b14693 := hb (x 8 7)
                      have b14694 := hb (x 9 6)
                      have b14695 := hb (x 10 5)
                      have b14696 := hb (x 11 4)
                      have b14697 := hb (x 12 11)
                      have b14698 := hb (x 13 10)
                      have b14699 := hb (x 14 9)
                      have b14700 := hb (x 15 8)
                      clear * - r14686 e14687 e14688 e14689 e14690 e14691 e14692 b14693 b14694 b14695 b14696 b14697 b14698 b14699 b14700 d14669 d14526 d14542 d14658
                      omega
                    have d14701 : (x 13 10).toNat = 0 := by
                      have r14702 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e14703 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                      have e14704 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                      have e14705 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                      have e14706 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                      have e14707 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                      have e14708 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                      have b14709 := hb (x 8 7)
                      have b14710 := hb (x 9 6)
                      have b14711 := hb (x 10 5)
                      have b14712 := hb (x 11 4)
                      have b14713 := hb (x 12 11)
                      have b14714 := hb (x 13 10)
                      have b14715 := hb (x 14 9)
                      have b14716 := hb (x 15 8)
                      clear * - r14702 e14703 e14704 e14705 e14706 e14707 e14708 b14709 b14710 b14711 b14712 b14713 b14714 b14715 b14716 d14669 d14685 d14526 d14542 d14658
                      omega
                    have d14717 : (x 12 11).toNat = 0 := by
                      have r14718 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e14719 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                      have e14720 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                      have e14721 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                      have e14722 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                      have e14723 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                      have e14724 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                      have b14725 := hb (x 8 7)
                      have b14726 := hb (x 9 6)
                      have b14727 := hb (x 10 5)
                      have b14728 := hb (x 11 4)
                      have b14729 := hb (x 12 11)
                      have b14730 := hb (x 13 10)
                      have b14731 := hb (x 14 9)
                      have b14732 := hb (x 15 8)
                      clear * - r14718 e14719 e14720 e14721 e14722 e14723 e14724 b14725 b14726 b14727 b14728 b14729 b14730 b14731 b14732 d14669 d14685 d14701 d14526 d14542 d14658
                      omega
                    have d14733 : (x 9 6).toNat = 0 := by
                      have r14734 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e14735 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                      have e14736 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                      have e14737 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                      have e14738 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                      have e14739 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                      have e14740 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                      have b14741 := hb (x 8 7)
                      have b14742 := hb (x 9 6)
                      have b14743 := hb (x 10 5)
                      have b14744 := hb (x 11 4)
                      have b14745 := hb (x 12 11)
                      have b14746 := hb (x 13 10)
                      have b14747 := hb (x 14 9)
                      have b14748 := hb (x 15 8)
                      clear * - r14734 e14735 e14736 e14737 e14738 e14739 e14740 b14741 b14742 b14743 b14744 b14745 b14746 b14747 b14748 d14669 d14685 d14701 d14717 d14526 d14542 d14658
                      omega
                    have r14749 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e14750 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
                    have e14751 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
                    have e14752 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
                    have e14753 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
                    have e14754 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
                    have e14755 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
                    have r14756 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e14757 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
                    have e14758 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
                    have r14759 : 1 ≤ (x 12 4).toNat + (x 11 1 && x 11 5).toNat + (x 10 2 && x 10 6).toNat + (x 9 3 && x 9 7).toNat + (x 8 4 && x 8 8).toNat + (x 7 5 && x 7 9).toNat + (x 6 6 && x 6 10).toNat + (x 5 7 && x 5 11).toNat + (x 4 8 && x 4 12).toNat + (x 3 9 && x 3 13).toNat + (x 2 10 && x 2 14).toNat + (x 1 11).toNat := by have q := hcov4 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e14760 : (x 11 1 && x 11 5).toNat = (x 11 5).toNat := handr _ _ (fun h => hp13 11 (hp5 11 (h)))
                    have e14761 : (x 2 10 && x 2 14).toNat = (x 2 10).toNat := handl _ _ (fun h => hp2 2 (hp10 2 (h)))
                    have r14762 : 1 ≤ (x 11 5).toNat + (x 10 1 && x 10 6).toNat + (x 9 2 && x 9 7).toNat + (x 8 3 && x 8 8).toNat + (x 7 4 && x 7 9).toNat + (x 6 5 && x 6 10).toNat + (x 5 6 && x 5 11).toNat + (x 4 7 && x 4 12).toNat + (x 3 8 && x 3 13).toNat + (x 2 9 && x 2 14).toNat + (x 1 10).toNat := by have q := hcov5 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r14763 : 1 ≤ (x 15 9).toNat + (x 14 1 && x 14 10).toNat + (x 13 2 && x 13 11).toNat + (x 12 3 && x 12 12).toNat + (x 11 4 && x 11 13).toNat + (x 10 5 && x 10 14).toNat + (x 9 6).toNat := by have q := hcov9 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r14764 : (x 11 5).toNat ≤ (x 11 13).toNat := himp _ _ (hp5 11)
                    have r14765 := hand1 (x 10 2) (x 10 6)
                    have r14766 := hand1 (x 9 3) (x 9 7)
                    have r14767 := hand2 (x 10 1) (x 10 6)
                    have r14768 := hand2 (x 14 1) (x 14 10)
                    have r14769 := hand2 (x 13 2) (x 13 11)
                    have r14770 := hand2 (x 12 3) (x 12 12)
                    linarith only [r14749, e14750, e14751, e14752, e14753, e14754, e14755, r14756, e14757, e14758, r14759, e14760, e14761, r14762, r14763, r14764, r14765, r14766, r14767, r14768, r14769, r14770, g18, g19, g22, d14733, d14244, d14268, d14296, d14483, g47, g48, d14558, d14240, d14264, d14292, d14419, d14614, g58, g59, d14530, d14546]
                · have f14809 : (x (-1) 7).toNat = 1 := by rw [h12670]; rfl
                  have d14810 : (x 6 8).toNat = 0 := by
                    have r14811 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e14812 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                    have e14813 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                    have e14814 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                    have e14815 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                    have e14816 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                    have e14817 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                    have b14818 := hb (x (-1) 7)
                    have b14819 := hb (x 0 6)
                    have b14820 := hb (x 1 5)
                    have b14821 := hb (x 2 4)
                    have b14822 := hb (x 3 11)
                    have b14823 := hb (x 4 10)
                    have b14824 := hb (x 5 9)
                    have b14825 := hb (x 6 8)
                    clear * - r14811 e14812 e14813 e14814 e14815 e14816 e14817 b14818 b14819 b14820 b14821 b14822 b14823 b14824 b14825 d12488 d12516 f12597 f14809
                    omega
                  have d14826 : (x 5 9).toNat = 0 := by
                    have r14827 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e14828 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                    have e14829 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                    have e14830 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                    have e14831 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                    have e14832 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                    have e14833 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                    have b14834 := hb (x (-1) 7)
                    have b14835 := hb (x 0 6)
                    have b14836 := hb (x 1 5)
                    have b14837 := hb (x 2 4)
                    have b14838 := hb (x 3 11)
                    have b14839 := hb (x 4 10)
                    have b14840 := hb (x 5 9)
                    have b14841 := hb (x 6 8)
                    clear * - r14827 e14828 e14829 e14830 e14831 e14832 e14833 b14834 b14835 b14836 b14837 b14838 b14839 b14840 b14841 d14810 d12488 d12516 f12597 f14809
                    omega
                  have d14842 : (x 4 10).toNat = 0 := by
                    have r14843 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e14844 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                    have e14845 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                    have e14846 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                    have e14847 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                    have e14848 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                    have e14849 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                    have b14850 := hb (x (-1) 7)
                    have b14851 := hb (x 0 6)
                    have b14852 := hb (x 1 5)
                    have b14853 := hb (x 2 4)
                    have b14854 := hb (x 3 11)
                    have b14855 := hb (x 4 10)
                    have b14856 := hb (x 5 9)
                    have b14857 := hb (x 6 8)
                    clear * - r14843 e14844 e14845 e14846 e14847 e14848 e14849 b14850 b14851 b14852 b14853 b14854 b14855 b14856 b14857 d14810 d14826 d12488 d12516 f12597 f14809
                    omega
                  have d14858 : (x 4 1 && x 4 10).toNat = 0 := by
                    have r14859 := hand2 (x 4 1) (x 4 10)
                    have b14860 := hb (x 4 10)
                    have b14861 := hb (x 4 1 && x 4 10)
                    clear * - r14859 b14860 b14861 d14842
                    omega
                  have d14862 : (x 3 2 && x 3 11).toNat = 1 := by
                    have r14863 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b14864 := hb (x (-1) 6)
                    have b14865 := hb (x 5 9)
                    have b14866 := hb (x 4 1 && x 4 10)
                    have b14867 := hb (x 3 2 && x 3 11)
                    have b14868 := hb (x 2 3 && x 2 12)
                    have b14869 := hb (x 1 4 && x 1 13)
                    have b14870 := hb (x 0 5 && x 0 14)
                    clear * - r14863 b14864 b14865 b14866 b14867 b14868 b14869 b14870 d14826 d14858 d12480 d12508 g79 f12669
                    omega
                  have d14871 : (x 3 11).toNat = 1 := by
                    have r14872 := hand2 (x 3 2) (x 3 11)
                    have b14873 := hb (x 3 11)
                    have b14874 := hb (x 3 2 && x 3 11)
                    clear * - r14872 b14873 b14874 d14862
                    omega
                  have r14875 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e14876 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                  have e14877 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                  have e14878 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                  have e14879 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                  have e14880 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                  have e14881 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                  have b14882 := hb (x (-1) 7)
                  have b14883 := hb (x 0 6)
                  have b14884 := hb (x 1 5)
                  have b14885 := hb (x 2 4)
                  have b14886 := hb (x 3 11)
                  have b14887 := hb (x 4 10)
                  have b14888 := hb (x 5 9)
                  have b14889 := hb (x 6 8)
                  linarith only [r14875, e14876, e14877, e14878, e14879, e14880, e14881, b14882, b14883, b14884, b14885, b14886, b14887, b14888, b14889, d14810, d14826, d14842, d14871, d12488, d12516, f12597, f14809]
              · have f14890 : (x (-1) 6).toNat = 1 := by rw [h12668]; rfl
                have d14891 : (x (-1) 14).toNat = 1 := by
                  have r14892 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
                  have b14893 := hb (x (-1) 6)
                  have b14894 := hb (x (-1) 14)
                  clear * - r14892 b14893 b14894 f14890
                  omega
                have d14895 : (x (-2) 1).toNat = 0 := by
                  have r14896 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b14897 := hb (x (-2) 1)
                  have b14898 := hb (x (-1) 14)
                  clear * - r14896 b14897 b14898 d14891
                  omega
                have d14899 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
                  have r14900 := hand1 (x (-2) 1) (x (-2) 14)
                  have b14901 := hb (x (-2) 1)
                  have b14902 := hb (x (-2) 1 && x (-2) 14)
                  clear * - r14900 b14901 b14902 d14895
                  omega
                have d14903 : (x (-2) 13).toNat = 0 := by
                  have r14904 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
                  have b14905 := hb (x (-2) 1)
                  have b14906 := hb (x (-2) 13)
                  clear * - r14904 b14905 b14906 d14895
                  omega
                have d14907 : (x (-2) 9).toNat = 0 := by
                  have r14908 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
                  have b14909 := hb (x (-2) 1)
                  have b14910 := hb (x (-2) 9)
                  clear * - r14908 b14909 b14910 d14895
                  omega
                have d14911 : (x (-3) 2).toNat = 1 := by
                  have r14912 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b14913 := hb (x (-3) 2)
                  have b14914 := hb (x (-1) 13)
                  have b14915 := hb (x (-2) 1 && x (-2) 14)
                  clear * - r14912 b14913 b14914 b14915 g10 d14899
                  omega
                have d14916 : (x (-1) 12).toNat = 0 := by
                  have r14917 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e14918 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                  have e14919 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                  have b14920 := hb (x (-4) 3)
                  have b14921 := hb (x (-3) 2)
                  have b14922 := hb (x (-2) 13)
                  have b14923 := hb (x (-1) 12)
                  clear * - r14917 e14918 e14919 b14920 b14921 b14922 b14923 d14903 d14911
                  omega
                have d14924 : (x (-4) 3).toNat = 0 := by
                  have r14925 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e14926 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                  have e14927 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                  have b14928 := hb (x (-4) 3)
                  have b14929 := hb (x (-3) 2)
                  have b14930 := hb (x (-2) 13)
                  have b14931 := hb (x (-1) 12)
                  clear * - r14925 e14926 e14927 b14928 b14929 b14930 b14931 d14916 d14903 d14911
                  omega
                have d14932 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
                  have r14933 := hand1 (x (-4) 3) (x (-4) 12)
                  have b14934 := hb (x (-4) 3)
                  have b14935 := hb (x (-4) 3 && x (-4) 12)
                  clear * - r14933 b14934 b14935 d14924
                  omega
                have d14936 : (x (-4) 11).toNat = 0 := by
                  have r14937 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
                  have b14938 := hb (x (-4) 3)
                  have b14939 := hb (x (-4) 11)
                  clear * - r14937 b14938 b14939 d14924
                  omega
                have d14940 : (x 5 8).toNat = 0 := by
                  have r14941 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e14942 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                  have e14943 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                  have e14944 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                  have e14945 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                  have e14946 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                  have e14947 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                  have b14948 := hb (x (-2) 7)
                  have b14949 := hb (x (-1) 6)
                  have b14950 := hb (x 0 5)
                  have b14951 := hb (x 1 4)
                  have b14952 := hb (x 2 11)
                  have b14953 := hb (x 3 10)
                  have b14954 := hb (x 4 9)
                  have b14955 := hb (x 5 8)
                  clear * - r14941 e14942 e14943 e14944 e14945 e14946 e14947 b14948 b14949 b14950 b14951 b14952 b14953 b14954 b14955 d12552 g14 f14890
                  omega
                have d14956 : (x 5 2 && x 5 8).toNat = 0 := by
                  have r14957 := hand2 (x 5 2) (x 5 8)
                  have b14958 := hb (x 5 8)
                  have b14959 := hb (x 5 2 && x 5 8)
                  clear * - r14957 b14958 b14959 d14940
                  omega
                have d14960 : (x 5 4 && x 5 8).toNat = 0 := by
                  have r14961 := hand2 (x 5 4) (x 5 8)
                  have b14962 := hb (x 5 8)
                  have b14963 := hb (x 5 4 && x 5 8)
                  clear * - r14961 b14962 b14963 d14940
                  omega
                have d14964 : (x 4 9).toNat = 0 := by
                  have r14965 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e14966 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                  have e14967 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                  have e14968 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                  have e14969 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                  have e14970 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                  have e14971 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                  have b14972 := hb (x (-2) 7)
                  have b14973 := hb (x (-1) 6)
                  have b14974 := hb (x 0 5)
                  have b14975 := hb (x 1 4)
                  have b14976 := hb (x 2 11)
                  have b14977 := hb (x 3 10)
                  have b14978 := hb (x 4 9)
                  have b14979 := hb (x 5 8)
                  clear * - r14965 e14966 e14967 e14968 e14969 e14970 e14971 b14972 b14973 b14974 b14975 b14976 b14977 b14978 b14979 d14940 d12552 g14 f14890
                  omega
                have d14980 : (x 4 3 && x 4 9).toNat = 0 := by
                  have r14981 := hand2 (x 4 3) (x 4 9)
                  have b14982 := hb (x 4 9)
                  have b14983 := hb (x 4 3 && x 4 9)
                  clear * - r14981 b14982 b14983 d14964
                  omega
                have d14984 : (x 4 5 && x 4 9).toNat = 0 := by
                  have r14985 := hand2 (x 4 5) (x 4 9)
                  have b14986 := hb (x 4 9)
                  have b14987 := hb (x 4 5 && x 4 9)
                  clear * - r14985 b14986 b14987 d14964
                  omega
                have d14988 : (x 3 10).toNat = 0 := by
                  have r14989 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e14990 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                  have e14991 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                  have e14992 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                  have e14993 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                  have e14994 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                  have e14995 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                  have b14996 := hb (x (-2) 7)
                  have b14997 := hb (x (-1) 6)
                  have b14998 := hb (x 0 5)
                  have b14999 := hb (x 1 4)
                  have b15000 := hb (x 2 11)
                  have b15001 := hb (x 3 10)
                  have b15002 := hb (x 4 9)
                  have b15003 := hb (x 5 8)
                  clear * - r14989 e14990 e14991 e14992 e14993 e14994 e14995 b14996 b14997 b14998 b14999 b15000 b15001 b15002 b15003 d14940 d14964 d12552 g14 f14890
                  omega
                have d15004 : (x 3 6 && x 3 10).toNat = 0 := by
                  have r15005 := hand2 (x 3 6) (x 3 10)
                  have b15006 := hb (x 3 10)
                  have b15007 := hb (x 3 6 && x 3 10)
                  clear * - r15005 b15006 b15007 d14988
                  omega
                have d15008 : (x 2 11).toNat = 0 := by
                  have r15009 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e15010 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                  have e15011 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                  have e15012 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                  have e15013 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                  have e15014 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                  have e15015 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                  have b15016 := hb (x (-2) 7)
                  have b15017 := hb (x (-1) 6)
                  have b15018 := hb (x 0 5)
                  have b15019 := hb (x 1 4)
                  have b15020 := hb (x 2 11)
                  have b15021 := hb (x 3 10)
                  have b15022 := hb (x 4 9)
                  have b15023 := hb (x 5 8)
                  clear * - r15009 e15010 e15011 e15012 e15013 e15014 e15015 b15016 b15017 b15018 b15019 b15020 b15021 b15022 b15023 d14940 d14964 d14988 d12552 g14 f14890
                  omega
                have d15024 : (x 2 7 && x 2 11).toNat = 0 := by
                  have r15025 := hand2 (x 2 7) (x 2 11)
                  have b15026 := hb (x 2 11)
                  have b15027 := hb (x 2 7 && x 2 11)
                  clear * - r15025 b15026 b15027 d15008
                  omega
                have r15028 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15029 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e15030 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e15031 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e15032 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e15033 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e15034 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have r15035 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15036 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                have e15037 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                have e15038 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                have e15039 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                have e15040 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                have e15041 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                have r15042 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15043 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                have e15044 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                have r15045 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15046 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                have e15047 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                have r15048 : 1 ≤ (x 9 4).toNat + (x 8 1 && x 8 5).toNat + (x 7 2 && x 7 6).toNat + (x 6 3 && x 6 7).toNat + (x 5 4 && x 5 8).toNat + (x 4 5 && x 4 9).toNat + (x 3 6 && x 3 10).toNat + (x 2 7 && x 2 11).toNat + (x 1 8 && x 1 12).toNat + (x 0 9 && x 0 13).toNat + (x (-1) 10 && x (-1) 14).toNat + (x (-2) 11).toNat := by have q := hcov4 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15049 : (x 8 1 && x 8 5).toNat = (x 8 5).toNat := handr _ _ (fun h => hp13 8 (hp5 8 (h)))
                have e15050 : (x (-1) 10 && x (-1) 14).toNat = (x (-1) 10).toNat := handl _ _ (fun h => hp2 (-1) (hp10 (-1) (h)))
                have r15051 : 1 ≤ (x 7 6).toNat + (x 6 1 && x 6 7).toNat + (x 5 2 && x 5 8).toNat + (x 4 3 && x 4 9).toNat + (x 3 4 && x 3 10).toNat + (x 2 5 && x 2 11).toNat + (x 1 6 && x 1 12).toNat + (x 0 7 && x 0 13).toNat + (x (-1) 8 && x (-1) 14).toNat + (x (-2) 9).toNat := by have q := hcov6 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r15052 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r15053 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r15054 : 1 ≤ (x 11 10).toNat + (x 10 1 && x 10 11).toNat + (x 9 2 && x 9 12).toNat + (x 8 3 && x 8 13).toNat + (x 7 4 && x 7 14).toNat + (x 6 5).toNat := by have q := hcov10 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r15055 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
                have r15056 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
                have r15057 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
                have r15058 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
                have r15059 := hand1 (x 7 2) (x 7 6)
                have r15060 := hand1 (x 6 3) (x 6 7)
                have r15061 := hand2 (x 6 1) (x 6 7)
                have r15062 := hand1 (x (-1) 8) (x (-1) 14)
                have r15063 := hand1 (x (-5) 4) (x (-5) 13)
                have r15064 := hand1 (x (-6) 5) (x (-6) 14)
                have r15065 := hand2 (x 4 1) (x 4 11)
                have r15066 := hand2 (x 10 1) (x 10 11)
                have r15067 := hand2 (x 9 2) (x 9 12)
                have r15068 := hand2 (x 8 3) (x 8 13)
                have r15069 := hand1 (x 7 4) (x 7 14)
                linarith only [r15028, e15029, e15030, e15031, e15032, e15033, e15034, r15035, e15036, e15037, e15038, e15039, e15040, e15041, r15042, e15043, e15044, r15045, e15046, e15047, r15048, e15049, e15050, r15051, r15052, r15053, r15054, r15055, r15056, r15057, r15058, r15059, r15060, r15061, r15062, r15063, r15064, r15065, r15066, r15067, r15068, r15069, d14936, d14907, d12588, d12455, d12568, g14, d14960, d14984, d15004, d15024, d12548, d12652, d14956, d14980, g68, g69, d12426, d12616, g74, g75, d14932, g86, g87, d12410]
            · have f15131 : (x 1 3).toNat = 1 := by rw [h12662]; rfl
              have d15132 : (x 4 12).toNat = 0 := by
                have r15133 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15134 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e15135 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b15136 := hb (x 1 3)
                have b15137 := hb (x 2 2)
                have b15138 := hb (x 3 13)
                have b15139 := hb (x 4 12)
                clear * - r15133 e15134 e15135 b15136 b15137 b15138 b15139 f15131
                omega
              have d15140 : (x 4 1 && x 4 12).toNat = 0 := by
                have r15141 := hand2 (x 4 1) (x 4 12)
                have b15142 := hb (x 4 12)
                have b15143 := hb (x 4 1 && x 4 12)
                clear * - r15141 b15142 b15143 d15132
                omega
              have d15144 : (x 4 4).toNat = 0 := by
                have r15145 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
                have b15146 := hb (x 4 4)
                have b15147 := hb (x 4 12)
                clear * - r15145 b15146 b15147 d15132
                omega
              have d15148 : (x 3 13).toNat = 0 := by
                have r15149 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15150 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e15151 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b15152 := hb (x 1 3)
                have b15153 := hb (x 2 2)
                have b15154 := hb (x 3 13)
                have b15155 := hb (x 4 12)
                clear * - r15149 e15150 e15151 b15152 b15153 b15154 b15155 d15132 f15131
                omega
              have d15156 : (x 3 2 && x 3 13).toNat = 0 := by
                have r15157 := hand2 (x 3 2) (x 3 13)
                have b15158 := hb (x 3 13)
                have b15159 := hb (x 3 2 && x 3 13)
                clear * - r15157 b15158 b15159 d15148
                omega
              have d15160 : (x 2 1 && x 2 14).toNat = 1 := by
                have r15161 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b15162 := hb (x 1 2)
                have b15163 := hb (x 3 13)
                have b15164 := hb (x 2 1 && x 2 14)
                clear * - r15161 b15162 b15163 b15164 d15148 g17
                omega
              have d15165 : (x 2 1).toNat = 1 := by
                have r15166 := hand1 (x 2 1) (x 2 14)
                have b15167 := hb (x 2 1)
                have b15168 := hb (x 2 1 && x 2 14)
                clear * - r15166 b15167 b15168 d15160
                omega
              have d15169 : (x 3 14).toNat = 0 := by
                have r15170 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b15171 := hb (x 2 1)
                have b15172 := hb (x 3 14)
                clear * - r15170 b15171 b15172 d15165
                omega
              have d15173 : (x 3 1 && x 3 14).toNat = 0 := by
                have r15174 := hand2 (x 3 1) (x 3 14)
                have b15175 := hb (x 3 14)
                have b15176 := hb (x 3 1 && x 3 14)
                clear * - r15174 b15175 b15176 d15169
                omega
              have d15177 : (x 3 2).toNat = 0 := by
                have r15178 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
                have b15179 := hb (x 3 2)
                have b15180 := hb (x 3 14)
                clear * - r15178 b15179 b15180 d15169
                omega
              have d15181 : (x 2 2).toNat = 0 := by
                have r15182 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15183 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e15184 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b15185 := hb (x 1 3)
                have b15186 := hb (x 2 2)
                have b15187 := hb (x 3 13)
                have b15188 := hb (x 4 12)
                clear * - r15182 e15183 e15184 b15185 b15186 b15187 b15188 d15132 d15148 f15131
                omega
              have d15189 : (x 4 13).toNat = 1 := by
                have r15190 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b15191 := hb (x 2 2)
                have b15192 := hb (x 4 13)
                have b15193 := hb (x 3 1 && x 3 14)
                clear * - r15190 b15191 b15192 b15193 d15173 d15181
                omega
              have d15194 : (x 4 1).toNat = 1 := by
                have r15195 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
                have b15196 := hb (x 4 1)
                have b15197 := hb (x 4 13)
                clear * - r15195 b15196 b15197 d15189
                omega
              have d15198 : (x 5 14).toNat = 0 := by
                have r15199 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b15200 := hb (x 4 1)
                have b15201 := hb (x 5 14)
                clear * - r15199 b15200 b15201 d15194
                omega
              have d15202 : (x 5 3 && x 5 14).toNat = 0 := by
                have r15203 := hand2 (x 5 3) (x 5 14)
                have b15204 := hb (x 5 14)
                have b15205 := hb (x 5 3 && x 5 14)
                clear * - r15203 b15204 b15205 d15198
                omega
              have d15206 : (x 5 2).toNat = 0 := by
                have r15207 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
                have b15208 := hb (x 5 2)
                have b15209 := hb (x 5 14)
                clear * - r15207 b15208 b15209 d15198
                omega
              have d15210 : (x 5 12).toNat = 0 := by
                have r15211 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15212 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                have e15213 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                have b15214 := hb (x 2 3)
                have b15215 := hb (x 3 2)
                have b15216 := hb (x 4 13)
                have b15217 := hb (x 5 12)
                clear * - r15211 e15212 e15213 b15214 b15215 b15216 b15217 d15189 d15177
                omega
              have d15218 : (x 5 4).toNat = 0 := by
                have r15219 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
                have b15220 := hb (x 5 4)
                have b15221 := hb (x 5 12)
                clear * - r15219 b15220 b15221 d15210
                omega
              have d15222 : (x 2 3).toNat = 0 := by
                have r15223 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15224 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                have e15225 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                have b15226 := hb (x 2 3)
                have b15227 := hb (x 3 2)
                have b15228 := hb (x 4 13)
                have b15229 := hb (x 5 12)
                clear * - r15223 e15224 e15225 b15226 b15227 b15228 b15229 d15210 d15189 d15177
                omega
              have d15230 : (x 2 3 && x 2 14).toNat = 0 := by
                have r15231 := hand1 (x 2 3) (x 2 14)
                have b15232 := hb (x 2 3)
                have b15233 := hb (x 2 3 && x 2 14)
                clear * - r15231 b15232 b15233 d15222
                omega
              have d15234 : (x 5 11).toNat = 1 := by
                have r15235 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b15236 := hb (x 1 4)
                have b15237 := hb (x 5 11)
                have b15238 := hb (x 4 1 && x 4 12)
                have b15239 := hb (x 3 2 && x 3 13)
                have b15240 := hb (x 2 3 && x 2 14)
                clear * - r15235 b15236 b15237 b15238 b15239 b15240 d15140 d15156 d15230 d12552
                omega
              have d15241 : (x 5 3).toNat = 1 := by
                have r15242 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
                have b15243 := hb (x 5 3)
                have b15244 := hb (x 5 11)
                clear * - r15242 b15243 b15244 d15234
                omega
              have d15245 : (x 8 12).toNat = 0 := by
                have r15246 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15247 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                have e15248 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                have b15249 := hb (x 5 3)
                have b15250 := hb (x 6 2)
                have b15251 := hb (x 7 13)
                have b15252 := hb (x 8 12)
                clear * - r15246 e15247 e15248 b15249 b15250 b15251 b15252 d15241
                omega
              have d15253 : (x 8 1 && x 8 12).toNat = 0 := by
                have r15254 := hand2 (x 8 1) (x 8 12)
                have b15255 := hb (x 8 12)
                have b15256 := hb (x 8 1 && x 8 12)
                clear * - r15254 b15255 b15256 d15245
                omega
              have d15257 : (x 8 4).toNat = 0 := by
                have r15258 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
                have b15259 := hb (x 8 4)
                have b15260 := hb (x 8 12)
                clear * - r15258 b15259 b15260 d15245
                omega
              have d15261 : (x 7 13).toNat = 0 := by
                have r15262 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15263 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                have e15264 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                have b15265 := hb (x 5 3)
                have b15266 := hb (x 6 2)
                have b15267 := hb (x 7 13)
                have b15268 := hb (x 8 12)
                clear * - r15262 e15263 e15264 b15265 b15266 b15267 b15268 d15245 d15241
                omega
              have d15269 : (x 7 2 && x 7 13).toNat = 0 := by
                have r15270 := hand2 (x 7 2) (x 7 13)
                have b15271 := hb (x 7 13)
                have b15272 := hb (x 7 2 && x 7 13)
                clear * - r15270 b15271 b15272 d15261
                omega
              have d15273 : (x 6 1 && x 6 14).toNat = 1 := by
                have r15274 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b15275 := hb (x 5 2)
                have b15276 := hb (x 7 13)
                have b15277 := hb (x 6 1 && x 6 14)
                clear * - r15274 b15275 b15276 b15277 d15261 d15206
                omega
              have d15278 : (x 6 1).toNat = 1 := by
                have r15279 := hand1 (x 6 1) (x 6 14)
                have b15280 := hb (x 6 1)
                have b15281 := hb (x 6 1 && x 6 14)
                clear * - r15279 b15280 b15281 d15273
                omega
              have d15282 : (x 7 14).toNat = 0 := by
                have r15283 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b15284 := hb (x 6 1)
                have b15285 := hb (x 7 14)
                clear * - r15283 b15284 b15285 d15278
                omega
              have d15286 : (x 7 1 && x 7 14).toNat = 0 := by
                have r15287 := hand2 (x 7 1) (x 7 14)
                have b15288 := hb (x 7 14)
                have b15289 := hb (x 7 1 && x 7 14)
                clear * - r15287 b15288 b15289 d15282
                omega
              have d15290 : (x 7 2).toNat = 0 := by
                have r15291 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
                have b15292 := hb (x 7 2)
                have b15293 := hb (x 7 14)
                clear * - r15291 b15292 b15293 d15282
                omega
              have d15294 : (x 6 2).toNat = 0 := by
                have r15295 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15296 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                have e15297 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                have b15298 := hb (x 5 3)
                have b15299 := hb (x 6 2)
                have b15300 := hb (x 7 13)
                have b15301 := hb (x 8 12)
                clear * - r15295 e15296 e15297 b15298 b15299 b15300 b15301 d15245 d15261 d15241
                omega
              have d15302 : (x 6 2 && x 6 13).toNat = 0 := by
                have r15303 := hand1 (x 6 2) (x 6 13)
                have b15304 := hb (x 6 2)
                have b15305 := hb (x 6 2 && x 6 13)
                clear * - r15303 b15304 b15305 d15294
                omega
              have d15306 : (x 8 13).toNat = 1 := by
                have r15307 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b15308 := hb (x 6 2)
                have b15309 := hb (x 8 13)
                have b15310 := hb (x 7 1 && x 7 14)
                clear * - r15307 b15308 b15309 b15310 d15286 d15294
                omega
              have d15311 : (x 8 1).toNat = 1 := by
                have r15312 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
                have b15313 := hb (x 8 1)
                have b15314 := hb (x 8 13)
                clear * - r15312 b15313 b15314 d15306
                omega
              have d15315 : (x 9 14).toNat = 0 := by
                have r15316 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b15317 := hb (x 8 1)
                have b15318 := hb (x 9 14)
                clear * - r15316 b15317 b15318 d15311
                omega
              have d15319 : (x 9 3 && x 9 14).toNat = 0 := by
                have r15320 := hand2 (x 9 3) (x 9 14)
                have b15321 := hb (x 9 14)
                have b15322 := hb (x 9 3 && x 9 14)
                clear * - r15320 b15321 b15322 d15315
                omega
              have d15323 : (x 9 2).toNat = 0 := by
                have r15324 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
                have b15325 := hb (x 9 2)
                have b15326 := hb (x 9 14)
                clear * - r15324 b15325 b15326 d15315
                omega
              have d15327 : (x 9 12).toNat = 0 := by
                have r15328 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15329 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                have e15330 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                have b15331 := hb (x 6 3)
                have b15332 := hb (x 7 2)
                have b15333 := hb (x 8 13)
                have b15334 := hb (x 9 12)
                clear * - r15328 e15329 e15330 b15331 b15332 b15333 b15334 d15306 d15290
                omega
              have d15335 : (x 9 4).toNat = 0 := by
                have r15336 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
                have b15337 := hb (x 9 4)
                have b15338 := hb (x 9 12)
                clear * - r15336 b15337 b15338 d15327
                omega
              have d15339 : (x 6 3).toNat = 0 := by
                have r15340 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15341 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                have e15342 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                have b15343 := hb (x 6 3)
                have b15344 := hb (x 7 2)
                have b15345 := hb (x 8 13)
                have b15346 := hb (x 9 12)
                clear * - r15340 e15341 e15342 b15343 b15344 b15345 b15346 d15327 d15306 d15290
                omega
              have d15347 : (x 6 3 && x 6 14).toNat = 0 := by
                have r15348 := hand1 (x 6 3) (x 6 14)
                have b15349 := hb (x 6 3)
                have b15350 := hb (x 6 3 && x 6 14)
                clear * - r15348 b15349 b15350 d15339
                omega
              have d15351 : (x 9 11).toNat = 1 := by
                have r15352 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b15353 := hb (x 5 4)
                have b15354 := hb (x 9 11)
                have b15355 := hb (x 8 1 && x 8 12)
                have b15356 := hb (x 7 2 && x 7 13)
                have b15357 := hb (x 6 3 && x 6 14)
                clear * - r15352 b15353 b15354 b15355 b15356 b15357 d15253 d15269 d15347 d15218
                omega
              have d15358 : (x 9 3).toNat = 1 := by
                have r15359 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
                have b15360 := hb (x 9 3)
                have b15361 := hb (x 9 11)
                clear * - r15359 b15360 b15361 d15351
                omega
              have d15362 : (x 12 12).toNat = 0 := by
                have r15363 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15364 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
                have e15365 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
                have b15366 := hb (x 9 3)
                have b15367 := hb (x 10 2)
                have b15368 := hb (x 11 13)
                have b15369 := hb (x 12 12)
                clear * - r15363 e15364 e15365 b15366 b15367 b15368 b15369 d15358
                omega
              have d15370 : (x 12 1 && x 12 12).toNat = 0 := by
                have r15371 := hand2 (x 12 1) (x 12 12)
                have b15372 := hb (x 12 12)
                have b15373 := hb (x 12 1 && x 12 12)
                clear * - r15371 b15372 b15373 d15362
                omega
              have d15374 : (x 12 4).toNat = 0 := by
                have r15375 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
                have b15376 := hb (x 12 4)
                have b15377 := hb (x 12 12)
                clear * - r15375 b15376 b15377 d15362
                omega
              have d15378 : (x 11 13).toNat = 0 := by
                have r15379 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15380 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
                have e15381 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
                have b15382 := hb (x 9 3)
                have b15383 := hb (x 10 2)
                have b15384 := hb (x 11 13)
                have b15385 := hb (x 12 12)
                clear * - r15379 e15380 e15381 b15382 b15383 b15384 b15385 d15362 d15358
                omega
              have d15386 : (x 11 2 && x 11 13).toNat = 0 := by
                have r15387 := hand2 (x 11 2) (x 11 13)
                have b15388 := hb (x 11 13)
                have b15389 := hb (x 11 2 && x 11 13)
                clear * - r15387 b15388 b15389 d15378
                omega
              have d15390 : (x 10 1 && x 10 14).toNat = 1 := by
                have r15391 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b15392 := hb (x 9 2)
                have b15393 := hb (x 11 13)
                have b15394 := hb (x 10 1 && x 10 14)
                clear * - r15391 b15392 b15393 b15394 d15378 d15323
                omega
              have d15395 : (x 10 14).toNat = 1 := by
                have r15396 := hand2 (x 10 1) (x 10 14)
                have b15397 := hb (x 10 14)
                have b15398 := hb (x 10 1 && x 10 14)
                clear * - r15396 b15397 b15398 d15390
                omega
              have d15399 : (x 9 1).toNat = 0 := by
                have r15400 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b15401 := hb (x 9 1)
                have b15402 := hb (x 10 14)
                clear * - r15400 b15401 b15402 d15395
                omega
              have d15403 : (x 9 13).toNat = 0 := by
                have r15404 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
                have b15405 := hb (x 9 1)
                have b15406 := hb (x 9 13)
                clear * - r15404 b15405 b15406 d15399
                omega
              have d15407 : (x 8 1 && x 8 14).toNat = 1 := by
                have r15408 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b15409 := hb (x 7 2)
                have b15410 := hb (x 9 13)
                have b15411 := hb (x 8 1 && x 8 14)
                clear * - r15408 b15409 b15410 b15411 d15403 d15290
                omega
              have d15412 : (x 8 14).toNat = 1 := by
                have r15413 := hand2 (x 8 1) (x 8 14)
                have b15414 := hb (x 8 14)
                have b15415 := hb (x 8 1 && x 8 14)
                clear * - r15413 b15414 b15415 d15407
                omega
              have d15416 : (x 7 1).toNat = 0 := by
                have r15417 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b15418 := hb (x 7 1)
                have b15419 := hb (x 8 14)
                clear * - r15417 b15418 b15419 d15412
                omega
              have d15420 : (x 7 1 && x 7 12).toNat = 0 := by
                have r15421 := hand1 (x 7 1) (x 7 12)
                have b15422 := hb (x 7 1)
                have b15423 := hb (x 7 1 && x 7 12)
                clear * - r15421 b15422 b15423 d15416
                omega
              have d15424 : (x 8 11).toNat = 1 := by
                have r15425 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b15426 := hb (x 4 4)
                have b15427 := hb (x 8 11)
                have b15428 := hb (x 7 1 && x 7 12)
                have b15429 := hb (x 6 2 && x 6 13)
                have b15430 := hb (x 5 3 && x 5 14)
                clear * - r15425 b15426 b15427 b15428 b15429 b15430 d15420 d15302 d15202 d15144
                omega
              have d15431 : (x 8 3).toNat = 1 := by
                have r15432 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
                have b15433 := hb (x 8 3)
                have b15434 := hb (x 8 11)
                clear * - r15432 b15433 b15434 d15424
                omega
              have d15435 : (x 11 12).toNat = 0 := by
                have r15436 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15437 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                have e15438 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                have b15439 := hb (x 8 3)
                have b15440 := hb (x 9 2)
                have b15441 := hb (x 10 13)
                have b15442 := hb (x 11 12)
                clear * - r15436 e15437 e15438 b15439 b15440 b15441 b15442 d15323 d15431
                omega
              have d15443 : (x 11 1 && x 11 12).toNat = 0 := by
                have r15444 := hand2 (x 11 1) (x 11 12)
                have b15445 := hb (x 11 12)
                have b15446 := hb (x 11 1 && x 11 12)
                clear * - r15444 b15445 b15446 d15435
                omega
              have d15447 : (x 10 13).toNat = 0 := by
                have r15448 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15449 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                have e15450 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                have b15451 := hb (x 8 3)
                have b15452 := hb (x 9 2)
                have b15453 := hb (x 10 13)
                have b15454 := hb (x 11 12)
                clear * - r15448 e15449 e15450 b15451 b15452 b15453 b15454 d15435 d15323 d15431
                omega
              have d15455 : (x 10 2 && x 10 13).toNat = 0 := by
                have r15456 := hand2 (x 10 2) (x 10 13)
                have b15457 := hb (x 10 13)
                have b15458 := hb (x 10 2 && x 10 13)
                clear * - r15456 b15457 b15458 d15447
                omega
              have d15459 : (x 12 11).toNat = 1 := by
                have r15460 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b15461 := hb (x 8 4)
                have b15462 := hb (x 12 11)
                have b15463 := hb (x 11 1 && x 11 12)
                have b15464 := hb (x 10 2 && x 10 13)
                have b15465 := hb (x 9 3 && x 9 14)
                clear * - r15460 b15461 b15462 b15463 b15464 b15465 d15443 d15455 d15319 d15257
                omega
              have d15466 : (x 12 3).toNat = 1 := by
                have r15467 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
                have b15468 := hb (x 12 3)
                have b15469 := hb (x 12 11)
                clear * - r15467 b15468 b15469 d15459
                omega
              have d15470 : (x 15 12).toNat = 0 := by
                have r15471 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15472 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
                have e15473 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
                have b15474 := hb (x 12 3)
                have b15475 := hb (x 13 2)
                have b15476 := hb (x 14 13)
                have b15477 := hb (x 15 12)
                clear * - r15471 e15472 e15473 b15474 b15475 b15476 b15477 d15466
                omega
              have d15478 : (x 15 1 && x 15 12).toNat = 0 := by
                have r15479 := hand2 (x 15 1) (x 15 12)
                have b15480 := hb (x 15 12)
                have b15481 := hb (x 15 1 && x 15 12)
                clear * - r15479 b15480 b15481 d15470
                omega
              have d15482 : (x 14 13).toNat = 0 := by
                have r15483 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15484 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
                have e15485 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
                have b15486 := hb (x 12 3)
                have b15487 := hb (x 13 2)
                have b15488 := hb (x 14 13)
                have b15489 := hb (x 15 12)
                clear * - r15483 e15484 e15485 b15486 b15487 b15488 b15489 d15470 d15466
                omega
              have d15490 : (x 14 2 && x 14 13).toNat = 0 := by
                have r15491 := hand2 (x 14 2) (x 14 13)
                have b15492 := hb (x 14 13)
                have b15493 := hb (x 14 2 && x 14 13)
                clear * - r15491 b15492 b15493 d15482
                omega
              have d15494 : (x 13 2).toNat = 0 := by
                have r15495 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15496 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
                have e15497 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
                have b15498 := hb (x 12 3)
                have b15499 := hb (x 13 2)
                have b15500 := hb (x 14 13)
                have b15501 := hb (x 15 12)
                clear * - r15495 e15496 e15497 b15498 b15499 b15500 b15501 d15470 d15482 d15466
                omega
              have d15502 : (x 10 1).toNat = 1 := by
                have r15503 := hand1 (x 10 1) (x 10 14)
                have b15504 := hb (x 10 1)
                have b15505 := hb (x 10 1 && x 10 14)
                clear * - r15503 b15504 b15505 d15390
                omega
              have d15506 : (x 11 14).toNat = 0 := by
                have r15507 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b15508 := hb (x 10 1)
                have b15509 := hb (x 11 14)
                clear * - r15507 b15508 b15509 d15502
                omega
              have d15510 : (x 11 1 && x 11 14).toNat = 0 := by
                have r15511 := hand2 (x 11 1) (x 11 14)
                have b15512 := hb (x 11 14)
                have b15513 := hb (x 11 1 && x 11 14)
                clear * - r15511 b15512 b15513 d15506
                omega
              have d15514 : (x 11 2).toNat = 0 := by
                have r15515 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
                have b15516 := hb (x 11 2)
                have b15517 := hb (x 11 14)
                clear * - r15515 b15516 b15517 d15506
                omega
              have d15518 : (x 10 2).toNat = 0 := by
                have r15519 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15520 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
                have e15521 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
                have b15522 := hb (x 9 3)
                have b15523 := hb (x 10 2)
                have b15524 := hb (x 11 13)
                have b15525 := hb (x 12 12)
                clear * - r15519 e15520 e15521 b15522 b15523 b15524 b15525 d15362 d15378 d15358
                omega
              have d15526 : (x 12 13).toNat = 1 := by
                have r15527 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b15528 := hb (x 10 2)
                have b15529 := hb (x 12 13)
                have b15530 := hb (x 11 1 && x 11 14)
                clear * - r15527 b15528 b15529 b15530 d15510 d15518
                omega
              have d15531 : (x 12 1).toNat = 1 := by
                have r15532 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
                have b15533 := hb (x 12 1)
                have b15534 := hb (x 12 13)
                clear * - r15532 b15533 b15534 d15526
                omega
              have d15535 : (x 13 14).toNat = 0 := by
                have r15536 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b15537 := hb (x 12 1)
                have b15538 := hb (x 13 14)
                clear * - r15536 b15537 b15538 d15531
                omega
              have d15539 : (x 13 1 && x 13 14).toNat = 0 := by
                have r15540 := hand2 (x 13 1) (x 13 14)
                have b15541 := hb (x 13 14)
                have b15542 := hb (x 13 1 && x 13 14)
                clear * - r15540 b15541 b15542 d15535
                omega
              have d15543 : (x 12 2).toNat = 1 := by
                have r15544 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b15545 := hb (x 12 2)
                have b15546 := hb (x 14 13)
                have b15547 := hb (x 13 1 && x 13 14)
                clear * - r15544 b15545 b15546 b15547 d15482 d15539
                omega
              have d15548 : (x 14 12).toNat = 0 := by
                have r15549 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15550 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
                have e15551 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
                have b15552 := hb (x 11 3)
                have b15553 := hb (x 12 2)
                have b15554 := hb (x 13 13)
                have b15555 := hb (x 14 12)
                clear * - r15549 e15550 e15551 b15552 b15553 b15554 b15555 d15543
                omega
              have d15556 : (x 14 4).toNat = 0 := by
                have r15557 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
                have b15558 := hb (x 14 4)
                have b15559 := hb (x 14 12)
                clear * - r15557 b15558 b15559 d15548
                omega
              have d15560 : (x 14 4 && x 14 14).toNat = 0 := by
                have r15561 := hand1 (x 14 4) (x 14 14)
                have b15562 := hb (x 14 4)
                have b15563 := hb (x 14 4 && x 14 14)
                clear * - r15561 b15562 b15563 d15556
                omega
              have d15564 : (x 13 13).toNat = 0 := by
                have r15565 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15566 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
                have e15567 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
                have b15568 := hb (x 11 3)
                have b15569 := hb (x 12 2)
                have b15570 := hb (x 13 13)
                have b15571 := hb (x 14 12)
                clear * - r15565 e15566 e15567 b15568 b15569 b15570 b15571 d15548 d15543
                omega
              have d15572 : (x 13 5).toNat = 0 := by
                have r15573 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
                have b15574 := hb (x 13 5)
                have b15575 := hb (x 13 13)
                clear * - r15573 b15574 b15575 d15564
                omega
              have d15576 : (x 13 3 && x 13 14).toNat = 0 := by
                have r15577 := hand2 (x 13 3) (x 13 14)
                have b15578 := hb (x 13 14)
                have b15579 := hb (x 13 3 && x 13 14)
                clear * - r15577 b15578 b15579 d15535
                omega
              have d15580 : (x 16 11).toNat = 1 := by
                have r15581 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b15582 := hb (x 12 4)
                have b15583 := hb (x 16 11)
                have b15584 := hb (x 15 1 && x 15 12)
                have b15585 := hb (x 14 2 && x 14 13)
                have b15586 := hb (x 13 3 && x 13 14)
                clear * - r15581 b15582 b15583 b15584 b15585 b15586 d15478 d15490 d15576 d15374
                omega
              have d15587 : (x 16 3).toNat = 1 := by
                have r15588 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
                have b15589 := hb (x 16 3)
                have b15590 := hb (x 16 11)
                clear * - r15588 b15589 b15590 d15580
                omega
              have d15591 : (x 19 12).toNat = 0 := by
                have r15592 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15593 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
                have e15594 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
                have b15595 := hb (x 16 3)
                have b15596 := hb (x 17 2)
                have b15597 := hb (x 18 13)
                have b15598 := hb (x 19 12)
                clear * - r15592 e15593 e15594 b15595 b15596 b15597 b15598 d15587
                omega
              have d15599 : (x 18 13).toNat = 0 := by
                have r15600 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15601 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
                have e15602 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
                have b15603 := hb (x 16 3)
                have b15604 := hb (x 17 2)
                have b15605 := hb (x 18 13)
                have b15606 := hb (x 19 12)
                clear * - r15600 e15601 e15602 b15603 b15604 b15605 b15606 d15591 d15587
                omega
              have d15607 : (x 17 2).toNat = 0 := by
                have r15608 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15609 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
                have e15610 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
                have b15611 := hb (x 16 3)
                have b15612 := hb (x 17 2)
                have b15613 := hb (x 18 13)
                have b15614 := hb (x 19 12)
                clear * - r15608 e15609 e15610 b15611 b15612 b15613 b15614 d15591 d15599 d15587
                omega
              have d15615 : (x 13 12).toNat = 0 := by
                have r15616 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15617 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
                have e15618 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
                have b15619 := hb (x 10 3)
                have b15620 := hb (x 11 2)
                have b15621 := hb (x 12 13)
                have b15622 := hb (x 13 12)
                clear * - r15616 e15617 e15618 b15619 b15620 b15621 b15622 d15526 d15514
                omega
              have d15623 : (x 13 4).toNat = 0 := by
                have r15624 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
                have b15625 := hb (x 13 4)
                have b15626 := hb (x 13 12)
                clear * - r15624 b15625 b15626 d15615
                omega
              have d15627 : (x 10 3).toNat = 0 := by
                have r15628 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15629 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
                have e15630 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
                have b15631 := hb (x 10 3)
                have b15632 := hb (x 11 2)
                have b15633 := hb (x 12 13)
                have b15634 := hb (x 13 12)
                clear * - r15628 e15629 e15630 b15631 b15632 b15633 b15634 d15615 d15526 d15514
                omega
              have d15635 : (x 10 3 && x 10 14).toNat = 0 := by
                have r15636 := hand1 (x 10 3) (x 10 14)
                have b15637 := hb (x 10 3)
                have b15638 := hb (x 10 3 && x 10 14)
                clear * - r15636 b15637 b15638 d15627
                omega
              have d15639 : (x 13 11).toNat = 1 := by
                have r15640 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b15641 := hb (x 9 4)
                have b15642 := hb (x 13 11)
                have b15643 := hb (x 12 1 && x 12 12)
                have b15644 := hb (x 11 2 && x 11 13)
                have b15645 := hb (x 10 3 && x 10 14)
                clear * - r15640 b15641 b15642 b15643 b15644 b15645 d15370 d15386 d15635 d15335
                omega
              have d15646 : (x 13 3).toNat = 1 := by
                have r15647 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
                have b15648 := hb (x 13 3)
                have b15649 := hb (x 13 11)
                clear * - r15647 b15648 b15649 d15639
                omega
              have d15650 : (x 16 12).toNat = 0 := by
                have r15651 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15652 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                have e15653 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                have b15654 := hb (x 13 3)
                have b15655 := hb (x 14 2)
                have b15656 := hb (x 15 13)
                have b15657 := hb (x 16 12)
                clear * - r15651 e15652 e15653 b15654 b15655 b15656 b15657 d15646
                omega
              have d15658 : (x 16 1 && x 16 12).toNat = 0 := by
                have r15659 := hand2 (x 16 1) (x 16 12)
                have b15660 := hb (x 16 12)
                have b15661 := hb (x 16 1 && x 16 12)
                clear * - r15659 b15660 b15661 d15650
                omega
              have d15662 : (x 16 2 && x 16 12).toNat = 0 := by
                have r15663 := hand2 (x 16 2) (x 16 12)
                have b15664 := hb (x 16 12)
                have b15665 := hb (x 16 2 && x 16 12)
                clear * - r15663 b15664 b15665 d15650
                omega
              have d15666 : (x 15 13).toNat = 0 := by
                have r15667 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15668 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                have e15669 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                have b15670 := hb (x 13 3)
                have b15671 := hb (x 14 2)
                have b15672 := hb (x 15 13)
                have b15673 := hb (x 16 12)
                clear * - r15667 e15668 e15669 b15670 b15671 b15672 b15673 d15650 d15646
                omega
              have d15674 : (x 15 2 && x 15 13).toNat = 0 := by
                have r15675 := hand2 (x 15 2) (x 15 13)
                have b15676 := hb (x 15 13)
                have b15677 := hb (x 15 2 && x 15 13)
                clear * - r15675 b15676 b15677 d15666
                omega
              have d15678 : (x 15 3 && x 15 13).toNat = 0 := by
                have r15679 := hand2 (x 15 3) (x 15 13)
                have b15680 := hb (x 15 13)
                have b15681 := hb (x 15 3 && x 15 13)
                clear * - r15679 b15680 b15681 d15666
                omega
              have d15682 : (x 14 1 && x 14 14).toNat = 1 := by
                have r15683 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b15684 := hb (x 13 2)
                have b15685 := hb (x 15 13)
                have b15686 := hb (x 14 1 && x 14 14)
                clear * - r15683 b15684 b15685 b15686 d15666 d15494
                omega
              have d15687 : (x 14 1).toNat = 1 := by
                have r15688 := hand1 (x 14 1) (x 14 14)
                have b15689 := hb (x 14 1)
                have b15690 := hb (x 14 1 && x 14 14)
                clear * - r15688 b15689 b15690 d15682
                omega
              have d15691 : (x 15 14).toNat = 0 := by
                have r15692 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b15693 := hb (x 14 1)
                have b15694 := hb (x 15 14)
                clear * - r15692 b15693 b15694 d15687
                omega
              have d15695 : (x 15 1 && x 15 14).toNat = 0 := by
                have r15696 := hand2 (x 15 1) (x 15 14)
                have b15697 := hb (x 15 14)
                have b15698 := hb (x 15 1 && x 15 14)
                clear * - r15696 b15697 b15698 d15691
                omega
              have d15699 : (x 15 2).toNat = 0 := by
                have r15700 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
                have b15701 := hb (x 15 2)
                have b15702 := hb (x 15 14)
                clear * - r15700 b15701 b15702 d15691
                omega
              have d15703 : (x 14 2).toNat = 0 := by
                have r15704 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15705 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                have e15706 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                have b15707 := hb (x 13 3)
                have b15708 := hb (x 14 2)
                have b15709 := hb (x 15 13)
                have b15710 := hb (x 16 12)
                clear * - r15704 e15705 e15706 b15707 b15708 b15709 b15710 d15650 d15666 d15646
                omega
              have d15711 : (x 16 13).toNat = 1 := by
                have r15712 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b15713 := hb (x 14 2)
                have b15714 := hb (x 16 13)
                have b15715 := hb (x 15 1 && x 15 14)
                clear * - r15712 b15713 b15714 b15715 d15695 d15703
                omega
              have d15716 : (x 17 12).toNat = 0 := by
                have r15717 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15718 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                have e15719 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                have b15720 := hb (x 14 3)
                have b15721 := hb (x 15 2)
                have b15722 := hb (x 16 13)
                have b15723 := hb (x 17 12)
                clear * - r15717 e15718 e15719 b15720 b15721 b15722 b15723 d15711 d15699
                omega
              have d15724 : (x 14 3).toNat = 0 := by
                have r15725 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15726 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                have e15727 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                have b15728 := hb (x 14 3)
                have b15729 := hb (x 15 2)
                have b15730 := hb (x 16 13)
                have b15731 := hb (x 17 12)
                clear * - r15725 e15726 e15727 b15728 b15729 b15730 b15731 d15716 d15711 d15699
                omega
              have d15732 : (x 14 3 && x 14 14).toNat = 0 := by
                have r15733 := hand1 (x 14 3) (x 14 14)
                have b15734 := hb (x 14 3)
                have b15735 := hb (x 14 3 && x 14 14)
                clear * - r15733 b15734 b15735 d15724
                omega
              have d15736 : (x 17 11).toNat = 1 := by
                have r15737 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b15738 := hb (x 13 4)
                have b15739 := hb (x 17 11)
                have b15740 := hb (x 16 1 && x 16 12)
                have b15741 := hb (x 15 2 && x 15 13)
                have b15742 := hb (x 14 3 && x 14 14)
                clear * - r15737 b15738 b15739 b15740 b15741 b15742 d15658 d15674 d15732 d15623
                omega
              have d15743 : (x 17 3).toNat = 1 := by
                have r15744 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
                have b15745 := hb (x 17 3)
                have b15746 := hb (x 17 11)
                clear * - r15744 b15745 b15746 d15736
                omega
              have d15747 : (x 20 12).toNat = 0 := by
                have r15748 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15749 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
                have e15750 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
                have b15751 := hb (x 17 3)
                have b15752 := hb (x 18 2)
                have b15753 := hb (x 19 13)
                have b15754 := hb (x 20 12)
                clear * - r15748 e15749 e15750 b15751 b15752 b15753 b15754 d15743
                omega
              have d15755 : (x 19 13).toNat = 0 := by
                have r15756 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15757 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
                have e15758 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
                have b15759 := hb (x 17 3)
                have b15760 := hb (x 18 2)
                have b15761 := hb (x 19 13)
                have b15762 := hb (x 20 12)
                clear * - r15756 e15757 e15758 b15759 b15760 b15761 b15762 d15747 d15743
                omega
              have d15763 : (x 18 1 && x 18 14).toNat = 1 := by
                have r15764 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b15765 := hb (x 17 2)
                have b15766 := hb (x 19 13)
                have b15767 := hb (x 18 1 && x 18 14)
                clear * - r15764 b15765 b15766 b15767 d15755 d15607
                omega
              have d15768 : (x 18 14).toNat = 1 := by
                have r15769 := hand2 (x 18 1) (x 18 14)
                have b15770 := hb (x 18 14)
                have b15771 := hb (x 18 1 && x 18 14)
                clear * - r15769 b15770 b15771 d15763
                omega
              have d15772 : (x 17 1).toNat = 0 := by
                have r15773 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b15774 := hb (x 17 1)
                have b15775 := hb (x 18 14)
                clear * - r15773 b15774 b15775 d15768
                omega
              have d15776 : (x 17 1 && x 17 11).toNat = 0 := by
                have r15777 := hand1 (x 17 1) (x 17 11)
                have b15778 := hb (x 17 1)
                have b15779 := hb (x 17 1 && x 17 11)
                clear * - r15777 b15778 b15779 d15772
                omega
              have d15780 : (x 18 2).toNat = 0 := by
                have r15781 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e15782 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
                have e15783 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
                have b15784 := hb (x 17 3)
                have b15785 := hb (x 18 2)
                have b15786 := hb (x 19 13)
                have b15787 := hb (x 20 12)
                clear * - r15781 e15782 e15783 b15784 b15785 b15786 b15787 d15747 d15755 d15743
                omega
              have d15788 : (x 18 10).toNat = 0 := by
                have r15789 : (x 18 10).toNat ≤ (x 18 2).toNat := himp _ _ (hp10 18)
                have b15790 := hb (x 18 2)
                have b15791 := hb (x 18 10)
                clear * - r15789 b15790 b15791 d15780
                omega
              have r15792 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := by have q := hcov10 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b15793 := hb (x 13 5)
              have b15794 := hb (x 18 10)
              have b15795 := hb (x 17 1 && x 17 11)
              have b15796 := hb (x 16 2 && x 16 12)
              have b15797 := hb (x 15 3 && x 15 13)
              have b15798 := hb (x 14 4 && x 14 14)
              linarith only [r15792, b15793, b15794, b15795, b15796, b15797, b15798, d15788, d15776, d15662, d15678, d15560, d15572]
          · have f15799 : (x 1 1).toNat = 1 := by rw [h12656]; rfl
            have d15800 : (x 2 14).toNat = 0 := by
              have r15801 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b15802 := hb (x 1 1)
              have b15803 := hb (x 2 14)
              clear * - r15801 b15802 b15803 f15799
              omega
            have d15804 : (x 2 1 && x 2 14).toNat = 0 := by
              have r15805 := hand2 (x 2 1) (x 2 14)
              have b15806 := hb (x 2 14)
              have b15807 := hb (x 2 1 && x 2 14)
              clear * - r15805 b15806 b15807 d15800
              omega
            have d15808 : (x 2 6).toNat = 0 := by
              have r15809 : (x 2 6).toNat ≤ (x 2 14).toNat := himp _ _ (hp6 2)
              have b15810 := hb (x 2 6)
              have b15811 := hb (x 2 14)
              clear * - r15809 b15810 b15811 d15800
              omega
            have d15812 : (x 2 2 && x 2 6).toNat = 0 := by
              have r15813 := hand2 (x 2 2) (x 2 6)
              have b15814 := hb (x 2 6)
              have b15815 := hb (x 2 2 && x 2 6)
              clear * - r15813 b15814 b15815 d15808
              omega
            have d15816 : (x 2 2).toNat = 0 := by
              have r15817 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
              have b15818 := hb (x 2 2)
              have b15819 := hb (x 2 14)
              clear * - r15817 b15818 b15819 d15800
              omega
            have d15820 : (x 3 13).toNat = 1 := by
              have r15821 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b15822 := hb (x 1 2)
              have b15823 := hb (x 3 13)
              have b15824 := hb (x 2 1 && x 2 14)
              clear * - r15821 b15822 b15823 b15824 d15804 g17
              omega
            have d15825 : (x 3 1).toNat = 1 := by
              have r15826 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
              have b15827 := hb (x 3 1)
              have b15828 := hb (x 3 13)
              clear * - r15826 b15827 b15828 d15820
              omega
            have d15829 : (x 4 12).toNat = 0 := by
              have r15830 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e15831 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e15832 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b15833 := hb (x 1 3)
              have b15834 := hb (x 2 2)
              have b15835 := hb (x 3 13)
              have b15836 := hb (x 4 12)
              clear * - r15830 e15831 e15832 b15833 b15834 b15835 b15836 d15820 d15816
              omega
            have d15837 : (x 4 3 && x 4 12).toNat = 0 := by
              have r15838 := hand2 (x 4 3) (x 4 12)
              have b15839 := hb (x 4 12)
              have b15840 := hb (x 4 3 && x 4 12)
              clear * - r15838 b15839 b15840 d15829
              omega
            have d15841 : (x 4 4).toNat = 0 := by
              have r15842 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
              have b15843 := hb (x 4 4)
              have b15844 := hb (x 4 12)
              clear * - r15842 b15843 b15844 d15829
              omega
            have d15845 : (x 1 3).toNat = 0 := by
              have r15846 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e15847 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e15848 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b15849 := hb (x 1 3)
              have b15850 := hb (x 2 2)
              have b15851 := hb (x 3 13)
              have b15852 := hb (x 4 12)
              clear * - r15846 e15847 e15848 b15849 b15850 b15851 b15852 d15829 d15820 d15816
              omega
            have d15853 : (x 1 3 && x 1 7).toNat = 0 := by
              have r15854 := hand1 (x 1 3) (x 1 7)
              have b15855 := hb (x 1 3)
              have b15856 := hb (x 1 3 && x 1 7)
              clear * - r15854 b15855 b15856 d15845
              omega
            have r15857 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r15858 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r15859 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e15860 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e15861 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e15862 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e15863 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e15864 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e15865 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have r15866 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e15867 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
            have e15868 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
            have r15869 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e15870 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
            have e15871 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
            have r15872 : 1 ≤ (x 2 6).toNat + (x 1 1 && x 1 7).toNat + (x 0 2 && x 0 8).toNat + (x (-1) 3 && x (-1) 9).toNat + (x (-2) 4 && x (-2) 10).toNat + (x (-3) 5 && x (-3) 11).toNat + (x (-4) 6 && x (-4) 12).toNat + (x (-5) 7 && x (-5) 13).toNat + (x (-6) 8 && x (-6) 14).toNat + (x (-7) 9).toNat := by have q := hcov6 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r15873 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r15874 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r15875 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r15876 : (x (-11) 5).toNat ≤ (x (-11) 13).toNat := himp _ _ (hp5 (-11))
            have r15877 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
            have r15878 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
            have r15879 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
            have r15880 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
            have r15881 := hand1 (x (-4) 8) (x (-4) 12)
            have r15882 := hand1 (x (-5) 9) (x (-5) 13)
            have r15883 := hand2 (x 1 1) (x 1 7)
            have r15884 := hand1 (x (-4) 6) (x (-4) 12)
            have r15885 := hand1 (x (-5) 7) (x (-5) 13)
            have r15886 := hand1 (x (-6) 8) (x (-6) 14)
            have r15887 := hand2 (x 6 1) (x 6 10)
            have r15888 := hand2 (x 5 2) (x 5 11)
            have r15889 := hand2 (x (-7) 1) (x (-7) 11)
            have r15890 := hand2 (x (-8) 2) (x (-8) 12)
            have r15891 := hand2 (x (-9) 3) (x (-9) 13)
            have r15892 := hand2 (x (-10) 4) (x (-10) 14)
            have r15893 := hand1 (x (-4) 4) (x (-4) 14)
            linarith only [r15857, r15858, r15859, e15860, e15861, e15862, e15863, e15864, e15865, r15866, e15867, e15868, r15869, e15870, e15871, r15872, r15873, r15874, r15875, r15876, r15877, r15878, r15879, r15880, r15881, r15882, r15883, r15884, r15885, r15886, r15887, r15888, r15889, r15890, r15891, r15892, r15893, g2, g6, d12520, g9, d12430, g13, g15, f15799, d15845, d12422, d15816, d15808, d15825, d15841, d15812, d15853, d12646, g36, g37, g38, d12638, d12463, g61, g62, d15837, g82, g83, d12447, g84, g85]
        · have f15968 : (x 0 9).toNat = 1 := by rw [h12650]; rfl
          have d15969 : (x 1 8).toNat = 0 := by
            have r15970 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e15971 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
            have e15972 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
            have e15973 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
            have e15974 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
            have e15975 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
            have e15976 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
            have b15977 := hb (x (-6) 7)
            have b15978 := hb (x (-5) 6)
            have b15979 := hb (x (-4) 5)
            have b15980 := hb (x (-3) 4)
            have b15981 := hb (x (-2) 11)
            have b15982 := hb (x (-1) 10)
            have b15983 := hb (x 0 9)
            have b15984 := hb (x 1 8)
            clear * - r15970 e15971 e15972 e15973 e15974 e15975 e15976 b15977 b15978 b15979 b15980 b15981 b15982 b15983 b15984 f15968 d12568 d12588
            omega
          have d15985 : (x (-3) 4).toNat = 0 := by
            have r15986 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e15987 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
            have e15988 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
            have e15989 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
            have e15990 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
            have e15991 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
            have e15992 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
            have b15993 := hb (x (-6) 7)
            have b15994 := hb (x (-5) 6)
            have b15995 := hb (x (-4) 5)
            have b15996 := hb (x (-3) 4)
            have b15997 := hb (x (-2) 11)
            have b15998 := hb (x (-1) 10)
            have b15999 := hb (x 0 9)
            have b16000 := hb (x 1 8)
            clear * - r15986 e15987 e15988 e15989 e15990 e15991 e15992 b15993 b15994 b15995 b15996 b15997 b15998 b15999 b16000 d15969 f15968 d12568 d12588
            omega
          have d16001 : (x (-3) 4 && x (-3) 13).toNat = 0 := by
            have r16002 := hand1 (x (-3) 4) (x (-3) 13)
            have b16003 := hb (x (-3) 4)
            have b16004 := hb (x (-3) 4 && x (-3) 13)
            clear * - r16002 b16003 b16004 d15985
            omega
          have d16005 : (x (-3) 4 && x (-3) 9).toNat = 0 := by
            have r16006 := hand1 (x (-3) 4) (x (-3) 9)
            have b16007 := hb (x (-3) 4)
            have b16008 := hb (x (-3) 4 && x (-3) 9)
            clear * - r16006 b16007 b16008 d15985
            omega
          have d16009 : (x (-4) 5).toNat = 0 := by
            have r16010 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e16011 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
            have e16012 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
            have e16013 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
            have e16014 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
            have e16015 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
            have e16016 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
            have b16017 := hb (x (-6) 7)
            have b16018 := hb (x (-5) 6)
            have b16019 := hb (x (-4) 5)
            have b16020 := hb (x (-3) 4)
            have b16021 := hb (x (-2) 11)
            have b16022 := hb (x (-1) 10)
            have b16023 := hb (x 0 9)
            have b16024 := hb (x 1 8)
            clear * - r16010 e16011 e16012 e16013 e16014 e16015 e16016 b16017 b16018 b16019 b16020 b16021 b16022 b16023 b16024 d15969 f15968 d12568 d12588 d15985
            omega
          have d16025 : (x (-4) 5 && x (-4) 14).toNat = 0 := by
            have r16026 := hand1 (x (-4) 5) (x (-4) 14)
            have b16027 := hb (x (-4) 5)
            have b16028 := hb (x (-4) 5 && x (-4) 14)
            clear * - r16026 b16027 b16028 d16009
            omega
          have d16029 : (x (-4) 5 && x (-4) 12).toNat = 0 := by
            have r16030 := hand1 (x (-4) 5) (x (-4) 12)
            have b16031 := hb (x (-4) 5)
            have b16032 := hb (x (-4) 5 && x (-4) 12)
            clear * - r16030 b16031 b16032 d16009
            omega
          have d16033 : (x (-4) 5 && x (-4) 10).toNat = 0 := by
            have r16034 := hand1 (x (-4) 5) (x (-4) 10)
            have b16035 := hb (x (-4) 5)
            have b16036 := hb (x (-4) 5 && x (-4) 10)
            clear * - r16034 b16035 b16036 d16009
            omega
          have d16037 : (x (-5) 6).toNat = 0 := by
            have r16038 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e16039 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
            have e16040 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
            have e16041 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
            have e16042 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
            have e16043 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
            have e16044 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
            have b16045 := hb (x (-6) 7)
            have b16046 := hb (x (-5) 6)
            have b16047 := hb (x (-4) 5)
            have b16048 := hb (x (-3) 4)
            have b16049 := hb (x (-2) 11)
            have b16050 := hb (x (-1) 10)
            have b16051 := hb (x 0 9)
            have b16052 := hb (x 1 8)
            clear * - r16038 e16039 e16040 e16041 e16042 e16043 e16044 b16045 b16046 b16047 b16048 b16049 b16050 b16051 b16052 d15969 f15968 d12568 d12588 d15985 d16009
            omega
          have d16053 : (x (-5) 6 && x (-5) 13).toNat = 0 := by
            have r16054 := hand1 (x (-5) 6) (x (-5) 13)
            have b16055 := hb (x (-5) 6)
            have b16056 := hb (x (-5) 6 && x (-5) 13)
            clear * - r16054 b16055 b16056 d16037
            omega
          have d16057 : (x (-5) 6 && x (-5) 11).toNat = 0 := by
            have r16058 := hand1 (x (-5) 6) (x (-5) 11)
            have b16059 := hb (x (-5) 6)
            have b16060 := hb (x (-5) 6 && x (-5) 11)
            clear * - r16058 b16059 b16060 d16037
            omega
          have d16061 : (x 1 9).toNat = 1 := by
            have r16062 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b16063 := hb (x (-5) 6)
            have b16064 := hb (x 1 9)
            have b16065 := hb (x 0 1 && x 0 10)
            have b16066 := hb (x (-1) 2 && x (-1) 11)
            have b16067 := hb (x (-2) 3 && x (-2) 12)
            have b16068 := hb (x (-3) 4 && x (-3) 13)
            have b16069 := hb (x (-4) 5 && x (-4) 14)
            clear * - r16062 b16063 b16064 b16065 b16066 b16067 b16068 b16069 g78 d12536 d12580 d16001 d16025 d16037
            omega
          have d16070 : (x 1 1).toNat = 1 := by
            have r16071 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
            have b16072 := hb (x 1 1)
            have b16073 := hb (x 1 9)
            clear * - r16071 b16072 b16073 d16061
            omega
          have d16074 : (x 2 14).toNat = 0 := by
            have r16075 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b16076 := hb (x 1 1)
            have b16077 := hb (x 2 14)
            clear * - r16075 b16076 b16077 d16070
            omega
          have d16078 : (x 2 1 && x 2 14).toNat = 0 := by
            have r16079 := hand2 (x 2 1) (x 2 14)
            have b16080 := hb (x 2 14)
            have b16081 := hb (x 2 1 && x 2 14)
            clear * - r16079 b16080 b16081 d16074
            omega
          have d16082 : (x 3 13).toNat = 1 := by
            have r16083 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b16084 := hb (x 1 2)
            have b16085 := hb (x 3 13)
            have b16086 := hb (x 2 1 && x 2 14)
            clear * - r16083 b16084 b16085 b16086 d16078 g17
            omega
          have d16087 : (x 4 12).toNat = 0 := by
            have r16088 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e16089 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e16090 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b16091 := hb (x 1 3)
            have b16092 := hb (x 2 2)
            have b16093 := hb (x 3 13)
            have b16094 := hb (x 4 12)
            clear * - r16088 e16089 e16090 b16091 b16092 b16093 b16094 d16082
            omega
          have d16095 : (x 4 3 && x 4 12).toNat = 0 := by
            have r16096 := hand2 (x 4 3) (x 4 12)
            have b16097 := hb (x 4 12)
            have b16098 := hb (x 4 3 && x 4 12)
            clear * - r16096 b16097 b16098 d16087
            omega
          have d16099 : (x 4 4).toNat = 0 := by
            have r16100 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
            have b16101 := hb (x 4 4)
            have b16102 := hb (x 4 12)
            clear * - r16100 b16101 b16102 d16087
            omega
          have d16103 : (x 2 6).toNat = 0 := by
            have r16104 : (x 2 6).toNat ≤ (x 2 14).toNat := himp _ _ (hp6 2)
            have b16105 := hb (x 2 6)
            have b16106 := hb (x 2 14)
            clear * - r16104 b16105 b16106 d16074
            omega
          have d16107 : (x 2 8).toNat = 0 := by
            have r16108 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e16109 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
            have e16110 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
            have e16111 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
            have e16112 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
            have e16113 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
            have e16114 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
            have b16115 := hb (x (-5) 7)
            have b16116 := hb (x (-4) 6)
            have b16117 := hb (x (-3) 5)
            have b16118 := hb (x (-2) 4)
            have b16119 := hb (x (-1) 11)
            have b16120 := hb (x 0 10)
            have b16121 := hb (x 1 9)
            have b16122 := hb (x 2 8)
            clear * - r16108 e16109 e16110 e16111 e16112 e16113 e16114 b16115 b16116 b16117 b16118 b16119 b16120 b16121 b16122 d16061 g15 d12532
            omega
          have d16123 : (x (-2) 4).toNat = 0 := by
            have r16124 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e16125 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
            have e16126 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
            have e16127 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
            have e16128 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
            have e16129 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
            have e16130 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
            have b16131 := hb (x (-5) 7)
            have b16132 := hb (x (-4) 6)
            have b16133 := hb (x (-3) 5)
            have b16134 := hb (x (-2) 4)
            have b16135 := hb (x (-1) 11)
            have b16136 := hb (x 0 10)
            have b16137 := hb (x 1 9)
            have b16138 := hb (x 2 8)
            clear * - r16124 e16125 e16126 e16127 e16128 e16129 e16130 b16131 b16132 b16133 b16134 b16135 b16136 b16137 b16138 d16107 d16061 g15 d12532
            omega
          have d16139 : (x (-2) 4 && x (-2) 8).toNat = 0 := by
            have r16140 := hand1 (x (-2) 4) (x (-2) 8)
            have b16141 := hb (x (-2) 4)
            have b16142 := hb (x (-2) 4 && x (-2) 8)
            clear * - r16140 b16141 b16142 d16123
            omega
          have d16143 : (x (-3) 5).toNat = 0 := by
            have r16144 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e16145 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
            have e16146 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
            have e16147 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
            have e16148 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
            have e16149 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
            have e16150 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
            have b16151 := hb (x (-5) 7)
            have b16152 := hb (x (-4) 6)
            have b16153 := hb (x (-3) 5)
            have b16154 := hb (x (-2) 4)
            have b16155 := hb (x (-1) 11)
            have b16156 := hb (x 0 10)
            have b16157 := hb (x 1 9)
            have b16158 := hb (x 2 8)
            clear * - r16144 e16145 e16146 e16147 e16148 e16149 e16150 b16151 b16152 b16153 b16154 b16155 b16156 b16157 b16158 d16107 d16061 g15 d12532 d16123
            omega
          have d16159 : (x (-3) 5 && x (-3) 9).toNat = 0 := by
            have r16160 := hand1 (x (-3) 5) (x (-3) 9)
            have b16161 := hb (x (-3) 5)
            have b16162 := hb (x (-3) 5 && x (-3) 9)
            clear * - r16160 b16161 b16162 d16143
            omega
          have d16163 : (x (-4) 6).toNat = 0 := by
            have r16164 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e16165 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
            have e16166 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
            have e16167 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
            have e16168 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
            have e16169 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
            have e16170 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
            have b16171 := hb (x (-5) 7)
            have b16172 := hb (x (-4) 6)
            have b16173 := hb (x (-3) 5)
            have b16174 := hb (x (-2) 4)
            have b16175 := hb (x (-1) 11)
            have b16176 := hb (x 0 10)
            have b16177 := hb (x 1 9)
            have b16178 := hb (x 2 8)
            clear * - r16164 e16165 e16166 e16167 e16168 e16169 e16170 b16171 b16172 b16173 b16174 b16175 b16176 b16177 b16178 d16107 d16061 g15 d12532 d16123 d16143
            omega
          have d16179 : (x (-4) 6 && x (-4) 10).toNat = 0 := by
            have r16180 := hand1 (x (-4) 6) (x (-4) 10)
            have b16181 := hb (x (-4) 6)
            have b16182 := hb (x (-4) 6 && x (-4) 10)
            clear * - r16180 b16181 b16182 d16163
            omega
          have d16183 : (x (-5) 7).toNat = 0 := by
            have r16184 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e16185 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
            have e16186 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
            have e16187 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
            have e16188 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
            have e16189 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
            have e16190 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
            have b16191 := hb (x (-5) 7)
            have b16192 := hb (x (-4) 6)
            have b16193 := hb (x (-3) 5)
            have b16194 := hb (x (-2) 4)
            have b16195 := hb (x (-1) 11)
            have b16196 := hb (x 0 10)
            have b16197 := hb (x 1 9)
            have b16198 := hb (x 2 8)
            clear * - r16184 e16185 e16186 e16187 e16188 e16189 e16190 b16191 b16192 b16193 b16194 b16195 b16196 b16197 b16198 d16107 d16061 g15 d12532 d16123 d16143 d16163
            omega
          have d16199 : (x (-5) 7 && x (-5) 11).toNat = 0 := by
            have r16200 := hand1 (x (-5) 7) (x (-5) 11)
            have b16201 := hb (x (-5) 7)
            have b16202 := hb (x (-5) 7 && x (-5) 11)
            clear * - r16200 b16201 b16202 d16183
            omega
          have d16203 : (x (-6) 7).toNat = 0 := by
            have r16204 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e16205 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
            have e16206 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
            have e16207 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
            have e16208 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
            have e16209 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
            have e16210 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
            have b16211 := hb (x (-6) 7)
            have b16212 := hb (x (-5) 6)
            have b16213 := hb (x (-4) 5)
            have b16214 := hb (x (-3) 4)
            have b16215 := hb (x (-2) 11)
            have b16216 := hb (x (-1) 10)
            have b16217 := hb (x 0 9)
            have b16218 := hb (x 1 8)
            clear * - r16204 e16205 e16206 e16207 e16208 e16209 e16210 b16211 b16212 b16213 b16214 b16215 b16216 b16217 b16218 d15969 f15968 d12568 d12588 d15985 d16009 d16037
            omega
          have d16219 : (x (-6) 7 && x (-6) 14).toNat = 0 := by
            have r16220 := hand1 (x (-6) 7) (x (-6) 14)
            have b16221 := hb (x (-6) 7)
            have b16222 := hb (x (-6) 7 && x (-6) 14)
            clear * - r16220 b16221 b16222 d16203
            omega
          have d16223 : (x (-6) 7 && x (-6) 12).toNat = 0 := by
            have r16224 := hand1 (x (-6) 7) (x (-6) 12)
            have b16225 := hb (x (-6) 7)
            have b16226 := hb (x (-6) 7 && x (-6) 12)
            clear * - r16224 b16225 b16226 d16203
            omega
          have r16227 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e16228 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
          have e16229 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
          have e16230 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
          have e16231 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
          have e16232 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
          have e16233 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
          have r16234 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e16235 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
          have e16236 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
          have e16237 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
          have e16238 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
          have e16239 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
          have e16240 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
          have r16241 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e16242 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e16243 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e16244 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e16245 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e16246 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e16247 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have r16248 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e16249 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
          have e16250 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
          have r16251 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e16252 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
          have e16253 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
          have r16254 : 1 ≤ (x 2 4).toNat + (x 1 1 && x 1 5).toNat + (x 0 2 && x 0 6).toNat + (x (-1) 3 && x (-1) 7).toNat + (x (-2) 4 && x (-2) 8).toNat + (x (-3) 5 && x (-3) 9).toNat + (x (-4) 6 && x (-4) 10).toNat + (x (-5) 7 && x (-5) 11).toNat + (x (-6) 8 && x (-6) 12).toNat + (x (-7) 9 && x (-7) 13).toNat + (x (-8) 10 && x (-8) 14).toNat + (x (-9) 11).toNat := by have q := hcov4 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e16255 : (x 1 1 && x 1 5).toNat = (x 1 5).toNat := handr _ _ (fun h => hp13 1 (hp5 1 (h)))
          have e16256 : (x (-8) 10 && x (-8) 14).toNat = (x (-8) 10).toNat := handl _ _ (fun h => hp2 (-8) (hp10 (-8) (h)))
          have r16257 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := by have q := hcov5 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r16258 : 1 ≤ (x 1 7).toNat + (x 0 1 && x 0 8).toNat + (x (-1) 2 && x (-1) 9).toNat + (x (-2) 3 && x (-2) 10).toNat + (x (-3) 4 && x (-3) 11).toNat + (x (-4) 5 && x (-4) 12).toNat + (x (-5) 6 && x (-5) 13).toNat + (x (-6) 7 && x (-6) 14).toNat + (x (-7) 8).toNat := by have q := hcov7 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r16259 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r16260 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r16261 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r16262 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
          have r16263 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
          have r16264 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
          have r16265 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
          have r16266 := hand2 (x (-6) 8) (x (-6) 12)
          have r16267 := hand1 (x (-7) 9) (x (-7) 13)
          have r16268 := hand2 (x (-7) 8) (x (-7) 13)
          have r16269 := hand1 (x (-8) 9) (x (-8) 14)
          have r16270 := hand2 (x 6 1) (x 6 10)
          have r16271 := hand2 (x 5 2) (x 5 11)
          have r16272 := hand2 (x (-7) 1) (x (-7) 11)
          have r16273 := hand1 (x (-8) 2) (x (-8) 12)
          have r16274 := hand1 (x (-9) 3) (x (-9) 13)
          have r16275 := hand1 (x (-10) 4) (x (-10) 14)
          have r16276 := hand1 (x (-4) 4) (x (-4) 14)
          linarith only [r16227, e16228, e16229, e16230, e16231, e16232, e16233, r16234, e16235, e16236, e16237, e16238, e16239, e16240, r16241, e16242, e16243, e16244, e16245, e16246, e16247, r16248, e16249, e16250, r16251, e16252, e16253, r16254, e16255, e16256, r16257, r16258, r16259, r16260, r16261, r16262, r16263, r16264, r16265, r16266, r16267, r16268, r16269, r16270, r16271, r16272, r16273, r16274, r16275, r16276, g15, d12516, d12422, d12488, d16103, d16099, d12606, d12528, d16139, d16159, d16179, d16199, d12602, d12564, d12584, d16005, d16033, d16057, d16223, d12634, d12459, g70, g71, d16029, d16053, d16219, d16095, g82, g83, d12447, g84, g85]
      · have f16354 : (x 0 8).toNat = 1 := by rw [h12632]; rfl
        have d16355 : (x (-4) 4).toNat = 0 := by
          have r16356 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e16357 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e16358 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e16359 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e16360 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e16361 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e16362 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b16363 := hb (x (-7) 7)
          have b16364 := hb (x (-6) 6)
          have b16365 := hb (x (-5) 5)
          have b16366 := hb (x (-4) 4)
          have b16367 := hb (x (-3) 11)
          have b16368 := hb (x (-2) 10)
          have b16369 := hb (x (-1) 9)
          have b16370 := hb (x 0 8)
          clear * - r16356 e16357 e16358 e16359 e16360 e16361 e16362 b16363 b16364 b16365 b16366 b16367 b16368 b16369 b16370 f16354 d12455 g7 g3
          omega
        have d16371 : (x (-4) 4 && x (-4) 14).toNat = 0 := by
          have r16372 := hand1 (x (-4) 4) (x (-4) 14)
          have b16373 := hb (x (-4) 4)
          have b16374 := hb (x (-4) 4 && x (-4) 14)
          clear * - r16372 b16373 b16374 d16355
          omega
        have d16375 : (x (-5) 5).toNat = 1 := by
          have r16376 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b16377 := hb (x (-5) 5)
          have b16378 := hb (x 0 10)
          have b16379 := hb (x (-1) 1 && x (-1) 11)
          have b16380 := hb (x (-2) 2 && x (-2) 12)
          have b16381 := hb (x (-3) 3 && x (-3) 13)
          have b16382 := hb (x (-4) 4 && x (-4) 14)
          clear * - r16376 b16377 b16378 b16379 b16380 b16381 b16382 g15 d12447 g84 g85 d16371
          omega
        have r16383 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e16384 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
        have e16385 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
        have e16386 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
        have e16387 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
        have e16388 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
        have e16389 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
        have b16390 := hb (x (-7) 7)
        have b16391 := hb (x (-6) 6)
        have b16392 := hb (x (-5) 5)
        have b16393 := hb (x (-4) 4)
        have b16394 := hb (x (-3) 11)
        have b16395 := hb (x (-2) 10)
        have b16396 := hb (x (-1) 9)
        have b16397 := hb (x 0 8)
        linarith only [r16383, e16384, e16385, e16386, e16387, e16388, e16389, b16390, b16391, b16392, b16393, b16394, b16395, b16396, b16397, f16354, d12455, g7, g3, d16355, d16375]
    · have f16398 : (x 0 7).toNat = 1 := by rw [h12614]; rfl
      have d16399 : (x 7 8).toNat = 0 := by
        have r16400 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e16401 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e16402 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e16403 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e16404 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e16405 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e16406 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b16407 := hb (x 0 7)
        have b16408 := hb (x 1 6)
        have b16409 := hb (x 2 5)
        have b16410 := hb (x 3 4)
        have b16411 := hb (x 4 11)
        have b16412 := hb (x 5 10)
        have b16413 := hb (x 6 9)
        have b16414 := hb (x 7 8)
        clear * - r16400 e16401 e16402 e16403 e16404 e16405 e16406 b16407 b16408 b16409 b16410 b16411 b16412 b16413 b16414 g24 g20 d12422 f16398
        omega
      have d16415 : (x 6 9).toNat = 0 := by
        have r16416 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e16417 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e16418 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e16419 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e16420 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e16421 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e16422 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b16423 := hb (x 0 7)
        have b16424 := hb (x 1 6)
        have b16425 := hb (x 2 5)
        have b16426 := hb (x 3 4)
        have b16427 := hb (x 4 11)
        have b16428 := hb (x 5 10)
        have b16429 := hb (x 6 9)
        have b16430 := hb (x 7 8)
        clear * - r16416 e16417 e16418 e16419 e16420 e16421 e16422 b16423 b16424 b16425 b16426 b16427 b16428 b16429 b16430 d16399 g24 g20 d12422 f16398
        omega
      have d16431 : (x 5 10).toNat = 0 := by
        have r16432 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e16433 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e16434 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e16435 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e16436 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e16437 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e16438 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b16439 := hb (x 0 7)
        have b16440 := hb (x 1 6)
        have b16441 := hb (x 2 5)
        have b16442 := hb (x 3 4)
        have b16443 := hb (x 4 11)
        have b16444 := hb (x 5 10)
        have b16445 := hb (x 6 9)
        have b16446 := hb (x 7 8)
        clear * - r16432 e16433 e16434 e16435 e16436 e16437 e16438 b16439 b16440 b16441 b16442 b16443 b16444 b16445 b16446 d16399 d16415 g24 g20 d12422 f16398
        omega
      have d16447 : (x 5 1 && x 5 10).toNat = 0 := by
        have r16448 := hand2 (x 5 1) (x 5 10)
        have b16449 := hb (x 5 10)
        have b16450 := hb (x 5 1 && x 5 10)
        clear * - r16448 b16449 b16450 d16431
        omega
      have d16451 : (x 4 2 && x 4 11).toNat = 1 := by
        have r16452 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b16453 := hb (x 0 6)
        have b16454 := hb (x 6 9)
        have b16455 := hb (x 5 1 && x 5 10)
        have b16456 := hb (x 4 2 && x 4 11)
        have b16457 := hb (x 3 3 && x 3 12)
        have b16458 := hb (x 2 4 && x 2 13)
        have b16459 := hb (x 1 5 && x 1 14)
        clear * - r16452 b16453 b16454 b16455 b16456 b16457 b16458 b16459 d16415 d16447 g80 g81 d12414 f12597
        omega
      have d16460 : (x 4 11).toNat = 1 := by
        have r16461 := hand2 (x 4 2) (x 4 11)
        have b16462 := hb (x 4 11)
        have b16463 := hb (x 4 2 && x 4 11)
        clear * - r16461 b16462 b16463 d16451
        omega
      have r16464 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16465 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e16466 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e16467 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e16468 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e16469 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e16470 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b16471 := hb (x 0 7)
      have b16472 := hb (x 1 6)
      have b16473 := hb (x 2 5)
      have b16474 := hb (x 3 4)
      have b16475 := hb (x 4 11)
      have b16476 := hb (x 5 10)
      have b16477 := hb (x 6 9)
      have b16478 := hb (x 7 8)
      linarith only [r16464, e16465, e16466, e16467, e16468, e16469, e16470, b16471, b16472, b16473, b16474, b16475, b16476, b16477, b16478, d16399, d16415, d16431, d16460, g24, g20, d12422, f16398]
  · have f16479 : (x 0 6).toNat = 1 := by rw [h12596]; rfl
    have d16480 : (x 6 8).toNat = 0 := by
      have r16481 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16482 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e16483 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e16484 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e16485 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e16486 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e16487 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b16488 := hb (x (-1) 7)
      have b16489 := hb (x 0 6)
      have b16490 := hb (x 1 5)
      have b16491 := hb (x 2 4)
      have b16492 := hb (x 3 11)
      have b16493 := hb (x 4 10)
      have b16494 := hb (x 5 9)
      have b16495 := hb (x 6 8)
      clear * - r16481 e16482 e16483 e16484 e16485 e16486 e16487 b16488 b16489 b16490 b16491 b16492 b16493 b16494 b16495 d12488 d12516 f16479
      omega
    have d16496 : (x 6 4 && x 6 8).toNat = 0 := by
      have r16497 := hand2 (x 6 4) (x 6 8)
      have b16498 := hb (x 6 8)
      have b16499 := hb (x 6 4 && x 6 8)
      clear * - r16497 b16498 b16499 d16480
      omega
    have d16500 : (x 5 9).toNat = 0 := by
      have r16501 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16502 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e16503 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e16504 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e16505 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e16506 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e16507 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b16508 := hb (x (-1) 7)
      have b16509 := hb (x 0 6)
      have b16510 := hb (x 1 5)
      have b16511 := hb (x 2 4)
      have b16512 := hb (x 3 11)
      have b16513 := hb (x 4 10)
      have b16514 := hb (x 5 9)
      have b16515 := hb (x 6 8)
      clear * - r16501 e16502 e16503 e16504 e16505 e16506 e16507 b16508 b16509 b16510 b16511 b16512 b16513 b16514 b16515 d16480 d12488 d12516 f16479
      omega
    have d16516 : (x 5 5 && x 5 9).toNat = 0 := by
      have r16517 := hand2 (x 5 5) (x 5 9)
      have b16518 := hb (x 5 9)
      have b16519 := hb (x 5 5 && x 5 9)
      clear * - r16517 b16518 b16519 d16500
      omega
    have d16520 : (x 4 10).toNat = 0 := by
      have r16521 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16522 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e16523 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e16524 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e16525 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e16526 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e16527 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b16528 := hb (x (-1) 7)
      have b16529 := hb (x 0 6)
      have b16530 := hb (x 1 5)
      have b16531 := hb (x 2 4)
      have b16532 := hb (x 3 11)
      have b16533 := hb (x 4 10)
      have b16534 := hb (x 5 9)
      have b16535 := hb (x 6 8)
      clear * - r16521 e16522 e16523 e16524 e16525 e16526 e16527 b16528 b16529 b16530 b16531 b16532 b16533 b16534 b16535 d16480 d16500 d12488 d12516 f16479
      omega
    have d16536 : (x 4 1 && x 4 10).toNat = 0 := by
      have r16537 := hand2 (x 4 1) (x 4 10)
      have b16538 := hb (x 4 10)
      have b16539 := hb (x 4 1 && x 4 10)
      clear * - r16537 b16538 b16539 d16520
      omega
    have d16540 : (x 4 6 && x 4 10).toNat = 0 := by
      have r16541 := hand2 (x 4 6) (x 4 10)
      have b16542 := hb (x 4 10)
      have b16543 := hb (x 4 6 && x 4 10)
      clear * - r16541 b16542 b16543 d16520
      omega
    have d16544 : (x 3 11).toNat = 0 := by
      have r16545 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16546 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e16547 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e16548 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e16549 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e16550 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e16551 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b16552 := hb (x (-1) 7)
      have b16553 := hb (x 0 6)
      have b16554 := hb (x 1 5)
      have b16555 := hb (x 2 4)
      have b16556 := hb (x 3 11)
      have b16557 := hb (x 4 10)
      have b16558 := hb (x 5 9)
      have b16559 := hb (x 6 8)
      clear * - r16545 e16546 e16547 e16548 e16549 e16550 e16551 b16552 b16553 b16554 b16555 b16556 b16557 b16558 b16559 d16480 d16500 d16520 d12488 d12516 f16479
      omega
    have d16560 : (x 3 2 && x 3 11).toNat = 0 := by
      have r16561 := hand2 (x 3 2) (x 3 11)
      have b16562 := hb (x 3 11)
      have b16563 := hb (x 3 2 && x 3 11)
      clear * - r16561 b16562 b16563 d16544
      omega
    have d16564 : (x (-1) 6).toNat = 1 := by
      have r16565 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16566 := hb (x (-1) 6)
      have b16567 := hb (x 5 9)
      have b16568 := hb (x 4 1 && x 4 10)
      have b16569 := hb (x 3 2 && x 3 11)
      have b16570 := hb (x 2 3 && x 2 12)
      have b16571 := hb (x 1 4 && x 1 13)
      have b16572 := hb (x 0 5 && x 0 14)
      clear * - r16565 b16566 b16567 b16568 b16569 b16570 b16571 b16572 d16500 d16536 d16560 d12480 d12508 g79
      omega
    have d16573 : (x (-1) 14).toNat = 1 := by
      have r16574 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
      have b16575 := hb (x (-1) 6)
      have b16576 := hb (x (-1) 14)
      clear * - r16574 b16575 b16576 d16564
      omega
    have d16577 : (x (-2) 1).toNat = 0 := by
      have r16578 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16579 := hb (x (-2) 1)
      have b16580 := hb (x (-1) 14)
      clear * - r16578 b16579 b16580 d16573
      omega
    have d16581 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
      have r16582 := hand1 (x (-2) 1) (x (-2) 14)
      have b16583 := hb (x (-2) 1)
      have b16584 := hb (x (-2) 1 && x (-2) 14)
      clear * - r16582 b16583 b16584 d16577
      omega
    have d16585 : (x (-3) 2).toNat = 1 := by
      have r16586 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16587 := hb (x (-3) 2)
      have b16588 := hb (x (-1) 13)
      have b16589 := hb (x (-2) 1 && x (-2) 14)
      clear * - r16586 b16587 b16588 b16589 g10 d16581
      omega
    have d16590 : (x (-3) 14).toNat = 1 := by
      have r16591 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
      have b16592 := hb (x (-3) 2)
      have b16593 := hb (x (-3) 14)
      clear * - r16591 b16592 b16593 d16585
      omega
    have d16594 : (x (-1) 12).toNat = 0 := by
      have r16595 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16596 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e16597 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b16598 := hb (x (-4) 3)
      have b16599 := hb (x (-3) 2)
      have b16600 := hb (x (-2) 13)
      have b16601 := hb (x (-1) 12)
      clear * - r16595 e16596 e16597 b16598 b16599 b16600 b16601 d16585
      omega
    have d16602 : (x (-1) 8 && x (-1) 12).toNat = 0 := by
      have r16603 := hand2 (x (-1) 8) (x (-1) 12)
      have b16604 := hb (x (-1) 12)
      have b16605 := hb (x (-1) 8 && x (-1) 12)
      clear * - r16603 b16604 b16605 d16594
      omega
    have d16606 : (x (-2) 13).toNat = 0 := by
      have r16607 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16608 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e16609 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b16610 := hb (x (-4) 3)
      have b16611 := hb (x (-3) 2)
      have b16612 := hb (x (-2) 13)
      have b16613 := hb (x (-1) 12)
      clear * - r16607 e16608 e16609 b16610 b16611 b16612 b16613 d16594 d16585
      omega
    have d16614 : (x (-2) 9 && x (-2) 13).toNat = 0 := by
      have r16615 := hand2 (x (-2) 9) (x (-2) 13)
      have b16616 := hb (x (-2) 13)
      have b16617 := hb (x (-2) 9 && x (-2) 13)
      clear * - r16615 b16616 b16617 d16606
      omega
    have d16618 : (x (-4) 3).toNat = 0 := by
      have r16619 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16620 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e16621 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b16622 := hb (x (-4) 3)
      have b16623 := hb (x (-3) 2)
      have b16624 := hb (x (-2) 13)
      have b16625 := hb (x (-1) 12)
      clear * - r16619 e16620 e16621 b16622 b16623 b16624 b16625 d16594 d16606 d16585
      omega
    have d16626 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
      have r16627 := hand1 (x (-4) 3) (x (-4) 12)
      have b16628 := hb (x (-4) 3)
      have b16629 := hb (x (-4) 3 && x (-4) 12)
      clear * - r16627 b16628 b16629 d16618
      omega
    have d16630 : (x (-4) 11).toNat = 0 := by
      have r16631 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
      have b16632 := hb (x (-4) 3)
      have b16633 := hb (x (-4) 11)
      clear * - r16631 b16632 b16633 d16618
      omega
    have d16634 : (x (-2) 9).toNat = 0 := by
      have r16635 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
      have b16636 := hb (x (-2) 1)
      have b16637 := hb (x (-2) 9)
      clear * - r16635 b16636 b16637 d16577
      omega
    have d16638 : (x 3 7 && x 3 11).toNat = 0 := by
      have r16639 := hand2 (x 3 7) (x 3 11)
      have b16640 := hb (x 3 11)
      have b16641 := hb (x 3 7 && x 3 11)
      clear * - r16639 b16640 b16641 d16544
      omega
    have r16642 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r16643 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16644 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
    have e16645 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
    have e16646 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
    have e16647 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
    have e16648 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
    have e16649 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
    have r16650 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16651 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e16652 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e16653 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e16654 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e16655 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e16656 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have r16657 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16658 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e16659 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e16660 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e16661 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e16662 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e16663 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have r16664 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16665 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e16666 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have r16667 : 1 ≤ (x 7 4).toNat + (x 6 1 && x 6 5).toNat + (x 5 2 && x 5 6).toNat + (x 4 3 && x 4 7).toNat + (x 3 4 && x 3 8).toNat + (x 2 5 && x 2 9).toNat + (x 1 6 && x 1 10).toNat + (x 0 7 && x 0 11).toNat + (x (-1) 8 && x (-1) 12).toNat + (x (-2) 9 && x (-2) 13).toNat + (x (-3) 10 && x (-3) 14).toNat + (x (-4) 11).toNat := by have q := hcov4 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16668 : (x 6 1 && x 6 5).toNat = (x 6 5).toNat := handr _ _ (fun h => hp13 6 (hp5 6 (h)))
    have e16669 : (x (-3) 10 && x (-3) 14).toNat = (x (-3) 10).toNat := handl _ _ (fun h => hp2 (-3) (hp10 (-3) (h)))
    have r16670 : 1 ≤ (x 10 4).toNat + (x 9 1 && x 9 5).toNat + (x 8 2 && x 8 6).toNat + (x 7 3 && x 7 7).toNat + (x 6 4 && x 6 8).toNat + (x 5 5 && x 5 9).toNat + (x 4 6 && x 4 10).toNat + (x 3 7 && x 3 11).toNat + (x 2 8 && x 2 12).toNat + (x 1 9 && x 1 13).toNat + (x 0 10 && x 0 14).toNat + (x (-1) 11).toNat := by have q := hcov4 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16671 : (x 9 1 && x 9 5).toNat = (x 9 5).toNat := handr _ _ (fun h => hp13 9 (hp5 9 (h)))
    have e16672 : (x 0 10 && x 0 14).toNat = (x 0 10).toNat := handl _ _ (fun h => hp2 0 (hp10 0 (h)))
    have r16673 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r16674 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r16675 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r16676 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
    have r16677 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
    have r16678 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
    have r16679 := hand2 (x 5 2) (x 5 6)
    have r16680 := hand2 (x 4 3) (x 4 7)
    have r16681 := hand1 (x 0 7) (x 0 11)
    have r16682 := hand2 (x 8 2) (x 8 6)
    have r16683 := hand2 (x 7 3) (x 7 7)
    have r16684 := hand1 (x (-5) 4) (x (-5) 13)
    have r16685 := hand1 (x (-6) 5) (x (-6) 14)
    have r16686 := hand2 (x 4 1) (x 4 11)
    have r16687 := hand1 (x 10 1) (x 10 12)
    have r16688 := hand1 (x 9 2) (x 9 13)
    have r16689 := hand1 (x 8 3) (x 8 14)
    linarith only [r16642, r16643, e16644, e16645, e16646, e16647, e16648, e16649, r16650, e16651, e16652, e16653, e16654, e16655, e16656, r16657, e16658, e16659, e16660, e16661, e16662, e16663, r16664, e16665, e16666, r16667, e16668, e16669, r16670, e16671, e16672, r16673, r16674, r16675, r16676, r16677, r16678, r16679, r16680, r16681, r16682, r16683, r16684, r16685, r16686, r16687, r16688, r16689, d16630, d16590, d16634, d16606, d12455, d12532, d16594, g14, g15, g16, d12422, g18, g20, g21, g24, g25, g39, g40, g41, d16602, d16614, d16496, d16516, d16540, d16638, d12484, d12512, g74, g75, d16626, g86, g87, d12410]

theorem cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b011 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-4) 7).toNat = 0)
    (g1 : (x (-3) 6).toNat = 0)
    (g2 : (x (-3) 7).toNat = 0)
    (g3 : (x (-3) 11).toNat = 0)
    (g4 : (x (-2) 2).toNat = 0)
    (g5 : (x (-2) 5).toNat = 0)
    (g6 : (x (-2) 6).toNat = 0)
    (g7 : (x (-2) 10).toNat = 0)
    (g8 : (x (-1) 4).toNat = 0)
    (g9 : (x (-1) 5).toNat = 0)
    (g10 : (x (-1) 13).toNat = 0)
    (g11 : (x 0 1).toNat = 1)
    (g12 : (x 0 3).toNat = 1)
    (g13 : (x 0 4).toNat = 1)
    (g14 : (x 0 5).toNat = 0)
    (g15 : (x 0 10).toNat = 0)
    (g16 : (x 0 11).toNat = 1)
    (g17 : (x 1 2).toNat = 0)
    (g18 : (x 1 10).toNat = 0)
    (g19 : (x 1 11).toNat = 0)
    (g20 : (x 2 5).toNat = 0)
    (g21 : (x 2 9).toNat = 0)
    (g22 : (x 2 10).toNat = 0)
    (g23 : (x 2 13).toNat = 0)
    (g24 : (x 3 4).toNat = 0)
    (g25 : (x 3 8).toNat = 0)
    (g26 : (x 1 2 && x 1 5).toNat = 0)
    (g27 : (x (-1) 4 && x (-1) 7).toNat = 0)
    (g28 : (x (-2) 5 && x (-2) 8).toNat = 0)
    (g29 : (x (-3) 6 && x (-3) 9).toNat = 0)
    (g30 : (x (-4) 7 && x (-4) 10).toNat = 0)
    (g31 : (x 1 2 && x 1 6).toNat = 0)
    (g32 : (x (-1) 4 && x (-1) 8).toNat = 0)
    (g33 : (x (-2) 5 && x (-2) 9).toNat = 0)
    (g34 : (x (-3) 6 && x (-3) 10).toNat = 0)
    (g35 : (x (-4) 7 && x (-4) 11).toNat = 0)
    (g36 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g37 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g38 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g39 : (x 3 4 && x 3 8).toNat = 0)
    (g40 : (x 2 5 && x 2 9).toNat = 0)
    (g41 : (x 1 6 && x 1 10).toNat = 0)
    (g42 : (x 4 4 && x 4 8).toNat = 0)
    (g43 : (x 3 5 && x 3 9).toNat = 0)
    (g44 : (x 2 6 && x 2 10).toNat = 0)
    (g45 : (x 1 7 && x 1 11).toNat = 0)
    (g46 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g47 : (x 4 8 && x 4 12).toNat = 0)
    (g48 : (x 3 9 && x 3 13).toNat = 0)
    (g49 : (x (-3) 1 && x (-3) 6).toNat = 0)
    (g50 : (x (-4) 2 && x (-4) 7).toNat = 0)
    (g51 : (x (-2) 1 && x (-2) 6).toNat = 0)
    (g52 : (x (-3) 2 && x (-3) 7).toNat = 0)
    (g53 : (x 4 3 && x 4 8).toNat = 0)
    (g54 : (x 3 4 && x 3 9).toNat = 0)
    (g55 : (x 2 5 && x 2 10).toNat = 0)
    (g56 : (x 1 6 && x 1 11).toNat = 0)
    (g57 : (x (-1) 8 && x (-1) 13).toNat = 0)
    (g58 : (x 3 8 && x 3 13).toNat = 0)
    (g59 : (x 2 9 && x 2 14).toNat = 0)
    (g60 : (x (-3) 1 && x (-3) 7).toNat = 0)
    (g61 : (x (-2) 4 && x (-2) 10).toNat = 0)
    (g62 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g63 : (x 4 2 && x 4 8).toNat = 0)
    (g64 : (x 3 3 && x 3 9).toNat = 0)
    (g65 : (x 2 4 && x 2 10).toNat = 0)
    (g66 : (x 1 5 && x 1 11).toNat = 0)
    (g67 : (x (-1) 7 && x (-1) 13).toNat = 0)
    (g68 : (x 3 4 && x 3 10).toNat = 0)
    (g69 : (x 2 5 && x 2 11).toNat = 0)
    (g70 : (x (-2) 3 && x (-2) 10).toNat = 0)
    (g71 : (x (-3) 4 && x (-3) 11).toNat = 0)
    (g72 : (x 3 5 && x 3 12).toNat = 0)
    (g73 : (x 2 6 && x 2 13).toNat = 0)
    (g74 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g75 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g76 : (x (-2) 2 && x (-2) 11).toNat = 0)
    (g77 : (x (-3) 3 && x (-3) 12).toNat = 0)
    (g78 : (x 0 1 && x 0 10).toNat = 0)
    (g79 : (x 0 5 && x 0 14).toNat = 0)
    (g80 : (x 3 3 && x 3 12).toNat = 0)
    (g81 : (x 2 4 && x 2 13).toNat = 0)
    (g82 : (x 3 4 && x 3 13).toNat = 0)
    (g83 : (x 2 5 && x 2 14).toNat = 0)
    (g84 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g85 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g86 : (x 3 2 && x 3 12).toNat = 0)
    (g87 : (x 2 3 && x 2 13).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b011_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83 g84 g85 g86 g87
