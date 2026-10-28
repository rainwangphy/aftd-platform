import AFTD.Prelude

/-!
# cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt1110111

Topic: combinatorics   Node: 4bae084263f8

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_alternates_core: under the layer-free tight-cover constraints for k = 15 and 118 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt1110111_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 7).toNat = 0)
    (g1 : (x (-3) 11).toNat = 0)
    (g2 : (x (-2) 6).toNat = 0)
    (g3 : (x (-2) 10).toNat = 0)
    (g4 : (x (-2) 11).toNat = 0)
    (g5 : (x (-1) 3).toNat = 0)
    (g6 : (x (-1) 5).toNat = 0)
    (g7 : (x (-1) 9).toNat = 0)
    (g8 : (x (-1) 10).toNat = 0)
    (g9 : (x (-1) 11).toNat = 0)
    (g10 : (x (-1) 13).toNat = 0)
    (g11 : (x 0 2).toNat = 1)
    (g12 : (x 0 4).toNat = 1)
    (g13 : (x 0 5).toNat = 1)
    (g14 : (x 0 7).toNat = 0)
    (g15 : (x 0 12).toNat = 1)
    (g16 : (x 0 13).toNat = 1)
    (g17 : (x 1 1).toNat = 1)
    (g18 : (x 1 3).toNat = 0)
    (g19 : (x 1 4).toNat = 0)
    (g20 : (x 1 5).toNat = 0)
    (g21 : (x 1 6).toNat = 0)
    (g22 : (x 1 10).toNat = 0)
    (g23 : (x 1 11).toNat = 0)
    (g24 : (x 1 12).toNat = 0)
    (g25 : (x 2 2).toNat = 0)
    (g26 : (x 2 4).toNat = 0)
    (g27 : (x 2 5).toNat = 0)
    (g28 : (x 2 6).toNat = 0)
    (g29 : (x 2 10).toNat = 0)
    (g30 : (x 3 1).toNat = 1)
    (g31 : (x 3 4).toNat = 0)
    (g32 : (x 3 9).toNat = 0)
    (g33 : (x 4 4).toNat = 0)
    (g34 : (x 4 6).toNat = 0)
    (g35 : (x 4 8).toNat = 0)
    (g36 : (x 4 10).toNat = 0)
    (g37 : (x 4 3 && x 4 4).toNat = 0)
    (g38 : (x 3 4 && x 3 5).toNat = 0)
    (g39 : (x 2 5 && x 2 6).toNat = 0)
    (g40 : (x 1 6 && x 1 7).toNat = 0)
    (g41 : (x 0 7 && x 0 8).toNat = 0)
    (g42 : (x (-1) 8 && x (-1) 9).toNat = 0)
    (g43 : (x (-2) 9 && x (-2) 10).toNat = 0)
    (g44 : (x (-3) 10 && x (-3) 11).toNat = 0)
    (g45 : (x 2 2 && x 2 6).toNat = 0)
    (g46 : (x 1 3 && x 1 7).toNat = 0)
    (g47 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g48 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g49 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g50 : (x 3 4 && x 3 8).toNat = 0)
    (g51 : (x 2 5 && x 2 9).toNat = 0)
    (g52 : (x 1 6 && x 1 10).toNat = 0)
    (g53 : (x 0 7 && x 0 11).toNat = 0)
    (g54 : (x 4 4 && x 4 8).toNat = 0)
    (g55 : (x 3 5 && x 3 9).toNat = 0)
    (g56 : (x 2 6 && x 2 10).toNat = 0)
    (g57 : (x 1 7 && x 1 11).toNat = 0)
    (g58 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g59 : (x (-2) 1 && x (-2) 6).toNat = 0)
    (g60 : (x (-3) 2 && x (-3) 7).toNat = 0)
    (g61 : (x 1 1 && x 1 6).toNat = 0)
    (g62 : (x 0 2 && x 0 7).toNat = 0)
    (g63 : (x (-1) 3 && x (-1) 8).toNat = 0)
    (g64 : (x 4 2 && x 4 7).toNat = 0)
    (g65 : (x 2 4 && x 2 9).toNat = 0)
    (g66 : (x 1 5 && x 1 10).toNat = 0)
    (g67 : (x 4 3 && x 4 8).toNat = 0)
    (g68 : (x 3 4 && x 3 9).toNat = 0)
    (g69 : (x 2 5 && x 2 10).toNat = 0)
    (g70 : (x 1 6 && x 1 11).toNat = 0)
    (g71 : (x 0 7 && x 0 12).toNat = 0)
    (g72 : (x (-1) 8 && x (-1) 13).toNat = 0)
    (g73 : (x (-1) 1 && x (-1) 7).toNat = 0)
    (g74 : (x (-2) 2 && x (-2) 8).toNat = 0)
    (g75 : (x (-3) 3 && x (-3) 9).toNat = 0)
    (g76 : (x 0 1 && x 0 7).toNat = 0)
    (g77 : (x (-1) 2 && x (-1) 8).toNat = 0)
    (g78 : (x (-2) 3 && x (-2) 9).toNat = 0)
    (g79 : (x (-1) 3 && x (-1) 9).toNat = 0)
    (g80 : (x (-2) 4 && x (-2) 10).toNat = 0)
    (g81 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g82 : (x 3 4 && x 3 10).toNat = 0)
    (g83 : (x 2 5 && x 2 11).toNat = 0)
    (g84 : (x 1 6 && x 1 12).toNat = 0)
    (g85 : (x 0 7 && x 0 13).toNat = 0)
    (g86 : (x 4 4 && x 4 10).toNat = 0)
    (g87 : (x 2 6 && x 2 12).toNat = 0)
    (g88 : (x 1 7 && x 1 13).toNat = 0)
    (g89 : (x (-1) 1 && x (-1) 8).toNat = 0)
    (g90 : (x (-2) 2 && x (-2) 9).toNat = 0)
    (g91 : (x (-3) 3 && x (-3) 10).toNat = 0)
    (g92 : (x 4 2 && x 4 9).toNat = 0)
    (g93 : (x 2 4 && x 2 11).toNat = 0)
    (g94 : (x 1 5 && x 1 12).toNat = 0)
    (g95 : (x 4 3 && x 4 10).toNat = 0)
    (g96 : (x 3 4 && x 3 11).toNat = 0)
    (g97 : (x 2 5 && x 2 12).toNat = 0)
    (g98 : (x 1 6 && x 1 13).toNat = 0)
    (g99 : (x 0 7 && x 0 14).toNat = 0)
    (g100 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g101 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g102 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g103 : (x (-2) 2 && x (-2) 11).toNat = 0)
    (g104 : (x (-3) 3 && x (-3) 12).toNat = 0)
    (g105 : (x 4 3 && x 4 12).toNat = 0)
    (g106 : (x 3 4 && x 3 13).toNat = 0)
    (g107 : (x 2 5 && x 2 14).toNat = 0)
    (g108 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g109 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g110 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g111 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g112 : (x (-1) 2 && x (-1) 12).toNat = 0)
    (g113 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g114 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g115 : (x (-2) 2 && x (-2) 13).toNat = 0)
    (g116 : (x (-3) 3 && x (-3) 14).toNat = 0)
    (g117 : (x 4 1 && x 4 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d37308 : (x 5 8).toNat = 0 := by
    have r37309 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37310 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e37311 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e37312 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e37313 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e37314 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e37315 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b37316 := hb (x (-2) 7)
    have b37317 := hb (x (-1) 6)
    have b37318 := hb (x 0 5)
    have b37319 := hb (x 1 4)
    have b37320 := hb (x 2 11)
    have b37321 := hb (x 3 10)
    have b37322 := hb (x 4 9)
    have b37323 := hb (x 5 8)
    clear * - r37309 e37310 e37311 e37312 e37313 e37314 e37315 b37316 b37317 b37318 b37319 b37320 b37321 b37322 b37323 g19 g13
    omega
  have d37324 : (x 5 1 && x 5 8).toNat = 0 := by
    have r37325 := hand2 (x 5 1) (x 5 8)
    have b37326 := hb (x 5 8)
    have b37327 := hb (x 5 1 && x 5 8)
    clear * - r37325 b37326 b37327 d37308
    omega
  have d37328 : (x 5 2 && x 5 8).toNat = 0 := by
    have r37329 := hand2 (x 5 2) (x 5 8)
    have b37330 := hb (x 5 8)
    have b37331 := hb (x 5 2 && x 5 8)
    clear * - r37329 b37330 b37331 d37308
    omega
  have d37332 : (x 4 9).toNat = 0 := by
    have r37333 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37334 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e37335 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e37336 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e37337 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e37338 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e37339 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b37340 := hb (x (-2) 7)
    have b37341 := hb (x (-1) 6)
    have b37342 := hb (x 0 5)
    have b37343 := hb (x 1 4)
    have b37344 := hb (x 2 11)
    have b37345 := hb (x 3 10)
    have b37346 := hb (x 4 9)
    have b37347 := hb (x 5 8)
    clear * - r37333 e37334 e37335 e37336 e37337 e37338 e37339 b37340 b37341 b37342 b37343 b37344 b37345 b37346 b37347 d37308 g19 g13
    omega
  have d37348 : (x 4 3 && x 4 9).toNat = 0 := by
    have r37349 := hand2 (x 4 3) (x 4 9)
    have b37350 := hb (x 4 9)
    have b37351 := hb (x 4 3 && x 4 9)
    clear * - r37349 b37350 b37351 d37332
    omega
  have d37352 : (x 3 10).toNat = 0 := by
    have r37353 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37354 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e37355 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e37356 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e37357 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e37358 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e37359 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b37360 := hb (x (-2) 7)
    have b37361 := hb (x (-1) 6)
    have b37362 := hb (x 0 5)
    have b37363 := hb (x 1 4)
    have b37364 := hb (x 2 11)
    have b37365 := hb (x 3 10)
    have b37366 := hb (x 4 9)
    have b37367 := hb (x 5 8)
    clear * - r37353 e37354 e37355 e37356 e37357 e37358 e37359 b37360 b37361 b37362 b37363 b37364 b37365 b37366 b37367 d37308 d37332 g19 g13
    omega
  have d37368 : (x 3 3 && x 3 10).toNat = 0 := by
    have r37369 := hand2 (x 3 3) (x 3 10)
    have b37370 := hb (x 3 10)
    have b37371 := hb (x 3 3 && x 3 10)
    clear * - r37369 b37370 b37371 d37352
    omega
  have d37372 : (x 2 11).toNat = 0 := by
    have r37373 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37374 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e37375 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e37376 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e37377 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e37378 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e37379 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b37380 := hb (x (-2) 7)
    have b37381 := hb (x (-1) 6)
    have b37382 := hb (x 0 5)
    have b37383 := hb (x 1 4)
    have b37384 := hb (x 2 11)
    have b37385 := hb (x 3 10)
    have b37386 := hb (x 4 9)
    have b37387 := hb (x 5 8)
    clear * - r37373 e37374 e37375 e37376 e37377 e37378 e37379 b37380 b37381 b37382 b37383 b37384 b37385 b37386 b37387 d37308 d37332 d37352 g19 g13
    omega
  cases h37388 : x 0 6
  · have f37389 : (x 0 6).toNat = 0 := by rw [h37388]; rfl
    have d37390 : (x 0 6 && x 0 13).toNat = 0 := by
      have r37391 := hand1 (x 0 6) (x 0 13)
      have b37392 := hb (x 0 6)
      have b37393 := hb (x 0 6 && x 0 13)
      clear * - r37391 b37392 b37393 f37389
      omega
    have d37394 : (x 0 6 && x 0 11).toNat = 0 := by
      have r37395 := hand1 (x 0 6) (x 0 11)
      have b37396 := hb (x 0 6)
      have b37397 := hb (x 0 6 && x 0 11)
      clear * - r37395 b37396 b37397 f37389
      omega
    cases h37398 : x 0 8
    · have f37399 : (x 0 8).toNat = 0 := by rw [h37398]; rfl
      have d37400 : (x 0 2 && x 0 8).toNat = 0 := by
        have r37401 := hand2 (x 0 2) (x 0 8)
        have b37402 := hb (x 0 8)
        have b37403 := hb (x 0 2 && x 0 8)
        clear * - r37401 b37402 b37403 f37399
        omega
      have d37404 : (x 0 4 && x 0 8).toNat = 0 := by
        have r37405 := hand2 (x 0 4) (x 0 8)
        have b37406 := hb (x 0 8)
        have b37407 := hb (x 0 4 && x 0 8)
        clear * - r37405 b37406 b37407 f37399
        omega
      have r37408 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r37409 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r37410 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r37411 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e37412 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e37413 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e37414 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e37415 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e37416 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e37417 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have r37418 : (x (-11) 12).toNat + (x (-12) 1 && x (-12) 13).toNat + (x (-13) 2 && x (-13) 14).toNat + (x (-14) 3).toNat = 1 := by have q := hd12 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e37419 : (x (-12) 1 && x (-12) 13).toNat = (x (-12) 13).toNat := handr _ _ (fun h => hp13 (-12) (h))
      have e37420 : (x (-13) 2 && x (-13) 14).toNat = (x (-13) 2).toNat := handl _ _ (fun h => hp2 (-13) (h))
      have r37421 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e37422 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e37423 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have r37424 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e37425 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e37426 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have r37427 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r37428 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e37429 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
      have e37430 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
      have r37431 : 1 ≤ (x 2 6).toNat + (x 1 1 && x 1 7).toNat + (x 0 2 && x 0 8).toNat + (x (-1) 3 && x (-1) 9).toNat + (x (-2) 4 && x (-2) 10).toNat + (x (-3) 5 && x (-3) 11).toNat + (x (-4) 6 && x (-4) 12).toNat + (x (-5) 7 && x (-5) 13).toNat + (x (-6) 8 && x (-6) 14).toNat + (x (-7) 9).toNat := by have q := hcov6 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r37432 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r37433 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r37434 : 1 ≤ (x (-7) 11).toNat + (x (-8) 1 && x (-8) 12).toNat + (x (-9) 2 && x (-9) 13).toNat + (x (-10) 3 && x (-10) 14).toNat + (x (-11) 4).toNat := by have q := hcov11 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r37435 : 1 ≤ (x (-11) 13).toNat + (x (-12) 1 && x (-12) 14).toNat + (x (-13) 2).toNat := by have q := hcov13 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r37436 : (x (-11) 4).toNat ≤ (x (-11) 12).toNat := himp _ _ (hp4 (-11))
      have r37437 : (x (-11) 5).toNat ≤ (x (-11) 13).toNat := himp _ _ (hp5 (-11))
      have r37438 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
      have r37439 := hand1 (x (-4) 8) (x (-4) 12)
      have r37440 := hand1 (x (-5) 9) (x (-5) 13)
      have r37441 := hand2 (x 1 1) (x 1 7)
      have r37442 := hand1 (x (-4) 6) (x (-4) 12)
      have r37443 := hand1 (x (-5) 7) (x (-5) 13)
      have r37444 := hand1 (x (-6) 8) (x (-6) 14)
      have r37445 := hand2 (x 6 1) (x 6 10)
      have r37446 := hand2 (x 5 2) (x 5 11)
      have r37447 := hand1 (x (-7) 1) (x (-7) 11)
      have r37448 := hand2 (x (-8) 2) (x (-8) 12)
      have r37449 := hand2 (x (-9) 3) (x (-9) 13)
      have r37450 := hand2 (x (-10) 4) (x (-10) 14)
      have r37451 := hand2 (x (-8) 1) (x (-8) 12)
      have r37452 := hand2 (x (-9) 2) (x (-9) 13)
      have r37453 := hand2 (x (-10) 3) (x (-10) 14)
      have r37454 := hand2 (x (-12) 1) (x (-12) 14)
      have b37508 := hb (x 7 1)
      linarith only [r37408, r37409, r37410, r37411, e37412, e37413, e37414, e37415, e37416, e37417, r37418, e37419, e37420, r37421, e37422, e37423, r37424, e37425, e37426, r37427, r37428, e37429, e37430, r37431, r37432, r37433, r37434, r37435, r37436, r37437, r37438, r37439, r37440, r37441, r37442, r37443, r37444, r37445, r37446, r37447, r37448, r37449, r37450, r37451, r37452, r37453, r37454, b37508, g0, g1, g2, g3, g5, g6, g7, g11, g12, f37399, g17, g18, g21, g25, g28, g30, g33, g45, g46, d37404, g47, g48, g49, d37400, g79, g80, g81, g105, g106, g107]
    · have f37542 : (x 0 8).toNat = 1 := by rw [h37398]; rfl
      have d37543 : (x (-4) 4).toNat = 0 := by
        have r37544 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e37545 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
        have e37546 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
        have e37547 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
        have e37548 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
        have e37549 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
        have e37550 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
        have b37551 := hb (x (-7) 7)
        have b37552 := hb (x (-6) 6)
        have b37553 := hb (x (-5) 5)
        have b37554 := hb (x (-4) 4)
        have b37555 := hb (x (-3) 11)
        have b37556 := hb (x (-2) 10)
        have b37557 := hb (x (-1) 9)
        have b37558 := hb (x 0 8)
        clear * - r37544 e37545 e37546 e37547 e37548 e37549 e37550 b37551 b37552 b37553 b37554 b37555 b37556 b37557 b37558 f37542 g7 g3 g1
        omega
      have d37559 : (x (-4) 4 && x (-4) 14).toNat = 0 := by
        have r37560 := hand1 (x (-4) 4) (x (-4) 14)
        have b37561 := hb (x (-4) 4)
        have b37562 := hb (x (-4) 4 && x (-4) 14)
        clear * - r37560 b37561 b37562 d37543
        omega
      have d37563 : (x (-4) 4 && x (-4) 13).toNat = 0 := by
        have r37564 := hand1 (x (-4) 4) (x (-4) 13)
        have b37565 := hb (x (-4) 4)
        have b37566 := hb (x (-4) 4 && x (-4) 13)
        clear * - r37564 b37565 b37566 d37543
        omega
      have d37567 : (x (-4) 4 && x (-4) 11).toNat = 0 := by
        have r37568 := hand1 (x (-4) 4) (x (-4) 11)
        have b37569 := hb (x (-4) 4)
        have b37570 := hb (x (-4) 4 && x (-4) 11)
        clear * - r37568 b37569 b37570 d37543
        omega
      have d37571 : (x (-4) 4 && x (-4) 10).toNat = 0 := by
        have r37572 := hand1 (x (-4) 4) (x (-4) 10)
        have b37573 := hb (x (-4) 4)
        have b37574 := hb (x (-4) 4 && x (-4) 10)
        clear * - r37572 b37573 b37574 d37543
        omega
      have d37575 : (x 0 11).toNat = 1 := by
        have r37576 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b37577 := hb (x (-4) 4)
        have b37578 := hb (x 0 11)
        have b37579 := hb (x (-1) 1 && x (-1) 12)
        have b37580 := hb (x (-2) 2 && x (-2) 13)
        have b37581 := hb (x (-3) 3 && x (-3) 14)
        clear * - r37576 b37577 b37578 b37579 b37580 b37581 g114 g115 g116 d37543
        omega
      have d37582 : (x 3 8).toNat = 0 := by
        have r37583 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e37584 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
        have e37585 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
        have e37586 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
        have e37587 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
        have e37588 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
        have e37589 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
        have b37590 := hb (x (-4) 7)
        have b37591 := hb (x (-3) 6)
        have b37592 := hb (x (-2) 5)
        have b37593 := hb (x (-1) 4)
        have b37594 := hb (x 0 11)
        have b37595 := hb (x 1 10)
        have b37596 := hb (x 2 9)
        have b37597 := hb (x 3 8)
        clear * - r37583 e37584 e37585 e37586 e37587 e37588 e37589 b37590 b37591 b37592 b37593 b37594 b37595 b37596 b37597 g22 d37575
        omega
      have d37598 : (x 3 3 && x 3 8).toNat = 0 := by
        have r37599 := hand2 (x 3 3) (x 3 8)
        have b37600 := hb (x 3 8)
        have b37601 := hb (x 3 3 && x 3 8)
        clear * - r37599 b37600 b37601 d37582
        omega
      have d37602 : (x 2 9).toNat = 0 := by
        have r37603 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e37604 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
        have e37605 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
        have e37606 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
        have e37607 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
        have e37608 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
        have e37609 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
        have b37610 := hb (x (-4) 7)
        have b37611 := hb (x (-3) 6)
        have b37612 := hb (x (-2) 5)
        have b37613 := hb (x (-1) 4)
        have b37614 := hb (x 0 11)
        have b37615 := hb (x 1 10)
        have b37616 := hb (x 2 9)
        have b37617 := hb (x 3 8)
        clear * - r37603 e37604 e37605 e37606 e37607 e37608 e37609 b37610 b37611 b37612 b37613 b37614 b37615 b37616 b37617 d37582 g22 d37575
        omega
      have d37618 : (x (-5) 5).toNat = 0 := by
        have r37619 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e37620 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
        have e37621 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
        have e37622 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
        have e37623 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
        have e37624 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
        have e37625 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
        have b37626 := hb (x (-7) 7)
        have b37627 := hb (x (-6) 6)
        have b37628 := hb (x (-5) 5)
        have b37629 := hb (x (-4) 4)
        have b37630 := hb (x (-3) 11)
        have b37631 := hb (x (-2) 10)
        have b37632 := hb (x (-1) 9)
        have b37633 := hb (x 0 8)
        clear * - r37619 e37620 e37621 e37622 e37623 e37624 e37625 b37626 b37627 b37628 b37629 b37630 b37631 b37632 b37633 f37542 g7 g3 g1 d37543
        omega
      have d37634 : (x (-5) 5 && x (-5) 14).toNat = 0 := by
        have r37635 := hand1 (x (-5) 5) (x (-5) 14)
        have b37636 := hb (x (-5) 5)
        have b37637 := hb (x (-5) 5 && x (-5) 14)
        clear * - r37635 b37636 b37637 d37618
        omega
      have d37638 : (x (-5) 5 && x (-5) 12).toNat = 0 := by
        have r37639 := hand1 (x (-5) 5) (x (-5) 12)
        have b37640 := hb (x (-5) 5)
        have b37641 := hb (x (-5) 5 && x (-5) 12)
        clear * - r37639 b37640 b37641 d37618
        omega
      have d37642 : (x (-5) 5 && x (-5) 11).toNat = 0 := by
        have r37643 := hand1 (x (-5) 5) (x (-5) 11)
        have b37644 := hb (x (-5) 5)
        have b37645 := hb (x (-5) 5 && x (-5) 11)
        clear * - r37643 b37644 b37645 d37618
        omega
      have d37646 : (x 0 10).toNat = 1 := by
        have r37647 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b37648 := hb (x (-5) 5)
        have b37649 := hb (x 0 10)
        have b37650 := hb (x (-1) 1 && x (-1) 11)
        have b37651 := hb (x (-2) 2 && x (-2) 12)
        have b37652 := hb (x (-3) 3 && x (-3) 13)
        have b37653 := hb (x (-4) 4 && x (-4) 14)
        clear * - r37647 b37648 b37649 b37650 b37651 b37652 b37653 g109 g110 g111 d37559 d37618
        omega
      have d37654 : (x 2 8).toNat = 0 := by
        have r37655 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e37656 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e37657 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e37658 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e37659 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e37660 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e37661 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b37662 := hb (x (-5) 7)
        have b37663 := hb (x (-4) 6)
        have b37664 := hb (x (-3) 5)
        have b37665 := hb (x (-2) 4)
        have b37666 := hb (x (-1) 11)
        have b37667 := hb (x 0 10)
        have b37668 := hb (x 1 9)
        have b37669 := hb (x 2 8)
        clear * - r37655 e37656 e37657 e37658 e37659 e37660 e37661 b37662 b37663 b37664 b37665 b37666 b37667 b37668 b37669 d37646 g9
        omega
      have d37670 : (x 1 9).toNat = 0 := by
        have r37671 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e37672 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e37673 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e37674 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e37675 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e37676 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e37677 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b37678 := hb (x (-5) 7)
        have b37679 := hb (x (-4) 6)
        have b37680 := hb (x (-3) 5)
        have b37681 := hb (x (-2) 4)
        have b37682 := hb (x (-1) 11)
        have b37683 := hb (x 0 10)
        have b37684 := hb (x 1 9)
        have b37685 := hb (x 2 8)
        clear * - r37671 e37672 e37673 e37674 e37675 e37676 e37677 b37678 b37679 b37680 b37681 b37682 b37683 b37684 b37685 d37654 d37646 g9
        omega
      have d37686 : (x (-2) 4).toNat = 0 := by
        have r37687 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e37688 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e37689 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e37690 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e37691 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e37692 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e37693 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b37694 := hb (x (-5) 7)
        have b37695 := hb (x (-4) 6)
        have b37696 := hb (x (-3) 5)
        have b37697 := hb (x (-2) 4)
        have b37698 := hb (x (-1) 11)
        have b37699 := hb (x 0 10)
        have b37700 := hb (x 1 9)
        have b37701 := hb (x 2 8)
        clear * - r37687 e37688 e37689 e37690 e37691 e37692 e37693 b37694 b37695 b37696 b37697 b37698 b37699 b37700 b37701 d37654 d37670 d37646 g9
        omega
      have d37702 : (x (-2) 4 && x (-2) 9).toNat = 0 := by
        have r37703 := hand1 (x (-2) 4) (x (-2) 9)
        have b37704 := hb (x (-2) 4)
        have b37705 := hb (x (-2) 4 && x (-2) 9)
        clear * - r37703 b37704 b37705 d37686
        omega
      have d37706 : (x (-3) 5).toNat = 0 := by
        have r37707 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e37708 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e37709 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e37710 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e37711 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e37712 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e37713 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b37714 := hb (x (-5) 7)
        have b37715 := hb (x (-4) 6)
        have b37716 := hb (x (-3) 5)
        have b37717 := hb (x (-2) 4)
        have b37718 := hb (x (-1) 11)
        have b37719 := hb (x 0 10)
        have b37720 := hb (x 1 9)
        have b37721 := hb (x 2 8)
        clear * - r37707 e37708 e37709 e37710 e37711 e37712 e37713 b37714 b37715 b37716 b37717 b37718 b37719 b37720 b37721 d37654 d37670 d37646 g9 d37686
        omega
      have d37722 : (x (-3) 5 && x (-3) 10).toNat = 0 := by
        have r37723 := hand1 (x (-3) 5) (x (-3) 10)
        have b37724 := hb (x (-3) 5)
        have b37725 := hb (x (-3) 5 && x (-3) 10)
        clear * - r37723 b37724 b37725 d37706
        omega
      have d37726 : (x (-4) 6).toNat = 0 := by
        have r37727 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e37728 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e37729 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e37730 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e37731 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e37732 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e37733 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b37734 := hb (x (-5) 7)
        have b37735 := hb (x (-4) 6)
        have b37736 := hb (x (-3) 5)
        have b37737 := hb (x (-2) 4)
        have b37738 := hb (x (-1) 11)
        have b37739 := hb (x 0 10)
        have b37740 := hb (x 1 9)
        have b37741 := hb (x 2 8)
        clear * - r37727 e37728 e37729 e37730 e37731 e37732 e37733 b37734 b37735 b37736 b37737 b37738 b37739 b37740 b37741 d37654 d37670 d37646 g9 d37686 d37706
        omega
      have d37742 : (x (-4) 6 && x (-4) 11).toNat = 0 := by
        have r37743 := hand1 (x (-4) 6) (x (-4) 11)
        have b37744 := hb (x (-4) 6)
        have b37745 := hb (x (-4) 6 && x (-4) 11)
        clear * - r37743 b37744 b37745 d37726
        omega
      have d37746 : (x (-5) 7).toNat = 0 := by
        have r37747 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e37748 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e37749 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e37750 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e37751 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e37752 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e37753 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b37754 := hb (x (-5) 7)
        have b37755 := hb (x (-4) 6)
        have b37756 := hb (x (-3) 5)
        have b37757 := hb (x (-2) 4)
        have b37758 := hb (x (-1) 11)
        have b37759 := hb (x 0 10)
        have b37760 := hb (x 1 9)
        have b37761 := hb (x 2 8)
        clear * - r37747 e37748 e37749 e37750 e37751 e37752 e37753 b37754 b37755 b37756 b37757 b37758 b37759 b37760 b37761 d37654 d37670 d37646 g9 d37686 d37706 d37726
        omega
      have d37762 : (x (-5) 7 && x (-5) 12).toNat = 0 := by
        have r37763 := hand1 (x (-5) 7) (x (-5) 12)
        have b37764 := hb (x (-5) 7)
        have b37765 := hb (x (-5) 7 && x (-5) 12)
        clear * - r37763 b37764 b37765 d37746
        omega
      have d37766 : (x (-6) 6).toNat = 0 := by
        have r37767 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e37768 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
        have e37769 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
        have e37770 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
        have e37771 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
        have e37772 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
        have e37773 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
        have b37774 := hb (x (-7) 7)
        have b37775 := hb (x (-6) 6)
        have b37776 := hb (x (-5) 5)
        have b37777 := hb (x (-4) 4)
        have b37778 := hb (x (-3) 11)
        have b37779 := hb (x (-2) 10)
        have b37780 := hb (x (-1) 9)
        have b37781 := hb (x 0 8)
        clear * - r37767 e37768 e37769 e37770 e37771 e37772 e37773 b37774 b37775 b37776 b37777 b37778 b37779 b37780 b37781 f37542 g7 g3 g1 d37543 d37618
        omega
      have d37782 : (x (-6) 6 && x (-6) 13).toNat = 0 := by
        have r37783 := hand1 (x (-6) 6) (x (-6) 13)
        have b37784 := hb (x (-6) 6)
        have b37785 := hb (x (-6) 6 && x (-6) 13)
        clear * - r37783 b37784 b37785 d37766
        omega
      have d37786 : (x (-6) 6 && x (-6) 12).toNat = 0 := by
        have r37787 := hand1 (x (-6) 6) (x (-6) 12)
        have b37788 := hb (x (-6) 6)
        have b37789 := hb (x (-6) 6 && x (-6) 12)
        clear * - r37787 b37788 b37789 d37766
        omega
      have d37790 : (x 0 9).toNat = 1 := by
        have r37791 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b37792 := hb (x (-6) 6)
        have b37793 := hb (x 0 9)
        have b37794 := hb (x (-1) 1 && x (-1) 10)
        have b37795 := hb (x (-2) 2 && x (-2) 11)
        have b37796 := hb (x (-3) 3 && x (-3) 12)
        have b37797 := hb (x (-4) 4 && x (-4) 13)
        have b37798 := hb (x (-5) 5 && x (-5) 14)
        clear * - r37791 b37792 b37793 b37794 b37795 b37796 b37797 b37798 g102 g103 g104 d37563 d37634 d37766
        omega
      have d37799 : (x 1 8).toNat = 0 := by
        have r37800 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e37801 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
        have e37802 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
        have e37803 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
        have e37804 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
        have e37805 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
        have e37806 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
        have b37807 := hb (x (-6) 7)
        have b37808 := hb (x (-5) 6)
        have b37809 := hb (x (-4) 5)
        have b37810 := hb (x (-3) 4)
        have b37811 := hb (x (-2) 11)
        have b37812 := hb (x (-1) 10)
        have b37813 := hb (x 0 9)
        have b37814 := hb (x 1 8)
        clear * - r37800 e37801 e37802 e37803 e37804 e37805 e37806 b37807 b37808 b37809 b37810 b37811 b37812 b37813 b37814 d37790 g8 g4
        omega
      have d37815 : (x (-3) 4).toNat = 0 := by
        have r37816 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e37817 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
        have e37818 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
        have e37819 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
        have e37820 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
        have e37821 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
        have e37822 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
        have b37823 := hb (x (-6) 7)
        have b37824 := hb (x (-5) 6)
        have b37825 := hb (x (-4) 5)
        have b37826 := hb (x (-3) 4)
        have b37827 := hb (x (-2) 11)
        have b37828 := hb (x (-1) 10)
        have b37829 := hb (x 0 9)
        have b37830 := hb (x 1 8)
        clear * - r37816 e37817 e37818 e37819 e37820 e37821 e37822 b37823 b37824 b37825 b37826 b37827 b37828 b37829 b37830 d37799 d37790 g8 g4
        omega
      have d37831 : (x (-3) 4 && x (-3) 10).toNat = 0 := by
        have r37832 := hand1 (x (-3) 4) (x (-3) 10)
        have b37833 := hb (x (-3) 4)
        have b37834 := hb (x (-3) 4 && x (-3) 10)
        clear * - r37832 b37833 b37834 d37815
        omega
      have d37835 : (x (-4) 5).toNat = 0 := by
        have r37836 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e37837 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
        have e37838 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
        have e37839 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
        have e37840 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
        have e37841 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
        have e37842 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
        have b37843 := hb (x (-6) 7)
        have b37844 := hb (x (-5) 6)
        have b37845 := hb (x (-4) 5)
        have b37846 := hb (x (-3) 4)
        have b37847 := hb (x (-2) 11)
        have b37848 := hb (x (-1) 10)
        have b37849 := hb (x 0 9)
        have b37850 := hb (x 1 8)
        clear * - r37836 e37837 e37838 e37839 e37840 e37841 e37842 b37843 b37844 b37845 b37846 b37847 b37848 b37849 b37850 d37799 d37790 g8 g4 d37815
        omega
      have d37851 : (x (-4) 5 && x (-4) 11).toNat = 0 := by
        have r37852 := hand1 (x (-4) 5) (x (-4) 11)
        have b37853 := hb (x (-4) 5)
        have b37854 := hb (x (-4) 5 && x (-4) 11)
        clear * - r37852 b37853 b37854 d37835
        omega
      have d37855 : (x (-5) 6).toNat = 0 := by
        have r37856 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e37857 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
        have e37858 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
        have e37859 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
        have e37860 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
        have e37861 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
        have e37862 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
        have b37863 := hb (x (-6) 7)
        have b37864 := hb (x (-5) 6)
        have b37865 := hb (x (-4) 5)
        have b37866 := hb (x (-3) 4)
        have b37867 := hb (x (-2) 11)
        have b37868 := hb (x (-1) 10)
        have b37869 := hb (x 0 9)
        have b37870 := hb (x 1 8)
        clear * - r37856 e37857 e37858 e37859 e37860 e37861 e37862 b37863 b37864 b37865 b37866 b37867 b37868 b37869 b37870 d37799 d37790 g8 g4 d37815 d37835
        omega
      have d37871 : (x (-5) 6 && x (-5) 12).toNat = 0 := by
        have r37872 := hand1 (x (-5) 6) (x (-5) 12)
        have b37873 := hb (x (-5) 6)
        have b37874 := hb (x (-5) 6 && x (-5) 12)
        clear * - r37872 b37873 b37874 d37855
        omega
      have d37875 : (x (-6) 7).toNat = 0 := by
        have r37876 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e37877 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
        have e37878 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
        have e37879 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
        have e37880 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
        have e37881 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
        have e37882 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
        have b37883 := hb (x (-6) 7)
        have b37884 := hb (x (-5) 6)
        have b37885 := hb (x (-4) 5)
        have b37886 := hb (x (-3) 4)
        have b37887 := hb (x (-2) 11)
        have b37888 := hb (x (-1) 10)
        have b37889 := hb (x 0 9)
        have b37890 := hb (x 1 8)
        clear * - r37876 e37877 e37878 e37879 e37880 e37881 e37882 b37883 b37884 b37885 b37886 b37887 b37888 b37889 b37890 d37799 d37790 g8 g4 d37815 d37835 d37855
        omega
      have d37891 : (x (-6) 7 && x (-6) 13).toNat = 0 := by
        have r37892 := hand1 (x (-6) 7) (x (-6) 13)
        have b37893 := hb (x (-6) 7)
        have b37894 := hb (x (-6) 7 && x (-6) 13)
        clear * - r37892 b37893 b37894 d37875
        omega
      have d37895 : (x (-7) 7).toNat = 0 := by
        have r37896 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e37897 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
        have e37898 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
        have e37899 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
        have e37900 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
        have e37901 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
        have e37902 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
        have b37903 := hb (x (-7) 7)
        have b37904 := hb (x (-6) 6)
        have b37905 := hb (x (-5) 5)
        have b37906 := hb (x (-4) 4)
        have b37907 := hb (x (-3) 11)
        have b37908 := hb (x (-2) 10)
        have b37909 := hb (x (-1) 9)
        have b37910 := hb (x 0 8)
        clear * - r37896 e37897 e37898 e37899 e37900 e37901 e37902 b37903 b37904 b37905 b37906 b37907 b37908 b37909 b37910 f37542 g7 g3 g1 d37543 d37618 d37766
        omega
      have d37911 : (x (-7) 7 && x (-7) 14).toNat = 0 := by
        have r37912 := hand1 (x (-7) 7) (x (-7) 14)
        have b37913 := hb (x (-7) 7)
        have b37914 := hb (x (-7) 7 && x (-7) 14)
        clear * - r37912 b37913 b37914 d37895
        omega
      have d37915 : (x (-7) 7 && x (-7) 13).toNat = 0 := by
        have r37916 := hand1 (x (-7) 7) (x (-7) 13)
        have b37917 := hb (x (-7) 7)
        have b37918 := hb (x (-7) 7 && x (-7) 13)
        clear * - r37916 b37917 b37918 d37895
        omega
      have d37919 : (x (-8) 8).toNat = 1 := by
        have r37920 : 1 ≤ (x 0 7).toNat + (x (-1) 1 && x (-1) 8).toNat + (x (-2) 2 && x (-2) 9).toNat + (x (-3) 3 && x (-3) 10).toNat + (x (-4) 4 && x (-4) 11).toNat + (x (-5) 5 && x (-5) 12).toNat + (x (-6) 6 && x (-6) 13).toNat + (x (-7) 7 && x (-7) 14).toNat + (x (-8) 8).toNat := by have q := hcov7 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b37921 := hb (x (-8) 8)
        have b37922 := hb (x 0 7)
        have b37923 := hb (x (-1) 1 && x (-1) 8)
        have b37924 := hb (x (-2) 2 && x (-2) 9)
        have b37925 := hb (x (-3) 3 && x (-3) 10)
        have b37926 := hb (x (-4) 4 && x (-4) 11)
        have b37927 := hb (x (-5) 5 && x (-5) 12)
        have b37928 := hb (x (-6) 6 && x (-6) 13)
        have b37929 := hb (x (-7) 7 && x (-7) 14)
        clear * - r37920 b37921 b37922 b37923 b37924 b37925 b37926 b37927 b37928 b37929 g14 g89 g90 g91 d37567 d37638 d37782 d37911
        omega
      have d37930 : (x (-9) 9).toNat = 0 := by
        have r37931 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e37932 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
        have e37933 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
        have e37934 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
        have e37935 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
        have e37936 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
        have e37937 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
        have b37938 := hb (x (-15) 7)
        have b37939 := hb (x (-14) 6)
        have b37940 := hb (x (-13) 5)
        have b37941 := hb (x (-12) 4)
        have b37942 := hb (x (-11) 11)
        have b37943 := hb (x (-10) 10)
        have b37944 := hb (x (-9) 9)
        have b37945 := hb (x (-8) 8)
        clear * - r37931 e37932 e37933 e37934 e37935 e37936 e37937 b37938 b37939 b37940 b37941 b37942 b37943 b37944 b37945 d37919
        omega
      have d37946 : (x (-10) 10).toNat = 0 := by
        have r37947 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e37948 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
        have e37949 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
        have e37950 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
        have e37951 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
        have e37952 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
        have e37953 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
        have b37954 := hb (x (-15) 7)
        have b37955 := hb (x (-14) 6)
        have b37956 := hb (x (-13) 5)
        have b37957 := hb (x (-12) 4)
        have b37958 := hb (x (-11) 11)
        have b37959 := hb (x (-10) 10)
        have b37960 := hb (x (-9) 9)
        have b37961 := hb (x (-8) 8)
        clear * - r37947 e37948 e37949 e37950 e37951 e37952 e37953 b37954 b37955 b37956 b37957 b37958 b37959 b37960 b37961 d37919 d37930
        omega
      have d37962 : (x (-11) 11).toNat = 0 := by
        have r37963 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e37964 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
        have e37965 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
        have e37966 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
        have e37967 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
        have e37968 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
        have e37969 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
        have b37970 := hb (x (-15) 7)
        have b37971 := hb (x (-14) 6)
        have b37972 := hb (x (-13) 5)
        have b37973 := hb (x (-12) 4)
        have b37974 := hb (x (-11) 11)
        have b37975 := hb (x (-10) 10)
        have b37976 := hb (x (-9) 9)
        have b37977 := hb (x (-8) 8)
        clear * - r37963 e37964 e37965 e37966 e37967 e37968 e37969 b37970 b37971 b37972 b37973 b37974 b37975 b37976 b37977 d37919 d37930 d37946
        omega
      have d37978 : (x (-12) 4).toNat = 0 := by
        have r37979 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e37980 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
        have e37981 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
        have e37982 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
        have e37983 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
        have e37984 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
        have e37985 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
        have b37986 := hb (x (-15) 7)
        have b37987 := hb (x (-14) 6)
        have b37988 := hb (x (-13) 5)
        have b37989 := hb (x (-12) 4)
        have b37990 := hb (x (-11) 11)
        have b37991 := hb (x (-10) 10)
        have b37992 := hb (x (-9) 9)
        have b37993 := hb (x (-8) 8)
        clear * - r37979 e37980 e37981 e37982 e37983 e37984 e37985 b37986 b37987 b37988 b37989 b37990 b37991 b37992 b37993 d37919 d37930 d37946 d37962
        omega
      have d37994 : (x (-8) 8 && x (-8) 14).toNat = 1 := by
        have r37995 : 1 ≤ (x 0 6).toNat + (x (-1) 1 && x (-1) 7).toNat + (x (-2) 2 && x (-2) 8).toNat + (x (-3) 3 && x (-3) 9).toNat + (x (-4) 4 && x (-4) 10).toNat + (x (-5) 5 && x (-5) 11).toNat + (x (-6) 6 && x (-6) 12).toNat + (x (-7) 7 && x (-7) 13).toNat + (x (-8) 8 && x (-8) 14).toNat + (x (-9) 9).toNat := by have q := hcov6 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b37996 := hb (x (-9) 9)
        have b37997 := hb (x 0 6)
        have b37998 := hb (x (-1) 1 && x (-1) 7)
        have b37999 := hb (x (-2) 2 && x (-2) 8)
        have b38000 := hb (x (-3) 3 && x (-3) 9)
        have b38001 := hb (x (-4) 4 && x (-4) 10)
        have b38002 := hb (x (-5) 5 && x (-5) 11)
        have b38003 := hb (x (-6) 6 && x (-6) 12)
        have b38004 := hb (x (-7) 7 && x (-7) 13)
        have b38005 := hb (x (-8) 8 && x (-8) 14)
        clear * - r37995 b37996 b37997 b37998 b37999 b38000 b38001 b38002 b38003 b38004 b38005 f37389 g73 g74 g75 d37571 d37642 d37786 d37915 d37930
        omega
      have d38006 : (x (-8) 14).toNat = 1 := by
        have r38007 := hand2 (x (-8) 8) (x (-8) 14)
        have b38008 := hb (x (-8) 14)
        have b38009 := hb (x (-8) 8 && x (-8) 14)
        clear * - r38007 b38008 b38009 d37994
        omega
      have d38010 : (x (-9) 1).toNat = 0 := by
        have r38011 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b38012 := hb (x (-9) 1)
        have b38013 := hb (x (-8) 14)
        clear * - r38011 b38012 b38013 d38006
        omega
      have d38014 : (x (-9) 1 && x (-9) 14).toNat = 0 := by
        have r38015 := hand1 (x (-9) 1) (x (-9) 14)
        have b38016 := hb (x (-9) 1)
        have b38017 := hb (x (-9) 1 && x (-9) 14)
        clear * - r38015 b38016 b38017 d38010
        omega
      have d38018 : (x (-9) 1 && x (-9) 12).toNat = 0 := by
        have r38019 := hand1 (x (-9) 1) (x (-9) 12)
        have b38020 := hb (x (-9) 1)
        have b38021 := hb (x (-9) 1 && x (-9) 12)
        clear * - r38019 b38020 b38021 d38010
        omega
      have d38022 : (x (-9) 13).toNat = 0 := by
        have r38023 : (x (-9) 13).toNat ≤ (x (-9) 1).toNat := himp _ _ (hp13 (-9))
        have b38024 := hb (x (-9) 1)
        have b38025 := hb (x (-9) 13)
        clear * - r38023 b38024 b38025 d38010
        omega
      have d38026 : (x (-9) 2 && x (-9) 13).toNat = 0 := by
        have r38027 := hand2 (x (-9) 2) (x (-9) 13)
        have b38028 := hb (x (-9) 13)
        have b38029 := hb (x (-9) 2 && x (-9) 13)
        clear * - r38027 b38028 b38029 d38022
        omega
      have d38030 : (x (-9) 8 && x (-9) 13).toNat = 0 := by
        have r38031 := hand2 (x (-9) 8) (x (-9) 13)
        have b38032 := hb (x (-9) 13)
        have b38033 := hb (x (-9) 8 && x (-9) 13)
        clear * - r38031 b38032 b38033 d38022
        omega
      cases h38034 : x 1 7
      · have f38035 : (x 1 7).toNat = 0 := by rw [h38034]; rfl
        cases h38036 : x (-1) 8
        · have f38037 : (x (-1) 8).toNat = 0 := by rw [h38036]; rfl
          have d38038 : (x (-1) 8 && x (-1) 14).toNat = 0 := by
            have r38039 := hand1 (x (-1) 8) (x (-1) 14)
            have b38040 := hb (x (-1) 8)
            have b38041 := hb (x (-1) 8 && x (-1) 14)
            clear * - r38039 b38040 b38041 f38037
            omega
          have d38042 : (x (-1) 8 && x (-1) 12).toNat = 0 := by
            have r38043 := hand1 (x (-1) 8) (x (-1) 12)
            have b38044 := hb (x (-1) 8)
            have b38045 := hb (x (-1) 8 && x (-1) 12)
            clear * - r38043 b38044 b38045 f38037
            omega
          cases h38046 : x (-1) 12
          · have f38047 : (x (-1) 12).toNat = 0 := by rw [h38046]; rfl
            cases h38048 : x (-1) 14
            · have f38049 : (x (-1) 14).toNat = 0 := by rw [h38048]; rfl
              have d38050 : (x (-2) 1).toNat = 1 := by
                have r38051 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b38052 := hb (x (-2) 1)
                have b38053 := hb (x (-1) 14)
                clear * - r38051 b38052 b38053 f38049
                omega
              have r38054 : (x (-2) 1).toNat + (x (-3) 2).toNat + (x (-4) 3).toNat + (x (-5) 4).toNat + (x (-6) 5).toNat + (x (-7) 6).toNat + (x (-8) 7).toNat + (x (-9) 8).toNat + (x (-10) 9).toNat + (x (-11) 10).toNat + (x (-12) 11).toNat + (x (-13) 12).toNat + (x (-14) 13).toNat + (x (-15) 14).toNat = 3 := by have q := hcount (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r38055 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r38056 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r38057 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e38058 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
              have e38059 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
              have e38060 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
              have e38061 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
              have e38062 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
              have e38063 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
              have r38064 : 1 ≤ (x (-1) 5).toNat + (x (-2) 1 && x (-2) 6).toNat + (x (-3) 2 && x (-3) 7).toNat + (x (-4) 3 && x (-4) 8).toNat + (x (-5) 4 && x (-5) 9).toNat + (x (-6) 5 && x (-6) 10).toNat + (x (-7) 6 && x (-7) 11).toNat + (x (-8) 7 && x (-8) 12).toNat + (x (-9) 8 && x (-9) 13).toNat + (x (-10) 9 && x (-10) 14).toNat + (x (-11) 10).toNat := by have q := hcov5 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r38065 : 1 ≤ (x 2 5).toNat + (x 1 1 && x 1 6).toNat + (x 0 2 && x 0 7).toNat + (x (-1) 3 && x (-1) 8).toNat + (x (-2) 4 && x (-2) 9).toNat + (x (-3) 5 && x (-3) 10).toNat + (x (-4) 6 && x (-4) 11).toNat + (x (-5) 7 && x (-5) 12).toNat + (x (-6) 8 && x (-6) 13).toNat + (x (-7) 9 && x (-7) 14).toNat + (x (-8) 10).toNat := by have q := hcov5 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r38066 : 1 ≤ (x 1 6).toNat + (x 0 1 && x 0 7).toNat + (x (-1) 2 && x (-1) 8).toNat + (x (-2) 3 && x (-2) 9).toNat + (x (-3) 4 && x (-3) 10).toNat + (x (-4) 5 && x (-4) 11).toNat + (x (-5) 6 && x (-5) 12).toNat + (x (-6) 7 && x (-6) 13).toNat + (x (-7) 8 && x (-7) 14).toNat + (x (-8) 9).toNat := by have q := hcov6 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r38067 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r38068 : 1 ≤ (x (-9) 11).toNat + (x (-10) 1 && x (-10) 12).toNat + (x (-11) 2 && x (-11) 13).toNat + (x (-12) 3 && x (-12) 14).toNat + (x (-13) 4).toNat := by have q := hcov11 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r38069 : 1 ≤ (x (-7) 11).toNat + (x (-8) 1 && x (-8) 12).toNat + (x (-9) 2 && x (-9) 13).toNat + (x (-10) 3 && x (-10) 14).toNat + (x (-11) 4).toNat := by have q := hcov11 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r38070 : (x (-13) 4).toNat ≤ (x (-13) 12).toNat := himp _ _ (hp4 (-13))
              have r38071 := hand2 (x (-4) 3) (x (-4) 8)
              have r38072 := hand2 (x (-5) 4) (x (-5) 9)
              have r38073 := hand2 (x (-6) 5) (x (-6) 10)
              have r38074 := hand1 (x (-7) 6) (x (-7) 11)
              have r38075 := hand1 (x (-8) 7) (x (-8) 12)
              have r38076 := hand1 (x (-10) 9) (x (-10) 14)
              have r38077 := hand1 (x (-6) 8) (x (-6) 13)
              have r38078 := hand1 (x (-7) 9) (x (-7) 14)
              have r38079 := hand1 (x (-7) 8) (x (-7) 14)
              have r38080 := hand1 (x (-3) 2) (x (-3) 12)
              have r38081 := hand1 (x (-4) 3) (x (-4) 13)
              have r38082 := hand1 (x (-5) 4) (x (-5) 14)
              have r38083 := hand2 (x (-10) 1) (x (-10) 12)
              have r38084 := hand2 (x (-11) 2) (x (-11) 13)
              have r38085 := hand2 (x (-12) 3) (x (-12) 14)
              have r38086 := hand2 (x (-8) 1) (x (-8) 12)
              have r38087 := hand2 (x (-10) 3) (x (-10) 14)
              linarith only [r38054, r38055, r38056, r38057, e38058, e38059, e38060, e38061, e38062, e38063, r38064, r38065, r38066, r38067, r38068, r38069, r38070, r38071, r38072, r38073, r38074, r38075, r38076, r38077, r38078, r38079, r38080, r38081, r38082, r38083, r38084, r38085, r38086, r38087, d38022, d37746, d37726, d37706, g0, d38050, d37686, g2, g5, g6, g8, g11, g12, g17, g18, g21, g25, g27, g30, g59, g60, d38030, g61, g62, g63, d37702, d37722, d37742, d37762, g76, g77, g78, d37831, d37851, d37871, d37891, g108, d38026]
            · have f38178 : (x (-1) 14).toNat = 1 := by rw [h38048]; rfl
              have d38179 : (x (-2) 1).toNat = 0 := by
                have r38180 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b38181 := hb (x (-2) 1)
                have b38182 := hb (x (-1) 14)
                clear * - r38180 b38181 b38182 f38178
                omega
              have d38183 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
                have r38184 := hand1 (x (-2) 1) (x (-2) 14)
                have b38185 := hb (x (-2) 1)
                have b38186 := hb (x (-2) 1 && x (-2) 14)
                clear * - r38184 b38185 b38186 d38179
                omega
              have d38187 : (x (-2) 13).toNat = 0 := by
                have r38188 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
                have b38189 := hb (x (-2) 1)
                have b38190 := hb (x (-2) 13)
                clear * - r38188 b38189 b38190 d38179
                omega
              have d38191 : (x (-2) 9 && x (-2) 13).toNat = 0 := by
                have r38192 := hand2 (x (-2) 9) (x (-2) 13)
                have b38193 := hb (x (-2) 13)
                have b38194 := hb (x (-2) 9 && x (-2) 13)
                clear * - r38192 b38193 b38194 d38187
                omega
              have d38195 : (x (-2) 9).toNat = 0 := by
                have r38196 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
                have b38197 := hb (x (-2) 1)
                have b38198 := hb (x (-2) 9)
                clear * - r38196 b38197 b38198 d38179
                omega
              have d38199 : (x (-3) 2).toNat = 1 := by
                have r38200 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b38201 := hb (x (-3) 2)
                have b38202 := hb (x (-1) 13)
                have b38203 := hb (x (-2) 1 && x (-2) 14)
                clear * - r38200 b38201 b38202 b38203 g10 d38183
                omega
              have d38204 : (x (-3) 14).toNat = 1 := by
                have r38205 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
                have b38206 := hb (x (-3) 2)
                have b38207 := hb (x (-3) 14)
                clear * - r38205 b38206 b38207 d38199
                omega
              have d38208 : (x (-4) 3).toNat = 0 := by
                have r38209 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e38210 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                have e38211 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                have b38212 := hb (x (-4) 3)
                have b38213 := hb (x (-3) 2)
                have b38214 := hb (x (-2) 13)
                have b38215 := hb (x (-1) 12)
                clear * - r38209 e38210 e38211 b38212 b38213 b38214 b38215 f38047 d38187 d38199
                omega
              have d38216 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
                have r38217 := hand1 (x (-4) 3) (x (-4) 12)
                have b38218 := hb (x (-4) 3)
                have b38219 := hb (x (-4) 3 && x (-4) 12)
                clear * - r38217 b38218 b38219 d38208
                omega
              have d38220 : (x (-4) 11).toNat = 0 := by
                have r38221 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
                have b38222 := hb (x (-4) 3)
                have b38223 := hb (x (-4) 11)
                clear * - r38221 b38222 b38223 d38208
                omega
              have r38224 : (x 6 1).toNat + (x 5 2).toNat + (x 4 3).toNat + (x 3 4).toNat + (x 2 5).toNat + (x 1 6).toNat + (x 0 7).toNat + (x (-1) 8).toNat + (x (-2) 9).toNat + (x (-3) 10).toNat + (x (-4) 11).toNat + (x (-5) 12).toNat + (x (-6) 13).toNat + (x (-7) 14).toNat = 3 := by have q := hcount 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r38225 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r38226 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r38227 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e38228 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e38229 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e38230 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e38231 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e38232 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e38233 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have r38234 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e38235 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
              have e38236 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
              have e38237 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
              have e38238 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
              have e38239 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
              have e38240 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
              have r38241 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e38242 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
              have e38243 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
              have r38244 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e38245 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
              have e38246 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
              have r38247 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e38248 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
              have e38249 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
              have r38250 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r38251 : 1 ≤ (x 7 4).toNat + (x 6 1 && x 6 5).toNat + (x 5 2 && x 5 6).toNat + (x 4 3 && x 4 7).toNat + (x 3 4 && x 3 8).toNat + (x 2 5 && x 2 9).toNat + (x 1 6 && x 1 10).toNat + (x 0 7 && x 0 11).toNat + (x (-1) 8 && x (-1) 12).toNat + (x (-2) 9 && x (-2) 13).toNat + (x (-3) 10 && x (-3) 14).toNat + (x (-4) 11).toNat := by have q := hcov4 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e38252 : (x 6 1 && x 6 5).toNat = (x 6 5).toNat := handr _ _ (fun h => hp13 6 (hp5 6 (h)))
              have e38253 : (x (-3) 10 && x (-3) 14).toNat = (x (-3) 10).toNat := handl _ _ (fun h => hp2 (-3) (hp10 (-3) (h)))
              have r38254 : 1 ≤ (x 7 6).toNat + (x 6 1 && x 6 7).toNat + (x 5 2 && x 5 8).toNat + (x 4 3 && x 4 9).toNat + (x 3 4 && x 3 10).toNat + (x 2 5 && x 2 11).toNat + (x 1 6 && x 1 12).toNat + (x 0 7 && x 0 13).toNat + (x (-1) 8 && x (-1) 14).toNat + (x (-2) 9).toNat := by have q := hcov6 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r38255 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r38256 : 1 ≤ (x 11 10).toNat + (x 10 1 && x 10 11).toNat + (x 9 2 && x 9 12).toNat + (x 8 3 && x 8 13).toNat + (x 7 4 && x 7 14).toNat + (x 6 5).toNat := by have q := hcov10 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r38257 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r38258 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r38259 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
              have r38260 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
              have r38261 := hand2 (x 5 2) (x 5 6)
              have r38262 := hand2 (x 4 3) (x 4 7)
              have r38263 := hand2 (x 6 1) (x 6 7)
              have r38264 := hand1 (x (-5) 4) (x (-5) 13)
              have r38265 := hand1 (x (-6) 5) (x (-6) 14)
              have r38266 := hand1 (x 10 1) (x 10 11)
              have r38267 := hand1 (x 9 2) (x 9 12)
              have r38268 := hand1 (x 8 3) (x 8 13)
              have r38269 := hand2 (x 7 4) (x 7 14)
              have r38270 := hand1 (x 10 1) (x 10 12)
              have r38271 := hand1 (x 9 2) (x 9 13)
              have r38272 := hand1 (x 8 3) (x 8 14)
              have r38273 := hand1 (x 12 1) (x 12 14)
              have b38278 := hb (x (-7) 14)
              linarith only [r38224, r38225, r38226, r38227, e38228, e38229, e38230, e38231, e38232, e38233, r38234, e38235, e38236, e38237, e38238, e38239, e38240, r38241, e38242, e38243, r38244, e38245, e38246, r38247, e38248, e38249, r38250, r38251, e38252, e38253, r38254, r38255, r38256, r38257, r38258, r38259, r38260, r38261, r38262, r38263, r38264, r38265, r38266, r38267, r38268, r38269, r38270, r38271, r38272, r38273, b38278, d38220, d38204, d38195, d38187, f38037, g7, f38047, f38178, g14, d37575, g16, g21, g22, g24, g27, d37602, d37372, g31, d37582, d37352, d37332, d37308, g50, g51, g52, g53, d38042, d38191, d37328, d37348, g82, g83, g84, g85, d38038, g100, g101, d38216]
          · have f38364 : (x (-1) 12).toNat = 1 := by rw [h38046]; rfl
            have d38365 : (x (-2) 13).toNat = 0 := by
              have r38366 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e38367 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e38368 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b38369 := hb (x (-4) 3)
              have b38370 := hb (x (-3) 2)
              have b38371 := hb (x (-2) 13)
              have b38372 := hb (x (-1) 12)
              clear * - r38366 e38367 e38368 b38369 b38370 b38371 b38372 f38364
              omega
            have d38373 : (x (-3) 2).toNat = 0 := by
              have r38374 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e38375 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e38376 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b38377 := hb (x (-4) 3)
              have b38378 := hb (x (-3) 2)
              have b38379 := hb (x (-2) 13)
              have b38380 := hb (x (-1) 12)
              clear * - r38374 e38375 e38376 b38377 b38378 b38379 b38380 f38364 d38365
              omega
            have d38381 : (x (-3) 2 && x (-3) 13).toNat = 0 := by
              have r38382 := hand1 (x (-3) 2) (x (-3) 13)
              have b38383 := hb (x (-3) 2)
              have b38384 := hb (x (-3) 2 && x (-3) 13)
              clear * - r38382 b38383 b38384 d38373
              omega
            have d38385 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
              have r38386 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b38387 := hb (x (-3) 2)
              have b38388 := hb (x (-1) 13)
              have b38389 := hb (x (-2) 1 && x (-2) 14)
              clear * - r38386 b38387 b38388 b38389 g10 d38373
              omega
            have d38390 : (x (-2) 14).toNat = 1 := by
              have r38391 := hand2 (x (-2) 1) (x (-2) 14)
              have b38392 := hb (x (-2) 14)
              have b38393 := hb (x (-2) 1 && x (-2) 14)
              clear * - r38391 b38392 b38393 d38385
              omega
            have d38394 : (x (-3) 1).toNat = 0 := by
              have r38395 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b38396 := hb (x (-3) 1)
              have b38397 := hb (x (-2) 14)
              clear * - r38395 b38396 b38397 d38390
              omega
            have d38398 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
              have r38399 := hand1 (x (-3) 1) (x (-3) 14)
              have b38400 := hb (x (-3) 1)
              have b38401 := hb (x (-3) 1 && x (-3) 14)
              clear * - r38399 b38400 b38401 d38394
              omega
            have d38402 : (x (-4) 2).toNat = 1 := by
              have r38403 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b38404 := hb (x (-4) 2)
              have b38405 := hb (x (-2) 13)
              have b38406 := hb (x (-3) 1 && x (-3) 14)
              clear * - r38403 b38404 b38405 b38406 d38365 d38398
              omega
            have d38407 : (x (-4) 14).toNat = 1 := by
              have r38408 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
              have b38409 := hb (x (-4) 2)
              have b38410 := hb (x (-4) 14)
              clear * - r38408 b38409 b38410 d38402
              omega
            have d38411 : (x (-5) 1).toNat = 0 := by
              have r38412 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b38413 := hb (x (-5) 1)
              have b38414 := hb (x (-4) 14)
              clear * - r38412 b38413 b38414 d38407
              omega
            have d38415 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
              have r38416 := hand1 (x (-5) 1) (x (-5) 12)
              have b38417 := hb (x (-5) 1)
              have b38418 := hb (x (-5) 1 && x (-5) 12)
              clear * - r38416 b38417 b38418 d38411
              omega
            have d38419 : (x (-5) 13).toNat = 0 := by
              have r38420 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
              have b38421 := hb (x (-5) 1)
              have b38422 := hb (x (-5) 13)
              clear * - r38420 b38421 b38422 d38411
              omega
            have d38423 : (x (-3) 13).toNat = 0 := by
              have r38424 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
              have b38425 := hb (x (-3) 1)
              have b38426 := hb (x (-3) 13)
              clear * - r38424 b38425 b38426 d38394
              omega
            have d38427 : (x (-4) 3).toNat = 0 := by
              have r38428 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e38429 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e38430 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b38431 := hb (x (-4) 3)
              have b38432 := hb (x (-3) 2)
              have b38433 := hb (x (-2) 13)
              have b38434 := hb (x (-1) 12)
              clear * - r38428 e38429 e38430 b38431 b38432 b38433 b38434 f38364 d38365 d38373
              omega
            have d38435 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
              have r38436 := hand1 (x (-4) 3) (x (-4) 14)
              have b38437 := hb (x (-4) 3)
              have b38438 := hb (x (-4) 3 && x (-4) 14)
              clear * - r38436 b38437 b38438 d38427
              omega
            have d38439 : (x (-4) 11).toNat = 0 := by
              have r38440 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
              have b38441 := hb (x (-4) 3)
              have b38442 := hb (x (-4) 11)
              clear * - r38440 b38441 b38442 d38427
              omega
            have d38443 : (x (-2) 12).toNat = 0 := by
              have r38444 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e38445 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
              have e38446 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
              have b38447 := hb (x (-5) 3)
              have b38448 := hb (x (-4) 2)
              have b38449 := hb (x (-3) 13)
              have b38450 := hb (x (-2) 12)
              clear * - r38444 e38445 e38446 b38447 b38448 b38449 b38450 d38423 d38402
              omega
            have d38451 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
              have r38452 := hand2 (x (-2) 1) (x (-2) 12)
              have b38453 := hb (x (-2) 12)
              have b38454 := hb (x (-2) 1 && x (-2) 12)
              clear * - r38452 b38453 b38454 d38443
              omega
            have d38455 : (x (-5) 3).toNat = 0 := by
              have r38456 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e38457 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
              have e38458 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
              have b38459 := hb (x (-5) 3)
              have b38460 := hb (x (-4) 2)
              have b38461 := hb (x (-3) 13)
              have b38462 := hb (x (-2) 12)
              clear * - r38456 e38457 e38458 b38459 b38460 b38461 b38462 d38443 d38423 d38402
              omega
            have d38463 : (x (-5) 11).toNat = 0 := by
              have r38464 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
              have b38465 := hb (x (-5) 3)
              have b38466 := hb (x (-5) 11)
              clear * - r38464 b38465 b38466 d38455
              omega
            have d38467 : (x (-5) 4).toNat = 1 := by
              have r38468 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b38469 := hb (x (-5) 4)
              have b38470 := hb (x (-1) 11)
              have b38471 := hb (x (-2) 1 && x (-2) 12)
              have b38472 := hb (x (-3) 2 && x (-3) 13)
              have b38473 := hb (x (-4) 3 && x (-4) 14)
              clear * - r38468 b38469 b38470 b38471 b38472 b38473 g9 d38451 d38381 d38435
              omega
            have d38474 : (x (-5) 12).toNat = 1 := by
              have r38475 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
              have b38476 := hb (x (-5) 4)
              have b38477 := hb (x (-5) 12)
              clear * - r38475 b38476 b38477 d38467
              omega
            have d38478 : (x (-6) 13).toNat = 0 := by
              have r38479 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e38480 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
              have e38481 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
              have b38482 := hb (x (-8) 3)
              have b38483 := hb (x (-7) 2)
              have b38484 := hb (x (-6) 13)
              have b38485 := hb (x (-5) 12)
              clear * - r38479 e38480 e38481 b38482 b38483 b38484 b38485 d38474
              omega
            have d38486 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
              have r38487 := hand2 (x (-6) 2) (x (-6) 13)
              have b38488 := hb (x (-6) 13)
              have b38489 := hb (x (-6) 2 && x (-6) 13)
              clear * - r38487 b38488 b38489 d38478
              omega
            have d38490 : (x (-7) 2).toNat = 0 := by
              have r38491 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e38492 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
              have e38493 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
              have b38494 := hb (x (-8) 3)
              have b38495 := hb (x (-7) 2)
              have b38496 := hb (x (-6) 13)
              have b38497 := hb (x (-5) 12)
              clear * - r38491 e38492 e38493 b38494 b38495 b38496 b38497 d38474 d38478
              omega
            have d38498 : (x (-7) 2 && x (-7) 13).toNat = 0 := by
              have r38499 := hand1 (x (-7) 2) (x (-7) 13)
              have b38500 := hb (x (-7) 2)
              have b38501 := hb (x (-7) 2 && x (-7) 13)
              clear * - r38499 b38500 b38501 d38490
              omega
            have d38502 : (x (-6) 1 && x (-6) 14).toNat = 1 := by
              have r38503 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b38504 := hb (x (-7) 2)
              have b38505 := hb (x (-5) 13)
              have b38506 := hb (x (-6) 1 && x (-6) 14)
              clear * - r38503 b38504 b38505 b38506 d38419 d38490
              omega
            have d38507 : (x (-6) 14).toNat = 1 := by
              have r38508 := hand2 (x (-6) 1) (x (-6) 14)
              have b38509 := hb (x (-6) 14)
              have b38510 := hb (x (-6) 1 && x (-6) 14)
              clear * - r38508 b38509 b38510 d38502
              omega
            have d38511 : (x (-7) 1).toNat = 0 := by
              have r38512 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b38513 := hb (x (-7) 1)
              have b38514 := hb (x (-6) 14)
              clear * - r38512 b38513 b38514 d38507
              omega
            have d38515 : (x (-7) 1 && x (-7) 14).toNat = 0 := by
              have r38516 := hand1 (x (-7) 1) (x (-7) 14)
              have b38517 := hb (x (-7) 1)
              have b38518 := hb (x (-7) 1 && x (-7) 14)
              clear * - r38516 b38517 b38518 d38511
              omega
            have d38519 : (x (-8) 2).toNat = 1 := by
              have r38520 : 1 ≤ (x (-6) 13).toNat + (x (-7) 1 && x (-7) 14).toNat + (x (-8) 2).toNat := by have q := hcov13 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b38521 := hb (x (-8) 2)
              have b38522 := hb (x (-6) 13)
              have b38523 := hb (x (-7) 1 && x (-7) 14)
              clear * - r38520 b38521 b38522 b38523 d38478 d38515
              omega
            have d38524 : (x (-6) 12).toNat = 0 := by
              have r38525 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e38526 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
              have e38527 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
              have b38528 := hb (x (-9) 3)
              have b38529 := hb (x (-8) 2)
              have b38530 := hb (x (-7) 13)
              have b38531 := hb (x (-6) 12)
              clear * - r38525 e38526 e38527 b38528 b38529 b38530 b38531 d38519
              omega
            have d38532 : (x (-6) 1 && x (-6) 12).toNat = 0 := by
              have r38533 := hand2 (x (-6) 1) (x (-6) 12)
              have b38534 := hb (x (-6) 12)
              have b38535 := hb (x (-6) 1 && x (-6) 12)
              clear * - r38533 b38534 b38535 d38524
              omega
            have d38536 : (x (-7) 13).toNat = 0 := by
              have r38537 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e38538 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
              have e38539 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
              have b38540 := hb (x (-9) 3)
              have b38541 := hb (x (-8) 2)
              have b38542 := hb (x (-7) 13)
              have b38543 := hb (x (-6) 12)
              clear * - r38537 e38538 e38539 b38540 b38541 b38542 b38543 d38524 d38519
              omega
            have d38544 : (x (-8) 3).toNat = 0 := by
              have r38545 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e38546 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
              have e38547 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
              have b38548 := hb (x (-8) 3)
              have b38549 := hb (x (-7) 2)
              have b38550 := hb (x (-6) 13)
              have b38551 := hb (x (-5) 12)
              clear * - r38545 e38546 e38547 b38548 b38549 b38550 b38551 d38474 d38478 d38490
              omega
            have d38552 : (x (-8) 3 && x (-8) 14).toNat = 0 := by
              have r38553 := hand1 (x (-8) 3) (x (-8) 14)
              have b38554 := hb (x (-8) 3)
              have b38555 := hb (x (-8) 3 && x (-8) 14)
              clear * - r38553 b38554 b38555 d38544
              omega
            have d38556 : (x (-8) 11).toNat = 0 := by
              have r38557 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
              have b38558 := hb (x (-8) 3)
              have b38559 := hb (x (-8) 11)
              clear * - r38557 b38558 b38559 d38544
              omega
            have d38560 : (x (-9) 4).toNat = 1 := by
              have r38561 : 1 ≤ (x (-5) 11).toNat + (x (-6) 1 && x (-6) 12).toNat + (x (-7) 2 && x (-7) 13).toNat + (x (-8) 3 && x (-8) 14).toNat + (x (-9) 4).toNat := by have q := hcov11 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b38562 := hb (x (-9) 4)
              have b38563 := hb (x (-5) 11)
              have b38564 := hb (x (-6) 1 && x (-6) 12)
              have b38565 := hb (x (-7) 2 && x (-7) 13)
              have b38566 := hb (x (-8) 3 && x (-8) 14)
              clear * - r38561 b38562 b38563 b38564 b38565 b38566 d38463 d38532 d38498 d38552
              omega
            have d38567 : (x (-9) 12).toNat = 1 := by
              have r38568 : (x (-9) 4).toNat ≤ (x (-9) 12).toNat := himp _ _ (hp4 (-9))
              have b38569 := hb (x (-9) 4)
              have b38570 := hb (x (-9) 12)
              clear * - r38568 b38569 b38570 d38560
              omega
            have d38571 : (x (-10) 13).toNat = 0 := by
              have r38572 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e38573 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
              have e38574 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
              have b38575 := hb (x (-12) 3)
              have b38576 := hb (x (-11) 2)
              have b38577 := hb (x (-10) 13)
              have b38578 := hb (x (-9) 12)
              clear * - r38572 e38573 e38574 b38575 b38576 b38577 b38578 d38567
              omega
            have d38579 : (x (-10) 2 && x (-10) 13).toNat = 0 := by
              have r38580 := hand2 (x (-10) 2) (x (-10) 13)
              have b38581 := hb (x (-10) 13)
              have b38582 := hb (x (-10) 2 && x (-10) 13)
              clear * - r38580 b38581 b38582 d38571
              omega
            have d38583 : (x (-11) 2).toNat = 0 := by
              have r38584 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e38585 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
              have e38586 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
              have b38587 := hb (x (-12) 3)
              have b38588 := hb (x (-11) 2)
              have b38589 := hb (x (-10) 13)
              have b38590 := hb (x (-9) 12)
              clear * - r38584 e38585 e38586 b38587 b38588 b38589 b38590 d38567 d38571
              omega
            have d38591 : (x (-10) 1 && x (-10) 14).toNat = 1 := by
              have r38592 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b38593 := hb (x (-11) 2)
              have b38594 := hb (x (-9) 13)
              have b38595 := hb (x (-10) 1 && x (-10) 14)
              clear * - r38592 b38593 b38594 b38595 d38022 d38583
              omega
            have d38596 : (x (-10) 1).toNat = 1 := by
              have r38597 := hand1 (x (-10) 1) (x (-10) 14)
              have b38598 := hb (x (-10) 1)
              have b38599 := hb (x (-10) 1 && x (-10) 14)
              clear * - r38597 b38598 b38599 d38591
              omega
            have d38600 : (x (-9) 14).toNat = 0 := by
              have r38601 : (x (-9) 14).toNat + (x (-10) 1).toNat = 1 := by have q := hd14 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b38602 := hb (x (-10) 1)
              have b38603 := hb (x (-9) 14)
              clear * - r38601 b38602 b38603 d38596
              omega
            have d38604 : (x (-9) 2).toNat = 0 := by
              have r38605 : (x (-9) 2).toNat ≤ (x (-9) 14).toNat := himp _ _ (hp2 (-9))
              have b38606 := hb (x (-9) 2)
              have b38607 := hb (x (-9) 14)
              clear * - r38605 b38606 b38607 d38600
              omega
            have d38608 : (x (-8) 1 && x (-8) 14).toNat = 1 := by
              have r38609 : 1 ≤ (x (-7) 13).toNat + (x (-8) 1 && x (-8) 14).toNat + (x (-9) 2).toNat := by have q := hcov13 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b38610 := hb (x (-9) 2)
              have b38611 := hb (x (-7) 13)
              have b38612 := hb (x (-8) 1 && x (-8) 14)
              clear * - r38609 b38610 b38611 b38612 d38536 d38604
              omega
            have d38613 : (x (-8) 1).toNat = 1 := by
              have r38614 := hand1 (x (-8) 1) (x (-8) 14)
              have b38615 := hb (x (-8) 1)
              have b38616 := hb (x (-8) 1 && x (-8) 14)
              clear * - r38614 b38615 b38616 d38608
              omega
            have d38617 : (x (-7) 14).toNat = 0 := by
              have r38618 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b38619 := hb (x (-8) 1)
              have b38620 := hb (x (-7) 14)
              clear * - r38618 b38619 b38620 d38613
              omega
            have d38621 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
              have r38622 := hand2 (x (-7) 3) (x (-7) 14)
              have b38623 := hb (x (-7) 14)
              have b38624 := hb (x (-7) 3 && x (-7) 14)
              clear * - r38622 b38623 b38624 d38617
              omega
            have d38625 : (x (-8) 4).toNat = 1 := by
              have r38626 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b38627 := hb (x (-8) 4)
              have b38628 := hb (x (-4) 11)
              have b38629 := hb (x (-5) 1 && x (-5) 12)
              have b38630 := hb (x (-6) 2 && x (-6) 13)
              have b38631 := hb (x (-7) 3 && x (-7) 14)
              clear * - r38626 b38627 b38628 b38629 b38630 b38631 d38439 d38415 d38486 d38621
              omega
            have d38632 : (x (-8) 12).toNat = 1 := by
              have r38633 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
              have b38634 := hb (x (-8) 4)
              have b38635 := hb (x (-8) 12)
              clear * - r38633 b38634 b38635 d38625
              omega
            have d38636 : (x (-10) 2).toNat = 0 := by
              have r38637 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e38638 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
              have e38639 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
              have b38640 := hb (x (-11) 3)
              have b38641 := hb (x (-10) 2)
              have b38642 := hb (x (-9) 13)
              have b38643 := hb (x (-8) 12)
              clear * - r38637 e38638 e38639 b38640 b38641 b38642 b38643 d38632 d38022
              omega
            have d38644 : (x (-11) 3).toNat = 0 := by
              have r38645 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e38646 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
              have e38647 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
              have b38648 := hb (x (-11) 3)
              have b38649 := hb (x (-10) 2)
              have b38650 := hb (x (-9) 13)
              have b38651 := hb (x (-8) 12)
              clear * - r38645 e38646 e38647 b38648 b38649 b38650 b38651 d38632 d38022 d38636
              omega
            have d38652 : (x (-11) 3 && x (-11) 14).toNat = 0 := by
              have r38653 := hand1 (x (-11) 3) (x (-11) 14)
              have b38654 := hb (x (-11) 3)
              have b38655 := hb (x (-11) 3 && x (-11) 14)
              clear * - r38653 b38654 b38655 d38644
              omega
            have r38656 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := by have q := hcov11 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b38657 := hb (x (-12) 4)
            have b38658 := hb (x (-8) 11)
            have b38659 := hb (x (-9) 1 && x (-9) 12)
            have b38660 := hb (x (-10) 2 && x (-10) 13)
            have b38661 := hb (x (-11) 3 && x (-11) 14)
            linarith only [r38656, b38657, b38658, b38659, b38660, b38661, d38556, d38018, d38579, d38652, d37978]
        · have f38662 : (x (-1) 8).toNat = 1 := by rw [h38036]; rfl
          have d38663 : (x (-2) 9).toNat = 0 := by
            have r38664 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e38665 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e38666 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e38667 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e38668 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e38669 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e38670 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have b38671 := hb (x (-8) 7)
            have b38672 := hb (x (-7) 6)
            have b38673 := hb (x (-6) 5)
            have b38674 := hb (x (-5) 4)
            have b38675 := hb (x (-4) 11)
            have b38676 := hb (x (-3) 10)
            have b38677 := hb (x (-2) 9)
            have b38678 := hb (x (-1) 8)
            clear * - r38664 e38665 e38666 e38667 e38668 e38669 e38670 b38671 b38672 b38673 b38674 b38675 b38676 b38677 b38678 f38662
            omega
          have d38679 : (x (-2) 9 && x (-2) 14).toNat = 0 := by
            have r38680 := hand1 (x (-2) 9) (x (-2) 14)
            have b38681 := hb (x (-2) 9)
            have b38682 := hb (x (-2) 9 && x (-2) 14)
            clear * - r38680 b38681 b38682 d38663
            omega
          have d38683 : (x (-3) 10).toNat = 0 := by
            have r38684 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e38685 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e38686 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e38687 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e38688 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e38689 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e38690 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have b38691 := hb (x (-8) 7)
            have b38692 := hb (x (-7) 6)
            have b38693 := hb (x (-6) 5)
            have b38694 := hb (x (-5) 4)
            have b38695 := hb (x (-4) 11)
            have b38696 := hb (x (-3) 10)
            have b38697 := hb (x (-2) 9)
            have b38698 := hb (x (-1) 8)
            clear * - r38684 e38685 e38686 e38687 e38688 e38689 e38690 b38691 b38692 b38693 b38694 b38695 b38696 b38697 b38698 f38662 d38663
            omega
          have d38699 : (x (-3) 1 && x (-3) 10).toNat = 0 := by
            have r38700 := hand2 (x (-3) 1) (x (-3) 10)
            have b38701 := hb (x (-3) 10)
            have b38702 := hb (x (-3) 1 && x (-3) 10)
            clear * - r38700 b38701 b38702 d38683
            omega
          have d38703 : (x (-4) 11).toNat = 0 := by
            have r38704 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e38705 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e38706 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e38707 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e38708 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e38709 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e38710 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have b38711 := hb (x (-8) 7)
            have b38712 := hb (x (-7) 6)
            have b38713 := hb (x (-6) 5)
            have b38714 := hb (x (-5) 4)
            have b38715 := hb (x (-4) 11)
            have b38716 := hb (x (-3) 10)
            have b38717 := hb (x (-2) 9)
            have b38718 := hb (x (-1) 8)
            clear * - r38704 e38705 e38706 e38707 e38708 e38709 e38710 b38711 b38712 b38713 b38714 b38715 b38716 b38717 b38718 f38662 d38663 d38683
            omega
          have d38719 : (x (-4) 2 && x (-4) 11).toNat = 0 := by
            have r38720 := hand2 (x (-4) 2) (x (-4) 11)
            have b38721 := hb (x (-4) 11)
            have b38722 := hb (x (-4) 2 && x (-4) 11)
            clear * - r38720 b38721 b38722 d38703
            omega
          have d38723 : (x (-4) 11 && x (-4) 12).toNat = 0 := by
            have r38724 := hand1 (x (-4) 11) (x (-4) 12)
            have b38725 := hb (x (-4) 11)
            have b38726 := hb (x (-4) 11 && x (-4) 12)
            clear * - r38724 b38725 b38726 d38703
            omega
          have d38727 : (x (-5) 4).toNat = 0 := by
            have r38728 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e38729 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e38730 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e38731 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e38732 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e38733 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e38734 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have b38735 := hb (x (-8) 7)
            have b38736 := hb (x (-7) 6)
            have b38737 := hb (x (-6) 5)
            have b38738 := hb (x (-5) 4)
            have b38739 := hb (x (-4) 11)
            have b38740 := hb (x (-3) 10)
            have b38741 := hb (x (-2) 9)
            have b38742 := hb (x (-1) 8)
            clear * - r38728 e38729 e38730 e38731 e38732 e38733 e38734 b38735 b38736 b38737 b38738 b38739 b38740 b38741 b38742 f38662 d38663 d38683 d38703
            omega
          have d38743 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
            have r38744 := hand1 (x (-5) 4) (x (-5) 14)
            have b38745 := hb (x (-5) 4)
            have b38746 := hb (x (-5) 4 && x (-5) 14)
            clear * - r38744 b38745 b38746 d38727
            omega
          have d38747 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
            have r38748 := hand1 (x (-5) 4) (x (-5) 13)
            have b38749 := hb (x (-5) 4)
            have b38750 := hb (x (-5) 4 && x (-5) 13)
            clear * - r38748 b38749 b38750 d38727
            omega
          have d38751 : (x (-6) 5).toNat = 0 := by
            have r38752 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e38753 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e38754 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e38755 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e38756 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e38757 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e38758 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have b38759 := hb (x (-8) 7)
            have b38760 := hb (x (-7) 6)
            have b38761 := hb (x (-6) 5)
            have b38762 := hb (x (-5) 4)
            have b38763 := hb (x (-4) 11)
            have b38764 := hb (x (-3) 10)
            have b38765 := hb (x (-2) 9)
            have b38766 := hb (x (-1) 8)
            clear * - r38752 e38753 e38754 e38755 e38756 e38757 e38758 b38759 b38760 b38761 b38762 b38763 b38764 b38765 b38766 f38662 d38663 d38683 d38703 d38727
            omega
          have d38767 : (x (-6) 5 && x (-6) 14).toNat = 0 := by
            have r38768 := hand1 (x (-6) 5) (x (-6) 14)
            have b38769 := hb (x (-6) 5)
            have b38770 := hb (x (-6) 5 && x (-6) 14)
            clear * - r38768 b38769 b38770 d38751
            omega
          have d38771 : (x (-7) 6).toNat = 0 := by
            have r38772 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e38773 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e38774 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e38775 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e38776 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e38777 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e38778 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have b38779 := hb (x (-8) 7)
            have b38780 := hb (x (-7) 6)
            have b38781 := hb (x (-6) 5)
            have b38782 := hb (x (-5) 4)
            have b38783 := hb (x (-4) 11)
            have b38784 := hb (x (-3) 10)
            have b38785 := hb (x (-2) 9)
            have b38786 := hb (x (-1) 8)
            clear * - r38772 e38773 e38774 e38775 e38776 e38777 e38778 b38779 b38780 b38781 b38782 b38783 b38784 b38785 b38786 f38662 d38663 d38683 d38703 d38727 d38751
            omega
          have d38787 : (x (-4) 3 && x (-4) 12).toNat = 1 := by
            have r38788 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b38789 := hb (x (-7) 6)
            have b38790 := hb (x (-1) 9)
            have b38791 := hb (x (-2) 1 && x (-2) 10)
            have b38792 := hb (x (-3) 2 && x (-3) 11)
            have b38793 := hb (x (-4) 3 && x (-4) 12)
            have b38794 := hb (x (-5) 4 && x (-5) 13)
            have b38795 := hb (x (-6) 5 && x (-6) 14)
            clear * - r38788 b38789 b38790 b38791 b38792 b38793 b38794 b38795 g7 g100 g101 d38747 d38767 d38771
            omega
          have d38796 : (x (-4) 12).toNat = 1 := by
            have r38797 := hand2 (x (-4) 3) (x (-4) 12)
            have b38798 := hb (x (-4) 12)
            have b38799 := hb (x (-4) 3 && x (-4) 12)
            clear * - r38797 b38798 b38799 d38787
            omega
          have d38800 : (x (-5) 13).toNat = 0 := by
            have r38801 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e38802 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
            have e38803 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
            have b38804 := hb (x (-7) 3)
            have b38805 := hb (x (-6) 2)
            have b38806 := hb (x (-5) 13)
            have b38807 := hb (x (-4) 12)
            clear * - r38801 e38802 e38803 b38804 b38805 b38806 b38807 d38796
            omega
          have d38808 : (x (-5) 12 && x (-5) 13).toNat = 0 := by
            have r38809 := hand2 (x (-5) 12) (x (-5) 13)
            have b38810 := hb (x (-5) 13)
            have b38811 := hb (x (-5) 12 && x (-5) 13)
            clear * - r38809 b38810 b38811 d38800
            omega
          have d38812 : (x (-6) 2).toNat = 0 := by
            have r38813 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e38814 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
            have e38815 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
            have b38816 := hb (x (-7) 3)
            have b38817 := hb (x (-6) 2)
            have b38818 := hb (x (-5) 13)
            have b38819 := hb (x (-4) 12)
            clear * - r38813 e38814 e38815 b38816 b38817 b38818 b38819 d38796 d38800
            omega
          have d38820 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
            have r38821 := hand1 (x (-6) 2) (x (-6) 13)
            have b38822 := hb (x (-6) 2)
            have b38823 := hb (x (-6) 2 && x (-6) 13)
            clear * - r38821 b38822 b38823 d38812
            omega
          have d38824 : (x (-7) 3).toNat = 0 := by
            have r38825 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e38826 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
            have e38827 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
            have b38828 := hb (x (-7) 3)
            have b38829 := hb (x (-6) 2)
            have b38830 := hb (x (-5) 13)
            have b38831 := hb (x (-4) 12)
            clear * - r38825 e38826 e38827 b38828 b38829 b38830 b38831 d38796 d38800 d38812
            omega
          have d38832 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
            have r38833 := hand1 (x (-7) 3) (x (-7) 14)
            have b38834 := hb (x (-7) 3)
            have b38835 := hb (x (-7) 3 && x (-7) 14)
            clear * - r38833 b38834 b38835 d38824
            omega
          have d38836 : (x (-4) 3).toNat = 1 := by
            have r38837 := hand1 (x (-4) 3) (x (-4) 12)
            have b38838 := hb (x (-4) 3)
            have b38839 := hb (x (-4) 3 && x (-4) 12)
            clear * - r38837 b38838 b38839 d38787
            omega
          have d38840 : (x (-1) 12).toNat = 0 := by
            have r38841 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e38842 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e38843 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b38844 := hb (x (-4) 3)
            have b38845 := hb (x (-3) 2)
            have b38846 := hb (x (-2) 13)
            have b38847 := hb (x (-1) 12)
            clear * - r38841 e38842 e38843 b38844 b38845 b38846 b38847 d38836
            omega
          have d38848 : (x (-1) 7 && x (-1) 12).toNat = 0 := by
            have r38849 := hand2 (x (-1) 7) (x (-1) 12)
            have b38850 := hb (x (-1) 12)
            have b38851 := hb (x (-1) 7 && x (-1) 12)
            clear * - r38849 b38850 b38851 d38840
            omega
          have d38852 : (x (-2) 13).toNat = 0 := by
            have r38853 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e38854 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e38855 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b38856 := hb (x (-4) 3)
            have b38857 := hb (x (-3) 2)
            have b38858 := hb (x (-2) 13)
            have b38859 := hb (x (-1) 12)
            clear * - r38853 e38854 e38855 b38856 b38857 b38858 b38859 d38840 d38836
            omega
          have d38860 : (x (-2) 8 && x (-2) 13).toNat = 0 := by
            have r38861 := hand2 (x (-2) 8) (x (-2) 13)
            have b38862 := hb (x (-2) 13)
            have b38863 := hb (x (-2) 8 && x (-2) 13)
            clear * - r38861 b38862 b38863 d38852
            omega
          have d38864 : (x (-3) 2).toNat = 0 := by
            have r38865 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e38866 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e38867 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b38868 := hb (x (-4) 3)
            have b38869 := hb (x (-3) 2)
            have b38870 := hb (x (-2) 13)
            have b38871 := hb (x (-1) 12)
            clear * - r38865 e38866 e38867 b38868 b38869 b38870 b38871 d38840 d38852 d38836
            omega
          have d38872 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
            have r38873 := hand1 (x (-3) 2) (x (-3) 12)
            have b38874 := hb (x (-3) 2)
            have b38875 := hb (x (-3) 2 && x (-3) 12)
            clear * - r38873 b38874 b38875 d38864
            omega
          have d38876 : (x (-4) 3 && x (-4) 13).toNat = 1 := by
            have r38877 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b38878 := hb (x (-6) 5)
            have b38879 := hb (x (-1) 10)
            have b38880 := hb (x (-2) 1 && x (-2) 11)
            have b38881 := hb (x (-3) 2 && x (-3) 12)
            have b38882 := hb (x (-4) 3 && x (-4) 13)
            have b38883 := hb (x (-5) 4 && x (-5) 14)
            clear * - r38877 b38878 b38879 b38880 b38881 b38882 b38883 g8 g108 d38872 d38743 d38751
            omega
          have d38884 : (x (-4) 13).toNat = 1 := by
            have r38885 := hand2 (x (-4) 3) (x (-4) 13)
            have b38886 := hb (x (-4) 13)
            have b38887 := hb (x (-4) 3 && x (-4) 13)
            clear * - r38885 b38886 b38887 d38876
            omega
          have d38888 : (x (-4) 1).toNat = 1 := by
            have r38889 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
            have b38890 := hb (x (-4) 1)
            have b38891 := hb (x (-4) 13)
            clear * - r38889 b38890 b38891 d38884
            omega
          have d38892 : (x (-3) 14).toNat = 0 := by
            have r38893 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b38894 := hb (x (-4) 1)
            have b38895 := hb (x (-3) 14)
            clear * - r38893 b38894 b38895 d38888
            omega
          have d38896 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
            have r38897 := hand2 (x (-3) 1) (x (-3) 14)
            have b38898 := hb (x (-3) 14)
            have b38899 := hb (x (-3) 1 && x (-3) 14)
            clear * - r38897 b38898 b38899 d38892
            omega
          have d38900 : (x (-4) 2).toNat = 1 := by
            have r38901 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b38902 := hb (x (-4) 2)
            have b38903 := hb (x (-2) 13)
            have b38904 := hb (x (-3) 1 && x (-3) 14)
            clear * - r38901 b38902 b38903 b38904 d38852 d38896
            omega
          have d38905 : (x (-4) 14).toNat = 1 := by
            have r38906 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
            have b38907 := hb (x (-4) 2)
            have b38908 := hb (x (-4) 14)
            clear * - r38906 b38907 b38908 d38900
            omega
          have d38909 : (x (-5) 1).toNat = 0 := by
            have r38910 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b38911 := hb (x (-5) 1)
            have b38912 := hb (x (-4) 14)
            clear * - r38910 b38911 b38912 d38905
            omega
          have d38913 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
            have r38914 := hand1 (x (-5) 1) (x (-5) 12)
            have b38915 := hb (x (-5) 1)
            have b38916 := hb (x (-5) 1 && x (-5) 12)
            clear * - r38914 b38915 b38916 d38909
            omega
          have d38917 : (x (-8) 4).toNat = 1 := by
            have r38918 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b38919 := hb (x (-8) 4)
            have b38920 := hb (x (-4) 11)
            have b38921 := hb (x (-5) 1 && x (-5) 12)
            have b38922 := hb (x (-6) 2 && x (-6) 13)
            have b38923 := hb (x (-7) 3 && x (-7) 14)
            clear * - r38918 b38919 b38920 b38921 b38922 b38923 d38703 d38913 d38820 d38832
            omega
          have d38924 : (x (-8) 12).toNat = 1 := by
            have r38925 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
            have b38926 := hb (x (-8) 4)
            have b38927 := hb (x (-8) 12)
            clear * - r38925 b38926 b38927 d38917
            omega
          have d38928 : (x (-10) 2).toNat = 0 := by
            have r38929 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e38930 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
            have e38931 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
            have b38932 := hb (x (-11) 3)
            have b38933 := hb (x (-10) 2)
            have b38934 := hb (x (-9) 13)
            have b38935 := hb (x (-8) 12)
            clear * - r38929 e38930 e38931 b38932 b38933 b38934 b38935 d38924 d38022
            omega
          have d38936 : (x (-10) 2 && x (-10) 13).toNat = 0 := by
            have r38937 := hand1 (x (-10) 2) (x (-10) 13)
            have b38938 := hb (x (-10) 2)
            have b38939 := hb (x (-10) 2 && x (-10) 13)
            clear * - r38937 b38938 b38939 d38928
            omega
          have d38940 : (x (-8) 13).toNat = 1 := by
            have r38941 : 1 ≤ (x (-8) 13).toNat + (x (-9) 1 && x (-9) 14).toNat + (x (-10) 2).toNat := by have q := hcov13 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b38942 := hb (x (-10) 2)
            have b38943 := hb (x (-8) 13)
            have b38944 := hb (x (-9) 1 && x (-9) 14)
            clear * - r38941 b38942 b38943 b38944 d38014 d38928
            omega
          have d38945 : (x (-8) 1).toNat = 1 := by
            have r38946 : (x (-8) 13).toNat ≤ (x (-8) 1).toNat := himp _ _ (hp13 (-8))
            have b38947 := hb (x (-8) 1)
            have b38948 := hb (x (-8) 13)
            clear * - r38946 b38947 b38948 d38940
            omega
          have d38949 : (x (-7) 14).toNat = 0 := by
            have r38950 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b38951 := hb (x (-8) 1)
            have b38952 := hb (x (-7) 14)
            clear * - r38950 b38951 b38952 d38945
            omega
          have d38953 : (x (-7) 1 && x (-7) 14).toNat = 0 := by
            have r38954 := hand2 (x (-7) 1) (x (-7) 14)
            have b38955 := hb (x (-7) 14)
            have b38956 := hb (x (-7) 1 && x (-7) 14)
            clear * - r38954 b38955 b38956 d38949
            omega
          have d38957 : (x (-7) 5 && x (-7) 14).toNat = 0 := by
            have r38958 := hand2 (x (-7) 5) (x (-7) 14)
            have b38959 := hb (x (-7) 14)
            have b38960 := hb (x (-7) 5 && x (-7) 14)
            clear * - r38958 b38959 b38960 d38949
            omega
          have d38961 : (x (-7) 2).toNat = 0 := by
            have r38962 : (x (-7) 2).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp2 (-7))
            have b38963 := hb (x (-7) 2)
            have b38964 := hb (x (-7) 14)
            clear * - r38962 b38963 b38964 d38949
            omega
          have d38965 : (x (-6) 1 && x (-6) 14).toNat = 1 := by
            have r38966 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b38967 := hb (x (-7) 2)
            have b38968 := hb (x (-5) 13)
            have b38969 := hb (x (-6) 1 && x (-6) 14)
            clear * - r38966 b38967 b38968 b38969 d38800 d38961
            omega
          have d38970 : (x (-6) 14).toNat = 1 := by
            have r38971 := hand2 (x (-6) 1) (x (-6) 14)
            have b38972 := hb (x (-6) 14)
            have b38973 := hb (x (-6) 1 && x (-6) 14)
            clear * - r38971 b38972 b38973 d38965
            omega
          have d38974 : (x (-7) 1).toNat = 0 := by
            have r38975 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b38976 := hb (x (-7) 1)
            have b38977 := hb (x (-6) 14)
            clear * - r38975 b38976 b38977 d38970
            omega
          have d38978 : (x (-7) 13).toNat = 0 := by
            have r38979 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
            have b38980 := hb (x (-7) 1)
            have b38981 := hb (x (-7) 13)
            clear * - r38979 b38980 b38981 d38974
            omega
          have d38982 : (x (-7) 5).toNat = 0 := by
            have r38983 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
            have b38984 := hb (x (-7) 5)
            have b38985 := hb (x (-7) 13)
            clear * - r38983 b38984 b38985 d38978
            omega
          have d38986 : (x (-11) 3).toNat = 0 := by
            have r38987 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e38988 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
            have e38989 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
            have b38990 := hb (x (-11) 3)
            have b38991 := hb (x (-10) 2)
            have b38992 := hb (x (-9) 13)
            have b38993 := hb (x (-8) 12)
            clear * - r38987 e38988 e38989 b38990 b38991 b38992 b38993 d38924 d38022 d38928
            omega
          have d38994 : (x (-11) 3 && x (-11) 14).toNat = 0 := by
            have r38995 := hand1 (x (-11) 3) (x (-11) 14)
            have b38996 := hb (x (-11) 3)
            have b38997 := hb (x (-11) 3 && x (-11) 14)
            clear * - r38995 b38996 b38997 d38986
            omega
          have d38998 : (x (-8) 11).toNat = 1 := by
            have r38999 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := by have q := hcov11 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b39000 := hb (x (-12) 4)
            have b39001 := hb (x (-8) 11)
            have b39002 := hb (x (-9) 1 && x (-9) 12)
            have b39003 := hb (x (-10) 2 && x (-10) 13)
            have b39004 := hb (x (-11) 3 && x (-11) 14)
            clear * - r38999 b39000 b39001 b39002 b39003 b39004 d38018 d38936 d38994 d37978
            omega
          have d39005 : (x (-8) 3).toNat = 1 := by
            have r39006 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
            have b39007 := hb (x (-8) 3)
            have b39008 := hb (x (-8) 11)
            clear * - r39006 b39007 b39008 d38998
            omega
          have d39009 : (x (-5) 12).toNat = 0 := by
            have r39010 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39011 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
            have e39012 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
            have b39013 := hb (x (-8) 3)
            have b39014 := hb (x (-7) 2)
            have b39015 := hb (x (-6) 13)
            have b39016 := hb (x (-5) 12)
            clear * - r39010 e39011 e39012 b39013 b39014 b39015 b39016 d38961 d39005
            omega
          have d39017 : (x (-5) 3 && x (-5) 12).toNat = 0 := by
            have r39018 := hand2 (x (-5) 3) (x (-5) 12)
            have b39019 := hb (x (-5) 12)
            have b39020 := hb (x (-5) 3 && x (-5) 12)
            clear * - r39018 b39019 b39020 d39009
            omega
          have d39021 : (x (-6) 13).toNat = 0 := by
            have r39022 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39023 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
            have e39024 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
            have b39025 := hb (x (-8) 3)
            have b39026 := hb (x (-7) 2)
            have b39027 := hb (x (-6) 13)
            have b39028 := hb (x (-5) 12)
            clear * - r39022 e39023 e39024 b39025 b39026 b39027 b39028 d39009 d38961 d39005
            omega
          have d39029 : (x (-6) 4 && x (-6) 13).toNat = 0 := by
            have r39030 := hand2 (x (-6) 4) (x (-6) 13)
            have b39031 := hb (x (-6) 13)
            have b39032 := hb (x (-6) 4 && x (-6) 13)
            clear * - r39030 b39031 b39032 d39021
            omega
          have d39033 : (x (-8) 6).toNat = 1 := by
            have r39034 : 1 ≤ (x (-2) 9).toNat + (x (-3) 1 && x (-3) 10).toNat + (x (-4) 2 && x (-4) 11).toNat + (x (-5) 3 && x (-5) 12).toNat + (x (-6) 4 && x (-6) 13).toNat + (x (-7) 5 && x (-7) 14).toNat + (x (-8) 6).toNat := by have q := hcov9 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b39035 := hb (x (-8) 6)
            have b39036 := hb (x (-2) 9)
            have b39037 := hb (x (-3) 1 && x (-3) 10)
            have b39038 := hb (x (-4) 2 && x (-4) 11)
            have b39039 := hb (x (-5) 3 && x (-5) 12)
            have b39040 := hb (x (-6) 4 && x (-6) 13)
            have b39041 := hb (x (-7) 5 && x (-7) 14)
            clear * - r39034 b39035 b39036 b39037 b39038 b39039 b39040 b39041 d38663 d38699 d38719 d39017 d39029 d38957
            omega
          have d39042 : (x (-6) 13 && x (-6) 14).toNat = 0 := by
            have r39043 := hand1 (x (-6) 13) (x (-6) 14)
            have b39044 := hb (x (-6) 13)
            have b39045 := hb (x (-6) 13 && x (-6) 14)
            clear * - r39043 b39044 b39045 d39021
            omega
          have d39046 : (x (-8) 2).toNat = 1 := by
            have r39047 : 1 ≤ (x (-6) 13).toNat + (x (-7) 1 && x (-7) 14).toNat + (x (-8) 2).toNat := by have q := hcov13 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b39048 := hb (x (-8) 2)
            have b39049 := hb (x (-6) 13)
            have b39050 := hb (x (-7) 1 && x (-7) 14)
            clear * - r39047 b39048 b39049 b39050 d39021 d38953
            omega
          have d39051 : (x (-6) 12).toNat = 0 := by
            have r39052 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39053 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
            have e39054 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
            have b39055 := hb (x (-9) 3)
            have b39056 := hb (x (-8) 2)
            have b39057 := hb (x (-7) 13)
            have b39058 := hb (x (-6) 12)
            clear * - r39052 e39053 e39054 b39055 b39056 b39057 b39058 d38978 d39046
            omega
          have d39059 : (x (-6) 4).toNat = 0 := by
            have r39060 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
            have b39061 := hb (x (-6) 4)
            have b39062 := hb (x (-6) 12)
            clear * - r39060 b39061 b39062 d39051
            omega
          have d39063 : (x (-2) 12).toNat = 0 := by
            have r39064 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39065 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
            have e39066 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
            have b39067 := hb (x (-5) 3)
            have b39068 := hb (x (-4) 2)
            have b39069 := hb (x (-3) 13)
            have b39070 := hb (x (-2) 12)
            clear * - r39064 e39065 e39066 b39067 b39068 b39069 b39070 d38900
            omega
          have d39071 : (x (-3) 13).toNat = 0 := by
            have r39072 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39073 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
            have e39074 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
            have b39075 := hb (x (-5) 3)
            have b39076 := hb (x (-4) 2)
            have b39077 := hb (x (-3) 13)
            have b39078 := hb (x (-2) 12)
            clear * - r39072 e39073 e39074 b39075 b39076 b39077 b39078 d39063 d38900
            omega
          have d39079 : (x (-5) 3).toNat = 0 := by
            have r39080 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39081 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
            have e39082 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
            have b39083 := hb (x (-5) 3)
            have b39084 := hb (x (-4) 2)
            have b39085 := hb (x (-3) 13)
            have b39086 := hb (x (-2) 12)
            clear * - r39080 e39081 e39082 b39083 b39084 b39085 b39086 d39063 d39071 d38900
            omega
          have d39087 : (x (-5) 11).toNat = 0 := by
            have r39088 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
            have b39089 := hb (x (-5) 3)
            have b39090 := hb (x (-5) 11)
            clear * - r39088 b39089 b39090 d39079
            omega
          have d39091 : (x (-3) 9 && x (-3) 14).toNat = 0 := by
            have r39092 := hand2 (x (-3) 9) (x (-3) 14)
            have b39093 := hb (x (-3) 14)
            have b39094 := hb (x (-3) 9 && x (-3) 14)
            clear * - r39092 b39093 b39094 d38892
            omega
          have d39095 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
            have r39096 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b39097 := hb (x (-3) 2)
            have b39098 := hb (x (-1) 13)
            have b39099 := hb (x (-2) 1 && x (-2) 14)
            clear * - r39096 b39097 b39098 b39099 g10 d38864
            omega
          have d39100 : (x (-2) 14).toNat = 1 := by
            have r39101 := hand2 (x (-2) 1) (x (-2) 14)
            have b39102 := hb (x (-2) 14)
            have b39103 := hb (x (-2) 1 && x (-2) 14)
            clear * - r39101 b39102 b39103 d39095
            omega
          have d39104 : (x (-3) 1).toNat = 0 := by
            have r39105 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b39106 := hb (x (-3) 1)
            have b39107 := hb (x (-2) 14)
            clear * - r39105 b39106 b39107 d39100
            omega
          have d39108 : (x (-3) 9).toNat = 0 := by
            have r39109 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
            have b39110 := hb (x (-3) 1)
            have b39111 := hb (x (-3) 9)
            clear * - r39109 b39110 b39111 d39104
            omega
          have d39112 : (x (-2) 1).toNat = 1 := by
            have r39113 := hand1 (x (-2) 1) (x (-2) 14)
            have b39114 := hb (x (-2) 1)
            have b39115 := hb (x (-2) 1 && x (-2) 14)
            clear * - r39113 b39114 b39115 d39095
            omega
          have d39116 : (x (-1) 14).toNat = 0 := by
            have r39117 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b39118 := hb (x (-2) 1)
            have b39119 := hb (x (-1) 14)
            clear * - r39117 b39118 b39119 d39112
            omega
          have d39120 : (x (-1) 7 && x (-1) 14).toNat = 0 := by
            have r39121 := hand2 (x (-1) 7) (x (-1) 14)
            have b39122 := hb (x (-1) 14)
            have b39123 := hb (x (-1) 7 && x (-1) 14)
            clear * - r39121 b39122 b39123 d39116
            omega
          have d39124 : (x (-1) 8 && x (-1) 14).toNat = 0 := by
            have r39125 := hand2 (x (-1) 8) (x (-1) 14)
            have b39126 := hb (x (-1) 14)
            have b39127 := hb (x (-1) 8 && x (-1) 14)
            clear * - r39125 b39126 b39127 d39116
            omega
          have d39128 : (x (-2) 8).toNat = 0 := by
            have r39129 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39130 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
            have e39131 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
            have e39132 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
            have e39133 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
            have e39134 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
            have e39135 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
            have b39136 := hb (x (-9) 7)
            have b39137 := hb (x (-8) 6)
            have b39138 := hb (x (-7) 5)
            have b39139 := hb (x (-6) 4)
            have b39140 := hb (x (-5) 11)
            have b39141 := hb (x (-4) 10)
            have b39142 := hb (x (-3) 9)
            have b39143 := hb (x (-2) 8)
            clear * - r39129 e39130 e39131 e39132 e39133 e39134 e39135 b39136 b39137 b39138 b39139 b39140 b39141 b39142 b39143 d39108 d39087 d39059 d38982 d39033
            omega
          have d39144 : (x (-4) 10).toNat = 0 := by
            have r39145 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39146 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
            have e39147 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
            have e39148 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
            have e39149 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
            have e39150 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
            have e39151 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
            have b39152 := hb (x (-9) 7)
            have b39153 := hb (x (-8) 6)
            have b39154 := hb (x (-7) 5)
            have b39155 := hb (x (-6) 4)
            have b39156 := hb (x (-5) 11)
            have b39157 := hb (x (-4) 10)
            have b39158 := hb (x (-3) 9)
            have b39159 := hb (x (-2) 8)
            clear * - r39145 e39146 e39147 e39148 e39149 e39150 e39151 b39152 b39153 b39154 b39155 b39156 b39157 b39158 b39159 d39128 d39108 d39087 d39059 d38982 d39033
            omega
          have d39160 : (x 6 7).toNat = 1 := by
            have r39161 : 1 ≤ (x 6 7).toNat + (x 5 1 && x 5 8).toNat + (x 4 2 && x 4 9).toNat + (x 3 3 && x 3 10).toNat + (x 2 4 && x 2 11).toNat + (x 1 5 && x 1 12).toNat + (x 0 6 && x 0 13).toNat + (x (-1) 7 && x (-1) 14).toNat + (x (-2) 8).toNat := by have q := hcov7 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b39162 := hb (x (-2) 8)
            have b39163 := hb (x 6 7)
            have b39164 := hb (x 5 1 && x 5 8)
            have b39165 := hb (x 4 2 && x 4 9)
            have b39166 := hb (x 3 3 && x 3 10)
            have b39167 := hb (x 2 4 && x 2 11)
            have b39168 := hb (x 1 5 && x 1 12)
            have b39169 := hb (x 0 6 && x 0 13)
            have b39170 := hb (x (-1) 7 && x (-1) 14)
            clear * - r39161 b39162 b39163 b39164 b39165 b39166 b39167 b39168 b39169 b39170 d37324 g92 d37368 g93 g94 d37390 d39120 d39128
            omega
          have d39171 : (x 13 8).toNat = 0 := by
            have r39172 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39173 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
            have e39174 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
            have e39175 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
            have e39176 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
            have e39177 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
            have e39178 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
            have b39179 := hb (x 6 7)
            have b39180 := hb (x 7 6)
            have b39181 := hb (x 8 5)
            have b39182 := hb (x 9 4)
            have b39183 := hb (x 10 11)
            have b39184 := hb (x 11 10)
            have b39185 := hb (x 12 9)
            have b39186 := hb (x 13 8)
            clear * - r39172 e39173 e39174 e39175 e39176 e39177 e39178 b39179 b39180 b39181 b39182 b39183 b39184 b39185 b39186 d39160
            omega
          have d39187 : (x 12 9).toNat = 0 := by
            have r39188 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39189 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
            have e39190 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
            have e39191 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
            have e39192 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
            have e39193 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
            have e39194 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
            have b39195 := hb (x 6 7)
            have b39196 := hb (x 7 6)
            have b39197 := hb (x 8 5)
            have b39198 := hb (x 9 4)
            have b39199 := hb (x 10 11)
            have b39200 := hb (x 11 10)
            have b39201 := hb (x 12 9)
            have b39202 := hb (x 13 8)
            clear * - r39188 e39189 e39190 e39191 e39192 e39193 e39194 b39195 b39196 b39197 b39198 b39199 b39200 b39201 b39202 d39171 d39160
            omega
          have d39203 : (x 11 10).toNat = 0 := by
            have r39204 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39205 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
            have e39206 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
            have e39207 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
            have e39208 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
            have e39209 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
            have e39210 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
            have b39211 := hb (x 6 7)
            have b39212 := hb (x 7 6)
            have b39213 := hb (x 8 5)
            have b39214 := hb (x 9 4)
            have b39215 := hb (x 10 11)
            have b39216 := hb (x 11 10)
            have b39217 := hb (x 12 9)
            have b39218 := hb (x 13 8)
            clear * - r39204 e39205 e39206 e39207 e39208 e39209 e39210 b39211 b39212 b39213 b39214 b39215 b39216 b39217 b39218 d39171 d39187 d39160
            omega
          have d39219 : (x 11 1 && x 11 10).toNat = 0 := by
            have r39220 := hand2 (x 11 1) (x 11 10)
            have b39221 := hb (x 11 10)
            have b39222 := hb (x 11 1 && x 11 10)
            clear * - r39220 b39221 b39222 d39203
            omega
          have d39223 : (x 10 11).toNat = 0 := by
            have r39224 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39225 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
            have e39226 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
            have e39227 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
            have e39228 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
            have e39229 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
            have e39230 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
            have b39231 := hb (x 6 7)
            have b39232 := hb (x 7 6)
            have b39233 := hb (x 8 5)
            have b39234 := hb (x 9 4)
            have b39235 := hb (x 10 11)
            have b39236 := hb (x 11 10)
            have b39237 := hb (x 12 9)
            have b39238 := hb (x 13 8)
            clear * - r39224 e39225 e39226 e39227 e39228 e39229 e39230 b39231 b39232 b39233 b39234 b39235 b39236 b39237 b39238 d39171 d39187 d39203 d39160
            omega
          have d39239 : (x 10 1 && x 10 11).toNat = 0 := by
            have r39240 := hand2 (x 10 1) (x 10 11)
            have b39241 := hb (x 10 11)
            have b39242 := hb (x 10 1 && x 10 11)
            clear * - r39240 b39241 b39242 d39223
            omega
          have d39243 : (x 10 2 && x 10 11).toNat = 0 := by
            have r39244 := hand2 (x 10 2) (x 10 11)
            have b39245 := hb (x 10 11)
            have b39246 := hb (x 10 2 && x 10 11)
            clear * - r39244 b39245 b39246 d39223
            omega
          have d39247 : (x 9 4).toNat = 0 := by
            have r39248 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39249 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
            have e39250 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
            have e39251 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
            have e39252 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
            have e39253 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
            have e39254 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
            have b39255 := hb (x 6 7)
            have b39256 := hb (x 7 6)
            have b39257 := hb (x 8 5)
            have b39258 := hb (x 9 4)
            have b39259 := hb (x 10 11)
            have b39260 := hb (x 11 10)
            have b39261 := hb (x 12 9)
            have b39262 := hb (x 13 8)
            clear * - r39248 e39249 e39250 e39251 e39252 e39253 e39254 b39255 b39256 b39257 b39258 b39259 b39260 b39261 b39262 d39171 d39187 d39203 d39223 d39160
            omega
          have d39263 : (x 8 5).toNat = 0 := by
            have r39264 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39265 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
            have e39266 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
            have e39267 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
            have e39268 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
            have e39269 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
            have e39270 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
            have b39271 := hb (x 6 7)
            have b39272 := hb (x 7 6)
            have b39273 := hb (x 8 5)
            have b39274 := hb (x 9 4)
            have b39275 := hb (x 10 11)
            have b39276 := hb (x 11 10)
            have b39277 := hb (x 12 9)
            have b39278 := hb (x 13 8)
            clear * - r39264 e39265 e39266 e39267 e39268 e39269 e39270 b39271 b39272 b39273 b39274 b39275 b39276 b39277 b39278 d39171 d39187 d39203 d39223 d39247 d39160
            omega
          have d39279 : (x 7 6).toNat = 0 := by
            have r39280 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39281 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
            have e39282 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
            have e39283 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
            have e39284 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
            have e39285 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
            have e39286 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
            have b39287 := hb (x 6 7)
            have b39288 := hb (x 7 6)
            have b39289 := hb (x 8 5)
            have b39290 := hb (x 9 4)
            have b39291 := hb (x 10 11)
            have b39292 := hb (x 11 10)
            have b39293 := hb (x 12 9)
            have b39294 := hb (x 13 8)
            clear * - r39280 e39281 e39282 e39283 e39284 e39285 e39286 b39287 b39288 b39289 b39290 b39291 b39292 b39293 b39294 d39171 d39187 d39203 d39223 d39247 d39263 d39160
            omega
          have d39295 : (x 6 1 && x 6 7).toNat = 1 := by
            have r39296 : 1 ≤ (x 7 6).toNat + (x 6 1 && x 6 7).toNat + (x 5 2 && x 5 8).toNat + (x 4 3 && x 4 9).toNat + (x 3 4 && x 3 10).toNat + (x 2 5 && x 2 11).toNat + (x 1 6 && x 1 12).toNat + (x 0 7 && x 0 13).toNat + (x (-1) 8 && x (-1) 14).toNat + (x (-2) 9).toNat := by have q := hcov6 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b39297 := hb (x (-2) 9)
            have b39298 := hb (x 7 6)
            have b39299 := hb (x 6 1 && x 6 7)
            have b39300 := hb (x 5 2 && x 5 8)
            have b39301 := hb (x 4 3 && x 4 9)
            have b39302 := hb (x 3 4 && x 3 10)
            have b39303 := hb (x 2 5 && x 2 11)
            have b39304 := hb (x 1 6 && x 1 12)
            have b39305 := hb (x 0 7 && x 0 13)
            have b39306 := hb (x (-1) 8 && x (-1) 14)
            clear * - r39296 b39297 b39298 b39299 b39300 b39301 b39302 b39303 b39304 b39305 b39306 d39279 d37328 d37348 g82 g83 g84 g85 d39124 d38663
            omega
          have d39307 : (x 6 1).toNat = 1 := by
            have r39308 := hand1 (x 6 1) (x 6 7)
            have b39309 := hb (x 6 1)
            have b39310 := hb (x 6 1 && x 6 7)
            clear * - r39308 b39309 b39310 d39295
            omega
          have d39311 : (x 7 14).toNat = 0 := by
            have r39312 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b39313 := hb (x 6 1)
            have b39314 := hb (x 7 14)
            clear * - r39312 b39313 b39314 d39307
            omega
          have d39315 : (x 7 4 && x 7 14).toNat = 0 := by
            have r39316 := hand2 (x 7 4) (x 7 14)
            have b39317 := hb (x 7 14)
            have b39318 := hb (x 7 4 && x 7 14)
            clear * - r39316 b39317 b39318 d39311
            omega
          have d39319 : (x 7 5 && x 7 14).toNat = 0 := by
            have r39320 := hand2 (x 7 5) (x 7 14)
            have b39321 := hb (x 7 14)
            have b39322 := hb (x 7 5 && x 7 14)
            clear * - r39320 b39321 b39322 d39311
            omega
          have d39323 : (x 7 2).toNat = 0 := by
            have r39324 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
            have b39325 := hb (x 7 2)
            have b39326 := hb (x 7 14)
            clear * - r39324 b39325 b39326 d39311
            omega
          have d39327 : (x 7 2 && x 7 12).toNat = 0 := by
            have r39328 := hand1 (x 7 2) (x 7 12)
            have b39329 := hb (x 7 2)
            have b39330 := hb (x 7 2 && x 7 12)
            clear * - r39328 b39329 b39330 d39323
            omega
          have d39331 : (x 7 1).toNat = 0 := by
            have r39332 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b39333 := hb (x (-6) 14)
            have b39334 := hb (x (-5) 13)
            have b39335 := hb (x (-4) 12)
            have b39336 := hb (x (-3) 11)
            have b39337 := hb (x (-2) 10)
            have b39338 := hb (x (-1) 9)
            have b39339 := hb (x 0 8)
            have b39340 := hb (x 1 7)
            have b39341 := hb (x 2 6)
            have b39342 := hb (x 3 5)
            have b39343 := hb (x 4 4)
            have b39344 := hb (x 5 3)
            have b39345 := hb (x 6 2)
            have b39346 := hb (x 7 1)
            clear * - r39332 b39333 b39334 b39335 b39336 b39337 b39338 b39339 b39340 b39341 b39342 b39343 b39344 b39345 b39346 g33 g28 f38035 f37542 g7 g3 g1 d38796 d38800 d38970
            omega
          have d39347 : (x 7 13).toNat = 0 := by
            have r39348 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
            have b39349 := hb (x 7 1)
            have b39350 := hb (x 7 13)
            clear * - r39348 b39349 b39350 d39331
            omega
          have d39351 : (x 7 3 && x 7 13).toNat = 0 := by
            have r39352 := hand2 (x 7 3) (x 7 13)
            have b39353 := hb (x 7 13)
            have b39354 := hb (x 7 3 && x 7 13)
            clear * - r39352 b39353 b39354 d39347
            omega
          have d39355 : (x 7 5).toNat = 0 := by
            have r39356 : (x 7 5).toNat ≤ (x 7 13).toNat := himp _ _ (hp5 7)
            have b39357 := hb (x 7 5)
            have b39358 := hb (x 7 13)
            clear * - r39356 b39357 b39358 d39347
            omega
          have d39359 : (x 6 2).toNat = 0 := by
            have r39360 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b39361 := hb (x (-6) 14)
            have b39362 := hb (x (-5) 13)
            have b39363 := hb (x (-4) 12)
            have b39364 := hb (x (-3) 11)
            have b39365 := hb (x (-2) 10)
            have b39366 := hb (x (-1) 9)
            have b39367 := hb (x 0 8)
            have b39368 := hb (x 1 7)
            have b39369 := hb (x 2 6)
            have b39370 := hb (x 3 5)
            have b39371 := hb (x 4 4)
            have b39372 := hb (x 5 3)
            have b39373 := hb (x 6 2)
            have b39374 := hb (x 7 1)
            clear * - r39360 b39361 b39362 b39363 b39364 b39365 b39366 b39367 b39368 b39369 b39370 b39371 b39372 b39373 b39374 d39331 g33 g28 f38035 f37542 g7 g3 g1 d38796 d38800 d38970
            omega
          have d39375 : (x 6 1 && x 6 2).toNat = 0 := by
            have r39376 := hand2 (x 6 1) (x 6 2)
            have b39377 := hb (x 6 2)
            have b39378 := hb (x 6 1 && x 6 2)
            clear * - r39376 b39377 b39378 d39359
            omega
          have d39379 : (x 5 2 && x 5 3).toNat = 1 := by
            have r39380 : 1 ≤ (x 7 1).toNat + (x 6 1 && x 6 2).toNat + (x 5 2 && x 5 3).toNat + (x 4 3 && x 4 4).toNat + (x 3 4 && x 3 5).toNat + (x 2 5 && x 2 6).toNat + (x 1 6 && x 1 7).toNat + (x 0 7 && x 0 8).toNat + (x (-1) 8 && x (-1) 9).toNat + (x (-2) 9 && x (-2) 10).toNat + (x (-3) 10 && x (-3) 11).toNat + (x (-4) 11 && x (-4) 12).toNat + (x (-5) 12 && x (-5) 13).toNat + (x (-6) 13 && x (-6) 14).toNat + (x (-7) 14).toNat := by have q := hcov1 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b39381 := hb (x (-7) 14)
            have b39382 := hb (x 7 1)
            have b39383 := hb (x 6 1 && x 6 2)
            have b39384 := hb (x 5 2 && x 5 3)
            have b39385 := hb (x 4 3 && x 4 4)
            have b39386 := hb (x 3 4 && x 3 5)
            have b39387 := hb (x 2 5 && x 2 6)
            have b39388 := hb (x 1 6 && x 1 7)
            have b39389 := hb (x 0 7 && x 0 8)
            have b39390 := hb (x (-1) 8 && x (-1) 9)
            have b39391 := hb (x (-2) 9 && x (-2) 10)
            have b39392 := hb (x (-3) 10 && x (-3) 11)
            have b39393 := hb (x (-4) 11 && x (-4) 12)
            have b39394 := hb (x (-5) 12 && x (-5) 13)
            have b39395 := hb (x (-6) 13 && x (-6) 14)
            clear * - r39380 b39381 b39382 b39383 b39384 b39385 b39386 b39387 b39388 b39389 b39390 b39391 b39392 b39393 b39394 b39395 d39331 d39375 g37 g38 g39 g40 g41 g42 g43 g44 d38723 d38808 d39042 d38949
            omega
          have d39396 : (x 5 2).toNat = 1 := by
            have r39397 := hand1 (x 5 2) (x 5 3)
            have b39398 := hb (x 5 2)
            have b39399 := hb (x 5 2 && x 5 3)
            clear * - r39397 b39398 b39399 d39379
            omega
          have d39400 : (x 5 14).toNat = 1 := by
            have r39401 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
            have b39402 := hb (x 5 2)
            have b39403 := hb (x 5 14)
            clear * - r39401 b39402 b39403 d39396
            omega
          have d39404 : (x 4 1).toNat = 0 := by
            have r39405 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b39406 := hb (x 4 1)
            have b39407 := hb (x 5 14)
            clear * - r39405 b39406 b39407 d39400
            omega
          have d39408 : (x 4 13).toNat = 0 := by
            have r39409 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
            have b39410 := hb (x 4 1)
            have b39411 := hb (x 4 13)
            clear * - r39409 b39410 b39411 d39404
            omega
          have d39412 : (x 4 5).toNat = 0 := by
            have r39413 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
            have b39414 := hb (x 4 5)
            have b39415 := hb (x 4 13)
            clear * - r39413 b39414 b39415 d39408
            omega
          have d39416 : (x 7 12).toNat = 0 := by
            have r39417 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39418 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
            have e39419 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
            have b39420 := hb (x 4 3)
            have b39421 := hb (x 5 2)
            have b39422 := hb (x 6 13)
            have b39423 := hb (x 7 12)
            clear * - r39417 e39418 e39419 b39420 b39421 b39422 b39423 d39396
            omega
          have d39424 : (x 7 4).toNat = 0 := by
            have r39425 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
            have b39426 := hb (x 7 4)
            have b39427 := hb (x 7 12)
            clear * - r39425 b39426 b39427 d39416
            omega
          have d39428 : (x 6 13).toNat = 0 := by
            have r39429 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39430 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
            have e39431 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
            have b39432 := hb (x 4 3)
            have b39433 := hb (x 5 2)
            have b39434 := hb (x 6 13)
            have b39435 := hb (x 7 12)
            clear * - r39429 e39430 e39431 b39432 b39433 b39434 b39435 d39416 d39396
            omega
          have d39436 : (x 6 3 && x 6 13).toNat = 0 := by
            have r39437 := hand2 (x 6 3) (x 6 13)
            have b39438 := hb (x 6 13)
            have b39439 := hb (x 6 3 && x 6 13)
            clear * - r39437 b39438 b39439 d39428
            omega
          have d39440 : (x 6 5).toNat = 0 := by
            have r39441 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
            have b39442 := hb (x 6 5)
            have b39443 := hb (x 6 13)
            clear * - r39441 b39442 b39443 d39428
            omega
          have d39444 : (x 5 1 && x 5 6).toNat = 1 := by
            have r39445 : 1 ≤ (x 6 5).toNat + (x 5 1 && x 5 6).toNat + (x 4 2 && x 4 7).toNat + (x 3 3 && x 3 8).toNat + (x 2 4 && x 2 9).toNat + (x 1 5 && x 1 10).toNat + (x 0 6 && x 0 11).toNat + (x (-1) 7 && x (-1) 12).toNat + (x (-2) 8 && x (-2) 13).toNat + (x (-3) 9 && x (-3) 14).toNat + (x (-4) 10).toNat := by have q := hcov5 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b39446 := hb (x (-4) 10)
            have b39447 := hb (x 6 5)
            have b39448 := hb (x 5 1 && x 5 6)
            have b39449 := hb (x 4 2 && x 4 7)
            have b39450 := hb (x 3 3 && x 3 8)
            have b39451 := hb (x 2 4 && x 2 9)
            have b39452 := hb (x 1 5 && x 1 10)
            have b39453 := hb (x 0 6 && x 0 11)
            have b39454 := hb (x (-1) 7 && x (-1) 12)
            have b39455 := hb (x (-2) 8 && x (-2) 13)
            have b39456 := hb (x (-3) 9 && x (-3) 14)
            clear * - r39445 b39446 b39447 b39448 b39449 b39450 b39451 b39452 b39453 b39454 b39455 b39456 d39440 g64 d37598 g65 g66 d37394 d38848 d38860 d39091 d39144
            omega
          have d39457 : (x 5 6).toNat = 1 := by
            have r39458 := hand2 (x 5 1) (x 5 6)
            have b39459 := hb (x 5 6)
            have b39460 := hb (x 5 1 && x 5 6)
            clear * - r39458 b39459 b39460 d39444
            omega
          have d39461 : (x 11 8).toNat = 0 := by
            have r39462 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39463 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
            have e39464 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
            have e39465 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
            have e39466 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
            have e39467 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
            have e39468 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
            have b39469 := hb (x 4 7)
            have b39470 := hb (x 5 6)
            have b39471 := hb (x 6 5)
            have b39472 := hb (x 7 4)
            have b39473 := hb (x 8 11)
            have b39474 := hb (x 9 10)
            have b39475 := hb (x 10 9)
            have b39476 := hb (x 11 8)
            clear * - r39462 e39463 e39464 e39465 e39466 e39467 e39468 b39469 b39470 b39471 b39472 b39473 b39474 b39475 b39476 d39424 d39440 d39457
            omega
          have d39477 : (x 10 9).toNat = 0 := by
            have r39478 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39479 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
            have e39480 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
            have e39481 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
            have e39482 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
            have e39483 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
            have e39484 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
            have b39485 := hb (x 4 7)
            have b39486 := hb (x 5 6)
            have b39487 := hb (x 6 5)
            have b39488 := hb (x 7 4)
            have b39489 := hb (x 8 11)
            have b39490 := hb (x 9 10)
            have b39491 := hb (x 10 9)
            have b39492 := hb (x 11 8)
            clear * - r39478 e39479 e39480 e39481 e39482 e39483 e39484 b39485 b39486 b39487 b39488 b39489 b39490 b39491 b39492 d39461 d39424 d39440 d39457
            omega
          have d39493 : (x 9 10).toNat = 0 := by
            have r39494 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39495 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
            have e39496 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
            have e39497 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
            have e39498 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
            have e39499 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
            have e39500 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
            have b39501 := hb (x 4 7)
            have b39502 := hb (x 5 6)
            have b39503 := hb (x 6 5)
            have b39504 := hb (x 7 4)
            have b39505 := hb (x 8 11)
            have b39506 := hb (x 9 10)
            have b39507 := hb (x 10 9)
            have b39508 := hb (x 11 8)
            clear * - r39494 e39495 e39496 e39497 e39498 e39499 e39500 b39501 b39502 b39503 b39504 b39505 b39506 b39507 b39508 d39461 d39477 d39424 d39440 d39457
            omega
          have d39509 : (x 8 11).toNat = 0 := by
            have r39510 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39511 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
            have e39512 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
            have e39513 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
            have e39514 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
            have e39515 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
            have e39516 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
            have b39517 := hb (x 4 7)
            have b39518 := hb (x 5 6)
            have b39519 := hb (x 6 5)
            have b39520 := hb (x 7 4)
            have b39521 := hb (x 8 11)
            have b39522 := hb (x 9 10)
            have b39523 := hb (x 10 9)
            have b39524 := hb (x 11 8)
            clear * - r39510 e39511 e39512 e39513 e39514 e39515 e39516 b39517 b39518 b39519 b39520 b39521 b39522 b39523 b39524 d39461 d39477 d39493 d39424 d39440 d39457
            omega
          have d39525 : (x 8 1 && x 8 11).toNat = 0 := by
            have r39526 := hand2 (x 8 1) (x 8 11)
            have b39527 := hb (x 8 11)
            have b39528 := hb (x 8 1 && x 8 11)
            clear * - r39526 b39527 b39528 d39509
            omega
          have d39529 : (x 5 4 && x 5 14).toNat = 1 := by
            have r39530 : 1 ≤ (x 9 10).toNat + (x 8 1 && x 8 11).toNat + (x 7 2 && x 7 12).toNat + (x 6 3 && x 6 13).toNat + (x 5 4 && x 5 14).toNat + (x 4 5).toNat := by have q := hcov10 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b39531 := hb (x 4 5)
            have b39532 := hb (x 9 10)
            have b39533 := hb (x 8 1 && x 8 11)
            have b39534 := hb (x 7 2 && x 7 12)
            have b39535 := hb (x 6 3 && x 6 13)
            have b39536 := hb (x 5 4 && x 5 14)
            clear * - r39530 b39531 b39532 b39533 b39534 b39535 b39536 d39493 d39525 d39327 d39436 d39412
            omega
          have d39537 : (x 5 4).toNat = 1 := by
            have r39538 := hand1 (x 5 4) (x 5 14)
            have b39539 := hb (x 5 4)
            have b39540 := hb (x 5 4 && x 5 14)
            clear * - r39538 b39539 b39540 d39529
            omega
          have d39541 : (x 5 12).toNat = 1 := by
            have r39542 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
            have b39543 := hb (x 5 4)
            have b39544 := hb (x 5 12)
            clear * - r39542 b39543 b39544 d39537
            omega
          have d39545 : (x 3 2).toNat = 0 := by
            have r39546 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39547 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e39548 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b39549 := hb (x 2 3)
            have b39550 := hb (x 3 2)
            have b39551 := hb (x 4 13)
            have b39552 := hb (x 5 12)
            clear * - r39546 e39547 e39548 b39549 b39550 b39551 b39552 d39541 d39408
            omega
          have d39553 : (x 5 13).toNat = 1 := by
            have r39554 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b39555 := hb (x 3 2)
            have b39556 := hb (x 5 13)
            have b39557 := hb (x 4 1 && x 4 14)
            clear * - r39554 b39555 b39556 b39557 g117 d39545
            omega
          have d39558 : (x 5 1).toNat = 1 := by
            have r39559 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
            have b39560 := hb (x 5 1)
            have b39561 := hb (x 5 13)
            clear * - r39559 b39560 b39561 d39553
            omega
          have d39562 : (x 6 14).toNat = 0 := by
            have r39563 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b39564 := hb (x 5 1)
            have b39565 := hb (x 6 14)
            clear * - r39563 b39564 b39565 d39558
            omega
          have d39566 : (x 6 4 && x 6 14).toNat = 0 := by
            have r39567 := hand2 (x 6 4) (x 6 14)
            have b39568 := hb (x 6 14)
            have b39569 := hb (x 6 4 && x 6 14)
            clear * - r39567 b39568 b39569 d39562
            omega
          have d39570 : (x 6 6).toNat = 0 := by
            have r39571 : (x 6 6).toNat ≤ (x 6 14).toNat := himp _ _ (hp6 6)
            have b39572 := hb (x 6 6)
            have b39573 := hb (x 6 14)
            clear * - r39571 b39572 b39573 d39562
            omega
          have d39574 : (x 6 1 && x 6 6).toNat = 0 := by
            have r39575 := hand2 (x 6 1) (x 6 6)
            have b39576 := hb (x 6 6)
            have b39577 := hb (x 6 1 && x 6 6)
            clear * - r39575 b39576 b39577 d39570
            omega
          have d39578 : (x 5 2 && x 5 7).toNat = 1 := by
            have r39579 : 1 ≤ (x 7 5).toNat + (x 6 1 && x 6 6).toNat + (x 5 2 && x 5 7).toNat + (x 4 3 && x 4 8).toNat + (x 3 4 && x 3 9).toNat + (x 2 5 && x 2 10).toNat + (x 1 6 && x 1 11).toNat + (x 0 7 && x 0 12).toNat + (x (-1) 8 && x (-1) 13).toNat + (x (-2) 9 && x (-2) 14).toNat + (x (-3) 10).toNat := by have q := hcov5 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b39580 := hb (x (-3) 10)
            have b39581 := hb (x 7 5)
            have b39582 := hb (x 6 1 && x 6 6)
            have b39583 := hb (x 5 2 && x 5 7)
            have b39584 := hb (x 4 3 && x 4 8)
            have b39585 := hb (x 3 4 && x 3 9)
            have b39586 := hb (x 2 5 && x 2 10)
            have b39587 := hb (x 1 6 && x 1 11)
            have b39588 := hb (x 0 7 && x 0 12)
            have b39589 := hb (x (-1) 8 && x (-1) 13)
            have b39590 := hb (x (-2) 9 && x (-2) 14)
            clear * - r39579 b39580 b39581 b39582 b39583 b39584 b39585 b39586 b39587 b39588 b39589 b39590 d39355 d39574 g67 g68 g69 g70 g71 g72 d38679 d38683
            omega
          have d39591 : (x 5 7).toNat = 1 := by
            have r39592 := hand2 (x 5 2) (x 5 7)
            have b39593 := hb (x 5 7)
            have b39594 := hb (x 5 2 && x 5 7)
            clear * - r39592 b39593 b39594 d39578
            omega
          have d39595 : (x 12 8).toNat = 0 := by
            have r39596 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39597 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
            have e39598 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
            have e39599 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
            have e39600 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
            have e39601 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
            have e39602 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
            have b39603 := hb (x 5 7)
            have b39604 := hb (x 6 6)
            have b39605 := hb (x 7 5)
            have b39606 := hb (x 8 4)
            have b39607 := hb (x 9 11)
            have b39608 := hb (x 10 10)
            have b39609 := hb (x 11 9)
            have b39610 := hb (x 12 8)
            clear * - r39596 e39597 e39598 e39599 e39600 e39601 e39602 b39603 b39604 b39605 b39606 b39607 b39608 b39609 b39610 d39355 d39570 d39591
            omega
          have d39611 : (x 11 9).toNat = 0 := by
            have r39612 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39613 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
            have e39614 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
            have e39615 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
            have e39616 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
            have e39617 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
            have e39618 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
            have b39619 := hb (x 5 7)
            have b39620 := hb (x 6 6)
            have b39621 := hb (x 7 5)
            have b39622 := hb (x 8 4)
            have b39623 := hb (x 9 11)
            have b39624 := hb (x 10 10)
            have b39625 := hb (x 11 9)
            have b39626 := hb (x 12 8)
            clear * - r39612 e39613 e39614 e39615 e39616 e39617 e39618 b39619 b39620 b39621 b39622 b39623 b39624 b39625 b39626 d39595 d39355 d39570 d39591
            omega
          have d39627 : (x 10 10).toNat = 0 := by
            have r39628 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39629 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
            have e39630 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
            have e39631 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
            have e39632 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
            have e39633 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
            have e39634 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
            have b39635 := hb (x 5 7)
            have b39636 := hb (x 6 6)
            have b39637 := hb (x 7 5)
            have b39638 := hb (x 8 4)
            have b39639 := hb (x 9 11)
            have b39640 := hb (x 10 10)
            have b39641 := hb (x 11 9)
            have b39642 := hb (x 12 8)
            clear * - r39628 e39629 e39630 e39631 e39632 e39633 e39634 b39635 b39636 b39637 b39638 b39639 b39640 b39641 b39642 d39595 d39611 d39355 d39570 d39591
            omega
          have d39643 : (x 9 11).toNat = 0 := by
            have r39644 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39645 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
            have e39646 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
            have e39647 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
            have e39648 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
            have e39649 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
            have e39650 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
            have b39651 := hb (x 5 7)
            have b39652 := hb (x 6 6)
            have b39653 := hb (x 7 5)
            have b39654 := hb (x 8 4)
            have b39655 := hb (x 9 11)
            have b39656 := hb (x 10 10)
            have b39657 := hb (x 11 9)
            have b39658 := hb (x 12 8)
            clear * - r39644 e39645 e39646 e39647 e39648 e39649 e39650 b39651 b39652 b39653 b39654 b39655 b39656 b39657 b39658 d39595 d39611 d39627 d39355 d39570 d39591
            omega
          have d39659 : (x 9 1 && x 9 11).toNat = 0 := by
            have r39660 := hand2 (x 9 1) (x 9 11)
            have b39661 := hb (x 9 11)
            have b39662 := hb (x 9 1 && x 9 11)
            clear * - r39660 b39661 b39662 d39643
            omega
          have d39663 : (x 8 4).toNat = 0 := by
            have r39664 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39665 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
            have e39666 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
            have e39667 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
            have e39668 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
            have e39669 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
            have e39670 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
            have b39671 := hb (x 5 7)
            have b39672 := hb (x 6 6)
            have b39673 := hb (x 7 5)
            have b39674 := hb (x 8 4)
            have b39675 := hb (x 9 11)
            have b39676 := hb (x 10 10)
            have b39677 := hb (x 11 9)
            have b39678 := hb (x 12 8)
            clear * - r39664 e39665 e39666 e39667 e39668 e39669 e39670 b39671 b39672 b39673 b39674 b39675 b39676 b39677 b39678 d39595 d39611 d39627 d39643 d39355 d39570 d39591
            omega
          have d39679 : (x 8 4 && x 8 13).toNat = 0 := by
            have r39680 := hand1 (x 8 4) (x 8 13)
            have b39681 := hb (x 8 4)
            have b39682 := hb (x 8 4 && x 8 13)
            clear * - r39680 b39681 b39682 d39663
            omega
          have d39683 : (x 9 3 && x 9 12).toNat = 1 := by
            have r39684 : 1 ≤ (x 12 9).toNat + (x 11 1 && x 11 10).toNat + (x 10 2 && x 10 11).toNat + (x 9 3 && x 9 12).toNat + (x 8 4 && x 8 13).toNat + (x 7 5 && x 7 14).toNat + (x 6 6).toNat := by have q := hcov9 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b39685 := hb (x 6 6)
            have b39686 := hb (x 12 9)
            have b39687 := hb (x 11 1 && x 11 10)
            have b39688 := hb (x 10 2 && x 10 11)
            have b39689 := hb (x 9 3 && x 9 12)
            have b39690 := hb (x 8 4 && x 8 13)
            have b39691 := hb (x 7 5 && x 7 14)
            clear * - r39684 b39685 b39686 b39687 b39688 b39689 b39690 b39691 d39187 d39219 d39243 d39679 d39319 d39570
            omega
          have d39692 : (x 9 12).toNat = 1 := by
            have r39693 := hand2 (x 9 3) (x 9 12)
            have b39694 := hb (x 9 12)
            have b39695 := hb (x 9 3 && x 9 12)
            clear * - r39693 b39694 b39695 d39683
            omega
          have d39696 : (x 8 13).toNat = 0 := by
            have r39697 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39698 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
            have e39699 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
            have b39700 := hb (x 6 3)
            have b39701 := hb (x 7 2)
            have b39702 := hb (x 8 13)
            have b39703 := hb (x 9 12)
            clear * - r39697 e39698 e39699 b39700 b39701 b39702 b39703 d39692 d39323
            omega
          have d39704 : (x 8 3 && x 8 13).toNat = 0 := by
            have r39705 := hand2 (x 8 3) (x 8 13)
            have b39706 := hb (x 8 13)
            have b39707 := hb (x 8 3 && x 8 13)
            clear * - r39705 b39706 b39707 d39696
            omega
          have d39708 : (x 9 2 && x 9 12).toNat = 1 := by
            have r39709 : 1 ≤ (x 11 10).toNat + (x 10 1 && x 10 11).toNat + (x 9 2 && x 9 12).toNat + (x 8 3 && x 8 13).toNat + (x 7 4 && x 7 14).toNat + (x 6 5).toNat := by have q := hcov10 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b39710 := hb (x 6 5)
            have b39711 := hb (x 11 10)
            have b39712 := hb (x 10 1 && x 10 11)
            have b39713 := hb (x 9 2 && x 9 12)
            have b39714 := hb (x 8 3 && x 8 13)
            have b39715 := hb (x 7 4 && x 7 14)
            clear * - r39709 b39710 b39711 b39712 b39713 b39714 b39715 d39203 d39239 d39704 d39315 d39440
            omega
          have d39716 : (x 9 2).toNat = 1 := by
            have r39717 := hand1 (x 9 2) (x 9 12)
            have b39718 := hb (x 9 2)
            have b39719 := hb (x 9 2 && x 9 12)
            clear * - r39717 b39718 b39719 d39708
            omega
          have d39720 : (x 9 14).toNat = 1 := by
            have r39721 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
            have b39722 := hb (x 9 2)
            have b39723 := hb (x 9 14)
            clear * - r39721 b39722 b39723 d39716
            omega
          have d39724 : (x 8 1).toNat = 0 := by
            have r39725 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b39726 := hb (x 8 1)
            have b39727 := hb (x 9 14)
            clear * - r39725 b39726 b39727 d39720
            omega
          have d39728 : (x 8 1 && x 8 14).toNat = 0 := by
            have r39729 := hand1 (x 8 1) (x 8 14)
            have b39730 := hb (x 8 1)
            have b39731 := hb (x 8 1 && x 8 14)
            clear * - r39729 b39730 b39731 d39724
            omega
          have d39732 : (x 9 13).toNat = 1 := by
            have r39733 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b39734 := hb (x 7 2)
            have b39735 := hb (x 9 13)
            have b39736 := hb (x 8 1 && x 8 14)
            clear * - r39733 b39734 b39735 b39736 d39728 d39323
            omega
          have d39737 : (x 9 1).toNat = 1 := by
            have r39738 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
            have b39739 := hb (x 9 1)
            have b39740 := hb (x 9 13)
            clear * - r39738 b39739 b39740 d39732
            omega
          have d39741 : (x 8 2).toNat = 0 := by
            have r39742 : (x 9 1).toNat + (x 8 2).toNat + (x 7 3).toNat + (x 6 4).toNat + (x 5 5).toNat + (x 4 6).toNat + (x 3 7).toNat + (x 2 8).toNat + (x 1 9).toNat + (x 0 10).toNat + (x (-1) 11).toNat + (x (-2) 12).toNat + (x (-3) 13).toNat + (x (-4) 14).toNat = 3 := by have q := hcount 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b39743 := hb (x (-4) 14)
            have b39744 := hb (x (-3) 13)
            have b39745 := hb (x (-2) 12)
            have b39746 := hb (x (-1) 11)
            have b39747 := hb (x 0 10)
            have b39748 := hb (x 1 9)
            have b39749 := hb (x 2 8)
            have b39750 := hb (x 3 7)
            have b39751 := hb (x 4 6)
            have b39752 := hb (x 5 5)
            have b39753 := hb (x 6 4)
            have b39754 := hb (x 7 3)
            have b39755 := hb (x 8 2)
            have b39756 := hb (x 9 1)
            clear * - r39742 b39743 b39744 b39745 b39746 b39747 b39748 b39749 b39750 b39751 b39752 b39753 b39754 b39755 b39756 d39737 g34 d37654 d37670 d37646 g9 d39063 d39071 d38905
            omega
          have d39757 : (x 8 2 && x 8 12).toNat = 0 := by
            have r39758 := hand1 (x 8 2) (x 8 12)
            have b39759 := hb (x 8 2)
            have b39760 := hb (x 8 2 && x 8 12)
            clear * - r39758 b39759 b39760 d39741
            omega
          have d39761 : (x 5 5).toNat = 1 := by
            have r39762 : 1 ≤ (x 10 10).toNat + (x 9 1 && x 9 11).toNat + (x 8 2 && x 8 12).toNat + (x 7 3 && x 7 13).toNat + (x 6 4 && x 6 14).toNat + (x 5 5).toNat := by have q := hcov10 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b39763 := hb (x 5 5)
            have b39764 := hb (x 10 10)
            have b39765 := hb (x 9 1 && x 9 11)
            have b39766 := hb (x 8 2 && x 8 12)
            have b39767 := hb (x 7 3 && x 7 13)
            have b39768 := hb (x 6 4 && x 6 14)
            clear * - r39762 b39763 b39764 b39765 b39766 b39767 b39768 d39627 d39659 d39757 d39351 d39566
            omega
          have d39769 : (x 10 8).toNat = 0 := by
            have r39770 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39771 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
            have e39772 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
            have e39773 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
            have e39774 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
            have e39775 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
            have e39776 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
            have b39777 := hb (x 3 7)
            have b39778 := hb (x 4 6)
            have b39779 := hb (x 5 5)
            have b39780 := hb (x 6 4)
            have b39781 := hb (x 7 11)
            have b39782 := hb (x 8 10)
            have b39783 := hb (x 9 9)
            have b39784 := hb (x 10 8)
            clear * - r39770 e39771 e39772 e39773 e39774 e39775 e39776 b39777 b39778 b39779 b39780 b39781 b39782 b39783 b39784 d39761 g34
            omega
          have d39785 : (x 9 9).toNat = 0 := by
            have r39786 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39787 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
            have e39788 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
            have e39789 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
            have e39790 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
            have e39791 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
            have e39792 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
            have b39793 := hb (x 3 7)
            have b39794 := hb (x 4 6)
            have b39795 := hb (x 5 5)
            have b39796 := hb (x 6 4)
            have b39797 := hb (x 7 11)
            have b39798 := hb (x 8 10)
            have b39799 := hb (x 9 9)
            have b39800 := hb (x 10 8)
            clear * - r39786 e39787 e39788 e39789 e39790 e39791 e39792 b39793 b39794 b39795 b39796 b39797 b39798 b39799 b39800 d39769 d39761 g34
            omega
          have d39801 : (x 8 10).toNat = 0 := by
            have r39802 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39803 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
            have e39804 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
            have e39805 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
            have e39806 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
            have e39807 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
            have e39808 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
            have b39809 := hb (x 3 7)
            have b39810 := hb (x 4 6)
            have b39811 := hb (x 5 5)
            have b39812 := hb (x 6 4)
            have b39813 := hb (x 7 11)
            have b39814 := hb (x 8 10)
            have b39815 := hb (x 9 9)
            have b39816 := hb (x 10 8)
            clear * - r39802 e39803 e39804 e39805 e39806 e39807 e39808 b39809 b39810 b39811 b39812 b39813 b39814 b39815 b39816 d39769 d39785 d39761 g34
            omega
          have d39817 : (x 7 11).toNat = 0 := by
            have r39818 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39819 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
            have e39820 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
            have e39821 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
            have e39822 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
            have e39823 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
            have e39824 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
            have b39825 := hb (x 3 7)
            have b39826 := hb (x 4 6)
            have b39827 := hb (x 5 5)
            have b39828 := hb (x 6 4)
            have b39829 := hb (x 7 11)
            have b39830 := hb (x 8 10)
            have b39831 := hb (x 9 9)
            have b39832 := hb (x 10 8)
            clear * - r39818 e39819 e39820 e39821 e39822 e39823 e39824 b39825 b39826 b39827 b39828 b39829 b39830 b39831 b39832 d39769 d39785 d39801 d39761 g34
            omega
          have d39833 : (x 6 4).toNat = 0 := by
            have r39834 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39835 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
            have e39836 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
            have e39837 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
            have e39838 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
            have e39839 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
            have e39840 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
            have b39841 := hb (x 3 7)
            have b39842 := hb (x 4 6)
            have b39843 := hb (x 5 5)
            have b39844 := hb (x 6 4)
            have b39845 := hb (x 7 11)
            have b39846 := hb (x 8 10)
            have b39847 := hb (x 9 9)
            have b39848 := hb (x 10 8)
            clear * - r39834 e39835 e39836 e39837 e39838 e39839 e39840 b39841 b39842 b39843 b39844 b39845 b39846 b39847 b39848 d39769 d39785 d39801 d39817 d39761 g34
            omega
          have d39849 : (x 3 7).toNat = 0 := by
            have r39850 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39851 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
            have e39852 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
            have e39853 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
            have e39854 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
            have e39855 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
            have e39856 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
            have b39857 := hb (x 3 7)
            have b39858 := hb (x 4 6)
            have b39859 := hb (x 5 5)
            have b39860 := hb (x 6 4)
            have b39861 := hb (x 7 11)
            have b39862 := hb (x 8 10)
            have b39863 := hb (x 9 9)
            have b39864 := hb (x 10 8)
            clear * - r39850 e39851 e39852 e39853 e39854 e39855 e39856 b39857 b39858 b39859 b39860 b39861 b39862 b39863 b39864 d39769 d39785 d39801 d39817 d39833 d39761 g34
            omega
          have r39865 : (x 9 1).toNat + (x 8 2).toNat + (x 7 3).toNat + (x 6 4).toNat + (x 5 5).toNat + (x 4 6).toNat + (x 3 7).toNat + (x 2 8).toNat + (x 1 9).toNat + (x 0 10).toNat + (x (-1) 11).toNat + (x (-2) 12).toNat + (x (-3) 13).toNat + (x (-4) 14).toNat = 3 := by have q := hcount 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b39866 := hb (x (-4) 14)
          have b39867 := hb (x (-3) 13)
          have b39868 := hb (x (-2) 12)
          have b39869 := hb (x (-1) 11)
          have b39870 := hb (x 0 10)
          have b39871 := hb (x 1 9)
          have b39872 := hb (x 2 8)
          have b39873 := hb (x 3 7)
          have b39874 := hb (x 4 6)
          have b39875 := hb (x 5 5)
          have b39876 := hb (x 6 4)
          have b39877 := hb (x 7 3)
          have b39878 := hb (x 8 2)
          have b39879 := hb (x 9 1)
          linarith only [r39865, b39866, b39867, b39868, b39869, b39870, b39871, b39872, b39873, b39874, b39875, b39876, b39877, b39878, b39879, d39737, d39741, d39833, d39761, g34, d39849, d37654, d37670, d37646, g9, d39063, d39071, d38905]
      · have f39880 : (x 1 7).toNat = 1 := by rw [h38034]; rfl
        have d39881 : (x 8 8).toNat = 0 := by
          have r39882 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e39883 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e39884 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e39885 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e39886 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e39887 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e39888 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have b39889 := hb (x 1 7)
          have b39890 := hb (x 2 6)
          have b39891 := hb (x 3 5)
          have b39892 := hb (x 4 4)
          have b39893 := hb (x 5 11)
          have b39894 := hb (x 6 10)
          have b39895 := hb (x 7 9)
          have b39896 := hb (x 8 8)
          clear * - r39882 e39883 e39884 e39885 e39886 e39887 e39888 b39889 b39890 b39891 b39892 b39893 b39894 b39895 b39896 g33 g28 f39880
          omega
        have d39897 : (x 7 9).toNat = 0 := by
          have r39898 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e39899 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e39900 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e39901 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e39902 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e39903 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e39904 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have b39905 := hb (x 1 7)
          have b39906 := hb (x 2 6)
          have b39907 := hb (x 3 5)
          have b39908 := hb (x 4 4)
          have b39909 := hb (x 5 11)
          have b39910 := hb (x 6 10)
          have b39911 := hb (x 7 9)
          have b39912 := hb (x 8 8)
          clear * - r39898 e39899 e39900 e39901 e39902 e39903 e39904 b39905 b39906 b39907 b39908 b39909 b39910 b39911 b39912 d39881 g33 g28 f39880
          omega
        have d39913 : (x 6 10).toNat = 0 := by
          have r39914 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e39915 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e39916 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e39917 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e39918 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e39919 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e39920 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have b39921 := hb (x 1 7)
          have b39922 := hb (x 2 6)
          have b39923 := hb (x 3 5)
          have b39924 := hb (x 4 4)
          have b39925 := hb (x 5 11)
          have b39926 := hb (x 6 10)
          have b39927 := hb (x 7 9)
          have b39928 := hb (x 8 8)
          clear * - r39914 e39915 e39916 e39917 e39918 e39919 e39920 b39921 b39922 b39923 b39924 b39925 b39926 b39927 b39928 d39881 d39897 g33 g28 f39880
          omega
        have d39929 : (x 6 1 && x 6 10).toNat = 0 := by
          have r39930 := hand2 (x 6 1) (x 6 10)
          have b39931 := hb (x 6 10)
          have b39932 := hb (x 6 1 && x 6 10)
          clear * - r39930 b39931 b39932 d39913
          omega
        have d39933 : (x 5 2 && x 5 11).toNat = 1 := by
          have r39934 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b39935 := hb (x 1 6)
          have b39936 := hb (x 7 9)
          have b39937 := hb (x 6 1 && x 6 10)
          have b39938 := hb (x 5 2 && x 5 11)
          have b39939 := hb (x 4 3 && x 4 12)
          have b39940 := hb (x 3 4 && x 3 13)
          have b39941 := hb (x 2 5 && x 2 14)
          clear * - r39934 b39935 b39936 b39937 b39938 b39939 b39940 b39941 d39897 d39929 g105 g106 g107 g21
          omega
        have d39942 : (x 5 11).toNat = 1 := by
          have r39943 := hand2 (x 5 2) (x 5 11)
          have b39944 := hb (x 5 11)
          have b39945 := hb (x 5 2 && x 5 11)
          clear * - r39943 b39944 b39945 d39933
          omega
        have r39946 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e39947 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e39948 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e39949 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e39950 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e39951 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e39952 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b39953 := hb (x 1 7)
        have b39954 := hb (x 2 6)
        have b39955 := hb (x 3 5)
        have b39956 := hb (x 4 4)
        have b39957 := hb (x 5 11)
        have b39958 := hb (x 6 10)
        have b39959 := hb (x 7 9)
        have b39960 := hb (x 8 8)
        linarith only [r39946, e39947, e39948, e39949, e39950, e39951, e39952, b39953, b39954, b39955, b39956, b39957, b39958, b39959, b39960, d39881, d39897, d39913, d39942, g33, g28, f39880]
  · have f39961 : (x 0 6).toNat = 1 := by rw [h37388]; rfl
    have d39962 : (x 6 8).toNat = 0 := by
      have r39963 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e39964 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e39965 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e39966 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e39967 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e39968 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e39969 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b39970 := hb (x (-1) 7)
      have b39971 := hb (x 0 6)
      have b39972 := hb (x 1 5)
      have b39973 := hb (x 2 4)
      have b39974 := hb (x 3 11)
      have b39975 := hb (x 4 10)
      have b39976 := hb (x 5 9)
      have b39977 := hb (x 6 8)
      clear * - r39963 e39964 e39965 e39966 e39967 e39968 e39969 b39970 b39971 b39972 b39973 b39974 b39975 b39976 b39977 g36 g26 g20 f39961
      omega
    have d39978 : (x 6 1 && x 6 8).toNat = 0 := by
      have r39979 := hand2 (x 6 1) (x 6 8)
      have b39980 := hb (x 6 8)
      have b39981 := hb (x 6 1 && x 6 8)
      clear * - r39979 b39980 b39981 d39962
      omega
    have d39982 : (x 6 2 && x 6 8).toNat = 0 := by
      have r39983 := hand2 (x 6 2) (x 6 8)
      have b39984 := hb (x 6 8)
      have b39985 := hb (x 6 2 && x 6 8)
      clear * - r39983 b39984 b39985 d39962
      omega
    have d39986 : (x 5 9).toNat = 0 := by
      have r39987 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e39988 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e39989 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e39990 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e39991 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e39992 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e39993 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b39994 := hb (x (-1) 7)
      have b39995 := hb (x 0 6)
      have b39996 := hb (x 1 5)
      have b39997 := hb (x 2 4)
      have b39998 := hb (x 3 11)
      have b39999 := hb (x 4 10)
      have b40000 := hb (x 5 9)
      have b40001 := hb (x 6 8)
      clear * - r39987 e39988 e39989 e39990 e39991 e39992 e39993 b39994 b39995 b39996 b39997 b39998 b39999 b40000 b40001 d39962 g36 g26 g20 f39961
      omega
    have d40002 : (x 5 2 && x 5 9).toNat = 0 := by
      have r40003 := hand2 (x 5 2) (x 5 9)
      have b40004 := hb (x 5 9)
      have b40005 := hb (x 5 2 && x 5 9)
      clear * - r40003 b40004 b40005 d39986
      omega
    have d40006 : (x 5 3 && x 5 9).toNat = 0 := by
      have r40007 := hand2 (x 5 3) (x 5 9)
      have b40008 := hb (x 5 9)
      have b40009 := hb (x 5 3 && x 5 9)
      clear * - r40007 b40008 b40009 d39986
      omega
    have d40010 : (x 3 11).toNat = 0 := by
      have r40011 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e40012 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e40013 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e40014 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e40015 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e40016 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e40017 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b40018 := hb (x (-1) 7)
      have b40019 := hb (x 0 6)
      have b40020 := hb (x 1 5)
      have b40021 := hb (x 2 4)
      have b40022 := hb (x 3 11)
      have b40023 := hb (x 4 10)
      have b40024 := hb (x 5 9)
      have b40025 := hb (x 6 8)
      clear * - r40011 e40012 e40013 e40014 e40015 e40016 e40017 b40018 b40019 b40020 b40021 b40022 b40023 b40024 b40025 d39962 d39986 g36 g26 g20 f39961
      omega
    have d40026 : (x 3 5 && x 3 11).toNat = 0 := by
      have r40027 := hand2 (x 3 5) (x 3 11)
      have b40028 := hb (x 3 11)
      have b40029 := hb (x 3 5 && x 3 11)
      clear * - r40027 b40028 b40029 d40010
      omega
    have d40030 : (x (-1) 7).toNat = 0 := by
      have r40031 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e40032 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e40033 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e40034 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e40035 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e40036 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e40037 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b40038 := hb (x (-1) 7)
      have b40039 := hb (x 0 6)
      have b40040 := hb (x 1 5)
      have b40041 := hb (x 2 4)
      have b40042 := hb (x 3 11)
      have b40043 := hb (x 4 10)
      have b40044 := hb (x 5 9)
      have b40045 := hb (x 6 8)
      clear * - r40031 e40032 e40033 e40034 e40035 e40036 e40037 b40038 b40039 b40040 b40041 b40042 b40043 b40044 b40045 d39962 d39986 g36 d40010 g26 g20 f39961
      omega
    cases h40046 : x 0 8
    · have f40047 : (x 0 8).toNat = 0 := by rw [h40046]; rfl
      have d40048 : (x 0 8 && x 0 14).toNat = 0 := by
        have r40049 := hand1 (x 0 8) (x 0 14)
        have b40050 := hb (x 0 8)
        have b40051 := hb (x 0 8 && x 0 14)
        clear * - r40049 b40050 b40051 f40047
        omega
      have d40052 : (x 0 2 && x 0 8).toNat = 0 := by
        have r40053 := hand2 (x 0 2) (x 0 8)
        have b40054 := hb (x 0 8)
        have b40055 := hb (x 0 2 && x 0 8)
        clear * - r40053 b40054 b40055 f40047
        omega
      have d40056 : (x 0 8 && x 0 12).toNat = 0 := by
        have r40057 := hand1 (x 0 8) (x 0 12)
        have b40058 := hb (x 0 8)
        have b40059 := hb (x 0 8 && x 0 12)
        clear * - r40057 b40058 b40059 f40047
        omega
      have d40060 : (x 0 4 && x 0 8).toNat = 0 := by
        have r40061 := hand2 (x 0 4) (x 0 8)
        have b40062 := hb (x 0 8)
        have b40063 := hb (x 0 4 && x 0 8)
        clear * - r40061 b40062 b40063 f40047
        omega
      cases h40064 : x 0 9
      · have f40065 : (x 0 9).toNat = 0 := by rw [h40064]; rfl
        have r40066 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r40067 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r40068 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r40069 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40070 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e40071 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e40072 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e40073 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e40074 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e40075 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have r40076 : (x (-11) 12).toNat + (x (-12) 1 && x (-12) 13).toNat + (x (-13) 2 && x (-13) 14).toNat + (x (-14) 3).toNat = 1 := by have q := hd12 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40077 : (x (-12) 1 && x (-12) 13).toNat = (x (-12) 13).toNat := handr _ _ (fun h => hp13 (-12) (h))
        have e40078 : (x (-13) 2 && x (-13) 14).toNat = (x (-13) 2).toNat := handl _ _ (fun h => hp2 (-13) (h))
        have r40079 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40080 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e40081 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have r40082 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40083 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e40084 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have r40085 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r40086 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40087 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
        have e40088 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
        have r40089 : 1 ≤ (x 2 6).toNat + (x 1 1 && x 1 7).toNat + (x 0 2 && x 0 8).toNat + (x (-1) 3 && x (-1) 9).toNat + (x (-2) 4 && x (-2) 10).toNat + (x (-3) 5 && x (-3) 11).toNat + (x (-4) 6 && x (-4) 12).toNat + (x (-5) 7 && x (-5) 13).toNat + (x (-6) 8 && x (-6) 14).toNat + (x (-7) 9).toNat := by have q := hcov6 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r40090 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r40091 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r40092 : 1 ≤ (x (-7) 11).toNat + (x (-8) 1 && x (-8) 12).toNat + (x (-9) 2 && x (-9) 13).toNat + (x (-10) 3 && x (-10) 14).toNat + (x (-11) 4).toNat := by have q := hcov11 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r40093 : 1 ≤ (x (-11) 13).toNat + (x (-12) 1 && x (-12) 14).toNat + (x (-13) 2).toNat := by have q := hcov13 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r40094 : (x (-11) 4).toNat ≤ (x (-11) 12).toNat := himp _ _ (hp4 (-11))
        have r40095 : (x (-11) 5).toNat ≤ (x (-11) 13).toNat := himp _ _ (hp5 (-11))
        have r40096 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
        have r40097 := hand1 (x (-4) 8) (x (-4) 12)
        have r40098 := hand1 (x (-5) 9) (x (-5) 13)
        have r40099 := hand2 (x 1 1) (x 1 7)
        have r40100 := hand1 (x (-4) 6) (x (-4) 12)
        have r40101 := hand1 (x (-5) 7) (x (-5) 13)
        have r40102 := hand1 (x (-6) 8) (x (-6) 14)
        have r40103 := hand2 (x 6 1) (x 6 10)
        have r40104 := hand2 (x 5 2) (x 5 11)
        have r40105 := hand1 (x (-7) 1) (x (-7) 11)
        have r40106 := hand2 (x (-8) 2) (x (-8) 12)
        have r40107 := hand2 (x (-9) 3) (x (-9) 13)
        have r40108 := hand2 (x (-10) 4) (x (-10) 14)
        have r40109 := hand2 (x (-8) 1) (x (-8) 12)
        have r40110 := hand2 (x (-9) 2) (x (-9) 13)
        have r40111 := hand2 (x (-10) 3) (x (-10) 14)
        have r40112 := hand2 (x (-12) 1) (x (-12) 14)
        have b40166 := hb (x 7 1)
        linarith only [r40066, r40067, r40068, r40069, e40070, e40071, e40072, e40073, e40074, e40075, r40076, e40077, e40078, r40079, e40080, e40081, r40082, e40083, e40084, r40085, r40086, e40087, e40088, r40089, r40090, r40091, r40092, r40093, r40094, r40095, r40096, r40097, r40098, r40099, r40100, r40101, r40102, r40103, r40104, r40105, r40106, r40107, r40108, r40109, r40110, r40111, r40112, b40166, g0, g1, g2, g3, g5, g6, g7, g11, g12, f40047, g17, g18, g21, g25, g28, g30, g33, g45, g46, d40060, g47, g48, g49, d40052, g79, g80, g81, g105, g106, g107]
      · have f40200 : (x 0 9).toNat = 1 := by rw [h40064]; rfl
        have d40201 : (x 1 8).toNat = 0 := by
          have r40202 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e40203 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e40204 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e40205 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e40206 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e40207 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e40208 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b40209 := hb (x (-6) 7)
          have b40210 := hb (x (-5) 6)
          have b40211 := hb (x (-4) 5)
          have b40212 := hb (x (-3) 4)
          have b40213 := hb (x (-2) 11)
          have b40214 := hb (x (-1) 10)
          have b40215 := hb (x 0 9)
          have b40216 := hb (x 1 8)
          clear * - r40202 e40203 e40204 e40205 e40206 e40207 e40208 b40209 b40210 b40211 b40212 b40213 b40214 b40215 b40216 f40200 g8 g4
          omega
        have d40217 : (x (-3) 4).toNat = 0 := by
          have r40218 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e40219 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e40220 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e40221 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e40222 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e40223 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e40224 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b40225 := hb (x (-6) 7)
          have b40226 := hb (x (-5) 6)
          have b40227 := hb (x (-4) 5)
          have b40228 := hb (x (-3) 4)
          have b40229 := hb (x (-2) 11)
          have b40230 := hb (x (-1) 10)
          have b40231 := hb (x 0 9)
          have b40232 := hb (x 1 8)
          clear * - r40218 e40219 e40220 e40221 e40222 e40223 e40224 b40225 b40226 b40227 b40228 b40229 b40230 b40231 b40232 d40201 f40200 g8 g4
          omega
        have d40233 : (x (-3) 4 && x (-3) 14).toNat = 0 := by
          have r40234 := hand1 (x (-3) 4) (x (-3) 14)
          have b40235 := hb (x (-3) 4)
          have b40236 := hb (x (-3) 4 && x (-3) 14)
          clear * - r40234 b40235 b40236 d40217
          omega
        have d40237 : (x (-3) 4 && x (-3) 10).toNat = 0 := by
          have r40238 := hand1 (x (-3) 4) (x (-3) 10)
          have b40239 := hb (x (-3) 4)
          have b40240 := hb (x (-3) 4 && x (-3) 10)
          clear * - r40238 b40239 b40240 d40217
          omega
        have d40241 : (x (-4) 5).toNat = 0 := by
          have r40242 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e40243 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e40244 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e40245 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e40246 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e40247 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e40248 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b40249 := hb (x (-6) 7)
          have b40250 := hb (x (-5) 6)
          have b40251 := hb (x (-4) 5)
          have b40252 := hb (x (-3) 4)
          have b40253 := hb (x (-2) 11)
          have b40254 := hb (x (-1) 10)
          have b40255 := hb (x 0 9)
          have b40256 := hb (x 1 8)
          clear * - r40242 e40243 e40244 e40245 e40246 e40247 e40248 b40249 b40250 b40251 b40252 b40253 b40254 b40255 b40256 d40201 f40200 g8 g4 d40217
          omega
        have d40257 : (x (-4) 5 && x (-4) 11).toNat = 0 := by
          have r40258 := hand1 (x (-4) 5) (x (-4) 11)
          have b40259 := hb (x (-4) 5)
          have b40260 := hb (x (-4) 5 && x (-4) 11)
          clear * - r40258 b40259 b40260 d40241
          omega
        have d40261 : (x 0 1 && x 0 11).toNat = 1 := by
          have r40262 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b40263 := hb (x (-4) 5)
          have b40264 := hb (x 1 10)
          have b40265 := hb (x 0 1 && x 0 11)
          have b40266 := hb (x (-1) 2 && x (-1) 12)
          have b40267 := hb (x (-2) 3 && x (-2) 13)
          have b40268 := hb (x (-3) 4 && x (-3) 14)
          clear * - r40262 b40263 b40264 b40265 b40266 b40267 b40268 g22 g112 g113 d40233 d40241
          omega
        have d40269 : (x 0 11).toNat = 1 := by
          have r40270 := hand2 (x 0 1) (x 0 11)
          have b40271 := hb (x 0 11)
          have b40272 := hb (x 0 1 && x 0 11)
          clear * - r40270 b40271 b40272 d40261
          omega
        have d40273 : (x 3 8).toNat = 0 := by
          have r40274 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e40275 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e40276 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e40277 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e40278 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e40279 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e40280 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b40281 := hb (x (-4) 7)
          have b40282 := hb (x (-3) 6)
          have b40283 := hb (x (-2) 5)
          have b40284 := hb (x (-1) 4)
          have b40285 := hb (x 0 11)
          have b40286 := hb (x 1 10)
          have b40287 := hb (x 2 9)
          have b40288 := hb (x 3 8)
          clear * - r40274 e40275 e40276 e40277 e40278 e40279 e40280 b40281 b40282 b40283 b40284 b40285 b40286 b40287 b40288 g22 d40269
          omega
        have d40289 : (x 2 9).toNat = 0 := by
          have r40290 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e40291 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e40292 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e40293 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e40294 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e40295 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e40296 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b40297 := hb (x (-4) 7)
          have b40298 := hb (x (-3) 6)
          have b40299 := hb (x (-2) 5)
          have b40300 := hb (x (-1) 4)
          have b40301 := hb (x 0 11)
          have b40302 := hb (x 1 10)
          have b40303 := hb (x 2 9)
          have b40304 := hb (x 3 8)
          clear * - r40290 e40291 e40292 e40293 e40294 e40295 e40296 b40297 b40298 b40299 b40300 b40301 b40302 b40303 b40304 d40273 g22 d40269
          omega
        have d40305 : (x (-5) 6).toNat = 0 := by
          have r40306 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e40307 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e40308 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e40309 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e40310 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e40311 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e40312 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b40313 := hb (x (-6) 7)
          have b40314 := hb (x (-5) 6)
          have b40315 := hb (x (-4) 5)
          have b40316 := hb (x (-3) 4)
          have b40317 := hb (x (-2) 11)
          have b40318 := hb (x (-1) 10)
          have b40319 := hb (x 0 9)
          have b40320 := hb (x 1 8)
          clear * - r40306 e40307 e40308 e40309 e40310 e40311 e40312 b40313 b40314 b40315 b40316 b40317 b40318 b40319 b40320 d40201 f40200 g8 g4 d40217 d40241
          omega
        have d40321 : (x (-5) 6 && x (-5) 12).toNat = 0 := by
          have r40322 := hand1 (x (-5) 6) (x (-5) 12)
          have b40323 := hb (x (-5) 6)
          have b40324 := hb (x (-5) 6 && x (-5) 12)
          clear * - r40322 b40323 b40324 d40305
          omega
        have d40325 : (x (-6) 7).toNat = 0 := by
          have r40326 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e40327 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e40328 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e40329 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e40330 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e40331 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e40332 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b40333 := hb (x (-6) 7)
          have b40334 := hb (x (-5) 6)
          have b40335 := hb (x (-4) 5)
          have b40336 := hb (x (-3) 4)
          have b40337 := hb (x (-2) 11)
          have b40338 := hb (x (-1) 10)
          have b40339 := hb (x 0 9)
          have b40340 := hb (x 1 8)
          clear * - r40326 e40327 e40328 e40329 e40330 e40331 e40332 b40333 b40334 b40335 b40336 b40337 b40338 b40339 b40340 d40201 f40200 g8 g4 d40217 d40241 d40305
          omega
        have d40341 : (x (-6) 7 && x (-6) 13).toNat = 0 := by
          have r40342 := hand1 (x (-6) 7) (x (-6) 13)
          have b40343 := hb (x (-6) 7)
          have b40344 := hb (x (-6) 7 && x (-6) 13)
          clear * - r40342 b40343 b40344 d40325
          omega
        have r40345 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r40346 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r40347 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r40348 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r40349 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40350 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
        have e40351 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
        have e40352 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
        have e40353 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
        have e40354 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
        have e40355 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
        have r40356 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40357 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e40358 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e40359 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e40360 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e40361 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e40362 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have r40363 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40364 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
        have e40365 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
        have e40366 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
        have e40367 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
        have e40368 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
        have e40369 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
        have r40370 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40371 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
        have e40372 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
        have e40373 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
        have e40374 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
        have e40375 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
        have e40376 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
        have r40377 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40378 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e40379 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have r40380 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40381 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e40382 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have r40383 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40384 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
        have e40385 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
        have r40386 : 1 ≤ (x 8 4).toNat + (x 7 1 && x 7 5).toNat + (x 6 2 && x 6 6).toNat + (x 5 3 && x 5 7).toNat + (x 4 4 && x 4 8).toNat + (x 3 5 && x 3 9).toNat + (x 2 6 && x 2 10).toNat + (x 1 7 && x 1 11).toNat + (x 0 8 && x 0 12).toNat + (x (-1) 9 && x (-1) 13).toNat + (x (-2) 10 && x (-2) 14).toNat + (x (-3) 11).toNat := by have q := hcov4 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40387 : (x 7 1 && x 7 5).toNat = (x 7 5).toNat := handr _ _ (fun h => hp13 7 (hp5 7 (h)))
        have e40388 : (x (-2) 10 && x (-2) 14).toNat = (x (-2) 10).toNat := handl _ _ (fun h => hp2 (-2) (hp10 (-2) (h)))
        have r40389 : 1 ≤ (x 1 6).toNat + (x 0 1 && x 0 7).toNat + (x (-1) 2 && x (-1) 8).toNat + (x (-2) 3 && x (-2) 9).toNat + (x (-3) 4 && x (-3) 10).toNat + (x (-4) 5 && x (-4) 11).toNat + (x (-5) 6 && x (-5) 12).toNat + (x (-6) 7 && x (-6) 13).toNat + (x (-7) 8 && x (-7) 14).toNat + (x (-8) 9).toNat := by have q := hcov6 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r40390 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r40391 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r40392 : 1 ≤ (x 11 9).toNat + (x 10 1 && x 10 10).toNat + (x 9 2 && x 9 11).toNat + (x 8 3 && x 8 12).toNat + (x 7 4 && x 7 13).toNat + (x 6 5 && x 6 14).toNat + (x 5 6).toNat := by have q := hcov9 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r40393 : 1 ≤ (x 12 10).toNat + (x 11 1 && x 11 11).toNat + (x 10 2 && x 10 12).toNat + (x 9 3 && x 9 13).toNat + (x 8 4 && x 8 14).toNat + (x 7 5).toNat := by have q := hcov10 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r40394 : 1 ≤ (x (-7) 11).toNat + (x (-8) 1 && x (-8) 12).toNat + (x (-9) 2 && x (-9) 13).toNat + (x (-10) 3 && x (-10) 14).toNat + (x (-11) 4).toNat := by have q := hcov11 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r40395 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r40396 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r40397 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
        have r40398 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
        have r40399 : (x 7 5).toNat ≤ (x 7 13).toNat := himp _ _ (hp5 7)
        have r40400 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
        have r40401 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
        have r40402 := hand1 (x (-4) 8) (x (-4) 12)
        have r40403 := hand1 (x (-5) 9) (x (-5) 13)
        have r40404 := hand2 (x 6 2) (x 6 6)
        have r40405 := hand2 (x 5 3) (x 5 7)
        have r40406 := hand1 (x (-7) 8) (x (-7) 14)
        have r40407 := hand2 (x 7 1) (x 7 7)
        have r40408 := hand2 (x 6 1) (x 6 10)
        have r40409 := hand2 (x 5 2) (x 5 11)
        have r40410 := hand2 (x 10 1) (x 10 10)
        have r40411 := hand2 (x 9 2) (x 9 11)
        have r40412 := hand1 (x 8 3) (x 8 12)
        have r40413 := hand1 (x 7 4) (x 7 13)
        have r40414 := hand1 (x 6 5) (x 6 14)
        have r40415 := hand2 (x 11 1) (x 11 11)
        have r40416 := hand1 (x 10 2) (x 10 12)
        have r40417 := hand1 (x 9 3) (x 9 13)
        have r40418 := hand1 (x 8 4) (x 8 14)
        have r40419 := hand2 (x (-8) 1) (x (-8) 12)
        have r40420 := hand2 (x (-9) 2) (x (-9) 13)
        have r40421 := hand2 (x (-10) 3) (x (-10) 14)
        have r40422 := hand2 (x (-2) 1) (x (-2) 14)
        have r40423 := hand1 (x 10 1) (x 10 14)
        have b40439 := hb (x (-6) 14)
        have b40484 := hb (x 7 1)
        linarith only [r40345, r40346, r40347, r40348, r40349, e40350, e40351, e40352, e40353, e40354, e40355, r40356, e40357, e40358, e40359, e40360, e40361, e40362, r40363, e40364, e40365, e40366, e40367, e40368, e40369, r40370, e40371, e40372, e40373, e40374, e40375, e40376, r40377, e40378, e40379, r40380, e40381, e40382, r40383, e40384, e40385, r40386, e40387, e40388, r40389, r40390, r40391, r40392, r40393, r40394, r40395, r40396, r40397, r40398, r40399, r40400, r40401, r40402, r40403, r40404, r40405, r40406, r40407, r40408, r40409, r40410, r40411, r40412, r40413, r40414, r40415, r40416, r40417, r40418, r40419, r40420, r40421, r40422, r40423, b40439, b40484, g0, g1, g2, g3, g6, g7, g10, g12, f40047, d40269, g15, g18, g21, g22, g23, g25, g28, d40289, g29, g30, d40273, g32, g33, g35, g45, g46, d40060, g47, g48, g49, g54, g55, g56, g57, d40056, g58, g76, g77, g78, d40237, d40257, d40321, d40341, d39982, d40006, g86, d40026, g87, g88, d40048, g105, g106, g107]
    · have f40562 : (x 0 8).toNat = 1 := by rw [h40046]; rfl
      have d40563 : (x (-4) 4).toNat = 0 := by
        have r40564 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40565 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
        have e40566 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
        have e40567 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
        have e40568 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
        have e40569 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
        have e40570 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
        have b40571 := hb (x (-7) 7)
        have b40572 := hb (x (-6) 6)
        have b40573 := hb (x (-5) 5)
        have b40574 := hb (x (-4) 4)
        have b40575 := hb (x (-3) 11)
        have b40576 := hb (x (-2) 10)
        have b40577 := hb (x (-1) 9)
        have b40578 := hb (x 0 8)
        clear * - r40564 e40565 e40566 e40567 e40568 e40569 e40570 b40571 b40572 b40573 b40574 b40575 b40576 b40577 b40578 f40562 g7 g3 g1
        omega
      have d40579 : (x (-4) 4 && x (-4) 14).toNat = 0 := by
        have r40580 := hand1 (x (-4) 4) (x (-4) 14)
        have b40581 := hb (x (-4) 4)
        have b40582 := hb (x (-4) 4 && x (-4) 14)
        clear * - r40580 b40581 b40582 d40563
        omega
      have d40583 : (x (-4) 4 && x (-4) 13).toNat = 0 := by
        have r40584 := hand1 (x (-4) 4) (x (-4) 13)
        have b40585 := hb (x (-4) 4)
        have b40586 := hb (x (-4) 4 && x (-4) 13)
        clear * - r40584 b40585 b40586 d40563
        omega
      have d40587 : (x (-4) 4 && x (-4) 11).toNat = 0 := by
        have r40588 := hand1 (x (-4) 4) (x (-4) 11)
        have b40589 := hb (x (-4) 4)
        have b40590 := hb (x (-4) 4 && x (-4) 11)
        clear * - r40588 b40589 b40590 d40563
        omega
      have d40591 : (x 0 11).toNat = 1 := by
        have r40592 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b40593 := hb (x (-4) 4)
        have b40594 := hb (x 0 11)
        have b40595 := hb (x (-1) 1 && x (-1) 12)
        have b40596 := hb (x (-2) 2 && x (-2) 13)
        have b40597 := hb (x (-3) 3 && x (-3) 14)
        clear * - r40592 b40593 b40594 b40595 b40596 b40597 g114 g115 g116 d40563
        omega
      have d40598 : (x 3 8).toNat = 0 := by
        have r40599 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40600 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
        have e40601 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
        have e40602 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
        have e40603 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
        have e40604 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
        have e40605 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
        have b40606 := hb (x (-4) 7)
        have b40607 := hb (x (-3) 6)
        have b40608 := hb (x (-2) 5)
        have b40609 := hb (x (-1) 4)
        have b40610 := hb (x 0 11)
        have b40611 := hb (x 1 10)
        have b40612 := hb (x 2 9)
        have b40613 := hb (x 3 8)
        clear * - r40599 e40600 e40601 e40602 e40603 e40604 e40605 b40606 b40607 b40608 b40609 b40610 b40611 b40612 b40613 g22 d40591
        omega
      have d40614 : (x 2 9).toNat = 0 := by
        have r40615 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40616 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
        have e40617 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
        have e40618 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
        have e40619 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
        have e40620 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
        have e40621 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
        have b40622 := hb (x (-4) 7)
        have b40623 := hb (x (-3) 6)
        have b40624 := hb (x (-2) 5)
        have b40625 := hb (x (-1) 4)
        have b40626 := hb (x 0 11)
        have b40627 := hb (x 1 10)
        have b40628 := hb (x 2 9)
        have b40629 := hb (x 3 8)
        clear * - r40615 e40616 e40617 e40618 e40619 e40620 e40621 b40622 b40623 b40624 b40625 b40626 b40627 b40628 b40629 d40598 g22 d40591
        omega
      have d40630 : (x (-5) 5).toNat = 0 := by
        have r40631 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40632 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
        have e40633 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
        have e40634 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
        have e40635 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
        have e40636 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
        have e40637 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
        have b40638 := hb (x (-7) 7)
        have b40639 := hb (x (-6) 6)
        have b40640 := hb (x (-5) 5)
        have b40641 := hb (x (-4) 4)
        have b40642 := hb (x (-3) 11)
        have b40643 := hb (x (-2) 10)
        have b40644 := hb (x (-1) 9)
        have b40645 := hb (x 0 8)
        clear * - r40631 e40632 e40633 e40634 e40635 e40636 e40637 b40638 b40639 b40640 b40641 b40642 b40643 b40644 b40645 f40562 g7 g3 g1 d40563
        omega
      have d40646 : (x (-5) 5 && x (-5) 14).toNat = 0 := by
        have r40647 := hand1 (x (-5) 5) (x (-5) 14)
        have b40648 := hb (x (-5) 5)
        have b40649 := hb (x (-5) 5 && x (-5) 14)
        clear * - r40647 b40648 b40649 d40630
        omega
      have d40650 : (x (-5) 5 && x (-5) 12).toNat = 0 := by
        have r40651 := hand1 (x (-5) 5) (x (-5) 12)
        have b40652 := hb (x (-5) 5)
        have b40653 := hb (x (-5) 5 && x (-5) 12)
        clear * - r40651 b40652 b40653 d40630
        omega
      have d40654 : (x 0 10).toNat = 1 := by
        have r40655 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b40656 := hb (x (-5) 5)
        have b40657 := hb (x 0 10)
        have b40658 := hb (x (-1) 1 && x (-1) 11)
        have b40659 := hb (x (-2) 2 && x (-2) 12)
        have b40660 := hb (x (-3) 3 && x (-3) 13)
        have b40661 := hb (x (-4) 4 && x (-4) 14)
        clear * - r40655 b40656 b40657 b40658 b40659 b40660 b40661 g109 g110 g111 d40579 d40630
        omega
      have d40662 : (x 2 8).toNat = 0 := by
        have r40663 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40664 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e40665 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e40666 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e40667 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e40668 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e40669 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b40670 := hb (x (-5) 7)
        have b40671 := hb (x (-4) 6)
        have b40672 := hb (x (-3) 5)
        have b40673 := hb (x (-2) 4)
        have b40674 := hb (x (-1) 11)
        have b40675 := hb (x 0 10)
        have b40676 := hb (x 1 9)
        have b40677 := hb (x 2 8)
        clear * - r40663 e40664 e40665 e40666 e40667 e40668 e40669 b40670 b40671 b40672 b40673 b40674 b40675 b40676 b40677 d40654 g9
        omega
      have d40678 : (x 1 9).toNat = 0 := by
        have r40679 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40680 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e40681 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e40682 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e40683 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e40684 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e40685 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b40686 := hb (x (-5) 7)
        have b40687 := hb (x (-4) 6)
        have b40688 := hb (x (-3) 5)
        have b40689 := hb (x (-2) 4)
        have b40690 := hb (x (-1) 11)
        have b40691 := hb (x 0 10)
        have b40692 := hb (x 1 9)
        have b40693 := hb (x 2 8)
        clear * - r40679 e40680 e40681 e40682 e40683 e40684 e40685 b40686 b40687 b40688 b40689 b40690 b40691 b40692 b40693 d40662 d40654 g9
        omega
      have d40694 : (x (-2) 4).toNat = 0 := by
        have r40695 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40696 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e40697 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e40698 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e40699 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e40700 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e40701 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b40702 := hb (x (-5) 7)
        have b40703 := hb (x (-4) 6)
        have b40704 := hb (x (-3) 5)
        have b40705 := hb (x (-2) 4)
        have b40706 := hb (x (-1) 11)
        have b40707 := hb (x 0 10)
        have b40708 := hb (x 1 9)
        have b40709 := hb (x 2 8)
        clear * - r40695 e40696 e40697 e40698 e40699 e40700 e40701 b40702 b40703 b40704 b40705 b40706 b40707 b40708 b40709 d40662 d40678 d40654 g9
        omega
      have d40710 : (x (-2) 4 && x (-2) 9).toNat = 0 := by
        have r40711 := hand1 (x (-2) 4) (x (-2) 9)
        have b40712 := hb (x (-2) 4)
        have b40713 := hb (x (-2) 4 && x (-2) 9)
        clear * - r40711 b40712 b40713 d40694
        omega
      have d40714 : (x (-3) 5).toNat = 0 := by
        have r40715 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40716 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e40717 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e40718 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e40719 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e40720 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e40721 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b40722 := hb (x (-5) 7)
        have b40723 := hb (x (-4) 6)
        have b40724 := hb (x (-3) 5)
        have b40725 := hb (x (-2) 4)
        have b40726 := hb (x (-1) 11)
        have b40727 := hb (x 0 10)
        have b40728 := hb (x 1 9)
        have b40729 := hb (x 2 8)
        clear * - r40715 e40716 e40717 e40718 e40719 e40720 e40721 b40722 b40723 b40724 b40725 b40726 b40727 b40728 b40729 d40662 d40678 d40654 g9 d40694
        omega
      have d40730 : (x (-3) 5 && x (-3) 10).toNat = 0 := by
        have r40731 := hand1 (x (-3) 5) (x (-3) 10)
        have b40732 := hb (x (-3) 5)
        have b40733 := hb (x (-3) 5 && x (-3) 10)
        clear * - r40731 b40732 b40733 d40714
        omega
      have d40734 : (x (-4) 6).toNat = 0 := by
        have r40735 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40736 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e40737 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e40738 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e40739 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e40740 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e40741 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b40742 := hb (x (-5) 7)
        have b40743 := hb (x (-4) 6)
        have b40744 := hb (x (-3) 5)
        have b40745 := hb (x (-2) 4)
        have b40746 := hb (x (-1) 11)
        have b40747 := hb (x 0 10)
        have b40748 := hb (x 1 9)
        have b40749 := hb (x 2 8)
        clear * - r40735 e40736 e40737 e40738 e40739 e40740 e40741 b40742 b40743 b40744 b40745 b40746 b40747 b40748 b40749 d40662 d40678 d40654 g9 d40694 d40714
        omega
      have d40750 : (x (-4) 6 && x (-4) 11).toNat = 0 := by
        have r40751 := hand1 (x (-4) 6) (x (-4) 11)
        have b40752 := hb (x (-4) 6)
        have b40753 := hb (x (-4) 6 && x (-4) 11)
        clear * - r40751 b40752 b40753 d40734
        omega
      have d40754 : (x (-5) 7).toNat = 0 := by
        have r40755 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40756 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e40757 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e40758 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e40759 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e40760 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e40761 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b40762 := hb (x (-5) 7)
        have b40763 := hb (x (-4) 6)
        have b40764 := hb (x (-3) 5)
        have b40765 := hb (x (-2) 4)
        have b40766 := hb (x (-1) 11)
        have b40767 := hb (x 0 10)
        have b40768 := hb (x 1 9)
        have b40769 := hb (x 2 8)
        clear * - r40755 e40756 e40757 e40758 e40759 e40760 e40761 b40762 b40763 b40764 b40765 b40766 b40767 b40768 b40769 d40662 d40678 d40654 g9 d40694 d40714 d40734
        omega
      have d40770 : (x (-5) 7 && x (-5) 12).toNat = 0 := by
        have r40771 := hand1 (x (-5) 7) (x (-5) 12)
        have b40772 := hb (x (-5) 7)
        have b40773 := hb (x (-5) 7 && x (-5) 12)
        clear * - r40771 b40772 b40773 d40754
        omega
      have d40774 : (x (-6) 6).toNat = 0 := by
        have r40775 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40776 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
        have e40777 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
        have e40778 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
        have e40779 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
        have e40780 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
        have e40781 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
        have b40782 := hb (x (-7) 7)
        have b40783 := hb (x (-6) 6)
        have b40784 := hb (x (-5) 5)
        have b40785 := hb (x (-4) 4)
        have b40786 := hb (x (-3) 11)
        have b40787 := hb (x (-2) 10)
        have b40788 := hb (x (-1) 9)
        have b40789 := hb (x 0 8)
        clear * - r40775 e40776 e40777 e40778 e40779 e40780 e40781 b40782 b40783 b40784 b40785 b40786 b40787 b40788 b40789 f40562 g7 g3 g1 d40563 d40630
        omega
      have d40790 : (x (-6) 6 && x (-6) 13).toNat = 0 := by
        have r40791 := hand1 (x (-6) 6) (x (-6) 13)
        have b40792 := hb (x (-6) 6)
        have b40793 := hb (x (-6) 6 && x (-6) 13)
        clear * - r40791 b40792 b40793 d40774
        omega
      have d40794 : (x 0 9).toNat = 1 := by
        have r40795 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b40796 := hb (x (-6) 6)
        have b40797 := hb (x 0 9)
        have b40798 := hb (x (-1) 1 && x (-1) 10)
        have b40799 := hb (x (-2) 2 && x (-2) 11)
        have b40800 := hb (x (-3) 3 && x (-3) 12)
        have b40801 := hb (x (-4) 4 && x (-4) 13)
        have b40802 := hb (x (-5) 5 && x (-5) 14)
        clear * - r40795 b40796 b40797 b40798 b40799 b40800 b40801 b40802 g102 g103 g104 d40583 d40646 d40774
        omega
      have d40803 : (x 1 8).toNat = 0 := by
        have r40804 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40805 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
        have e40806 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
        have e40807 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
        have e40808 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
        have e40809 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
        have e40810 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
        have b40811 := hb (x (-6) 7)
        have b40812 := hb (x (-5) 6)
        have b40813 := hb (x (-4) 5)
        have b40814 := hb (x (-3) 4)
        have b40815 := hb (x (-2) 11)
        have b40816 := hb (x (-1) 10)
        have b40817 := hb (x 0 9)
        have b40818 := hb (x 1 8)
        clear * - r40804 e40805 e40806 e40807 e40808 e40809 e40810 b40811 b40812 b40813 b40814 b40815 b40816 b40817 b40818 d40794 g8 g4
        omega
      have d40819 : (x (-3) 4).toNat = 0 := by
        have r40820 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40821 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
        have e40822 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
        have e40823 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
        have e40824 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
        have e40825 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
        have e40826 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
        have b40827 := hb (x (-6) 7)
        have b40828 := hb (x (-5) 6)
        have b40829 := hb (x (-4) 5)
        have b40830 := hb (x (-3) 4)
        have b40831 := hb (x (-2) 11)
        have b40832 := hb (x (-1) 10)
        have b40833 := hb (x 0 9)
        have b40834 := hb (x 1 8)
        clear * - r40820 e40821 e40822 e40823 e40824 e40825 e40826 b40827 b40828 b40829 b40830 b40831 b40832 b40833 b40834 d40803 d40794 g8 g4
        omega
      have d40835 : (x (-3) 4 && x (-3) 10).toNat = 0 := by
        have r40836 := hand1 (x (-3) 4) (x (-3) 10)
        have b40837 := hb (x (-3) 4)
        have b40838 := hb (x (-3) 4 && x (-3) 10)
        clear * - r40836 b40837 b40838 d40819
        omega
      have d40839 : (x (-4) 5).toNat = 0 := by
        have r40840 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40841 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
        have e40842 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
        have e40843 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
        have e40844 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
        have e40845 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
        have e40846 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
        have b40847 := hb (x (-6) 7)
        have b40848 := hb (x (-5) 6)
        have b40849 := hb (x (-4) 5)
        have b40850 := hb (x (-3) 4)
        have b40851 := hb (x (-2) 11)
        have b40852 := hb (x (-1) 10)
        have b40853 := hb (x 0 9)
        have b40854 := hb (x 1 8)
        clear * - r40840 e40841 e40842 e40843 e40844 e40845 e40846 b40847 b40848 b40849 b40850 b40851 b40852 b40853 b40854 d40803 d40794 g8 g4 d40819
        omega
      have d40855 : (x (-4) 5 && x (-4) 11).toNat = 0 := by
        have r40856 := hand1 (x (-4) 5) (x (-4) 11)
        have b40857 := hb (x (-4) 5)
        have b40858 := hb (x (-4) 5 && x (-4) 11)
        clear * - r40856 b40857 b40858 d40839
        omega
      have d40859 : (x (-5) 6).toNat = 0 := by
        have r40860 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40861 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
        have e40862 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
        have e40863 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
        have e40864 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
        have e40865 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
        have e40866 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
        have b40867 := hb (x (-6) 7)
        have b40868 := hb (x (-5) 6)
        have b40869 := hb (x (-4) 5)
        have b40870 := hb (x (-3) 4)
        have b40871 := hb (x (-2) 11)
        have b40872 := hb (x (-1) 10)
        have b40873 := hb (x 0 9)
        have b40874 := hb (x 1 8)
        clear * - r40860 e40861 e40862 e40863 e40864 e40865 e40866 b40867 b40868 b40869 b40870 b40871 b40872 b40873 b40874 d40803 d40794 g8 g4 d40819 d40839
        omega
      have d40875 : (x (-5) 6 && x (-5) 12).toNat = 0 := by
        have r40876 := hand1 (x (-5) 6) (x (-5) 12)
        have b40877 := hb (x (-5) 6)
        have b40878 := hb (x (-5) 6 && x (-5) 12)
        clear * - r40876 b40877 b40878 d40859
        omega
      have d40879 : (x (-6) 7).toNat = 0 := by
        have r40880 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40881 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
        have e40882 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
        have e40883 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
        have e40884 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
        have e40885 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
        have e40886 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
        have b40887 := hb (x (-6) 7)
        have b40888 := hb (x (-5) 6)
        have b40889 := hb (x (-4) 5)
        have b40890 := hb (x (-3) 4)
        have b40891 := hb (x (-2) 11)
        have b40892 := hb (x (-1) 10)
        have b40893 := hb (x 0 9)
        have b40894 := hb (x 1 8)
        clear * - r40880 e40881 e40882 e40883 e40884 e40885 e40886 b40887 b40888 b40889 b40890 b40891 b40892 b40893 b40894 d40803 d40794 g8 g4 d40819 d40839 d40859
        omega
      have d40895 : (x (-6) 7 && x (-6) 13).toNat = 0 := by
        have r40896 := hand1 (x (-6) 7) (x (-6) 13)
        have b40897 := hb (x (-6) 7)
        have b40898 := hb (x (-6) 7 && x (-6) 13)
        clear * - r40896 b40897 b40898 d40879
        omega
      have d40899 : (x (-7) 7).toNat = 0 := by
        have r40900 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40901 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
        have e40902 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
        have e40903 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
        have e40904 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
        have e40905 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
        have e40906 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
        have b40907 := hb (x (-7) 7)
        have b40908 := hb (x (-6) 6)
        have b40909 := hb (x (-5) 5)
        have b40910 := hb (x (-4) 4)
        have b40911 := hb (x (-3) 11)
        have b40912 := hb (x (-2) 10)
        have b40913 := hb (x (-1) 9)
        have b40914 := hb (x 0 8)
        clear * - r40900 e40901 e40902 e40903 e40904 e40905 e40906 b40907 b40908 b40909 b40910 b40911 b40912 b40913 b40914 f40562 g7 g3 g1 d40563 d40630 d40774
        omega
      have d40915 : (x (-7) 7 && x (-7) 14).toNat = 0 := by
        have r40916 := hand1 (x (-7) 7) (x (-7) 14)
        have b40917 := hb (x (-7) 7)
        have b40918 := hb (x (-7) 7 && x (-7) 14)
        clear * - r40916 b40917 b40918 d40899
        omega
      have d40919 : (x (-8) 8).toNat = 1 := by
        have r40920 : 1 ≤ (x 0 7).toNat + (x (-1) 1 && x (-1) 8).toNat + (x (-2) 2 && x (-2) 9).toNat + (x (-3) 3 && x (-3) 10).toNat + (x (-4) 4 && x (-4) 11).toNat + (x (-5) 5 && x (-5) 12).toNat + (x (-6) 6 && x (-6) 13).toNat + (x (-7) 7 && x (-7) 14).toNat + (x (-8) 8).toNat := by have q := hcov7 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b40921 := hb (x (-8) 8)
        have b40922 := hb (x 0 7)
        have b40923 := hb (x (-1) 1 && x (-1) 8)
        have b40924 := hb (x (-2) 2 && x (-2) 9)
        have b40925 := hb (x (-3) 3 && x (-3) 10)
        have b40926 := hb (x (-4) 4 && x (-4) 11)
        have b40927 := hb (x (-5) 5 && x (-5) 12)
        have b40928 := hb (x (-6) 6 && x (-6) 13)
        have b40929 := hb (x (-7) 7 && x (-7) 14)
        clear * - r40920 b40921 b40922 b40923 b40924 b40925 b40926 b40927 b40928 b40929 g14 g89 g90 g91 d40587 d40650 d40790 d40915
        omega
      have d40930 : (x (-9) 9).toNat = 0 := by
        have r40931 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40932 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
        have e40933 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
        have e40934 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
        have e40935 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
        have e40936 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
        have e40937 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
        have b40938 := hb (x (-15) 7)
        have b40939 := hb (x (-14) 6)
        have b40940 := hb (x (-13) 5)
        have b40941 := hb (x (-12) 4)
        have b40942 := hb (x (-11) 11)
        have b40943 := hb (x (-10) 10)
        have b40944 := hb (x (-9) 9)
        have b40945 := hb (x (-8) 8)
        clear * - r40931 e40932 e40933 e40934 e40935 e40936 e40937 b40938 b40939 b40940 b40941 b40942 b40943 b40944 b40945 d40919
        omega
      have d40946 : (x (-10) 10).toNat = 0 := by
        have r40947 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40948 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
        have e40949 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
        have e40950 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
        have e40951 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
        have e40952 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
        have e40953 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
        have b40954 := hb (x (-15) 7)
        have b40955 := hb (x (-14) 6)
        have b40956 := hb (x (-13) 5)
        have b40957 := hb (x (-12) 4)
        have b40958 := hb (x (-11) 11)
        have b40959 := hb (x (-10) 10)
        have b40960 := hb (x (-9) 9)
        have b40961 := hb (x (-8) 8)
        clear * - r40947 e40948 e40949 e40950 e40951 e40952 e40953 b40954 b40955 b40956 b40957 b40958 b40959 b40960 b40961 d40919 d40930
        omega
      have d40962 : (x (-11) 11).toNat = 0 := by
        have r40963 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40964 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
        have e40965 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
        have e40966 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
        have e40967 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
        have e40968 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
        have e40969 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
        have b40970 := hb (x (-15) 7)
        have b40971 := hb (x (-14) 6)
        have b40972 := hb (x (-13) 5)
        have b40973 := hb (x (-12) 4)
        have b40974 := hb (x (-11) 11)
        have b40975 := hb (x (-10) 10)
        have b40976 := hb (x (-9) 9)
        have b40977 := hb (x (-8) 8)
        clear * - r40963 e40964 e40965 e40966 e40967 e40968 e40969 b40970 b40971 b40972 b40973 b40974 b40975 b40976 b40977 d40919 d40930 d40946
        omega
      have d40978 : (x (-12) 4).toNat = 0 := by
        have r40979 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40980 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
        have e40981 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
        have e40982 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
        have e40983 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
        have e40984 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
        have e40985 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
        have b40986 := hb (x (-15) 7)
        have b40987 := hb (x (-14) 6)
        have b40988 := hb (x (-13) 5)
        have b40989 := hb (x (-12) 4)
        have b40990 := hb (x (-11) 11)
        have b40991 := hb (x (-10) 10)
        have b40992 := hb (x (-9) 9)
        have b40993 := hb (x (-8) 8)
        clear * - r40979 e40980 e40981 e40982 e40983 e40984 e40985 b40986 b40987 b40988 b40989 b40990 b40991 b40992 b40993 d40919 d40930 d40946 d40962
        omega
      cases h40994 : x 1 7
      · have f40995 : (x 1 7).toNat = 0 := by rw [h40994]; rfl
        cases h40996 : x (-1) 8
        · have f40997 : (x (-1) 8).toNat = 0 := by rw [h40996]; rfl
          have d40998 : (x (-1) 8 && x (-1) 14).toNat = 0 := by
            have r40999 := hand1 (x (-1) 8) (x (-1) 14)
            have b41000 := hb (x (-1) 8)
            have b41001 := hb (x (-1) 8 && x (-1) 14)
            clear * - r40999 b41000 b41001 f40997
            omega
          have d41002 : (x (-1) 8 && x (-1) 12).toNat = 0 := by
            have r41003 := hand1 (x (-1) 8) (x (-1) 12)
            have b41004 := hb (x (-1) 8)
            have b41005 := hb (x (-1) 8 && x (-1) 12)
            clear * - r41003 b41004 b41005 f40997
            omega
          have d41006 : (x 7 7).toNat = 1 := by
            have r41007 : 1 ≤ (x 7 7).toNat + (x 6 1 && x 6 8).toNat + (x 5 2 && x 5 9).toNat + (x 4 3 && x 4 10).toNat + (x 3 4 && x 3 11).toNat + (x 2 5 && x 2 12).toNat + (x 1 6 && x 1 13).toNat + (x 0 7 && x 0 14).toNat + (x (-1) 8).toNat := by have q := hcov7 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b41008 := hb (x (-1) 8)
            have b41009 := hb (x 7 7)
            have b41010 := hb (x 6 1 && x 6 8)
            have b41011 := hb (x 5 2 && x 5 9)
            have b41012 := hb (x 4 3 && x 4 10)
            have b41013 := hb (x 3 4 && x 3 11)
            have b41014 := hb (x 2 5 && x 2 12)
            have b41015 := hb (x 1 6 && x 1 13)
            have b41016 := hb (x 0 7 && x 0 14)
            clear * - r41007 b41008 b41009 b41010 b41011 b41012 b41013 b41014 b41015 b41016 d39978 d40002 g95 g96 g97 g98 g99 f40997
            omega
          have d41017 : (x 14 8).toNat = 0 := by
            have r41018 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e41019 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
            have e41020 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
            have e41021 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
            have e41022 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
            have e41023 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
            have e41024 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
            have b41025 := hb (x 7 7)
            have b41026 := hb (x 8 6)
            have b41027 := hb (x 9 5)
            have b41028 := hb (x 10 4)
            have b41029 := hb (x 11 11)
            have b41030 := hb (x 12 10)
            have b41031 := hb (x 13 9)
            have b41032 := hb (x 14 8)
            clear * - r41018 e41019 e41020 e41021 e41022 e41023 e41024 b41025 b41026 b41027 b41028 b41029 b41030 b41031 b41032 d41006
            omega
          have d41033 : (x 13 9).toNat = 0 := by
            have r41034 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e41035 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
            have e41036 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
            have e41037 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
            have e41038 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
            have e41039 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
            have e41040 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
            have b41041 := hb (x 7 7)
            have b41042 := hb (x 8 6)
            have b41043 := hb (x 9 5)
            have b41044 := hb (x 10 4)
            have b41045 := hb (x 11 11)
            have b41046 := hb (x 12 10)
            have b41047 := hb (x 13 9)
            have b41048 := hb (x 14 8)
            clear * - r41034 e41035 e41036 e41037 e41038 e41039 e41040 b41041 b41042 b41043 b41044 b41045 b41046 b41047 b41048 d41017 d41006
            omega
          have d41049 : (x 12 10).toNat = 0 := by
            have r41050 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e41051 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
            have e41052 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
            have e41053 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
            have e41054 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
            have e41055 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
            have e41056 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
            have b41057 := hb (x 7 7)
            have b41058 := hb (x 8 6)
            have b41059 := hb (x 9 5)
            have b41060 := hb (x 10 4)
            have b41061 := hb (x 11 11)
            have b41062 := hb (x 12 10)
            have b41063 := hb (x 13 9)
            have b41064 := hb (x 14 8)
            clear * - r41050 e41051 e41052 e41053 e41054 e41055 e41056 b41057 b41058 b41059 b41060 b41061 b41062 b41063 b41064 d41017 d41033 d41006
            omega
          have d41065 : (x 12 1 && x 12 10).toNat = 0 := by
            have r41066 := hand2 (x 12 1) (x 12 10)
            have b41067 := hb (x 12 10)
            have b41068 := hb (x 12 1 && x 12 10)
            clear * - r41066 b41067 b41068 d41049
            omega
          have d41069 : (x 11 11).toNat = 0 := by
            have r41070 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e41071 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
            have e41072 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
            have e41073 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
            have e41074 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
            have e41075 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
            have e41076 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
            have b41077 := hb (x 7 7)
            have b41078 := hb (x 8 6)
            have b41079 := hb (x 9 5)
            have b41080 := hb (x 10 4)
            have b41081 := hb (x 11 11)
            have b41082 := hb (x 12 10)
            have b41083 := hb (x 13 9)
            have b41084 := hb (x 14 8)
            clear * - r41070 e41071 e41072 e41073 e41074 e41075 e41076 b41077 b41078 b41079 b41080 b41081 b41082 b41083 b41084 d41017 d41033 d41049 d41006
            omega
          have d41085 : (x 11 2 && x 11 11).toNat = 0 := by
            have r41086 := hand2 (x 11 2) (x 11 11)
            have b41087 := hb (x 11 11)
            have b41088 := hb (x 11 2 && x 11 11)
            clear * - r41086 b41087 b41088 d41069
            omega
          cases h41089 : x (-1) 12
          · have f41090 : (x (-1) 12).toNat = 0 := by rw [h41089]; rfl
            cases h41091 : x (-1) 14
            · have f41092 : (x (-1) 14).toNat = 0 := by rw [h41091]; rfl
              have d41093 : (x (-2) 1).toNat = 1 := by
                have r41094 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b41095 := hb (x (-2) 1)
                have b41096 := hb (x (-1) 14)
                clear * - r41094 b41095 b41096 f41092
                omega
              have r41097 : (x (-2) 1).toNat + (x (-3) 2).toNat + (x (-4) 3).toNat + (x (-5) 4).toNat + (x (-6) 5).toNat + (x (-7) 6).toNat + (x (-8) 7).toNat + (x (-9) 8).toNat + (x (-10) 9).toNat + (x (-11) 10).toNat + (x (-12) 11).toNat + (x (-13) 12).toNat + (x (-14) 13).toNat + (x (-15) 14).toNat = 3 := by have q := hcount (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r41098 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r41099 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r41100 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e41101 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
              have e41102 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
              have e41103 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
              have e41104 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
              have e41105 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
              have e41106 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
              have r41107 : 1 ≤ (x (-1) 5).toNat + (x (-2) 1 && x (-2) 6).toNat + (x (-3) 2 && x (-3) 7).toNat + (x (-4) 3 && x (-4) 8).toNat + (x (-5) 4 && x (-5) 9).toNat + (x (-6) 5 && x (-6) 10).toNat + (x (-7) 6 && x (-7) 11).toNat + (x (-8) 7 && x (-8) 12).toNat + (x (-9) 8 && x (-9) 13).toNat + (x (-10) 9 && x (-10) 14).toNat + (x (-11) 10).toNat := by have q := hcov5 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r41108 : 1 ≤ (x 2 5).toNat + (x 1 1 && x 1 6).toNat + (x 0 2 && x 0 7).toNat + (x (-1) 3 && x (-1) 8).toNat + (x (-2) 4 && x (-2) 9).toNat + (x (-3) 5 && x (-3) 10).toNat + (x (-4) 6 && x (-4) 11).toNat + (x (-5) 7 && x (-5) 12).toNat + (x (-6) 8 && x (-6) 13).toNat + (x (-7) 9 && x (-7) 14).toNat + (x (-8) 10).toNat := by have q := hcov5 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r41109 : 1 ≤ (x 1 6).toNat + (x 0 1 && x 0 7).toNat + (x (-1) 2 && x (-1) 8).toNat + (x (-2) 3 && x (-2) 9).toNat + (x (-3) 4 && x (-3) 10).toNat + (x (-4) 5 && x (-4) 11).toNat + (x (-5) 6 && x (-5) 12).toNat + (x (-6) 7 && x (-6) 13).toNat + (x (-7) 8 && x (-7) 14).toNat + (x (-8) 9).toNat := by have q := hcov6 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r41110 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r41111 : 1 ≤ (x (-9) 11).toNat + (x (-10) 1 && x (-10) 12).toNat + (x (-11) 2 && x (-11) 13).toNat + (x (-12) 3 && x (-12) 14).toNat + (x (-13) 4).toNat := by have q := hcov11 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r41112 : 1 ≤ (x (-7) 11).toNat + (x (-8) 1 && x (-8) 12).toNat + (x (-9) 2 && x (-9) 13).toNat + (x (-10) 3 && x (-10) 14).toNat + (x (-11) 4).toNat := by have q := hcov11 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r41113 : (x (-13) 4).toNat ≤ (x (-13) 12).toNat := himp _ _ (hp4 (-13))
              have r41114 := hand2 (x (-4) 3) (x (-4) 8)
              have r41115 := hand2 (x (-5) 4) (x (-5) 9)
              have r41116 := hand2 (x (-6) 5) (x (-6) 10)
              have r41117 := hand1 (x (-7) 6) (x (-7) 11)
              have r41118 := hand1 (x (-8) 7) (x (-8) 12)
              have r41119 := hand1 (x (-9) 8) (x (-9) 13)
              have r41120 := hand1 (x (-10) 9) (x (-10) 14)
              have r41121 := hand1 (x (-6) 8) (x (-6) 13)
              have r41122 := hand1 (x (-7) 9) (x (-7) 14)
              have r41123 := hand1 (x (-7) 8) (x (-7) 14)
              have r41124 := hand1 (x (-3) 2) (x (-3) 12)
              have r41125 := hand1 (x (-4) 3) (x (-4) 13)
              have r41126 := hand1 (x (-5) 4) (x (-5) 14)
              have r41127 := hand2 (x (-10) 1) (x (-10) 12)
              have r41128 := hand2 (x (-11) 2) (x (-11) 13)
              have r41129 := hand2 (x (-12) 3) (x (-12) 14)
              have r41130 := hand2 (x (-8) 1) (x (-8) 12)
              have r41131 := hand2 (x (-9) 2) (x (-9) 13)
              have r41132 := hand2 (x (-10) 3) (x (-10) 14)
              linarith only [r41097, r41098, r41099, r41100, e41101, e41102, e41103, e41104, e41105, e41106, r41107, r41108, r41109, r41110, r41111, r41112, r41113, r41114, r41115, r41116, r41117, r41118, r41119, r41120, r41121, r41122, r41123, r41124, r41125, r41126, r41127, r41128, r41129, r41130, r41131, r41132, d40754, d40734, d40714, g0, d41093, d40694, g2, g5, g6, g8, g11, g12, g17, g18, g21, g25, g27, g30, g59, g60, g61, g62, g63, d40710, d40730, d40750, d40770, g76, g77, g78, d40835, d40855, d40875, d40895, g108]
            · have f41223 : (x (-1) 14).toNat = 1 := by rw [h41091]; rfl
              have d41224 : (x (-2) 1).toNat = 0 := by
                have r41225 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b41226 := hb (x (-2) 1)
                have b41227 := hb (x (-1) 14)
                clear * - r41225 b41226 b41227 f41223
                omega
              have d41228 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
                have r41229 := hand1 (x (-2) 1) (x (-2) 14)
                have b41230 := hb (x (-2) 1)
                have b41231 := hb (x (-2) 1 && x (-2) 14)
                clear * - r41229 b41230 b41231 d41224
                omega
              have d41232 : (x (-2) 13).toNat = 0 := by
                have r41233 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
                have b41234 := hb (x (-2) 1)
                have b41235 := hb (x (-2) 13)
                clear * - r41233 b41234 b41235 d41224
                omega
              have d41236 : (x (-2) 9 && x (-2) 13).toNat = 0 := by
                have r41237 := hand2 (x (-2) 9) (x (-2) 13)
                have b41238 := hb (x (-2) 13)
                have b41239 := hb (x (-2) 9 && x (-2) 13)
                clear * - r41237 b41238 b41239 d41232
                omega
              have d41240 : (x (-2) 9).toNat = 0 := by
                have r41241 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
                have b41242 := hb (x (-2) 1)
                have b41243 := hb (x (-2) 9)
                clear * - r41241 b41242 b41243 d41224
                omega
              have d41244 : (x (-3) 2).toNat = 1 := by
                have r41245 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b41246 := hb (x (-3) 2)
                have b41247 := hb (x (-1) 13)
                have b41248 := hb (x (-2) 1 && x (-2) 14)
                clear * - r41245 b41246 b41247 b41248 g10 d41228
                omega
              have d41249 : (x (-3) 14).toNat = 1 := by
                have r41250 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
                have b41251 := hb (x (-3) 2)
                have b41252 := hb (x (-3) 14)
                clear * - r41250 b41251 b41252 d41244
                omega
              have d41253 : (x (-4) 3).toNat = 0 := by
                have r41254 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e41255 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                have e41256 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                have b41257 := hb (x (-4) 3)
                have b41258 := hb (x (-3) 2)
                have b41259 := hb (x (-2) 13)
                have b41260 := hb (x (-1) 12)
                clear * - r41254 e41255 e41256 b41257 b41258 b41259 b41260 f41090 d41232 d41244
                omega
              have d41261 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
                have r41262 := hand1 (x (-4) 3) (x (-4) 12)
                have b41263 := hb (x (-4) 3)
                have b41264 := hb (x (-4) 3 && x (-4) 12)
                clear * - r41262 b41263 b41264 d41253
                omega
              have d41265 : (x (-4) 11).toNat = 0 := by
                have r41266 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
                have b41267 := hb (x (-4) 3)
                have b41268 := hb (x (-4) 11)
                clear * - r41266 b41267 b41268 d41253
                omega
              have r41269 : (x 6 1).toNat + (x 5 2).toNat + (x 4 3).toNat + (x 3 4).toNat + (x 2 5).toNat + (x 1 6).toNat + (x 0 7).toNat + (x (-1) 8).toNat + (x (-2) 9).toNat + (x (-3) 10).toNat + (x (-4) 11).toNat + (x (-5) 12).toNat + (x (-6) 13).toNat + (x (-7) 14).toNat = 3 := by have q := hcount 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r41270 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r41271 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r41272 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e41273 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e41274 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e41275 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e41276 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e41277 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e41278 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have r41279 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e41280 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
              have e41281 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
              have r41282 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e41283 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
              have e41284 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
              have r41285 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r41286 : 1 ≤ (x 7 4).toNat + (x 6 1 && x 6 5).toNat + (x 5 2 && x 5 6).toNat + (x 4 3 && x 4 7).toNat + (x 3 4 && x 3 8).toNat + (x 2 5 && x 2 9).toNat + (x 1 6 && x 1 10).toNat + (x 0 7 && x 0 11).toNat + (x (-1) 8 && x (-1) 12).toNat + (x (-2) 9 && x (-2) 13).toNat + (x (-3) 10 && x (-3) 14).toNat + (x (-4) 11).toNat := by have q := hcov4 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e41287 : (x 6 1 && x 6 5).toNat = (x 6 5).toNat := handr _ _ (fun h => hp13 6 (hp5 6 (h)))
              have e41288 : (x (-3) 10 && x (-3) 14).toNat = (x (-3) 10).toNat := handl _ _ (fun h => hp2 (-3) (hp10 (-3) (h)))
              have r41289 : 1 ≤ (x 7 6).toNat + (x 6 1 && x 6 7).toNat + (x 5 2 && x 5 8).toNat + (x 4 3 && x 4 9).toNat + (x 3 4 && x 3 10).toNat + (x 2 5 && x 2 11).toNat + (x 1 6 && x 1 12).toNat + (x 0 7 && x 0 13).toNat + (x (-1) 8 && x (-1) 14).toNat + (x (-2) 9).toNat := by have q := hcov6 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r41290 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r41291 : 1 ≤ (x 13 9).toNat + (x 12 1 && x 12 10).toNat + (x 11 2 && x 11 11).toNat + (x 10 3 && x 10 12).toNat + (x 9 4 && x 9 13).toNat + (x 8 5 && x 8 14).toNat + (x 7 6).toNat := by have q := hcov9 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r41292 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r41293 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
              have r41294 : (x 7 6).toNat ≤ (x 7 14).toNat := himp _ _ (hp6 7)
              have r41295 := hand2 (x 5 2) (x 5 6)
              have r41296 := hand2 (x 4 3) (x 4 7)
              have r41297 := hand2 (x 6 1) (x 6 7)
              have r41298 := hand1 (x (-5) 4) (x (-5) 13)
              have r41299 := hand1 (x (-6) 5) (x (-6) 14)
              have r41300 := hand1 (x 10 3) (x 10 12)
              have r41301 := hand1 (x 9 4) (x 9 13)
              have r41302 := hand1 (x 8 5) (x 8 14)
              have r41303 := hand1 (x 10 1) (x 10 12)
              have r41304 := hand1 (x 9 2) (x 9 13)
              have r41305 := hand1 (x 8 3) (x 8 14)
              have b41310 := hb (x (-7) 14)
              linarith only [r41269, r41270, r41271, r41272, e41273, e41274, e41275, e41276, e41277, e41278, r41279, e41280, e41281, r41282, e41283, e41284, r41285, r41286, e41287, e41288, r41289, r41290, r41291, r41292, r41293, r41294, r41295, r41296, r41297, r41298, r41299, r41300, r41301, r41302, r41303, r41304, r41305, b41310, d41265, d41249, d41240, d41232, f40997, g7, f41090, f41223, g14, d40591, g16, g21, g22, g24, g27, d40614, d37372, g31, d40598, d37352, d37332, d37308, d41069, d41033, g50, g51, g52, g53, d41002, d41236, d37328, d37348, g82, g83, g84, g85, d40998, g100, g101, d41261, d41065, d41085]
          · have f41389 : (x (-1) 12).toNat = 1 := by rw [h41089]; rfl
            have d41390 : (x (-2) 13).toNat = 0 := by
              have r41391 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e41392 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e41393 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b41394 := hb (x (-4) 3)
              have b41395 := hb (x (-3) 2)
              have b41396 := hb (x (-2) 13)
              have b41397 := hb (x (-1) 12)
              clear * - r41391 e41392 e41393 b41394 b41395 b41396 b41397 f41389
              omega
            have d41398 : (x (-3) 2).toNat = 0 := by
              have r41399 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e41400 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e41401 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b41402 := hb (x (-4) 3)
              have b41403 := hb (x (-3) 2)
              have b41404 := hb (x (-2) 13)
              have b41405 := hb (x (-1) 12)
              clear * - r41399 e41400 e41401 b41402 b41403 b41404 b41405 f41389 d41390
              omega
            have d41406 : (x (-3) 2 && x (-3) 13).toNat = 0 := by
              have r41407 := hand1 (x (-3) 2) (x (-3) 13)
              have b41408 := hb (x (-3) 2)
              have b41409 := hb (x (-3) 2 && x (-3) 13)
              clear * - r41407 b41408 b41409 d41398
              omega
            have d41410 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
              have r41411 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b41412 := hb (x (-3) 2)
              have b41413 := hb (x (-1) 13)
              have b41414 := hb (x (-2) 1 && x (-2) 14)
              clear * - r41411 b41412 b41413 b41414 g10 d41398
              omega
            have d41415 : (x (-2) 14).toNat = 1 := by
              have r41416 := hand2 (x (-2) 1) (x (-2) 14)
              have b41417 := hb (x (-2) 14)
              have b41418 := hb (x (-2) 1 && x (-2) 14)
              clear * - r41416 b41417 b41418 d41410
              omega
            have d41419 : (x (-3) 1).toNat = 0 := by
              have r41420 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b41421 := hb (x (-3) 1)
              have b41422 := hb (x (-2) 14)
              clear * - r41420 b41421 b41422 d41415
              omega
            have d41423 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
              have r41424 := hand1 (x (-3) 1) (x (-3) 14)
              have b41425 := hb (x (-3) 1)
              have b41426 := hb (x (-3) 1 && x (-3) 14)
              clear * - r41424 b41425 b41426 d41419
              omega
            have d41427 : (x (-4) 2).toNat = 1 := by
              have r41428 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b41429 := hb (x (-4) 2)
              have b41430 := hb (x (-2) 13)
              have b41431 := hb (x (-3) 1 && x (-3) 14)
              clear * - r41428 b41429 b41430 b41431 d41390 d41423
              omega
            have d41432 : (x (-4) 14).toNat = 1 := by
              have r41433 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
              have b41434 := hb (x (-4) 2)
              have b41435 := hb (x (-4) 14)
              clear * - r41433 b41434 b41435 d41427
              omega
            have d41436 : (x (-5) 1).toNat = 0 := by
              have r41437 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b41438 := hb (x (-5) 1)
              have b41439 := hb (x (-4) 14)
              clear * - r41437 b41438 b41439 d41432
              omega
            have d41440 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
              have r41441 := hand1 (x (-5) 1) (x (-5) 12)
              have b41442 := hb (x (-5) 1)
              have b41443 := hb (x (-5) 1 && x (-5) 12)
              clear * - r41441 b41442 b41443 d41436
              omega
            have d41444 : (x (-5) 13).toNat = 0 := by
              have r41445 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
              have b41446 := hb (x (-5) 1)
              have b41447 := hb (x (-5) 13)
              clear * - r41445 b41446 b41447 d41436
              omega
            have d41448 : (x (-3) 13).toNat = 0 := by
              have r41449 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
              have b41450 := hb (x (-3) 1)
              have b41451 := hb (x (-3) 13)
              clear * - r41449 b41450 b41451 d41419
              omega
            have d41452 : (x (-4) 3).toNat = 0 := by
              have r41453 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e41454 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e41455 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b41456 := hb (x (-4) 3)
              have b41457 := hb (x (-3) 2)
              have b41458 := hb (x (-2) 13)
              have b41459 := hb (x (-1) 12)
              clear * - r41453 e41454 e41455 b41456 b41457 b41458 b41459 f41389 d41390 d41398
              omega
            have d41460 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
              have r41461 := hand1 (x (-4) 3) (x (-4) 14)
              have b41462 := hb (x (-4) 3)
              have b41463 := hb (x (-4) 3 && x (-4) 14)
              clear * - r41461 b41462 b41463 d41452
              omega
            have d41464 : (x (-4) 11).toNat = 0 := by
              have r41465 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
              have b41466 := hb (x (-4) 3)
              have b41467 := hb (x (-4) 11)
              clear * - r41465 b41466 b41467 d41452
              omega
            have d41468 : (x (-2) 12).toNat = 0 := by
              have r41469 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e41470 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
              have e41471 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
              have b41472 := hb (x (-5) 3)
              have b41473 := hb (x (-4) 2)
              have b41474 := hb (x (-3) 13)
              have b41475 := hb (x (-2) 12)
              clear * - r41469 e41470 e41471 b41472 b41473 b41474 b41475 d41448 d41427
              omega
            have d41476 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
              have r41477 := hand2 (x (-2) 1) (x (-2) 12)
              have b41478 := hb (x (-2) 12)
              have b41479 := hb (x (-2) 1 && x (-2) 12)
              clear * - r41477 b41478 b41479 d41468
              omega
            have d41480 : (x (-5) 3).toNat = 0 := by
              have r41481 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e41482 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
              have e41483 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
              have b41484 := hb (x (-5) 3)
              have b41485 := hb (x (-4) 2)
              have b41486 := hb (x (-3) 13)
              have b41487 := hb (x (-2) 12)
              clear * - r41481 e41482 e41483 b41484 b41485 b41486 b41487 d41468 d41448 d41427
              omega
            have d41488 : (x (-5) 11).toNat = 0 := by
              have r41489 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
              have b41490 := hb (x (-5) 3)
              have b41491 := hb (x (-5) 11)
              clear * - r41489 b41490 b41491 d41480
              omega
            have d41492 : (x (-5) 4).toNat = 1 := by
              have r41493 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b41494 := hb (x (-5) 4)
              have b41495 := hb (x (-1) 11)
              have b41496 := hb (x (-2) 1 && x (-2) 12)
              have b41497 := hb (x (-3) 2 && x (-3) 13)
              have b41498 := hb (x (-4) 3 && x (-4) 14)
              clear * - r41493 b41494 b41495 b41496 b41497 b41498 g9 d41476 d41406 d41460
              omega
            have d41499 : (x (-5) 12).toNat = 1 := by
              have r41500 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
              have b41501 := hb (x (-5) 4)
              have b41502 := hb (x (-5) 12)
              clear * - r41500 b41501 b41502 d41492
              omega
            have d41503 : (x (-6) 13).toNat = 0 := by
              have r41504 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e41505 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
              have e41506 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
              have b41507 := hb (x (-8) 3)
              have b41508 := hb (x (-7) 2)
              have b41509 := hb (x (-6) 13)
              have b41510 := hb (x (-5) 12)
              clear * - r41504 e41505 e41506 b41507 b41508 b41509 b41510 d41499
              omega
            have d41511 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
              have r41512 := hand2 (x (-6) 2) (x (-6) 13)
              have b41513 := hb (x (-6) 13)
              have b41514 := hb (x (-6) 2 && x (-6) 13)
              clear * - r41512 b41513 b41514 d41503
              omega
            have d41515 : (x (-7) 2).toNat = 0 := by
              have r41516 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e41517 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
              have e41518 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
              have b41519 := hb (x (-8) 3)
              have b41520 := hb (x (-7) 2)
              have b41521 := hb (x (-6) 13)
              have b41522 := hb (x (-5) 12)
              clear * - r41516 e41517 e41518 b41519 b41520 b41521 b41522 d41499 d41503
              omega
            have d41523 : (x (-7) 2 && x (-7) 13).toNat = 0 := by
              have r41524 := hand1 (x (-7) 2) (x (-7) 13)
              have b41525 := hb (x (-7) 2)
              have b41526 := hb (x (-7) 2 && x (-7) 13)
              clear * - r41524 b41525 b41526 d41515
              omega
            have d41527 : (x (-6) 1 && x (-6) 14).toNat = 1 := by
              have r41528 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b41529 := hb (x (-7) 2)
              have b41530 := hb (x (-5) 13)
              have b41531 := hb (x (-6) 1 && x (-6) 14)
              clear * - r41528 b41529 b41530 b41531 d41444 d41515
              omega
            have d41532 : (x (-6) 14).toNat = 1 := by
              have r41533 := hand2 (x (-6) 1) (x (-6) 14)
              have b41534 := hb (x (-6) 14)
              have b41535 := hb (x (-6) 1 && x (-6) 14)
              clear * - r41533 b41534 b41535 d41527
              omega
            have d41536 : (x (-7) 1).toNat = 0 := by
              have r41537 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b41538 := hb (x (-7) 1)
              have b41539 := hb (x (-6) 14)
              clear * - r41537 b41538 b41539 d41532
              omega
            have d41540 : (x (-7) 1 && x (-7) 14).toNat = 0 := by
              have r41541 := hand1 (x (-7) 1) (x (-7) 14)
              have b41542 := hb (x (-7) 1)
              have b41543 := hb (x (-7) 1 && x (-7) 14)
              clear * - r41541 b41542 b41543 d41536
              omega
            have d41544 : (x (-8) 2).toNat = 1 := by
              have r41545 : 1 ≤ (x (-6) 13).toNat + (x (-7) 1 && x (-7) 14).toNat + (x (-8) 2).toNat := by have q := hcov13 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b41546 := hb (x (-8) 2)
              have b41547 := hb (x (-6) 13)
              have b41548 := hb (x (-7) 1 && x (-7) 14)
              clear * - r41545 b41546 b41547 b41548 d41503 d41540
              omega
            have d41549 : (x (-8) 14).toNat = 1 := by
              have r41550 : (x (-8) 2).toNat ≤ (x (-8) 14).toNat := himp _ _ (hp2 (-8))
              have b41551 := hb (x (-8) 2)
              have b41552 := hb (x (-8) 14)
              clear * - r41550 b41551 b41552 d41544
              omega
            have d41553 : (x (-9) 1).toNat = 0 := by
              have r41554 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b41555 := hb (x (-9) 1)
              have b41556 := hb (x (-8) 14)
              clear * - r41554 b41555 b41556 d41549
              omega
            have d41557 : (x (-9) 1 && x (-9) 12).toNat = 0 := by
              have r41558 := hand1 (x (-9) 1) (x (-9) 12)
              have b41559 := hb (x (-9) 1)
              have b41560 := hb (x (-9) 1 && x (-9) 12)
              clear * - r41558 b41559 b41560 d41553
              omega
            have d41561 : (x (-9) 13).toNat = 0 := by
              have r41562 : (x (-9) 13).toNat ≤ (x (-9) 1).toNat := himp _ _ (hp13 (-9))
              have b41563 := hb (x (-9) 1)
              have b41564 := hb (x (-9) 13)
              clear * - r41562 b41563 b41564 d41553
              omega
            have d41565 : (x (-6) 12).toNat = 0 := by
              have r41566 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e41567 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
              have e41568 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
              have b41569 := hb (x (-9) 3)
              have b41570 := hb (x (-8) 2)
              have b41571 := hb (x (-7) 13)
              have b41572 := hb (x (-6) 12)
              clear * - r41566 e41567 e41568 b41569 b41570 b41571 b41572 d41544
              omega
            have d41573 : (x (-6) 1 && x (-6) 12).toNat = 0 := by
              have r41574 := hand2 (x (-6) 1) (x (-6) 12)
              have b41575 := hb (x (-6) 12)
              have b41576 := hb (x (-6) 1 && x (-6) 12)
              clear * - r41574 b41575 b41576 d41565
              omega
            have d41577 : (x (-7) 13).toNat = 0 := by
              have r41578 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e41579 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
              have e41580 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
              have b41581 := hb (x (-9) 3)
              have b41582 := hb (x (-8) 2)
              have b41583 := hb (x (-7) 13)
              have b41584 := hb (x (-6) 12)
              clear * - r41578 e41579 e41580 b41581 b41582 b41583 b41584 d41565 d41544
              omega
            have d41585 : (x (-8) 3).toNat = 0 := by
              have r41586 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e41587 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
              have e41588 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
              have b41589 := hb (x (-8) 3)
              have b41590 := hb (x (-7) 2)
              have b41591 := hb (x (-6) 13)
              have b41592 := hb (x (-5) 12)
              clear * - r41586 e41587 e41588 b41589 b41590 b41591 b41592 d41499 d41503 d41515
              omega
            have d41593 : (x (-8) 3 && x (-8) 14).toNat = 0 := by
              have r41594 := hand1 (x (-8) 3) (x (-8) 14)
              have b41595 := hb (x (-8) 3)
              have b41596 := hb (x (-8) 3 && x (-8) 14)
              clear * - r41594 b41595 b41596 d41585
              omega
            have d41597 : (x (-8) 11).toNat = 0 := by
              have r41598 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
              have b41599 := hb (x (-8) 3)
              have b41600 := hb (x (-8) 11)
              clear * - r41598 b41599 b41600 d41585
              omega
            have d41601 : (x (-9) 4).toNat = 1 := by
              have r41602 : 1 ≤ (x (-5) 11).toNat + (x (-6) 1 && x (-6) 12).toNat + (x (-7) 2 && x (-7) 13).toNat + (x (-8) 3 && x (-8) 14).toNat + (x (-9) 4).toNat := by have q := hcov11 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b41603 := hb (x (-9) 4)
              have b41604 := hb (x (-5) 11)
              have b41605 := hb (x (-6) 1 && x (-6) 12)
              have b41606 := hb (x (-7) 2 && x (-7) 13)
              have b41607 := hb (x (-8) 3 && x (-8) 14)
              clear * - r41602 b41603 b41604 b41605 b41606 b41607 d41488 d41573 d41523 d41593
              omega
            have d41608 : (x (-9) 12).toNat = 1 := by
              have r41609 : (x (-9) 4).toNat ≤ (x (-9) 12).toNat := himp _ _ (hp4 (-9))
              have b41610 := hb (x (-9) 4)
              have b41611 := hb (x (-9) 12)
              clear * - r41609 b41610 b41611 d41601
              omega
            have d41612 : (x (-10) 13).toNat = 0 := by
              have r41613 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e41614 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
              have e41615 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
              have b41616 := hb (x (-12) 3)
              have b41617 := hb (x (-11) 2)
              have b41618 := hb (x (-10) 13)
              have b41619 := hb (x (-9) 12)
              clear * - r41613 e41614 e41615 b41616 b41617 b41618 b41619 d41608
              omega
            have d41620 : (x (-10) 2 && x (-10) 13).toNat = 0 := by
              have r41621 := hand2 (x (-10) 2) (x (-10) 13)
              have b41622 := hb (x (-10) 13)
              have b41623 := hb (x (-10) 2 && x (-10) 13)
              clear * - r41621 b41622 b41623 d41612
              omega
            have d41624 : (x (-11) 2).toNat = 0 := by
              have r41625 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e41626 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
              have e41627 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
              have b41628 := hb (x (-12) 3)
              have b41629 := hb (x (-11) 2)
              have b41630 := hb (x (-10) 13)
              have b41631 := hb (x (-9) 12)
              clear * - r41625 e41626 e41627 b41628 b41629 b41630 b41631 d41608 d41612
              omega
            have d41632 : (x (-10) 1 && x (-10) 14).toNat = 1 := by
              have r41633 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b41634 := hb (x (-11) 2)
              have b41635 := hb (x (-9) 13)
              have b41636 := hb (x (-10) 1 && x (-10) 14)
              clear * - r41633 b41634 b41635 b41636 d41561 d41624
              omega
            have d41637 : (x (-10) 1).toNat = 1 := by
              have r41638 := hand1 (x (-10) 1) (x (-10) 14)
              have b41639 := hb (x (-10) 1)
              have b41640 := hb (x (-10) 1 && x (-10) 14)
              clear * - r41638 b41639 b41640 d41632
              omega
            have d41641 : (x (-9) 14).toNat = 0 := by
              have r41642 : (x (-9) 14).toNat + (x (-10) 1).toNat = 1 := by have q := hd14 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b41643 := hb (x (-10) 1)
              have b41644 := hb (x (-9) 14)
              clear * - r41642 b41643 b41644 d41637
              omega
            have d41645 : (x (-9) 2).toNat = 0 := by
              have r41646 : (x (-9) 2).toNat ≤ (x (-9) 14).toNat := himp _ _ (hp2 (-9))
              have b41647 := hb (x (-9) 2)
              have b41648 := hb (x (-9) 14)
              clear * - r41646 b41647 b41648 d41641
              omega
            have d41649 : (x (-8) 1 && x (-8) 14).toNat = 1 := by
              have r41650 : 1 ≤ (x (-7) 13).toNat + (x (-8) 1 && x (-8) 14).toNat + (x (-9) 2).toNat := by have q := hcov13 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b41651 := hb (x (-9) 2)
              have b41652 := hb (x (-7) 13)
              have b41653 := hb (x (-8) 1 && x (-8) 14)
              clear * - r41650 b41651 b41652 b41653 d41577 d41645
              omega
            have d41654 : (x (-8) 1).toNat = 1 := by
              have r41655 := hand1 (x (-8) 1) (x (-8) 14)
              have b41656 := hb (x (-8) 1)
              have b41657 := hb (x (-8) 1 && x (-8) 14)
              clear * - r41655 b41656 b41657 d41649
              omega
            have d41658 : (x (-7) 14).toNat = 0 := by
              have r41659 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b41660 := hb (x (-8) 1)
              have b41661 := hb (x (-7) 14)
              clear * - r41659 b41660 b41661 d41654
              omega
            have d41662 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
              have r41663 := hand2 (x (-7) 3) (x (-7) 14)
              have b41664 := hb (x (-7) 14)
              have b41665 := hb (x (-7) 3 && x (-7) 14)
              clear * - r41663 b41664 b41665 d41658
              omega
            have d41666 : (x (-8) 4).toNat = 1 := by
              have r41667 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b41668 := hb (x (-8) 4)
              have b41669 := hb (x (-4) 11)
              have b41670 := hb (x (-5) 1 && x (-5) 12)
              have b41671 := hb (x (-6) 2 && x (-6) 13)
              have b41672 := hb (x (-7) 3 && x (-7) 14)
              clear * - r41667 b41668 b41669 b41670 b41671 b41672 d41464 d41440 d41511 d41662
              omega
            have d41673 : (x (-8) 12).toNat = 1 := by
              have r41674 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
              have b41675 := hb (x (-8) 4)
              have b41676 := hb (x (-8) 12)
              clear * - r41674 b41675 b41676 d41666
              omega
            have d41677 : (x (-10) 2).toNat = 0 := by
              have r41678 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e41679 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
              have e41680 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
              have b41681 := hb (x (-11) 3)
              have b41682 := hb (x (-10) 2)
              have b41683 := hb (x (-9) 13)
              have b41684 := hb (x (-8) 12)
              clear * - r41678 e41679 e41680 b41681 b41682 b41683 b41684 d41673 d41561
              omega
            have d41685 : (x (-11) 3).toNat = 0 := by
              have r41686 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e41687 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
              have e41688 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
              have b41689 := hb (x (-11) 3)
              have b41690 := hb (x (-10) 2)
              have b41691 := hb (x (-9) 13)
              have b41692 := hb (x (-8) 12)
              clear * - r41686 e41687 e41688 b41689 b41690 b41691 b41692 d41673 d41561 d41677
              omega
            have d41693 : (x (-11) 3 && x (-11) 14).toNat = 0 := by
              have r41694 := hand1 (x (-11) 3) (x (-11) 14)
              have b41695 := hb (x (-11) 3)
              have b41696 := hb (x (-11) 3 && x (-11) 14)
              clear * - r41694 b41695 b41696 d41685
              omega
            have r41697 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := by have q := hcov11 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b41698 := hb (x (-12) 4)
            have b41699 := hb (x (-8) 11)
            have b41700 := hb (x (-9) 1 && x (-9) 12)
            have b41701 := hb (x (-10) 2 && x (-10) 13)
            have b41702 := hb (x (-11) 3 && x (-11) 14)
            linarith only [r41697, b41698, b41699, b41700, b41701, b41702, d41597, d41557, d41620, d41693, d40978]
        · have f41703 : (x (-1) 8).toNat = 1 := by rw [h40996]; rfl
          have d41704 : (x (-2) 9).toNat = 0 := by
            have r41705 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e41706 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e41707 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e41708 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e41709 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e41710 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e41711 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have b41712 := hb (x (-8) 7)
            have b41713 := hb (x (-7) 6)
            have b41714 := hb (x (-6) 5)
            have b41715 := hb (x (-5) 4)
            have b41716 := hb (x (-4) 11)
            have b41717 := hb (x (-3) 10)
            have b41718 := hb (x (-2) 9)
            have b41719 := hb (x (-1) 8)
            clear * - r41705 e41706 e41707 e41708 e41709 e41710 e41711 b41712 b41713 b41714 b41715 b41716 b41717 b41718 b41719 f41703
            omega
          have d41720 : (x (-3) 10).toNat = 0 := by
            have r41721 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e41722 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e41723 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e41724 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e41725 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e41726 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e41727 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have b41728 := hb (x (-8) 7)
            have b41729 := hb (x (-7) 6)
            have b41730 := hb (x (-6) 5)
            have b41731 := hb (x (-5) 4)
            have b41732 := hb (x (-4) 11)
            have b41733 := hb (x (-3) 10)
            have b41734 := hb (x (-2) 9)
            have b41735 := hb (x (-1) 8)
            clear * - r41721 e41722 e41723 e41724 e41725 e41726 e41727 b41728 b41729 b41730 b41731 b41732 b41733 b41734 b41735 f41703 d41704
            omega
          have d41736 : (x (-3) 1 && x (-3) 10).toNat = 0 := by
            have r41737 := hand2 (x (-3) 1) (x (-3) 10)
            have b41738 := hb (x (-3) 10)
            have b41739 := hb (x (-3) 1 && x (-3) 10)
            clear * - r41737 b41738 b41739 d41720
            omega
          have d41740 : (x (-4) 11).toNat = 0 := by
            have r41741 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e41742 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e41743 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e41744 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e41745 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e41746 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e41747 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have b41748 := hb (x (-8) 7)
            have b41749 := hb (x (-7) 6)
            have b41750 := hb (x (-6) 5)
            have b41751 := hb (x (-5) 4)
            have b41752 := hb (x (-4) 11)
            have b41753 := hb (x (-3) 10)
            have b41754 := hb (x (-2) 9)
            have b41755 := hb (x (-1) 8)
            clear * - r41741 e41742 e41743 e41744 e41745 e41746 e41747 b41748 b41749 b41750 b41751 b41752 b41753 b41754 b41755 f41703 d41704 d41720
            omega
          have d41756 : (x (-4) 2 && x (-4) 11).toNat = 0 := by
            have r41757 := hand2 (x (-4) 2) (x (-4) 11)
            have b41758 := hb (x (-4) 11)
            have b41759 := hb (x (-4) 2 && x (-4) 11)
            clear * - r41757 b41758 b41759 d41740
            omega
          have d41760 : (x (-5) 4).toNat = 0 := by
            have r41761 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e41762 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e41763 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e41764 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e41765 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e41766 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e41767 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have b41768 := hb (x (-8) 7)
            have b41769 := hb (x (-7) 6)
            have b41770 := hb (x (-6) 5)
            have b41771 := hb (x (-5) 4)
            have b41772 := hb (x (-4) 11)
            have b41773 := hb (x (-3) 10)
            have b41774 := hb (x (-2) 9)
            have b41775 := hb (x (-1) 8)
            clear * - r41761 e41762 e41763 e41764 e41765 e41766 e41767 b41768 b41769 b41770 b41771 b41772 b41773 b41774 b41775 f41703 d41704 d41720 d41740
            omega
          have d41776 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
            have r41777 := hand1 (x (-5) 4) (x (-5) 14)
            have b41778 := hb (x (-5) 4)
            have b41779 := hb (x (-5) 4 && x (-5) 14)
            clear * - r41777 b41778 b41779 d41760
            omega
          have d41780 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
            have r41781 := hand1 (x (-5) 4) (x (-5) 13)
            have b41782 := hb (x (-5) 4)
            have b41783 := hb (x (-5) 4 && x (-5) 13)
            clear * - r41781 b41782 b41783 d41760
            omega
          have d41784 : (x (-5) 4 && x (-5) 11).toNat = 0 := by
            have r41785 := hand1 (x (-5) 4) (x (-5) 11)
            have b41786 := hb (x (-5) 4)
            have b41787 := hb (x (-5) 4 && x (-5) 11)
            clear * - r41785 b41786 b41787 d41760
            omega
          have d41788 : (x (-5) 4 && x (-5) 9).toNat = 0 := by
            have r41789 := hand1 (x (-5) 4) (x (-5) 9)
            have b41790 := hb (x (-5) 4)
            have b41791 := hb (x (-5) 4 && x (-5) 9)
            clear * - r41789 b41790 b41791 d41760
            omega
          have d41792 : (x (-6) 5).toNat = 0 := by
            have r41793 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e41794 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e41795 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e41796 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e41797 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e41798 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e41799 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have b41800 := hb (x (-8) 7)
            have b41801 := hb (x (-7) 6)
            have b41802 := hb (x (-6) 5)
            have b41803 := hb (x (-5) 4)
            have b41804 := hb (x (-4) 11)
            have b41805 := hb (x (-3) 10)
            have b41806 := hb (x (-2) 9)
            have b41807 := hb (x (-1) 8)
            clear * - r41793 e41794 e41795 e41796 e41797 e41798 e41799 b41800 b41801 b41802 b41803 b41804 b41805 b41806 b41807 f41703 d41704 d41720 d41740 d41760
            omega
          have d41808 : (x (-6) 5 && x (-6) 14).toNat = 0 := by
            have r41809 := hand1 (x (-6) 5) (x (-6) 14)
            have b41810 := hb (x (-6) 5)
            have b41811 := hb (x (-6) 5 && x (-6) 14)
            clear * - r41809 b41810 b41811 d41792
            omega
          have d41812 : (x (-6) 5 && x (-6) 12).toNat = 0 := by
            have r41813 := hand1 (x (-6) 5) (x (-6) 12)
            have b41814 := hb (x (-6) 5)
            have b41815 := hb (x (-6) 5 && x (-6) 12)
            clear * - r41813 b41814 b41815 d41792
            omega
          have d41816 : (x (-6) 5 && x (-6) 10).toNat = 0 := by
            have r41817 := hand1 (x (-6) 5) (x (-6) 10)
            have b41818 := hb (x (-6) 5)
            have b41819 := hb (x (-6) 5 && x (-6) 10)
            clear * - r41817 b41818 b41819 d41792
            omega
          have d41820 : (x (-7) 6).toNat = 0 := by
            have r41821 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e41822 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e41823 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e41824 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e41825 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e41826 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e41827 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have b41828 := hb (x (-8) 7)
            have b41829 := hb (x (-7) 6)
            have b41830 := hb (x (-6) 5)
            have b41831 := hb (x (-5) 4)
            have b41832 := hb (x (-4) 11)
            have b41833 := hb (x (-3) 10)
            have b41834 := hb (x (-2) 9)
            have b41835 := hb (x (-1) 8)
            clear * - r41821 e41822 e41823 e41824 e41825 e41826 e41827 b41828 b41829 b41830 b41831 b41832 b41833 b41834 b41835 f41703 d41704 d41720 d41740 d41760 d41792
            omega
          have d41836 : (x (-7) 6 && x (-7) 13).toNat = 0 := by
            have r41837 := hand1 (x (-7) 6) (x (-7) 13)
            have b41838 := hb (x (-7) 6)
            have b41839 := hb (x (-7) 6 && x (-7) 13)
            clear * - r41837 b41838 b41839 d41820
            omega
          have d41840 : (x (-7) 6 && x (-7) 11).toNat = 0 := by
            have r41841 := hand1 (x (-7) 6) (x (-7) 11)
            have b41842 := hb (x (-7) 6)
            have b41843 := hb (x (-7) 6 && x (-7) 11)
            clear * - r41841 b41842 b41843 d41820
            omega
          have d41844 : (x (-4) 3 && x (-4) 12).toNat = 1 := by
            have r41845 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b41846 := hb (x (-7) 6)
            have b41847 := hb (x (-1) 9)
            have b41848 := hb (x (-2) 1 && x (-2) 10)
            have b41849 := hb (x (-3) 2 && x (-3) 11)
            have b41850 := hb (x (-4) 3 && x (-4) 12)
            have b41851 := hb (x (-5) 4 && x (-5) 13)
            have b41852 := hb (x (-6) 5 && x (-6) 14)
            clear * - r41845 b41846 b41847 b41848 b41849 b41850 b41851 b41852 g7 g100 g101 d41780 d41808 d41820
            omega
          have d41853 : (x (-4) 12).toNat = 1 := by
            have r41854 := hand2 (x (-4) 3) (x (-4) 12)
            have b41855 := hb (x (-4) 12)
            have b41856 := hb (x (-4) 3 && x (-4) 12)
            clear * - r41854 b41855 b41856 d41844
            omega
          have d41857 : (x (-5) 13).toNat = 0 := by
            have r41858 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e41859 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
            have e41860 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
            have b41861 := hb (x (-7) 3)
            have b41862 := hb (x (-6) 2)
            have b41863 := hb (x (-5) 13)
            have b41864 := hb (x (-4) 12)
            clear * - r41858 e41859 e41860 b41861 b41862 b41863 b41864 d41853
            omega
          have d41865 : (x (-6) 2).toNat = 0 := by
            have r41866 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e41867 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
            have e41868 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
            have b41869 := hb (x (-7) 3)
            have b41870 := hb (x (-6) 2)
            have b41871 := hb (x (-5) 13)
            have b41872 := hb (x (-4) 12)
            clear * - r41866 e41867 e41868 b41869 b41870 b41871 b41872 d41853 d41857
            omega
          have d41873 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
            have r41874 := hand1 (x (-6) 2) (x (-6) 13)
            have b41875 := hb (x (-6) 2)
            have b41876 := hb (x (-6) 2 && x (-6) 13)
            clear * - r41874 b41875 b41876 d41865
            omega
          have d41877 : (x (-6) 10).toNat = 0 := by
            have r41878 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
            have b41879 := hb (x (-6) 2)
            have b41880 := hb (x (-6) 10)
            clear * - r41878 b41879 b41880 d41865
            omega
          have d41881 : (x (-7) 3).toNat = 0 := by
            have r41882 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e41883 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
            have e41884 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
            have b41885 := hb (x (-7) 3)
            have b41886 := hb (x (-6) 2)
            have b41887 := hb (x (-5) 13)
            have b41888 := hb (x (-4) 12)
            clear * - r41882 e41883 e41884 b41885 b41886 b41887 b41888 d41853 d41857 d41865
            omega
          have d41889 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
            have r41890 := hand1 (x (-7) 3) (x (-7) 14)
            have b41891 := hb (x (-7) 3)
            have b41892 := hb (x (-7) 3 && x (-7) 14)
            clear * - r41890 b41891 b41892 d41881
            omega
          have d41893 : (x (-7) 11).toNat = 0 := by
            have r41894 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
            have b41895 := hb (x (-7) 3)
            have b41896 := hb (x (-7) 11)
            clear * - r41894 b41895 b41896 d41881
            omega
          have d41897 : (x (-4) 3).toNat = 1 := by
            have r41898 := hand1 (x (-4) 3) (x (-4) 12)
            have b41899 := hb (x (-4) 3)
            have b41900 := hb (x (-4) 3 && x (-4) 12)
            clear * - r41898 b41899 b41900 d41844
            omega
          have d41901 : (x (-1) 12).toNat = 0 := by
            have r41902 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e41903 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e41904 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b41905 := hb (x (-4) 3)
            have b41906 := hb (x (-3) 2)
            have b41907 := hb (x (-2) 13)
            have b41908 := hb (x (-1) 12)
            clear * - r41902 e41903 e41904 b41905 b41906 b41907 b41908 d41897
            omega
          have d41909 : (x (-2) 13).toNat = 0 := by
            have r41910 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e41911 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e41912 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b41913 := hb (x (-4) 3)
            have b41914 := hb (x (-3) 2)
            have b41915 := hb (x (-2) 13)
            have b41916 := hb (x (-1) 12)
            clear * - r41910 e41911 e41912 b41913 b41914 b41915 b41916 d41901 d41897
            omega
          have d41917 : (x (-3) 2).toNat = 0 := by
            have r41918 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e41919 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e41920 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b41921 := hb (x (-4) 3)
            have b41922 := hb (x (-3) 2)
            have b41923 := hb (x (-2) 13)
            have b41924 := hb (x (-1) 12)
            clear * - r41918 e41919 e41920 b41921 b41922 b41923 b41924 d41901 d41909 d41897
            omega
          have d41925 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
            have r41926 := hand1 (x (-3) 2) (x (-3) 12)
            have b41927 := hb (x (-3) 2)
            have b41928 := hb (x (-3) 2 && x (-3) 12)
            clear * - r41926 b41927 b41928 d41917
            omega
          have d41929 : (x (-4) 3 && x (-4) 13).toNat = 1 := by
            have r41930 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b41931 := hb (x (-6) 5)
            have b41932 := hb (x (-1) 10)
            have b41933 := hb (x (-2) 1 && x (-2) 11)
            have b41934 := hb (x (-3) 2 && x (-3) 12)
            have b41935 := hb (x (-4) 3 && x (-4) 13)
            have b41936 := hb (x (-5) 4 && x (-5) 14)
            clear * - r41930 b41931 b41932 b41933 b41934 b41935 b41936 g8 g108 d41925 d41776 d41792
            omega
          have d41937 : (x (-4) 13).toNat = 1 := by
            have r41938 := hand2 (x (-4) 3) (x (-4) 13)
            have b41939 := hb (x (-4) 13)
            have b41940 := hb (x (-4) 3 && x (-4) 13)
            clear * - r41938 b41939 b41940 d41929
            omega
          have d41941 : (x (-4) 1).toNat = 1 := by
            have r41942 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
            have b41943 := hb (x (-4) 1)
            have b41944 := hb (x (-4) 13)
            clear * - r41942 b41943 b41944 d41937
            omega
          have d41945 : (x (-3) 14).toNat = 0 := by
            have r41946 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b41947 := hb (x (-4) 1)
            have b41948 := hb (x (-3) 14)
            clear * - r41946 b41947 b41948 d41941
            omega
          have d41949 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
            have r41950 := hand2 (x (-3) 1) (x (-3) 14)
            have b41951 := hb (x (-3) 14)
            have b41952 := hb (x (-3) 1 && x (-3) 14)
            clear * - r41950 b41951 b41952 d41945
            omega
          have d41953 : (x (-4) 2).toNat = 1 := by
            have r41954 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b41955 := hb (x (-4) 2)
            have b41956 := hb (x (-2) 13)
            have b41957 := hb (x (-3) 1 && x (-3) 14)
            clear * - r41954 b41955 b41956 b41957 d41909 d41949
            omega
          have d41958 : (x (-4) 14).toNat = 1 := by
            have r41959 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
            have b41960 := hb (x (-4) 2)
            have b41961 := hb (x (-4) 14)
            clear * - r41959 b41960 b41961 d41953
            omega
          have d41962 : (x (-5) 1).toNat = 0 := by
            have r41963 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b41964 := hb (x (-5) 1)
            have b41965 := hb (x (-4) 14)
            clear * - r41963 b41964 b41965 d41958
            omega
          have d41966 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
            have r41967 := hand1 (x (-5) 1) (x (-5) 12)
            have b41968 := hb (x (-5) 1)
            have b41969 := hb (x (-5) 1 && x (-5) 12)
            clear * - r41967 b41968 b41969 d41962
            omega
          have d41970 : (x (-8) 4).toNat = 1 := by
            have r41971 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b41972 := hb (x (-8) 4)
            have b41973 := hb (x (-4) 11)
            have b41974 := hb (x (-5) 1 && x (-5) 12)
            have b41975 := hb (x (-6) 2 && x (-6) 13)
            have b41976 := hb (x (-7) 3 && x (-7) 14)
            clear * - r41971 b41972 b41973 b41974 b41975 b41976 d41740 d41966 d41873 d41889
            omega
          have d41977 : (x (-8) 12).toNat = 1 := by
            have r41978 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
            have b41979 := hb (x (-8) 4)
            have b41980 := hb (x (-8) 12)
            clear * - r41978 b41979 b41980 d41970
            omega
          have d41981 : (x (-9) 13).toNat = 0 := by
            have r41982 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e41983 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
            have e41984 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
            have b41985 := hb (x (-11) 3)
            have b41986 := hb (x (-10) 2)
            have b41987 := hb (x (-9) 13)
            have b41988 := hb (x (-8) 12)
            clear * - r41982 e41983 e41984 b41985 b41986 b41987 b41988 d41977
            omega
          have d41989 : (x (-9) 8 && x (-9) 13).toNat = 0 := by
            have r41990 := hand2 (x (-9) 8) (x (-9) 13)
            have b41991 := hb (x (-9) 13)
            have b41992 := hb (x (-9) 8 && x (-9) 13)
            clear * - r41990 b41991 b41992 d41981
            omega
          have d41993 : (x (-9) 5).toNat = 0 := by
            have r41994 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
            have b41995 := hb (x (-9) 5)
            have b41996 := hb (x (-9) 13)
            clear * - r41994 b41995 b41996 d41981
            omega
          have d41997 : (x (-10) 2).toNat = 0 := by
            have r41998 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e41999 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
            have e42000 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
            have b42001 := hb (x (-11) 3)
            have b42002 := hb (x (-10) 2)
            have b42003 := hb (x (-9) 13)
            have b42004 := hb (x (-8) 12)
            clear * - r41998 e41999 e42000 b42001 b42002 b42003 b42004 d41977 d41981
            omega
          have d42005 : (x (-10) 2 && x (-10) 13).toNat = 0 := by
            have r42006 := hand1 (x (-10) 2) (x (-10) 13)
            have b42007 := hb (x (-10) 2)
            have b42008 := hb (x (-10) 2 && x (-10) 13)
            clear * - r42006 b42007 b42008 d41997
            omega
          have d42009 : (x (-11) 3).toNat = 0 := by
            have r42010 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e42011 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
            have e42012 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
            have b42013 := hb (x (-11) 3)
            have b42014 := hb (x (-10) 2)
            have b42015 := hb (x (-9) 13)
            have b42016 := hb (x (-8) 12)
            clear * - r42010 e42011 e42012 b42013 b42014 b42015 b42016 d41977 d41981 d41997
            omega
          have d42017 : (x (-11) 3 && x (-11) 14).toNat = 0 := by
            have r42018 := hand1 (x (-11) 3) (x (-11) 14)
            have b42019 := hb (x (-11) 3)
            have b42020 := hb (x (-11) 3 && x (-11) 14)
            clear * - r42018 b42019 b42020 d42009
            omega
          have d42021 : (x (-5) 9).toNat = 0 := by
            have r42022 : (x (-5) 9).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp9 (-5))
            have b42023 := hb (x (-5) 1)
            have b42024 := hb (x (-5) 9)
            clear * - r42022 b42023 b42024 d41962
            omega
          have d42025 : (x (-2) 12).toNat = 0 := by
            have r42026 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e42027 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
            have e42028 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
            have b42029 := hb (x (-5) 3)
            have b42030 := hb (x (-4) 2)
            have b42031 := hb (x (-3) 13)
            have b42032 := hb (x (-2) 12)
            clear * - r42026 e42027 e42028 b42029 b42030 b42031 b42032 d41953
            omega
          have d42033 : (x (-3) 13).toNat = 0 := by
            have r42034 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e42035 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
            have e42036 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
            have b42037 := hb (x (-5) 3)
            have b42038 := hb (x (-4) 2)
            have b42039 := hb (x (-3) 13)
            have b42040 := hb (x (-2) 12)
            clear * - r42034 e42035 e42036 b42037 b42038 b42039 b42040 d42025 d41953
            omega
          have d42041 : (x (-5) 3).toNat = 0 := by
            have r42042 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e42043 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
            have e42044 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
            have b42045 := hb (x (-5) 3)
            have b42046 := hb (x (-4) 2)
            have b42047 := hb (x (-3) 13)
            have b42048 := hb (x (-2) 12)
            clear * - r42042 e42043 e42044 b42045 b42046 b42047 b42048 d42025 d42033 d41953
            omega
          have d42049 : (x (-5) 3 && x (-5) 12).toNat = 0 := by
            have r42050 := hand1 (x (-5) 3) (x (-5) 12)
            have b42051 := hb (x (-5) 3)
            have b42052 := hb (x (-5) 3 && x (-5) 12)
            clear * - r42050 b42051 b42052 d42041
            omega
          have d42053 : (x (-5) 11).toNat = 0 := by
            have r42054 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
            have b42055 := hb (x (-5) 3)
            have b42056 := hb (x (-5) 11)
            clear * - r42054 b42055 b42056 d42041
            omega
          have d42057 : (x (-3) 2 && x (-3) 9).toNat = 0 := by
            have r42058 := hand1 (x (-3) 2) (x (-3) 9)
            have b42059 := hb (x (-3) 2)
            have b42060 := hb (x (-3) 2 && x (-3) 9)
            clear * - r42058 b42059 b42060 d41917
            omega
          have d42061 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
            have r42062 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b42063 := hb (x (-3) 2)
            have b42064 := hb (x (-1) 13)
            have b42065 := hb (x (-2) 1 && x (-2) 14)
            clear * - r42062 b42063 b42064 b42065 g10 d41917
            omega
          have d42066 : (x (-2) 14).toNat = 1 := by
            have r42067 := hand2 (x (-2) 1) (x (-2) 14)
            have b42068 := hb (x (-2) 14)
            have b42069 := hb (x (-2) 1 && x (-2) 14)
            clear * - r42067 b42068 b42069 d42061
            omega
          have d42070 : (x (-3) 1).toNat = 0 := by
            have r42071 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b42072 := hb (x (-3) 1)
            have b42073 := hb (x (-2) 14)
            clear * - r42071 b42072 b42073 d42066
            omega
          have d42074 : (x (-3) 9).toNat = 0 := by
            have r42075 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
            have b42076 := hb (x (-3) 1)
            have b42077 := hb (x (-3) 9)
            clear * - r42075 b42076 b42077 d42070
            omega
          have d42078 : (x (-8) 7).toNat = 0 := by
            have r42079 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e42080 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e42081 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e42082 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e42083 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e42084 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e42085 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have b42086 := hb (x (-8) 7)
            have b42087 := hb (x (-7) 6)
            have b42088 := hb (x (-6) 5)
            have b42089 := hb (x (-5) 4)
            have b42090 := hb (x (-4) 11)
            have b42091 := hb (x (-3) 10)
            have b42092 := hb (x (-2) 9)
            have b42093 := hb (x (-1) 8)
            clear * - r42079 e42080 e42081 e42082 e42083 e42084 e42085 b42086 b42087 b42088 b42089 b42090 b42091 b42092 b42093 f41703 d41704 d41720 d41740 d41760 d41792 d41820
            omega
          have d42094 : (x (-8) 7 && x (-8) 14).toNat = 0 := by
            have r42095 := hand1 (x (-8) 7) (x (-8) 14)
            have b42096 := hb (x (-8) 7)
            have b42097 := hb (x (-8) 7 && x (-8) 14)
            clear * - r42095 b42096 b42097 d42078
            omega
          have d42098 : (x (-8) 7 && x (-8) 12).toNat = 0 := by
            have r42099 := hand1 (x (-8) 7) (x (-8) 12)
            have b42100 := hb (x (-8) 7)
            have b42101 := hb (x (-8) 7 && x (-8) 12)
            clear * - r42099 b42100 b42101 d42078
            omega
          have d42102 : (x (-4) 8).toNat = 0 := by
            have r42103 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e42104 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
            have e42105 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
            have e42106 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
            have e42107 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
            have e42108 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
            have e42109 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
            have b42110 := hb (x (-11) 7)
            have b42111 := hb (x (-10) 6)
            have b42112 := hb (x (-9) 5)
            have b42113 := hb (x (-8) 4)
            have b42114 := hb (x (-7) 11)
            have b42115 := hb (x (-6) 10)
            have b42116 := hb (x (-5) 9)
            have b42117 := hb (x (-4) 8)
            clear * - r42103 e42104 e42105 e42106 e42107 e42108 e42109 b42110 b42111 b42112 b42113 b42114 b42115 b42116 b42117 d42021 d41877 d41893 d41970 d41993
            omega
          have d42118 : (x (-4) 3 && x (-4) 8).toNat = 0 := by
            have r42119 := hand2 (x (-4) 3) (x (-4) 8)
            have b42120 := hb (x (-4) 8)
            have b42121 := hb (x (-4) 3 && x (-4) 8)
            clear * - r42119 b42120 b42121 d42102
            omega
          have d42122 : (x (-10) 14).toNat = 0 := by
            have r42123 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b42124 := hb (x (-10) 14)
            have b42125 := hb (x (-9) 13)
            have b42126 := hb (x (-8) 12)
            have b42127 := hb (x (-7) 11)
            have b42128 := hb (x (-6) 10)
            have b42129 := hb (x (-5) 9)
            have b42130 := hb (x (-4) 8)
            have b42131 := hb (x (-3) 7)
            have b42132 := hb (x (-2) 6)
            have b42133 := hb (x (-1) 5)
            have b42134 := hb (x 0 4)
            have b42135 := hb (x 1 3)
            have b42136 := hb (x 2 2)
            have b42137 := hb (x 3 1)
            clear * - r42123 b42124 b42125 b42126 b42127 b42128 b42129 b42130 b42131 b42132 b42133 b42134 b42135 b42136 b42137 g30 g25 g18 g12 g6 g2 g0 d42102 d42021 d41877 d41893 d41977 d41981
            omega
          have d42138 : (x (-10) 1 && x (-10) 14).toNat = 0 := by
            have r42139 := hand2 (x (-10) 1) (x (-10) 14)
            have b42140 := hb (x (-10) 14)
            have b42141 := hb (x (-10) 1 && x (-10) 14)
            clear * - r42139 b42140 b42141 d42122
            omega
          have d42142 : (x (-11) 2).toNat = 1 := by
            have r42143 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b42144 := hb (x (-11) 2)
            have b42145 := hb (x (-9) 13)
            have b42146 := hb (x (-10) 1 && x (-10) 14)
            clear * - r42143 b42144 b42145 b42146 d41981 d42138
            omega
          have d42147 : (x (-9) 12).toNat = 0 := by
            have r42148 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e42149 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
            have e42150 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
            have b42151 := hb (x (-12) 3)
            have b42152 := hb (x (-11) 2)
            have b42153 := hb (x (-10) 13)
            have b42154 := hb (x (-9) 12)
            clear * - r42148 e42149 e42150 b42151 b42152 b42153 b42154 d42142
            omega
          have d42155 : (x (-9) 1 && x (-9) 12).toNat = 0 := by
            have r42156 := hand2 (x (-9) 1) (x (-9) 12)
            have b42157 := hb (x (-9) 12)
            have b42158 := hb (x (-9) 1 && x (-9) 12)
            clear * - r42156 b42157 b42158 d42147
            omega
          have d42159 : (x (-8) 11).toNat = 1 := by
            have r42160 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := by have q := hcov11 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b42161 := hb (x (-12) 4)
            have b42162 := hb (x (-8) 11)
            have b42163 := hb (x (-9) 1 && x (-9) 12)
            have b42164 := hb (x (-10) 2 && x (-10) 13)
            have b42165 := hb (x (-11) 3 && x (-11) 14)
            clear * - r42160 b42161 b42162 b42163 b42164 b42165 d42155 d42005 d42017 d40978
            omega
          have d42166 : (x (-8) 3).toNat = 1 := by
            have r42167 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
            have b42168 := hb (x (-8) 3)
            have b42169 := hb (x (-8) 11)
            clear * - r42167 b42168 b42169 d42159
            omega
          have d42170 : (x (-5) 12).toNat = 0 := by
            have r42171 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e42172 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
            have e42173 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
            have b42174 := hb (x (-8) 3)
            have b42175 := hb (x (-7) 2)
            have b42176 := hb (x (-6) 13)
            have b42177 := hb (x (-5) 12)
            clear * - r42171 e42172 e42173 b42174 b42175 b42176 b42177 d42166
            omega
          have d42178 : (x (-6) 13).toNat = 0 := by
            have r42179 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e42180 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
            have e42181 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
            have b42182 := hb (x (-8) 3)
            have b42183 := hb (x (-7) 2)
            have b42184 := hb (x (-6) 13)
            have b42185 := hb (x (-5) 12)
            clear * - r42179 e42180 e42181 b42182 b42183 b42184 b42185 d42170 d42166
            omega
          have d42186 : (x (-6) 4 && x (-6) 13).toNat = 0 := by
            have r42187 := hand2 (x (-6) 4) (x (-6) 13)
            have b42188 := hb (x (-6) 13)
            have b42189 := hb (x (-6) 4 && x (-6) 13)
            clear * - r42187 b42188 b42189 d42178
            omega
          have d42190 : (x (-7) 2).toNat = 0 := by
            have r42191 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e42192 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
            have e42193 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
            have b42194 := hb (x (-8) 3)
            have b42195 := hb (x (-7) 2)
            have b42196 := hb (x (-6) 13)
            have b42197 := hb (x (-5) 12)
            clear * - r42191 e42192 e42193 b42194 b42195 b42196 b42197 d42170 d42178 d42166
            omega
          have d42198 : (x (-6) 1 && x (-6) 14).toNat = 1 := by
            have r42199 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b42200 := hb (x (-7) 2)
            have b42201 := hb (x (-5) 13)
            have b42202 := hb (x (-6) 1 && x (-6) 14)
            clear * - r42199 b42200 b42201 b42202 d41857 d42190
            omega
          have d42203 : (x (-6) 14).toNat = 1 := by
            have r42204 := hand2 (x (-6) 1) (x (-6) 14)
            have b42205 := hb (x (-6) 14)
            have b42206 := hb (x (-6) 1 && x (-6) 14)
            clear * - r42204 b42205 b42206 d42198
            omega
          have d42207 : (x (-7) 1).toNat = 0 := by
            have r42208 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b42209 := hb (x (-7) 1)
            have b42210 := hb (x (-6) 14)
            clear * - r42208 b42209 b42210 d42203
            omega
          have d42211 : (x (-7) 1 && x (-7) 14).toNat = 0 := by
            have r42212 := hand1 (x (-7) 1) (x (-7) 14)
            have b42213 := hb (x (-7) 1)
            have b42214 := hb (x (-7) 1 && x (-7) 14)
            clear * - r42212 b42213 b42214 d42207
            omega
          have d42215 : (x (-8) 2).toNat = 1 := by
            have r42216 : 1 ≤ (x (-6) 13).toNat + (x (-7) 1 && x (-7) 14).toNat + (x (-8) 2).toNat := by have q := hcov13 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b42217 := hb (x (-8) 2)
            have b42218 := hb (x (-6) 13)
            have b42219 := hb (x (-7) 1 && x (-7) 14)
            clear * - r42216 b42217 b42218 b42219 d42178 d42211
            omega
          have d42220 : (x (-8) 14).toNat = 1 := by
            have r42221 : (x (-8) 2).toNat ≤ (x (-8) 14).toNat := himp _ _ (hp2 (-8))
            have b42222 := hb (x (-8) 2)
            have b42223 := hb (x (-8) 14)
            clear * - r42221 b42222 b42223 d42215
            omega
          have d42224 : (x (-9) 1).toNat = 0 := by
            have r42225 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b42226 := hb (x (-9) 1)
            have b42227 := hb (x (-8) 14)
            clear * - r42225 b42226 b42227 d42220
            omega
          have d42228 : (x (-9) 1 && x (-9) 14).toNat = 0 := by
            have r42229 := hand1 (x (-9) 1) (x (-9) 14)
            have b42230 := hb (x (-9) 1)
            have b42231 := hb (x (-9) 1 && x (-9) 14)
            clear * - r42229 b42230 b42231 d42224
            omega
          have d42232 : (x (-8) 13).toNat = 1 := by
            have r42233 : 1 ≤ (x (-8) 13).toNat + (x (-9) 1 && x (-9) 14).toNat + (x (-10) 2).toNat := by have q := hcov13 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b42234 := hb (x (-10) 2)
            have b42235 := hb (x (-8) 13)
            have b42236 := hb (x (-9) 1 && x (-9) 14)
            clear * - r42233 b42234 b42235 b42236 d42228 d41997
            omega
          have d42237 : (x (-8) 1).toNat = 1 := by
            have r42238 : (x (-8) 13).toNat ≤ (x (-8) 1).toNat := himp _ _ (hp13 (-8))
            have b42239 := hb (x (-8) 1)
            have b42240 := hb (x (-8) 13)
            clear * - r42238 b42239 b42240 d42232
            omega
          have d42241 : (x (-7) 14).toNat = 0 := by
            have r42242 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b42243 := hb (x (-8) 1)
            have b42244 := hb (x (-7) 14)
            clear * - r42242 b42243 b42244 d42237
            omega
          have d42245 : (x (-7) 5 && x (-7) 14).toNat = 0 := by
            have r42246 := hand2 (x (-7) 5) (x (-7) 14)
            have b42247 := hb (x (-7) 14)
            have b42248 := hb (x (-7) 5 && x (-7) 14)
            clear * - r42246 b42247 b42248 d42241
            omega
          have d42249 : (x (-8) 6).toNat = 1 := by
            have r42250 : 1 ≤ (x (-2) 9).toNat + (x (-3) 1 && x (-3) 10).toNat + (x (-4) 2 && x (-4) 11).toNat + (x (-5) 3 && x (-5) 12).toNat + (x (-6) 4 && x (-6) 13).toNat + (x (-7) 5 && x (-7) 14).toNat + (x (-8) 6).toNat := by have q := hcov9 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b42251 := hb (x (-8) 6)
            have b42252 := hb (x (-2) 9)
            have b42253 := hb (x (-3) 1 && x (-3) 10)
            have b42254 := hb (x (-4) 2 && x (-4) 11)
            have b42255 := hb (x (-5) 3 && x (-5) 12)
            have b42256 := hb (x (-6) 4 && x (-6) 13)
            have b42257 := hb (x (-7) 5 && x (-7) 14)
            clear * - r42250 b42251 b42252 b42253 b42254 b42255 b42256 b42257 d41704 d41736 d41756 d42049 d42186 d42245
            omega
          have d42258 : (x (-2) 8).toNat = 0 := by
            have r42259 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e42260 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
            have e42261 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
            have e42262 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
            have e42263 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
            have e42264 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
            have e42265 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
            have b42266 := hb (x (-9) 7)
            have b42267 := hb (x (-8) 6)
            have b42268 := hb (x (-7) 5)
            have b42269 := hb (x (-6) 4)
            have b42270 := hb (x (-5) 11)
            have b42271 := hb (x (-4) 10)
            have b42272 := hb (x (-3) 9)
            have b42273 := hb (x (-2) 8)
            clear * - r42259 e42260 e42261 e42262 e42263 e42264 e42265 b42266 b42267 b42268 b42269 b42270 b42271 b42272 b42273 d42074 d42053 d42249
            omega
          have d42274 : (x (-2) 1 && x (-2) 8).toNat = 0 := by
            have r42275 := hand2 (x (-2) 1) (x (-2) 8)
            have b42276 := hb (x (-2) 8)
            have b42277 := hb (x (-2) 1 && x (-2) 8)
            clear * - r42275 b42276 b42277 d42258
            omega
          have d42278 : (x (-4) 10).toNat = 0 := by
            have r42279 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e42280 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
            have e42281 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
            have e42282 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
            have e42283 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
            have e42284 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
            have e42285 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
            have b42286 := hb (x (-9) 7)
            have b42287 := hb (x (-8) 6)
            have b42288 := hb (x (-7) 5)
            have b42289 := hb (x (-6) 4)
            have b42290 := hb (x (-5) 11)
            have b42291 := hb (x (-4) 10)
            have b42292 := hb (x (-3) 9)
            have b42293 := hb (x (-2) 8)
            clear * - r42279 e42280 e42281 e42282 e42283 e42284 e42285 b42286 b42287 b42288 b42289 b42290 b42291 b42292 b42293 d42258 d42074 d42053 d42249
            omega
          have d42294 : (x (-4) 3 && x (-4) 10).toNat = 0 := by
            have r42295 := hand2 (x (-4) 3) (x (-4) 10)
            have b42296 := hb (x (-4) 10)
            have b42297 := hb (x (-4) 3 && x (-4) 10)
            clear * - r42295 b42296 b42297 d42278
            omega
          have d42298 : (x (-9) 8).toNat = 1 := by
            have r42299 : 1 ≤ (x (-1) 7).toNat + (x (-2) 1 && x (-2) 8).toNat + (x (-3) 2 && x (-3) 9).toNat + (x (-4) 3 && x (-4) 10).toNat + (x (-5) 4 && x (-5) 11).toNat + (x (-6) 5 && x (-6) 12).toNat + (x (-7) 6 && x (-7) 13).toNat + (x (-8) 7 && x (-8) 14).toNat + (x (-9) 8).toNat := by have q := hcov7 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b42300 := hb (x (-9) 8)
            have b42301 := hb (x (-1) 7)
            have b42302 := hb (x (-2) 1 && x (-2) 8)
            have b42303 := hb (x (-3) 2 && x (-3) 9)
            have b42304 := hb (x (-4) 3 && x (-4) 10)
            have b42305 := hb (x (-5) 4 && x (-5) 11)
            have b42306 := hb (x (-6) 5 && x (-6) 12)
            have b42307 := hb (x (-7) 6 && x (-7) 13)
            have b42308 := hb (x (-8) 7 && x (-8) 14)
            clear * - r42299 b42300 b42301 b42302 b42303 b42304 b42305 b42306 b42307 b42308 d40030 d42274 d42057 d42294 d41784 d41812 d41836 d42094
            omega
          have d42309 : (x (-10) 9).toNat = 0 := by
            have r42310 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e42311 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
            have e42312 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
            have e42313 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
            have e42314 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
            have e42315 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
            have e42316 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
            have b42317 := hb (x (-16) 7)
            have b42318 := hb (x (-15) 6)
            have b42319 := hb (x (-14) 5)
            have b42320 := hb (x (-13) 4)
            have b42321 := hb (x (-12) 11)
            have b42322 := hb (x (-11) 10)
            have b42323 := hb (x (-10) 9)
            have b42324 := hb (x (-9) 8)
            clear * - r42310 e42311 e42312 e42313 e42314 e42315 e42316 b42317 b42318 b42319 b42320 b42321 b42322 b42323 b42324 d42298
            omega
          have d42325 : (x (-10) 9 && x (-10) 14).toNat = 0 := by
            have r42326 := hand1 (x (-10) 9) (x (-10) 14)
            have b42327 := hb (x (-10) 9)
            have b42328 := hb (x (-10) 9 && x (-10) 14)
            clear * - r42326 b42327 b42328 d42309
            omega
          have d42329 : (x (-11) 10).toNat = 1 := by
            have r42330 : 1 ≤ (x (-1) 5).toNat + (x (-2) 1 && x (-2) 6).toNat + (x (-3) 2 && x (-3) 7).toNat + (x (-4) 3 && x (-4) 8).toNat + (x (-5) 4 && x (-5) 9).toNat + (x (-6) 5 && x (-6) 10).toNat + (x (-7) 6 && x (-7) 11).toNat + (x (-8) 7 && x (-8) 12).toNat + (x (-9) 8 && x (-9) 13).toNat + (x (-10) 9 && x (-10) 14).toNat + (x (-11) 10).toNat := by have q := hcov5 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b42331 := hb (x (-11) 10)
            have b42332 := hb (x (-1) 5)
            have b42333 := hb (x (-2) 1 && x (-2) 6)
            have b42334 := hb (x (-3) 2 && x (-3) 7)
            have b42335 := hb (x (-4) 3 && x (-4) 8)
            have b42336 := hb (x (-5) 4 && x (-5) 9)
            have b42337 := hb (x (-6) 5 && x (-6) 10)
            have b42338 := hb (x (-7) 6 && x (-7) 11)
            have b42339 := hb (x (-8) 7 && x (-8) 12)
            have b42340 := hb (x (-9) 8 && x (-9) 13)
            have b42341 := hb (x (-10) 9 && x (-10) 14)
            clear * - r42330 b42331 b42332 b42333 b42334 b42335 b42336 b42337 b42338 b42339 b42340 b42341 g6 g59 g60 d42118 d41788 d41816 d41840 d42098 d41989 d42325
            omega
          have r42342 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e42343 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
          have e42344 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
          have e42345 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
          have e42346 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
          have e42347 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
          have e42348 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
          have b42349 := hb (x (-16) 7)
          have b42350 := hb (x (-15) 6)
          have b42351 := hb (x (-14) 5)
          have b42352 := hb (x (-13) 4)
          have b42353 := hb (x (-12) 11)
          have b42354 := hb (x (-11) 10)
          have b42355 := hb (x (-10) 9)
          have b42356 := hb (x (-9) 8)
          linarith only [r42342, e42343, e42344, e42345, e42346, e42347, e42348, b42349, b42350, b42351, b42352, b42353, b42354, b42355, b42356, d42298, d42309, d42329]
      · have f42357 : (x 1 7).toNat = 1 := by rw [h40994]; rfl
        have d42358 : (x 8 8).toNat = 0 := by
          have r42359 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e42360 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e42361 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e42362 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e42363 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e42364 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e42365 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have b42366 := hb (x 1 7)
          have b42367 := hb (x 2 6)
          have b42368 := hb (x 3 5)
          have b42369 := hb (x 4 4)
          have b42370 := hb (x 5 11)
          have b42371 := hb (x 6 10)
          have b42372 := hb (x 7 9)
          have b42373 := hb (x 8 8)
          clear * - r42359 e42360 e42361 e42362 e42363 e42364 e42365 b42366 b42367 b42368 b42369 b42370 b42371 b42372 b42373 g33 g28 f42357
          omega
        have d42374 : (x 7 9).toNat = 0 := by
          have r42375 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e42376 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e42377 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e42378 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e42379 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e42380 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e42381 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have b42382 := hb (x 1 7)
          have b42383 := hb (x 2 6)
          have b42384 := hb (x 3 5)
          have b42385 := hb (x 4 4)
          have b42386 := hb (x 5 11)
          have b42387 := hb (x 6 10)
          have b42388 := hb (x 7 9)
          have b42389 := hb (x 8 8)
          clear * - r42375 e42376 e42377 e42378 e42379 e42380 e42381 b42382 b42383 b42384 b42385 b42386 b42387 b42388 b42389 d42358 g33 g28 f42357
          omega
        have d42390 : (x 6 10).toNat = 0 := by
          have r42391 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e42392 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e42393 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e42394 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e42395 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e42396 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e42397 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have b42398 := hb (x 1 7)
          have b42399 := hb (x 2 6)
          have b42400 := hb (x 3 5)
          have b42401 := hb (x 4 4)
          have b42402 := hb (x 5 11)
          have b42403 := hb (x 6 10)
          have b42404 := hb (x 7 9)
          have b42405 := hb (x 8 8)
          clear * - r42391 e42392 e42393 e42394 e42395 e42396 e42397 b42398 b42399 b42400 b42401 b42402 b42403 b42404 b42405 d42358 d42374 g33 g28 f42357
          omega
        have d42406 : (x 6 1 && x 6 10).toNat = 0 := by
          have r42407 := hand2 (x 6 1) (x 6 10)
          have b42408 := hb (x 6 10)
          have b42409 := hb (x 6 1 && x 6 10)
          clear * - r42407 b42408 b42409 d42390
          omega
        have d42410 : (x 5 2 && x 5 11).toNat = 1 := by
          have r42411 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b42412 := hb (x 1 6)
          have b42413 := hb (x 7 9)
          have b42414 := hb (x 6 1 && x 6 10)
          have b42415 := hb (x 5 2 && x 5 11)
          have b42416 := hb (x 4 3 && x 4 12)
          have b42417 := hb (x 3 4 && x 3 13)
          have b42418 := hb (x 2 5 && x 2 14)
          clear * - r42411 b42412 b42413 b42414 b42415 b42416 b42417 b42418 d42374 d42406 g105 g106 g107 g21
          omega
        have d42419 : (x 5 11).toNat = 1 := by
          have r42420 := hand2 (x 5 2) (x 5 11)
          have b42421 := hb (x 5 11)
          have b42422 := hb (x 5 2 && x 5 11)
          clear * - r42420 b42421 b42422 d42410
          omega
        have r42423 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e42424 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e42425 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e42426 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e42427 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e42428 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e42429 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b42430 := hb (x 1 7)
        have b42431 := hb (x 2 6)
        have b42432 := hb (x 3 5)
        have b42433 := hb (x 4 4)
        have b42434 := hb (x 5 11)
        have b42435 := hb (x 6 10)
        have b42436 := hb (x 7 9)
        have b42437 := hb (x 8 8)
        linarith only [r42423, e42424, e42425, e42426, e42427, e42428, e42429, b42430, b42431, b42432, b42433, b42434, b42435, b42436, b42437, d42358, d42374, d42390, d42419, g33, g28, f42357]

theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt1110111 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 7).toNat = 0)
    (g1 : (x (-3) 11).toNat = 0)
    (g2 : (x (-2) 6).toNat = 0)
    (g3 : (x (-2) 10).toNat = 0)
    (g4 : (x (-2) 11).toNat = 0)
    (g5 : (x (-1) 3).toNat = 0)
    (g6 : (x (-1) 5).toNat = 0)
    (g7 : (x (-1) 9).toNat = 0)
    (g8 : (x (-1) 10).toNat = 0)
    (g9 : (x (-1) 11).toNat = 0)
    (g10 : (x (-1) 13).toNat = 0)
    (g11 : (x 0 2).toNat = 1)
    (g12 : (x 0 4).toNat = 1)
    (g13 : (x 0 5).toNat = 1)
    (g14 : (x 0 7).toNat = 0)
    (g15 : (x 0 12).toNat = 1)
    (g16 : (x 0 13).toNat = 1)
    (g17 : (x 1 1).toNat = 1)
    (g18 : (x 1 3).toNat = 0)
    (g19 : (x 1 4).toNat = 0)
    (g20 : (x 1 5).toNat = 0)
    (g21 : (x 1 6).toNat = 0)
    (g22 : (x 1 10).toNat = 0)
    (g23 : (x 1 11).toNat = 0)
    (g24 : (x 1 12).toNat = 0)
    (g25 : (x 2 2).toNat = 0)
    (g26 : (x 2 4).toNat = 0)
    (g27 : (x 2 5).toNat = 0)
    (g28 : (x 2 6).toNat = 0)
    (g29 : (x 2 10).toNat = 0)
    (g30 : (x 3 1).toNat = 1)
    (g31 : (x 3 4).toNat = 0)
    (g32 : (x 3 9).toNat = 0)
    (g33 : (x 4 4).toNat = 0)
    (g34 : (x 4 6).toNat = 0)
    (g35 : (x 4 8).toNat = 0)
    (g36 : (x 4 10).toNat = 0)
    (g37 : (x 4 3 && x 4 4).toNat = 0)
    (g38 : (x 3 4 && x 3 5).toNat = 0)
    (g39 : (x 2 5 && x 2 6).toNat = 0)
    (g40 : (x 1 6 && x 1 7).toNat = 0)
    (g41 : (x 0 7 && x 0 8).toNat = 0)
    (g42 : (x (-1) 8 && x (-1) 9).toNat = 0)
    (g43 : (x (-2) 9 && x (-2) 10).toNat = 0)
    (g44 : (x (-3) 10 && x (-3) 11).toNat = 0)
    (g45 : (x 2 2 && x 2 6).toNat = 0)
    (g46 : (x 1 3 && x 1 7).toNat = 0)
    (g47 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g48 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g49 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g50 : (x 3 4 && x 3 8).toNat = 0)
    (g51 : (x 2 5 && x 2 9).toNat = 0)
    (g52 : (x 1 6 && x 1 10).toNat = 0)
    (g53 : (x 0 7 && x 0 11).toNat = 0)
    (g54 : (x 4 4 && x 4 8).toNat = 0)
    (g55 : (x 3 5 && x 3 9).toNat = 0)
    (g56 : (x 2 6 && x 2 10).toNat = 0)
    (g57 : (x 1 7 && x 1 11).toNat = 0)
    (g58 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g59 : (x (-2) 1 && x (-2) 6).toNat = 0)
    (g60 : (x (-3) 2 && x (-3) 7).toNat = 0)
    (g61 : (x 1 1 && x 1 6).toNat = 0)
    (g62 : (x 0 2 && x 0 7).toNat = 0)
    (g63 : (x (-1) 3 && x (-1) 8).toNat = 0)
    (g64 : (x 4 2 && x 4 7).toNat = 0)
    (g65 : (x 2 4 && x 2 9).toNat = 0)
    (g66 : (x 1 5 && x 1 10).toNat = 0)
    (g67 : (x 4 3 && x 4 8).toNat = 0)
    (g68 : (x 3 4 && x 3 9).toNat = 0)
    (g69 : (x 2 5 && x 2 10).toNat = 0)
    (g70 : (x 1 6 && x 1 11).toNat = 0)
    (g71 : (x 0 7 && x 0 12).toNat = 0)
    (g72 : (x (-1) 8 && x (-1) 13).toNat = 0)
    (g73 : (x (-1) 1 && x (-1) 7).toNat = 0)
    (g74 : (x (-2) 2 && x (-2) 8).toNat = 0)
    (g75 : (x (-3) 3 && x (-3) 9).toNat = 0)
    (g76 : (x 0 1 && x 0 7).toNat = 0)
    (g77 : (x (-1) 2 && x (-1) 8).toNat = 0)
    (g78 : (x (-2) 3 && x (-2) 9).toNat = 0)
    (g79 : (x (-1) 3 && x (-1) 9).toNat = 0)
    (g80 : (x (-2) 4 && x (-2) 10).toNat = 0)
    (g81 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g82 : (x 3 4 && x 3 10).toNat = 0)
    (g83 : (x 2 5 && x 2 11).toNat = 0)
    (g84 : (x 1 6 && x 1 12).toNat = 0)
    (g85 : (x 0 7 && x 0 13).toNat = 0)
    (g86 : (x 4 4 && x 4 10).toNat = 0)
    (g87 : (x 2 6 && x 2 12).toNat = 0)
    (g88 : (x 1 7 && x 1 13).toNat = 0)
    (g89 : (x (-1) 1 && x (-1) 8).toNat = 0)
    (g90 : (x (-2) 2 && x (-2) 9).toNat = 0)
    (g91 : (x (-3) 3 && x (-3) 10).toNat = 0)
    (g92 : (x 4 2 && x 4 9).toNat = 0)
    (g93 : (x 2 4 && x 2 11).toNat = 0)
    (g94 : (x 1 5 && x 1 12).toNat = 0)
    (g95 : (x 4 3 && x 4 10).toNat = 0)
    (g96 : (x 3 4 && x 3 11).toNat = 0)
    (g97 : (x 2 5 && x 2 12).toNat = 0)
    (g98 : (x 1 6 && x 1 13).toNat = 0)
    (g99 : (x 0 7 && x 0 14).toNat = 0)
    (g100 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g101 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g102 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g103 : (x (-2) 2 && x (-2) 11).toNat = 0)
    (g104 : (x (-3) 3 && x (-3) 12).toNat = 0)
    (g105 : (x 4 3 && x 4 12).toNat = 0)
    (g106 : (x 3 4 && x 3 13).toNat = 0)
    (g107 : (x 2 5 && x 2 14).toNat = 0)
    (g108 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g109 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g110 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g111 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g112 : (x (-1) 2 && x (-1) 12).toNat = 0)
    (g113 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g114 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g115 : (x (-2) 2 && x (-2) 13).toNat = 0)
    (g116 : (x (-3) 3 && x (-3) 14).toNat = 0)
    (g117 : (x 4 1 && x 4 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt1110111_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83 g84 g85 g86 g87 g88 g89 g90 g91 g92 g93 g94 g95 g96 g97 g98 g99 g100 g101 g102 g103 g104 g105 g106 g107 g108 g109 g110 g111 g112 g113 g114 g115 g116 g117
