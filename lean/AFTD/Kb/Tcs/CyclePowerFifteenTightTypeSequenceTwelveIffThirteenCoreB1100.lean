import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b1100

Topic: combinatorics   Node: fa03b6de595f

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core: under the layer-free tight-cover constraints for k = 15 and 110 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b1100_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-2) 3).toNat = 0)
    (g1 : (x (-2) 11).toNat = 0)
    (g2 : (x (-1) 2).toNat = 0)
    (g3 : (x (-1) 5).toNat = 0)
    (g4 : (x (-1) 9).toNat = 0)
    (g5 : (x (-1) 10).toNat = 0)
    (g6 : (x (-1) 11).toNat = 0)
    (g7 : (x (-1) 13).toNat = 0)
    (g8 : (x 0 1).toNat = 1)
    (g9 : (x 0 3).toNat = 1)
    (g10 : (x 0 4).toNat = 0)
    (g11 : (x 0 8).toNat = 0)
    (g12 : (x 0 12).toNat = 0)
    (g13 : (x 0 13).toNat = 1)
    (g14 : (x 0 14).toNat = 1)
    (g15 : (x 1 2).toNat = 0)
    (g16 : (x 1 4).toNat = 0)
    (g17 : (x 1 5).toNat = 0)
    (g18 : (x 1 6).toNat = 0)
    (g19 : (x 1 9).toNat = 0)
    (g20 : (x 1 10).toNat = 0)
    (g21 : (x 1 12).toNat = 0)
    (g22 : (x 1 13).toNat = 0)
    (g23 : (x 2 1).toNat = 1)
    (g24 : (x 2 5).toNat = 0)
    (g25 : (x 2 12).toNat = 0)
    (g26 : (x 3 2).toNat = 0)
    (g27 : (x 3 5).toNat = 0)
    (g28 : (x 3 6).toNat = 0)
    (g29 : (x 3 9).toNat = 0)
    (g30 : (x 3 10).toNat = 0)
    (g31 : (x 3 11).toNat = 0)
    (g32 : (x 3 13).toNat = 0)
    (g33 : (x 4 10).toNat = 1)
    (g34 : (x 5 2).toNat = 0)
    (g35 : (x 5 6).toNat = 0)
    (g36 : (x 5 9).toNat = 0)
    (g37 : (x 6 5).toNat = 0)
    (g38 : (x 6 8).toNat = 0)
    (g39 : (x 6 9).toNat = 0)
    (g40 : (x 7 4).toNat = 0)
    (g41 : (x 6 6 && x 6 8).toNat = 0)
    (g42 : (x 5 7 && x 5 9).toNat = 0)
    (g43 : (x 3 9 && x 3 11).toNat = 0)
    (g44 : (x 2 10 && x 2 12).toNat = 0)
    (g45 : (x 1 11 && x 1 13).toNat = 0)
    (g46 : (x 0 12 && x 0 14).toNat = 0)
    (g47 : (x 0 1 && x 0 4).toNat = 0)
    (g48 : (x (-1) 2 && x (-1) 5).toNat = 0)
    (g49 : (x (-2) 3 && x (-2) 6).toNat = 0)
    (g50 : (x 1 2 && x 1 7).toNat = 0)
    (g51 : (x (-1) 4 && x (-1) 9).toNat = 0)
    (g52 : (x 1 2 && x 1 8).toNat = 0)
    (g53 : (x (-1) 4 && x (-1) 10).toNat = 0)
    (g54 : (x (-2) 5 && x (-2) 11).toNat = 0)
    (g55 : (x 3 2 && x 3 8).toNat = 0)
    (g56 : (x 1 4 && x 1 10).toNat = 0)
    (g57 : (x 0 5 && x 0 11).toNat = 0)
    (g58 : (x 6 2 && x 6 8).toNat = 0)
    (g59 : (x 5 3 && x 5 9).toNat = 0)
    (g60 : (x 3 5 && x 3 11).toNat = 0)
    (g61 : (x 2 6 && x 2 12).toNat = 0)
    (g62 : (x 1 7 && x 1 13).toNat = 0)
    (g63 : (x 7 4 && x 7 10).toNat = 0)
    (g64 : (x 6 5 && x 6 11).toNat = 0)
    (g65 : (x 5 6 && x 5 12).toNat = 0)
    (g66 : (x 3 8 && x 3 14).toNat = 0)
    (g67 : (x 7 8 && x 7 14).toNat = 0)
    (g68 : (x 3 1 && x 3 8).toNat = 0)
    (g69 : (x 1 3 && x 1 10).toNat = 0)
    (g70 : (x 0 4 && x 0 11).toNat = 0)
    (g71 : (x (-1) 5 && x (-1) 12).toNat = 0)
    (g72 : (x 7 1 && x 7 8).toNat = 0)
    (g73 : (x 6 2 && x 6 9).toNat = 0)
    (g74 : (x 5 3 && x 5 10).toNat = 0)
    (g75 : (x 3 5 && x 3 12).toNat = 0)
    (g76 : (x 2 6 && x 2 13).toNat = 0)
    (g77 : (x 1 7 && x 1 14).toNat = 0)
    (g78 : (x (-1) 2 && x (-1) 11).toNat = 0)
    (g79 : (x (-2) 3 && x (-2) 12).toNat = 0)
    (g80 : (x 1 2 && x 1 11).toNat = 0)
    (g81 : (x 0 3 && x 0 12).toNat = 0)
    (g82 : (x (-1) 4 && x (-1) 13).toNat = 0)
    (g83 : (x 3 1 && x 3 10).toNat = 0)
    (g84 : (x 1 3 && x 1 12).toNat = 0)
    (g85 : (x 0 4 && x 0 13).toNat = 0)
    (g86 : (x (-1) 5 && x (-1) 14).toNat = 0)
    (g87 : (x 5 2 && x 5 11).toNat = 0)
    (g88 : (x 3 4 && x 3 13).toNat = 0)
    (g89 : (x 2 5 && x 2 14).toNat = 0)
    (g90 : (x 7 4 && x 7 13).toNat = 0)
    (g91 : (x 6 5 && x 6 14).toNat = 0)
    (g92 : (x (-1) 2 && x (-1) 12).toNat = 0)
    (g93 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g94 : (x 1 1 && x 1 11).toNat = 0)
    (g95 : (x 0 2 && x 0 12).toNat = 0)
    (g96 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g97 : (x 3 3 && x 3 13).toNat = 0)
    (g98 : (x 2 4 && x 2 14).toNat = 0)
    (g99 : (x 5 2 && x 5 12).toNat = 0)
    (g100 : (x 3 4 && x 3 14).toNat = 0)
    (g101 : (x 7 4 && x 7 14).toNat = 0)
    (g102 : (x 0 1 && x 0 12).toNat = 0)
    (g103 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g104 : (x (-2) 3 && x (-2) 14).toNat = 0)
    (g105 : (x 3 2 && x 3 13).toNat = 0)
    (g106 : (x 7 1 && x 7 12).toNat = 0)
    (g107 : (x 6 2 && x 6 13).toNat = 0)
    (g108 : (x 5 3 && x 5 14).toNat = 0)
    (g109 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d19300 : (x 0 8 && x 0 14).toNat = 0 := by
    have r19301 := hand1 (x 0 8) (x 0 14)
    have b19302 := hb (x 0 8)
    have b19303 := hb (x 0 8 && x 0 14)
    clear * - r19301 b19302 b19303 g11
    omega
  have d19304 : (x 0 3 && x 0 8).toNat = 0 := by
    have r19305 := hand2 (x 0 3) (x 0 8)
    have b19306 := hb (x 0 8)
    have b19307 := hb (x 0 3 && x 0 8)
    clear * - r19305 b19306 b19307 g11
    omega
  cases h19308 : x 0 9
  · have f19309 : (x 0 9).toNat = 0 := by rw [h19308]; rfl
    have d19310 : (x 0 3 && x 0 9).toNat = 0 := by
      have r19311 := hand2 (x 0 3) (x 0 9)
      have b19312 := hb (x 0 9)
      have b19313 := hb (x 0 3 && x 0 9)
      clear * - r19311 b19312 b19313 f19309
      omega
    cases h19314 : x 0 10
    · have f19315 : (x 0 10).toNat = 0 := by rw [h19314]; rfl
      have d19316 : (x 0 1 && x 0 10).toNat = 0 := by
        have r19317 := hand2 (x 0 1) (x 0 10)
        have b19318 := hb (x 0 10)
        have b19319 := hb (x 0 1 && x 0 10)
        clear * - r19317 b19318 b19319 f19315
        omega
      cases h19320 : x 0 11
      · have f19321 : (x 0 11).toNat = 0 := by rw [h19320]; rfl
        have d19322 : (x 0 1 && x 0 11).toNat = 0 := by
          have r19323 := hand2 (x 0 1) (x 0 11)
          have b19324 := hb (x 0 11)
          have b19325 := hb (x 0 1 && x 0 11)
          clear * - r19323 b19324 b19325 f19321
          omega
        cases h19326 : x 1 3
        · have f19327 : (x 1 3).toNat = 0 := by rw [h19326]; rfl
          have d19328 : (x 1 11).toNat = 0 := by
            have r19329 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
            have b19330 := hb (x 1 3)
            have b19331 := hb (x 1 11)
            clear * - r19329 b19330 b19331 f19327
            omega
          have d19332 : (x (-3) 4).toNat = 1 := by
            have r19333 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b19334 := hb (x (-3) 4)
            have b19335 := hb (x 1 11)
            have b19336 := hb (x 0 1 && x 0 12)
            have b19337 := hb (x (-1) 2 && x (-1) 13)
            have b19338 := hb (x (-2) 3 && x (-2) 14)
            clear * - r19333 b19334 b19335 b19336 b19337 b19338 d19328 g102 g103 g104
            omega
          have d19339 : (x (-3) 12).toNat = 1 := by
            have r19340 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
            have b19341 := hb (x (-3) 4)
            have b19342 := hb (x (-3) 12)
            clear * - r19340 b19341 b19342 d19332
            omega
          have d19343 : (x (-4) 13).toNat = 0 := by
            have r19344 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e19345 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
            have e19346 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
            have b19347 := hb (x (-6) 3)
            have b19348 := hb (x (-5) 2)
            have b19349 := hb (x (-4) 13)
            have b19350 := hb (x (-3) 12)
            clear * - r19344 e19345 e19346 b19347 b19348 b19349 b19350 d19339
            omega
          have d19351 : (x (-4) 5).toNat = 0 := by
            have r19352 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
            have b19353 := hb (x (-4) 5)
            have b19354 := hb (x (-4) 13)
            clear * - r19352 b19353 b19354 d19343
            omega
          have d19355 : (x (-4) 5 && x (-4) 8).toNat = 0 := by
            have r19356 := hand1 (x (-4) 5) (x (-4) 8)
            have b19357 := hb (x (-4) 5)
            have b19358 := hb (x (-4) 5 && x (-4) 8)
            clear * - r19356 b19357 b19358 d19351
            omega
          have d19359 : (x (-5) 2).toNat = 0 := by
            have r19360 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e19361 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
            have e19362 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
            have b19363 := hb (x (-6) 3)
            have b19364 := hb (x (-5) 2)
            have b19365 := hb (x (-4) 13)
            have b19366 := hb (x (-3) 12)
            clear * - r19360 e19361 e19362 b19363 b19364 b19365 b19366 d19339 d19343
            omega
          have d19367 : (x (-3) 4 && x (-3) 14).toNat = 1 := by
            have r19368 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b19369 := hb (x (-4) 5)
            have b19370 := hb (x 1 10)
            have b19371 := hb (x 0 1 && x 0 11)
            have b19372 := hb (x (-1) 2 && x (-1) 12)
            have b19373 := hb (x (-2) 3 && x (-2) 13)
            have b19374 := hb (x (-3) 4 && x (-3) 14)
            clear * - r19368 b19369 b19370 b19371 b19372 b19373 b19374 g20 d19322 g92 g93 d19351
            omega
          have d19375 : (x (-3) 14).toNat = 1 := by
            have r19376 := hand2 (x (-3) 4) (x (-3) 14)
            have b19377 := hb (x (-3) 14)
            have b19378 := hb (x (-3) 4 && x (-3) 14)
            clear * - r19376 b19377 b19378 d19367
            omega
          have d19379 : (x (-4) 1).toNat = 0 := by
            have r19380 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b19381 := hb (x (-4) 1)
            have b19382 := hb (x (-3) 14)
            clear * - r19380 b19381 b19382 d19375
            omega
          have d19383 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
            have r19384 := hand1 (x (-4) 1) (x (-4) 14)
            have b19385 := hb (x (-4) 1)
            have b19386 := hb (x (-4) 1 && x (-4) 14)
            clear * - r19384 b19385 b19386 d19379
            omega
          have d19387 : (x (-3) 13).toNat = 1 := by
            have r19388 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b19389 := hb (x (-5) 2)
            have b19390 := hb (x (-3) 13)
            have b19391 := hb (x (-4) 1 && x (-4) 14)
            clear * - r19388 b19389 b19390 b19391 d19383 d19359
            omega
          have d19392 : (x (-3) 1).toNat = 1 := by
            have r19393 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
            have b19394 := hb (x (-3) 1)
            have b19395 := hb (x (-3) 13)
            clear * - r19393 b19394 b19395 d19387
            omega
          have d19396 : (x (-2) 14).toNat = 0 := by
            have r19397 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b19398 := hb (x (-3) 1)
            have b19399 := hb (x (-2) 14)
            clear * - r19397 b19398 b19399 d19392
            omega
          have d19400 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
            have r19401 := hand2 (x (-2) 1) (x (-2) 14)
            have b19402 := hb (x (-2) 14)
            have b19403 := hb (x (-2) 1 && x (-2) 14)
            clear * - r19401 b19402 b19403 d19396
            omega
          have d19404 : (x (-3) 2).toNat = 1 := by
            have r19405 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b19406 := hb (x (-3) 2)
            have b19407 := hb (x (-1) 13)
            have b19408 := hb (x (-2) 1 && x (-2) 14)
            clear * - r19405 b19406 b19407 b19408 g7 d19400
            omega
          have d19409 : (x (-1) 12).toNat = 0 := by
            have r19410 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e19411 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e19412 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b19413 := hb (x (-4) 3)
            have b19414 := hb (x (-3) 2)
            have b19415 := hb (x (-2) 13)
            have b19416 := hb (x (-1) 12)
            clear * - r19410 e19411 e19412 b19413 b19414 b19415 b19416 d19404
            omega
          have d19417 : (x (-1) 4).toNat = 0 := by
            have r19418 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
            have b19419 := hb (x (-1) 4)
            have b19420 := hb (x (-1) 12)
            clear * - r19418 b19419 b19420 d19409
            omega
          have d19421 : (x (-2) 13).toNat = 0 := by
            have r19422 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e19423 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e19424 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b19425 := hb (x (-4) 3)
            have b19426 := hb (x (-3) 2)
            have b19427 := hb (x (-2) 13)
            have b19428 := hb (x (-1) 12)
            clear * - r19422 e19423 e19424 b19425 b19426 b19427 b19428 d19409 d19404
            omega
          have d19429 : (x (-2) 5).toNat = 0 := by
            have r19430 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
            have b19431 := hb (x (-2) 5)
            have b19432 := hb (x (-2) 13)
            clear * - r19430 b19431 b19432 d19421
            omega
          have d19433 : (x (-2) 5 && x (-2) 14).toNat = 0 := by
            have r19434 := hand1 (x (-2) 5) (x (-2) 14)
            have b19435 := hb (x (-2) 5)
            have b19436 := hb (x (-2) 5 && x (-2) 14)
            clear * - r19434 b19435 b19436 d19429
            omega
          have d19437 : (x (-2) 5 && x (-2) 10).toNat = 0 := by
            have r19438 := hand1 (x (-2) 5) (x (-2) 10)
            have b19439 := hb (x (-2) 5)
            have b19440 := hb (x (-2) 5 && x (-2) 10)
            clear * - r19438 b19439 b19440 d19429
            omega
          have d19441 : (x (-2) 6).toNat = 0 := by
            have r19442 : (x (-2) 6).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp6 (-2))
            have b19443 := hb (x (-2) 6)
            have b19444 := hb (x (-2) 14)
            clear * - r19442 b19443 b19444 d19396
            omega
          have d19445 : (x 1 8).toNat = 0 := by
            have r19446 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e19447 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
            have e19448 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
            have e19449 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
            have e19450 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
            have e19451 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
            have e19452 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
            have b19453 := hb (x (-6) 7)
            have b19454 := hb (x (-5) 6)
            have b19455 := hb (x (-4) 5)
            have b19456 := hb (x (-3) 4)
            have b19457 := hb (x (-2) 11)
            have b19458 := hb (x (-1) 10)
            have b19459 := hb (x 0 9)
            have b19460 := hb (x 1 8)
            clear * - r19446 e19447 e19448 e19449 e19450 e19451 e19452 b19453 b19454 b19455 b19456 b19457 b19458 b19459 b19460 f19309 g5 g1 d19332 d19351
            omega
          have d19461 : (x (-5) 6).toNat = 0 := by
            have r19462 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e19463 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
            have e19464 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
            have e19465 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
            have e19466 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
            have e19467 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
            have e19468 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
            have b19469 := hb (x (-6) 7)
            have b19470 := hb (x (-5) 6)
            have b19471 := hb (x (-4) 5)
            have b19472 := hb (x (-3) 4)
            have b19473 := hb (x (-2) 11)
            have b19474 := hb (x (-1) 10)
            have b19475 := hb (x 0 9)
            have b19476 := hb (x 1 8)
            clear * - r19462 e19463 e19464 e19465 e19466 e19467 e19468 b19469 b19470 b19471 b19472 b19473 b19474 b19475 b19476 d19445 f19309 g5 g1 d19332 d19351
            omega
          have d19477 : (x (-5) 6 && x (-5) 9).toNat = 0 := by
            have r19478 := hand1 (x (-5) 6) (x (-5) 9)
            have b19479 := hb (x (-5) 6)
            have b19480 := hb (x (-5) 6 && x (-5) 9)
            clear * - r19478 b19479 b19480 d19461
            omega
          have d19481 : (x (-6) 7).toNat = 0 := by
            have r19482 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e19483 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
            have e19484 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
            have e19485 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
            have e19486 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
            have e19487 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
            have e19488 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
            have b19489 := hb (x (-6) 7)
            have b19490 := hb (x (-5) 6)
            have b19491 := hb (x (-4) 5)
            have b19492 := hb (x (-3) 4)
            have b19493 := hb (x (-2) 11)
            have b19494 := hb (x (-1) 10)
            have b19495 := hb (x 0 9)
            have b19496 := hb (x 1 8)
            clear * - r19482 e19483 e19484 e19485 e19486 e19487 e19488 b19489 b19490 b19491 b19492 b19493 b19494 b19495 b19496 d19445 f19309 g5 g1 d19332 d19351 d19461
            omega
          have d19497 : (x (-6) 7 && x (-6) 10).toNat = 0 := by
            have r19498 := hand1 (x (-6) 7) (x (-6) 10)
            have b19499 := hb (x (-6) 7)
            have b19500 := hb (x (-6) 7 && x (-6) 10)
            clear * - r19498 b19499 b19500 d19481
            omega
          have r19501 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r19502 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r19503 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r19504 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r19505 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19506 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
          have e19507 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
          have e19508 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
          have e19509 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
          have e19510 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
          have e19511 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
          have r19512 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19513 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e19514 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e19515 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e19516 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e19517 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e19518 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have r19519 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19520 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
          have e19521 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
          have e19522 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
          have e19523 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
          have e19524 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
          have e19525 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
          have r19526 : (x (-12) 12).toNat + (x (-13) 1 && x (-13) 13).toNat + (x (-14) 2 && x (-14) 14).toNat + (x (-15) 3).toNat = 1 := by have q := hd12 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19527 : (x (-13) 1 && x (-13) 13).toNat = (x (-13) 13).toNat := handr _ _ (fun h => hp13 (-13) (h))
          have e19528 : (x (-14) 2 && x (-14) 14).toNat = (x (-14) 2).toNat := handl _ _ (fun h => hp2 (-14) (h))
          have r19529 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19530 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e19531 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have r19532 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19533 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e19534 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have r19535 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19536 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
          have e19537 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
          have r19538 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r19539 : (x 12 14).toNat + (x 11 1).toNat = 1 := by have q := hd14 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r19540 : 1 ≤ (x 12 2).toNat + (x 11 1 && x 11 3).toNat + (x 10 2 && x 10 4).toNat + (x 9 3 && x 9 5).toNat + (x 8 4 && x 8 6).toNat + (x 7 5 && x 7 7).toNat + (x 6 6 && x 6 8).toNat + (x 5 7 && x 5 9).toNat + (x 4 8 && x 4 10).toNat + (x 3 9 && x 3 11).toNat + (x 2 10 && x 2 12).toNat + (x 1 11 && x 1 13).toNat + (x 0 12 && x 0 14).toNat + (x (-1) 13).toNat := by have q := hcov2 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r19541 : 1 ≤ (x 1 3).toNat + (x 0 1 && x 0 4).toNat + (x (-1) 2 && x (-1) 5).toNat + (x (-2) 3 && x (-2) 6).toNat + (x (-3) 4 && x (-3) 7).toNat + (x (-4) 5 && x (-4) 8).toNat + (x (-5) 6 && x (-5) 9).toNat + (x (-6) 7 && x (-6) 10).toNat + (x (-7) 8 && x (-7) 11).toNat + (x (-8) 9 && x (-8) 12).toNat + (x (-9) 10 && x (-9) 13).toNat + (x (-10) 11 && x (-10) 14).toNat + (x (-11) 12).toNat := by have q := hcov3 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r19542 : 1 ≤ (x 3 5).toNat + (x 2 1 && x 2 6).toNat + (x 1 2 && x 1 7).toNat + (x 0 3 && x 0 8).toNat + (x (-1) 4 && x (-1) 9).toNat + (x (-2) 5 && x (-2) 10).toNat + (x (-3) 6 && x (-3) 11).toNat + (x (-4) 7 && x (-4) 12).toNat + (x (-5) 8 && x (-5) 13).toNat + (x (-6) 9 && x (-6) 14).toNat + (x (-7) 10).toNat := by have q := hcov5 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r19543 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r19544 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r19545 : 1 ≤ (x 11 9).toNat + (x 10 1 && x 10 10).toNat + (x 9 2 && x 9 11).toNat + (x 8 3 && x 8 12).toNat + (x 7 4 && x 7 13).toNat + (x 6 5 && x 6 14).toNat + (x 5 6).toNat := by have q := hcov9 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r19546 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := by have q := hcov11 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r19547 : 1 ≤ (x (-12) 13).toNat + (x (-13) 1 && x (-13) 14).toNat + (x (-14) 2).toNat := by have q := hcov13 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r19548 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r19549 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r19550 : (x (-12) 4).toNat ≤ (x (-12) 12).toNat := himp _ _ (hp4 (-12))
          have r19551 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
          have r19552 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
          have r19553 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
          have r19554 := hand2 (x 11 1) (x 11 3)
          have r19555 := hand2 (x 10 2) (x 10 4)
          have r19556 := hand2 (x 9 3) (x 9 5)
          have r19557 := hand2 (x 8 4) (x 8 6)
          have r19558 := hand2 (x 7 5) (x 7 7)
          have r19559 := hand1 (x 4 8) (x 4 10)
          have r19560 := hand2 (x (-3) 4) (x (-3) 7)
          have r19561 := hand1 (x (-7) 8) (x (-7) 11)
          have r19562 := hand1 (x (-8) 9) (x (-8) 12)
          have r19563 := hand1 (x (-9) 10) (x (-9) 13)
          have r19564 := hand1 (x (-10) 11) (x (-10) 14)
          have r19565 := hand2 (x 2 1) (x 2 6)
          have r19566 := hand1 (x (-3) 6) (x (-3) 11)
          have r19567 := hand1 (x (-4) 7) (x (-4) 12)
          have r19568 := hand1 (x (-5) 8) (x (-5) 13)
          have r19569 := hand1 (x (-6) 9) (x (-6) 14)
          have r19570 := hand2 (x 2 1) (x 2 10)
          have r19571 := hand2 (x 6 1) (x 6 10)
          have r19572 := hand2 (x 4 3) (x 4 12)
          have r19573 := hand2 (x 10 1) (x 10 10)
          have r19574 := hand2 (x 9 2) (x 9 11)
          have r19575 := hand1 (x 8 3) (x 8 12)
          have r19576 := hand2 (x (-9) 1) (x (-9) 12)
          have r19577 := hand2 (x (-10) 2) (x (-10) 13)
          have r19578 := hand2 (x (-11) 3) (x (-11) 14)
          have r19579 := hand2 (x (-13) 1) (x (-13) 14)
          have r19580 := hand1 (x 10 1) (x 10 14)
          have r19581 := hand2 (x 12 1) (x 12 14)
          linarith only [r19501, r19502, r19503, r19504, r19505, e19506, e19507, e19508, e19509, e19510, e19511, r19512, e19513, e19514, e19515, e19516, e19517, e19518, r19519, e19520, e19521, e19522, e19523, e19524, e19525, r19526, e19527, e19528, r19529, e19530, e19531, r19532, e19533, e19534, r19535, e19536, e19537, r19538, r19539, r19540, r19541, r19542, r19543, r19544, r19545, r19546, r19547, r19548, r19549, r19550, r19551, r19552, r19553, r19554, r19555, r19556, r19557, r19558, r19559, r19560, r19561, r19562, r19563, r19564, r19565, r19566, r19567, r19568, r19569, r19570, r19571, r19572, r19573, r19574, r19575, r19576, r19577, r19578, r19579, r19580, r19581, d19481, d19461, d19351, d19332, g0, d19429, d19441, d19396, g2, d19417, g3, g7, g8, g9, g10, g12, g14, g15, f19327, g18, d19328, g22, g23, g25, g27, g29, g31, g32, g33, g35, g36, g38, g41, g42, g43, g44, g45, g46, g47, g48, g49, d19355, d19477, d19497, g50, d19304, g51, d19437, g80, g81, g82, d19433, g87, g88, g89, g90, g91]
        · have f19729 : (x 1 3).toNat = 1 := by rw [h19326]; rfl
          have d19730 : (x 4 12).toNat = 0 := by
            have r19731 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e19732 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e19733 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b19734 := hb (x 1 3)
            have b19735 := hb (x 2 2)
            have b19736 := hb (x 3 13)
            have b19737 := hb (x 4 12)
            clear * - r19731 e19732 e19733 b19734 b19735 b19736 b19737 g32 f19729
            omega
          have d19738 : (x 4 1 && x 4 12).toNat = 0 := by
            have r19739 := hand2 (x 4 1) (x 4 12)
            have b19740 := hb (x 4 12)
            have b19741 := hb (x 4 1 && x 4 12)
            clear * - r19739 b19740 b19741 d19730
            omega
          have d19742 : (x 4 4).toNat = 0 := by
            have r19743 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
            have b19744 := hb (x 4 4)
            have b19745 := hb (x 4 12)
            clear * - r19743 b19744 b19745 d19730
            omega
          have d19746 : (x 2 2).toNat = 0 := by
            have r19747 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e19748 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e19749 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b19750 := hb (x 1 3)
            have b19751 := hb (x 2 2)
            have b19752 := hb (x 3 13)
            have b19753 := hb (x 4 12)
            clear * - r19747 e19748 e19749 b19750 b19751 b19752 b19753 d19730 g32 f19729
            omega
          have d19754 : (x 4 13).toNat = 1 := by
            have r19755 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b19756 := hb (x 2 2)
            have b19757 := hb (x 4 13)
            have b19758 := hb (x 3 1 && x 3 14)
            clear * - r19755 b19756 b19757 b19758 g109 d19746
            omega
          have d19759 : (x 5 12).toNat = 0 := by
            have r19760 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e19761 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e19762 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b19763 := hb (x 2 3)
            have b19764 := hb (x 3 2)
            have b19765 := hb (x 4 13)
            have b19766 := hb (x 5 12)
            clear * - r19760 e19761 e19762 b19763 b19764 b19765 b19766 d19754 g26
            omega
          have d19767 : (x 5 4).toNat = 0 := by
            have r19768 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
            have b19769 := hb (x 5 4)
            have b19770 := hb (x 5 12)
            clear * - r19768 b19769 b19770 d19759
            omega
          have d19771 : (x 2 3).toNat = 0 := by
            have r19772 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e19773 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e19774 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b19775 := hb (x 2 3)
            have b19776 := hb (x 3 2)
            have b19777 := hb (x 4 13)
            have b19778 := hb (x 5 12)
            clear * - r19772 e19773 e19774 b19775 b19776 b19777 b19778 d19759 d19754 g26
            omega
          have d19779 : (x 2 3 && x 2 14).toNat = 0 := by
            have r19780 := hand1 (x 2 3) (x 2 14)
            have b19781 := hb (x 2 3)
            have b19782 := hb (x 2 3 && x 2 14)
            clear * - r19780 b19781 b19782 d19771
            omega
          have d19783 : (x 8 11).toNat = 1 := by
            have r19784 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b19785 := hb (x 4 4)
            have b19786 := hb (x 8 11)
            have b19787 := hb (x 7 1 && x 7 12)
            have b19788 := hb (x 6 2 && x 6 13)
            have b19789 := hb (x 5 3 && x 5 14)
            clear * - r19784 b19785 b19786 b19787 b19788 b19789 g106 g107 g108 d19742
            omega
          have d19790 : (x 8 3).toNat = 1 := by
            have r19791 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
            have b19792 := hb (x 8 3)
            have b19793 := hb (x 8 11)
            clear * - r19791 b19792 b19793 d19783
            omega
          have d19794 : (x 11 12).toNat = 0 := by
            have r19795 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e19796 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
            have e19797 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
            have b19798 := hb (x 8 3)
            have b19799 := hb (x 9 2)
            have b19800 := hb (x 10 13)
            have b19801 := hb (x 11 12)
            clear * - r19795 e19796 e19797 b19798 b19799 b19800 b19801 d19790
            omega
          have d19802 : (x 11 1 && x 11 12).toNat = 0 := by
            have r19803 := hand2 (x 11 1) (x 11 12)
            have b19804 := hb (x 11 12)
            have b19805 := hb (x 11 1 && x 11 12)
            clear * - r19803 b19804 b19805 d19794
            omega
          have d19806 : (x 10 13).toNat = 0 := by
            have r19807 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e19808 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
            have e19809 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
            have b19810 := hb (x 8 3)
            have b19811 := hb (x 9 2)
            have b19812 := hb (x 10 13)
            have b19813 := hb (x 11 12)
            clear * - r19807 e19808 e19809 b19810 b19811 b19812 b19813 d19794 d19790
            omega
          have d19814 : (x 10 2 && x 10 13).toNat = 0 := by
            have r19815 := hand2 (x 10 2) (x 10 13)
            have b19816 := hb (x 10 13)
            have b19817 := hb (x 10 2 && x 10 13)
            clear * - r19815 b19816 b19817 d19806
            omega
          have d19818 : (x 9 2).toNat = 0 := by
            have r19819 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e19820 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
            have e19821 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
            have b19822 := hb (x 8 3)
            have b19823 := hb (x 9 2)
            have b19824 := hb (x 10 13)
            have b19825 := hb (x 11 12)
            clear * - r19819 e19820 e19821 b19822 b19823 b19824 b19825 d19794 d19806 d19790
            omega
          have d19826 : (x 5 11).toNat = 1 := by
            have r19827 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b19828 := hb (x 1 4)
            have b19829 := hb (x 5 11)
            have b19830 := hb (x 4 1 && x 4 12)
            have b19831 := hb (x 3 2 && x 3 13)
            have b19832 := hb (x 2 3 && x 2 14)
            clear * - r19827 b19828 b19829 b19830 b19831 b19832 d19738 g105 d19779 g16
            omega
          have d19833 : (x 5 3).toNat = 1 := by
            have r19834 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
            have b19835 := hb (x 5 3)
            have b19836 := hb (x 5 11)
            clear * - r19834 b19835 b19836 d19826
            omega
          have d19837 : (x 8 12).toNat = 0 := by
            have r19838 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e19839 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
            have e19840 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
            have b19841 := hb (x 5 3)
            have b19842 := hb (x 6 2)
            have b19843 := hb (x 7 13)
            have b19844 := hb (x 8 12)
            clear * - r19838 e19839 e19840 b19841 b19842 b19843 b19844 d19833
            omega
          have d19845 : (x 8 1 && x 8 12).toNat = 0 := by
            have r19846 := hand2 (x 8 1) (x 8 12)
            have b19847 := hb (x 8 12)
            have b19848 := hb (x 8 1 && x 8 12)
            clear * - r19846 b19847 b19848 d19837
            omega
          have d19849 : (x 8 4).toNat = 0 := by
            have r19850 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
            have b19851 := hb (x 8 4)
            have b19852 := hb (x 8 12)
            clear * - r19850 b19851 b19852 d19837
            omega
          have d19853 : (x 7 13).toNat = 0 := by
            have r19854 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e19855 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
            have e19856 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
            have b19857 := hb (x 5 3)
            have b19858 := hb (x 6 2)
            have b19859 := hb (x 7 13)
            have b19860 := hb (x 8 12)
            clear * - r19854 e19855 e19856 b19857 b19858 b19859 b19860 d19837 d19833
            omega
          have d19861 : (x 7 2 && x 7 13).toNat = 0 := by
            have r19862 := hand2 (x 7 2) (x 7 13)
            have b19863 := hb (x 7 13)
            have b19864 := hb (x 7 2 && x 7 13)
            clear * - r19862 b19863 b19864 d19853
            omega
          have d19865 : (x 6 1 && x 6 14).toNat = 1 := by
            have r19866 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b19867 := hb (x 5 2)
            have b19868 := hb (x 7 13)
            have b19869 := hb (x 6 1 && x 6 14)
            clear * - r19866 b19867 b19868 b19869 d19853 g34
            omega
          have d19870 : (x 6 1).toNat = 1 := by
            have r19871 := hand1 (x 6 1) (x 6 14)
            have b19872 := hb (x 6 1)
            have b19873 := hb (x 6 1 && x 6 14)
            clear * - r19871 b19872 b19873 d19865
            omega
          have d19874 : (x 7 14).toNat = 0 := by
            have r19875 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b19876 := hb (x 6 1)
            have b19877 := hb (x 7 14)
            clear * - r19875 b19876 b19877 d19870
            omega
          have d19878 : (x 7 1 && x 7 14).toNat = 0 := by
            have r19879 := hand2 (x 7 1) (x 7 14)
            have b19880 := hb (x 7 14)
            have b19881 := hb (x 7 1 && x 7 14)
            clear * - r19879 b19880 b19881 d19874
            omega
          have d19882 : (x 7 2).toNat = 0 := by
            have r19883 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
            have b19884 := hb (x 7 2)
            have b19885 := hb (x 7 14)
            clear * - r19883 b19884 b19885 d19874
            omega
          have d19886 : (x 6 2).toNat = 0 := by
            have r19887 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e19888 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
            have e19889 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
            have b19890 := hb (x 5 3)
            have b19891 := hb (x 6 2)
            have b19892 := hb (x 7 13)
            have b19893 := hb (x 8 12)
            clear * - r19887 e19888 e19889 b19890 b19891 b19892 b19893 d19837 d19853 d19833
            omega
          have d19894 : (x 8 13).toNat = 1 := by
            have r19895 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b19896 := hb (x 6 2)
            have b19897 := hb (x 8 13)
            have b19898 := hb (x 7 1 && x 7 14)
            clear * - r19895 b19896 b19897 b19898 d19878 d19886
            omega
          have d19899 : (x 8 1).toNat = 1 := by
            have r19900 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
            have b19901 := hb (x 8 1)
            have b19902 := hb (x 8 13)
            clear * - r19900 b19901 b19902 d19894
            omega
          have d19903 : (x 9 14).toNat = 0 := by
            have r19904 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b19905 := hb (x 8 1)
            have b19906 := hb (x 9 14)
            clear * - r19904 b19905 b19906 d19899
            omega
          have d19907 : (x 9 3 && x 9 14).toNat = 0 := by
            have r19908 := hand2 (x 9 3) (x 9 14)
            have b19909 := hb (x 9 14)
            have b19910 := hb (x 9 3 && x 9 14)
            clear * - r19908 b19909 b19910 d19903
            omega
          have d19911 : (x 12 11).toNat = 1 := by
            have r19912 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b19913 := hb (x 8 4)
            have b19914 := hb (x 12 11)
            have b19915 := hb (x 11 1 && x 11 12)
            have b19916 := hb (x 10 2 && x 10 13)
            have b19917 := hb (x 9 3 && x 9 14)
            clear * - r19912 b19913 b19914 b19915 b19916 b19917 d19802 d19814 d19907 d19849
            omega
          have d19918 : (x 12 3).toNat = 1 := by
            have r19919 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
            have b19920 := hb (x 12 3)
            have b19921 := hb (x 12 11)
            clear * - r19919 b19920 b19921 d19911
            omega
          have d19922 : (x 15 12).toNat = 0 := by
            have r19923 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e19924 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
            have e19925 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
            have b19926 := hb (x 12 3)
            have b19927 := hb (x 13 2)
            have b19928 := hb (x 14 13)
            have b19929 := hb (x 15 12)
            clear * - r19923 e19924 e19925 b19926 b19927 b19928 b19929 d19918
            omega
          have d19930 : (x 15 1 && x 15 12).toNat = 0 := by
            have r19931 := hand2 (x 15 1) (x 15 12)
            have b19932 := hb (x 15 12)
            have b19933 := hb (x 15 1 && x 15 12)
            clear * - r19931 b19932 b19933 d19922
            omega
          have d19934 : (x 14 13).toNat = 0 := by
            have r19935 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e19936 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
            have e19937 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
            have b19938 := hb (x 12 3)
            have b19939 := hb (x 13 2)
            have b19940 := hb (x 14 13)
            have b19941 := hb (x 15 12)
            clear * - r19935 e19936 e19937 b19938 b19939 b19940 b19941 d19922 d19918
            omega
          have d19942 : (x 14 2 && x 14 13).toNat = 0 := by
            have r19943 := hand2 (x 14 2) (x 14 13)
            have b19944 := hb (x 14 13)
            have b19945 := hb (x 14 2 && x 14 13)
            clear * - r19943 b19944 b19945 d19934
            omega
          have d19946 : (x 13 2).toNat = 0 := by
            have r19947 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e19948 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
            have e19949 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
            have b19950 := hb (x 12 3)
            have b19951 := hb (x 13 2)
            have b19952 := hb (x 14 13)
            have b19953 := hb (x 15 12)
            clear * - r19947 e19948 e19949 b19950 b19951 b19952 b19953 d19922 d19934 d19918
            omega
          have d19954 : (x 9 12).toNat = 0 := by
            have r19955 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e19956 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
            have e19957 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
            have b19958 := hb (x 6 3)
            have b19959 := hb (x 7 2)
            have b19960 := hb (x 8 13)
            have b19961 := hb (x 9 12)
            clear * - r19955 e19956 e19957 b19958 b19959 b19960 b19961 d19894 d19882
            omega
          have d19962 : (x 9 4).toNat = 0 := by
            have r19963 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
            have b19964 := hb (x 9 4)
            have b19965 := hb (x 9 12)
            clear * - r19963 b19964 b19965 d19954
            omega
          have d19966 : (x 6 3).toNat = 0 := by
            have r19967 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e19968 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
            have e19969 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
            have b19970 := hb (x 6 3)
            have b19971 := hb (x 7 2)
            have b19972 := hb (x 8 13)
            have b19973 := hb (x 9 12)
            clear * - r19967 e19968 e19969 b19970 b19971 b19972 b19973 d19954 d19894 d19882
            omega
          have d19974 : (x 6 3 && x 6 14).toNat = 0 := by
            have r19975 := hand1 (x 6 3) (x 6 14)
            have b19976 := hb (x 6 3)
            have b19977 := hb (x 6 3 && x 6 14)
            clear * - r19975 b19976 b19977 d19966
            omega
          have d19978 : (x 9 11).toNat = 1 := by
            have r19979 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b19980 := hb (x 5 4)
            have b19981 := hb (x 9 11)
            have b19982 := hb (x 8 1 && x 8 12)
            have b19983 := hb (x 7 2 && x 7 13)
            have b19984 := hb (x 6 3 && x 6 14)
            clear * - r19979 b19980 b19981 b19982 b19983 b19984 d19845 d19861 d19974 d19767
            omega
          have d19985 : (x 9 3).toNat = 1 := by
            have r19986 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
            have b19987 := hb (x 9 3)
            have b19988 := hb (x 9 11)
            clear * - r19986 b19987 b19988 d19978
            omega
          have d19989 : (x 12 12).toNat = 0 := by
            have r19990 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e19991 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
            have e19992 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
            have b19993 := hb (x 9 3)
            have b19994 := hb (x 10 2)
            have b19995 := hb (x 11 13)
            have b19996 := hb (x 12 12)
            clear * - r19990 e19991 e19992 b19993 b19994 b19995 b19996 d19985
            omega
          have d19997 : (x 12 1 && x 12 12).toNat = 0 := by
            have r19998 := hand2 (x 12 1) (x 12 12)
            have b19999 := hb (x 12 12)
            have b20000 := hb (x 12 1 && x 12 12)
            clear * - r19998 b19999 b20000 d19989
            omega
          have d20001 : (x 12 4).toNat = 0 := by
            have r20002 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
            have b20003 := hb (x 12 4)
            have b20004 := hb (x 12 12)
            clear * - r20002 b20003 b20004 d19989
            omega
          have d20005 : (x 11 13).toNat = 0 := by
            have r20006 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e20007 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
            have e20008 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
            have b20009 := hb (x 9 3)
            have b20010 := hb (x 10 2)
            have b20011 := hb (x 11 13)
            have b20012 := hb (x 12 12)
            clear * - r20006 e20007 e20008 b20009 b20010 b20011 b20012 d19989 d19985
            omega
          have d20013 : (x 11 2 && x 11 13).toNat = 0 := by
            have r20014 := hand2 (x 11 2) (x 11 13)
            have b20015 := hb (x 11 13)
            have b20016 := hb (x 11 2 && x 11 13)
            clear * - r20014 b20015 b20016 d20005
            omega
          have d20017 : (x 10 1 && x 10 14).toNat = 1 := by
            have r20018 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b20019 := hb (x 9 2)
            have b20020 := hb (x 11 13)
            have b20021 := hb (x 10 1 && x 10 14)
            clear * - r20018 b20019 b20020 b20021 d20005 d19818
            omega
          have d20022 : (x 10 1).toNat = 1 := by
            have r20023 := hand1 (x 10 1) (x 10 14)
            have b20024 := hb (x 10 1)
            have b20025 := hb (x 10 1 && x 10 14)
            clear * - r20023 b20024 b20025 d20017
            omega
          have d20026 : (x 11 14).toNat = 0 := by
            have r20027 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b20028 := hb (x 10 1)
            have b20029 := hb (x 11 14)
            clear * - r20027 b20028 b20029 d20022
            omega
          have d20030 : (x 11 1 && x 11 14).toNat = 0 := by
            have r20031 := hand2 (x 11 1) (x 11 14)
            have b20032 := hb (x 11 14)
            have b20033 := hb (x 11 1 && x 11 14)
            clear * - r20031 b20032 b20033 d20026
            omega
          have d20034 : (x 11 2).toNat = 0 := by
            have r20035 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
            have b20036 := hb (x 11 2)
            have b20037 := hb (x 11 14)
            clear * - r20035 b20036 b20037 d20026
            omega
          have d20038 : (x 10 2).toNat = 0 := by
            have r20039 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e20040 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
            have e20041 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
            have b20042 := hb (x 9 3)
            have b20043 := hb (x 10 2)
            have b20044 := hb (x 11 13)
            have b20045 := hb (x 12 12)
            clear * - r20039 e20040 e20041 b20042 b20043 b20044 b20045 d19989 d20005 d19985
            omega
          have d20046 : (x 12 13).toNat = 1 := by
            have r20047 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b20048 := hb (x 10 2)
            have b20049 := hb (x 12 13)
            have b20050 := hb (x 11 1 && x 11 14)
            clear * - r20047 b20048 b20049 b20050 d20030 d20038
            omega
          have d20051 : (x 12 1).toNat = 1 := by
            have r20052 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
            have b20053 := hb (x 12 1)
            have b20054 := hb (x 12 13)
            clear * - r20052 b20053 b20054 d20046
            omega
          have d20055 : (x 13 14).toNat = 0 := by
            have r20056 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b20057 := hb (x 12 1)
            have b20058 := hb (x 13 14)
            clear * - r20056 b20057 b20058 d20051
            omega
          have d20059 : (x 13 1 && x 13 14).toNat = 0 := by
            have r20060 := hand2 (x 13 1) (x 13 14)
            have b20061 := hb (x 13 14)
            have b20062 := hb (x 13 1 && x 13 14)
            clear * - r20060 b20061 b20062 d20055
            omega
          have d20063 : (x 12 2).toNat = 1 := by
            have r20064 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b20065 := hb (x 12 2)
            have b20066 := hb (x 14 13)
            have b20067 := hb (x 13 1 && x 13 14)
            clear * - r20064 b20065 b20066 b20067 d19934 d20059
            omega
          have d20068 : (x 14 12).toNat = 0 := by
            have r20069 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e20070 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
            have e20071 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
            have b20072 := hb (x 11 3)
            have b20073 := hb (x 12 2)
            have b20074 := hb (x 13 13)
            have b20075 := hb (x 14 12)
            clear * - r20069 e20070 e20071 b20072 b20073 b20074 b20075 d20063
            omega
          have d20076 : (x 14 4).toNat = 0 := by
            have r20077 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
            have b20078 := hb (x 14 4)
            have b20079 := hb (x 14 12)
            clear * - r20077 b20078 b20079 d20068
            omega
          have d20080 : (x 14 4 && x 14 14).toNat = 0 := by
            have r20081 := hand1 (x 14 4) (x 14 14)
            have b20082 := hb (x 14 4)
            have b20083 := hb (x 14 4 && x 14 14)
            clear * - r20081 b20082 b20083 d20076
            omega
          have d20084 : (x 13 13).toNat = 0 := by
            have r20085 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e20086 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
            have e20087 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
            have b20088 := hb (x 11 3)
            have b20089 := hb (x 12 2)
            have b20090 := hb (x 13 13)
            have b20091 := hb (x 14 12)
            clear * - r20085 e20086 e20087 b20088 b20089 b20090 b20091 d20068 d20063
            omega
          have d20092 : (x 13 5).toNat = 0 := by
            have r20093 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
            have b20094 := hb (x 13 5)
            have b20095 := hb (x 13 13)
            clear * - r20093 b20094 b20095 d20084
            omega
          have d20096 : (x 13 3 && x 13 14).toNat = 0 := by
            have r20097 := hand2 (x 13 3) (x 13 14)
            have b20098 := hb (x 13 14)
            have b20099 := hb (x 13 3 && x 13 14)
            clear * - r20097 b20098 b20099 d20055
            omega
          have d20100 : (x 16 11).toNat = 1 := by
            have r20101 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b20102 := hb (x 12 4)
            have b20103 := hb (x 16 11)
            have b20104 := hb (x 15 1 && x 15 12)
            have b20105 := hb (x 14 2 && x 14 13)
            have b20106 := hb (x 13 3 && x 13 14)
            clear * - r20101 b20102 b20103 b20104 b20105 b20106 d19930 d19942 d20096 d20001
            omega
          have d20107 : (x 16 3).toNat = 1 := by
            have r20108 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
            have b20109 := hb (x 16 3)
            have b20110 := hb (x 16 11)
            clear * - r20108 b20109 b20110 d20100
            omega
          have d20111 : (x 19 12).toNat = 0 := by
            have r20112 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e20113 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
            have e20114 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
            have b20115 := hb (x 16 3)
            have b20116 := hb (x 17 2)
            have b20117 := hb (x 18 13)
            have b20118 := hb (x 19 12)
            clear * - r20112 e20113 e20114 b20115 b20116 b20117 b20118 d20107
            omega
          have d20119 : (x 18 13).toNat = 0 := by
            have r20120 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e20121 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
            have e20122 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
            have b20123 := hb (x 16 3)
            have b20124 := hb (x 17 2)
            have b20125 := hb (x 18 13)
            have b20126 := hb (x 19 12)
            clear * - r20120 e20121 e20122 b20123 b20124 b20125 b20126 d20111 d20107
            omega
          have d20127 : (x 17 2).toNat = 0 := by
            have r20128 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e20129 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
            have e20130 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
            have b20131 := hb (x 16 3)
            have b20132 := hb (x 17 2)
            have b20133 := hb (x 18 13)
            have b20134 := hb (x 19 12)
            clear * - r20128 e20129 e20130 b20131 b20132 b20133 b20134 d20111 d20119 d20107
            omega
          have d20135 : (x 13 12).toNat = 0 := by
            have r20136 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e20137 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
            have e20138 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
            have b20139 := hb (x 10 3)
            have b20140 := hb (x 11 2)
            have b20141 := hb (x 12 13)
            have b20142 := hb (x 13 12)
            clear * - r20136 e20137 e20138 b20139 b20140 b20141 b20142 d20046 d20034
            omega
          have d20143 : (x 13 4).toNat = 0 := by
            have r20144 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
            have b20145 := hb (x 13 4)
            have b20146 := hb (x 13 12)
            clear * - r20144 b20145 b20146 d20135
            omega
          have d20147 : (x 10 3).toNat = 0 := by
            have r20148 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e20149 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
            have e20150 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
            have b20151 := hb (x 10 3)
            have b20152 := hb (x 11 2)
            have b20153 := hb (x 12 13)
            have b20154 := hb (x 13 12)
            clear * - r20148 e20149 e20150 b20151 b20152 b20153 b20154 d20135 d20046 d20034
            omega
          have d20155 : (x 10 3 && x 10 14).toNat = 0 := by
            have r20156 := hand1 (x 10 3) (x 10 14)
            have b20157 := hb (x 10 3)
            have b20158 := hb (x 10 3 && x 10 14)
            clear * - r20156 b20157 b20158 d20147
            omega
          have d20159 : (x 13 11).toNat = 1 := by
            have r20160 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b20161 := hb (x 9 4)
            have b20162 := hb (x 13 11)
            have b20163 := hb (x 12 1 && x 12 12)
            have b20164 := hb (x 11 2 && x 11 13)
            have b20165 := hb (x 10 3 && x 10 14)
            clear * - r20160 b20161 b20162 b20163 b20164 b20165 d19997 d20013 d20155 d19962
            omega
          have d20166 : (x 13 3).toNat = 1 := by
            have r20167 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
            have b20168 := hb (x 13 3)
            have b20169 := hb (x 13 11)
            clear * - r20167 b20168 b20169 d20159
            omega
          have d20170 : (x 16 12).toNat = 0 := by
            have r20171 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e20172 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
            have e20173 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
            have b20174 := hb (x 13 3)
            have b20175 := hb (x 14 2)
            have b20176 := hb (x 15 13)
            have b20177 := hb (x 16 12)
            clear * - r20171 e20172 e20173 b20174 b20175 b20176 b20177 d20166
            omega
          have d20178 : (x 16 1 && x 16 12).toNat = 0 := by
            have r20179 := hand2 (x 16 1) (x 16 12)
            have b20180 := hb (x 16 12)
            have b20181 := hb (x 16 1 && x 16 12)
            clear * - r20179 b20180 b20181 d20170
            omega
          have d20182 : (x 16 2 && x 16 12).toNat = 0 := by
            have r20183 := hand2 (x 16 2) (x 16 12)
            have b20184 := hb (x 16 12)
            have b20185 := hb (x 16 2 && x 16 12)
            clear * - r20183 b20184 b20185 d20170
            omega
          have d20186 : (x 15 13).toNat = 0 := by
            have r20187 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e20188 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
            have e20189 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
            have b20190 := hb (x 13 3)
            have b20191 := hb (x 14 2)
            have b20192 := hb (x 15 13)
            have b20193 := hb (x 16 12)
            clear * - r20187 e20188 e20189 b20190 b20191 b20192 b20193 d20170 d20166
            omega
          have d20194 : (x 15 2 && x 15 13).toNat = 0 := by
            have r20195 := hand2 (x 15 2) (x 15 13)
            have b20196 := hb (x 15 13)
            have b20197 := hb (x 15 2 && x 15 13)
            clear * - r20195 b20196 b20197 d20186
            omega
          have d20198 : (x 15 3 && x 15 13).toNat = 0 := by
            have r20199 := hand2 (x 15 3) (x 15 13)
            have b20200 := hb (x 15 13)
            have b20201 := hb (x 15 3 && x 15 13)
            clear * - r20199 b20200 b20201 d20186
            omega
          have d20202 : (x 14 1 && x 14 14).toNat = 1 := by
            have r20203 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b20204 := hb (x 13 2)
            have b20205 := hb (x 15 13)
            have b20206 := hb (x 14 1 && x 14 14)
            clear * - r20203 b20204 b20205 b20206 d20186 d19946
            omega
          have d20207 : (x 14 1).toNat = 1 := by
            have r20208 := hand1 (x 14 1) (x 14 14)
            have b20209 := hb (x 14 1)
            have b20210 := hb (x 14 1 && x 14 14)
            clear * - r20208 b20209 b20210 d20202
            omega
          have d20211 : (x 15 14).toNat = 0 := by
            have r20212 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b20213 := hb (x 14 1)
            have b20214 := hb (x 15 14)
            clear * - r20212 b20213 b20214 d20207
            omega
          have d20215 : (x 15 1 && x 15 14).toNat = 0 := by
            have r20216 := hand2 (x 15 1) (x 15 14)
            have b20217 := hb (x 15 14)
            have b20218 := hb (x 15 1 && x 15 14)
            clear * - r20216 b20217 b20218 d20211
            omega
          have d20219 : (x 15 2).toNat = 0 := by
            have r20220 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
            have b20221 := hb (x 15 2)
            have b20222 := hb (x 15 14)
            clear * - r20220 b20221 b20222 d20211
            omega
          have d20223 : (x 14 2).toNat = 0 := by
            have r20224 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e20225 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
            have e20226 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
            have b20227 := hb (x 13 3)
            have b20228 := hb (x 14 2)
            have b20229 := hb (x 15 13)
            have b20230 := hb (x 16 12)
            clear * - r20224 e20225 e20226 b20227 b20228 b20229 b20230 d20170 d20186 d20166
            omega
          have d20231 : (x 16 13).toNat = 1 := by
            have r20232 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b20233 := hb (x 14 2)
            have b20234 := hb (x 16 13)
            have b20235 := hb (x 15 1 && x 15 14)
            clear * - r20232 b20233 b20234 b20235 d20215 d20223
            omega
          have d20236 : (x 17 12).toNat = 0 := by
            have r20237 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e20238 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
            have e20239 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
            have b20240 := hb (x 14 3)
            have b20241 := hb (x 15 2)
            have b20242 := hb (x 16 13)
            have b20243 := hb (x 17 12)
            clear * - r20237 e20238 e20239 b20240 b20241 b20242 b20243 d20231 d20219
            omega
          have d20244 : (x 14 3).toNat = 0 := by
            have r20245 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e20246 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
            have e20247 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
            have b20248 := hb (x 14 3)
            have b20249 := hb (x 15 2)
            have b20250 := hb (x 16 13)
            have b20251 := hb (x 17 12)
            clear * - r20245 e20246 e20247 b20248 b20249 b20250 b20251 d20236 d20231 d20219
            omega
          have d20252 : (x 14 3 && x 14 14).toNat = 0 := by
            have r20253 := hand1 (x 14 3) (x 14 14)
            have b20254 := hb (x 14 3)
            have b20255 := hb (x 14 3 && x 14 14)
            clear * - r20253 b20254 b20255 d20244
            omega
          have d20256 : (x 17 11).toNat = 1 := by
            have r20257 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b20258 := hb (x 13 4)
            have b20259 := hb (x 17 11)
            have b20260 := hb (x 16 1 && x 16 12)
            have b20261 := hb (x 15 2 && x 15 13)
            have b20262 := hb (x 14 3 && x 14 14)
            clear * - r20257 b20258 b20259 b20260 b20261 b20262 d20178 d20194 d20252 d20143
            omega
          have d20263 : (x 17 3).toNat = 1 := by
            have r20264 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
            have b20265 := hb (x 17 3)
            have b20266 := hb (x 17 11)
            clear * - r20264 b20265 b20266 d20256
            omega
          have d20267 : (x 20 12).toNat = 0 := by
            have r20268 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e20269 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
            have e20270 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
            have b20271 := hb (x 17 3)
            have b20272 := hb (x 18 2)
            have b20273 := hb (x 19 13)
            have b20274 := hb (x 20 12)
            clear * - r20268 e20269 e20270 b20271 b20272 b20273 b20274 d20263
            omega
          have d20275 : (x 19 13).toNat = 0 := by
            have r20276 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e20277 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
            have e20278 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
            have b20279 := hb (x 17 3)
            have b20280 := hb (x 18 2)
            have b20281 := hb (x 19 13)
            have b20282 := hb (x 20 12)
            clear * - r20276 e20277 e20278 b20279 b20280 b20281 b20282 d20267 d20263
            omega
          have d20283 : (x 18 1 && x 18 14).toNat = 1 := by
            have r20284 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b20285 := hb (x 17 2)
            have b20286 := hb (x 19 13)
            have b20287 := hb (x 18 1 && x 18 14)
            clear * - r20284 b20285 b20286 b20287 d20275 d20127
            omega
          have d20288 : (x 18 14).toNat = 1 := by
            have r20289 := hand2 (x 18 1) (x 18 14)
            have b20290 := hb (x 18 14)
            have b20291 := hb (x 18 1 && x 18 14)
            clear * - r20289 b20290 b20291 d20283
            omega
          have d20292 : (x 17 1).toNat = 0 := by
            have r20293 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b20294 := hb (x 17 1)
            have b20295 := hb (x 18 14)
            clear * - r20293 b20294 b20295 d20288
            omega
          have d20296 : (x 17 1 && x 17 11).toNat = 0 := by
            have r20297 := hand1 (x 17 1) (x 17 11)
            have b20298 := hb (x 17 1)
            have b20299 := hb (x 17 1 && x 17 11)
            clear * - r20297 b20298 b20299 d20292
            omega
          have d20300 : (x 18 2).toNat = 0 := by
            have r20301 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e20302 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
            have e20303 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
            have b20304 := hb (x 17 3)
            have b20305 := hb (x 18 2)
            have b20306 := hb (x 19 13)
            have b20307 := hb (x 20 12)
            clear * - r20301 e20302 e20303 b20304 b20305 b20306 b20307 d20267 d20275 d20263
            omega
          have d20308 : (x 18 10).toNat = 0 := by
            have r20309 : (x 18 10).toNat ≤ (x 18 2).toNat := himp _ _ (hp10 18)
            have b20310 := hb (x 18 2)
            have b20311 := hb (x 18 10)
            clear * - r20309 b20310 b20311 d20300
            omega
          have r20312 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := by have q := hcov10 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20313 := hb (x 13 5)
          have b20314 := hb (x 18 10)
          have b20315 := hb (x 17 1 && x 17 11)
          have b20316 := hb (x 16 2 && x 16 12)
          have b20317 := hb (x 15 3 && x 15 13)
          have b20318 := hb (x 14 4 && x 14 14)
          linarith only [r20312, b20313, b20314, b20315, b20316, b20317, b20318, d20308, d20296, d20182, d20198, d20080, d20092]
      · have f20319 : (x 0 11).toNat = 1 := by rw [h19320]; rfl
        have d20320 : (x 3 8).toNat = 0 := by
          have r20321 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20322 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e20323 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e20324 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e20325 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e20326 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e20327 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b20328 := hb (x (-4) 7)
          have b20329 := hb (x (-3) 6)
          have b20330 := hb (x (-2) 5)
          have b20331 := hb (x (-1) 4)
          have b20332 := hb (x 0 11)
          have b20333 := hb (x 1 10)
          have b20334 := hb (x 2 9)
          have b20335 := hb (x 3 8)
          clear * - r20321 e20322 e20323 e20324 e20325 e20326 e20327 b20328 b20329 b20330 b20331 b20332 b20333 b20334 b20335 g20 f20319
          omega
        have d20336 : (x 2 9).toNat = 0 := by
          have r20337 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20338 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e20339 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e20340 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e20341 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e20342 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e20343 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b20344 := hb (x (-4) 7)
          have b20345 := hb (x (-3) 6)
          have b20346 := hb (x (-2) 5)
          have b20347 := hb (x (-1) 4)
          have b20348 := hb (x 0 11)
          have b20349 := hb (x 1 10)
          have b20350 := hb (x 2 9)
          have b20351 := hb (x 3 8)
          clear * - r20337 e20338 e20339 e20340 e20341 e20342 e20343 b20344 b20345 b20346 b20347 b20348 b20349 b20350 b20351 d20320 g20 f20319
          omega
        have d20352 : (x 2 2 && x 2 9).toNat = 0 := by
          have r20353 := hand2 (x 2 2) (x 2 9)
          have b20354 := hb (x 2 9)
          have b20355 := hb (x 2 2 && x 2 9)
          clear * - r20353 b20354 b20355 d20336
          omega
        have d20356 : (x 2 3 && x 2 9).toNat = 0 := by
          have r20357 := hand2 (x 2 3) (x 2 9)
          have b20358 := hb (x 2 9)
          have b20359 := hb (x 2 3 && x 2 9)
          clear * - r20357 b20358 b20359 d20336
          omega
        have d20360 : (x (-1) 4).toNat = 0 := by
          have r20361 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20362 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e20363 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e20364 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e20365 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e20366 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e20367 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b20368 := hb (x (-4) 7)
          have b20369 := hb (x (-3) 6)
          have b20370 := hb (x (-2) 5)
          have b20371 := hb (x (-1) 4)
          have b20372 := hb (x 0 11)
          have b20373 := hb (x 1 10)
          have b20374 := hb (x 2 9)
          have b20375 := hb (x 3 8)
          clear * - r20361 e20362 e20363 e20364 e20365 e20366 e20367 b20368 b20369 b20370 b20371 b20372 b20373 b20374 b20375 d20320 d20336 g20 f20319
          omega
        have d20376 : (x (-2) 5).toNat = 0 := by
          have r20377 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20378 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e20379 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e20380 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e20381 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e20382 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e20383 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b20384 := hb (x (-4) 7)
          have b20385 := hb (x (-3) 6)
          have b20386 := hb (x (-2) 5)
          have b20387 := hb (x (-1) 4)
          have b20388 := hb (x 0 11)
          have b20389 := hb (x 1 10)
          have b20390 := hb (x 2 9)
          have b20391 := hb (x 3 8)
          clear * - r20377 e20378 e20379 e20380 e20381 e20382 e20383 b20384 b20385 b20386 b20387 b20388 b20389 b20390 b20391 d20320 d20336 g20 f20319 d20360
          omega
        have d20392 : (x (-2) 5 && x (-2) 14).toNat = 0 := by
          have r20393 := hand1 (x (-2) 5) (x (-2) 14)
          have b20394 := hb (x (-2) 5)
          have b20395 := hb (x (-2) 5 && x (-2) 14)
          clear * - r20393 b20394 b20395 d20376
          omega
        have d20396 : (x (-3) 6).toNat = 0 := by
          have r20397 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20398 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e20399 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e20400 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e20401 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e20402 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e20403 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b20404 := hb (x (-4) 7)
          have b20405 := hb (x (-3) 6)
          have b20406 := hb (x (-2) 5)
          have b20407 := hb (x (-1) 4)
          have b20408 := hb (x 0 11)
          have b20409 := hb (x 1 10)
          have b20410 := hb (x 2 9)
          have b20411 := hb (x 3 8)
          clear * - r20397 e20398 e20399 e20400 e20401 e20402 e20403 b20404 b20405 b20406 b20407 b20408 b20409 b20410 b20411 d20320 d20336 g20 f20319 d20360 d20376
          omega
        have d20412 : (x (-3) 6 && x (-3) 12).toNat = 0 := by
          have r20413 := hand1 (x (-3) 6) (x (-3) 12)
          have b20414 := hb (x (-3) 6)
          have b20415 := hb (x (-3) 6 && x (-3) 12)
          clear * - r20413 b20414 b20415 d20396
          omega
        have d20416 : (x 2 1 && x 2 10).toNat = 1 := by
          have r20417 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20418 := hb (x (-3) 6)
          have b20419 := hb (x 3 9)
          have b20420 := hb (x 2 1 && x 2 10)
          have b20421 := hb (x 1 2 && x 1 11)
          have b20422 := hb (x 0 3 && x 0 12)
          have b20423 := hb (x (-1) 4 && x (-1) 13)
          have b20424 := hb (x (-2) 5 && x (-2) 14)
          clear * - r20417 b20418 b20419 b20420 b20421 b20422 b20423 b20424 g29 g80 g81 g82 d20392 d20396
          omega
        have d20425 : (x 2 10).toNat = 1 := by
          have r20426 := hand2 (x 2 1) (x 2 10)
          have b20427 := hb (x 2 10)
          have b20428 := hb (x 2 1 && x 2 10)
          clear * - r20426 b20427 b20428 d20416
          omega
        have d20429 : (x 2 2).toNat = 1 := by
          have r20430 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
          have b20431 := hb (x 2 2)
          have b20432 := hb (x 2 10)
          clear * - r20430 b20431 b20432 d20425
          omega
        have d20433 : (x 4 12).toNat = 0 := by
          have r20434 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20435 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e20436 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b20437 := hb (x 1 3)
          have b20438 := hb (x 2 2)
          have b20439 := hb (x 3 13)
          have b20440 := hb (x 4 12)
          clear * - r20434 e20435 e20436 b20437 b20438 b20439 b20440 g32 d20429
          omega
        have d20441 : (x 4 1 && x 4 12).toNat = 0 := by
          have r20442 := hand2 (x 4 1) (x 4 12)
          have b20443 := hb (x 4 12)
          have b20444 := hb (x 4 1 && x 4 12)
          clear * - r20442 b20443 b20444 d20433
          omega
        have d20445 : (x 4 4).toNat = 0 := by
          have r20446 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
          have b20447 := hb (x 4 4)
          have b20448 := hb (x 4 12)
          clear * - r20446 b20447 b20448 d20433
          omega
        have d20449 : (x 4 4 && x 4 11).toNat = 0 := by
          have r20450 := hand1 (x 4 4) (x 4 11)
          have b20451 := hb (x 4 4)
          have b20452 := hb (x 4 4 && x 4 11)
          clear * - r20450 b20451 b20452 d20445
          omega
        have d20453 : (x 4 4 && x 4 10).toNat = 0 := by
          have r20454 := hand1 (x 4 4) (x 4 10)
          have b20455 := hb (x 4 4)
          have b20456 := hb (x 4 4 && x 4 10)
          clear * - r20454 b20455 b20456 d20445
          omega
        have d20457 : (x 8 11).toNat = 1 := by
          have r20458 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20459 := hb (x 4 4)
          have b20460 := hb (x 8 11)
          have b20461 := hb (x 7 1 && x 7 12)
          have b20462 := hb (x 6 2 && x 6 13)
          have b20463 := hb (x 5 3 && x 5 14)
          clear * - r20458 b20459 b20460 b20461 b20462 b20463 g106 g107 g108 d20445
          omega
        have d20464 : (x 8 3).toNat = 1 := by
          have r20465 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
          have b20466 := hb (x 8 3)
          have b20467 := hb (x 8 11)
          clear * - r20465 b20466 b20467 d20457
          omega
        have d20468 : (x 11 12).toNat = 0 := by
          have r20469 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20470 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e20471 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have b20472 := hb (x 8 3)
          have b20473 := hb (x 9 2)
          have b20474 := hb (x 10 13)
          have b20475 := hb (x 11 12)
          clear * - r20469 e20470 e20471 b20472 b20473 b20474 b20475 d20464
          omega
        have d20476 : (x 11 1 && x 11 12).toNat = 0 := by
          have r20477 := hand2 (x 11 1) (x 11 12)
          have b20478 := hb (x 11 12)
          have b20479 := hb (x 11 1 && x 11 12)
          clear * - r20477 b20478 b20479 d20468
          omega
        have d20480 : (x 11 2 && x 11 12).toNat = 0 := by
          have r20481 := hand2 (x 11 2) (x 11 12)
          have b20482 := hb (x 11 12)
          have b20483 := hb (x 11 2 && x 11 12)
          clear * - r20481 b20482 b20483 d20468
          omega
        have d20484 : (x 11 4).toNat = 0 := by
          have r20485 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
          have b20486 := hb (x 11 4)
          have b20487 := hb (x 11 12)
          clear * - r20485 b20486 b20487 d20468
          omega
        have d20488 : (x 11 4 && x 11 14).toNat = 0 := by
          have r20489 := hand1 (x 11 4) (x 11 14)
          have b20490 := hb (x 11 4)
          have b20491 := hb (x 11 4 && x 11 14)
          clear * - r20489 b20490 b20491 d20484
          omega
        have d20492 : (x 11 4 && x 11 10).toNat = 0 := by
          have r20493 := hand1 (x 11 4) (x 11 10)
          have b20494 := hb (x 11 4)
          have b20495 := hb (x 11 4 && x 11 10)
          clear * - r20493 b20494 b20495 d20484
          omega
        have d20496 : (x 10 13).toNat = 0 := by
          have r20497 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20498 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e20499 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have b20500 := hb (x 8 3)
          have b20501 := hb (x 9 2)
          have b20502 := hb (x 10 13)
          have b20503 := hb (x 11 12)
          clear * - r20497 e20498 e20499 b20500 b20501 b20502 b20503 d20468 d20464
          omega
        have d20504 : (x 10 2 && x 10 13).toNat = 0 := by
          have r20505 := hand2 (x 10 2) (x 10 13)
          have b20506 := hb (x 10 13)
          have b20507 := hb (x 10 2 && x 10 13)
          clear * - r20505 b20506 b20507 d20496
          omega
        have d20508 : (x 10 3 && x 10 13).toNat = 0 := by
          have r20509 := hand2 (x 10 3) (x 10 13)
          have b20510 := hb (x 10 13)
          have b20511 := hb (x 10 3 && x 10 13)
          clear * - r20509 b20510 b20511 d20496
          omega
        have d20512 : (x 10 5).toNat = 0 := by
          have r20513 : (x 10 5).toNat ≤ (x 10 13).toNat := himp _ _ (hp5 10)
          have b20514 := hb (x 10 5)
          have b20515 := hb (x 10 13)
          clear * - r20513 b20514 b20515 d20496
          omega
        have d20516 : (x 10 5 && x 10 11).toNat = 0 := by
          have r20517 := hand1 (x 10 5) (x 10 11)
          have b20518 := hb (x 10 5)
          have b20519 := hb (x 10 5 && x 10 11)
          clear * - r20517 b20518 b20519 d20512
          omega
        have d20520 : (x 9 2).toNat = 0 := by
          have r20521 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20522 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e20523 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have b20524 := hb (x 8 3)
          have b20525 := hb (x 9 2)
          have b20526 := hb (x 10 13)
          have b20527 := hb (x 11 12)
          clear * - r20521 e20522 e20523 b20524 b20525 b20526 b20527 d20468 d20496 d20464
          omega
        have d20528 : (x 9 2 && x 9 12).toNat = 0 := by
          have r20529 := hand1 (x 9 2) (x 9 12)
          have b20530 := hb (x 9 2)
          have b20531 := hb (x 9 2 && x 9 12)
          clear * - r20529 b20530 b20531 d20520
          omega
        have d20532 : (x 9 2 && x 9 8).toNat = 0 := by
          have r20533 := hand1 (x 9 2) (x 9 8)
          have b20534 := hb (x 9 2)
          have b20535 := hb (x 9 2 && x 9 8)
          clear * - r20533 b20534 b20535 d20520
          omega
        have d20536 : (x 9 10).toNat = 0 := by
          have r20537 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
          have b20538 := hb (x 9 2)
          have b20539 := hb (x 9 10)
          clear * - r20537 b20538 b20539 d20520
          omega
        have d20540 : (x 11 8).toNat = 0 := by
          have r20541 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20542 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
          have e20543 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
          have e20544 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
          have e20545 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
          have e20546 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
          have e20547 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
          have b20548 := hb (x 4 7)
          have b20549 := hb (x 5 6)
          have b20550 := hb (x 6 5)
          have b20551 := hb (x 7 4)
          have b20552 := hb (x 8 11)
          have b20553 := hb (x 9 10)
          have b20554 := hb (x 10 9)
          have b20555 := hb (x 11 8)
          clear * - r20541 e20542 e20543 e20544 e20545 e20546 e20547 b20548 b20549 b20550 b20551 b20552 b20553 b20554 b20555 d20536 d20457 g40 g37 g35
          omega
        have d20556 : (x 10 9).toNat = 0 := by
          have r20557 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20558 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
          have e20559 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
          have e20560 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
          have e20561 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
          have e20562 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
          have e20563 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
          have b20564 := hb (x 4 7)
          have b20565 := hb (x 5 6)
          have b20566 := hb (x 6 5)
          have b20567 := hb (x 7 4)
          have b20568 := hb (x 8 11)
          have b20569 := hb (x 9 10)
          have b20570 := hb (x 10 9)
          have b20571 := hb (x 11 8)
          clear * - r20557 e20558 e20559 e20560 e20561 e20562 e20563 b20564 b20565 b20566 b20567 b20568 b20569 b20570 b20571 d20540 d20536 d20457 g40 g37 g35
          omega
        have d20572 : (x 4 7).toNat = 0 := by
          have r20573 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20574 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
          have e20575 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
          have e20576 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
          have e20577 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
          have e20578 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
          have e20579 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
          have b20580 := hb (x 4 7)
          have b20581 := hb (x 5 6)
          have b20582 := hb (x 6 5)
          have b20583 := hb (x 7 4)
          have b20584 := hb (x 8 11)
          have b20585 := hb (x 9 10)
          have b20586 := hb (x 10 9)
          have b20587 := hb (x 11 8)
          clear * - r20573 e20574 e20575 e20576 e20577 e20578 e20579 b20580 b20581 b20582 b20583 b20584 b20585 b20586 b20587 d20540 d20556 d20536 d20457 g40 g37 g35
          omega
        have d20588 : (x 4 7 && x 4 13).toNat = 0 := by
          have r20589 := hand1 (x 4 7) (x 4 13)
          have b20590 := hb (x 4 7)
          have b20591 := hb (x 4 7 && x 4 13)
          clear * - r20589 b20590 b20591 d20572
          omega
        have d20592 : (x 4 1 && x 4 7).toNat = 0 := by
          have r20593 := hand2 (x 4 1) (x 4 7)
          have b20594 := hb (x 4 7)
          have b20595 := hb (x 4 1 && x 4 7)
          clear * - r20593 b20594 b20595 d20572
          omega
        have d20596 : (x 1 3).toNat = 0 := by
          have r20597 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20598 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e20599 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b20600 := hb (x 1 3)
          have b20601 := hb (x 2 2)
          have b20602 := hb (x 3 13)
          have b20603 := hb (x 4 12)
          clear * - r20597 e20598 e20599 b20600 b20601 b20602 b20603 d20433 g32 d20429
          omega
        have d20604 : (x 1 11).toNat = 0 := by
          have r20605 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
          have b20606 := hb (x 1 3)
          have b20607 := hb (x 1 11)
          clear * - r20605 b20606 b20607 d20596
          omega
        have d20608 : (x (-3) 4).toNat = 1 := by
          have r20609 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20610 := hb (x (-3) 4)
          have b20611 := hb (x 1 11)
          have b20612 := hb (x 0 1 && x 0 12)
          have b20613 := hb (x (-1) 2 && x (-1) 13)
          have b20614 := hb (x (-2) 3 && x (-2) 14)
          clear * - r20609 b20610 b20611 b20612 b20613 b20614 d20604 g102 g103 g104
          omega
        have d20615 : (x (-3) 12).toNat = 1 := by
          have r20616 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
          have b20617 := hb (x (-3) 4)
          have b20618 := hb (x (-3) 12)
          clear * - r20616 b20617 b20618 d20608
          omega
        have d20619 : (x (-4) 13).toNat = 0 := by
          have r20620 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20621 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
          have e20622 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
          have b20623 := hb (x (-6) 3)
          have b20624 := hb (x (-5) 2)
          have b20625 := hb (x (-4) 13)
          have b20626 := hb (x (-3) 12)
          clear * - r20620 e20621 e20622 b20623 b20624 b20625 b20626 d20615
          omega
        have d20627 : (x (-4) 7 && x (-4) 13).toNat = 0 := by
          have r20628 := hand2 (x (-4) 7) (x (-4) 13)
          have b20629 := hb (x (-4) 13)
          have b20630 := hb (x (-4) 7 && x (-4) 13)
          clear * - r20628 b20629 b20630 d20619
          omega
        have d20631 : (x (-4) 5).toNat = 0 := by
          have r20632 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
          have b20633 := hb (x (-4) 5)
          have b20634 := hb (x (-4) 13)
          clear * - r20632 b20633 b20634 d20619
          omega
        have d20635 : (x (-4) 5 && x (-4) 14).toNat = 0 := by
          have r20636 := hand1 (x (-4) 5) (x (-4) 14)
          have b20637 := hb (x (-4) 5)
          have b20638 := hb (x (-4) 5 && x (-4) 14)
          clear * - r20636 b20637 b20638 d20631
          omega
        have d20639 : (x (-5) 2).toNat = 0 := by
          have r20640 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20641 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
          have e20642 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
          have b20643 := hb (x (-6) 3)
          have b20644 := hb (x (-5) 2)
          have b20645 := hb (x (-4) 13)
          have b20646 := hb (x (-3) 12)
          clear * - r20640 e20641 e20642 b20643 b20644 b20645 b20646 d20615 d20619
          omega
        have d20647 : (x (-5) 2 && x (-5) 11).toNat = 0 := by
          have r20648 := hand1 (x (-5) 2) (x (-5) 11)
          have b20649 := hb (x (-5) 2)
          have b20650 := hb (x (-5) 2 && x (-5) 11)
          clear * - r20648 b20649 b20650 d20639
          omega
        have d20651 : (x (-5) 2 && x (-5) 9).toNat = 0 := by
          have r20652 := hand1 (x (-5) 2) (x (-5) 9)
          have b20653 := hb (x (-5) 2)
          have b20654 := hb (x (-5) 2 && x (-5) 9)
          clear * - r20652 b20653 b20654 d20639
          omega
        have d20655 : (x (-5) 2 && x (-5) 8).toNat = 0 := by
          have r20656 := hand1 (x (-5) 2) (x (-5) 8)
          have b20657 := hb (x (-5) 2)
          have b20658 := hb (x (-5) 2 && x (-5) 8)
          clear * - r20656 b20657 b20658 d20639
          omega
        have d20659 : (x (-5) 10).toNat = 0 := by
          have r20660 : (x (-5) 10).toNat ≤ (x (-5) 2).toNat := himp _ _ (hp10 (-5))
          have b20661 := hb (x (-5) 2)
          have b20662 := hb (x (-5) 10)
          clear * - r20660 b20661 b20662 d20639
          omega
        have d20663 : (x (-5) 1 && x (-5) 10).toNat = 0 := by
          have r20664 := hand2 (x (-5) 1) (x (-5) 10)
          have b20665 := hb (x (-5) 10)
          have b20666 := hb (x (-5) 1 && x (-5) 10)
          clear * - r20664 b20665 b20666 d20659
          omega
        have d20667 : (x (-6) 3).toNat = 0 := by
          have r20668 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20669 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
          have e20670 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
          have b20671 := hb (x (-6) 3)
          have b20672 := hb (x (-5) 2)
          have b20673 := hb (x (-4) 13)
          have b20674 := hb (x (-3) 12)
          clear * - r20668 e20669 e20670 b20671 b20672 b20673 b20674 d20615 d20619 d20639
          omega
        have d20675 : (x (-6) 3 && x (-6) 12).toNat = 0 := by
          have r20676 := hand1 (x (-6) 3) (x (-6) 12)
          have b20677 := hb (x (-6) 3)
          have b20678 := hb (x (-6) 3 && x (-6) 12)
          clear * - r20676 b20677 b20678 d20667
          omega
        have d20679 : (x (-6) 3 && x (-6) 10).toNat = 0 := by
          have r20680 := hand1 (x (-6) 3) (x (-6) 10)
          have b20681 := hb (x (-6) 3)
          have b20682 := hb (x (-6) 3 && x (-6) 10)
          clear * - r20680 b20681 b20682 d20667
          omega
        have d20683 : (x (-6) 3 && x (-6) 9).toNat = 0 := by
          have r20684 := hand1 (x (-6) 3) (x (-6) 9)
          have b20685 := hb (x (-6) 3)
          have b20686 := hb (x (-6) 3 && x (-6) 9)
          clear * - r20684 b20685 b20686 d20667
          omega
        have d20687 : (x (-6) 11).toNat = 0 := by
          have r20688 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
          have b20689 := hb (x (-6) 3)
          have b20690 := hb (x (-6) 11)
          clear * - r20688 b20689 b20690 d20667
          omega
        have d20691 : (x (-6) 2 && x (-6) 11).toNat = 0 := by
          have r20692 := hand2 (x (-6) 2) (x (-6) 11)
          have b20693 := hb (x (-6) 11)
          have b20694 := hb (x (-6) 2 && x (-6) 11)
          clear * - r20692 b20693 b20694 d20687
          omega
        have d20695 : (x 4 8).toNat = 0 := by
          have r20696 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20697 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
          have e20698 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
          have e20699 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
          have e20700 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
          have e20701 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
          have e20702 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
          have b20703 := hb (x (-3) 7)
          have b20704 := hb (x (-2) 6)
          have b20705 := hb (x (-1) 5)
          have b20706 := hb (x 0 4)
          have b20707 := hb (x 1 11)
          have b20708 := hb (x 2 10)
          have b20709 := hb (x 3 9)
          have b20710 := hb (x 4 8)
          clear * - r20696 e20697 e20698 e20699 e20700 e20701 e20702 b20703 b20704 b20705 b20706 b20707 b20708 b20709 b20710 g29 d20425 d20604 g10 g3
          omega
        have d20711 : (x (-2) 6).toNat = 0 := by
          have r20712 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20713 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
          have e20714 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
          have e20715 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
          have e20716 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
          have e20717 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
          have e20718 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
          have b20719 := hb (x (-3) 7)
          have b20720 := hb (x (-2) 6)
          have b20721 := hb (x (-1) 5)
          have b20722 := hb (x 0 4)
          have b20723 := hb (x 1 11)
          have b20724 := hb (x 2 10)
          have b20725 := hb (x 3 9)
          have b20726 := hb (x 4 8)
          clear * - r20712 e20713 e20714 e20715 e20716 e20717 e20718 b20719 b20720 b20721 b20722 b20723 b20724 b20725 b20726 d20695 g29 d20425 d20604 g10 g3
          omega
        have d20727 : (x (-2) 6 && x (-2) 13).toNat = 0 := by
          have r20728 := hand1 (x (-2) 6) (x (-2) 13)
          have b20729 := hb (x (-2) 6)
          have b20730 := hb (x (-2) 6 && x (-2) 13)
          clear * - r20728 b20729 b20730 d20711
          omega
        have d20731 : (x (-3) 7).toNat = 0 := by
          have r20732 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20733 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
          have e20734 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
          have e20735 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
          have e20736 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
          have e20737 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
          have e20738 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
          have b20739 := hb (x (-3) 7)
          have b20740 := hb (x (-2) 6)
          have b20741 := hb (x (-1) 5)
          have b20742 := hb (x 0 4)
          have b20743 := hb (x 1 11)
          have b20744 := hb (x 2 10)
          have b20745 := hb (x 3 9)
          have b20746 := hb (x 4 8)
          clear * - r20732 e20733 e20734 e20735 e20736 e20737 e20738 b20739 b20740 b20741 b20742 b20743 b20744 b20745 b20746 d20695 g29 d20425 d20604 g10 g3 d20711
          omega
        have d20747 : (x (-3) 7 && x (-3) 14).toNat = 0 := by
          have r20748 := hand1 (x (-3) 7) (x (-3) 14)
          have b20749 := hb (x (-3) 7)
          have b20750 := hb (x (-3) 7 && x (-3) 14)
          clear * - r20748 b20749 b20750 d20731
          omega
        have d20751 : (x (-3) 1 && x (-3) 7).toNat = 0 := by
          have r20752 := hand2 (x (-3) 1) (x (-3) 7)
          have b20753 := hb (x (-3) 7)
          have b20754 := hb (x (-3) 1 && x (-3) 7)
          clear * - r20752 b20753 b20754 d20731
          omega
        have d20755 : (x (-4) 7).toNat = 0 := by
          have r20756 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20757 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e20758 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e20759 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e20760 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e20761 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e20762 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b20763 := hb (x (-4) 7)
          have b20764 := hb (x (-3) 6)
          have b20765 := hb (x (-2) 5)
          have b20766 := hb (x (-1) 4)
          have b20767 := hb (x 0 11)
          have b20768 := hb (x 1 10)
          have b20769 := hb (x 2 9)
          have b20770 := hb (x 3 8)
          clear * - r20756 e20757 e20758 e20759 e20760 e20761 e20762 b20763 b20764 b20765 b20766 b20767 b20768 b20769 b20770 d20320 d20336 g20 f20319 d20360 d20376 d20396
          omega
        have d20771 : (x (-4) 1 && x (-4) 7).toNat = 0 := by
          have r20772 := hand2 (x (-4) 1) (x (-4) 7)
          have b20773 := hb (x (-4) 7)
          have b20774 := hb (x (-4) 1 && x (-4) 7)
          clear * - r20772 b20773 b20774 d20755
          omega
        have d20775 : (x 1 8).toNat = 0 := by
          have r20776 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20777 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e20778 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e20779 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e20780 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e20781 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e20782 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b20783 := hb (x (-6) 7)
          have b20784 := hb (x (-5) 6)
          have b20785 := hb (x (-4) 5)
          have b20786 := hb (x (-3) 4)
          have b20787 := hb (x (-2) 11)
          have b20788 := hb (x (-1) 10)
          have b20789 := hb (x 0 9)
          have b20790 := hb (x 1 8)
          clear * - r20776 e20777 e20778 e20779 e20780 e20781 e20782 b20783 b20784 b20785 b20786 b20787 b20788 b20789 b20790 f19309 g5 g1 d20608 d20631
          omega
        have d20791 : (x (-5) 6).toNat = 0 := by
          have r20792 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20793 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e20794 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e20795 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e20796 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e20797 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e20798 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b20799 := hb (x (-6) 7)
          have b20800 := hb (x (-5) 6)
          have b20801 := hb (x (-4) 5)
          have b20802 := hb (x (-3) 4)
          have b20803 := hb (x (-2) 11)
          have b20804 := hb (x (-1) 10)
          have b20805 := hb (x 0 9)
          have b20806 := hb (x 1 8)
          clear * - r20792 e20793 e20794 e20795 e20796 e20797 e20798 b20799 b20800 b20801 b20802 b20803 b20804 b20805 b20806 d20775 f19309 g5 g1 d20608 d20631
          omega
        have d20807 : (x (-3) 4 && x (-3) 13).toNat = 1 := by
          have r20808 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20809 := hb (x (-5) 6)
          have b20810 := hb (x 1 9)
          have b20811 := hb (x 0 1 && x 0 10)
          have b20812 := hb (x (-1) 2 && x (-1) 11)
          have b20813 := hb (x (-2) 3 && x (-2) 12)
          have b20814 := hb (x (-3) 4 && x (-3) 13)
          have b20815 := hb (x (-4) 5 && x (-4) 14)
          clear * - r20808 b20809 b20810 b20811 b20812 b20813 b20814 b20815 g19 d19316 g78 g79 d20635 d20791
          omega
        have d20816 : (x (-3) 13).toNat = 1 := by
          have r20817 := hand2 (x (-3) 4) (x (-3) 13)
          have b20818 := hb (x (-3) 13)
          have b20819 := hb (x (-3) 4 && x (-3) 13)
          clear * - r20817 b20818 b20819 d20807
          omega
        have d20820 : (x (-3) 1).toNat = 1 := by
          have r20821 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
          have b20822 := hb (x (-3) 1)
          have b20823 := hb (x (-3) 13)
          clear * - r20821 b20822 b20823 d20816
          omega
        have d20824 : (x (-2) 14).toNat = 0 := by
          have r20825 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20826 := hb (x (-3) 1)
          have b20827 := hb (x (-2) 14)
          clear * - r20825 b20826 b20827 d20820
          omega
        have d20828 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
          have r20829 := hand2 (x (-2) 1) (x (-2) 14)
          have b20830 := hb (x (-2) 14)
          have b20831 := hb (x (-2) 1 && x (-2) 14)
          clear * - r20829 b20830 b20831 d20824
          omega
        have d20832 : (x (-3) 2).toNat = 1 := by
          have r20833 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20834 := hb (x (-3) 2)
          have b20835 := hb (x (-1) 13)
          have b20836 := hb (x (-2) 1 && x (-2) 14)
          clear * - r20833 b20834 b20835 b20836 g7 d20828
          omega
        have d20837 : (x (-3) 14).toNat = 1 := by
          have r20838 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
          have b20839 := hb (x (-3) 2)
          have b20840 := hb (x (-3) 14)
          clear * - r20838 b20839 b20840 d20832
          omega
        have d20841 : (x (-4) 1).toNat = 0 := by
          have r20842 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20843 := hb (x (-4) 1)
          have b20844 := hb (x (-3) 14)
          clear * - r20842 b20843 b20844 d20837
          omega
        have d20845 : (x (-4) 1 && x (-4) 10).toNat = 0 := by
          have r20846 := hand1 (x (-4) 1) (x (-4) 10)
          have b20847 := hb (x (-4) 1)
          have b20848 := hb (x (-4) 1 && x (-4) 10)
          clear * - r20846 b20847 b20848 d20841
          omega
        have d20849 : (x (-4) 1 && x (-4) 8).toNat = 0 := by
          have r20850 := hand1 (x (-4) 1) (x (-4) 8)
          have b20851 := hb (x (-4) 1)
          have b20852 := hb (x (-4) 1 && x (-4) 8)
          clear * - r20850 b20851 b20852 d20841
          omega
        have d20853 : (x (-4) 9).toNat = 0 := by
          have r20854 : (x (-4) 9).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp9 (-4))
          have b20855 := hb (x (-4) 1)
          have b20856 := hb (x (-4) 9)
          clear * - r20854 b20855 b20856 d20841
          omega
        have d20857 : (x (-1) 12).toNat = 0 := by
          have r20858 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20859 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e20860 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b20861 := hb (x (-4) 3)
          have b20862 := hb (x (-3) 2)
          have b20863 := hb (x (-2) 13)
          have b20864 := hb (x (-1) 12)
          clear * - r20858 e20859 e20860 b20861 b20862 b20863 b20864 d20832
          omega
        have d20865 : (x (-1) 6 && x (-1) 12).toNat = 0 := by
          have r20866 := hand2 (x (-1) 6) (x (-1) 12)
          have b20867 := hb (x (-1) 12)
          have b20868 := hb (x (-1) 6 && x (-1) 12)
          clear * - r20866 b20867 b20868 d20857
          omega
        have d20869 : (x (-2) 13).toNat = 0 := by
          have r20870 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20871 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e20872 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b20873 := hb (x (-4) 3)
          have b20874 := hb (x (-3) 2)
          have b20875 := hb (x (-2) 13)
          have b20876 := hb (x (-1) 12)
          clear * - r20870 e20871 e20872 b20873 b20874 b20875 b20876 d20857 d20832
          omega
        have d20877 : (x (-2) 7 && x (-2) 13).toNat = 0 := by
          have r20878 := hand2 (x (-2) 7) (x (-2) 13)
          have b20879 := hb (x (-2) 13)
          have b20880 := hb (x (-2) 7 && x (-2) 13)
          clear * - r20878 b20879 b20880 d20869
          omega
        have d20881 : (x (-2) 12).toNat = 0 := by
          have r20882 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20883 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
          have e20884 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
          have b20885 := hb (x (-5) 3)
          have b20886 := hb (x (-4) 2)
          have b20887 := hb (x (-3) 13)
          have b20888 := hb (x (-2) 12)
          clear * - r20882 e20883 e20884 b20885 b20886 b20887 b20888 d20816
          omega
        have d20889 : (x (-4) 2).toNat = 0 := by
          have r20890 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20891 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
          have e20892 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
          have b20893 := hb (x (-5) 3)
          have b20894 := hb (x (-4) 2)
          have b20895 := hb (x (-3) 13)
          have b20896 := hb (x (-2) 12)
          clear * - r20890 e20891 e20892 b20893 b20894 b20895 b20896 d20881 d20816
          omega
        have d20897 : (x (-4) 2 && x (-4) 8).toNat = 0 := by
          have r20898 := hand1 (x (-4) 2) (x (-4) 8)
          have b20899 := hb (x (-4) 2)
          have b20900 := hb (x (-4) 2 && x (-4) 8)
          clear * - r20898 b20899 b20900 d20889
          omega
        have d20901 : (x (-4) 10).toNat = 0 := by
          have r20902 : (x (-4) 10).toNat ≤ (x (-4) 2).toNat := himp _ _ (hp10 (-4))
          have b20903 := hb (x (-4) 2)
          have b20904 := hb (x (-4) 10)
          clear * - r20902 b20903 b20904 d20889
          omega
        have d20905 : (x (-5) 3).toNat = 0 := by
          have r20906 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20907 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
          have e20908 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
          have b20909 := hb (x (-5) 3)
          have b20910 := hb (x (-4) 2)
          have b20911 := hb (x (-3) 13)
          have b20912 := hb (x (-2) 12)
          clear * - r20906 e20907 e20908 b20909 b20910 b20911 b20912 d20881 d20816 d20889
          omega
        have d20913 : (x (-5) 3 && x (-5) 9).toNat = 0 := by
          have r20914 := hand1 (x (-5) 3) (x (-5) 9)
          have b20915 := hb (x (-5) 3)
          have b20916 := hb (x (-5) 3 && x (-5) 9)
          clear * - r20914 b20915 b20916 d20905
          omega
        have d20917 : (x (-5) 11).toNat = 0 := by
          have r20918 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
          have b20919 := hb (x (-5) 3)
          have b20920 := hb (x (-5) 11)
          clear * - r20918 b20919 b20920 d20905
          omega
        have d20921 : (x (-5) 1 && x (-5) 11).toNat = 0 := by
          have r20922 := hand2 (x (-5) 1) (x (-5) 11)
          have b20923 := hb (x (-5) 11)
          have b20924 := hb (x (-5) 1 && x (-5) 11)
          clear * - r20922 b20923 b20924 d20917
          omega
        have d20925 : (x 8 7).toNat = 1 := by
          have r20926 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := by have q := hcov7 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20927 := hb (x 0 8)
          have b20928 := hb (x 8 7)
          have b20929 := hb (x 7 1 && x 7 8)
          have b20930 := hb (x 6 2 && x 6 9)
          have b20931 := hb (x 5 3 && x 5 10)
          have b20932 := hb (x 4 4 && x 4 11)
          have b20933 := hb (x 3 5 && x 3 12)
          have b20934 := hb (x 2 6 && x 2 13)
          have b20935 := hb (x 1 7 && x 1 14)
          clear * - r20926 b20927 b20928 b20929 b20930 b20931 b20932 b20933 b20934 b20935 g72 g73 g74 d20449 g75 g76 g77 g11
          omega
        have d20936 : (x 15 8).toNat = 0 := by
          have r20937 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20938 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
          have e20939 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
          have e20940 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
          have e20941 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
          have e20942 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
          have e20943 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
          have b20944 := hb (x 8 7)
          have b20945 := hb (x 9 6)
          have b20946 := hb (x 10 5)
          have b20947 := hb (x 11 4)
          have b20948 := hb (x 12 11)
          have b20949 := hb (x 13 10)
          have b20950 := hb (x 14 9)
          have b20951 := hb (x 15 8)
          clear * - r20937 e20938 e20939 e20940 e20941 e20942 e20943 b20944 b20945 b20946 b20947 b20948 b20949 b20950 b20951 d20484 d20512 d20925
          omega
        have d20952 : (x 14 9).toNat = 0 := by
          have r20953 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20954 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
          have e20955 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
          have e20956 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
          have e20957 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
          have e20958 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
          have e20959 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
          have b20960 := hb (x 8 7)
          have b20961 := hb (x 9 6)
          have b20962 := hb (x 10 5)
          have b20963 := hb (x 11 4)
          have b20964 := hb (x 12 11)
          have b20965 := hb (x 13 10)
          have b20966 := hb (x 14 9)
          have b20967 := hb (x 15 8)
          clear * - r20953 e20954 e20955 e20956 e20957 e20958 e20959 b20960 b20961 b20962 b20963 b20964 b20965 b20966 b20967 d20936 d20484 d20512 d20925
          omega
        have d20968 : (x 13 10).toNat = 0 := by
          have r20969 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20970 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
          have e20971 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
          have e20972 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
          have e20973 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
          have e20974 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
          have e20975 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
          have b20976 := hb (x 8 7)
          have b20977 := hb (x 9 6)
          have b20978 := hb (x 10 5)
          have b20979 := hb (x 11 4)
          have b20980 := hb (x 12 11)
          have b20981 := hb (x 13 10)
          have b20982 := hb (x 14 9)
          have b20983 := hb (x 15 8)
          clear * - r20969 e20970 e20971 e20972 e20973 e20974 e20975 b20976 b20977 b20978 b20979 b20980 b20981 b20982 b20983 d20936 d20952 d20484 d20512 d20925
          omega
        have d20984 : (x 12 11).toNat = 0 := by
          have r20985 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20986 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
          have e20987 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
          have e20988 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
          have e20989 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
          have e20990 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
          have e20991 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
          have b20992 := hb (x 8 7)
          have b20993 := hb (x 9 6)
          have b20994 := hb (x 10 5)
          have b20995 := hb (x 11 4)
          have b20996 := hb (x 12 11)
          have b20997 := hb (x 13 10)
          have b20998 := hb (x 14 9)
          have b20999 := hb (x 15 8)
          clear * - r20985 e20986 e20987 e20988 e20989 e20990 e20991 b20992 b20993 b20994 b20995 b20996 b20997 b20998 b20999 d20936 d20952 d20968 d20484 d20512 d20925
          omega
        have d21000 : (x 12 1 && x 12 11).toNat = 0 := by
          have r21001 := hand2 (x 12 1) (x 12 11)
          have b21002 := hb (x 12 11)
          have b21003 := hb (x 12 1 && x 12 11)
          clear * - r21001 b21002 b21003 d20984
          omega
        have d21004 : (x 9 6).toNat = 0 := by
          have r21005 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21006 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
          have e21007 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
          have e21008 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
          have e21009 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
          have e21010 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
          have e21011 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
          have b21012 := hb (x 8 7)
          have b21013 := hb (x 9 6)
          have b21014 := hb (x 10 5)
          have b21015 := hb (x 11 4)
          have b21016 := hb (x 12 11)
          have b21017 := hb (x 13 10)
          have b21018 := hb (x 14 9)
          have b21019 := hb (x 15 8)
          clear * - r21005 e21006 e21007 e21008 e21009 e21010 e21011 b21012 b21013 b21014 b21015 b21016 b21017 b21018 b21019 d20936 d20952 d20968 d20984 d20484 d20512 d20925
          omega
        have d21020 : (x 9 6 && x 9 12).toNat = 0 := by
          have r21021 := hand1 (x 9 6) (x 9 12)
          have b21022 := hb (x 9 6)
          have b21023 := hb (x 9 6 && x 9 12)
          clear * - r21021 b21022 b21023 d21004
          omega
        have d21024 : (x (-4) 8).toNat = 1 := by
          have r21025 : 1 ≤ (x 4 7).toNat + (x 3 1 && x 3 8).toNat + (x 2 2 && x 2 9).toNat + (x 1 3 && x 1 10).toNat + (x 0 4 && x 0 11).toNat + (x (-1) 5 && x (-1) 12).toNat + (x (-2) 6 && x (-2) 13).toNat + (x (-3) 7 && x (-3) 14).toNat + (x (-4) 8).toNat := by have q := hcov7 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21026 := hb (x (-4) 8)
          have b21027 := hb (x 4 7)
          have b21028 := hb (x 3 1 && x 3 8)
          have b21029 := hb (x 2 2 && x 2 9)
          have b21030 := hb (x 1 3 && x 1 10)
          have b21031 := hb (x 0 4 && x 0 11)
          have b21032 := hb (x (-1) 5 && x (-1) 12)
          have b21033 := hb (x (-2) 6 && x (-2) 13)
          have b21034 := hb (x (-3) 7 && x (-3) 14)
          clear * - r21025 b21026 b21027 b21028 b21029 b21030 b21031 b21032 b21033 b21034 d20572 g68 d20352 g69 g70 g71 d20727 d20747
          omega
        have d21035 : (x (-5) 9).toNat = 0 := by
          have r21036 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21037 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
          have e21038 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
          have e21039 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
          have e21040 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
          have e21041 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
          have e21042 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
          have b21043 := hb (x (-11) 7)
          have b21044 := hb (x (-10) 6)
          have b21045 := hb (x (-9) 5)
          have b21046 := hb (x (-8) 4)
          have b21047 := hb (x (-7) 11)
          have b21048 := hb (x (-6) 10)
          have b21049 := hb (x (-5) 9)
          have b21050 := hb (x (-4) 8)
          clear * - r21036 e21037 e21038 e21039 e21040 e21041 e21042 b21043 b21044 b21045 b21046 b21047 b21048 b21049 b21050 d21024
          omega
        have d21051 : (x (-6) 10).toNat = 0 := by
          have r21052 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21053 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
          have e21054 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
          have e21055 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
          have e21056 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
          have e21057 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
          have e21058 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
          have b21059 := hb (x (-11) 7)
          have b21060 := hb (x (-10) 6)
          have b21061 := hb (x (-9) 5)
          have b21062 := hb (x (-8) 4)
          have b21063 := hb (x (-7) 11)
          have b21064 := hb (x (-6) 10)
          have b21065 := hb (x (-5) 9)
          have b21066 := hb (x (-4) 8)
          clear * - r21052 e21053 e21054 e21055 e21056 e21057 e21058 b21059 b21060 b21061 b21062 b21063 b21064 b21065 b21066 d21024 d21035
          omega
        have d21067 : (x (-6) 1 && x (-6) 10).toNat = 0 := by
          have r21068 := hand2 (x (-6) 1) (x (-6) 10)
          have b21069 := hb (x (-6) 10)
          have b21070 := hb (x (-6) 1 && x (-6) 10)
          clear * - r21068 b21069 b21070 d21051
          omega
        have d21071 : (x (-6) 4 && x (-6) 10).toNat = 0 := by
          have r21072 := hand2 (x (-6) 4) (x (-6) 10)
          have b21073 := hb (x (-6) 10)
          have b21074 := hb (x (-6) 4 && x (-6) 10)
          clear * - r21072 b21073 b21074 d21051
          omega
        have d21075 : (x (-7) 11).toNat = 0 := by
          have r21076 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21077 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
          have e21078 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
          have e21079 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
          have e21080 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
          have e21081 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
          have e21082 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
          have b21083 := hb (x (-11) 7)
          have b21084 := hb (x (-10) 6)
          have b21085 := hb (x (-9) 5)
          have b21086 := hb (x (-8) 4)
          have b21087 := hb (x (-7) 11)
          have b21088 := hb (x (-6) 10)
          have b21089 := hb (x (-5) 9)
          have b21090 := hb (x (-4) 8)
          clear * - r21076 e21077 e21078 e21079 e21080 e21081 e21082 b21083 b21084 b21085 b21086 b21087 b21088 b21089 b21090 d21024 d21035 d21051
          omega
        have d21091 : (x (-7) 2 && x (-7) 11).toNat = 0 := by
          have r21092 := hand2 (x (-7) 2) (x (-7) 11)
          have b21093 := hb (x (-7) 11)
          have b21094 := hb (x (-7) 2 && x (-7) 11)
          clear * - r21092 b21093 b21094 d21075
          omega
        have d21095 : (x (-7) 4 && x (-7) 11).toNat = 0 := by
          have r21096 := hand2 (x (-7) 4) (x (-7) 11)
          have b21097 := hb (x (-7) 11)
          have b21098 := hb (x (-7) 4 && x (-7) 11)
          clear * - r21096 b21097 b21098 d21075
          omega
        have d21099 : (x (-7) 5 && x (-7) 11).toNat = 0 := by
          have r21100 := hand2 (x (-7) 5) (x (-7) 11)
          have b21101 := hb (x (-7) 11)
          have b21102 := hb (x (-7) 5 && x (-7) 11)
          clear * - r21100 b21101 b21102 d21075
          omega
        have d21103 : (x (-8) 4).toNat = 0 := by
          have r21104 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21105 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
          have e21106 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
          have e21107 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
          have e21108 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
          have e21109 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
          have e21110 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
          have b21111 := hb (x (-11) 7)
          have b21112 := hb (x (-10) 6)
          have b21113 := hb (x (-9) 5)
          have b21114 := hb (x (-8) 4)
          have b21115 := hb (x (-7) 11)
          have b21116 := hb (x (-6) 10)
          have b21117 := hb (x (-5) 9)
          have b21118 := hb (x (-4) 8)
          clear * - r21104 e21105 e21106 e21107 e21108 e21109 e21110 b21111 b21112 b21113 b21114 b21115 b21116 b21117 b21118 d21024 d21035 d21051 d21075
          omega
        have d21119 : (x (-8) 4 && x (-8) 14).toNat = 0 := by
          have r21120 := hand1 (x (-8) 4) (x (-8) 14)
          have b21121 := hb (x (-8) 4)
          have b21122 := hb (x (-8) 4 && x (-8) 14)
          clear * - r21120 b21121 b21122 d21103
          omega
        have d21123 : (x (-8) 4 && x (-8) 13).toNat = 0 := by
          have r21124 := hand1 (x (-8) 4) (x (-8) 13)
          have b21125 := hb (x (-8) 4)
          have b21126 := hb (x (-8) 4 && x (-8) 13)
          clear * - r21124 b21125 b21126 d21103
          omega
        have d21127 : (x (-9) 5).toNat = 0 := by
          have r21128 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21129 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
          have e21130 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
          have e21131 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
          have e21132 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
          have e21133 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
          have e21134 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
          have b21135 := hb (x (-11) 7)
          have b21136 := hb (x (-10) 6)
          have b21137 := hb (x (-9) 5)
          have b21138 := hb (x (-8) 4)
          have b21139 := hb (x (-7) 11)
          have b21140 := hb (x (-6) 10)
          have b21141 := hb (x (-5) 9)
          have b21142 := hb (x (-4) 8)
          clear * - r21128 e21129 e21130 e21131 e21132 e21133 e21134 b21135 b21136 b21137 b21138 b21139 b21140 b21141 b21142 d21024 d21035 d21051 d21075 d21103
          omega
        have d21143 : (x (-9) 5 && x (-9) 14).toNat = 0 := by
          have r21144 := hand1 (x (-9) 5) (x (-9) 14)
          have b21145 := hb (x (-9) 5)
          have b21146 := hb (x (-9) 5 && x (-9) 14)
          clear * - r21144 b21145 b21146 d21127
          omega
        have d21147 : (x (-10) 6).toNat = 0 := by
          have r21148 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21149 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
          have e21150 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
          have e21151 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
          have e21152 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
          have e21153 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
          have e21154 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
          have b21155 := hb (x (-11) 7)
          have b21156 := hb (x (-10) 6)
          have b21157 := hb (x (-9) 5)
          have b21158 := hb (x (-8) 4)
          have b21159 := hb (x (-7) 11)
          have b21160 := hb (x (-6) 10)
          have b21161 := hb (x (-5) 9)
          have b21162 := hb (x (-4) 8)
          clear * - r21148 e21149 e21150 e21151 e21152 e21153 e21154 b21155 b21156 b21157 b21158 b21159 b21160 b21161 b21162 d21024 d21035 d21051 d21075 d21103 d21127
          omega
        have d21163 : (x (-7) 3 && x (-7) 12).toNat = 1 := by
          have r21164 : 1 ≤ (x (-4) 9).toNat + (x (-5) 1 && x (-5) 10).toNat + (x (-6) 2 && x (-6) 11).toNat + (x (-7) 3 && x (-7) 12).toNat + (x (-8) 4 && x (-8) 13).toNat + (x (-9) 5 && x (-9) 14).toNat + (x (-10) 6).toNat := by have q := hcov9 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21165 := hb (x (-10) 6)
          have b21166 := hb (x (-4) 9)
          have b21167 := hb (x (-5) 1 && x (-5) 10)
          have b21168 := hb (x (-6) 2 && x (-6) 11)
          have b21169 := hb (x (-7) 3 && x (-7) 12)
          have b21170 := hb (x (-8) 4 && x (-8) 13)
          have b21171 := hb (x (-9) 5 && x (-9) 14)
          clear * - r21164 b21165 b21166 b21167 b21168 b21169 b21170 b21171 d20853 d20663 d20691 d21123 d21143 d21147
          omega
        have d21172 : (x (-7) 12).toNat = 1 := by
          have r21173 := hand2 (x (-7) 3) (x (-7) 12)
          have b21174 := hb (x (-7) 12)
          have b21175 := hb (x (-7) 3 && x (-7) 12)
          clear * - r21173 b21174 b21175 d21163
          omega
        have d21176 : (x (-8) 13).toNat = 0 := by
          have r21177 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21178 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
          have e21179 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
          have b21180 := hb (x (-10) 3)
          have b21181 := hb (x (-9) 2)
          have b21182 := hb (x (-8) 13)
          have b21183 := hb (x (-7) 12)
          clear * - r21177 e21178 e21179 b21180 b21181 b21182 b21183 d21172
          omega
        have d21184 : (x (-8) 5).toNat = 0 := by
          have r21185 : (x (-8) 5).toNat ≤ (x (-8) 13).toNat := himp _ _ (hp5 (-8))
          have b21186 := hb (x (-8) 5)
          have b21187 := hb (x (-8) 13)
          clear * - r21185 b21186 b21187 d21176
          omega
        have d21188 : (x (-8) 5 && x (-8) 14).toNat = 0 := by
          have r21189 := hand1 (x (-8) 5) (x (-8) 14)
          have b21190 := hb (x (-8) 5)
          have b21191 := hb (x (-8) 5 && x (-8) 14)
          clear * - r21189 b21190 b21191 d21184
          omega
        have d21192 : (x (-8) 5 && x (-8) 12).toNat = 0 := by
          have r21193 := hand1 (x (-8) 5) (x (-8) 12)
          have b21194 := hb (x (-8) 5)
          have b21195 := hb (x (-8) 5 && x (-8) 12)
          clear * - r21193 b21194 b21195 d21184
          omega
        have d21196 : (x (-8) 5 && x (-8) 11).toNat = 0 := by
          have r21197 := hand1 (x (-8) 5) (x (-8) 11)
          have b21198 := hb (x (-8) 5)
          have b21199 := hb (x (-8) 5 && x (-8) 11)
          clear * - r21197 b21198 b21199 d21184
          omega
        have d21200 : (x (-9) 2).toNat = 0 := by
          have r21201 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21202 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
          have e21203 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
          have b21204 := hb (x (-10) 3)
          have b21205 := hb (x (-9) 2)
          have b21206 := hb (x (-8) 13)
          have b21207 := hb (x (-7) 12)
          clear * - r21201 e21202 e21203 b21204 b21205 b21206 b21207 d21172 d21176
          omega
        have d21208 : (x (-9) 2 && x (-9) 13).toNat = 0 := by
          have r21209 := hand1 (x (-9) 2) (x (-9) 13)
          have b21210 := hb (x (-9) 2)
          have b21211 := hb (x (-9) 2 && x (-9) 13)
          clear * - r21209 b21210 b21211 d21200
          omega
        have d21212 : (x (-10) 3).toNat = 0 := by
          have r21213 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21214 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
          have e21215 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
          have b21216 := hb (x (-10) 3)
          have b21217 := hb (x (-9) 2)
          have b21218 := hb (x (-8) 13)
          have b21219 := hb (x (-7) 12)
          clear * - r21213 e21214 e21215 b21216 b21217 b21218 b21219 d21172 d21176 d21200
          omega
        have d21220 : (x (-10) 3 && x (-10) 14).toNat = 0 := by
          have r21221 := hand1 (x (-10) 3) (x (-10) 14)
          have b21222 := hb (x (-10) 3)
          have b21223 := hb (x (-10) 3 && x (-10) 14)
          clear * - r21221 b21222 b21223 d21212
          omega
        have d21224 : (x (-7) 3).toNat = 1 := by
          have r21225 := hand1 (x (-7) 3) (x (-7) 12)
          have b21226 := hb (x (-7) 3)
          have b21227 := hb (x (-7) 3 && x (-7) 12)
          clear * - r21225 b21226 b21227 d21163
          omega
        have d21228 : (x (-4) 12).toNat = 0 := by
          have r21229 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21230 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
          have e21231 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
          have b21232 := hb (x (-7) 3)
          have b21233 := hb (x (-6) 2)
          have b21234 := hb (x (-5) 13)
          have b21235 := hb (x (-4) 12)
          clear * - r21229 e21230 e21231 b21232 b21233 b21234 b21235 d21224
          omega
        have d21236 : (x (-5) 13).toNat = 0 := by
          have r21237 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21238 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
          have e21239 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
          have b21240 := hb (x (-7) 3)
          have b21241 := hb (x (-6) 2)
          have b21242 := hb (x (-5) 13)
          have b21243 := hb (x (-4) 12)
          clear * - r21237 e21238 e21239 b21240 b21241 b21242 b21243 d21228 d21224
          omega
        have d21244 : (x (-6) 2).toNat = 0 := by
          have r21245 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21246 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
          have e21247 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
          have b21248 := hb (x (-7) 3)
          have b21249 := hb (x (-6) 2)
          have b21250 := hb (x (-5) 13)
          have b21251 := hb (x (-4) 12)
          clear * - r21245 e21246 e21247 b21248 b21249 b21250 b21251 d21228 d21236 d21224
          omega
        have d21252 : (x (-6) 2 && x (-6) 12).toNat = 0 := by
          have r21253 := hand1 (x (-6) 2) (x (-6) 12)
          have b21254 := hb (x (-6) 2)
          have b21255 := hb (x (-6) 2 && x (-6) 12)
          clear * - r21253 b21254 b21255 d21244
          omega
        have d21256 : (x (-7) 3 && x (-7) 13).toNat = 1 := by
          have r21257 : 1 ≤ (x (-4) 10).toNat + (x (-5) 1 && x (-5) 11).toNat + (x (-6) 2 && x (-6) 12).toNat + (x (-7) 3 && x (-7) 13).toNat + (x (-8) 4 && x (-8) 14).toNat + (x (-9) 5).toNat := by have q := hcov10 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21258 := hb (x (-9) 5)
          have b21259 := hb (x (-4) 10)
          have b21260 := hb (x (-5) 1 && x (-5) 11)
          have b21261 := hb (x (-6) 2 && x (-6) 12)
          have b21262 := hb (x (-7) 3 && x (-7) 13)
          have b21263 := hb (x (-8) 4 && x (-8) 14)
          clear * - r21257 b21258 b21259 b21260 b21261 b21262 b21263 d20901 d20921 d21252 d21119 d21127
          omega
        have d21264 : (x (-7) 13).toNat = 1 := by
          have r21265 := hand2 (x (-7) 3) (x (-7) 13)
          have b21266 := hb (x (-7) 13)
          have b21267 := hb (x (-7) 3 && x (-7) 13)
          clear * - r21265 b21266 b21267 d21256
          omega
        have d21268 : (x (-7) 1).toNat = 1 := by
          have r21269 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
          have b21270 := hb (x (-7) 1)
          have b21271 := hb (x (-7) 13)
          clear * - r21269 b21270 b21271 d21264
          omega
        have d21272 : (x (-6) 14).toNat = 0 := by
          have r21273 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21274 := hb (x (-7) 1)
          have b21275 := hb (x (-6) 14)
          clear * - r21273 b21274 b21275 d21268
          omega
        have d21276 : (x (-6) 1 && x (-6) 14).toNat = 0 := by
          have r21277 := hand2 (x (-6) 1) (x (-6) 14)
          have b21278 := hb (x (-6) 14)
          have b21279 := hb (x (-6) 1 && x (-6) 14)
          clear * - r21277 b21278 b21279 d21272
          omega
        have d21280 : (x (-7) 2).toNat = 1 := by
          have r21281 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21282 := hb (x (-7) 2)
          have b21283 := hb (x (-5) 13)
          have b21284 := hb (x (-6) 1 && x (-6) 14)
          clear * - r21281 b21282 b21283 b21284 d21236 d21276
          omega
        have d21285 : (x (-7) 14).toNat = 1 := by
          have r21286 : (x (-7) 2).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp2 (-7))
          have b21287 := hb (x (-7) 2)
          have b21288 := hb (x (-7) 14)
          clear * - r21286 b21287 b21288 d21280
          omega
        have d21289 : (x (-8) 1).toNat = 0 := by
          have r21290 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21291 := hb (x (-8) 1)
          have b21292 := hb (x (-7) 14)
          clear * - r21290 b21291 b21292 d21285
          omega
        have d21293 : (x (-8) 1 && x (-8) 12).toNat = 0 := by
          have r21294 := hand1 (x (-8) 1) (x (-8) 12)
          have b21295 := hb (x (-8) 1)
          have b21296 := hb (x (-8) 1 && x (-8) 12)
          clear * - r21294 b21295 b21296 d21289
          omega
        have d21297 : (x (-11) 4).toNat = 1 := by
          have r21298 : 1 ≤ (x (-7) 11).toNat + (x (-8) 1 && x (-8) 12).toNat + (x (-9) 2 && x (-9) 13).toNat + (x (-10) 3 && x (-10) 14).toNat + (x (-11) 4).toNat := by have q := hcov11 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21299 := hb (x (-11) 4)
          have b21300 := hb (x (-7) 11)
          have b21301 := hb (x (-8) 1 && x (-8) 12)
          have b21302 := hb (x (-9) 2 && x (-9) 13)
          have b21303 := hb (x (-10) 3 && x (-10) 14)
          clear * - r21298 b21299 b21300 b21301 b21302 b21303 d21075 d21293 d21208 d21220
          omega
        have d21304 : (x (-11) 12).toNat = 1 := by
          have r21305 : (x (-11) 4).toNat ≤ (x (-11) 12).toNat := himp _ _ (hp4 (-11))
          have b21306 := hb (x (-11) 4)
          have b21307 := hb (x (-11) 12)
          clear * - r21305 b21306 b21307 d21297
          omega
        have d21308 : (x (-12) 13).toNat = 0 := by
          have r21309 : (x (-11) 12).toNat + (x (-12) 1 && x (-12) 13).toNat + (x (-13) 2 && x (-13) 14).toNat + (x (-14) 3).toNat = 1 := by have q := hd12 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21310 : (x (-12) 1 && x (-12) 13).toNat = (x (-12) 13).toNat := handr _ _ (fun h => hp13 (-12) (h))
          have e21311 : (x (-13) 2 && x (-13) 14).toNat = (x (-13) 2).toNat := handl _ _ (fun h => hp2 (-13) (h))
          have b21312 := hb (x (-14) 3)
          have b21313 := hb (x (-13) 2)
          have b21314 := hb (x (-12) 13)
          have b21315 := hb (x (-11) 12)
          clear * - r21309 e21310 e21311 b21312 b21313 b21314 b21315 d21304
          omega
        have d21316 : (x (-13) 2).toNat = 0 := by
          have r21317 : (x (-11) 12).toNat + (x (-12) 1 && x (-12) 13).toNat + (x (-13) 2 && x (-13) 14).toNat + (x (-14) 3).toNat = 1 := by have q := hd12 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21318 : (x (-12) 1 && x (-12) 13).toNat = (x (-12) 13).toNat := handr _ _ (fun h => hp13 (-12) (h))
          have e21319 : (x (-13) 2 && x (-13) 14).toNat = (x (-13) 2).toNat := handl _ _ (fun h => hp2 (-13) (h))
          have b21320 := hb (x (-14) 3)
          have b21321 := hb (x (-13) 2)
          have b21322 := hb (x (-12) 13)
          have b21323 := hb (x (-11) 12)
          clear * - r21317 e21318 e21319 b21320 b21321 b21322 b21323 d21304 d21308
          omega
        have d21324 : (x (-13) 10).toNat = 0 := by
          have r21325 : (x (-13) 10).toNat ≤ (x (-13) 2).toNat := himp _ _ (hp10 (-13))
          have b21326 := hb (x (-13) 2)
          have b21327 := hb (x (-13) 10)
          clear * - r21325 b21326 b21327 d21316
          omega
        have d21328 : (x (-14) 3).toNat = 0 := by
          have r21329 : (x (-11) 12).toNat + (x (-12) 1 && x (-12) 13).toNat + (x (-13) 2 && x (-13) 14).toNat + (x (-14) 3).toNat = 1 := by have q := hd12 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21330 : (x (-12) 1 && x (-12) 13).toNat = (x (-12) 13).toNat := handr _ _ (fun h => hp13 (-12) (h))
          have e21331 : (x (-13) 2 && x (-13) 14).toNat = (x (-13) 2).toNat := handl _ _ (fun h => hp2 (-13) (h))
          have b21332 := hb (x (-14) 3)
          have b21333 := hb (x (-13) 2)
          have b21334 := hb (x (-12) 13)
          have b21335 := hb (x (-11) 12)
          clear * - r21329 e21330 e21331 b21332 b21333 b21334 b21335 d21304 d21308 d21316
          omega
        have d21336 : (x (-14) 11).toNat = 0 := by
          have r21337 : (x (-14) 11).toNat ≤ (x (-14) 3).toNat := himp _ _ (hp11 (-14))
          have b21338 := hb (x (-14) 3)
          have b21339 := hb (x (-14) 11)
          clear * - r21337 b21338 b21339 d21328
          omega
        have d21340 : (x (-5) 12).toNat = 0 := by
          have r21341 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21342 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
          have e21343 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
          have b21344 := hb (x (-8) 3)
          have b21345 := hb (x (-7) 2)
          have b21346 := hb (x (-6) 13)
          have b21347 := hb (x (-5) 12)
          clear * - r21341 e21342 e21343 b21344 b21345 b21346 b21347 d21280
          omega
        have d21348 : (x (-6) 13).toNat = 0 := by
          have r21349 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21350 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
          have e21351 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
          have b21352 := hb (x (-8) 3)
          have b21353 := hb (x (-7) 2)
          have b21354 := hb (x (-6) 13)
          have b21355 := hb (x (-5) 12)
          clear * - r21349 e21350 e21351 b21352 b21353 b21354 b21355 d21340 d21280
          omega
        have d21356 : (x (-8) 3).toNat = 0 := by
          have r21357 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21358 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
          have e21359 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
          have b21360 := hb (x (-8) 3)
          have b21361 := hb (x (-7) 2)
          have b21362 := hb (x (-6) 13)
          have b21363 := hb (x (-5) 12)
          clear * - r21357 e21358 e21359 b21360 b21361 b21362 b21363 d21340 d21348 d21280
          omega
        have d21364 : (x (-8) 3 && x (-8) 12).toNat = 0 := by
          have r21365 := hand1 (x (-8) 3) (x (-8) 12)
          have b21366 := hb (x (-8) 3)
          have b21367 := hb (x (-8) 3 && x (-8) 12)
          clear * - r21365 b21366 b21367 d21356
          omega
        have d21368 : (x (-8) 11).toNat = 0 := by
          have r21369 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
          have b21370 := hb (x (-8) 3)
          have b21371 := hb (x (-8) 11)
          clear * - r21369 b21370 b21371 d21356
          omega
        have d21372 : (x (-6) 12).toNat = 0 := by
          have r21373 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21374 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
          have e21375 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
          have b21376 := hb (x (-9) 3)
          have b21377 := hb (x (-8) 2)
          have b21378 := hb (x (-7) 13)
          have b21379 := hb (x (-6) 12)
          clear * - r21373 e21374 e21375 b21376 b21377 b21378 b21379 d21264
          omega
        have d21380 : (x (-6) 4).toNat = 0 := by
          have r21381 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
          have b21382 := hb (x (-6) 4)
          have b21383 := hb (x (-6) 12)
          clear * - r21381 b21382 b21383 d21372
          omega
        have d21384 : (x (-5) 1 && x (-5) 14).toNat = 1 := by
          have r21385 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21386 := hb (x (-6) 2)
          have b21387 := hb (x (-4) 13)
          have b21388 := hb (x (-5) 1 && x (-5) 14)
          clear * - r21385 b21386 b21387 b21388 d20619 d21244
          omega
        have d21389 : (x (-5) 14).toNat = 1 := by
          have r21390 := hand2 (x (-5) 1) (x (-5) 14)
          have b21391 := hb (x (-5) 14)
          have b21392 := hb (x (-5) 1 && x (-5) 14)
          clear * - r21390 b21391 b21392 d21384
          omega
        have d21393 : (x (-6) 1).toNat = 0 := by
          have r21394 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21395 := hb (x (-6) 1)
          have b21396 := hb (x (-5) 14)
          clear * - r21394 b21395 b21396 d21389
          omega
        have d21397 : (x (-6) 9).toNat = 0 := by
          have r21398 : (x (-6) 9).toNat ≤ (x (-6) 1).toNat := himp _ _ (hp9 (-6))
          have b21399 := hb (x (-6) 1)
          have b21400 := hb (x (-6) 9)
          clear * - r21398 b21399 b21400 d21393
          omega
        have d21401 : (x (-3) 8 && x (-3) 14).toNat = 1 := by
          have r21402 : 1 ≤ (x 5 6).toNat + (x 4 1 && x 4 7).toNat + (x 3 2 && x 3 8).toNat + (x 2 3 && x 2 9).toNat + (x 1 4 && x 1 10).toNat + (x 0 5 && x 0 11).toNat + (x (-1) 6 && x (-1) 12).toNat + (x (-2) 7 && x (-2) 13).toNat + (x (-3) 8 && x (-3) 14).toNat + (x (-4) 9).toNat := by have q := hcov6 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21403 := hb (x (-4) 9)
          have b21404 := hb (x 5 6)
          have b21405 := hb (x 4 1 && x 4 7)
          have b21406 := hb (x 3 2 && x 3 8)
          have b21407 := hb (x 2 3 && x 2 9)
          have b21408 := hb (x 1 4 && x 1 10)
          have b21409 := hb (x 0 5 && x 0 11)
          have b21410 := hb (x (-1) 6 && x (-1) 12)
          have b21411 := hb (x (-2) 7 && x (-2) 13)
          have b21412 := hb (x (-3) 8 && x (-3) 14)
          clear * - r21402 b21403 b21404 b21405 b21406 b21407 b21408 b21409 b21410 b21411 b21412 g35 d20592 g55 d20356 g56 g57 d20865 d20877 d20853
          omega
        have d21413 : (x (-3) 8).toNat = 1 := by
          have r21414 := hand1 (x (-3) 8) (x (-3) 14)
          have b21415 := hb (x (-3) 8)
          have b21416 := hb (x (-3) 8 && x (-3) 14)
          clear * - r21414 b21415 b21416 d21401
          omega
        have d21417 : (x (-7) 4).toNat = 0 := by
          have r21418 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21419 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
          have e21420 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
          have e21421 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
          have e21422 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
          have e21423 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
          have e21424 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
          have b21425 := hb (x (-10) 7)
          have b21426 := hb (x (-9) 6)
          have b21427 := hb (x (-8) 5)
          have b21428 := hb (x (-7) 4)
          have b21429 := hb (x (-6) 11)
          have b21430 := hb (x (-5) 10)
          have b21431 := hb (x (-4) 9)
          have b21432 := hb (x (-3) 8)
          clear * - r21418 e21419 e21420 e21421 e21422 e21423 e21424 b21425 b21426 b21427 b21428 b21429 b21430 b21431 b21432 d21413 d20853 d20659 d20687 d21184
          omega
        have d21433 : (x (-7) 4 && x (-7) 13).toNat = 0 := by
          have r21434 := hand1 (x (-7) 4) (x (-7) 13)
          have b21435 := hb (x (-7) 4)
          have b21436 := hb (x (-7) 4 && x (-7) 13)
          clear * - r21434 b21435 b21436 d21417
          omega
        have d21437 : (x (-7) 4 && x (-7) 10).toNat = 0 := by
          have r21438 := hand1 (x (-7) 4) (x (-7) 10)
          have b21439 := hb (x (-7) 4)
          have b21440 := hb (x (-7) 4 && x (-7) 10)
          clear * - r21438 b21439 b21440 d21417
          omega
        have d21441 : (x (-9) 6).toNat = 0 := by
          have r21442 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21443 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
          have e21444 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
          have e21445 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
          have e21446 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
          have e21447 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
          have e21448 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
          have b21449 := hb (x (-10) 7)
          have b21450 := hb (x (-9) 6)
          have b21451 := hb (x (-8) 5)
          have b21452 := hb (x (-7) 4)
          have b21453 := hb (x (-6) 11)
          have b21454 := hb (x (-5) 10)
          have b21455 := hb (x (-4) 9)
          have b21456 := hb (x (-3) 8)
          clear * - r21442 e21443 e21444 e21445 e21446 e21447 e21448 b21449 b21450 b21451 b21452 b21453 b21454 b21455 b21456 d21413 d20853 d20659 d20687 d21417 d21184
          omega
        have d21457 : (x (-9) 6 && x (-9) 13).toNat = 0 := by
          have r21458 := hand1 (x (-9) 6) (x (-9) 13)
          have b21459 := hb (x (-9) 6)
          have b21460 := hb (x (-9) 6 && x (-9) 13)
          clear * - r21458 b21459 b21460 d21441
          omega
        have d21461 : (x (-9) 6 && x (-9) 12).toNat = 0 := by
          have r21462 := hand1 (x (-9) 6) (x (-9) 12)
          have b21463 := hb (x (-9) 6)
          have b21464 := hb (x (-9) 6 && x (-9) 12)
          clear * - r21462 b21463 b21464 d21441
          omega
        have d21465 : (x (-3) 9).toNat = 1 := by
          have r21466 : 1 ≤ (x (-3) 9).toNat + (x (-4) 1 && x (-4) 10).toNat + (x (-5) 2 && x (-5) 11).toNat + (x (-6) 3 && x (-6) 12).toNat + (x (-7) 4 && x (-7) 13).toNat + (x (-8) 5 && x (-8) 14).toNat + (x (-9) 6).toNat := by have q := hcov9 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21467 := hb (x (-9) 6)
          have b21468 := hb (x (-3) 9)
          have b21469 := hb (x (-4) 1 && x (-4) 10)
          have b21470 := hb (x (-5) 2 && x (-5) 11)
          have b21471 := hb (x (-6) 3 && x (-6) 12)
          have b21472 := hb (x (-7) 4 && x (-7) 13)
          have b21473 := hb (x (-8) 5 && x (-8) 14)
          clear * - r21466 b21467 b21468 b21469 b21470 b21471 b21472 b21473 d20845 d20647 d20675 d21433 d21188 d21441
          omega
        have d21474 : (x (-2) 8).toNat = 0 := by
          have r21475 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21476 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
          have e21477 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
          have e21478 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
          have e21479 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
          have e21480 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
          have e21481 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
          have b21482 := hb (x (-9) 7)
          have b21483 := hb (x (-8) 6)
          have b21484 := hb (x (-7) 5)
          have b21485 := hb (x (-6) 4)
          have b21486 := hb (x (-5) 11)
          have b21487 := hb (x (-4) 10)
          have b21488 := hb (x (-3) 9)
          have b21489 := hb (x (-2) 8)
          clear * - r21475 e21476 e21477 e21478 e21479 e21480 e21481 b21482 b21483 b21484 b21485 b21486 b21487 b21488 b21489 d21465 d20901 d20917 d21380
          omega
        have d21490 : (x (-7) 5).toNat = 0 := by
          have r21491 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21492 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
          have e21493 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
          have e21494 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
          have e21495 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
          have e21496 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
          have e21497 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
          have b21498 := hb (x (-9) 7)
          have b21499 := hb (x (-8) 6)
          have b21500 := hb (x (-7) 5)
          have b21501 := hb (x (-6) 4)
          have b21502 := hb (x (-5) 11)
          have b21503 := hb (x (-4) 10)
          have b21504 := hb (x (-3) 9)
          have b21505 := hb (x (-2) 8)
          clear * - r21491 e21492 e21493 e21494 e21495 e21496 e21497 b21498 b21499 b21500 b21501 b21502 b21503 b21504 b21505 d21474 d21465 d20901 d20917 d21380
          omega
        have d21506 : (x (-8) 6).toNat = 0 := by
          have r21507 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21508 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
          have e21509 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
          have e21510 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
          have e21511 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
          have e21512 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
          have e21513 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
          have b21514 := hb (x (-9) 7)
          have b21515 := hb (x (-8) 6)
          have b21516 := hb (x (-7) 5)
          have b21517 := hb (x (-6) 4)
          have b21518 := hb (x (-5) 11)
          have b21519 := hb (x (-4) 10)
          have b21520 := hb (x (-3) 9)
          have b21521 := hb (x (-2) 8)
          clear * - r21507 e21508 e21509 e21510 e21511 e21512 e21513 b21514 b21515 b21516 b21517 b21518 b21519 b21520 b21521 d21474 d21465 d20901 d20917 d21380 d21490
          omega
        have d21522 : (x (-8) 6 && x (-8) 12).toNat = 0 := by
          have r21523 := hand1 (x (-8) 6) (x (-8) 12)
          have b21524 := hb (x (-8) 6)
          have b21525 := hb (x (-8) 6 && x (-8) 12)
          clear * - r21523 b21524 b21525 d21506
          omega
        have d21526 : (x (-9) 7).toNat = 0 := by
          have r21527 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21528 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
          have e21529 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
          have e21530 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
          have e21531 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
          have e21532 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
          have e21533 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
          have b21534 := hb (x (-9) 7)
          have b21535 := hb (x (-8) 6)
          have b21536 := hb (x (-7) 5)
          have b21537 := hb (x (-6) 4)
          have b21538 := hb (x (-5) 11)
          have b21539 := hb (x (-4) 10)
          have b21540 := hb (x (-3) 9)
          have b21541 := hb (x (-2) 8)
          clear * - r21527 e21528 e21529 e21530 e21531 e21532 e21533 b21534 b21535 b21536 b21537 b21538 b21539 b21540 b21541 d21474 d21465 d20901 d20917 d21380 d21490 d21506
          omega
        have d21542 : (x (-9) 7 && x (-9) 13).toNat = 0 := by
          have r21543 := hand1 (x (-9) 7) (x (-9) 13)
          have b21544 := hb (x (-9) 7)
          have b21545 := hb (x (-9) 7 && x (-9) 13)
          clear * - r21543 b21544 b21545 d21526
          omega
        have d21546 : (x (-10) 7).toNat = 0 := by
          have r21547 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21548 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
          have e21549 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
          have e21550 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
          have e21551 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
          have e21552 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
          have e21553 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
          have b21554 := hb (x (-10) 7)
          have b21555 := hb (x (-9) 6)
          have b21556 := hb (x (-8) 5)
          have b21557 := hb (x (-7) 4)
          have b21558 := hb (x (-6) 11)
          have b21559 := hb (x (-5) 10)
          have b21560 := hb (x (-4) 9)
          have b21561 := hb (x (-3) 8)
          clear * - r21547 e21548 e21549 e21550 e21551 e21552 e21553 b21554 b21555 b21556 b21557 b21558 b21559 b21560 b21561 d21413 d20853 d20659 d20687 d21417 d21184 d21441
          omega
        have d21562 : (x (-10) 7 && x (-10) 14).toNat = 0 := by
          have r21563 := hand1 (x (-10) 7) (x (-10) 14)
          have b21564 := hb (x (-10) 7)
          have b21565 := hb (x (-10) 7 && x (-10) 14)
          clear * - r21563 b21564 b21565 d21546
          omega
        have d21566 : (x (-11) 8).toNat = 1 := by
          have r21567 : 1 ≤ (x (-3) 7).toNat + (x (-4) 1 && x (-4) 8).toNat + (x (-5) 2 && x (-5) 9).toNat + (x (-6) 3 && x (-6) 10).toNat + (x (-7) 4 && x (-7) 11).toNat + (x (-8) 5 && x (-8) 12).toNat + (x (-9) 6 && x (-9) 13).toNat + (x (-10) 7 && x (-10) 14).toNat + (x (-11) 8).toNat := by have q := hcov7 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21568 := hb (x (-11) 8)
          have b21569 := hb (x (-3) 7)
          have b21570 := hb (x (-4) 1 && x (-4) 8)
          have b21571 := hb (x (-5) 2 && x (-5) 9)
          have b21572 := hb (x (-6) 3 && x (-6) 10)
          have b21573 := hb (x (-7) 4 && x (-7) 11)
          have b21574 := hb (x (-8) 5 && x (-8) 12)
          have b21575 := hb (x (-9) 6 && x (-9) 13)
          have b21576 := hb (x (-10) 7 && x (-10) 14)
          clear * - r21567 b21568 b21569 b21570 b21571 b21572 b21573 b21574 b21575 b21576 d20731 d20849 d20651 d20679 d21095 d21192 d21457 d21562
          omega
        have d21577 : (x (-12) 9).toNat = 0 := by
          have r21578 : (x (-11) 8).toNat + (x (-12) 1 && x (-12) 9).toNat + (x (-13) 2 && x (-13) 10).toNat + (x (-14) 3 && x (-14) 11).toNat + (x (-15) 4 && x (-15) 12).toNat + (x (-16) 5 && x (-16) 13).toNat + (x (-17) 6 && x (-17) 14).toNat + (x (-18) 7).toNat = 1 := by have q := hd8 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21579 : (x (-12) 1 && x (-12) 9).toNat = (x (-12) 9).toNat := handr _ _ (fun h => hp9 (-12) (h))
          have e21580 : (x (-13) 2 && x (-13) 10).toNat = (x (-13) 10).toNat := handr _ _ (fun h => hp10 (-13) (h))
          have e21581 : (x (-14) 3 && x (-14) 11).toNat = (x (-14) 11).toNat := handr _ _ (fun h => hp11 (-14) (h))
          have e21582 : (x (-15) 4 && x (-15) 12).toNat = (x (-15) 4).toNat := handl _ _ (fun h => hp4 (-15) (h))
          have e21583 : (x (-16) 5 && x (-16) 13).toNat = (x (-16) 5).toNat := handl _ _ (fun h => hp5 (-16) (h))
          have e21584 : (x (-17) 6 && x (-17) 14).toNat = (x (-17) 6).toNat := handl _ _ (fun h => hp6 (-17) (h))
          have b21585 := hb (x (-18) 7)
          have b21586 := hb (x (-17) 6)
          have b21587 := hb (x (-16) 5)
          have b21588 := hb (x (-15) 4)
          have b21589 := hb (x (-14) 11)
          have b21590 := hb (x (-13) 10)
          have b21591 := hb (x (-12) 9)
          have b21592 := hb (x (-11) 8)
          clear * - r21578 e21579 e21580 e21581 e21582 e21583 e21584 b21585 b21586 b21587 b21588 b21589 b21590 b21591 b21592 d21566 d21324 d21336
          omega
        have d21593 : (x (-10) 7 && x (-10) 13).toNat = 0 := by
          have r21594 := hand1 (x (-10) 7) (x (-10) 13)
          have b21595 := hb (x (-10) 7)
          have b21596 := hb (x (-10) 7 && x (-10) 13)
          clear * - r21594 b21595 b21596 d21546
          omega
        have d21597 : (x (-11) 8 && x (-11) 14).toNat = 1 := by
          have r21598 : 1 ≤ (x (-3) 6).toNat + (x (-4) 1 && x (-4) 7).toNat + (x (-5) 2 && x (-5) 8).toNat + (x (-6) 3 && x (-6) 9).toNat + (x (-7) 4 && x (-7) 10).toNat + (x (-8) 5 && x (-8) 11).toNat + (x (-9) 6 && x (-9) 12).toNat + (x (-10) 7 && x (-10) 13).toNat + (x (-11) 8 && x (-11) 14).toNat + (x (-12) 9).toNat := by have q := hcov6 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21599 := hb (x (-12) 9)
          have b21600 := hb (x (-3) 6)
          have b21601 := hb (x (-4) 1 && x (-4) 7)
          have b21602 := hb (x (-5) 2 && x (-5) 8)
          have b21603 := hb (x (-6) 3 && x (-6) 9)
          have b21604 := hb (x (-7) 4 && x (-7) 10)
          have b21605 := hb (x (-8) 5 && x (-8) 11)
          have b21606 := hb (x (-9) 6 && x (-9) 12)
          have b21607 := hb (x (-10) 7 && x (-10) 13)
          have b21608 := hb (x (-11) 8 && x (-11) 14)
          clear * - r21598 b21599 b21600 b21601 b21602 b21603 b21604 b21605 b21606 b21607 b21608 d20396 d20771 d20655 d20683 d21437 d21196 d21461 d21593 d21577
          omega
        have d21609 : (x (-11) 14).toNat = 1 := by
          have r21610 := hand2 (x (-11) 8) (x (-11) 14)
          have b21611 := hb (x (-11) 14)
          have b21612 := hb (x (-11) 8 && x (-11) 14)
          clear * - r21610 b21611 b21612 d21597
          omega
        have d21613 : (x (-12) 1).toNat = 0 := by
          have r21614 : (x (-11) 14).toNat + (x (-12) 1).toNat = 1 := by have q := hd14 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21615 := hb (x (-12) 1)
          have b21616 := hb (x (-11) 14)
          clear * - r21614 b21615 b21616 d21609
          omega
        have d21617 : (x (-12) 1 && x (-12) 14).toNat = 0 := by
          have r21618 := hand1 (x (-12) 1) (x (-12) 14)
          have b21619 := hb (x (-12) 1)
          have b21620 := hb (x (-12) 1 && x (-12) 14)
          clear * - r21618 b21619 b21620 d21613
          omega
        have d21621 : (x (-11) 13).toNat = 1 := by
          have r21622 : 1 ≤ (x (-11) 13).toNat + (x (-12) 1 && x (-12) 14).toNat + (x (-13) 2).toNat := by have q := hcov13 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21623 := hb (x (-13) 2)
          have b21624 := hb (x (-11) 13)
          have b21625 := hb (x (-12) 1 && x (-12) 14)
          clear * - r21622 b21623 b21624 b21625 d21617 d21316
          omega
        have d21626 : (x (-11) 1).toNat = 1 := by
          have r21627 : (x (-11) 13).toNat ≤ (x (-11) 1).toNat := himp _ _ (hp13 (-11))
          have b21628 := hb (x (-11) 1)
          have b21629 := hb (x (-11) 13)
          clear * - r21627 b21628 b21629 d21621
          omega
        have d21630 : (x (-10) 14).toNat = 0 := by
          have r21631 : (x (-10) 14).toNat + (x (-11) 1).toNat = 1 := by have q := hd14 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21632 := hb (x (-11) 1)
          have b21633 := hb (x (-10) 14)
          clear * - r21631 b21632 b21633 d21626
          omega
        have d21634 : (x (-10) 5 && x (-10) 14).toNat = 0 := by
          have r21635 := hand2 (x (-10) 5) (x (-10) 14)
          have b21636 := hb (x (-10) 14)
          have b21637 := hb (x (-10) 5 && x (-10) 14)
          clear * - r21635 b21636 b21637 d21630
          omega
        have d21638 : (x (-10) 8 && x (-10) 14).toNat = 0 := by
          have r21639 := hand2 (x (-10) 8) (x (-10) 14)
          have b21640 := hb (x (-10) 14)
          have b21641 := hb (x (-10) 8 && x (-10) 14)
          clear * - r21639 b21640 b21641 d21630
          omega
        have d21642 : (x (-11) 9).toNat = 1 := by
          have r21643 : 1 ≤ (x (-2) 6).toNat + (x (-3) 1 && x (-3) 7).toNat + (x (-4) 2 && x (-4) 8).toNat + (x (-5) 3 && x (-5) 9).toNat + (x (-6) 4 && x (-6) 10).toNat + (x (-7) 5 && x (-7) 11).toNat + (x (-8) 6 && x (-8) 12).toNat + (x (-9) 7 && x (-9) 13).toNat + (x (-10) 8 && x (-10) 14).toNat + (x (-11) 9).toNat := by have q := hcov6 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21644 := hb (x (-11) 9)
          have b21645 := hb (x (-2) 6)
          have b21646 := hb (x (-3) 1 && x (-3) 7)
          have b21647 := hb (x (-4) 2 && x (-4) 8)
          have b21648 := hb (x (-5) 3 && x (-5) 9)
          have b21649 := hb (x (-6) 4 && x (-6) 10)
          have b21650 := hb (x (-7) 5 && x (-7) 11)
          have b21651 := hb (x (-8) 6 && x (-8) 12)
          have b21652 := hb (x (-9) 7 && x (-9) 13)
          have b21653 := hb (x (-10) 8 && x (-10) 14)
          clear * - r21643 b21644 b21645 b21646 b21647 b21648 b21649 b21650 b21651 b21652 b21653 d20711 d20751 d20897 d20913 d21071 d21099 d21522 d21542 d21638
          omega
        have d21654 : (x (-10) 8).toNat = 0 := by
          have r21655 : (x (-10) 8).toNat + (x (-11) 1 && x (-11) 9).toNat + (x (-12) 2 && x (-12) 10).toNat + (x (-13) 3 && x (-13) 11).toNat + (x (-14) 4 && x (-14) 12).toNat + (x (-15) 5 && x (-15) 13).toNat + (x (-16) 6 && x (-16) 14).toNat + (x (-17) 7).toNat = 1 := by have q := hd8 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21656 : (x (-11) 1 && x (-11) 9).toNat = (x (-11) 9).toNat := handr _ _ (fun h => hp9 (-11) (h))
          have e21657 : (x (-12) 2 && x (-12) 10).toNat = (x (-12) 10).toNat := handr _ _ (fun h => hp10 (-12) (h))
          have e21658 : (x (-13) 3 && x (-13) 11).toNat = (x (-13) 11).toNat := handr _ _ (fun h => hp11 (-13) (h))
          have e21659 : (x (-14) 4 && x (-14) 12).toNat = (x (-14) 4).toNat := handl _ _ (fun h => hp4 (-14) (h))
          have e21660 : (x (-15) 5 && x (-15) 13).toNat = (x (-15) 5).toNat := handl _ _ (fun h => hp5 (-15) (h))
          have e21661 : (x (-16) 6 && x (-16) 14).toNat = (x (-16) 6).toNat := handl _ _ (fun h => hp6 (-16) (h))
          have b21662 := hb (x (-17) 7)
          have b21663 := hb (x (-16) 6)
          have b21664 := hb (x (-15) 5)
          have b21665 := hb (x (-14) 4)
          have b21666 := hb (x (-13) 11)
          have b21667 := hb (x (-12) 10)
          have b21668 := hb (x (-11) 9)
          have b21669 := hb (x (-10) 8)
          clear * - r21655 e21656 e21657 e21658 e21659 e21660 e21661 b21662 b21663 b21664 b21665 b21666 b21667 b21668 b21669 d21642
          omega
        have d21670 : (x (-12) 10).toNat = 0 := by
          have r21671 : (x (-10) 8).toNat + (x (-11) 1 && x (-11) 9).toNat + (x (-12) 2 && x (-12) 10).toNat + (x (-13) 3 && x (-13) 11).toNat + (x (-14) 4 && x (-14) 12).toNat + (x (-15) 5 && x (-15) 13).toNat + (x (-16) 6 && x (-16) 14).toNat + (x (-17) 7).toNat = 1 := by have q := hd8 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21672 : (x (-11) 1 && x (-11) 9).toNat = (x (-11) 9).toNat := handr _ _ (fun h => hp9 (-11) (h))
          have e21673 : (x (-12) 2 && x (-12) 10).toNat = (x (-12) 10).toNat := handr _ _ (fun h => hp10 (-12) (h))
          have e21674 : (x (-13) 3 && x (-13) 11).toNat = (x (-13) 11).toNat := handr _ _ (fun h => hp11 (-13) (h))
          have e21675 : (x (-14) 4 && x (-14) 12).toNat = (x (-14) 4).toNat := handl _ _ (fun h => hp4 (-14) (h))
          have e21676 : (x (-15) 5 && x (-15) 13).toNat = (x (-15) 5).toNat := handl _ _ (fun h => hp5 (-15) (h))
          have e21677 : (x (-16) 6 && x (-16) 14).toNat = (x (-16) 6).toNat := handl _ _ (fun h => hp6 (-16) (h))
          have b21678 := hb (x (-17) 7)
          have b21679 := hb (x (-16) 6)
          have b21680 := hb (x (-15) 5)
          have b21681 := hb (x (-14) 4)
          have b21682 := hb (x (-13) 11)
          have b21683 := hb (x (-12) 10)
          have b21684 := hb (x (-11) 9)
          have b21685 := hb (x (-10) 8)
          clear * - r21671 e21672 e21673 e21674 e21675 e21676 e21677 b21678 b21679 b21680 b21681 b21682 b21683 b21684 b21685 d21654 d21642
          omega
        have d21686 : (x (-13) 11).toNat = 0 := by
          have r21687 : (x (-10) 8).toNat + (x (-11) 1 && x (-11) 9).toNat + (x (-12) 2 && x (-12) 10).toNat + (x (-13) 3 && x (-13) 11).toNat + (x (-14) 4 && x (-14) 12).toNat + (x (-15) 5 && x (-15) 13).toNat + (x (-16) 6 && x (-16) 14).toNat + (x (-17) 7).toNat = 1 := by have q := hd8 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21688 : (x (-11) 1 && x (-11) 9).toNat = (x (-11) 9).toNat := handr _ _ (fun h => hp9 (-11) (h))
          have e21689 : (x (-12) 2 && x (-12) 10).toNat = (x (-12) 10).toNat := handr _ _ (fun h => hp10 (-12) (h))
          have e21690 : (x (-13) 3 && x (-13) 11).toNat = (x (-13) 11).toNat := handr _ _ (fun h => hp11 (-13) (h))
          have e21691 : (x (-14) 4 && x (-14) 12).toNat = (x (-14) 4).toNat := handl _ _ (fun h => hp4 (-14) (h))
          have e21692 : (x (-15) 5 && x (-15) 13).toNat = (x (-15) 5).toNat := handl _ _ (fun h => hp5 (-15) (h))
          have e21693 : (x (-16) 6 && x (-16) 14).toNat = (x (-16) 6).toNat := handl _ _ (fun h => hp6 (-16) (h))
          have b21694 := hb (x (-17) 7)
          have b21695 := hb (x (-16) 6)
          have b21696 := hb (x (-15) 5)
          have b21697 := hb (x (-14) 4)
          have b21698 := hb (x (-13) 11)
          have b21699 := hb (x (-12) 10)
          have b21700 := hb (x (-11) 9)
          have b21701 := hb (x (-10) 8)
          clear * - r21687 e21688 e21689 e21690 e21691 e21692 e21693 b21694 b21695 b21696 b21697 b21698 b21699 b21700 b21701 d21654 d21642 d21670
          omega
        have d21702 : (x (-14) 4).toNat = 0 := by
          have r21703 : (x (-10) 8).toNat + (x (-11) 1 && x (-11) 9).toNat + (x (-12) 2 && x (-12) 10).toNat + (x (-13) 3 && x (-13) 11).toNat + (x (-14) 4 && x (-14) 12).toNat + (x (-15) 5 && x (-15) 13).toNat + (x (-16) 6 && x (-16) 14).toNat + (x (-17) 7).toNat = 1 := by have q := hd8 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21704 : (x (-11) 1 && x (-11) 9).toNat = (x (-11) 9).toNat := handr _ _ (fun h => hp9 (-11) (h))
          have e21705 : (x (-12) 2 && x (-12) 10).toNat = (x (-12) 10).toNat := handr _ _ (fun h => hp10 (-12) (h))
          have e21706 : (x (-13) 3 && x (-13) 11).toNat = (x (-13) 11).toNat := handr _ _ (fun h => hp11 (-13) (h))
          have e21707 : (x (-14) 4 && x (-14) 12).toNat = (x (-14) 4).toNat := handl _ _ (fun h => hp4 (-14) (h))
          have e21708 : (x (-15) 5 && x (-15) 13).toNat = (x (-15) 5).toNat := handl _ _ (fun h => hp5 (-15) (h))
          have e21709 : (x (-16) 6 && x (-16) 14).toNat = (x (-16) 6).toNat := handl _ _ (fun h => hp6 (-16) (h))
          have b21710 := hb (x (-17) 7)
          have b21711 := hb (x (-16) 6)
          have b21712 := hb (x (-15) 5)
          have b21713 := hb (x (-14) 4)
          have b21714 := hb (x (-13) 11)
          have b21715 := hb (x (-12) 10)
          have b21716 := hb (x (-11) 9)
          have b21717 := hb (x (-10) 8)
          clear * - r21703 e21704 e21705 e21706 e21707 e21708 e21709 b21710 b21711 b21712 b21713 b21714 b21715 b21716 b21717 d21654 d21642 d21670 d21686
          omega
        have d21718 : (x (-14) 4 && x (-14) 14).toNat = 0 := by
          have r21719 := hand1 (x (-14) 4) (x (-14) 14)
          have b21720 := hb (x (-14) 4)
          have b21721 := hb (x (-14) 4 && x (-14) 14)
          clear * - r21719 b21720 b21721 d21702
          omega
        have d21722 : (x (-15) 5).toNat = 0 := by
          have r21723 : (x (-10) 8).toNat + (x (-11) 1 && x (-11) 9).toNat + (x (-12) 2 && x (-12) 10).toNat + (x (-13) 3 && x (-13) 11).toNat + (x (-14) 4 && x (-14) 12).toNat + (x (-15) 5 && x (-15) 13).toNat + (x (-16) 6 && x (-16) 14).toNat + (x (-17) 7).toNat = 1 := by have q := hd8 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21724 : (x (-11) 1 && x (-11) 9).toNat = (x (-11) 9).toNat := handr _ _ (fun h => hp9 (-11) (h))
          have e21725 : (x (-12) 2 && x (-12) 10).toNat = (x (-12) 10).toNat := handr _ _ (fun h => hp10 (-12) (h))
          have e21726 : (x (-13) 3 && x (-13) 11).toNat = (x (-13) 11).toNat := handr _ _ (fun h => hp11 (-13) (h))
          have e21727 : (x (-14) 4 && x (-14) 12).toNat = (x (-14) 4).toNat := handl _ _ (fun h => hp4 (-14) (h))
          have e21728 : (x (-15) 5 && x (-15) 13).toNat = (x (-15) 5).toNat := handl _ _ (fun h => hp5 (-15) (h))
          have e21729 : (x (-16) 6 && x (-16) 14).toNat = (x (-16) 6).toNat := handl _ _ (fun h => hp6 (-16) (h))
          have b21730 := hb (x (-17) 7)
          have b21731 := hb (x (-16) 6)
          have b21732 := hb (x (-15) 5)
          have b21733 := hb (x (-14) 4)
          have b21734 := hb (x (-13) 11)
          have b21735 := hb (x (-12) 10)
          have b21736 := hb (x (-11) 9)
          have b21737 := hb (x (-10) 8)
          clear * - r21723 e21724 e21725 e21726 e21727 e21728 e21729 b21730 b21731 b21732 b21733 b21734 b21735 b21736 b21737 d21654 d21642 d21670 d21686 d21702
          omega
        have d21738 : (x (-10) 2).toNat = 0 := by
          have r21739 : (x (-10) 2).toNat ≤ (x (-10) 14).toNat := himp _ _ (hp2 (-10))
          have b21740 := hb (x (-10) 2)
          have b21741 := hb (x (-10) 14)
          clear * - r21739 b21740 b21741 d21630
          omega
        have d21742 : (x (-10) 10).toNat = 0 := by
          have r21743 : (x (-10) 10).toNat ≤ (x (-10) 2).toNat := himp _ _ (hp10 (-10))
          have b21744 := hb (x (-10) 2)
          have b21745 := hb (x (-10) 10)
          clear * - r21743 b21744 b21745 d21738
          omega
        have d21746 : (x (-9) 1 && x (-9) 14).toNat = 1 := by
          have r21747 : 1 ≤ (x (-8) 13).toNat + (x (-9) 1 && x (-9) 14).toNat + (x (-10) 2).toNat := by have q := hcov13 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21748 := hb (x (-10) 2)
          have b21749 := hb (x (-8) 13)
          have b21750 := hb (x (-9) 1 && x (-9) 14)
          clear * - r21747 b21748 b21749 b21750 d21176 d21738
          omega
        have d21751 : (x (-9) 14).toNat = 1 := by
          have r21752 := hand2 (x (-9) 1) (x (-9) 14)
          have b21753 := hb (x (-9) 14)
          have b21754 := hb (x (-9) 1 && x (-9) 14)
          clear * - r21752 b21753 b21754 d21746
          omega
        have d21755 : (x (-10) 1).toNat = 0 := by
          have r21756 : (x (-9) 14).toNat + (x (-10) 1).toNat = 1 := by have q := hd14 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21757 := hb (x (-10) 1)
          have b21758 := hb (x (-9) 14)
          clear * - r21756 b21757 b21758 d21751
          omega
        have d21759 : (x (-10) 13).toNat = 0 := by
          have r21760 : (x (-10) 13).toNat ≤ (x (-10) 1).toNat := himp _ _ (hp13 (-10))
          have b21761 := hb (x (-10) 1)
          have b21762 := hb (x (-10) 13)
          clear * - r21760 b21761 b21762 d21755
          omega
        have d21763 : (x (-10) 5).toNat = 0 := by
          have r21764 : (x (-10) 5).toNat ≤ (x (-10) 13).toNat := himp _ _ (hp5 (-10))
          have b21765 := hb (x (-10) 5)
          have b21766 := hb (x (-10) 13)
          clear * - r21764 b21765 b21766 d21759
          omega
        have d21767 : (x (-10) 12).toNat = 0 := by
          have r21768 : (x (-10) 12).toNat + (x (-11) 1 && x (-11) 13).toNat + (x (-12) 2 && x (-12) 14).toNat + (x (-13) 3).toNat = 1 := by have q := hd12 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21769 : (x (-11) 1 && x (-11) 13).toNat = (x (-11) 13).toNat := handr _ _ (fun h => hp13 (-11) (h))
          have e21770 : (x (-12) 2 && x (-12) 14).toNat = (x (-12) 2).toNat := handl _ _ (fun h => hp2 (-12) (h))
          have b21771 := hb (x (-13) 3)
          have b21772 := hb (x (-12) 2)
          have b21773 := hb (x (-11) 13)
          have b21774 := hb (x (-10) 12)
          clear * - r21768 e21769 e21770 b21771 b21772 b21773 b21774 d21621
          omega
        have d21775 : (x (-12) 2).toNat = 0 := by
          have r21776 : (x (-10) 12).toNat + (x (-11) 1 && x (-11) 13).toNat + (x (-12) 2 && x (-12) 14).toNat + (x (-13) 3).toNat = 1 := by have q := hd12 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21777 : (x (-11) 1 && x (-11) 13).toNat = (x (-11) 13).toNat := handr _ _ (fun h => hp13 (-11) (h))
          have e21778 : (x (-12) 2 && x (-12) 14).toNat = (x (-12) 2).toNat := handl _ _ (fun h => hp2 (-12) (h))
          have b21779 := hb (x (-13) 3)
          have b21780 := hb (x (-12) 2)
          have b21781 := hb (x (-11) 13)
          have b21782 := hb (x (-10) 12)
          clear * - r21776 e21777 e21778 b21779 b21780 b21781 b21782 d21767 d21621
          omega
        have d21783 : (x (-12) 2 && x (-12) 12).toNat = 0 := by
          have r21784 := hand1 (x (-12) 2) (x (-12) 12)
          have b21785 := hb (x (-12) 2)
          have b21786 := hb (x (-12) 2 && x (-12) 12)
          clear * - r21784 b21785 b21786 d21775
          omega
        have d21787 : (x (-13) 3).toNat = 0 := by
          have r21788 : (x (-10) 12).toNat + (x (-11) 1 && x (-11) 13).toNat + (x (-12) 2 && x (-12) 14).toNat + (x (-13) 3).toNat = 1 := by have q := hd12 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21789 : (x (-11) 1 && x (-11) 13).toNat = (x (-11) 13).toNat := handr _ _ (fun h => hp13 (-11) (h))
          have e21790 : (x (-12) 2 && x (-12) 14).toNat = (x (-12) 2).toNat := handl _ _ (fun h => hp2 (-12) (h))
          have b21791 := hb (x (-13) 3)
          have b21792 := hb (x (-12) 2)
          have b21793 := hb (x (-11) 13)
          have b21794 := hb (x (-10) 12)
          clear * - r21788 e21789 e21790 b21791 b21792 b21793 b21794 d21767 d21621 d21775
          omega
        have d21795 : (x (-13) 3 && x (-13) 13).toNat = 0 := by
          have r21796 := hand1 (x (-13) 3) (x (-13) 13)
          have b21797 := hb (x (-13) 3)
          have b21798 := hb (x (-13) 3 && x (-13) 13)
          clear * - r21796 b21797 b21798 d21787
          omega
        have d21799 : (x (-11) 1 && x (-11) 11).toNat = 1 := by
          have r21800 : 1 ≤ (x (-10) 10).toNat + (x (-11) 1 && x (-11) 11).toNat + (x (-12) 2 && x (-12) 12).toNat + (x (-13) 3 && x (-13) 13).toNat + (x (-14) 4 && x (-14) 14).toNat + (x (-15) 5).toNat := by have q := hcov10 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21801 := hb (x (-15) 5)
          have b21802 := hb (x (-10) 10)
          have b21803 := hb (x (-11) 1 && x (-11) 11)
          have b21804 := hb (x (-12) 2 && x (-12) 12)
          have b21805 := hb (x (-13) 3 && x (-13) 13)
          have b21806 := hb (x (-14) 4 && x (-14) 14)
          clear * - r21800 b21801 b21802 b21803 b21804 b21805 b21806 d21742 d21783 d21795 d21718 d21722
          omega
        have d21807 : (x (-11) 11).toNat = 1 := by
          have r21808 := hand2 (x (-11) 1) (x (-11) 11)
          have b21809 := hb (x (-11) 11)
          have b21810 := hb (x (-11) 1 && x (-11) 11)
          clear * - r21808 b21809 b21810 d21799
          omega
        have d21811 : (x (-11) 3).toNat = 1 := by
          have r21812 : (x (-11) 11).toNat ≤ (x (-11) 3).toNat := himp _ _ (hp11 (-11))
          have b21813 := hb (x (-11) 3)
          have b21814 := hb (x (-11) 11)
          clear * - r21812 b21813 b21814 d21807
          omega
        have d21815 : (x (-8) 12).toNat = 0 := by
          have r21816 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21817 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
          have e21818 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
          have b21819 := hb (x (-11) 3)
          have b21820 := hb (x (-10) 2)
          have b21821 := hb (x (-9) 13)
          have b21822 := hb (x (-8) 12)
          clear * - r21816 e21817 e21818 b21819 b21820 b21821 b21822 d21738 d21811
          omega
        have d21823 : (x (-9) 13).toNat = 0 := by
          have r21824 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21825 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
          have e21826 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
          have b21827 := hb (x (-11) 3)
          have b21828 := hb (x (-10) 2)
          have b21829 := hb (x (-9) 13)
          have b21830 := hb (x (-8) 12)
          clear * - r21824 e21825 e21826 b21827 b21828 b21829 b21830 d21815 d21738 d21811
          omega
        have d21831 : (x (-9) 4 && x (-9) 13).toNat = 0 := by
          have r21832 := hand2 (x (-9) 4) (x (-9) 13)
          have b21833 := hb (x (-9) 13)
          have b21834 := hb (x (-9) 4 && x (-9) 13)
          clear * - r21832 b21833 b21834 d21823
          omega
        have d21835 : (x (-11) 6).toNat = 1 := by
          have r21836 : 1 ≤ (x (-5) 9).toNat + (x (-6) 1 && x (-6) 10).toNat + (x (-7) 2 && x (-7) 11).toNat + (x (-8) 3 && x (-8) 12).toNat + (x (-9) 4 && x (-9) 13).toNat + (x (-10) 5 && x (-10) 14).toNat + (x (-11) 6).toNat := by have q := hcov9 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21837 := hb (x (-11) 6)
          have b21838 := hb (x (-5) 9)
          have b21839 := hb (x (-6) 1 && x (-6) 10)
          have b21840 := hb (x (-7) 2 && x (-7) 11)
          have b21841 := hb (x (-8) 3 && x (-8) 12)
          have b21842 := hb (x (-9) 4 && x (-9) 13)
          have b21843 := hb (x (-10) 5 && x (-10) 14)
          clear * - r21836 b21837 b21838 b21839 b21840 b21841 b21842 b21843 d21035 d21067 d21091 d21364 d21831 d21634
          omega
        have d21844 : (x (-5) 8).toNat = 0 := by
          have r21845 : (x (-5) 8).toNat + (x (-6) 1 && x (-6) 9).toNat + (x (-7) 2 && x (-7) 10).toNat + (x (-8) 3 && x (-8) 11).toNat + (x (-9) 4 && x (-9) 12).toNat + (x (-10) 5 && x (-10) 13).toNat + (x (-11) 6 && x (-11) 14).toNat + (x (-12) 7).toNat = 1 := by have q := hd8 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21846 : (x (-6) 1 && x (-6) 9).toNat = (x (-6) 9).toNat := handr _ _ (fun h => hp9 (-6) (h))
          have e21847 : (x (-7) 2 && x (-7) 10).toNat = (x (-7) 10).toNat := handr _ _ (fun h => hp10 (-7) (h))
          have e21848 : (x (-8) 3 && x (-8) 11).toNat = (x (-8) 11).toNat := handr _ _ (fun h => hp11 (-8) (h))
          have e21849 : (x (-9) 4 && x (-9) 12).toNat = (x (-9) 4).toNat := handl _ _ (fun h => hp4 (-9) (h))
          have e21850 : (x (-10) 5 && x (-10) 13).toNat = (x (-10) 5).toNat := handl _ _ (fun h => hp5 (-10) (h))
          have e21851 : (x (-11) 6 && x (-11) 14).toNat = (x (-11) 6).toNat := handl _ _ (fun h => hp6 (-11) (h))
          have b21852 := hb (x (-12) 7)
          have b21853 := hb (x (-11) 6)
          have b21854 := hb (x (-10) 5)
          have b21855 := hb (x (-9) 4)
          have b21856 := hb (x (-8) 11)
          have b21857 := hb (x (-7) 10)
          have b21858 := hb (x (-6) 9)
          have b21859 := hb (x (-5) 8)
          clear * - r21845 e21846 e21847 e21848 e21849 e21850 e21851 b21852 b21853 b21854 b21855 b21856 b21857 b21858 b21859 d21397 d21368 d21763 d21835
          omega
        have d21860 : (x (-5) 8 && x (-5) 14).toNat = 0 := by
          have r21861 := hand1 (x (-5) 8) (x (-5) 14)
          have b21862 := hb (x (-5) 8)
          have b21863 := hb (x (-5) 8 && x (-5) 14)
          clear * - r21861 b21862 b21863 d21844
          omega
        have d21864 : (x 2 1 && x 2 7).toNat = 1 := by
          have r21865 : 1 ≤ (x 3 6).toNat + (x 2 1 && x 2 7).toNat + (x 1 2 && x 1 8).toNat + (x 0 3 && x 0 9).toNat + (x (-1) 4 && x (-1) 10).toNat + (x (-2) 5 && x (-2) 11).toNat + (x (-3) 6 && x (-3) 12).toNat + (x (-4) 7 && x (-4) 13).toNat + (x (-5) 8 && x (-5) 14).toNat + (x (-6) 9).toNat := by have q := hcov6 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21866 := hb (x (-6) 9)
          have b21867 := hb (x 3 6)
          have b21868 := hb (x 2 1 && x 2 7)
          have b21869 := hb (x 1 2 && x 1 8)
          have b21870 := hb (x 0 3 && x 0 9)
          have b21871 := hb (x (-1) 4 && x (-1) 10)
          have b21872 := hb (x (-2) 5 && x (-2) 11)
          have b21873 := hb (x (-3) 6 && x (-3) 12)
          have b21874 := hb (x (-4) 7 && x (-4) 13)
          have b21875 := hb (x (-5) 8 && x (-5) 14)
          clear * - r21865 b21866 b21867 b21868 b21869 b21870 b21871 b21872 b21873 b21874 b21875 g28 g52 d19310 g53 g54 d20412 d20627 d21860 d21397
          omega
        have d21876 : (x 2 7).toNat = 1 := by
          have r21877 := hand2 (x 2 1) (x 2 7)
          have b21878 := hb (x 2 7)
          have b21879 := hb (x 2 1 && x 2 7)
          clear * - r21877 b21878 b21879 d21864
          omega
        have d21880 : (x 9 8).toNat = 0 := by
          have r21881 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21882 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
          have e21883 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
          have e21884 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
          have e21885 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
          have e21886 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
          have e21887 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
          have b21888 := hb (x 2 7)
          have b21889 := hb (x 3 6)
          have b21890 := hb (x 4 5)
          have b21891 := hb (x 5 4)
          have b21892 := hb (x 6 11)
          have b21893 := hb (x 7 10)
          have b21894 := hb (x 8 9)
          have b21895 := hb (x 9 8)
          clear * - r21881 e21882 e21883 e21884 e21885 e21886 e21887 b21888 b21889 b21890 b21891 b21892 b21893 b21894 b21895 g28 d21876
          omega
        have d21896 : (x 8 9).toNat = 0 := by
          have r21897 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21898 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
          have e21899 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
          have e21900 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
          have e21901 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
          have e21902 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
          have e21903 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
          have b21904 := hb (x 2 7)
          have b21905 := hb (x 3 6)
          have b21906 := hb (x 4 5)
          have b21907 := hb (x 5 4)
          have b21908 := hb (x 6 11)
          have b21909 := hb (x 7 10)
          have b21910 := hb (x 8 9)
          have b21911 := hb (x 9 8)
          clear * - r21897 e21898 e21899 e21900 e21901 e21902 e21903 b21904 b21905 b21906 b21907 b21908 b21909 b21910 b21911 d21880 g28 d21876
          omega
        have d21912 : (x 8 3 && x 8 9).toNat = 0 := by
          have r21913 := hand2 (x 8 3) (x 8 9)
          have b21914 := hb (x 8 9)
          have b21915 := hb (x 8 3 && x 8 9)
          clear * - r21913 b21914 b21915 d21896
          omega
        have d21916 : (x 7 10).toNat = 0 := by
          have r21917 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21918 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
          have e21919 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
          have e21920 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
          have e21921 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
          have e21922 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
          have e21923 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
          have b21924 := hb (x 2 7)
          have b21925 := hb (x 3 6)
          have b21926 := hb (x 4 5)
          have b21927 := hb (x 5 4)
          have b21928 := hb (x 6 11)
          have b21929 := hb (x 7 10)
          have b21930 := hb (x 8 9)
          have b21931 := hb (x 9 8)
          clear * - r21917 e21918 e21919 e21920 e21921 e21922 e21923 b21924 b21925 b21926 b21927 b21928 b21929 b21930 b21931 d21880 d21896 g28 d21876
          omega
        have d21932 : (x 6 11).toNat = 0 := by
          have r21933 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21934 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
          have e21935 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
          have e21936 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
          have e21937 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
          have e21938 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
          have e21939 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
          have b21940 := hb (x 2 7)
          have b21941 := hb (x 3 6)
          have b21942 := hb (x 4 5)
          have b21943 := hb (x 5 4)
          have b21944 := hb (x 6 11)
          have b21945 := hb (x 7 10)
          have b21946 := hb (x 8 9)
          have b21947 := hb (x 9 8)
          clear * - r21933 e21934 e21935 e21936 e21937 e21938 e21939 b21940 b21941 b21942 b21943 b21944 b21945 b21946 b21947 d21880 d21896 d21916 g28 d21876
          omega
        have d21948 : (x 6 1 && x 6 11).toNat = 0 := by
          have r21949 := hand2 (x 6 1) (x 6 11)
          have b21950 := hb (x 6 11)
          have b21951 := hb (x 6 1 && x 6 11)
          clear * - r21949 b21950 b21951 d21932
          omega
        have d21952 : (x 4 3 && x 4 13).toNat = 1 := by
          have r21953 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21954 := hb (x 2 5)
          have b21955 := hb (x 7 10)
          have b21956 := hb (x 6 1 && x 6 11)
          have b21957 := hb (x 5 2 && x 5 12)
          have b21958 := hb (x 4 3 && x 4 13)
          have b21959 := hb (x 3 4 && x 3 14)
          clear * - r21953 b21954 b21955 b21956 b21957 b21958 b21959 d21916 d21948 g99 g100 g24
          omega
        have d21960 : (x 4 13).toNat = 1 := by
          have r21961 := hand2 (x 4 3) (x 4 13)
          have b21962 := hb (x 4 13)
          have b21963 := hb (x 4 3 && x 4 13)
          clear * - r21961 b21962 b21963 d21952
          omega
        have d21964 : (x 5 12).toNat = 0 := by
          have r21965 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21966 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e21967 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b21968 := hb (x 2 3)
          have b21969 := hb (x 3 2)
          have b21970 := hb (x 4 13)
          have b21971 := hb (x 5 12)
          clear * - r21965 e21966 e21967 b21968 b21969 b21970 b21971 d21960 g26
          omega
        have d21972 : (x 2 3).toNat = 0 := by
          have r21973 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21974 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e21975 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b21976 := hb (x 2 3)
          have b21977 := hb (x 3 2)
          have b21978 := hb (x 4 13)
          have b21979 := hb (x 5 12)
          clear * - r21973 e21974 e21975 b21976 b21977 b21978 b21979 d21964 d21960 g26
          omega
        have d21980 : (x 2 3 && x 2 14).toNat = 0 := by
          have r21981 := hand1 (x 2 3) (x 2 14)
          have b21982 := hb (x 2 3)
          have b21983 := hb (x 2 3 && x 2 14)
          clear * - r21981 b21982 b21983 d21972
          omega
        have d21984 : (x 5 11).toNat = 1 := by
          have r21985 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21986 := hb (x 1 4)
          have b21987 := hb (x 5 11)
          have b21988 := hb (x 4 1 && x 4 12)
          have b21989 := hb (x 3 2 && x 3 13)
          have b21990 := hb (x 2 3 && x 2 14)
          clear * - r21985 b21986 b21987 b21988 b21989 b21990 d20441 g105 d21980 g16
          omega
        have d21991 : (x 5 3).toNat = 1 := by
          have r21992 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
          have b21993 := hb (x 5 3)
          have b21994 := hb (x 5 11)
          clear * - r21992 b21993 b21994 d21984
          omega
        have d21995 : (x 8 12).toNat = 0 := by
          have r21996 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21997 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
          have e21998 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
          have b21999 := hb (x 5 3)
          have b22000 := hb (x 6 2)
          have b22001 := hb (x 7 13)
          have b22002 := hb (x 8 12)
          clear * - r21996 e21997 e21998 b21999 b22000 b22001 b22002 d21991
          omega
        have d22003 : (x 8 4).toNat = 0 := by
          have r22004 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
          have b22005 := hb (x 8 4)
          have b22006 := hb (x 8 12)
          clear * - r22004 b22005 b22006 d21995
          omega
        have d22007 : (x 9 3 && x 9 14).toNat = 1 := by
          have r22008 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b22009 := hb (x 8 4)
          have b22010 := hb (x 12 11)
          have b22011 := hb (x 11 1 && x 11 12)
          have b22012 := hb (x 10 2 && x 10 13)
          have b22013 := hb (x 9 3 && x 9 14)
          clear * - r22008 b22009 b22010 b22011 b22012 b22013 d20984 d20476 d20504 d22003
          omega
        have d22014 : (x 9 14).toNat = 1 := by
          have r22015 := hand2 (x 9 3) (x 9 14)
          have b22016 := hb (x 9 14)
          have b22017 := hb (x 9 3 && x 9 14)
          clear * - r22015 b22016 b22017 d22007
          omega
        have d22018 : (x 8 1).toNat = 0 := by
          have r22019 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b22020 := hb (x 8 1)
          have b22021 := hb (x 9 14)
          clear * - r22019 b22020 b22021 d22014
          omega
        have d22022 : (x 8 13).toNat = 0 := by
          have r22023 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
          have b22024 := hb (x 8 1)
          have b22025 := hb (x 8 13)
          clear * - r22023 b22024 b22025 d22018
          omega
        have d22026 : (x 8 3 && x 8 13).toNat = 0 := by
          have r22027 := hand2 (x 8 3) (x 8 13)
          have b22028 := hb (x 8 13)
          have b22029 := hb (x 8 3 && x 8 13)
          clear * - r22027 b22028 b22029 d22022
          omega
        have d22030 : (x 8 6 && x 8 13).toNat = 0 := by
          have r22031 := hand2 (x 8 6) (x 8 13)
          have b22032 := hb (x 8 13)
          have b22033 := hb (x 8 6 && x 8 13)
          clear * - r22031 b22032 b22033 d22022
          omega
        have d22034 : (x 8 7 && x 8 13).toNat = 0 := by
          have r22035 := hand2 (x 8 7) (x 8 13)
          have b22036 := hb (x 8 13)
          have b22037 := hb (x 8 7 && x 8 13)
          clear * - r22035 b22036 b22037 d22022
          omega
        have d22038 : (x 8 5).toNat = 0 := by
          have r22039 : (x 8 5).toNat ≤ (x 8 13).toNat := himp _ _ (hp5 8)
          have b22040 := hb (x 8 5)
          have b22041 := hb (x 8 13)
          clear * - r22039 b22040 b22041 d22022
          omega
        have d22042 : (x 9 4 && x 9 14).toNat = 1 := by
          have r22043 : 1 ≤ (x 13 10).toNat + (x 12 1 && x 12 11).toNat + (x 11 2 && x 11 12).toNat + (x 10 3 && x 10 13).toNat + (x 9 4 && x 9 14).toNat + (x 8 5).toNat := by have q := hcov10 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b22044 := hb (x 8 5)
          have b22045 := hb (x 13 10)
          have b22046 := hb (x 12 1 && x 12 11)
          have b22047 := hb (x 11 2 && x 11 12)
          have b22048 := hb (x 10 3 && x 10 13)
          have b22049 := hb (x 9 4 && x 9 14)
          clear * - r22043 b22044 b22045 b22046 b22047 b22048 b22049 d20968 d21000 d20480 d20508 d22038
          omega
        have d22050 : (x 9 4).toNat = 1 := by
          have r22051 := hand1 (x 9 4) (x 9 14)
          have b22052 := hb (x 9 4)
          have b22053 := hb (x 9 4 && x 9 14)
          clear * - r22051 b22052 b22053 d22042
          omega
        have d22054 : (x 13 8).toNat = 0 := by
          have r22055 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22056 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
          have e22057 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
          have e22058 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
          have e22059 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
          have e22060 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
          have e22061 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
          have b22062 := hb (x 6 7)
          have b22063 := hb (x 7 6)
          have b22064 := hb (x 8 5)
          have b22065 := hb (x 9 4)
          have b22066 := hb (x 10 11)
          have b22067 := hb (x 11 10)
          have b22068 := hb (x 12 9)
          have b22069 := hb (x 13 8)
          clear * - r22055 e22056 e22057 e22058 e22059 e22060 e22061 b22062 b22063 b22064 b22065 b22066 b22067 b22068 b22069 d22050 d22038
          omega
        have d22070 : (x 13 1 && x 13 8).toNat = 0 := by
          have r22071 := hand2 (x 13 1) (x 13 8)
          have b22072 := hb (x 13 8)
          have b22073 := hb (x 13 1 && x 13 8)
          clear * - r22071 b22072 b22073 d22054
          omega
        have d22074 : (x 13 2 && x 13 8).toNat = 0 := by
          have r22075 := hand2 (x 13 2) (x 13 8)
          have b22076 := hb (x 13 8)
          have b22077 := hb (x 13 2 && x 13 8)
          clear * - r22075 b22076 b22077 d22054
          omega
        have d22078 : (x 12 9).toNat = 0 := by
          have r22079 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22080 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
          have e22081 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
          have e22082 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
          have e22083 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
          have e22084 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
          have e22085 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
          have b22086 := hb (x 6 7)
          have b22087 := hb (x 7 6)
          have b22088 := hb (x 8 5)
          have b22089 := hb (x 9 4)
          have b22090 := hb (x 10 11)
          have b22091 := hb (x 11 10)
          have b22092 := hb (x 12 9)
          have b22093 := hb (x 13 8)
          clear * - r22079 e22080 e22081 e22082 e22083 e22084 e22085 b22086 b22087 b22088 b22089 b22090 b22091 b22092 b22093 d22054 d22050 d22038
          omega
        have d22094 : (x 12 2 && x 12 9).toNat = 0 := by
          have r22095 := hand2 (x 12 2) (x 12 9)
          have b22096 := hb (x 12 9)
          have b22097 := hb (x 12 2 && x 12 9)
          clear * - r22095 b22096 b22097 d22078
          omega
        have d22098 : (x 12 3 && x 12 9).toNat = 0 := by
          have r22099 := hand2 (x 12 3) (x 12 9)
          have b22100 := hb (x 12 9)
          have b22101 := hb (x 12 3 && x 12 9)
          clear * - r22099 b22100 b22101 d22078
          omega
        have d22102 : (x 11 10).toNat = 0 := by
          have r22103 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22104 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
          have e22105 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
          have e22106 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
          have e22107 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
          have e22108 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
          have e22109 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
          have b22110 := hb (x 6 7)
          have b22111 := hb (x 7 6)
          have b22112 := hb (x 8 5)
          have b22113 := hb (x 9 4)
          have b22114 := hb (x 10 11)
          have b22115 := hb (x 11 10)
          have b22116 := hb (x 12 9)
          have b22117 := hb (x 13 8)
          clear * - r22103 e22104 e22105 e22106 e22107 e22108 e22109 b22110 b22111 b22112 b22113 b22114 b22115 b22116 b22117 d22054 d22078 d22050 d22038
          omega
        have d22118 : (x 11 3 && x 11 10).toNat = 0 := by
          have r22119 := hand2 (x 11 3) (x 11 10)
          have b22120 := hb (x 11 10)
          have b22121 := hb (x 11 3 && x 11 10)
          clear * - r22119 b22120 b22121 d22102
          omega
        have d22122 : (x 10 1 && x 10 11).toNat = 1 := by
          have r22123 : 1 ≤ (x 11 10).toNat + (x 10 1 && x 10 11).toNat + (x 9 2 && x 9 12).toNat + (x 8 3 && x 8 13).toNat + (x 7 4 && x 7 14).toNat + (x 6 5).toNat := by have q := hcov10 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b22124 := hb (x 6 5)
          have b22125 := hb (x 11 10)
          have b22126 := hb (x 10 1 && x 10 11)
          have b22127 := hb (x 9 2 && x 9 12)
          have b22128 := hb (x 8 3 && x 8 13)
          have b22129 := hb (x 7 4 && x 7 14)
          clear * - r22123 b22124 b22125 b22126 b22127 b22128 b22129 d22102 d20528 d22026 g101 g37
          omega
        have d22130 : (x 10 11).toNat = 1 := by
          have r22131 := hand2 (x 10 1) (x 10 11)
          have b22132 := hb (x 10 11)
          have b22133 := hb (x 10 1 && x 10 11)
          clear * - r22131 b22132 b22133 d22122
          omega
        have d22134 : (x 10 3).toNat = 1 := by
          have r22135 : (x 10 11).toNat ≤ (x 10 3).toNat := himp _ _ (hp11 10)
          have b22136 := hb (x 10 3)
          have b22137 := hb (x 10 11)
          clear * - r22135 b22136 b22137 d22130
          omega
        have d22138 : (x 13 12).toNat = 0 := by
          have r22139 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22140 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
          have e22141 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
          have b22142 := hb (x 10 3)
          have b22143 := hb (x 11 2)
          have b22144 := hb (x 12 13)
          have b22145 := hb (x 13 12)
          clear * - r22139 e22140 e22141 b22142 b22143 b22144 b22145 d22134
          omega
        have d22146 : (x 13 2 && x 13 12).toNat = 0 := by
          have r22147 := hand2 (x 13 2) (x 13 12)
          have b22148 := hb (x 13 12)
          have b22149 := hb (x 13 2 && x 13 12)
          clear * - r22147 b22148 b22149 d22138
          omega
        have d22150 : (x 13 4).toNat = 0 := by
          have r22151 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
          have b22152 := hb (x 13 4)
          have b22153 := hb (x 13 12)
          clear * - r22151 b22152 b22153 d22138
          omega
        have d22154 : (x 12 13).toNat = 0 := by
          have r22155 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22156 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
          have e22157 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
          have b22158 := hb (x 10 3)
          have b22159 := hb (x 11 2)
          have b22160 := hb (x 12 13)
          have b22161 := hb (x 13 12)
          clear * - r22155 e22156 e22157 b22158 b22159 b22160 b22161 d22138 d22134
          omega
        have d22162 : (x 12 3 && x 12 13).toNat = 0 := by
          have r22163 := hand2 (x 12 3) (x 12 13)
          have b22164 := hb (x 12 13)
          have b22165 := hb (x 12 3 && x 12 13)
          clear * - r22163 b22164 b22165 d22154
          omega
        have d22166 : (x 12 5).toNat = 0 := by
          have r22167 : (x 12 5).toNat ≤ (x 12 13).toNat := himp _ _ (hp5 12)
          have b22168 := hb (x 12 5)
          have b22169 := hb (x 12 13)
          clear * - r22167 b22168 b22169 d22154
          omega
        have d22170 : (x 10 1).toNat = 1 := by
          have r22171 := hand1 (x 10 1) (x 10 11)
          have b22172 := hb (x 10 1)
          have b22173 := hb (x 10 1 && x 10 11)
          clear * - r22171 b22172 b22173 d22122
          omega
        have d22174 : (x 11 14).toNat = 0 := by
          have r22175 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b22176 := hb (x 10 1)
          have b22177 := hb (x 11 14)
          clear * - r22175 b22176 b22177 d22170
          omega
        have d22178 : (x 11 1 && x 11 14).toNat = 0 := by
          have r22179 := hand2 (x 11 1) (x 11 14)
          have b22180 := hb (x 11 14)
          have b22181 := hb (x 11 1 && x 11 14)
          clear * - r22179 b22180 b22181 d22174
          omega
        have d22182 : (x 10 2).toNat = 1 := by
          have r22183 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b22184 := hb (x 10 2)
          have b22185 := hb (x 12 13)
          have b22186 := hb (x 11 1 && x 11 14)
          clear * - r22183 b22184 b22185 b22186 d22154 d22178
          omega
        have d22187 : (x 10 14).toNat = 1 := by
          have r22188 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
          have b22189 := hb (x 10 2)
          have b22190 := hb (x 10 14)
          clear * - r22188 b22189 b22190 d22182
          omega
        have d22191 : (x 9 1).toNat = 0 := by
          have r22192 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b22193 := hb (x 9 1)
          have b22194 := hb (x 10 14)
          clear * - r22192 b22193 b22194 d22187
          omega
        have d22195 : (x 9 1 && x 9 14).toNat = 0 := by
          have r22196 := hand1 (x 9 1) (x 9 14)
          have b22197 := hb (x 9 1)
          have b22198 := hb (x 9 1 && x 9 14)
          clear * - r22196 b22197 b22198 d22191
          omega
        have d22199 : (x 8 2).toNat = 1 := by
          have r22200 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b22201 := hb (x 8 2)
          have b22202 := hb (x 10 13)
          have b22203 := hb (x 9 1 && x 9 14)
          clear * - r22200 b22201 b22202 b22203 d20496 d22195
          omega
        have d22204 : (x 8 14).toNat = 1 := by
          have r22205 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
          have b22206 := hb (x 8 2)
          have b22207 := hb (x 8 14)
          clear * - r22205 b22206 b22207 d22199
          omega
        have d22208 : (x 7 1).toNat = 0 := by
          have r22209 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b22210 := hb (x 7 1)
          have b22211 := hb (x 8 14)
          clear * - r22209 b22210 b22211 d22204
          omega
        have d22212 : (x 7 1 && x 7 7).toNat = 0 := by
          have r22213 := hand1 (x 7 1) (x 7 7)
          have b22214 := hb (x 7 1)
          have b22215 := hb (x 7 1 && x 7 7)
          clear * - r22213 b22214 b22215 d22208
          omega
        have d22216 : (x 8 6).toNat = 1 := by
          have r22217 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b22218 := hb (x (-1) 9)
          have b22219 := hb (x 8 6)
          have b22220 := hb (x 7 1 && x 7 7)
          have b22221 := hb (x 6 2 && x 6 8)
          have b22222 := hb (x 5 3 && x 5 9)
          have b22223 := hb (x 4 4 && x 4 10)
          have b22224 := hb (x 3 5 && x 3 11)
          have b22225 := hb (x 2 6 && x 2 12)
          have b22226 := hb (x 1 7 && x 1 13)
          have b22227 := hb (x 0 8 && x 0 14)
          clear * - r22217 b22218 b22219 b22220 b22221 b22222 b22223 b22224 b22225 b22226 b22227 d22212 g58 g59 d20453 g60 g61 g62 d19300 g4
          omega
        have d22228 : (x 14 8).toNat = 0 := by
          have r22229 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22230 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
          have e22231 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
          have e22232 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
          have e22233 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
          have e22234 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
          have e22235 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
          have b22236 := hb (x 7 7)
          have b22237 := hb (x 8 6)
          have b22238 := hb (x 9 5)
          have b22239 := hb (x 10 4)
          have b22240 := hb (x 11 11)
          have b22241 := hb (x 12 10)
          have b22242 := hb (x 13 9)
          have b22243 := hb (x 14 8)
          clear * - r22229 e22230 e22231 e22232 e22233 e22234 e22235 b22236 b22237 b22238 b22239 b22240 b22241 b22242 b22243 d22216
          omega
        have d22244 : (x 13 9).toNat = 0 := by
          have r22245 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22246 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
          have e22247 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
          have e22248 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
          have e22249 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
          have e22250 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
          have e22251 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
          have b22252 := hb (x 7 7)
          have b22253 := hb (x 8 6)
          have b22254 := hb (x 9 5)
          have b22255 := hb (x 10 4)
          have b22256 := hb (x 11 11)
          have b22257 := hb (x 12 10)
          have b22258 := hb (x 13 9)
          have b22259 := hb (x 14 8)
          clear * - r22245 e22246 e22247 e22248 e22249 e22250 e22251 b22252 b22253 b22254 b22255 b22256 b22257 b22258 b22259 d22228 d22216
          omega
        have d22260 : (x 12 10).toNat = 0 := by
          have r22261 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22262 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
          have e22263 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
          have e22264 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
          have e22265 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
          have e22266 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
          have e22267 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
          have b22268 := hb (x 7 7)
          have b22269 := hb (x 8 6)
          have b22270 := hb (x 9 5)
          have b22271 := hb (x 10 4)
          have b22272 := hb (x 11 11)
          have b22273 := hb (x 12 10)
          have b22274 := hb (x 13 9)
          have b22275 := hb (x 14 8)
          clear * - r22261 e22262 e22263 e22264 e22265 e22266 e22267 b22268 b22269 b22270 b22271 b22272 b22273 b22274 b22275 d22228 d22244 d22216
          omega
        have d22276 : (x 11 11).toNat = 0 := by
          have r22277 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22278 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
          have e22279 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
          have e22280 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
          have e22281 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
          have e22282 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
          have e22283 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
          have b22284 := hb (x 7 7)
          have b22285 := hb (x 8 6)
          have b22286 := hb (x 9 5)
          have b22287 := hb (x 10 4)
          have b22288 := hb (x 11 11)
          have b22289 := hb (x 12 10)
          have b22290 := hb (x 13 9)
          have b22291 := hb (x 14 8)
          clear * - r22277 e22278 e22279 e22280 e22281 e22282 e22283 b22284 b22285 b22286 b22287 b22288 b22289 b22290 b22291 d22228 d22244 d22260 d22216
          omega
        have d22292 : (x 10 4).toNat = 0 := by
          have r22293 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22294 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
          have e22295 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
          have e22296 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
          have e22297 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
          have e22298 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
          have e22299 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
          have b22300 := hb (x 7 7)
          have b22301 := hb (x 8 6)
          have b22302 := hb (x 9 5)
          have b22303 := hb (x 10 4)
          have b22304 := hb (x 11 11)
          have b22305 := hb (x 12 10)
          have b22306 := hb (x 13 9)
          have b22307 := hb (x 14 8)
          clear * - r22293 e22294 e22295 e22296 e22297 e22298 e22299 b22300 b22301 b22302 b22303 b22304 b22305 b22306 b22307 d22228 d22244 d22260 d22276 d22216
          omega
        have d22308 : (x 10 4 && x 10 11).toNat = 0 := by
          have r22309 := hand1 (x 10 4) (x 10 11)
          have b22310 := hb (x 10 4)
          have b22311 := hb (x 10 4 && x 10 11)
          clear * - r22309 b22310 b22311 d22292
          omega
        have d22312 : (x 9 5).toNat = 0 := by
          have r22313 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22314 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
          have e22315 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
          have e22316 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
          have e22317 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
          have e22318 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
          have e22319 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
          have b22320 := hb (x 7 7)
          have b22321 := hb (x 8 6)
          have b22322 := hb (x 9 5)
          have b22323 := hb (x 10 4)
          have b22324 := hb (x 11 11)
          have b22325 := hb (x 12 10)
          have b22326 := hb (x 13 9)
          have b22327 := hb (x 14 8)
          clear * - r22313 e22314 e22315 e22316 e22317 e22318 e22319 b22320 b22321 b22322 b22323 b22324 b22325 b22326 b22327 d22228 d22244 d22260 d22276 d22292 d22216
          omega
        have d22328 : (x 9 5 && x 9 12).toNat = 0 := by
          have r22329 := hand1 (x 9 5) (x 9 12)
          have b22330 := hb (x 9 5)
          have b22331 := hb (x 9 5 && x 9 12)
          clear * - r22329 b22330 b22331 d22312
          omega
        have d22332 : (x 7 7).toNat = 0 := by
          have r22333 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22334 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
          have e22335 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
          have e22336 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
          have e22337 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
          have e22338 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
          have e22339 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
          have b22340 := hb (x 7 7)
          have b22341 := hb (x 8 6)
          have b22342 := hb (x 9 5)
          have b22343 := hb (x 10 4)
          have b22344 := hb (x 11 11)
          have b22345 := hb (x 12 10)
          have b22346 := hb (x 13 9)
          have b22347 := hb (x 14 8)
          clear * - r22333 e22334 e22335 e22336 e22337 e22338 e22339 b22340 b22341 b22342 b22343 b22344 b22345 b22346 b22347 d22228 d22244 d22260 d22276 d22292 d22312 d22216
          omega
        have d22348 : (x 7 7 && x 7 14).toNat = 0 := by
          have r22349 := hand1 (x 7 7) (x 7 14)
          have b22350 := hb (x 7 7)
          have b22351 := hb (x 7 7 && x 7 14)
          clear * - r22349 b22350 b22351 d22332
          omega
        have d22352 : (x 14 7).toNat = 1 := by
          have r22353 : 1 ≤ (x 14 7).toNat + (x 13 1 && x 13 8).toNat + (x 12 2 && x 12 9).toNat + (x 11 3 && x 11 10).toNat + (x 10 4 && x 10 11).toNat + (x 9 5 && x 9 12).toNat + (x 8 6 && x 8 13).toNat + (x 7 7 && x 7 14).toNat + (x 6 8).toNat := by have q := hcov7 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b22354 := hb (x 6 8)
          have b22355 := hb (x 14 7)
          have b22356 := hb (x 13 1 && x 13 8)
          have b22357 := hb (x 12 2 && x 12 9)
          have b22358 := hb (x 11 3 && x 11 10)
          have b22359 := hb (x 10 4 && x 10 11)
          have b22360 := hb (x 9 5 && x 9 12)
          have b22361 := hb (x 8 6 && x 8 13)
          have b22362 := hb (x 7 7 && x 7 14)
          clear * - r22353 b22354 b22355 b22356 b22357 b22358 b22359 b22360 b22361 b22362 d22070 d22094 d22118 d22308 d22328 d22030 d22348 g38
          omega
        have d22363 : (x 21 8).toNat = 0 := by
          have r22364 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22365 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
          have e22366 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
          have e22367 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
          have e22368 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
          have e22369 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
          have e22370 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
          have b22371 := hb (x 14 7)
          have b22372 := hb (x 15 6)
          have b22373 := hb (x 16 5)
          have b22374 := hb (x 17 4)
          have b22375 := hb (x 18 11)
          have b22376 := hb (x 19 10)
          have b22377 := hb (x 20 9)
          have b22378 := hb (x 21 8)
          clear * - r22364 e22365 e22366 e22367 e22368 e22369 e22370 b22371 b22372 b22373 b22374 b22375 b22376 b22377 b22378 d22352
          omega
        have d22379 : (x 20 9).toNat = 0 := by
          have r22380 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22381 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
          have e22382 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
          have e22383 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
          have e22384 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
          have e22385 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
          have e22386 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
          have b22387 := hb (x 14 7)
          have b22388 := hb (x 15 6)
          have b22389 := hb (x 16 5)
          have b22390 := hb (x 17 4)
          have b22391 := hb (x 18 11)
          have b22392 := hb (x 19 10)
          have b22393 := hb (x 20 9)
          have b22394 := hb (x 21 8)
          clear * - r22380 e22381 e22382 e22383 e22384 e22385 e22386 b22387 b22388 b22389 b22390 b22391 b22392 b22393 b22394 d22363 d22352
          omega
        have d22395 : (x 19 10).toNat = 0 := by
          have r22396 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22397 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
          have e22398 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
          have e22399 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
          have e22400 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
          have e22401 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
          have e22402 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
          have b22403 := hb (x 14 7)
          have b22404 := hb (x 15 6)
          have b22405 := hb (x 16 5)
          have b22406 := hb (x 17 4)
          have b22407 := hb (x 18 11)
          have b22408 := hb (x 19 10)
          have b22409 := hb (x 20 9)
          have b22410 := hb (x 21 8)
          clear * - r22396 e22397 e22398 e22399 e22400 e22401 e22402 b22403 b22404 b22405 b22406 b22407 b22408 b22409 b22410 d22363 d22379 d22352
          omega
        have d22411 : (x 18 11).toNat = 0 := by
          have r22412 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22413 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
          have e22414 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
          have e22415 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
          have e22416 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
          have e22417 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
          have e22418 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
          have b22419 := hb (x 14 7)
          have b22420 := hb (x 15 6)
          have b22421 := hb (x 16 5)
          have b22422 := hb (x 17 4)
          have b22423 := hb (x 18 11)
          have b22424 := hb (x 19 10)
          have b22425 := hb (x 20 9)
          have b22426 := hb (x 21 8)
          clear * - r22412 e22413 e22414 e22415 e22416 e22417 e22418 b22419 b22420 b22421 b22422 b22423 b22424 b22425 b22426 d22363 d22379 d22395 d22352
          omega
        have d22427 : (x 17 4).toNat = 0 := by
          have r22428 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22429 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
          have e22430 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
          have e22431 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
          have e22432 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
          have e22433 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
          have e22434 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
          have b22435 := hb (x 14 7)
          have b22436 := hb (x 15 6)
          have b22437 := hb (x 16 5)
          have b22438 := hb (x 17 4)
          have b22439 := hb (x 18 11)
          have b22440 := hb (x 19 10)
          have b22441 := hb (x 20 9)
          have b22442 := hb (x 21 8)
          clear * - r22428 e22429 e22430 e22431 e22432 e22433 e22434 b22435 b22436 b22437 b22438 b22439 b22440 b22441 b22442 d22363 d22379 d22395 d22411 d22352
          omega
        have d22443 : (x 16 5).toNat = 0 := by
          have r22444 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22445 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
          have e22446 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
          have e22447 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
          have e22448 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
          have e22449 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
          have e22450 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
          have b22451 := hb (x 14 7)
          have b22452 := hb (x 15 6)
          have b22453 := hb (x 16 5)
          have b22454 := hb (x 17 4)
          have b22455 := hb (x 18 11)
          have b22456 := hb (x 19 10)
          have b22457 := hb (x 20 9)
          have b22458 := hb (x 21 8)
          clear * - r22444 e22445 e22446 e22447 e22448 e22449 e22450 b22451 b22452 b22453 b22454 b22455 b22456 b22457 b22458 d22363 d22379 d22395 d22411 d22427 d22352
          omega
        have d22459 : (x 15 6).toNat = 0 := by
          have r22460 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22461 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
          have e22462 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
          have e22463 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
          have e22464 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
          have e22465 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
          have e22466 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
          have b22467 := hb (x 14 7)
          have b22468 := hb (x 15 6)
          have b22469 := hb (x 16 5)
          have b22470 := hb (x 17 4)
          have b22471 := hb (x 18 11)
          have b22472 := hb (x 19 10)
          have b22473 := hb (x 20 9)
          have b22474 := hb (x 21 8)
          clear * - r22460 e22461 e22462 e22463 e22464 e22465 e22466 b22467 b22468 b22469 b22470 b22471 b22472 b22473 b22474 d22363 d22379 d22395 d22411 d22427 d22443 d22352
          omega
        have d22475 : (x 14 1 && x 14 7).toNat = 1 := by
          have r22476 : 1 ≤ (x 15 6).toNat + (x 14 1 && x 14 7).toNat + (x 13 2 && x 13 8).toNat + (x 12 3 && x 12 9).toNat + (x 11 4 && x 11 10).toNat + (x 10 5 && x 10 11).toNat + (x 9 6 && x 9 12).toNat + (x 8 7 && x 8 13).toNat + (x 7 8 && x 7 14).toNat + (x 6 9).toNat := by have q := hcov6 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b22477 := hb (x 6 9)
          have b22478 := hb (x 15 6)
          have b22479 := hb (x 14 1 && x 14 7)
          have b22480 := hb (x 13 2 && x 13 8)
          have b22481 := hb (x 12 3 && x 12 9)
          have b22482 := hb (x 11 4 && x 11 10)
          have b22483 := hb (x 10 5 && x 10 11)
          have b22484 := hb (x 9 6 && x 9 12)
          have b22485 := hb (x 8 7 && x 8 13)
          have b22486 := hb (x 7 8 && x 7 14)
          clear * - r22476 b22477 b22478 b22479 b22480 b22481 b22482 b22483 b22484 b22485 b22486 d22459 d22074 d22098 d20492 d20516 d21020 d22034 g67 g39
          omega
        have d22487 : (x 14 1).toNat = 1 := by
          have r22488 := hand1 (x 14 1) (x 14 7)
          have b22489 := hb (x 14 1)
          have b22490 := hb (x 14 1 && x 14 7)
          clear * - r22488 b22489 b22490 d22475
          omega
        have d22491 : (x 15 14).toNat = 0 := by
          have r22492 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b22493 := hb (x 14 1)
          have b22494 := hb (x 15 14)
          clear * - r22492 b22493 b22494 d22487
          omega
        have d22495 : (x 15 2).toNat = 0 := by
          have r22496 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
          have b22497 := hb (x 15 2)
          have b22498 := hb (x 15 14)
          clear * - r22496 b22497 b22498 d22491
          omega
        have d22499 : (x 15 10).toNat = 0 := by
          have r22500 : (x 15 10).toNat ≤ (x 15 2).toNat := himp _ _ (hp10 15)
          have b22501 := hb (x 15 2)
          have b22502 := hb (x 15 10)
          clear * - r22500 b22501 b22502 d22495
          omega
        have d22503 : (x 14 1 && x 14 11).toNat = 1 := by
          have r22504 : 1 ≤ (x 15 10).toNat + (x 14 1 && x 14 11).toNat + (x 13 2 && x 13 12).toNat + (x 12 3 && x 12 13).toNat + (x 11 4 && x 11 14).toNat + (x 10 5).toNat := by have q := hcov10 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b22505 := hb (x 10 5)
          have b22506 := hb (x 15 10)
          have b22507 := hb (x 14 1 && x 14 11)
          have b22508 := hb (x 13 2 && x 13 12)
          have b22509 := hb (x 12 3 && x 12 13)
          have b22510 := hb (x 11 4 && x 11 14)
          clear * - r22504 b22505 b22506 b22507 b22508 b22509 b22510 d22499 d22146 d22162 d20488 d20512
          omega
        have d22511 : (x 14 11).toNat = 1 := by
          have r22512 := hand2 (x 14 1) (x 14 11)
          have b22513 := hb (x 14 11)
          have b22514 := hb (x 14 1 && x 14 11)
          clear * - r22512 b22513 b22514 d22503
          omega
        have d22515 : (x 17 8).toNat = 0 := by
          have r22516 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22517 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
          have e22518 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
          have e22519 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
          have e22520 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
          have e22521 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
          have e22522 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
          have b22523 := hb (x 10 7)
          have b22524 := hb (x 11 6)
          have b22525 := hb (x 12 5)
          have b22526 := hb (x 13 4)
          have b22527 := hb (x 14 11)
          have b22528 := hb (x 15 10)
          have b22529 := hb (x 16 9)
          have b22530 := hb (x 17 8)
          clear * - r22516 e22517 e22518 e22519 e22520 e22521 e22522 b22523 b22524 b22525 b22526 b22527 b22528 b22529 b22530 d22499 d22511 d22150 d22166
          omega
        have d22531 : (x 16 9).toNat = 0 := by
          have r22532 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22533 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
          have e22534 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
          have e22535 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
          have e22536 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
          have e22537 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
          have e22538 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
          have b22539 := hb (x 10 7)
          have b22540 := hb (x 11 6)
          have b22541 := hb (x 12 5)
          have b22542 := hb (x 13 4)
          have b22543 := hb (x 14 11)
          have b22544 := hb (x 15 10)
          have b22545 := hb (x 16 9)
          have b22546 := hb (x 17 8)
          clear * - r22532 e22533 e22534 e22535 e22536 e22537 e22538 b22539 b22540 b22541 b22542 b22543 b22544 b22545 b22546 d22515 d22499 d22511 d22150 d22166
          omega
        have d22547 : (x 11 6).toNat = 0 := by
          have r22548 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22549 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
          have e22550 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
          have e22551 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
          have e22552 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
          have e22553 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
          have e22554 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
          have b22555 := hb (x 10 7)
          have b22556 := hb (x 11 6)
          have b22557 := hb (x 12 5)
          have b22558 := hb (x 13 4)
          have b22559 := hb (x 14 11)
          have b22560 := hb (x 15 10)
          have b22561 := hb (x 16 9)
          have b22562 := hb (x 17 8)
          clear * - r22548 e22549 e22550 e22551 e22552 e22553 e22554 b22555 b22556 b22557 b22558 b22559 b22560 b22561 b22562 d22515 d22531 d22499 d22511 d22150 d22166
          omega
        have d22563 : (x 10 7).toNat = 0 := by
          have r22564 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22565 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
          have e22566 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
          have e22567 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
          have e22568 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
          have e22569 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
          have e22570 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
          have b22571 := hb (x 10 7)
          have b22572 := hb (x 11 6)
          have b22573 := hb (x 12 5)
          have b22574 := hb (x 13 4)
          have b22575 := hb (x 14 11)
          have b22576 := hb (x 15 10)
          have b22577 := hb (x 16 9)
          have b22578 := hb (x 17 8)
          clear * - r22564 e22565 e22566 e22567 e22568 e22569 e22570 b22571 b22572 b22573 b22574 b22575 b22576 b22577 b22578 d22515 d22531 d22499 d22511 d22150 d22166 d22547
          omega
        have d22579 : (x 10 1 && x 10 7).toNat = 0 := by
          have r22580 := hand2 (x 10 1) (x 10 7)
          have b22581 := hb (x 10 7)
          have b22582 := hb (x 10 1 && x 10 7)
          clear * - r22580 b22581 b22582 d22563
          omega
        have r22583 : 1 ≤ (x 11 6).toNat + (x 10 1 && x 10 7).toNat + (x 9 2 && x 9 8).toNat + (x 8 3 && x 8 9).toNat + (x 7 4 && x 7 10).toNat + (x 6 5 && x 6 11).toNat + (x 5 6 && x 5 12).toNat + (x 4 7 && x 4 13).toNat + (x 3 8 && x 3 14).toNat + (x 2 9).toNat := by have q := hcov6 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b22584 := hb (x 2 9)
        have b22585 := hb (x 11 6)
        have b22586 := hb (x 10 1 && x 10 7)
        have b22587 := hb (x 9 2 && x 9 8)
        have b22588 := hb (x 8 3 && x 8 9)
        have b22589 := hb (x 7 4 && x 7 10)
        have b22590 := hb (x 6 5 && x 6 11)
        have b22591 := hb (x 5 6 && x 5 12)
        have b22592 := hb (x 4 7 && x 4 13)
        have b22593 := hb (x 3 8 && x 3 14)
        linarith only [r22583, b22584, b22585, b22586, b22587, b22588, b22589, b22590, b22591, b22592, b22593, d22547, d22579, d20532, d21912, g63, g64, g65, d20588, g66, d20336]
    · have f22594 : (x 0 10).toNat = 1 := by rw [h19314]; rfl
      have d22595 : (x 2 8).toNat = 0 := by
        have r22596 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22597 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e22598 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e22599 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e22600 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e22601 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e22602 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b22603 := hb (x (-5) 7)
        have b22604 := hb (x (-4) 6)
        have b22605 := hb (x (-3) 5)
        have b22606 := hb (x (-2) 4)
        have b22607 := hb (x (-1) 11)
        have b22608 := hb (x 0 10)
        have b22609 := hb (x 1 9)
        have b22610 := hb (x 2 8)
        clear * - r22596 e22597 e22598 e22599 e22600 e22601 e22602 b22603 b22604 b22605 b22606 b22607 b22608 b22609 b22610 g19 f22594 g6
        omega
      have d22611 : (x (-2) 4).toNat = 0 := by
        have r22612 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22613 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e22614 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e22615 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e22616 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e22617 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e22618 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b22619 := hb (x (-5) 7)
        have b22620 := hb (x (-4) 6)
        have b22621 := hb (x (-3) 5)
        have b22622 := hb (x (-2) 4)
        have b22623 := hb (x (-1) 11)
        have b22624 := hb (x 0 10)
        have b22625 := hb (x 1 9)
        have b22626 := hb (x 2 8)
        clear * - r22612 e22613 e22614 e22615 e22616 e22617 e22618 b22619 b22620 b22621 b22622 b22623 b22624 b22625 b22626 d22595 g19 f22594 g6
        omega
      have d22627 : (x (-2) 4 && x (-2) 14).toNat = 0 := by
        have r22628 := hand1 (x (-2) 4) (x (-2) 14)
        have b22629 := hb (x (-2) 4)
        have b22630 := hb (x (-2) 4 && x (-2) 14)
        clear * - r22628 b22629 b22630 d22611
        omega
      have d22631 : (x (-3) 5).toNat = 0 := by
        have r22632 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22633 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e22634 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e22635 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e22636 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e22637 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e22638 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b22639 := hb (x (-5) 7)
        have b22640 := hb (x (-4) 6)
        have b22641 := hb (x (-3) 5)
        have b22642 := hb (x (-2) 4)
        have b22643 := hb (x (-1) 11)
        have b22644 := hb (x 0 10)
        have b22645 := hb (x 1 9)
        have b22646 := hb (x 2 8)
        clear * - r22632 e22633 e22634 e22635 e22636 e22637 e22638 b22639 b22640 b22641 b22642 b22643 b22644 b22645 b22646 d22595 g19 f22594 g6 d22611
        omega
      have d22647 : (x 2 10).toNat = 1 := by
        have r22648 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b22649 := hb (x (-3) 5)
        have b22650 := hb (x 2 10)
        have b22651 := hb (x 1 1 && x 1 11)
        have b22652 := hb (x 0 2 && x 0 12)
        have b22653 := hb (x (-1) 3 && x (-1) 13)
        have b22654 := hb (x (-2) 4 && x (-2) 14)
        clear * - r22648 b22649 b22650 b22651 b22652 b22653 b22654 g94 g95 g96 d22627 d22631
        omega
      have d22655 : (x 2 2).toNat = 1 := by
        have r22656 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
        have b22657 := hb (x 2 2)
        have b22658 := hb (x 2 10)
        clear * - r22656 b22657 b22658 d22647
        omega
      have d22659 : (x 4 12).toNat = 0 := by
        have r22660 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22661 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e22662 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b22663 := hb (x 1 3)
        have b22664 := hb (x 2 2)
        have b22665 := hb (x 3 13)
        have b22666 := hb (x 4 12)
        clear * - r22660 e22661 e22662 b22663 b22664 b22665 b22666 g32 d22655
        omega
      have d22667 : (x 4 4).toNat = 0 := by
        have r22668 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
        have b22669 := hb (x 4 4)
        have b22670 := hb (x 4 12)
        clear * - r22668 b22669 b22670 d22659
        omega
      have d22671 : (x 4 4 && x 4 11).toNat = 0 := by
        have r22672 := hand1 (x 4 4) (x 4 11)
        have b22673 := hb (x 4 4)
        have b22674 := hb (x 4 4 && x 4 11)
        clear * - r22672 b22673 b22674 d22667
        omega
      have d22675 : (x 4 4 && x 4 10).toNat = 0 := by
        have r22676 := hand1 (x 4 4) (x 4 10)
        have b22677 := hb (x 4 4)
        have b22678 := hb (x 4 4 && x 4 10)
        clear * - r22676 b22677 b22678 d22667
        omega
      have d22679 : (x 8 11).toNat = 1 := by
        have r22680 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b22681 := hb (x 4 4)
        have b22682 := hb (x 8 11)
        have b22683 := hb (x 7 1 && x 7 12)
        have b22684 := hb (x 6 2 && x 6 13)
        have b22685 := hb (x 5 3 && x 5 14)
        clear * - r22680 b22681 b22682 b22683 b22684 b22685 g106 g107 g108 d22667
        omega
      have d22686 : (x 8 3).toNat = 1 := by
        have r22687 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
        have b22688 := hb (x 8 3)
        have b22689 := hb (x 8 11)
        clear * - r22687 b22688 b22689 d22679
        omega
      have d22690 : (x 11 12).toNat = 0 := by
        have r22691 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22692 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e22693 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b22694 := hb (x 8 3)
        have b22695 := hb (x 9 2)
        have b22696 := hb (x 10 13)
        have b22697 := hb (x 11 12)
        clear * - r22691 e22692 e22693 b22694 b22695 b22696 b22697 d22686
        omega
      have d22698 : (x 11 2 && x 11 12).toNat = 0 := by
        have r22699 := hand2 (x 11 2) (x 11 12)
        have b22700 := hb (x 11 12)
        have b22701 := hb (x 11 2 && x 11 12)
        clear * - r22699 b22700 b22701 d22690
        omega
      have d22702 : (x 11 4).toNat = 0 := by
        have r22703 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
        have b22704 := hb (x 11 4)
        have b22705 := hb (x 11 12)
        clear * - r22703 b22704 b22705 d22690
        omega
      have d22706 : (x 10 13).toNat = 0 := by
        have r22707 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22708 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e22709 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b22710 := hb (x 8 3)
        have b22711 := hb (x 9 2)
        have b22712 := hb (x 10 13)
        have b22713 := hb (x 11 12)
        clear * - r22707 e22708 e22709 b22710 b22711 b22712 b22713 d22690 d22686
        omega
      have d22714 : (x 10 3 && x 10 13).toNat = 0 := by
        have r22715 := hand2 (x 10 3) (x 10 13)
        have b22716 := hb (x 10 13)
        have b22717 := hb (x 10 3 && x 10 13)
        clear * - r22715 b22716 b22717 d22706
        omega
      have d22718 : (x 10 5).toNat = 0 := by
        have r22719 : (x 10 5).toNat ≤ (x 10 13).toNat := himp _ _ (hp5 10)
        have b22720 := hb (x 10 5)
        have b22721 := hb (x 10 13)
        clear * - r22719 b22720 b22721 d22706
        omega
      have d22722 : (x 1 3).toNat = 0 := by
        have r22723 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22724 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e22725 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b22726 := hb (x 1 3)
        have b22727 := hb (x 2 2)
        have b22728 := hb (x 3 13)
        have b22729 := hb (x 4 12)
        clear * - r22723 e22724 e22725 b22726 b22727 b22728 b22729 d22659 g32 d22655
        omega
      have d22730 : (x 1 11).toNat = 0 := by
        have r22731 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
        have b22732 := hb (x 1 3)
        have b22733 := hb (x 1 11)
        clear * - r22731 b22732 b22733 d22722
        omega
      have d22734 : (x 4 8).toNat = 0 := by
        have r22735 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22736 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
        have e22737 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
        have e22738 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
        have e22739 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
        have e22740 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
        have e22741 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
        have b22742 := hb (x (-3) 7)
        have b22743 := hb (x (-2) 6)
        have b22744 := hb (x (-1) 5)
        have b22745 := hb (x 0 4)
        have b22746 := hb (x 1 11)
        have b22747 := hb (x 2 10)
        have b22748 := hb (x 3 9)
        have b22749 := hb (x 4 8)
        clear * - r22735 e22736 e22737 e22738 e22739 e22740 e22741 b22742 b22743 b22744 b22745 b22746 b22747 b22748 b22749 g29 d22647 d22730 g10 g3
        omega
      have d22750 : (x (-2) 6).toNat = 0 := by
        have r22751 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22752 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
        have e22753 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
        have e22754 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
        have e22755 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
        have e22756 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
        have e22757 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
        have b22758 := hb (x (-3) 7)
        have b22759 := hb (x (-2) 6)
        have b22760 := hb (x (-1) 5)
        have b22761 := hb (x 0 4)
        have b22762 := hb (x 1 11)
        have b22763 := hb (x 2 10)
        have b22764 := hb (x 3 9)
        have b22765 := hb (x 4 8)
        clear * - r22751 e22752 e22753 e22754 e22755 e22756 e22757 b22758 b22759 b22760 b22761 b22762 b22763 b22764 b22765 d22734 g29 d22647 d22730 g10 g3
        omega
      have d22766 : (x 8 7).toNat = 1 := by
        have r22767 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := by have q := hcov7 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b22768 := hb (x 0 8)
        have b22769 := hb (x 8 7)
        have b22770 := hb (x 7 1 && x 7 8)
        have b22771 := hb (x 6 2 && x 6 9)
        have b22772 := hb (x 5 3 && x 5 10)
        have b22773 := hb (x 4 4 && x 4 11)
        have b22774 := hb (x 3 5 && x 3 12)
        have b22775 := hb (x 2 6 && x 2 13)
        have b22776 := hb (x 1 7 && x 1 14)
        clear * - r22767 b22768 b22769 b22770 b22771 b22772 b22773 b22774 b22775 b22776 g72 g73 g74 d22671 g75 g76 g77 g11
        omega
      have d22777 : (x 15 8).toNat = 0 := by
        have r22778 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22779 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
        have e22780 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
        have e22781 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
        have e22782 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
        have e22783 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
        have e22784 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
        have b22785 := hb (x 8 7)
        have b22786 := hb (x 9 6)
        have b22787 := hb (x 10 5)
        have b22788 := hb (x 11 4)
        have b22789 := hb (x 12 11)
        have b22790 := hb (x 13 10)
        have b22791 := hb (x 14 9)
        have b22792 := hb (x 15 8)
        clear * - r22778 e22779 e22780 e22781 e22782 e22783 e22784 b22785 b22786 b22787 b22788 b22789 b22790 b22791 b22792 d22702 d22718 d22766
        omega
      have d22793 : (x 14 9).toNat = 0 := by
        have r22794 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22795 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
        have e22796 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
        have e22797 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
        have e22798 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
        have e22799 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
        have e22800 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
        have b22801 := hb (x 8 7)
        have b22802 := hb (x 9 6)
        have b22803 := hb (x 10 5)
        have b22804 := hb (x 11 4)
        have b22805 := hb (x 12 11)
        have b22806 := hb (x 13 10)
        have b22807 := hb (x 14 9)
        have b22808 := hb (x 15 8)
        clear * - r22794 e22795 e22796 e22797 e22798 e22799 e22800 b22801 b22802 b22803 b22804 b22805 b22806 b22807 b22808 d22777 d22702 d22718 d22766
        omega
      have d22809 : (x 13 10).toNat = 0 := by
        have r22810 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22811 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
        have e22812 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
        have e22813 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
        have e22814 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
        have e22815 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
        have e22816 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
        have b22817 := hb (x 8 7)
        have b22818 := hb (x 9 6)
        have b22819 := hb (x 10 5)
        have b22820 := hb (x 11 4)
        have b22821 := hb (x 12 11)
        have b22822 := hb (x 13 10)
        have b22823 := hb (x 14 9)
        have b22824 := hb (x 15 8)
        clear * - r22810 e22811 e22812 e22813 e22814 e22815 e22816 b22817 b22818 b22819 b22820 b22821 b22822 b22823 b22824 d22777 d22793 d22702 d22718 d22766
        omega
      have d22825 : (x 12 11).toNat = 0 := by
        have r22826 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22827 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
        have e22828 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
        have e22829 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
        have e22830 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
        have e22831 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
        have e22832 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
        have b22833 := hb (x 8 7)
        have b22834 := hb (x 9 6)
        have b22835 := hb (x 10 5)
        have b22836 := hb (x 11 4)
        have b22837 := hb (x 12 11)
        have b22838 := hb (x 13 10)
        have b22839 := hb (x 14 9)
        have b22840 := hb (x 15 8)
        clear * - r22826 e22827 e22828 e22829 e22830 e22831 e22832 b22833 b22834 b22835 b22836 b22837 b22838 b22839 b22840 d22777 d22793 d22809 d22702 d22718 d22766
        omega
      have d22841 : (x 12 1 && x 12 11).toNat = 0 := by
        have r22842 := hand2 (x 12 1) (x 12 11)
        have b22843 := hb (x 12 11)
        have b22844 := hb (x 12 1 && x 12 11)
        clear * - r22842 b22843 b22844 d22825
        omega
      have r22845 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r22846 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r22847 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r22848 : 1 ≤ (x 4 9).toNat + (x 3 1 && x 3 10).toNat + (x 2 2 && x 2 11).toNat + (x 1 3 && x 1 12).toNat + (x 0 4 && x 0 13).toNat + (x (-1) 5 && x (-1) 14).toNat + (x (-2) 6).toNat := by have q := hcov9 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r22849 : 1 ≤ (x 13 10).toNat + (x 12 1 && x 12 11).toNat + (x 11 2 && x 11 12).toNat + (x 10 3 && x 10 13).toNat + (x 9 4 && x 9 14).toNat + (x 8 5).toNat := by have q := hcov10 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r22850 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r22851 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
      have r22852 := hand2 (x 7 1) (x 7 7)
      have r22853 := hand2 (x 2 2) (x 2 11)
      have r22854 := hand1 (x 9 4) (x 9 14)
      have r22855 := hand1 (x 12 1) (x 12 14)
      linarith only [r22845, r22846, r22847, r22848, r22849, r22850, r22851, r22852, r22853, r22854, r22855, d22750, g4, g13, g14, g21, g22, g25, g30, g31, g33, g36, g38, d22809, g58, g59, d22675, g60, g61, g62, d19300, g83, g84, g85, g86, d22841, d22698, d22714]
  · have f22906 : (x 0 9).toNat = 1 := by rw [h19308]; rfl
    have d22907 : (x 1 8).toNat = 0 := by
      have r22908 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22909 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e22910 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e22911 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e22912 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e22913 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e22914 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b22915 := hb (x (-6) 7)
      have b22916 := hb (x (-5) 6)
      have b22917 := hb (x (-4) 5)
      have b22918 := hb (x (-3) 4)
      have b22919 := hb (x (-2) 11)
      have b22920 := hb (x (-1) 10)
      have b22921 := hb (x 0 9)
      have b22922 := hb (x 1 8)
      clear * - r22908 e22909 e22910 e22911 e22912 e22913 e22914 b22915 b22916 b22917 b22918 b22919 b22920 b22921 b22922 f22906 g5 g1
      omega
    have d22923 : (x (-3) 4).toNat = 0 := by
      have r22924 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22925 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e22926 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e22927 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e22928 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e22929 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e22930 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b22931 := hb (x (-6) 7)
      have b22932 := hb (x (-5) 6)
      have b22933 := hb (x (-4) 5)
      have b22934 := hb (x (-3) 4)
      have b22935 := hb (x (-2) 11)
      have b22936 := hb (x (-1) 10)
      have b22937 := hb (x 0 9)
      have b22938 := hb (x 1 8)
      clear * - r22924 e22925 e22926 e22927 e22928 e22929 e22930 b22931 b22932 b22933 b22934 b22935 b22936 b22937 b22938 d22907 f22906 g5 g1
      omega
    have d22939 : (x 1 11).toNat = 1 := by
      have r22940 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b22941 := hb (x (-3) 4)
      have b22942 := hb (x 1 11)
      have b22943 := hb (x 0 1 && x 0 12)
      have b22944 := hb (x (-1) 2 && x (-1) 13)
      have b22945 := hb (x (-2) 3 && x (-2) 14)
      clear * - r22940 b22941 b22942 b22943 b22944 b22945 g102 g103 g104 d22923
      omega
    have d22946 : (x 1 3).toNat = 1 := by
      have r22947 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
      have b22948 := hb (x 1 3)
      have b22949 := hb (x 1 11)
      clear * - r22947 b22948 b22949 d22939
      omega
    have d22950 : (x 4 12).toNat = 0 := by
      have r22951 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22952 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e22953 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b22954 := hb (x 1 3)
      have b22955 := hb (x 2 2)
      have b22956 := hb (x 3 13)
      have b22957 := hb (x 4 12)
      clear * - r22951 e22952 e22953 b22954 b22955 b22956 b22957 g32 d22946
      omega
    have d22958 : (x 4 1 && x 4 12).toNat = 0 := by
      have r22959 := hand2 (x 4 1) (x 4 12)
      have b22960 := hb (x 4 12)
      have b22961 := hb (x 4 1 && x 4 12)
      clear * - r22959 b22960 b22961 d22950
      omega
    have d22962 : (x 4 2 && x 4 12).toNat = 0 := by
      have r22963 := hand2 (x 4 2) (x 4 12)
      have b22964 := hb (x 4 12)
      have b22965 := hb (x 4 2 && x 4 12)
      clear * - r22963 b22964 b22965 d22950
      omega
    have d22966 : (x 2 2).toNat = 0 := by
      have r22967 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22968 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e22969 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b22970 := hb (x 1 3)
      have b22971 := hb (x 2 2)
      have b22972 := hb (x 3 13)
      have b22973 := hb (x 4 12)
      clear * - r22967 e22968 e22969 b22970 b22971 b22972 b22973 d22950 g32 d22946
      omega
    have d22974 : (x 4 13).toNat = 1 := by
      have r22975 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b22976 := hb (x 2 2)
      have b22977 := hb (x 4 13)
      have b22978 := hb (x 3 1 && x 3 14)
      clear * - r22975 b22976 b22977 b22978 g109 d22966
      omega
    have d22979 : (x 5 12).toNat = 0 := by
      have r22980 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22981 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e22982 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b22983 := hb (x 2 3)
      have b22984 := hb (x 3 2)
      have b22985 := hb (x 4 13)
      have b22986 := hb (x 5 12)
      clear * - r22980 e22981 e22982 b22983 b22984 b22985 b22986 d22974 g26
      omega
    have d22987 : (x 2 3).toNat = 0 := by
      have r22988 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22989 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e22990 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b22991 := hb (x 2 3)
      have b22992 := hb (x 3 2)
      have b22993 := hb (x 4 13)
      have b22994 := hb (x 5 12)
      clear * - r22988 e22989 e22990 b22991 b22992 b22993 b22994 d22979 d22974 g26
      omega
    have d22995 : (x 2 3 && x 2 14).toNat = 0 := by
      have r22996 := hand1 (x 2 3) (x 2 14)
      have b22997 := hb (x 2 3)
      have b22998 := hb (x 2 3 && x 2 14)
      clear * - r22996 b22997 b22998 d22987
      omega
    have d22999 : (x 5 11).toNat = 1 := by
      have r23000 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b23001 := hb (x 1 4)
      have b23002 := hb (x 5 11)
      have b23003 := hb (x 4 1 && x 4 12)
      have b23004 := hb (x 3 2 && x 3 13)
      have b23005 := hb (x 2 3 && x 2 14)
      clear * - r23000 b23001 b23002 b23003 b23004 b23005 d22958 g105 d22995 g16
      omega
    have d23006 : (x 5 3).toNat = 1 := by
      have r23007 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
      have b23008 := hb (x 5 3)
      have b23009 := hb (x 5 11)
      clear * - r23007 b23008 b23009 d22999
      omega
    have d23010 : (x 8 12).toNat = 0 := by
      have r23011 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23012 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e23013 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have b23014 := hb (x 5 3)
      have b23015 := hb (x 6 2)
      have b23016 := hb (x 7 13)
      have b23017 := hb (x 8 12)
      clear * - r23011 e23012 e23013 b23014 b23015 b23016 b23017 d23006
      omega
    have d23018 : (x 7 13).toNat = 0 := by
      have r23019 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23020 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e23021 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have b23022 := hb (x 5 3)
      have b23023 := hb (x 6 2)
      have b23024 := hb (x 7 13)
      have b23025 := hb (x 8 12)
      clear * - r23019 e23020 e23021 b23022 b23023 b23024 b23025 d23010 d23006
      omega
    have d23026 : (x 6 1 && x 6 14).toNat = 1 := by
      have r23027 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b23028 := hb (x 5 2)
      have b23029 := hb (x 7 13)
      have b23030 := hb (x 6 1 && x 6 14)
      clear * - r23027 b23028 b23029 b23030 d23018 g34
      omega
    have d23031 : (x 6 14).toNat = 1 := by
      have r23032 := hand2 (x 6 1) (x 6 14)
      have b23033 := hb (x 6 14)
      have b23034 := hb (x 6 1 && x 6 14)
      clear * - r23032 b23033 b23034 d23026
      omega
    have d23035 : (x 5 1).toNat = 0 := by
      have r23036 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b23037 := hb (x 5 1)
      have b23038 := hb (x 6 14)
      clear * - r23036 b23037 b23038 d23031
      omega
    have d23039 : (x 5 1 && x 5 11).toNat = 0 := by
      have r23040 := hand1 (x 5 1) (x 5 11)
      have b23041 := hb (x 5 1)
      have b23042 := hb (x 5 1 && x 5 11)
      clear * - r23040 b23041 b23042 d23035
      omega
    have d23043 : (x 6 10).toNat = 1 := by
      have r23044 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b23045 := hb (x 1 5)
      have b23046 := hb (x 6 10)
      have b23047 := hb (x 5 1 && x 5 11)
      have b23048 := hb (x 4 2 && x 4 12)
      have b23049 := hb (x 3 3 && x 3 13)
      have b23050 := hb (x 2 4 && x 2 14)
      clear * - r23044 b23045 b23046 b23047 b23048 b23049 b23050 d23039 d22962 g97 g98 g17
      omega
    have d23051 : (x 6 2).toNat = 1 := by
      have r23052 : (x 6 10).toNat ≤ (x 6 2).toNat := himp _ _ (hp10 6)
      have b23053 := hb (x 6 2)
      have b23054 := hb (x 6 10)
      clear * - r23052 b23053 b23054 d23043
      omega
    have r23055 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e23056 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e23057 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b23058 := hb (x 5 3)
    have b23059 := hb (x 6 2)
    have b23060 := hb (x 7 13)
    have b23061 := hb (x 8 12)
    linarith only [r23055, e23056, e23057, b23058, b23059, b23060, b23061, d23010, d23018, d23051, d23006]

theorem cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b1100 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-2) 3).toNat = 0)
    (g1 : (x (-2) 11).toNat = 0)
    (g2 : (x (-1) 2).toNat = 0)
    (g3 : (x (-1) 5).toNat = 0)
    (g4 : (x (-1) 9).toNat = 0)
    (g5 : (x (-1) 10).toNat = 0)
    (g6 : (x (-1) 11).toNat = 0)
    (g7 : (x (-1) 13).toNat = 0)
    (g8 : (x 0 1).toNat = 1)
    (g9 : (x 0 3).toNat = 1)
    (g10 : (x 0 4).toNat = 0)
    (g11 : (x 0 8).toNat = 0)
    (g12 : (x 0 12).toNat = 0)
    (g13 : (x 0 13).toNat = 1)
    (g14 : (x 0 14).toNat = 1)
    (g15 : (x 1 2).toNat = 0)
    (g16 : (x 1 4).toNat = 0)
    (g17 : (x 1 5).toNat = 0)
    (g18 : (x 1 6).toNat = 0)
    (g19 : (x 1 9).toNat = 0)
    (g20 : (x 1 10).toNat = 0)
    (g21 : (x 1 12).toNat = 0)
    (g22 : (x 1 13).toNat = 0)
    (g23 : (x 2 1).toNat = 1)
    (g24 : (x 2 5).toNat = 0)
    (g25 : (x 2 12).toNat = 0)
    (g26 : (x 3 2).toNat = 0)
    (g27 : (x 3 5).toNat = 0)
    (g28 : (x 3 6).toNat = 0)
    (g29 : (x 3 9).toNat = 0)
    (g30 : (x 3 10).toNat = 0)
    (g31 : (x 3 11).toNat = 0)
    (g32 : (x 3 13).toNat = 0)
    (g33 : (x 4 10).toNat = 1)
    (g34 : (x 5 2).toNat = 0)
    (g35 : (x 5 6).toNat = 0)
    (g36 : (x 5 9).toNat = 0)
    (g37 : (x 6 5).toNat = 0)
    (g38 : (x 6 8).toNat = 0)
    (g39 : (x 6 9).toNat = 0)
    (g40 : (x 7 4).toNat = 0)
    (g41 : (x 6 6 && x 6 8).toNat = 0)
    (g42 : (x 5 7 && x 5 9).toNat = 0)
    (g43 : (x 3 9 && x 3 11).toNat = 0)
    (g44 : (x 2 10 && x 2 12).toNat = 0)
    (g45 : (x 1 11 && x 1 13).toNat = 0)
    (g46 : (x 0 12 && x 0 14).toNat = 0)
    (g47 : (x 0 1 && x 0 4).toNat = 0)
    (g48 : (x (-1) 2 && x (-1) 5).toNat = 0)
    (g49 : (x (-2) 3 && x (-2) 6).toNat = 0)
    (g50 : (x 1 2 && x 1 7).toNat = 0)
    (g51 : (x (-1) 4 && x (-1) 9).toNat = 0)
    (g52 : (x 1 2 && x 1 8).toNat = 0)
    (g53 : (x (-1) 4 && x (-1) 10).toNat = 0)
    (g54 : (x (-2) 5 && x (-2) 11).toNat = 0)
    (g55 : (x 3 2 && x 3 8).toNat = 0)
    (g56 : (x 1 4 && x 1 10).toNat = 0)
    (g57 : (x 0 5 && x 0 11).toNat = 0)
    (g58 : (x 6 2 && x 6 8).toNat = 0)
    (g59 : (x 5 3 && x 5 9).toNat = 0)
    (g60 : (x 3 5 && x 3 11).toNat = 0)
    (g61 : (x 2 6 && x 2 12).toNat = 0)
    (g62 : (x 1 7 && x 1 13).toNat = 0)
    (g63 : (x 7 4 && x 7 10).toNat = 0)
    (g64 : (x 6 5 && x 6 11).toNat = 0)
    (g65 : (x 5 6 && x 5 12).toNat = 0)
    (g66 : (x 3 8 && x 3 14).toNat = 0)
    (g67 : (x 7 8 && x 7 14).toNat = 0)
    (g68 : (x 3 1 && x 3 8).toNat = 0)
    (g69 : (x 1 3 && x 1 10).toNat = 0)
    (g70 : (x 0 4 && x 0 11).toNat = 0)
    (g71 : (x (-1) 5 && x (-1) 12).toNat = 0)
    (g72 : (x 7 1 && x 7 8).toNat = 0)
    (g73 : (x 6 2 && x 6 9).toNat = 0)
    (g74 : (x 5 3 && x 5 10).toNat = 0)
    (g75 : (x 3 5 && x 3 12).toNat = 0)
    (g76 : (x 2 6 && x 2 13).toNat = 0)
    (g77 : (x 1 7 && x 1 14).toNat = 0)
    (g78 : (x (-1) 2 && x (-1) 11).toNat = 0)
    (g79 : (x (-2) 3 && x (-2) 12).toNat = 0)
    (g80 : (x 1 2 && x 1 11).toNat = 0)
    (g81 : (x 0 3 && x 0 12).toNat = 0)
    (g82 : (x (-1) 4 && x (-1) 13).toNat = 0)
    (g83 : (x 3 1 && x 3 10).toNat = 0)
    (g84 : (x 1 3 && x 1 12).toNat = 0)
    (g85 : (x 0 4 && x 0 13).toNat = 0)
    (g86 : (x (-1) 5 && x (-1) 14).toNat = 0)
    (g87 : (x 5 2 && x 5 11).toNat = 0)
    (g88 : (x 3 4 && x 3 13).toNat = 0)
    (g89 : (x 2 5 && x 2 14).toNat = 0)
    (g90 : (x 7 4 && x 7 13).toNat = 0)
    (g91 : (x 6 5 && x 6 14).toNat = 0)
    (g92 : (x (-1) 2 && x (-1) 12).toNat = 0)
    (g93 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g94 : (x 1 1 && x 1 11).toNat = 0)
    (g95 : (x 0 2 && x 0 12).toNat = 0)
    (g96 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g97 : (x 3 3 && x 3 13).toNat = 0)
    (g98 : (x 2 4 && x 2 14).toNat = 0)
    (g99 : (x 5 2 && x 5 12).toNat = 0)
    (g100 : (x 3 4 && x 3 14).toNat = 0)
    (g101 : (x 7 4 && x 7 14).toNat = 0)
    (g102 : (x 0 1 && x 0 12).toNat = 0)
    (g103 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g104 : (x (-2) 3 && x (-2) 14).toNat = 0)
    (g105 : (x 3 2 && x 3 13).toNat = 0)
    (g106 : (x 7 1 && x 7 12).toNat = 0)
    (g107 : (x 6 2 && x 6 13).toNat = 0)
    (g108 : (x 5 3 && x 5 14).toNat = 0)
    (g109 : (x 3 1 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b1100_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83 g84 g85 g86 g87 g88 g89 g90 g91 g92 g93 g94 g95 g96 g97 g98 g99 g100 g101 g102 g103 g104 g105 g106 g107 g108 g109
