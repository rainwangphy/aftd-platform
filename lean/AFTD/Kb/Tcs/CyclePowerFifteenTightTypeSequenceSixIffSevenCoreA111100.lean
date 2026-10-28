import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_a111100

Topic: combinatorics   Node: d5f3e22837c8

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_six_iff_seven_core: under the layer-free tight-cover constraints for k = 15 and 79 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_a111100_aux (x : ℤ → Fin 16 → Bool)
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
    (g3 : (x (-2) 7).toNat = 0)
    (g4 : (x (-2) 10).toNat = 0)
    (g5 : (x (-2) 11).toNat = 0)
    (g6 : (x (-1) 3).toNat = 0)
    (g7 : (x (-1) 5).toNat = 0)
    (g8 : (x (-1) 6).toNat = 0)
    (g9 : (x (-1) 7).toNat = 0)
    (g10 : (x (-1) 9).toNat = 0)
    (g11 : (x (-1) 10).toNat = 0)
    (g12 : (x (-1) 13).toNat = 0)
    (g13 : (x 0 2).toNat = 1)
    (g14 : (x 0 4).toNat = 1)
    (g15 : (x 0 5).toNat = 1)
    (g16 : (x 0 7).toNat = 0)
    (g17 : (x 0 8).toNat = 0)
    (g18 : (x 0 9).toNat = 0)
    (g19 : (x 1 2).toNat = 0)
    (g20 : (x 1 4).toNat = 0)
    (g21 : (x 1 5).toNat = 0)
    (g22 : (x 1 6).toNat = 0)
    (g23 : (x 2 5).toNat = 0)
    (g24 : (x 3 4).toNat = 0)
    (g25 : (x 0 4 && x 0 8).toNat = 0)
    (g26 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g27 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g28 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g29 : (x 1 4 && x 1 8).toNat = 0)
    (g30 : (x (-1) 6 && x (-1) 10).toNat = 0)
    (g31 : (x (-2) 7 && x (-2) 11).toNat = 0)
    (g32 : (x 3 4 && x 3 8).toNat = 0)
    (g33 : (x 2 5 && x 2 9).toNat = 0)
    (g34 : (x 1 6 && x 1 10).toNat = 0)
    (g35 : (x 0 7 && x 0 11).toNat = 0)
    (g36 : (x 5 4 && x 5 8).toNat = 0)
    (g37 : (x 4 5 && x 4 9).toNat = 0)
    (g38 : (x 3 6 && x 3 10).toNat = 0)
    (g39 : (x 2 7 && x 2 11).toNat = 0)
    (g40 : (x 1 8 && x 1 12).toNat = 0)
    (g41 : (x (-2) 1 && x (-2) 6).toNat = 0)
    (g42 : (x (-3) 2 && x (-3) 7).toNat = 0)
    (g43 : (x 6 3 && x 6 8).toNat = 0)
    (g44 : (x 5 4 && x 5 9).toNat = 0)
    (g45 : (x 4 5 && x 4 10).toNat = 0)
    (g46 : (x 3 6 && x 3 11).toNat = 0)
    (g47 : (x 2 7 && x 2 12).toNat = 0)
    (g48 : (x 1 8 && x 1 13).toNat = 0)
    (g49 : (x 0 2 && x 0 8).toNat = 0)
    (g50 : (x (-1) 3 && x (-1) 9).toNat = 0)
    (g51 : (x (-2) 4 && x (-2) 10).toNat = 0)
    (g52 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g53 : (x 1 2 && x 1 8).toNat = 0)
    (g54 : (x (-1) 4 && x (-1) 10).toNat = 0)
    (g55 : (x (-2) 5 && x (-2) 11).toNat = 0)
    (g56 : (x (-3) 6 && x (-3) 12).toNat = 0)
    (g57 : (x (-4) 7 && x (-4) 13).toNat = 0)
    (g58 : (x 6 2 && x 6 8).toNat = 0)
    (g59 : (x 5 3 && x 5 9).toNat = 0)
    (g60 : (x 4 4 && x 4 10).toNat = 0)
    (g61 : (x 3 5 && x 3 11).toNat = 0)
    (g62 : (x 2 6 && x 2 12).toNat = 0)
    (g63 : (x 1 7 && x 1 13).toNat = 0)
    (g64 : (x 0 8 && x 0 14).toNat = 0)
    (g65 : (x 6 1 && x 6 8).toNat = 0)
    (g66 : (x 5 2 && x 5 9).toNat = 0)
    (g67 : (x 4 3 && x 4 10).toNat = 0)
    (g68 : (x 3 4 && x 3 11).toNat = 0)
    (g69 : (x 2 5 && x 2 12).toNat = 0)
    (g70 : (x 1 6 && x 1 13).toNat = 0)
    (g71 : (x 0 7 && x 0 14).toNat = 0)
    (g72 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g73 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g74 : (x 3 4 && x 3 13).toNat = 0)
    (g75 : (x 2 5 && x 2 14).toNat = 0)
    (g76 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g77 : (x 2 4 && x 2 14).toNat = 0)
    (g78 : (x 3 4 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d39156 : (x 0 3 && x 0 9).toNat = 0 := by
    have r39157 := hand2 (x 0 3) (x 0 9)
    have b39158 := hb (x 0 9)
    have b39159 := hb (x 0 3 && x 0 9)
    clear * - r39157 b39158 b39159 g18
    omega
  have d39160 : (x 0 9 && x 0 14).toNat = 0 := by
    have r39161 := hand1 (x 0 9) (x 0 14)
    have b39162 := hb (x 0 9)
    have b39163 := hb (x 0 9 && x 0 14)
    clear * - r39161 b39162 b39163 g18
    omega
  have d39164 : (x 0 9 && x 0 13).toNat = 0 := by
    have r39165 := hand1 (x 0 9) (x 0 13)
    have b39166 := hb (x 0 9)
    have b39167 := hb (x 0 9 && x 0 13)
    clear * - r39165 b39166 b39167 g18
    omega
  have d39168 : (x 0 5 && x 0 9).toNat = 0 := by
    have r39169 := hand2 (x 0 5) (x 0 9)
    have b39170 := hb (x 0 9)
    have b39171 := hb (x 0 5 && x 0 9)
    clear * - r39169 b39170 b39171 g18
    omega
  cases h39172 : x 1 1
  · have f39173 : (x 1 1).toNat = 0 := by rw [h39172]; rfl
    cases h39174 : x 1 3
    · have f39175 : (x 1 3).toNat = 0 := by rw [h39174]; rfl
      cases h39176 : x 1 7
      · have f39177 : (x 1 7).toNat = 0 := by rw [h39176]; rfl
        cases h39178 : x (-1) 8
        · have f39179 : (x (-1) 8).toNat = 0 := by rw [h39178]; rfl
          have d39180 : (x 7 7).toNat = 1 := by
            have r39181 : 1 ≤ (x 7 7).toNat + (x 6 1 && x 6 8).toNat + (x 5 2 && x 5 9).toNat + (x 4 3 && x 4 10).toNat + (x 3 4 && x 3 11).toNat + (x 2 5 && x 2 12).toNat + (x 1 6 && x 1 13).toNat + (x 0 7 && x 0 14).toNat + (x (-1) 8).toNat := by have q := hcov7 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b39182 := hb (x (-1) 8)
            have b39183 := hb (x 7 7)
            have b39184 := hb (x 6 1 && x 6 8)
            have b39185 := hb (x 5 2 && x 5 9)
            have b39186 := hb (x 4 3 && x 4 10)
            have b39187 := hb (x 3 4 && x 3 11)
            have b39188 := hb (x 2 5 && x 2 12)
            have b39189 := hb (x 1 6 && x 1 13)
            have b39190 := hb (x 0 7 && x 0 14)
            clear * - r39181 b39182 b39183 b39184 b39185 b39186 b39187 b39188 b39189 b39190 g65 g66 g67 g68 g69 g70 g71 f39179
            omega
          have d39191 : (x 14 8).toNat = 0 := by
            have r39192 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39193 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
            have e39194 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
            have e39195 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
            have e39196 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
            have e39197 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
            have e39198 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
            have b39199 := hb (x 7 7)
            have b39200 := hb (x 8 6)
            have b39201 := hb (x 9 5)
            have b39202 := hb (x 10 4)
            have b39203 := hb (x 11 11)
            have b39204 := hb (x 12 10)
            have b39205 := hb (x 13 9)
            have b39206 := hb (x 14 8)
            clear * - r39192 e39193 e39194 e39195 e39196 e39197 e39198 b39199 b39200 b39201 b39202 b39203 b39204 b39205 b39206 d39180
            omega
          have d39207 : (x 13 9).toNat = 0 := by
            have r39208 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39209 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
            have e39210 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
            have e39211 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
            have e39212 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
            have e39213 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
            have e39214 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
            have b39215 := hb (x 7 7)
            have b39216 := hb (x 8 6)
            have b39217 := hb (x 9 5)
            have b39218 := hb (x 10 4)
            have b39219 := hb (x 11 11)
            have b39220 := hb (x 12 10)
            have b39221 := hb (x 13 9)
            have b39222 := hb (x 14 8)
            clear * - r39208 e39209 e39210 e39211 e39212 e39213 e39214 b39215 b39216 b39217 b39218 b39219 b39220 b39221 b39222 d39191 d39180
            omega
          have d39223 : (x 12 10).toNat = 0 := by
            have r39224 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39225 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
            have e39226 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
            have e39227 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
            have e39228 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
            have e39229 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
            have e39230 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
            have b39231 := hb (x 7 7)
            have b39232 := hb (x 8 6)
            have b39233 := hb (x 9 5)
            have b39234 := hb (x 10 4)
            have b39235 := hb (x 11 11)
            have b39236 := hb (x 12 10)
            have b39237 := hb (x 13 9)
            have b39238 := hb (x 14 8)
            clear * - r39224 e39225 e39226 e39227 e39228 e39229 e39230 b39231 b39232 b39233 b39234 b39235 b39236 b39237 b39238 d39191 d39207 d39180
            omega
          have d39239 : (x 11 11).toNat = 0 := by
            have r39240 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39241 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
            have e39242 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
            have e39243 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
            have e39244 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
            have e39245 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
            have e39246 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
            have b39247 := hb (x 7 7)
            have b39248 := hb (x 8 6)
            have b39249 := hb (x 9 5)
            have b39250 := hb (x 10 4)
            have b39251 := hb (x 11 11)
            have b39252 := hb (x 12 10)
            have b39253 := hb (x 13 9)
            have b39254 := hb (x 14 8)
            clear * - r39240 e39241 e39242 e39243 e39244 e39245 e39246 b39247 b39248 b39249 b39250 b39251 b39252 b39253 b39254 d39191 d39207 d39223 d39180
            omega
          have d39255 : (x 10 4).toNat = 0 := by
            have r39256 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39257 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
            have e39258 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
            have e39259 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
            have e39260 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
            have e39261 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
            have e39262 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
            have b39263 := hb (x 7 7)
            have b39264 := hb (x 8 6)
            have b39265 := hb (x 9 5)
            have b39266 := hb (x 10 4)
            have b39267 := hb (x 11 11)
            have b39268 := hb (x 12 10)
            have b39269 := hb (x 13 9)
            have b39270 := hb (x 14 8)
            clear * - r39256 e39257 e39258 e39259 e39260 e39261 e39262 b39263 b39264 b39265 b39266 b39267 b39268 b39269 b39270 d39191 d39207 d39223 d39239 d39180
            omega
          have d39271 : (x 9 5).toNat = 0 := by
            have r39272 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39273 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
            have e39274 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
            have e39275 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
            have e39276 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
            have e39277 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
            have e39278 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
            have b39279 := hb (x 7 7)
            have b39280 := hb (x 8 6)
            have b39281 := hb (x 9 5)
            have b39282 := hb (x 10 4)
            have b39283 := hb (x 11 11)
            have b39284 := hb (x 12 10)
            have b39285 := hb (x 13 9)
            have b39286 := hb (x 14 8)
            clear * - r39272 e39273 e39274 e39275 e39276 e39277 e39278 b39279 b39280 b39281 b39282 b39283 b39284 b39285 b39286 d39191 d39207 d39223 d39239 d39255 d39180
            omega
          have d39287 : (x 8 6).toNat = 0 := by
            have r39288 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39289 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
            have e39290 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
            have e39291 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
            have e39292 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
            have e39293 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
            have e39294 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
            have b39295 := hb (x 7 7)
            have b39296 := hb (x 8 6)
            have b39297 := hb (x 9 5)
            have b39298 := hb (x 10 4)
            have b39299 := hb (x 11 11)
            have b39300 := hb (x 12 10)
            have b39301 := hb (x 13 9)
            have b39302 := hb (x 14 8)
            clear * - r39288 e39289 e39290 e39291 e39292 e39293 e39294 b39295 b39296 b39297 b39298 b39299 b39300 b39301 b39302 d39191 d39207 d39223 d39239 d39255 d39271 d39180
            omega
          have d39303 : (x 8 1 && x 8 6).toNat = 0 := by
            have r39304 := hand2 (x 8 1) (x 8 6)
            have b39305 := hb (x 8 6)
            have b39306 := hb (x 8 1 && x 8 6)
            clear * - r39304 b39305 b39306 d39287
            omega
          have d39307 : (x 7 2 && x 7 7).toNat = 1 := by
            have r39308 : 1 ≤ (x 9 5).toNat + (x 8 1 && x 8 6).toNat + (x 7 2 && x 7 7).toNat + (x 6 3 && x 6 8).toNat + (x 5 4 && x 5 9).toNat + (x 4 5 && x 4 10).toNat + (x 3 6 && x 3 11).toNat + (x 2 7 && x 2 12).toNat + (x 1 8 && x 1 13).toNat + (x 0 9 && x 0 14).toNat + (x (-1) 10).toNat := by have q := hcov5 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b39309 := hb (x (-1) 10)
            have b39310 := hb (x 9 5)
            have b39311 := hb (x 8 1 && x 8 6)
            have b39312 := hb (x 7 2 && x 7 7)
            have b39313 := hb (x 6 3 && x 6 8)
            have b39314 := hb (x 5 4 && x 5 9)
            have b39315 := hb (x 4 5 && x 4 10)
            have b39316 := hb (x 3 6 && x 3 11)
            have b39317 := hb (x 2 7 && x 2 12)
            have b39318 := hb (x 1 8 && x 1 13)
            have b39319 := hb (x 0 9 && x 0 14)
            clear * - r39308 b39309 b39310 b39311 b39312 b39313 b39314 b39315 b39316 b39317 b39318 b39319 d39271 d39303 g43 g44 g45 g46 g47 g48 d39160 g11
            omega
          have d39320 : (x 7 2).toNat = 1 := by
            have r39321 := hand1 (x 7 2) (x 7 7)
            have b39322 := hb (x 7 2)
            have b39323 := hb (x 7 2 && x 7 7)
            clear * - r39321 b39322 b39323 d39307
            omega
          have d39324 : (x 7 14).toNat = 1 := by
            have r39325 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
            have b39326 := hb (x 7 2)
            have b39327 := hb (x 7 14)
            clear * - r39325 b39326 b39327 d39320
            omega
          have d39328 : (x 6 1).toNat = 0 := by
            have r39329 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b39330 := hb (x 6 1)
            have b39331 := hb (x 7 14)
            clear * - r39329 b39330 b39331 d39324
            omega
          have d39332 : (x 6 1 && x 6 14).toNat = 0 := by
            have r39333 := hand1 (x 6 1) (x 6 14)
            have b39334 := hb (x 6 1)
            have b39335 := hb (x 6 1 && x 6 14)
            clear * - r39333 b39334 b39335 d39328
            omega
          have d39336 : (x 6 1 && x 6 11).toNat = 0 := by
            have r39337 := hand1 (x 6 1) (x 6 11)
            have b39338 := hb (x 6 1)
            have b39339 := hb (x 6 1 && x 6 11)
            clear * - r39337 b39338 b39339 d39328
            omega
          have d39340 : (x 6 13).toNat = 0 := by
            have r39341 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
            have b39342 := hb (x 6 1)
            have b39343 := hb (x 6 13)
            clear * - r39341 b39342 b39343 d39328
            omega
          have d39344 : (x 6 5).toNat = 0 := by
            have r39345 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
            have b39346 := hb (x 6 5)
            have b39347 := hb (x 6 13)
            clear * - r39345 b39346 b39347 d39340
            omega
          have d39348 : (x 9 12).toNat = 0 := by
            have r39349 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39350 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
            have e39351 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
            have b39352 := hb (x 6 3)
            have b39353 := hb (x 7 2)
            have b39354 := hb (x 8 13)
            have b39355 := hb (x 9 12)
            clear * - r39349 e39350 e39351 b39352 b39353 b39354 b39355 d39320
            omega
          have d39356 : (x 9 2 && x 9 12).toNat = 0 := by
            have r39357 := hand2 (x 9 2) (x 9 12)
            have b39358 := hb (x 9 12)
            have b39359 := hb (x 9 2 && x 9 12)
            clear * - r39357 b39358 b39359 d39348
            omega
          have d39360 : (x 9 4).toNat = 0 := by
            have r39361 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
            have b39362 := hb (x 9 4)
            have b39363 := hb (x 9 12)
            clear * - r39361 b39362 b39363 d39348
            omega
          have d39364 : (x 8 13).toNat = 0 := by
            have r39365 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39366 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
            have e39367 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
            have b39368 := hb (x 6 3)
            have b39369 := hb (x 7 2)
            have b39370 := hb (x 8 13)
            have b39371 := hb (x 9 12)
            clear * - r39365 e39366 e39367 b39368 b39369 b39370 b39371 d39348 d39320
            omega
          have d39372 : (x 8 3 && x 8 13).toNat = 0 := by
            have r39373 := hand2 (x 8 3) (x 8 13)
            have b39374 := hb (x 8 13)
            have b39375 := hb (x 8 3 && x 8 13)
            clear * - r39373 b39374 b39375 d39364
            omega
          have d39376 : (x 8 5).toNat = 0 := by
            have r39377 : (x 8 5).toNat ≤ (x 8 13).toNat := himp _ _ (hp5 8)
            have b39378 := hb (x 8 5)
            have b39379 := hb (x 8 13)
            clear * - r39377 b39378 b39379 d39364
            omega
          have d39380 : (x 6 3).toNat = 0 := by
            have r39381 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39382 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
            have e39383 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
            have b39384 := hb (x 6 3)
            have b39385 := hb (x 7 2)
            have b39386 := hb (x 8 13)
            have b39387 := hb (x 9 12)
            clear * - r39381 e39382 e39383 b39384 b39385 b39386 b39387 d39348 d39364 d39320
            omega
          have d39388 : (x 6 3 && x 6 7).toNat = 0 := by
            have r39389 := hand1 (x 6 3) (x 6 7)
            have b39390 := hb (x 6 3)
            have b39391 := hb (x 6 3 && x 6 7)
            clear * - r39389 b39390 b39391 d39380
            omega
          have d39392 : (x 6 11).toNat = 0 := by
            have r39393 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
            have b39394 := hb (x 6 3)
            have b39395 := hb (x 6 11)
            clear * - r39393 b39394 b39395 d39380
            omega
          have d39396 : (x 7 2 && x 7 6).toNat = 1 := by
            have r39397 : 1 ≤ (x 9 4).toNat + (x 8 1 && x 8 5).toNat + (x 7 2 && x 7 6).toNat + (x 6 3 && x 6 7).toNat + (x 5 4 && x 5 8).toNat + (x 4 5 && x 4 9).toNat + (x 3 6 && x 3 10).toNat + (x 2 7 && x 2 11).toNat + (x 1 8 && x 1 12).toNat + (x 0 9 && x 0 13).toNat + (x (-1) 10 && x (-1) 14).toNat + (x (-2) 11).toNat := by have q := hcov4 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39398 : (x 8 1 && x 8 5).toNat = (x 8 5).toNat := handr _ _ (fun h => hp13 8 (hp5 8 (h)))
            have e39399 : (x (-1) 10 && x (-1) 14).toNat = (x (-1) 10).toNat := handl _ _ (fun h => hp2 (-1) (hp10 (-1) (h)))
            have b39400 := hb (x (-2) 11)
            have b39401 := hb (x (-1) 10)
            have b39402 := hb (x 8 5)
            have b39403 := hb (x 9 4)
            have b39404 := hb (x 7 2 && x 7 6)
            have b39405 := hb (x 6 3 && x 6 7)
            have b39406 := hb (x 5 4 && x 5 8)
            have b39407 := hb (x 4 5 && x 4 9)
            have b39408 := hb (x 3 6 && x 3 10)
            have b39409 := hb (x 2 7 && x 2 11)
            have b39410 := hb (x 1 8 && x 1 12)
            have b39411 := hb (x 0 9 && x 0 13)
            clear * - r39397 e39398 e39399 b39400 b39401 b39402 b39403 b39404 b39405 b39406 b39407 b39408 b39409 b39410 b39411 d39360 d39376 d39388 g36 g37 g38 g39 g40 d39164 g11 g5
            omega
          have d39412 : (x 7 6).toNat = 1 := by
            have r39413 := hand2 (x 7 2) (x 7 6)
            have b39414 := hb (x 7 6)
            have b39415 := hb (x 7 2 && x 7 6)
            clear * - r39413 b39414 b39415 d39396
            omega
          have d39416 : (x 13 8).toNat = 0 := by
            have r39417 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39418 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
            have e39419 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
            have e39420 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
            have e39421 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
            have e39422 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
            have e39423 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
            have b39424 := hb (x 6 7)
            have b39425 := hb (x 7 6)
            have b39426 := hb (x 8 5)
            have b39427 := hb (x 9 4)
            have b39428 := hb (x 10 11)
            have b39429 := hb (x 11 10)
            have b39430 := hb (x 12 9)
            have b39431 := hb (x 13 8)
            clear * - r39417 e39418 e39419 e39420 e39421 e39422 e39423 b39424 b39425 b39426 b39427 b39428 b39429 b39430 b39431 d39360 d39376 d39412
            omega
          have d39432 : (x 12 9).toNat = 0 := by
            have r39433 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39434 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
            have e39435 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
            have e39436 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
            have e39437 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
            have e39438 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
            have e39439 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
            have b39440 := hb (x 6 7)
            have b39441 := hb (x 7 6)
            have b39442 := hb (x 8 5)
            have b39443 := hb (x 9 4)
            have b39444 := hb (x 10 11)
            have b39445 := hb (x 11 10)
            have b39446 := hb (x 12 9)
            have b39447 := hb (x 13 8)
            clear * - r39433 e39434 e39435 e39436 e39437 e39438 e39439 b39440 b39441 b39442 b39443 b39444 b39445 b39446 b39447 d39416 d39360 d39376 d39412
            omega
          have d39448 : (x 11 10).toNat = 0 := by
            have r39449 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39450 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
            have e39451 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
            have e39452 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
            have e39453 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
            have e39454 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
            have e39455 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
            have b39456 := hb (x 6 7)
            have b39457 := hb (x 7 6)
            have b39458 := hb (x 8 5)
            have b39459 := hb (x 9 4)
            have b39460 := hb (x 10 11)
            have b39461 := hb (x 11 10)
            have b39462 := hb (x 12 9)
            have b39463 := hb (x 13 8)
            clear * - r39449 e39450 e39451 e39452 e39453 e39454 e39455 b39456 b39457 b39458 b39459 b39460 b39461 b39462 b39463 d39416 d39432 d39360 d39376 d39412
            omega
          have d39464 : (x 10 11).toNat = 0 := by
            have r39465 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39466 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
            have e39467 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
            have e39468 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
            have e39469 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
            have e39470 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
            have e39471 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
            have b39472 := hb (x 6 7)
            have b39473 := hb (x 7 6)
            have b39474 := hb (x 8 5)
            have b39475 := hb (x 9 4)
            have b39476 := hb (x 10 11)
            have b39477 := hb (x 11 10)
            have b39478 := hb (x 12 9)
            have b39479 := hb (x 13 8)
            clear * - r39465 e39466 e39467 e39468 e39469 e39470 e39471 b39472 b39473 b39474 b39475 b39476 b39477 b39478 b39479 d39416 d39432 d39448 d39360 d39376 d39412
            omega
          have d39480 : (x 10 1 && x 10 11).toNat = 0 := by
            have r39481 := hand2 (x 10 1) (x 10 11)
            have b39482 := hb (x 10 11)
            have b39483 := hb (x 10 1 && x 10 11)
            clear * - r39481 b39482 b39483 d39464
            omega
          have d39484 : (x 7 4 && x 7 14).toNat = 1 := by
            have r39485 : 1 ≤ (x 11 10).toNat + (x 10 1 && x 10 11).toNat + (x 9 2 && x 9 12).toNat + (x 8 3 && x 8 13).toNat + (x 7 4 && x 7 14).toNat + (x 6 5).toNat := by have q := hcov10 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b39486 := hb (x 6 5)
            have b39487 := hb (x 11 10)
            have b39488 := hb (x 10 1 && x 10 11)
            have b39489 := hb (x 9 2 && x 9 12)
            have b39490 := hb (x 8 3 && x 8 13)
            have b39491 := hb (x 7 4 && x 7 14)
            clear * - r39485 b39486 b39487 b39488 b39489 b39490 b39491 d39448 d39480 d39356 d39372 d39344
            omega
          have d39492 : (x 7 4).toNat = 1 := by
            have r39493 := hand1 (x 7 4) (x 7 14)
            have b39494 := hb (x 7 4)
            have b39495 := hb (x 7 4 && x 7 14)
            clear * - r39493 b39494 b39495 d39484
            omega
          have d39496 : (x 7 12).toNat = 1 := by
            have r39497 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
            have b39498 := hb (x 7 4)
            have b39499 := hb (x 7 12)
            clear * - r39497 b39498 b39499 d39492
            omega
          have d39500 : (x 5 2).toNat = 0 := by
            have r39501 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39502 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
            have e39503 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
            have b39504 := hb (x 4 3)
            have b39505 := hb (x 5 2)
            have b39506 := hb (x 6 13)
            have b39507 := hb (x 7 12)
            clear * - r39501 e39502 e39503 b39504 b39505 b39506 b39507 d39496 d39340
            omega
          have d39508 : (x 5 2 && x 5 12).toNat = 0 := by
            have r39509 := hand1 (x 5 2) (x 5 12)
            have b39510 := hb (x 5 2)
            have b39511 := hb (x 5 2 && x 5 12)
            clear * - r39509 b39510 b39511 d39500
            omega
          have d39512 : (x 7 13).toNat = 1 := by
            have r39513 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b39514 := hb (x 5 2)
            have b39515 := hb (x 7 13)
            have b39516 := hb (x 6 1 && x 6 14)
            clear * - r39513 b39514 b39515 b39516 d39332 d39500
            omega
          have d39517 : (x 8 12).toNat = 0 := by
            have r39518 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39519 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
            have e39520 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
            have b39521 := hb (x 5 3)
            have b39522 := hb (x 6 2)
            have b39523 := hb (x 7 13)
            have b39524 := hb (x 8 12)
            clear * - r39518 e39519 e39520 b39521 b39522 b39523 b39524 d39512
            omega
          have d39525 : (x 6 2).toNat = 0 := by
            have r39526 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39527 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
            have e39528 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
            have b39529 := hb (x 5 3)
            have b39530 := hb (x 6 2)
            have b39531 := hb (x 7 13)
            have b39532 := hb (x 8 12)
            clear * - r39526 e39527 e39528 b39529 b39530 b39531 b39532 d39517 d39512
            omega
          have d39533 : (x 5 3).toNat = 0 := by
            have r39534 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39535 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
            have e39536 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
            have b39537 := hb (x 5 3)
            have b39538 := hb (x 6 2)
            have b39539 := hb (x 7 13)
            have b39540 := hb (x 8 12)
            clear * - r39534 e39535 e39536 b39537 b39538 b39539 b39540 d39517 d39512 d39525
            omega
          have d39541 : (x 5 11).toNat = 0 := by
            have r39542 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
            have b39543 := hb (x 5 3)
            have b39544 := hb (x 5 11)
            clear * - r39542 b39543 b39544 d39533
            omega
          have d39545 : (x 4 3).toNat = 0 := by
            have r39546 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39547 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
            have e39548 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
            have b39549 := hb (x 4 3)
            have b39550 := hb (x 5 2)
            have b39551 := hb (x 6 13)
            have b39552 := hb (x 7 12)
            clear * - r39546 e39547 e39548 b39549 b39550 b39551 b39552 d39496 d39340 d39500
            omega
          have d39553 : (x 4 3 && x 4 13).toNat = 0 := by
            have r39554 := hand1 (x 4 3) (x 4 13)
            have b39555 := hb (x 4 3)
            have b39556 := hb (x 4 3 && x 4 13)
            clear * - r39554 b39555 b39556 d39545
            omega
          have d39557 : (x 7 10).toNat = 1 := by
            have r39558 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b39559 := hb (x 2 5)
            have b39560 := hb (x 7 10)
            have b39561 := hb (x 6 1 && x 6 11)
            have b39562 := hb (x 5 2 && x 5 12)
            have b39563 := hb (x 4 3 && x 4 13)
            have b39564 := hb (x 3 4 && x 3 14)
            clear * - r39558 b39559 b39560 b39561 b39562 b39563 b39564 d39336 d39508 d39553 g78 g23
            omega
          have d39565 : (x 9 8).toNat = 0 := by
            have r39566 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39567 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
            have e39568 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
            have e39569 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
            have e39570 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
            have e39571 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
            have e39572 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
            have b39573 := hb (x 2 7)
            have b39574 := hb (x 3 6)
            have b39575 := hb (x 4 5)
            have b39576 := hb (x 5 4)
            have b39577 := hb (x 6 11)
            have b39578 := hb (x 7 10)
            have b39579 := hb (x 8 9)
            have b39580 := hb (x 9 8)
            clear * - r39566 e39567 e39568 e39569 e39570 e39571 e39572 b39573 b39574 b39575 b39576 b39577 b39578 b39579 b39580 d39557 d39392
            omega
          have d39581 : (x 8 9).toNat = 0 := by
            have r39582 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39583 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
            have e39584 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
            have e39585 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
            have e39586 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
            have e39587 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
            have e39588 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
            have b39589 := hb (x 2 7)
            have b39590 := hb (x 3 6)
            have b39591 := hb (x 4 5)
            have b39592 := hb (x 5 4)
            have b39593 := hb (x 6 11)
            have b39594 := hb (x 7 10)
            have b39595 := hb (x 8 9)
            have b39596 := hb (x 9 8)
            clear * - r39582 e39583 e39584 e39585 e39586 e39587 e39588 b39589 b39590 b39591 b39592 b39593 b39594 b39595 b39596 d39565 d39557 d39392
            omega
          have d39597 : (x 5 4).toNat = 0 := by
            have r39598 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39599 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
            have e39600 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
            have e39601 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
            have e39602 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
            have e39603 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
            have e39604 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
            have b39605 := hb (x 2 7)
            have b39606 := hb (x 3 6)
            have b39607 := hb (x 4 5)
            have b39608 := hb (x 5 4)
            have b39609 := hb (x 6 11)
            have b39610 := hb (x 7 10)
            have b39611 := hb (x 8 9)
            have b39612 := hb (x 9 8)
            clear * - r39598 e39599 e39600 e39601 e39602 e39603 e39604 b39605 b39606 b39607 b39608 b39609 b39610 b39611 b39612 d39565 d39581 d39557 d39392
            omega
          have d39613 : (x 4 5).toNat = 0 := by
            have r39614 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39615 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
            have e39616 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
            have e39617 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
            have e39618 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
            have e39619 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
            have e39620 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
            have b39621 := hb (x 2 7)
            have b39622 := hb (x 3 6)
            have b39623 := hb (x 4 5)
            have b39624 := hb (x 5 4)
            have b39625 := hb (x 6 11)
            have b39626 := hb (x 7 10)
            have b39627 := hb (x 8 9)
            have b39628 := hb (x 9 8)
            clear * - r39614 e39615 e39616 e39617 e39618 e39619 e39620 b39621 b39622 b39623 b39624 b39625 b39626 b39627 b39628 d39565 d39581 d39557 d39392 d39597
            omega
          have d39629 : (x 3 6).toNat = 0 := by
            have r39630 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39631 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
            have e39632 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
            have e39633 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
            have e39634 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
            have e39635 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
            have e39636 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
            have b39637 := hb (x 2 7)
            have b39638 := hb (x 3 6)
            have b39639 := hb (x 4 5)
            have b39640 := hb (x 5 4)
            have b39641 := hb (x 6 11)
            have b39642 := hb (x 7 10)
            have b39643 := hb (x 8 9)
            have b39644 := hb (x 9 8)
            clear * - r39630 e39631 e39632 e39633 e39634 e39635 e39636 b39637 b39638 b39639 b39640 b39641 b39642 b39643 b39644 d39565 d39581 d39557 d39392 d39597 d39613
            omega
          have d39645 : (x 3 2 && x 3 6).toNat = 0 := by
            have r39646 := hand2 (x 3 2) (x 3 6)
            have b39647 := hb (x 3 6)
            have b39648 := hb (x 3 2 && x 3 6)
            clear * - r39646 b39647 b39648 d39629
            omega
          have d39649 : (x 2 7).toNat = 0 := by
            have r39650 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39651 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
            have e39652 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
            have e39653 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
            have e39654 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
            have e39655 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
            have e39656 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
            have b39657 := hb (x 2 7)
            have b39658 := hb (x 3 6)
            have b39659 := hb (x 4 5)
            have b39660 := hb (x 5 4)
            have b39661 := hb (x 6 11)
            have b39662 := hb (x 7 10)
            have b39663 := hb (x 8 9)
            have b39664 := hb (x 9 8)
            clear * - r39650 e39651 e39652 e39653 e39654 e39655 e39656 b39657 b39658 b39659 b39660 b39661 b39662 b39663 b39664 d39565 d39581 d39557 d39392 d39597 d39613 d39629
            omega
          have d39665 : (x 2 1 && x 2 7).toNat = 0 := by
            have r39666 := hand2 (x 2 1) (x 2 7)
            have b39667 := hb (x 2 7)
            have b39668 := hb (x 2 1 && x 2 7)
            clear * - r39666 b39667 b39668 d39649
            omega
          have d39669 : (x 2 3 && x 2 7).toNat = 0 := by
            have r39670 := hand2 (x 2 3) (x 2 7)
            have b39671 := hb (x 2 7)
            have b39672 := hb (x 2 3 && x 2 7)
            clear * - r39670 b39671 b39672 d39649
            omega
          have r39673 : (x 4 1).toNat + (x 3 2).toNat + (x 2 3).toNat + (x 1 4).toNat + (x 0 5).toNat + (x (-1) 6).toNat + (x (-2) 7).toNat + (x (-3) 8).toNat + (x (-4) 9).toNat + (x (-5) 10).toNat + (x (-6) 11).toNat + (x (-7) 12).toNat + (x (-8) 13).toNat + (x (-9) 14).toNat = 3 := by have q := hcount 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r39674 : (x 6 1).toNat + (x 5 2).toNat + (x 4 3).toNat + (x 3 4).toNat + (x 2 5).toNat + (x 1 6).toNat + (x 0 7).toNat + (x (-1) 8).toNat + (x (-2) 9).toNat + (x (-3) 10).toNat + (x (-4) 11).toNat + (x (-5) 12).toNat + (x (-6) 13).toNat + (x (-7) 14).toNat = 3 := by have q := hcount 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r39675 : (x (-5) 8).toNat + (x (-6) 1 && x (-6) 9).toNat + (x (-7) 2 && x (-7) 10).toNat + (x (-8) 3 && x (-8) 11).toNat + (x (-9) 4 && x (-9) 12).toNat + (x (-10) 5 && x (-10) 13).toNat + (x (-11) 6 && x (-11) 14).toNat + (x (-12) 7).toNat = 1 := by have q := hd8 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e39676 : (x (-6) 1 && x (-6) 9).toNat = (x (-6) 9).toNat := handr _ _ (fun h => hp9 (-6) (h))
          have e39677 : (x (-7) 2 && x (-7) 10).toNat = (x (-7) 10).toNat := handr _ _ (fun h => hp10 (-7) (h))
          have e39678 : (x (-8) 3 && x (-8) 11).toNat = (x (-8) 11).toNat := handr _ _ (fun h => hp11 (-8) (h))
          have e39679 : (x (-9) 4 && x (-9) 12).toNat = (x (-9) 4).toNat := handl _ _ (fun h => hp4 (-9) (h))
          have e39680 : (x (-10) 5 && x (-10) 13).toNat = (x (-10) 5).toNat := handl _ _ (fun h => hp5 (-10) (h))
          have e39681 : (x (-11) 6 && x (-11) 14).toNat = (x (-11) 6).toNat := handl _ _ (fun h => hp6 (-11) (h))
          have r39682 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e39683 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
          have e39684 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
          have e39685 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
          have e39686 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
          have e39687 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
          have e39688 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
          have r39689 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e39690 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
          have e39691 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
          have r39692 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e39693 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
          have e39694 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
          have r39695 : 1 ≤ (x 5 4).toNat + (x 4 1 && x 4 5).toNat + (x 3 2 && x 3 6).toNat + (x 2 3 && x 2 7).toNat + (x 1 4 && x 1 8).toNat + (x 0 5 && x 0 9).toNat + (x (-1) 6 && x (-1) 10).toNat + (x (-2) 7 && x (-2) 11).toNat + (x (-3) 8 && x (-3) 12).toNat + (x (-4) 9 && x (-4) 13).toNat + (x (-5) 10 && x (-5) 14).toNat + (x (-6) 11).toNat := by have q := hcov4 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e39696 : (x 4 1 && x 4 5).toNat = (x 4 5).toNat := handr _ _ (fun h => hp13 4 (hp5 4 (h)))
          have e39697 : (x (-5) 10 && x (-5) 14).toNat = (x (-5) 10).toNat := handl _ _ (fun h => hp2 (-5) (hp10 (-5) (h)))
          have r39698 : 1 ≤ (x 3 6).toNat + (x 2 1 && x 2 7).toNat + (x 1 2 && x 1 8).toNat + (x 0 3 && x 0 9).toNat + (x (-1) 4 && x (-1) 10).toNat + (x (-2) 5 && x (-2) 11).toNat + (x (-3) 6 && x (-3) 12).toNat + (x (-4) 7 && x (-4) 13).toNat + (x (-5) 8 && x (-5) 14).toNat + (x (-6) 9).toNat := by have q := hcov6 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r39699 : 1 ≤ (x (-5) 10).toNat + (x (-6) 1 && x (-6) 11).toNat + (x (-7) 2 && x (-7) 12).toNat + (x (-8) 3 && x (-8) 13).toNat + (x (-9) 4 && x (-9) 14).toNat + (x (-10) 5).toNat := by have q := hcov10 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r39700 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r39701 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r39702 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
          have r39703 : (x (-5) 10).toNat ≤ (x (-5) 2).toNat := himp _ _ (hp10 (-5))
          have r39704 := hand1 (x (-3) 8) (x (-3) 12)
          have r39705 := hand1 (x (-4) 9) (x (-4) 13)
          have r39706 := hand1 (x (-5) 8) (x (-5) 14)
          have r39707 := hand2 (x (-6) 1) (x (-6) 11)
          have r39708 := hand2 (x (-7) 2) (x (-7) 12)
          have r39709 := hand2 (x (-8) 3) (x (-8) 13)
          have r39710 := hand1 (x (-9) 4) (x (-9) 14)
          have r39711 := hand2 (x (-3) 2) (x (-3) 12)
          have r39712 := hand2 (x (-4) 3) (x (-4) 13)
          have r39713 := hand1 (x (-5) 4) (x (-5) 14)
          have r39714 := hand1 (x 4 1) (x 4 12)
          have r39715 := hand1 (x 3 2) (x 3 13)
          have r39716 := hand1 (x 2 3) (x 2 14)
          have b39730 := hb (x (-7) 14)
          linarith only [r39673, r39674, r39675, e39676, e39677, e39678, e39679, e39680, e39681, r39682, e39683, e39684, e39685, e39686, e39687, e39688, r39689, e39690, e39691, r39692, e39693, e39694, r39695, e39696, e39697, r39698, r39699, r39700, r39701, r39702, r39703, r39704, r39705, r39706, r39707, r39708, r39709, r39710, r39711, r39712, r39713, r39714, r39715, r39716, b39730, g3, g8, f39179, g11, g15, g16, g20, g22, g23, g24, d39629, d39545, d39613, d39500, d39597, d39541, d39328, d39645, d39669, g29, d39168, g30, g31, d39665, g53, d39156, g54, g55, g56, g57, g76]
        · have f39795 : (x (-1) 8).toNat = 1 := by rw [h39178]; rfl
          have d39796 : (x (-2) 9).toNat = 0 := by
            have r39797 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39798 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e39799 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e39800 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e39801 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e39802 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e39803 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have b39804 := hb (x (-8) 7)
            have b39805 := hb (x (-7) 6)
            have b39806 := hb (x (-6) 5)
            have b39807 := hb (x (-5) 4)
            have b39808 := hb (x (-4) 11)
            have b39809 := hb (x (-3) 10)
            have b39810 := hb (x (-2) 9)
            have b39811 := hb (x (-1) 8)
            clear * - r39797 e39798 e39799 e39800 e39801 e39802 e39803 b39804 b39805 b39806 b39807 b39808 b39809 b39810 b39811 f39795
            omega
          have d39812 : (x (-3) 10).toNat = 0 := by
            have r39813 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39814 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e39815 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e39816 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e39817 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e39818 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e39819 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have b39820 := hb (x (-8) 7)
            have b39821 := hb (x (-7) 6)
            have b39822 := hb (x (-6) 5)
            have b39823 := hb (x (-5) 4)
            have b39824 := hb (x (-4) 11)
            have b39825 := hb (x (-3) 10)
            have b39826 := hb (x (-2) 9)
            have b39827 := hb (x (-1) 8)
            clear * - r39813 e39814 e39815 e39816 e39817 e39818 e39819 b39820 b39821 b39822 b39823 b39824 b39825 b39826 b39827 f39795 d39796
            omega
          have d39828 : (x (-3) 1 && x (-3) 10).toNat = 0 := by
            have r39829 := hand2 (x (-3) 1) (x (-3) 10)
            have b39830 := hb (x (-3) 10)
            have b39831 := hb (x (-3) 1 && x (-3) 10)
            clear * - r39829 b39830 b39831 d39812
            omega
          have d39832 : (x (-4) 11).toNat = 0 := by
            have r39833 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39834 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e39835 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e39836 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e39837 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e39838 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e39839 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have b39840 := hb (x (-8) 7)
            have b39841 := hb (x (-7) 6)
            have b39842 := hb (x (-6) 5)
            have b39843 := hb (x (-5) 4)
            have b39844 := hb (x (-4) 11)
            have b39845 := hb (x (-3) 10)
            have b39846 := hb (x (-2) 9)
            have b39847 := hb (x (-1) 8)
            clear * - r39833 e39834 e39835 e39836 e39837 e39838 e39839 b39840 b39841 b39842 b39843 b39844 b39845 b39846 b39847 f39795 d39796 d39812
            omega
          have d39848 : (x (-4) 2 && x (-4) 11).toNat = 0 := by
            have r39849 := hand2 (x (-4) 2) (x (-4) 11)
            have b39850 := hb (x (-4) 11)
            have b39851 := hb (x (-4) 2 && x (-4) 11)
            clear * - r39849 b39850 b39851 d39832
            omega
          have d39852 : (x (-5) 4).toNat = 0 := by
            have r39853 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39854 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e39855 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e39856 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e39857 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e39858 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e39859 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have b39860 := hb (x (-8) 7)
            have b39861 := hb (x (-7) 6)
            have b39862 := hb (x (-6) 5)
            have b39863 := hb (x (-5) 4)
            have b39864 := hb (x (-4) 11)
            have b39865 := hb (x (-3) 10)
            have b39866 := hb (x (-2) 9)
            have b39867 := hb (x (-1) 8)
            clear * - r39853 e39854 e39855 e39856 e39857 e39858 e39859 b39860 b39861 b39862 b39863 b39864 b39865 b39866 b39867 f39795 d39796 d39812 d39832
            omega
          have d39868 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
            have r39869 := hand1 (x (-5) 4) (x (-5) 14)
            have b39870 := hb (x (-5) 4)
            have b39871 := hb (x (-5) 4 && x (-5) 14)
            clear * - r39869 b39870 b39871 d39852
            omega
          have d39872 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
            have r39873 := hand1 (x (-5) 4) (x (-5) 13)
            have b39874 := hb (x (-5) 4)
            have b39875 := hb (x (-5) 4 && x (-5) 13)
            clear * - r39873 b39874 b39875 d39852
            omega
          have d39876 : (x (-5) 4 && x (-5) 11).toNat = 0 := by
            have r39877 := hand1 (x (-5) 4) (x (-5) 11)
            have b39878 := hb (x (-5) 4)
            have b39879 := hb (x (-5) 4 && x (-5) 11)
            clear * - r39877 b39878 b39879 d39852
            omega
          have d39880 : (x (-5) 4 && x (-5) 9).toNat = 0 := by
            have r39881 := hand1 (x (-5) 4) (x (-5) 9)
            have b39882 := hb (x (-5) 4)
            have b39883 := hb (x (-5) 4 && x (-5) 9)
            clear * - r39881 b39882 b39883 d39852
            omega
          have d39884 : (x (-6) 5).toNat = 0 := by
            have r39885 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39886 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e39887 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e39888 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e39889 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e39890 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e39891 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have b39892 := hb (x (-8) 7)
            have b39893 := hb (x (-7) 6)
            have b39894 := hb (x (-6) 5)
            have b39895 := hb (x (-5) 4)
            have b39896 := hb (x (-4) 11)
            have b39897 := hb (x (-3) 10)
            have b39898 := hb (x (-2) 9)
            have b39899 := hb (x (-1) 8)
            clear * - r39885 e39886 e39887 e39888 e39889 e39890 e39891 b39892 b39893 b39894 b39895 b39896 b39897 b39898 b39899 f39795 d39796 d39812 d39832 d39852
            omega
          have d39900 : (x (-6) 5 && x (-6) 14).toNat = 0 := by
            have r39901 := hand1 (x (-6) 5) (x (-6) 14)
            have b39902 := hb (x (-6) 5)
            have b39903 := hb (x (-6) 5 && x (-6) 14)
            clear * - r39901 b39902 b39903 d39884
            omega
          have d39904 : (x (-6) 5 && x (-6) 12).toNat = 0 := by
            have r39905 := hand1 (x (-6) 5) (x (-6) 12)
            have b39906 := hb (x (-6) 5)
            have b39907 := hb (x (-6) 5 && x (-6) 12)
            clear * - r39905 b39906 b39907 d39884
            omega
          have d39908 : (x (-6) 5 && x (-6) 10).toNat = 0 := by
            have r39909 := hand1 (x (-6) 5) (x (-6) 10)
            have b39910 := hb (x (-6) 5)
            have b39911 := hb (x (-6) 5 && x (-6) 10)
            clear * - r39909 b39910 b39911 d39884
            omega
          have d39912 : (x (-7) 6).toNat = 0 := by
            have r39913 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39914 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e39915 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e39916 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e39917 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e39918 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e39919 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have b39920 := hb (x (-8) 7)
            have b39921 := hb (x (-7) 6)
            have b39922 := hb (x (-6) 5)
            have b39923 := hb (x (-5) 4)
            have b39924 := hb (x (-4) 11)
            have b39925 := hb (x (-3) 10)
            have b39926 := hb (x (-2) 9)
            have b39927 := hb (x (-1) 8)
            clear * - r39913 e39914 e39915 e39916 e39917 e39918 e39919 b39920 b39921 b39922 b39923 b39924 b39925 b39926 b39927 f39795 d39796 d39812 d39832 d39852 d39884
            omega
          have d39928 : (x (-7) 6 && x (-7) 13).toNat = 0 := by
            have r39929 := hand1 (x (-7) 6) (x (-7) 13)
            have b39930 := hb (x (-7) 6)
            have b39931 := hb (x (-7) 6 && x (-7) 13)
            clear * - r39929 b39930 b39931 d39912
            omega
          have d39932 : (x (-7) 6 && x (-7) 11).toNat = 0 := by
            have r39933 := hand1 (x (-7) 6) (x (-7) 11)
            have b39934 := hb (x (-7) 6)
            have b39935 := hb (x (-7) 6 && x (-7) 11)
            clear * - r39933 b39934 b39935 d39912
            omega
          have d39936 : (x (-4) 3 && x (-4) 12).toNat = 1 := by
            have r39937 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b39938 := hb (x (-7) 6)
            have b39939 := hb (x (-1) 9)
            have b39940 := hb (x (-2) 1 && x (-2) 10)
            have b39941 := hb (x (-3) 2 && x (-3) 11)
            have b39942 := hb (x (-4) 3 && x (-4) 12)
            have b39943 := hb (x (-5) 4 && x (-5) 13)
            have b39944 := hb (x (-6) 5 && x (-6) 14)
            clear * - r39937 b39938 b39939 b39940 b39941 b39942 b39943 b39944 g10 g72 g73 d39872 d39900 d39912
            omega
          have d39945 : (x (-4) 12).toNat = 1 := by
            have r39946 := hand2 (x (-4) 3) (x (-4) 12)
            have b39947 := hb (x (-4) 12)
            have b39948 := hb (x (-4) 3 && x (-4) 12)
            clear * - r39946 b39947 b39948 d39936
            omega
          have d39949 : (x (-5) 13).toNat = 0 := by
            have r39950 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39951 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
            have e39952 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
            have b39953 := hb (x (-7) 3)
            have b39954 := hb (x (-6) 2)
            have b39955 := hb (x (-5) 13)
            have b39956 := hb (x (-4) 12)
            clear * - r39950 e39951 e39952 b39953 b39954 b39955 b39956 d39945
            omega
          have d39957 : (x (-6) 2).toNat = 0 := by
            have r39958 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39959 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
            have e39960 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
            have b39961 := hb (x (-7) 3)
            have b39962 := hb (x (-6) 2)
            have b39963 := hb (x (-5) 13)
            have b39964 := hb (x (-4) 12)
            clear * - r39958 e39959 e39960 b39961 b39962 b39963 b39964 d39945 d39949
            omega
          have d39965 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
            have r39966 := hand1 (x (-6) 2) (x (-6) 13)
            have b39967 := hb (x (-6) 2)
            have b39968 := hb (x (-6) 2 && x (-6) 13)
            clear * - r39966 b39967 b39968 d39957
            omega
          have d39969 : (x (-6) 10).toNat = 0 := by
            have r39970 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
            have b39971 := hb (x (-6) 2)
            have b39972 := hb (x (-6) 10)
            clear * - r39970 b39971 b39972 d39957
            omega
          have d39973 : (x (-7) 3).toNat = 0 := by
            have r39974 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39975 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
            have e39976 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
            have b39977 := hb (x (-7) 3)
            have b39978 := hb (x (-6) 2)
            have b39979 := hb (x (-5) 13)
            have b39980 := hb (x (-4) 12)
            clear * - r39974 e39975 e39976 b39977 b39978 b39979 b39980 d39945 d39949 d39957
            omega
          have d39981 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
            have r39982 := hand1 (x (-7) 3) (x (-7) 14)
            have b39983 := hb (x (-7) 3)
            have b39984 := hb (x (-7) 3 && x (-7) 14)
            clear * - r39982 b39983 b39984 d39973
            omega
          have d39985 : (x (-7) 11).toNat = 0 := by
            have r39986 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
            have b39987 := hb (x (-7) 3)
            have b39988 := hb (x (-7) 11)
            clear * - r39986 b39987 b39988 d39973
            omega
          have d39989 : (x (-4) 3).toNat = 1 := by
            have r39990 := hand1 (x (-4) 3) (x (-4) 12)
            have b39991 := hb (x (-4) 3)
            have b39992 := hb (x (-4) 3 && x (-4) 12)
            clear * - r39990 b39991 b39992 d39936
            omega
          have d39993 : (x (-1) 12).toNat = 0 := by
            have r39994 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e39995 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e39996 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b39997 := hb (x (-4) 3)
            have b39998 := hb (x (-3) 2)
            have b39999 := hb (x (-2) 13)
            have b40000 := hb (x (-1) 12)
            clear * - r39994 e39995 e39996 b39997 b39998 b39999 b40000 d39989
            omega
          have d40001 : (x (-2) 13).toNat = 0 := by
            have r40002 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e40003 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e40004 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b40005 := hb (x (-4) 3)
            have b40006 := hb (x (-3) 2)
            have b40007 := hb (x (-2) 13)
            have b40008 := hb (x (-1) 12)
            clear * - r40002 e40003 e40004 b40005 b40006 b40007 b40008 d39993 d39989
            omega
          have d40009 : (x (-3) 2).toNat = 0 := by
            have r40010 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e40011 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e40012 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b40013 := hb (x (-4) 3)
            have b40014 := hb (x (-3) 2)
            have b40015 := hb (x (-2) 13)
            have b40016 := hb (x (-1) 12)
            clear * - r40010 e40011 e40012 b40013 b40014 b40015 b40016 d39993 d40001 d39989
            omega
          have d40017 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
            have r40018 := hand1 (x (-3) 2) (x (-3) 12)
            have b40019 := hb (x (-3) 2)
            have b40020 := hb (x (-3) 2 && x (-3) 12)
            clear * - r40018 b40019 b40020 d40009
            omega
          have d40021 : (x (-4) 3 && x (-4) 13).toNat = 1 := by
            have r40022 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b40023 := hb (x (-6) 5)
            have b40024 := hb (x (-1) 10)
            have b40025 := hb (x (-2) 1 && x (-2) 11)
            have b40026 := hb (x (-3) 2 && x (-3) 12)
            have b40027 := hb (x (-4) 3 && x (-4) 13)
            have b40028 := hb (x (-5) 4 && x (-5) 14)
            clear * - r40022 b40023 b40024 b40025 b40026 b40027 b40028 g11 g76 d40017 d39868 d39884
            omega
          have d40029 : (x (-4) 13).toNat = 1 := by
            have r40030 := hand2 (x (-4) 3) (x (-4) 13)
            have b40031 := hb (x (-4) 13)
            have b40032 := hb (x (-4) 3 && x (-4) 13)
            clear * - r40030 b40031 b40032 d40021
            omega
          have d40033 : (x (-4) 1).toNat = 1 := by
            have r40034 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
            have b40035 := hb (x (-4) 1)
            have b40036 := hb (x (-4) 13)
            clear * - r40034 b40035 b40036 d40029
            omega
          have d40037 : (x (-3) 14).toNat = 0 := by
            have r40038 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b40039 := hb (x (-4) 1)
            have b40040 := hb (x (-3) 14)
            clear * - r40038 b40039 b40040 d40033
            omega
          have d40041 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
            have r40042 := hand2 (x (-3) 1) (x (-3) 14)
            have b40043 := hb (x (-3) 14)
            have b40044 := hb (x (-3) 1 && x (-3) 14)
            clear * - r40042 b40043 b40044 d40037
            omega
          have d40045 : (x (-4) 2).toNat = 1 := by
            have r40046 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b40047 := hb (x (-4) 2)
            have b40048 := hb (x (-2) 13)
            have b40049 := hb (x (-3) 1 && x (-3) 14)
            clear * - r40046 b40047 b40048 b40049 d40001 d40041
            omega
          have d40050 : (x (-4) 14).toNat = 1 := by
            have r40051 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
            have b40052 := hb (x (-4) 2)
            have b40053 := hb (x (-4) 14)
            clear * - r40051 b40052 b40053 d40045
            omega
          have d40054 : (x (-5) 1).toNat = 0 := by
            have r40055 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b40056 := hb (x (-5) 1)
            have b40057 := hb (x (-4) 14)
            clear * - r40055 b40056 b40057 d40050
            omega
          have d40058 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
            have r40059 := hand1 (x (-5) 1) (x (-5) 12)
            have b40060 := hb (x (-5) 1)
            have b40061 := hb (x (-5) 1 && x (-5) 12)
            clear * - r40059 b40060 b40061 d40054
            omega
          have d40062 : (x (-8) 4).toNat = 1 := by
            have r40063 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b40064 := hb (x (-8) 4)
            have b40065 := hb (x (-4) 11)
            have b40066 := hb (x (-5) 1 && x (-5) 12)
            have b40067 := hb (x (-6) 2 && x (-6) 13)
            have b40068 := hb (x (-7) 3 && x (-7) 14)
            clear * - r40063 b40064 b40065 b40066 b40067 b40068 d39832 d40058 d39965 d39981
            omega
          have d40069 : (x (-8) 12).toNat = 1 := by
            have r40070 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
            have b40071 := hb (x (-8) 4)
            have b40072 := hb (x (-8) 12)
            clear * - r40070 b40071 b40072 d40062
            omega
          have d40073 : (x (-9) 13).toNat = 0 := by
            have r40074 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e40075 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
            have e40076 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
            have b40077 := hb (x (-11) 3)
            have b40078 := hb (x (-10) 2)
            have b40079 := hb (x (-9) 13)
            have b40080 := hb (x (-8) 12)
            clear * - r40074 e40075 e40076 b40077 b40078 b40079 b40080 d40069
            omega
          have d40081 : (x (-9) 8 && x (-9) 13).toNat = 0 := by
            have r40082 := hand2 (x (-9) 8) (x (-9) 13)
            have b40083 := hb (x (-9) 13)
            have b40084 := hb (x (-9) 8 && x (-9) 13)
            clear * - r40082 b40083 b40084 d40073
            omega
          have d40085 : (x (-9) 5).toNat = 0 := by
            have r40086 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
            have b40087 := hb (x (-9) 5)
            have b40088 := hb (x (-9) 13)
            clear * - r40086 b40087 b40088 d40073
            omega
          have d40089 : (x (-5) 9).toNat = 0 := by
            have r40090 : (x (-5) 9).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp9 (-5))
            have b40091 := hb (x (-5) 1)
            have b40092 := hb (x (-5) 9)
            clear * - r40090 b40091 b40092 d40054
            omega
          have d40093 : (x (-2) 12).toNat = 0 := by
            have r40094 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e40095 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
            have e40096 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
            have b40097 := hb (x (-5) 3)
            have b40098 := hb (x (-4) 2)
            have b40099 := hb (x (-3) 13)
            have b40100 := hb (x (-2) 12)
            clear * - r40094 e40095 e40096 b40097 b40098 b40099 b40100 d40045
            omega
          have d40101 : (x (-3) 13).toNat = 0 := by
            have r40102 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e40103 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
            have e40104 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
            have b40105 := hb (x (-5) 3)
            have b40106 := hb (x (-4) 2)
            have b40107 := hb (x (-3) 13)
            have b40108 := hb (x (-2) 12)
            clear * - r40102 e40103 e40104 b40105 b40106 b40107 b40108 d40093 d40045
            omega
          have d40109 : (x (-5) 3).toNat = 0 := by
            have r40110 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e40111 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
            have e40112 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
            have b40113 := hb (x (-5) 3)
            have b40114 := hb (x (-4) 2)
            have b40115 := hb (x (-3) 13)
            have b40116 := hb (x (-2) 12)
            clear * - r40110 e40111 e40112 b40113 b40114 b40115 b40116 d40093 d40101 d40045
            omega
          have d40117 : (x (-5) 3 && x (-5) 12).toNat = 0 := by
            have r40118 := hand1 (x (-5) 3) (x (-5) 12)
            have b40119 := hb (x (-5) 3)
            have b40120 := hb (x (-5) 3 && x (-5) 12)
            clear * - r40118 b40119 b40120 d40109
            omega
          have d40121 : (x (-5) 11).toNat = 0 := by
            have r40122 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
            have b40123 := hb (x (-5) 3)
            have b40124 := hb (x (-5) 11)
            clear * - r40122 b40123 b40124 d40109
            omega
          have d40125 : (x (-3) 2 && x (-3) 9).toNat = 0 := by
            have r40126 := hand1 (x (-3) 2) (x (-3) 9)
            have b40127 := hb (x (-3) 2)
            have b40128 := hb (x (-3) 2 && x (-3) 9)
            clear * - r40126 b40127 b40128 d40009
            omega
          have d40129 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
            have r40130 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b40131 := hb (x (-3) 2)
            have b40132 := hb (x (-1) 13)
            have b40133 := hb (x (-2) 1 && x (-2) 14)
            clear * - r40130 b40131 b40132 b40133 g12 d40009
            omega
          have d40134 : (x (-2) 14).toNat = 1 := by
            have r40135 := hand2 (x (-2) 1) (x (-2) 14)
            have b40136 := hb (x (-2) 14)
            have b40137 := hb (x (-2) 1 && x (-2) 14)
            clear * - r40135 b40136 b40137 d40129
            omega
          have d40138 : (x (-3) 1).toNat = 0 := by
            have r40139 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b40140 := hb (x (-3) 1)
            have b40141 := hb (x (-2) 14)
            clear * - r40139 b40140 b40141 d40134
            omega
          have d40142 : (x (-3) 9).toNat = 0 := by
            have r40143 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
            have b40144 := hb (x (-3) 1)
            have b40145 := hb (x (-3) 9)
            clear * - r40143 b40144 b40145 d40138
            omega
          have d40146 : (x (-2) 1).toNat = 1 := by
            have r40147 := hand1 (x (-2) 1) (x (-2) 14)
            have b40148 := hb (x (-2) 1)
            have b40149 := hb (x (-2) 1 && x (-2) 14)
            clear * - r40147 b40148 b40149 d40129
            omega
          have d40150 : (x (-8) 7).toNat = 0 := by
            have r40151 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e40152 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e40153 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e40154 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e40155 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e40156 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e40157 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have b40158 := hb (x (-8) 7)
            have b40159 := hb (x (-7) 6)
            have b40160 := hb (x (-6) 5)
            have b40161 := hb (x (-5) 4)
            have b40162 := hb (x (-4) 11)
            have b40163 := hb (x (-3) 10)
            have b40164 := hb (x (-2) 9)
            have b40165 := hb (x (-1) 8)
            clear * - r40151 e40152 e40153 e40154 e40155 e40156 e40157 b40158 b40159 b40160 b40161 b40162 b40163 b40164 b40165 f39795 d39796 d39812 d39832 d39852 d39884 d39912
            omega
          have d40166 : (x (-8) 7 && x (-8) 14).toNat = 0 := by
            have r40167 := hand1 (x (-8) 7) (x (-8) 14)
            have b40168 := hb (x (-8) 7)
            have b40169 := hb (x (-8) 7 && x (-8) 14)
            clear * - r40167 b40168 b40169 d40150
            omega
          have d40170 : (x (-8) 7 && x (-8) 12).toNat = 0 := by
            have r40171 := hand1 (x (-8) 7) (x (-8) 12)
            have b40172 := hb (x (-8) 7)
            have b40173 := hb (x (-8) 7 && x (-8) 12)
            clear * - r40171 b40172 b40173 d40150
            omega
          have d40174 : (x (-4) 8).toNat = 0 := by
            have r40175 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e40176 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
            have e40177 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
            have e40178 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
            have e40179 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
            have e40180 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
            have e40181 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
            have b40182 := hb (x (-11) 7)
            have b40183 := hb (x (-10) 6)
            have b40184 := hb (x (-9) 5)
            have b40185 := hb (x (-8) 4)
            have b40186 := hb (x (-7) 11)
            have b40187 := hb (x (-6) 10)
            have b40188 := hb (x (-5) 9)
            have b40189 := hb (x (-4) 8)
            clear * - r40175 e40176 e40177 e40178 e40179 e40180 e40181 b40182 b40183 b40184 b40185 b40186 b40187 b40188 b40189 d40089 d39969 d39985 d40062 d40085
            omega
          have d40190 : (x (-4) 3 && x (-4) 8).toNat = 0 := by
            have r40191 := hand2 (x (-4) 3) (x (-4) 8)
            have b40192 := hb (x (-4) 8)
            have b40193 := hb (x (-4) 3 && x (-4) 8)
            clear * - r40191 b40192 b40193 d40174
            omega
          have r40194 : (x (-2) 1).toNat + (x (-3) 2).toNat + (x (-4) 3).toNat + (x (-5) 4).toNat + (x (-6) 5).toNat + (x (-7) 6).toNat + (x (-8) 7).toNat + (x (-9) 8).toNat + (x (-10) 9).toNat + (x (-11) 10).toNat + (x (-12) 11).toNat + (x (-13) 12).toNat + (x (-14) 13).toNat + (x (-15) 14).toNat = 3 := by have q := hcount (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r40195 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e40196 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
          have e40197 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
          have e40198 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
          have e40199 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
          have e40200 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
          have e40201 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
          have r40202 : 1 ≤ (x (-1) 5).toNat + (x (-2) 1 && x (-2) 6).toNat + (x (-3) 2 && x (-3) 7).toNat + (x (-4) 3 && x (-4) 8).toNat + (x (-5) 4 && x (-5) 9).toNat + (x (-6) 5 && x (-6) 10).toNat + (x (-7) 6 && x (-7) 11).toNat + (x (-8) 7 && x (-8) 12).toNat + (x (-9) 8 && x (-9) 13).toNat + (x (-10) 9 && x (-10) 14).toNat + (x (-11) 10).toNat := by have q := hcov5 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r40203 : 1 ≤ (x (-1) 7).toNat + (x (-2) 1 && x (-2) 8).toNat + (x (-3) 2 && x (-3) 9).toNat + (x (-4) 3 && x (-4) 10).toNat + (x (-5) 4 && x (-5) 11).toNat + (x (-6) 5 && x (-6) 12).toNat + (x (-7) 6 && x (-7) 13).toNat + (x (-8) 7 && x (-8) 14).toNat + (x (-9) 8).toNat := by have q := hcov7 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r40204 : 1 ≤ (x (-2) 9).toNat + (x (-3) 1 && x (-3) 10).toNat + (x (-4) 2 && x (-4) 11).toNat + (x (-5) 3 && x (-5) 12).toNat + (x (-6) 4 && x (-6) 13).toNat + (x (-7) 5 && x (-7) 14).toNat + (x (-8) 6).toNat := by have q := hcov9 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r40205 := hand1 (x (-10) 9) (x (-10) 14)
          have r40206 := hand2 (x (-2) 1) (x (-2) 8)
          have r40207 := hand2 (x (-4) 3) (x (-4) 10)
          have r40208 := hand1 (x (-6) 4) (x (-6) 13)
          have r40209 := hand1 (x (-7) 5) (x (-7) 14)
          linarith only [r40194, r40195, e40196, e40197, e40198, e40199, e40200, e40201, r40202, r40203, r40204, r40205, r40206, r40207, r40208, r40209, d40150, d39912, d39884, d39852, d40121, d39989, d40009, d40142, d40146, d39796, g7, g9, g41, g42, d40190, d39880, d39908, d39932, d40170, d40081, d40125, d39876, d39904, d39928, d40166, d39828, d39848, d40117]
      · have f40256 : (x 1 7).toNat = 1 := by rw [h39176]; rfl
        have d40257 : (x 8 8).toNat = 0 := by
          have r40258 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e40259 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e40260 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e40261 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e40262 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e40263 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e40264 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have b40265 := hb (x 1 7)
          have b40266 := hb (x 2 6)
          have b40267 := hb (x 3 5)
          have b40268 := hb (x 4 4)
          have b40269 := hb (x 5 11)
          have b40270 := hb (x 6 10)
          have b40271 := hb (x 7 9)
          have b40272 := hb (x 8 8)
          clear * - r40258 e40259 e40260 e40261 e40262 e40263 e40264 b40265 b40266 b40267 b40268 b40269 b40270 b40271 b40272 f40256
          omega
        have d40273 : (x 7 9).toNat = 0 := by
          have r40274 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e40275 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e40276 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e40277 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e40278 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e40279 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e40280 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have b40281 := hb (x 1 7)
          have b40282 := hb (x 2 6)
          have b40283 := hb (x 3 5)
          have b40284 := hb (x 4 4)
          have b40285 := hb (x 5 11)
          have b40286 := hb (x 6 10)
          have b40287 := hb (x 7 9)
          have b40288 := hb (x 8 8)
          clear * - r40274 e40275 e40276 e40277 e40278 e40279 e40280 b40281 b40282 b40283 b40284 b40285 b40286 b40287 b40288 d40257 f40256
          omega
        have d40289 : (x 6 10).toNat = 0 := by
          have r40290 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e40291 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e40292 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e40293 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e40294 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e40295 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e40296 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have b40297 := hb (x 1 7)
          have b40298 := hb (x 2 6)
          have b40299 := hb (x 3 5)
          have b40300 := hb (x 4 4)
          have b40301 := hb (x 5 11)
          have b40302 := hb (x 6 10)
          have b40303 := hb (x 7 9)
          have b40304 := hb (x 8 8)
          clear * - r40290 e40291 e40292 e40293 e40294 e40295 e40296 b40297 b40298 b40299 b40300 b40301 b40302 b40303 b40304 d40257 d40273 f40256
          omega
        have d40305 : (x 6 1 && x 6 10).toNat = 0 := by
          have r40306 := hand2 (x 6 1) (x 6 10)
          have b40307 := hb (x 6 10)
          have b40308 := hb (x 6 1 && x 6 10)
          clear * - r40306 b40307 b40308 d40289
          omega
        have d40309 : (x 5 11).toNat = 0 := by
          have r40310 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e40311 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e40312 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e40313 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e40314 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e40315 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e40316 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have b40317 := hb (x 1 7)
          have b40318 := hb (x 2 6)
          have b40319 := hb (x 3 5)
          have b40320 := hb (x 4 4)
          have b40321 := hb (x 5 11)
          have b40322 := hb (x 6 10)
          have b40323 := hb (x 7 9)
          have b40324 := hb (x 8 8)
          clear * - r40310 e40311 e40312 e40313 e40314 e40315 e40316 b40317 b40318 b40319 b40320 b40321 b40322 b40323 b40324 d40257 d40273 d40289 f40256
          omega
        have d40325 : (x 5 1 && x 5 11).toNat = 0 := by
          have r40326 := hand2 (x 5 1) (x 5 11)
          have b40327 := hb (x 5 11)
          have b40328 := hb (x 5 1 && x 5 11)
          clear * - r40326 b40327 b40328 d40309
          omega
        have d40329 : (x 5 2 && x 5 11).toNat = 0 := by
          have r40330 := hand2 (x 5 2) (x 5 11)
          have b40331 := hb (x 5 11)
          have b40332 := hb (x 5 2 && x 5 11)
          clear * - r40330 b40331 b40332 d40309
          omega
        have d40333 : (x 4 3 && x 4 12).toNat = 1 := by
          have r40334 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b40335 := hb (x 1 6)
          have b40336 := hb (x 7 9)
          have b40337 := hb (x 6 1 && x 6 10)
          have b40338 := hb (x 5 2 && x 5 11)
          have b40339 := hb (x 4 3 && x 4 12)
          have b40340 := hb (x 3 4 && x 3 13)
          have b40341 := hb (x 2 5 && x 2 14)
          clear * - r40334 b40335 b40336 b40337 b40338 b40339 b40340 b40341 d40273 d40305 d40329 g74 g75 g22
          omega
        have d40342 : (x 4 12).toNat = 1 := by
          have r40343 := hand2 (x 4 3) (x 4 12)
          have b40344 := hb (x 4 12)
          have b40345 := hb (x 4 3 && x 4 12)
          clear * - r40343 b40344 b40345 d40333
          omega
        have d40346 : (x 3 13).toNat = 0 := by
          have r40347 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e40348 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e40349 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b40350 := hb (x 1 3)
          have b40351 := hb (x 2 2)
          have b40352 := hb (x 3 13)
          have b40353 := hb (x 4 12)
          clear * - r40347 e40348 e40349 b40350 b40351 b40352 b40353 d40342 f39175
          omega
        have d40354 : (x 3 3 && x 3 13).toNat = 0 := by
          have r40355 := hand2 (x 3 3) (x 3 13)
          have b40356 := hb (x 3 13)
          have b40357 := hb (x 3 3 && x 3 13)
          clear * - r40355 b40356 b40357 d40346
          omega
        have d40358 : (x 4 2 && x 4 12).toNat = 1 := by
          have r40359 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b40360 := hb (x 1 5)
          have b40361 := hb (x 6 10)
          have b40362 := hb (x 5 1 && x 5 11)
          have b40363 := hb (x 4 2 && x 4 12)
          have b40364 := hb (x 3 3 && x 3 13)
          have b40365 := hb (x 2 4 && x 2 14)
          clear * - r40359 b40360 b40361 b40362 b40363 b40364 b40365 d40289 d40325 d40354 g77 g21
          omega
        have d40366 : (x 4 2).toNat = 1 := by
          have r40367 := hand1 (x 4 2) (x 4 12)
          have b40368 := hb (x 4 2)
          have b40369 := hb (x 4 2 && x 4 12)
          clear * - r40367 b40368 b40369 d40358
          omega
        have d40370 : (x 6 12).toNat = 0 := by
          have r40371 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e40372 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e40373 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b40374 := hb (x 3 3)
          have b40375 := hb (x 4 2)
          have b40376 := hb (x 5 13)
          have b40377 := hb (x 6 12)
          clear * - r40371 e40372 e40373 b40374 b40375 b40376 b40377 d40366
          omega
        have d40378 : (x 6 2 && x 6 12).toNat = 0 := by
          have r40379 := hand2 (x 6 2) (x 6 12)
          have b40380 := hb (x 6 12)
          have b40381 := hb (x 6 2 && x 6 12)
          clear * - r40379 b40380 b40381 d40370
          omega
        have d40382 : (x 6 4).toNat = 0 := by
          have r40383 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
          have b40384 := hb (x 6 4)
          have b40385 := hb (x 6 12)
          clear * - r40383 b40384 b40385 d40370
          omega
        have d40386 : (x 6 4 && x 6 13).toNat = 0 := by
          have r40387 := hand1 (x 6 4) (x 6 13)
          have b40388 := hb (x 6 4)
          have b40389 := hb (x 6 4 && x 6 13)
          clear * - r40387 b40388 b40389 d40382
          omega
        have d40390 : (x 5 13).toNat = 0 := by
          have r40391 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e40392 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e40393 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b40394 := hb (x 3 3)
          have b40395 := hb (x 4 2)
          have b40396 := hb (x 5 13)
          have b40397 := hb (x 6 12)
          clear * - r40391 e40392 e40393 b40394 b40395 b40396 b40397 d40370 d40366
          omega
        have d40398 : (x 5 3 && x 5 13).toNat = 0 := by
          have r40399 := hand2 (x 5 3) (x 5 13)
          have b40400 := hb (x 5 13)
          have b40401 := hb (x 5 3 && x 5 13)
          clear * - r40399 b40400 b40401 d40390
          omega
        have d40402 : (x 5 5).toNat = 0 := by
          have r40403 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
          have b40404 := hb (x 5 5)
          have b40405 := hb (x 5 13)
          clear * - r40403 b40404 b40405 d40390
          omega
        have d40406 : (x 5 5 && x 5 14).toNat = 0 := by
          have r40407 := hand1 (x 5 5) (x 5 14)
          have b40408 := hb (x 5 5)
          have b40409 := hb (x 5 5 && x 5 14)
          clear * - r40407 b40408 b40409 d40402
          omega
        have d40410 : (x 3 5).toNat = 0 := by
          have r40411 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
          have b40412 := hb (x 3 5)
          have b40413 := hb (x 3 13)
          clear * - r40411 b40412 b40413 d40346
          omega
        have d40414 : (x 2 1 && x 2 14).toNat = 1 := by
          have r40415 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b40416 := hb (x 1 2)
          have b40417 := hb (x 3 13)
          have b40418 := hb (x 2 1 && x 2 14)
          clear * - r40415 b40416 b40417 b40418 d40346 g19
          omega
        have d40419 : (x 2 1).toNat = 1 := by
          have r40420 := hand1 (x 2 1) (x 2 14)
          have b40421 := hb (x 2 1)
          have b40422 := hb (x 2 1 && x 2 14)
          clear * - r40420 b40421 b40422 d40414
          omega
        have d40423 : (x 3 14).toNat = 0 := by
          have r40424 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b40425 := hb (x 2 1)
          have b40426 := hb (x 3 14)
          clear * - r40424 b40425 b40426 d40419
          omega
        have d40427 : (x 3 2).toNat = 0 := by
          have r40428 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
          have b40429 := hb (x 3 2)
          have b40430 := hb (x 3 14)
          clear * - r40428 b40429 b40430 d40423
          omega
        have d40431 : (x 4 1 && x 4 14).toNat = 1 := by
          have r40432 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b40433 := hb (x 3 2)
          have b40434 := hb (x 5 13)
          have b40435 := hb (x 4 1 && x 4 14)
          clear * - r40432 b40433 b40434 b40435 d40390 d40427
          omega
        have d40436 : (x 4 1).toNat = 1 := by
          have r40437 := hand1 (x 4 1) (x 4 14)
          have b40438 := hb (x 4 1)
          have b40439 := hb (x 4 1 && x 4 14)
          clear * - r40437 b40438 b40439 d40431
          omega
        have d40440 : (x 5 14).toNat = 0 := by
          have r40441 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b40442 := hb (x 4 1)
          have b40443 := hb (x 5 14)
          clear * - r40441 b40442 b40443 d40436
          omega
        have d40444 : (x 5 3 && x 5 14).toNat = 0 := by
          have r40445 := hand2 (x 5 3) (x 5 14)
          have b40446 := hb (x 5 14)
          have b40447 := hb (x 5 3 && x 5 14)
          clear * - r40445 b40446 b40447 d40440
          omega
        have d40448 : (x 5 6).toNat = 0 := by
          have r40449 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
          have b40450 := hb (x 5 6)
          have b40451 := hb (x 5 14)
          clear * - r40449 b40450 b40451 d40440
          omega
        have d40452 : (x 5 2 && x 5 6).toNat = 0 := by
          have r40453 := hand2 (x 5 2) (x 5 6)
          have b40454 := hb (x 5 6)
          have b40455 := hb (x 5 2 && x 5 6)
          clear * - r40453 b40454 b40455 d40448
          omega
        have d40456 : (x 5 2).toNat = 0 := by
          have r40457 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
          have b40458 := hb (x 5 2)
          have b40459 := hb (x 5 14)
          clear * - r40457 b40458 b40459 d40440
          omega
        have d40460 : (x 4 3).toNat = 1 := by
          have r40461 := hand1 (x 4 3) (x 4 12)
          have b40462 := hb (x 4 3)
          have b40463 := hb (x 4 3 && x 4 12)
          clear * - r40461 b40462 b40463 d40333
          omega
        have d40464 : (x 7 12).toNat = 0 := by
          have r40465 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e40466 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
          have e40467 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
          have b40468 := hb (x 4 3)
          have b40469 := hb (x 5 2)
          have b40470 := hb (x 6 13)
          have b40471 := hb (x 7 12)
          clear * - r40465 e40466 e40467 b40468 b40469 b40470 b40471 d40456 d40460
          omega
        have d40472 : (x 7 1 && x 7 12).toNat = 0 := by
          have r40473 := hand2 (x 7 1) (x 7 12)
          have b40474 := hb (x 7 12)
          have b40475 := hb (x 7 1 && x 7 12)
          clear * - r40473 b40474 b40475 d40464
          omega
        have d40476 : (x 7 3 && x 7 12).toNat = 0 := by
          have r40477 := hand2 (x 7 3) (x 7 12)
          have b40478 := hb (x 7 12)
          have b40479 := hb (x 7 3 && x 7 12)
          clear * - r40477 b40478 b40479 d40464
          omega
        have d40480 : (x 7 4).toNat = 0 := by
          have r40481 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
          have b40482 := hb (x 7 4)
          have b40483 := hb (x 7 12)
          clear * - r40481 b40482 b40483 d40464
          omega
        have d40484 : (x 6 13).toNat = 0 := by
          have r40485 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e40486 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
          have e40487 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
          have b40488 := hb (x 4 3)
          have b40489 := hb (x 5 2)
          have b40490 := hb (x 6 13)
          have b40491 := hb (x 7 12)
          clear * - r40485 e40486 e40487 b40488 b40489 b40490 b40491 d40464 d40456 d40460
          omega
        have d40492 : (x 6 2 && x 6 13).toNat = 0 := by
          have r40493 := hand2 (x 6 2) (x 6 13)
          have b40494 := hb (x 6 13)
          have b40495 := hb (x 6 2 && x 6 13)
          clear * - r40493 b40494 b40495 d40484
          omega
        have d40496 : (x 6 5).toNat = 0 := by
          have r40497 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
          have b40498 := hb (x 6 5)
          have b40499 := hb (x 6 13)
          clear * - r40497 b40498 b40499 d40484
          omega
        have d40500 : (x 4 4).toNat = 0 := by
          have r40501 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e40502 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e40503 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e40504 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e40505 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e40506 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e40507 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have b40508 := hb (x 1 7)
          have b40509 := hb (x 2 6)
          have b40510 := hb (x 3 5)
          have b40511 := hb (x 4 4)
          have b40512 := hb (x 5 11)
          have b40513 := hb (x 6 10)
          have b40514 := hb (x 7 9)
          have b40515 := hb (x 8 8)
          clear * - r40501 e40502 e40503 e40504 e40505 e40506 e40507 b40508 b40509 b40510 b40511 b40512 b40513 b40514 b40515 d40257 d40273 d40289 d40309 d40410 f40256
          omega
        have d40516 : (x 4 4 && x 4 14).toNat = 0 := by
          have r40517 := hand1 (x 4 4) (x 4 14)
          have b40518 := hb (x 4 4)
          have b40519 := hb (x 4 4 && x 4 14)
          clear * - r40517 b40518 b40519 d40500
          omega
        have d40520 : (x 8 11).toNat = 1 := by
          have r40521 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b40522 := hb (x 4 4)
          have b40523 := hb (x 8 11)
          have b40524 := hb (x 7 1 && x 7 12)
          have b40525 := hb (x 6 2 && x 6 13)
          have b40526 := hb (x 5 3 && x 5 14)
          clear * - r40521 b40522 b40523 b40524 b40525 b40526 d40472 d40492 d40444 d40500
          omega
        have d40527 : (x 8 3).toNat = 1 := by
          have r40528 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
          have b40529 := hb (x 8 3)
          have b40530 := hb (x 8 11)
          clear * - r40528 b40529 b40530 d40520
          omega
        have d40531 : (x 11 12).toNat = 0 := by
          have r40532 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e40533 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e40534 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have b40535 := hb (x 8 3)
          have b40536 := hb (x 9 2)
          have b40537 := hb (x 10 13)
          have b40538 := hb (x 11 12)
          clear * - r40532 e40533 e40534 b40535 b40536 b40537 b40538 d40527
          omega
        have d40539 : (x 10 13).toNat = 0 := by
          have r40540 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e40541 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e40542 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have b40543 := hb (x 8 3)
          have b40544 := hb (x 9 2)
          have b40545 := hb (x 10 13)
          have b40546 := hb (x 11 12)
          clear * - r40540 e40541 e40542 b40543 b40544 b40545 b40546 d40531 d40527
          omega
        have d40547 : (x 9 2).toNat = 0 := by
          have r40548 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e40549 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e40550 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have b40551 := hb (x 8 3)
          have b40552 := hb (x 9 2)
          have b40553 := hb (x 10 13)
          have b40554 := hb (x 11 12)
          clear * - r40548 e40549 e40550 b40551 b40552 b40553 b40554 d40531 d40539 d40527
          omega
        have d40555 : (x 9 10).toNat = 0 := by
          have r40556 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
          have b40557 := hb (x 9 2)
          have b40558 := hb (x 9 10)
          clear * - r40556 b40557 b40558 d40547
          omega
        have d40559 : (x 9 1 && x 9 10).toNat = 0 := by
          have r40560 := hand2 (x 9 1) (x 9 10)
          have b40561 := hb (x 9 10)
          have b40562 := hb (x 9 1 && x 9 10)
          clear * - r40560 b40561 b40562 d40555
          omega
        have d40563 : (x 11 8).toNat = 0 := by
          have r40564 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e40565 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
          have e40566 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
          have e40567 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
          have e40568 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
          have e40569 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
          have e40570 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
          have b40571 := hb (x 4 7)
          have b40572 := hb (x 5 6)
          have b40573 := hb (x 6 5)
          have b40574 := hb (x 7 4)
          have b40575 := hb (x 8 11)
          have b40576 := hb (x 9 10)
          have b40577 := hb (x 10 9)
          have b40578 := hb (x 11 8)
          clear * - r40564 e40565 e40566 e40567 e40568 e40569 e40570 b40571 b40572 b40573 b40574 b40575 b40576 b40577 b40578 d40555 d40520 d40480 d40496 d40448
          omega
        have d40579 : (x 10 9).toNat = 0 := by
          have r40580 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e40581 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
          have e40582 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
          have e40583 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
          have e40584 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
          have e40585 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
          have e40586 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
          have b40587 := hb (x 4 7)
          have b40588 := hb (x 5 6)
          have b40589 := hb (x 6 5)
          have b40590 := hb (x 7 4)
          have b40591 := hb (x 8 11)
          have b40592 := hb (x 9 10)
          have b40593 := hb (x 10 9)
          have b40594 := hb (x 11 8)
          clear * - r40580 e40581 e40582 e40583 e40584 e40585 e40586 b40587 b40588 b40589 b40590 b40591 b40592 b40593 b40594 d40563 d40555 d40520 d40480 d40496 d40448
          omega
        have d40595 : (x 4 7).toNat = 0 := by
          have r40596 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e40597 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
          have e40598 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
          have e40599 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
          have e40600 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
          have e40601 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
          have e40602 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
          have b40603 := hb (x 4 7)
          have b40604 := hb (x 5 6)
          have b40605 := hb (x 6 5)
          have b40606 := hb (x 7 4)
          have b40607 := hb (x 8 11)
          have b40608 := hb (x 9 10)
          have b40609 := hb (x 10 9)
          have b40610 := hb (x 11 8)
          clear * - r40596 e40597 e40598 e40599 e40600 e40601 e40602 b40603 b40604 b40605 b40606 b40607 b40608 b40609 b40610 d40563 d40579 d40555 d40520 d40480 d40496 d40448
          omega
        have d40611 : (x 4 3 && x 4 7).toNat = 0 := by
          have r40612 := hand2 (x 4 3) (x 4 7)
          have b40613 := hb (x 4 7)
          have b40614 := hb (x 4 3 && x 4 7)
          clear * - r40612 b40613 b40614 d40595
          omega
        have r40615 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40616 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e40617 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e40618 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e40619 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e40620 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e40621 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have r40622 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40623 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
        have e40624 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
        have e40625 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
        have e40626 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
        have e40627 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
        have e40628 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
        have r40629 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40630 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
        have e40631 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
        have e40632 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
        have e40633 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
        have e40634 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
        have e40635 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
        have r40636 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40637 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e40638 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have r40639 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r40640 : 1 ≤ (x 7 4).toNat + (x 6 1 && x 6 5).toNat + (x 5 2 && x 5 6).toNat + (x 4 3 && x 4 7).toNat + (x 3 4 && x 3 8).toNat + (x 2 5 && x 2 9).toNat + (x 1 6 && x 1 10).toNat + (x 0 7 && x 0 11).toNat + (x (-1) 8 && x (-1) 12).toNat + (x (-2) 9 && x (-2) 13).toNat + (x (-3) 10 && x (-3) 14).toNat + (x (-4) 11).toNat := by have q := hcov4 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40641 : (x 6 1 && x 6 5).toNat = (x 6 5).toNat := handr _ _ (fun h => hp13 6 (hp5 6 (h)))
        have e40642 : (x (-3) 10 && x (-3) 14).toNat = (x (-3) 10).toNat := handl _ _ (fun h => hp2 (-3) (hp10 (-3) (h)))
        have r40643 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r40644 : 1 ≤ (x 7 7).toNat + (x 6 1 && x 6 8).toNat + (x 5 2 && x 5 9).toNat + (x 4 3 && x 4 10).toNat + (x 3 4 && x 3 11).toNat + (x 2 5 && x 2 12).toNat + (x 1 6 && x 1 13).toNat + (x 0 7 && x 0 14).toNat + (x (-1) 8).toNat := by have q := hcov7 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r40645 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r40646 : 1 ≤ (x 10 9).toNat + (x 9 1 && x 9 10).toNat + (x 8 2 && x 8 11).toNat + (x 7 3 && x 7 12).toNat + (x 6 4 && x 6 13).toNat + (x 5 5 && x 5 14).toNat + (x 4 6).toNat := by have q := hcov9 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r40647 : 1 ≤ (x 8 10).toNat + (x 7 1 && x 7 11).toNat + (x 6 2 && x 6 12).toNat + (x 5 3 && x 5 13).toNat + (x 4 4 && x 4 14).toNat + (x 3 5).toNat := by have q := hcov10 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r40648 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
        have r40649 := hand2 (x (-1) 8) (x (-1) 12)
        have r40650 := hand2 (x (-2) 9) (x (-2) 13)
        have r40651 := hand1 (x 7 1) (x 7 7)
        have r40652 := hand1 (x (-4) 3) (x (-4) 12)
        have r40653 := hand1 (x (-5) 4) (x (-5) 13)
        have r40654 := hand1 (x (-6) 5) (x (-6) 14)
        have r40655 := hand1 (x 8 2) (x 8 11)
        have r40656 := hand2 (x 7 1) (x 7 11)
        linarith only [r40615, e40616, e40617, e40618, e40619, e40620, e40621, r40622, e40623, e40624, e40625, e40626, e40627, e40628, r40629, e40630, e40631, e40632, e40633, e40634, e40635, r40636, e40637, e40638, r40639, r40640, e40641, e40642, r40643, r40644, r40645, r40646, r40647, r40648, r40649, r40650, r40651, r40652, r40653, r40654, r40655, r40656, g10, d40410, d40402, d40382, d40496, d40480, d40579, d40452, d40611, g32, g33, g34, g35, g58, g59, g60, g61, g62, g63, g64, g65, g66, g67, g68, g69, g70, g71, g72, g73, d40559, d40476, d40386, d40406, d40378, d40398, d40516]
    · have f40730 : (x 1 3).toNat = 1 := by rw [h39174]; rfl
      have d40731 : (x 4 12).toNat = 0 := by
        have r40732 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40733 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e40734 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b40735 := hb (x 1 3)
        have b40736 := hb (x 2 2)
        have b40737 := hb (x 3 13)
        have b40738 := hb (x 4 12)
        clear * - r40732 e40733 e40734 b40735 b40736 b40737 b40738 f40730
        omega
      have d40739 : (x 4 1 && x 4 12).toNat = 0 := by
        have r40740 := hand2 (x 4 1) (x 4 12)
        have b40741 := hb (x 4 12)
        have b40742 := hb (x 4 1 && x 4 12)
        clear * - r40740 b40741 b40742 d40731
        omega
      have d40743 : (x 4 4).toNat = 0 := by
        have r40744 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
        have b40745 := hb (x 4 4)
        have b40746 := hb (x 4 12)
        clear * - r40744 b40745 b40746 d40731
        omega
      have d40747 : (x 3 13).toNat = 0 := by
        have r40748 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40749 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e40750 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b40751 := hb (x 1 3)
        have b40752 := hb (x 2 2)
        have b40753 := hb (x 3 13)
        have b40754 := hb (x 4 12)
        clear * - r40748 e40749 e40750 b40751 b40752 b40753 b40754 d40731 f40730
        omega
      have d40755 : (x 3 2 && x 3 13).toNat = 0 := by
        have r40756 := hand2 (x 3 2) (x 3 13)
        have b40757 := hb (x 3 13)
        have b40758 := hb (x 3 2 && x 3 13)
        clear * - r40756 b40757 b40758 d40747
        omega
      have d40759 : (x 2 1 && x 2 14).toNat = 1 := by
        have r40760 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b40761 := hb (x 1 2)
        have b40762 := hb (x 3 13)
        have b40763 := hb (x 2 1 && x 2 14)
        clear * - r40760 b40761 b40762 b40763 d40747 g19
        omega
      have d40764 : (x 2 1).toNat = 1 := by
        have r40765 := hand1 (x 2 1) (x 2 14)
        have b40766 := hb (x 2 1)
        have b40767 := hb (x 2 1 && x 2 14)
        clear * - r40765 b40766 b40767 d40759
        omega
      have d40768 : (x 3 14).toNat = 0 := by
        have r40769 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b40770 := hb (x 2 1)
        have b40771 := hb (x 3 14)
        clear * - r40769 b40770 b40771 d40764
        omega
      have d40772 : (x 3 1 && x 3 14).toNat = 0 := by
        have r40773 := hand2 (x 3 1) (x 3 14)
        have b40774 := hb (x 3 14)
        have b40775 := hb (x 3 1 && x 3 14)
        clear * - r40773 b40774 b40775 d40768
        omega
      have d40776 : (x 3 2).toNat = 0 := by
        have r40777 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
        have b40778 := hb (x 3 2)
        have b40779 := hb (x 3 14)
        clear * - r40777 b40778 b40779 d40768
        omega
      have d40780 : (x 2 2).toNat = 0 := by
        have r40781 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40782 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e40783 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b40784 := hb (x 1 3)
        have b40785 := hb (x 2 2)
        have b40786 := hb (x 3 13)
        have b40787 := hb (x 4 12)
        clear * - r40781 e40782 e40783 b40784 b40785 b40786 b40787 d40731 d40747 f40730
        omega
      have d40788 : (x 4 13).toNat = 1 := by
        have r40789 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b40790 := hb (x 2 2)
        have b40791 := hb (x 4 13)
        have b40792 := hb (x 3 1 && x 3 14)
        clear * - r40789 b40790 b40791 b40792 d40772 d40780
        omega
      have d40793 : (x 4 1).toNat = 1 := by
        have r40794 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
        have b40795 := hb (x 4 1)
        have b40796 := hb (x 4 13)
        clear * - r40794 b40795 b40796 d40788
        omega
      have d40797 : (x 5 14).toNat = 0 := by
        have r40798 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b40799 := hb (x 4 1)
        have b40800 := hb (x 5 14)
        clear * - r40798 b40799 b40800 d40793
        omega
      have d40801 : (x 5 3 && x 5 14).toNat = 0 := by
        have r40802 := hand2 (x 5 3) (x 5 14)
        have b40803 := hb (x 5 14)
        have b40804 := hb (x 5 3 && x 5 14)
        clear * - r40802 b40803 b40804 d40797
        omega
      have d40805 : (x 5 2).toNat = 0 := by
        have r40806 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
        have b40807 := hb (x 5 2)
        have b40808 := hb (x 5 14)
        clear * - r40806 b40807 b40808 d40797
        omega
      have d40809 : (x 5 12).toNat = 0 := by
        have r40810 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40811 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e40812 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b40813 := hb (x 2 3)
        have b40814 := hb (x 3 2)
        have b40815 := hb (x 4 13)
        have b40816 := hb (x 5 12)
        clear * - r40810 e40811 e40812 b40813 b40814 b40815 b40816 d40788 d40776
        omega
      have d40817 : (x 5 4).toNat = 0 := by
        have r40818 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
        have b40819 := hb (x 5 4)
        have b40820 := hb (x 5 12)
        clear * - r40818 b40819 b40820 d40809
        omega
      have d40821 : (x 2 3).toNat = 0 := by
        have r40822 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40823 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e40824 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b40825 := hb (x 2 3)
        have b40826 := hb (x 3 2)
        have b40827 := hb (x 4 13)
        have b40828 := hb (x 5 12)
        clear * - r40822 e40823 e40824 b40825 b40826 b40827 b40828 d40809 d40788 d40776
        omega
      have d40829 : (x 2 3 && x 2 14).toNat = 0 := by
        have r40830 := hand1 (x 2 3) (x 2 14)
        have b40831 := hb (x 2 3)
        have b40832 := hb (x 2 3 && x 2 14)
        clear * - r40830 b40831 b40832 d40821
        omega
      have d40833 : (x 5 11).toNat = 1 := by
        have r40834 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b40835 := hb (x 1 4)
        have b40836 := hb (x 5 11)
        have b40837 := hb (x 4 1 && x 4 12)
        have b40838 := hb (x 3 2 && x 3 13)
        have b40839 := hb (x 2 3 && x 2 14)
        clear * - r40834 b40835 b40836 b40837 b40838 b40839 d40739 d40755 d40829 g20
        omega
      have d40840 : (x 5 3).toNat = 1 := by
        have r40841 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
        have b40842 := hb (x 5 3)
        have b40843 := hb (x 5 11)
        clear * - r40841 b40842 b40843 d40833
        omega
      have d40844 : (x 8 12).toNat = 0 := by
        have r40845 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40846 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e40847 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have b40848 := hb (x 5 3)
        have b40849 := hb (x 6 2)
        have b40850 := hb (x 7 13)
        have b40851 := hb (x 8 12)
        clear * - r40845 e40846 e40847 b40848 b40849 b40850 b40851 d40840
        omega
      have d40852 : (x 8 1 && x 8 12).toNat = 0 := by
        have r40853 := hand2 (x 8 1) (x 8 12)
        have b40854 := hb (x 8 12)
        have b40855 := hb (x 8 1 && x 8 12)
        clear * - r40853 b40854 b40855 d40844
        omega
      have d40856 : (x 8 4).toNat = 0 := by
        have r40857 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
        have b40858 := hb (x 8 4)
        have b40859 := hb (x 8 12)
        clear * - r40857 b40858 b40859 d40844
        omega
      have d40860 : (x 7 13).toNat = 0 := by
        have r40861 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40862 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e40863 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have b40864 := hb (x 5 3)
        have b40865 := hb (x 6 2)
        have b40866 := hb (x 7 13)
        have b40867 := hb (x 8 12)
        clear * - r40861 e40862 e40863 b40864 b40865 b40866 b40867 d40844 d40840
        omega
      have d40868 : (x 7 2 && x 7 13).toNat = 0 := by
        have r40869 := hand2 (x 7 2) (x 7 13)
        have b40870 := hb (x 7 13)
        have b40871 := hb (x 7 2 && x 7 13)
        clear * - r40869 b40870 b40871 d40860
        omega
      have d40872 : (x 6 1 && x 6 14).toNat = 1 := by
        have r40873 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b40874 := hb (x 5 2)
        have b40875 := hb (x 7 13)
        have b40876 := hb (x 6 1 && x 6 14)
        clear * - r40873 b40874 b40875 b40876 d40860 d40805
        omega
      have d40877 : (x 6 1).toNat = 1 := by
        have r40878 := hand1 (x 6 1) (x 6 14)
        have b40879 := hb (x 6 1)
        have b40880 := hb (x 6 1 && x 6 14)
        clear * - r40878 b40879 b40880 d40872
        omega
      have d40881 : (x 7 14).toNat = 0 := by
        have r40882 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b40883 := hb (x 6 1)
        have b40884 := hb (x 7 14)
        clear * - r40882 b40883 b40884 d40877
        omega
      have d40885 : (x 7 1 && x 7 14).toNat = 0 := by
        have r40886 := hand2 (x 7 1) (x 7 14)
        have b40887 := hb (x 7 14)
        have b40888 := hb (x 7 1 && x 7 14)
        clear * - r40886 b40887 b40888 d40881
        omega
      have d40889 : (x 7 2).toNat = 0 := by
        have r40890 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
        have b40891 := hb (x 7 2)
        have b40892 := hb (x 7 14)
        clear * - r40890 b40891 b40892 d40881
        omega
      have d40893 : (x 6 2).toNat = 0 := by
        have r40894 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40895 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e40896 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have b40897 := hb (x 5 3)
        have b40898 := hb (x 6 2)
        have b40899 := hb (x 7 13)
        have b40900 := hb (x 8 12)
        clear * - r40894 e40895 e40896 b40897 b40898 b40899 b40900 d40844 d40860 d40840
        omega
      have d40901 : (x 6 2 && x 6 13).toNat = 0 := by
        have r40902 := hand1 (x 6 2) (x 6 13)
        have b40903 := hb (x 6 2)
        have b40904 := hb (x 6 2 && x 6 13)
        clear * - r40902 b40903 b40904 d40893
        omega
      have d40905 : (x 8 13).toNat = 1 := by
        have r40906 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b40907 := hb (x 6 2)
        have b40908 := hb (x 8 13)
        have b40909 := hb (x 7 1 && x 7 14)
        clear * - r40906 b40907 b40908 b40909 d40885 d40893
        omega
      have d40910 : (x 8 1).toNat = 1 := by
        have r40911 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
        have b40912 := hb (x 8 1)
        have b40913 := hb (x 8 13)
        clear * - r40911 b40912 b40913 d40905
        omega
      have d40914 : (x 9 14).toNat = 0 := by
        have r40915 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b40916 := hb (x 8 1)
        have b40917 := hb (x 9 14)
        clear * - r40915 b40916 b40917 d40910
        omega
      have d40918 : (x 9 3 && x 9 14).toNat = 0 := by
        have r40919 := hand2 (x 9 3) (x 9 14)
        have b40920 := hb (x 9 14)
        have b40921 := hb (x 9 3 && x 9 14)
        clear * - r40919 b40920 b40921 d40914
        omega
      have d40922 : (x 9 2).toNat = 0 := by
        have r40923 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
        have b40924 := hb (x 9 2)
        have b40925 := hb (x 9 14)
        clear * - r40923 b40924 b40925 d40914
        omega
      have d40926 : (x 9 12).toNat = 0 := by
        have r40927 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40928 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
        have e40929 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
        have b40930 := hb (x 6 3)
        have b40931 := hb (x 7 2)
        have b40932 := hb (x 8 13)
        have b40933 := hb (x 9 12)
        clear * - r40927 e40928 e40929 b40930 b40931 b40932 b40933 d40905 d40889
        omega
      have d40934 : (x 9 4).toNat = 0 := by
        have r40935 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
        have b40936 := hb (x 9 4)
        have b40937 := hb (x 9 12)
        clear * - r40935 b40936 b40937 d40926
        omega
      have d40938 : (x 6 3).toNat = 0 := by
        have r40939 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40940 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
        have e40941 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
        have b40942 := hb (x 6 3)
        have b40943 := hb (x 7 2)
        have b40944 := hb (x 8 13)
        have b40945 := hb (x 9 12)
        clear * - r40939 e40940 e40941 b40942 b40943 b40944 b40945 d40926 d40905 d40889
        omega
      have d40946 : (x 6 3 && x 6 14).toNat = 0 := by
        have r40947 := hand1 (x 6 3) (x 6 14)
        have b40948 := hb (x 6 3)
        have b40949 := hb (x 6 3 && x 6 14)
        clear * - r40947 b40948 b40949 d40938
        omega
      have d40950 : (x 9 11).toNat = 1 := by
        have r40951 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b40952 := hb (x 5 4)
        have b40953 := hb (x 9 11)
        have b40954 := hb (x 8 1 && x 8 12)
        have b40955 := hb (x 7 2 && x 7 13)
        have b40956 := hb (x 6 3 && x 6 14)
        clear * - r40951 b40952 b40953 b40954 b40955 b40956 d40852 d40868 d40946 d40817
        omega
      have d40957 : (x 9 3).toNat = 1 := by
        have r40958 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
        have b40959 := hb (x 9 3)
        have b40960 := hb (x 9 11)
        clear * - r40958 b40959 b40960 d40950
        omega
      have d40961 : (x 12 12).toNat = 0 := by
        have r40962 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40963 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
        have e40964 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
        have b40965 := hb (x 9 3)
        have b40966 := hb (x 10 2)
        have b40967 := hb (x 11 13)
        have b40968 := hb (x 12 12)
        clear * - r40962 e40963 e40964 b40965 b40966 b40967 b40968 d40957
        omega
      have d40969 : (x 12 1 && x 12 12).toNat = 0 := by
        have r40970 := hand2 (x 12 1) (x 12 12)
        have b40971 := hb (x 12 12)
        have b40972 := hb (x 12 1 && x 12 12)
        clear * - r40970 b40971 b40972 d40961
        omega
      have d40973 : (x 12 4).toNat = 0 := by
        have r40974 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
        have b40975 := hb (x 12 4)
        have b40976 := hb (x 12 12)
        clear * - r40974 b40975 b40976 d40961
        omega
      have d40977 : (x 11 13).toNat = 0 := by
        have r40978 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e40979 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
        have e40980 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
        have b40981 := hb (x 9 3)
        have b40982 := hb (x 10 2)
        have b40983 := hb (x 11 13)
        have b40984 := hb (x 12 12)
        clear * - r40978 e40979 e40980 b40981 b40982 b40983 b40984 d40961 d40957
        omega
      have d40985 : (x 11 2 && x 11 13).toNat = 0 := by
        have r40986 := hand2 (x 11 2) (x 11 13)
        have b40987 := hb (x 11 13)
        have b40988 := hb (x 11 2 && x 11 13)
        clear * - r40986 b40987 b40988 d40977
        omega
      have d40989 : (x 10 1 && x 10 14).toNat = 1 := by
        have r40990 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b40991 := hb (x 9 2)
        have b40992 := hb (x 11 13)
        have b40993 := hb (x 10 1 && x 10 14)
        clear * - r40990 b40991 b40992 b40993 d40977 d40922
        omega
      have d40994 : (x 10 14).toNat = 1 := by
        have r40995 := hand2 (x 10 1) (x 10 14)
        have b40996 := hb (x 10 14)
        have b40997 := hb (x 10 1 && x 10 14)
        clear * - r40995 b40996 b40997 d40989
        omega
      have d40998 : (x 9 1).toNat = 0 := by
        have r40999 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b41000 := hb (x 9 1)
        have b41001 := hb (x 10 14)
        clear * - r40999 b41000 b41001 d40994
        omega
      have d41002 : (x 9 13).toNat = 0 := by
        have r41003 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
        have b41004 := hb (x 9 1)
        have b41005 := hb (x 9 13)
        clear * - r41003 b41004 b41005 d40998
        omega
      have d41006 : (x 8 1 && x 8 14).toNat = 1 := by
        have r41007 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b41008 := hb (x 7 2)
        have b41009 := hb (x 9 13)
        have b41010 := hb (x 8 1 && x 8 14)
        clear * - r41007 b41008 b41009 b41010 d41002 d40889
        omega
      have d41011 : (x 8 14).toNat = 1 := by
        have r41012 := hand2 (x 8 1) (x 8 14)
        have b41013 := hb (x 8 14)
        have b41014 := hb (x 8 1 && x 8 14)
        clear * - r41012 b41013 b41014 d41006
        omega
      have d41015 : (x 7 1).toNat = 0 := by
        have r41016 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b41017 := hb (x 7 1)
        have b41018 := hb (x 8 14)
        clear * - r41016 b41017 b41018 d41011
        omega
      have d41019 : (x 7 1 && x 7 12).toNat = 0 := by
        have r41020 := hand1 (x 7 1) (x 7 12)
        have b41021 := hb (x 7 1)
        have b41022 := hb (x 7 1 && x 7 12)
        clear * - r41020 b41021 b41022 d41015
        omega
      have d41023 : (x 8 11).toNat = 1 := by
        have r41024 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b41025 := hb (x 4 4)
        have b41026 := hb (x 8 11)
        have b41027 := hb (x 7 1 && x 7 12)
        have b41028 := hb (x 6 2 && x 6 13)
        have b41029 := hb (x 5 3 && x 5 14)
        clear * - r41024 b41025 b41026 b41027 b41028 b41029 d41019 d40901 d40801 d40743
        omega
      have d41030 : (x 8 3).toNat = 1 := by
        have r41031 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
        have b41032 := hb (x 8 3)
        have b41033 := hb (x 8 11)
        clear * - r41031 b41032 b41033 d41023
        omega
      have d41034 : (x 11 12).toNat = 0 := by
        have r41035 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e41036 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e41037 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b41038 := hb (x 8 3)
        have b41039 := hb (x 9 2)
        have b41040 := hb (x 10 13)
        have b41041 := hb (x 11 12)
        clear * - r41035 e41036 e41037 b41038 b41039 b41040 b41041 d40922 d41030
        omega
      have d41042 : (x 11 1 && x 11 12).toNat = 0 := by
        have r41043 := hand2 (x 11 1) (x 11 12)
        have b41044 := hb (x 11 12)
        have b41045 := hb (x 11 1 && x 11 12)
        clear * - r41043 b41044 b41045 d41034
        omega
      have d41046 : (x 10 13).toNat = 0 := by
        have r41047 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e41048 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e41049 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b41050 := hb (x 8 3)
        have b41051 := hb (x 9 2)
        have b41052 := hb (x 10 13)
        have b41053 := hb (x 11 12)
        clear * - r41047 e41048 e41049 b41050 b41051 b41052 b41053 d41034 d40922 d41030
        omega
      have d41054 : (x 10 2 && x 10 13).toNat = 0 := by
        have r41055 := hand2 (x 10 2) (x 10 13)
        have b41056 := hb (x 10 13)
        have b41057 := hb (x 10 2 && x 10 13)
        clear * - r41055 b41056 b41057 d41046
        omega
      have d41058 : (x 12 11).toNat = 1 := by
        have r41059 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b41060 := hb (x 8 4)
        have b41061 := hb (x 12 11)
        have b41062 := hb (x 11 1 && x 11 12)
        have b41063 := hb (x 10 2 && x 10 13)
        have b41064 := hb (x 9 3 && x 9 14)
        clear * - r41059 b41060 b41061 b41062 b41063 b41064 d41042 d41054 d40918 d40856
        omega
      have d41065 : (x 12 3).toNat = 1 := by
        have r41066 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
        have b41067 := hb (x 12 3)
        have b41068 := hb (x 12 11)
        clear * - r41066 b41067 b41068 d41058
        omega
      have d41069 : (x 15 12).toNat = 0 := by
        have r41070 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e41071 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e41072 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b41073 := hb (x 12 3)
        have b41074 := hb (x 13 2)
        have b41075 := hb (x 14 13)
        have b41076 := hb (x 15 12)
        clear * - r41070 e41071 e41072 b41073 b41074 b41075 b41076 d41065
        omega
      have d41077 : (x 15 1 && x 15 12).toNat = 0 := by
        have r41078 := hand2 (x 15 1) (x 15 12)
        have b41079 := hb (x 15 12)
        have b41080 := hb (x 15 1 && x 15 12)
        clear * - r41078 b41079 b41080 d41069
        omega
      have d41081 : (x 14 13).toNat = 0 := by
        have r41082 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e41083 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e41084 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b41085 := hb (x 12 3)
        have b41086 := hb (x 13 2)
        have b41087 := hb (x 14 13)
        have b41088 := hb (x 15 12)
        clear * - r41082 e41083 e41084 b41085 b41086 b41087 b41088 d41069 d41065
        omega
      have d41089 : (x 14 2 && x 14 13).toNat = 0 := by
        have r41090 := hand2 (x 14 2) (x 14 13)
        have b41091 := hb (x 14 13)
        have b41092 := hb (x 14 2 && x 14 13)
        clear * - r41090 b41091 b41092 d41081
        omega
      have d41093 : (x 13 2).toNat = 0 := by
        have r41094 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e41095 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e41096 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b41097 := hb (x 12 3)
        have b41098 := hb (x 13 2)
        have b41099 := hb (x 14 13)
        have b41100 := hb (x 15 12)
        clear * - r41094 e41095 e41096 b41097 b41098 b41099 b41100 d41069 d41081 d41065
        omega
      have d41101 : (x 10 1).toNat = 1 := by
        have r41102 := hand1 (x 10 1) (x 10 14)
        have b41103 := hb (x 10 1)
        have b41104 := hb (x 10 1 && x 10 14)
        clear * - r41102 b41103 b41104 d40989
        omega
      have d41105 : (x 11 14).toNat = 0 := by
        have r41106 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b41107 := hb (x 10 1)
        have b41108 := hb (x 11 14)
        clear * - r41106 b41107 b41108 d41101
        omega
      have d41109 : (x 11 1 && x 11 14).toNat = 0 := by
        have r41110 := hand2 (x 11 1) (x 11 14)
        have b41111 := hb (x 11 14)
        have b41112 := hb (x 11 1 && x 11 14)
        clear * - r41110 b41111 b41112 d41105
        omega
      have d41113 : (x 11 2).toNat = 0 := by
        have r41114 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
        have b41115 := hb (x 11 2)
        have b41116 := hb (x 11 14)
        clear * - r41114 b41115 b41116 d41105
        omega
      have d41117 : (x 10 2).toNat = 0 := by
        have r41118 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e41119 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
        have e41120 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
        have b41121 := hb (x 9 3)
        have b41122 := hb (x 10 2)
        have b41123 := hb (x 11 13)
        have b41124 := hb (x 12 12)
        clear * - r41118 e41119 e41120 b41121 b41122 b41123 b41124 d40961 d40977 d40957
        omega
      have d41125 : (x 12 13).toNat = 1 := by
        have r41126 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b41127 := hb (x 10 2)
        have b41128 := hb (x 12 13)
        have b41129 := hb (x 11 1 && x 11 14)
        clear * - r41126 b41127 b41128 b41129 d41109 d41117
        omega
      have d41130 : (x 12 1).toNat = 1 := by
        have r41131 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
        have b41132 := hb (x 12 1)
        have b41133 := hb (x 12 13)
        clear * - r41131 b41132 b41133 d41125
        omega
      have d41134 : (x 13 14).toNat = 0 := by
        have r41135 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b41136 := hb (x 12 1)
        have b41137 := hb (x 13 14)
        clear * - r41135 b41136 b41137 d41130
        omega
      have d41138 : (x 13 1 && x 13 14).toNat = 0 := by
        have r41139 := hand2 (x 13 1) (x 13 14)
        have b41140 := hb (x 13 14)
        have b41141 := hb (x 13 1 && x 13 14)
        clear * - r41139 b41140 b41141 d41134
        omega
      have d41142 : (x 12 2).toNat = 1 := by
        have r41143 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b41144 := hb (x 12 2)
        have b41145 := hb (x 14 13)
        have b41146 := hb (x 13 1 && x 13 14)
        clear * - r41143 b41144 b41145 b41146 d41081 d41138
        omega
      have d41147 : (x 14 12).toNat = 0 := by
        have r41148 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e41149 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
        have e41150 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
        have b41151 := hb (x 11 3)
        have b41152 := hb (x 12 2)
        have b41153 := hb (x 13 13)
        have b41154 := hb (x 14 12)
        clear * - r41148 e41149 e41150 b41151 b41152 b41153 b41154 d41142
        omega
      have d41155 : (x 14 4).toNat = 0 := by
        have r41156 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
        have b41157 := hb (x 14 4)
        have b41158 := hb (x 14 12)
        clear * - r41156 b41157 b41158 d41147
        omega
      have d41159 : (x 14 4 && x 14 14).toNat = 0 := by
        have r41160 := hand1 (x 14 4) (x 14 14)
        have b41161 := hb (x 14 4)
        have b41162 := hb (x 14 4 && x 14 14)
        clear * - r41160 b41161 b41162 d41155
        omega
      have d41163 : (x 13 13).toNat = 0 := by
        have r41164 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e41165 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
        have e41166 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
        have b41167 := hb (x 11 3)
        have b41168 := hb (x 12 2)
        have b41169 := hb (x 13 13)
        have b41170 := hb (x 14 12)
        clear * - r41164 e41165 e41166 b41167 b41168 b41169 b41170 d41147 d41142
        omega
      have d41171 : (x 13 5).toNat = 0 := by
        have r41172 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
        have b41173 := hb (x 13 5)
        have b41174 := hb (x 13 13)
        clear * - r41172 b41173 b41174 d41163
        omega
      have d41175 : (x 13 3 && x 13 14).toNat = 0 := by
        have r41176 := hand2 (x 13 3) (x 13 14)
        have b41177 := hb (x 13 14)
        have b41178 := hb (x 13 3 && x 13 14)
        clear * - r41176 b41177 b41178 d41134
        omega
      have d41179 : (x 16 11).toNat = 1 := by
        have r41180 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b41181 := hb (x 12 4)
        have b41182 := hb (x 16 11)
        have b41183 := hb (x 15 1 && x 15 12)
        have b41184 := hb (x 14 2 && x 14 13)
        have b41185 := hb (x 13 3 && x 13 14)
        clear * - r41180 b41181 b41182 b41183 b41184 b41185 d41077 d41089 d41175 d40973
        omega
      have d41186 : (x 16 3).toNat = 1 := by
        have r41187 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
        have b41188 := hb (x 16 3)
        have b41189 := hb (x 16 11)
        clear * - r41187 b41188 b41189 d41179
        omega
      have d41190 : (x 19 12).toNat = 0 := by
        have r41191 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e41192 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
        have e41193 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
        have b41194 := hb (x 16 3)
        have b41195 := hb (x 17 2)
        have b41196 := hb (x 18 13)
        have b41197 := hb (x 19 12)
        clear * - r41191 e41192 e41193 b41194 b41195 b41196 b41197 d41186
        omega
      have d41198 : (x 18 13).toNat = 0 := by
        have r41199 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e41200 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
        have e41201 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
        have b41202 := hb (x 16 3)
        have b41203 := hb (x 17 2)
        have b41204 := hb (x 18 13)
        have b41205 := hb (x 19 12)
        clear * - r41199 e41200 e41201 b41202 b41203 b41204 b41205 d41190 d41186
        omega
      have d41206 : (x 17 2).toNat = 0 := by
        have r41207 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e41208 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
        have e41209 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
        have b41210 := hb (x 16 3)
        have b41211 := hb (x 17 2)
        have b41212 := hb (x 18 13)
        have b41213 := hb (x 19 12)
        clear * - r41207 e41208 e41209 b41210 b41211 b41212 b41213 d41190 d41198 d41186
        omega
      have d41214 : (x 13 12).toNat = 0 := by
        have r41215 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e41216 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
        have e41217 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
        have b41218 := hb (x 10 3)
        have b41219 := hb (x 11 2)
        have b41220 := hb (x 12 13)
        have b41221 := hb (x 13 12)
        clear * - r41215 e41216 e41217 b41218 b41219 b41220 b41221 d41125 d41113
        omega
      have d41222 : (x 13 4).toNat = 0 := by
        have r41223 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
        have b41224 := hb (x 13 4)
        have b41225 := hb (x 13 12)
        clear * - r41223 b41224 b41225 d41214
        omega
      have d41226 : (x 10 3).toNat = 0 := by
        have r41227 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e41228 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
        have e41229 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
        have b41230 := hb (x 10 3)
        have b41231 := hb (x 11 2)
        have b41232 := hb (x 12 13)
        have b41233 := hb (x 13 12)
        clear * - r41227 e41228 e41229 b41230 b41231 b41232 b41233 d41214 d41125 d41113
        omega
      have d41234 : (x 10 3 && x 10 14).toNat = 0 := by
        have r41235 := hand1 (x 10 3) (x 10 14)
        have b41236 := hb (x 10 3)
        have b41237 := hb (x 10 3 && x 10 14)
        clear * - r41235 b41236 b41237 d41226
        omega
      have d41238 : (x 13 11).toNat = 1 := by
        have r41239 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b41240 := hb (x 9 4)
        have b41241 := hb (x 13 11)
        have b41242 := hb (x 12 1 && x 12 12)
        have b41243 := hb (x 11 2 && x 11 13)
        have b41244 := hb (x 10 3 && x 10 14)
        clear * - r41239 b41240 b41241 b41242 b41243 b41244 d40969 d40985 d41234 d40934
        omega
      have d41245 : (x 13 3).toNat = 1 := by
        have r41246 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
        have b41247 := hb (x 13 3)
        have b41248 := hb (x 13 11)
        clear * - r41246 b41247 b41248 d41238
        omega
      have d41249 : (x 16 12).toNat = 0 := by
        have r41250 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e41251 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
        have e41252 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
        have b41253 := hb (x 13 3)
        have b41254 := hb (x 14 2)
        have b41255 := hb (x 15 13)
        have b41256 := hb (x 16 12)
        clear * - r41250 e41251 e41252 b41253 b41254 b41255 b41256 d41245
        omega
      have d41257 : (x 16 1 && x 16 12).toNat = 0 := by
        have r41258 := hand2 (x 16 1) (x 16 12)
        have b41259 := hb (x 16 12)
        have b41260 := hb (x 16 1 && x 16 12)
        clear * - r41258 b41259 b41260 d41249
        omega
      have d41261 : (x 16 2 && x 16 12).toNat = 0 := by
        have r41262 := hand2 (x 16 2) (x 16 12)
        have b41263 := hb (x 16 12)
        have b41264 := hb (x 16 2 && x 16 12)
        clear * - r41262 b41263 b41264 d41249
        omega
      have d41265 : (x 15 13).toNat = 0 := by
        have r41266 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e41267 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
        have e41268 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
        have b41269 := hb (x 13 3)
        have b41270 := hb (x 14 2)
        have b41271 := hb (x 15 13)
        have b41272 := hb (x 16 12)
        clear * - r41266 e41267 e41268 b41269 b41270 b41271 b41272 d41249 d41245
        omega
      have d41273 : (x 15 2 && x 15 13).toNat = 0 := by
        have r41274 := hand2 (x 15 2) (x 15 13)
        have b41275 := hb (x 15 13)
        have b41276 := hb (x 15 2 && x 15 13)
        clear * - r41274 b41275 b41276 d41265
        omega
      have d41277 : (x 15 3 && x 15 13).toNat = 0 := by
        have r41278 := hand2 (x 15 3) (x 15 13)
        have b41279 := hb (x 15 13)
        have b41280 := hb (x 15 3 && x 15 13)
        clear * - r41278 b41279 b41280 d41265
        omega
      have d41281 : (x 14 1 && x 14 14).toNat = 1 := by
        have r41282 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b41283 := hb (x 13 2)
        have b41284 := hb (x 15 13)
        have b41285 := hb (x 14 1 && x 14 14)
        clear * - r41282 b41283 b41284 b41285 d41265 d41093
        omega
      have d41286 : (x 14 1).toNat = 1 := by
        have r41287 := hand1 (x 14 1) (x 14 14)
        have b41288 := hb (x 14 1)
        have b41289 := hb (x 14 1 && x 14 14)
        clear * - r41287 b41288 b41289 d41281
        omega
      have d41290 : (x 15 14).toNat = 0 := by
        have r41291 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b41292 := hb (x 14 1)
        have b41293 := hb (x 15 14)
        clear * - r41291 b41292 b41293 d41286
        omega
      have d41294 : (x 15 1 && x 15 14).toNat = 0 := by
        have r41295 := hand2 (x 15 1) (x 15 14)
        have b41296 := hb (x 15 14)
        have b41297 := hb (x 15 1 && x 15 14)
        clear * - r41295 b41296 b41297 d41290
        omega
      have d41298 : (x 15 2).toNat = 0 := by
        have r41299 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
        have b41300 := hb (x 15 2)
        have b41301 := hb (x 15 14)
        clear * - r41299 b41300 b41301 d41290
        omega
      have d41302 : (x 14 2).toNat = 0 := by
        have r41303 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e41304 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
        have e41305 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
        have b41306 := hb (x 13 3)
        have b41307 := hb (x 14 2)
        have b41308 := hb (x 15 13)
        have b41309 := hb (x 16 12)
        clear * - r41303 e41304 e41305 b41306 b41307 b41308 b41309 d41249 d41265 d41245
        omega
      have d41310 : (x 16 13).toNat = 1 := by
        have r41311 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b41312 := hb (x 14 2)
        have b41313 := hb (x 16 13)
        have b41314 := hb (x 15 1 && x 15 14)
        clear * - r41311 b41312 b41313 b41314 d41294 d41302
        omega
      have d41315 : (x 17 12).toNat = 0 := by
        have r41316 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e41317 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
        have e41318 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
        have b41319 := hb (x 14 3)
        have b41320 := hb (x 15 2)
        have b41321 := hb (x 16 13)
        have b41322 := hb (x 17 12)
        clear * - r41316 e41317 e41318 b41319 b41320 b41321 b41322 d41310 d41298
        omega
      have d41323 : (x 14 3).toNat = 0 := by
        have r41324 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e41325 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
        have e41326 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
        have b41327 := hb (x 14 3)
        have b41328 := hb (x 15 2)
        have b41329 := hb (x 16 13)
        have b41330 := hb (x 17 12)
        clear * - r41324 e41325 e41326 b41327 b41328 b41329 b41330 d41315 d41310 d41298
        omega
      have d41331 : (x 14 3 && x 14 14).toNat = 0 := by
        have r41332 := hand1 (x 14 3) (x 14 14)
        have b41333 := hb (x 14 3)
        have b41334 := hb (x 14 3 && x 14 14)
        clear * - r41332 b41333 b41334 d41323
        omega
      have d41335 : (x 17 11).toNat = 1 := by
        have r41336 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b41337 := hb (x 13 4)
        have b41338 := hb (x 17 11)
        have b41339 := hb (x 16 1 && x 16 12)
        have b41340 := hb (x 15 2 && x 15 13)
        have b41341 := hb (x 14 3 && x 14 14)
        clear * - r41336 b41337 b41338 b41339 b41340 b41341 d41257 d41273 d41331 d41222
        omega
      have d41342 : (x 17 3).toNat = 1 := by
        have r41343 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
        have b41344 := hb (x 17 3)
        have b41345 := hb (x 17 11)
        clear * - r41343 b41344 b41345 d41335
        omega
      have d41346 : (x 20 12).toNat = 0 := by
        have r41347 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e41348 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
        have e41349 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
        have b41350 := hb (x 17 3)
        have b41351 := hb (x 18 2)
        have b41352 := hb (x 19 13)
        have b41353 := hb (x 20 12)
        clear * - r41347 e41348 e41349 b41350 b41351 b41352 b41353 d41342
        omega
      have d41354 : (x 19 13).toNat = 0 := by
        have r41355 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e41356 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
        have e41357 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
        have b41358 := hb (x 17 3)
        have b41359 := hb (x 18 2)
        have b41360 := hb (x 19 13)
        have b41361 := hb (x 20 12)
        clear * - r41355 e41356 e41357 b41358 b41359 b41360 b41361 d41346 d41342
        omega
      have d41362 : (x 18 1 && x 18 14).toNat = 1 := by
        have r41363 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b41364 := hb (x 17 2)
        have b41365 := hb (x 19 13)
        have b41366 := hb (x 18 1 && x 18 14)
        clear * - r41363 b41364 b41365 b41366 d41354 d41206
        omega
      have d41367 : (x 18 14).toNat = 1 := by
        have r41368 := hand2 (x 18 1) (x 18 14)
        have b41369 := hb (x 18 14)
        have b41370 := hb (x 18 1 && x 18 14)
        clear * - r41368 b41369 b41370 d41362
        omega
      have d41371 : (x 17 1).toNat = 0 := by
        have r41372 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b41373 := hb (x 17 1)
        have b41374 := hb (x 18 14)
        clear * - r41372 b41373 b41374 d41367
        omega
      have d41375 : (x 17 1 && x 17 11).toNat = 0 := by
        have r41376 := hand1 (x 17 1) (x 17 11)
        have b41377 := hb (x 17 1)
        have b41378 := hb (x 17 1 && x 17 11)
        clear * - r41376 b41377 b41378 d41371
        omega
      have d41379 : (x 18 2).toNat = 0 := by
        have r41380 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e41381 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
        have e41382 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
        have b41383 := hb (x 17 3)
        have b41384 := hb (x 18 2)
        have b41385 := hb (x 19 13)
        have b41386 := hb (x 20 12)
        clear * - r41380 e41381 e41382 b41383 b41384 b41385 b41386 d41346 d41354 d41342
        omega
      have d41387 : (x 18 10).toNat = 0 := by
        have r41388 : (x 18 10).toNat ≤ (x 18 2).toNat := himp _ _ (hp10 18)
        have b41389 := hb (x 18 2)
        have b41390 := hb (x 18 10)
        clear * - r41388 b41389 b41390 d41379
        omega
      have r41391 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := by have q := hcov10 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b41392 := hb (x 13 5)
      have b41393 := hb (x 18 10)
      have b41394 := hb (x 17 1 && x 17 11)
      have b41395 := hb (x 16 2 && x 16 12)
      have b41396 := hb (x 15 3 && x 15 13)
      have b41397 := hb (x 14 4 && x 14 14)
      linarith only [r41391, b41392, b41393, b41394, b41395, b41396, b41397, d41387, d41375, d41261, d41277, d41159, d41171]
  · have f41398 : (x 1 1).toNat = 1 := by rw [h39172]; rfl
    have d41399 : (x 2 14).toNat = 0 := by
      have r41400 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b41401 := hb (x 1 1)
      have b41402 := hb (x 2 14)
      clear * - r41400 b41401 b41402 f41398
      omega
    have d41403 : (x 2 1 && x 2 14).toNat = 0 := by
      have r41404 := hand2 (x 2 1) (x 2 14)
      have b41405 := hb (x 2 14)
      have b41406 := hb (x 2 1 && x 2 14)
      clear * - r41404 b41405 b41406 d41399
      omega
    have d41407 : (x 2 6).toNat = 0 := by
      have r41408 : (x 2 6).toNat ≤ (x 2 14).toNat := himp _ _ (hp6 2)
      have b41409 := hb (x 2 6)
      have b41410 := hb (x 2 14)
      clear * - r41408 b41409 b41410 d41399
      omega
    have d41411 : (x 2 2 && x 2 6).toNat = 0 := by
      have r41412 := hand2 (x 2 2) (x 2 6)
      have b41413 := hb (x 2 6)
      have b41414 := hb (x 2 2 && x 2 6)
      clear * - r41412 b41413 b41414 d41407
      omega
    have d41415 : (x 2 2).toNat = 0 := by
      have r41416 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
      have b41417 := hb (x 2 2)
      have b41418 := hb (x 2 14)
      clear * - r41416 b41417 b41418 d41399
      omega
    have d41419 : (x 3 13).toNat = 1 := by
      have r41420 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b41421 := hb (x 1 2)
      have b41422 := hb (x 3 13)
      have b41423 := hb (x 2 1 && x 2 14)
      clear * - r41420 b41421 b41422 b41423 d41403 g19
      omega
    have d41424 : (x 3 1).toNat = 1 := by
      have r41425 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
      have b41426 := hb (x 3 1)
      have b41427 := hb (x 3 13)
      clear * - r41425 b41426 b41427 d41419
      omega
    have d41428 : (x 4 12).toNat = 0 := by
      have r41429 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e41430 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e41431 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b41432 := hb (x 1 3)
      have b41433 := hb (x 2 2)
      have b41434 := hb (x 3 13)
      have b41435 := hb (x 4 12)
      clear * - r41429 e41430 e41431 b41432 b41433 b41434 b41435 d41419 d41415
      omega
    have d41436 : (x 4 3 && x 4 12).toNat = 0 := by
      have r41437 := hand2 (x 4 3) (x 4 12)
      have b41438 := hb (x 4 12)
      have b41439 := hb (x 4 3 && x 4 12)
      clear * - r41437 b41438 b41439 d41428
      omega
    have d41440 : (x 4 4).toNat = 0 := by
      have r41441 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
      have b41442 := hb (x 4 4)
      have b41443 := hb (x 4 12)
      clear * - r41441 b41442 b41443 d41428
      omega
    have d41444 : (x 1 3).toNat = 0 := by
      have r41445 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e41446 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e41447 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b41448 := hb (x 1 3)
      have b41449 := hb (x 2 2)
      have b41450 := hb (x 3 13)
      have b41451 := hb (x 4 12)
      clear * - r41445 e41446 e41447 b41448 b41449 b41450 b41451 d41428 d41419 d41415
      omega
    have d41452 : (x 1 3 && x 1 7).toNat = 0 := by
      have r41453 := hand1 (x 1 3) (x 1 7)
      have b41454 := hb (x 1 3)
      have b41455 := hb (x 1 3 && x 1 7)
      clear * - r41453 b41454 b41455 d41444
      omega
    have r41456 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r41457 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r41458 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r41459 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e41460 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e41461 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e41462 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e41463 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e41464 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e41465 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have r41466 : (x (-11) 12).toNat + (x (-12) 1 && x (-12) 13).toNat + (x (-13) 2 && x (-13) 14).toNat + (x (-14) 3).toNat = 1 := by have q := hd12 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e41467 : (x (-12) 1 && x (-12) 13).toNat = (x (-12) 13).toNat := handr _ _ (fun h => hp13 (-12) (h))
    have e41468 : (x (-13) 2 && x (-13) 14).toNat = (x (-13) 2).toNat := handl _ _ (fun h => hp2 (-13) (h))
    have r41469 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e41470 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e41471 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have r41472 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e41473 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e41474 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have r41475 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r41476 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e41477 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
    have e41478 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
    have r41479 : 1 ≤ (x 2 6).toNat + (x 1 1 && x 1 7).toNat + (x 0 2 && x 0 8).toNat + (x (-1) 3 && x (-1) 9).toNat + (x (-2) 4 && x (-2) 10).toNat + (x (-3) 5 && x (-3) 11).toNat + (x (-4) 6 && x (-4) 12).toNat + (x (-5) 7 && x (-5) 13).toNat + (x (-6) 8 && x (-6) 14).toNat + (x (-7) 9).toNat := by have q := hcov6 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r41480 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r41481 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r41482 : 1 ≤ (x (-7) 11).toNat + (x (-8) 1 && x (-8) 12).toNat + (x (-9) 2 && x (-9) 13).toNat + (x (-10) 3 && x (-10) 14).toNat + (x (-11) 4).toNat := by have q := hcov11 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r41483 : 1 ≤ (x (-11) 13).toNat + (x (-12) 1 && x (-12) 14).toNat + (x (-13) 2).toNat := by have q := hcov13 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r41484 : (x (-11) 4).toNat ≤ (x (-11) 12).toNat := himp _ _ (hp4 (-11))
    have r41485 : (x (-11) 5).toNat ≤ (x (-11) 13).toNat := himp _ _ (hp5 (-11))
    have r41486 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
    have r41487 := hand1 (x (-4) 8) (x (-4) 12)
    have r41488 := hand1 (x (-5) 9) (x (-5) 13)
    have r41489 := hand2 (x 1 1) (x 1 7)
    have r41490 := hand1 (x (-4) 6) (x (-4) 12)
    have r41491 := hand1 (x (-5) 7) (x (-5) 13)
    have r41492 := hand1 (x (-6) 8) (x (-6) 14)
    have r41493 := hand2 (x 6 1) (x 6 10)
    have r41494 := hand2 (x 5 2) (x 5 11)
    have r41495 := hand1 (x (-7) 1) (x (-7) 11)
    have r41496 := hand2 (x (-8) 2) (x (-8) 12)
    have r41497 := hand2 (x (-9) 3) (x (-9) 13)
    have r41498 := hand2 (x (-10) 4) (x (-10) 14)
    have r41499 := hand2 (x (-8) 1) (x (-8) 12)
    have r41500 := hand2 (x (-9) 2) (x (-9) 13)
    have r41501 := hand2 (x (-10) 3) (x (-10) 14)
    have r41502 := hand2 (x (-12) 1) (x (-12) 14)
    have b41556 := hb (x 7 1)
    linarith only [r41456, r41457, r41458, r41459, e41460, e41461, e41462, e41463, e41464, e41465, r41466, e41467, e41468, r41469, e41470, e41471, r41472, e41473, e41474, r41475, r41476, e41477, e41478, r41479, r41480, r41481, r41482, r41483, r41484, r41485, r41486, r41487, r41488, r41489, r41490, r41491, r41492, r41493, r41494, r41495, r41496, r41497, r41498, r41499, r41500, r41501, r41502, b41556, g0, g1, g2, g4, g6, g7, g10, g13, g14, g17, f41398, d41444, g22, d41415, d41407, d41424, d41440, d41411, d41452, g25, g26, g27, g28, g49, g50, g51, g52, d41436, g74, g75]

theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_a111100 (x : ℤ → Fin 16 → Bool)
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
    (g3 : (x (-2) 7).toNat = 0)
    (g4 : (x (-2) 10).toNat = 0)
    (g5 : (x (-2) 11).toNat = 0)
    (g6 : (x (-1) 3).toNat = 0)
    (g7 : (x (-1) 5).toNat = 0)
    (g8 : (x (-1) 6).toNat = 0)
    (g9 : (x (-1) 7).toNat = 0)
    (g10 : (x (-1) 9).toNat = 0)
    (g11 : (x (-1) 10).toNat = 0)
    (g12 : (x (-1) 13).toNat = 0)
    (g13 : (x 0 2).toNat = 1)
    (g14 : (x 0 4).toNat = 1)
    (g15 : (x 0 5).toNat = 1)
    (g16 : (x 0 7).toNat = 0)
    (g17 : (x 0 8).toNat = 0)
    (g18 : (x 0 9).toNat = 0)
    (g19 : (x 1 2).toNat = 0)
    (g20 : (x 1 4).toNat = 0)
    (g21 : (x 1 5).toNat = 0)
    (g22 : (x 1 6).toNat = 0)
    (g23 : (x 2 5).toNat = 0)
    (g24 : (x 3 4).toNat = 0)
    (g25 : (x 0 4 && x 0 8).toNat = 0)
    (g26 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g27 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g28 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g29 : (x 1 4 && x 1 8).toNat = 0)
    (g30 : (x (-1) 6 && x (-1) 10).toNat = 0)
    (g31 : (x (-2) 7 && x (-2) 11).toNat = 0)
    (g32 : (x 3 4 && x 3 8).toNat = 0)
    (g33 : (x 2 5 && x 2 9).toNat = 0)
    (g34 : (x 1 6 && x 1 10).toNat = 0)
    (g35 : (x 0 7 && x 0 11).toNat = 0)
    (g36 : (x 5 4 && x 5 8).toNat = 0)
    (g37 : (x 4 5 && x 4 9).toNat = 0)
    (g38 : (x 3 6 && x 3 10).toNat = 0)
    (g39 : (x 2 7 && x 2 11).toNat = 0)
    (g40 : (x 1 8 && x 1 12).toNat = 0)
    (g41 : (x (-2) 1 && x (-2) 6).toNat = 0)
    (g42 : (x (-3) 2 && x (-3) 7).toNat = 0)
    (g43 : (x 6 3 && x 6 8).toNat = 0)
    (g44 : (x 5 4 && x 5 9).toNat = 0)
    (g45 : (x 4 5 && x 4 10).toNat = 0)
    (g46 : (x 3 6 && x 3 11).toNat = 0)
    (g47 : (x 2 7 && x 2 12).toNat = 0)
    (g48 : (x 1 8 && x 1 13).toNat = 0)
    (g49 : (x 0 2 && x 0 8).toNat = 0)
    (g50 : (x (-1) 3 && x (-1) 9).toNat = 0)
    (g51 : (x (-2) 4 && x (-2) 10).toNat = 0)
    (g52 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g53 : (x 1 2 && x 1 8).toNat = 0)
    (g54 : (x (-1) 4 && x (-1) 10).toNat = 0)
    (g55 : (x (-2) 5 && x (-2) 11).toNat = 0)
    (g56 : (x (-3) 6 && x (-3) 12).toNat = 0)
    (g57 : (x (-4) 7 && x (-4) 13).toNat = 0)
    (g58 : (x 6 2 && x 6 8).toNat = 0)
    (g59 : (x 5 3 && x 5 9).toNat = 0)
    (g60 : (x 4 4 && x 4 10).toNat = 0)
    (g61 : (x 3 5 && x 3 11).toNat = 0)
    (g62 : (x 2 6 && x 2 12).toNat = 0)
    (g63 : (x 1 7 && x 1 13).toNat = 0)
    (g64 : (x 0 8 && x 0 14).toNat = 0)
    (g65 : (x 6 1 && x 6 8).toNat = 0)
    (g66 : (x 5 2 && x 5 9).toNat = 0)
    (g67 : (x 4 3 && x 4 10).toNat = 0)
    (g68 : (x 3 4 && x 3 11).toNat = 0)
    (g69 : (x 2 5 && x 2 12).toNat = 0)
    (g70 : (x 1 6 && x 1 13).toNat = 0)
    (g71 : (x 0 7 && x 0 14).toNat = 0)
    (g72 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g73 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g74 : (x 3 4 && x 3 13).toNat = 0)
    (g75 : (x 2 5 && x 2 14).toNat = 0)
    (g76 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g77 : (x 2 4 && x 2 14).toNat = 0)
    (g78 : (x 3 4 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_a111100_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78
